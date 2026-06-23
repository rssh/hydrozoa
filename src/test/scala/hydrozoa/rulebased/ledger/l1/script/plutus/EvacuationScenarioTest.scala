package hydrozoa.rulebased.ledger.l1.script.plutus

import cats.effect.unsafe.implicits.global
import cps.*
import hydrozoa.*
import hydrozoa.config.HydrozoaBlueprint
import hydrozoa.config.node.{MultiNodeConfig, NodeConfig}
import hydrozoa.lib.cardano.scalus.QuantizedTime.QuantizedInstant.realTimeQuantizedInstant
import hydrozoa.lib.cardano.scalus.VerificationKeyExtra.{addrKeyHash, shelleyAddress}
import hydrozoa.multisig.consensus.peer.PeerWallet
import hydrozoa.multisig.ledger.commitment.TrustedSetup
import hydrozoa.multisig.ledger.joint.EvacuationMap
import hydrozoa.rulebased.ledger.l1.state.TreasuryState.RuleBasedTreasuryDatum.Resolved
import hydrozoa.rulebased.ledger.l1.tx.CommonGenerators.genCollateralUtxo
import hydrozoa.rulebased.ledger.l1.tx.EvacuationTx
import hydrozoa.rulebased.ledger.l1.utxo.{RuleBasedTreasuryOutput, RuleBasedTreasuryUtxo}
import org.scalacheck.rng.Seed
import org.scalacheck.{Arbitrary, Gen}
import org.scalatest.funsuite.AnyFunSuite
import scala.concurrent.Await
import scala.concurrent.duration.Duration
import scalus.cardano.ledger.*
import scalus.cardano.ledger.ArbitraryInstances.given
import scalus.cardano.ledger.EvaluatorMode.EvaluateAndComputeCost
import scalus.cardano.ledger.rules.{CardanoMutator, State, UtxoEnv}
import scalus.testing.{ImmutableEmulator, Scenario}
import scalus.uplc.builtin.bls12_381.G2Element
import test.Generators.Hydrozoa.{genEvacuationMap, genPubKeyUtxo}

/** Evacuation safety/liveness scenario for the rule-based regime (test "B").
  *
  * Starting from a **Resolved** treasury whose accumulator commits to a full evacuation map `M`,
  * peers drain `M` to L1 by submitting `EvacuationTx`s carrying KZG membership proofs. This test
  * evacuates `M` **one obligation at a time**, with the `Scenario` monad branching over **which
  * obligation to evacuate next** (`Scenario.fromCollection(remaining.keys)`), so it explores all
  * `N!` evacuation orders. On every order it asserts:
  *
  *   - **distribution == M**: the multiset of evacuated outputs equals `M.outputsCooked` (every
  *     obligation paid out exactly once, to its own address/value — no theft, no stranding);
  *   - the treasury **drains exactly**: the final residual value equals the initial value minus
  *     `M.totalValue` (the on-chain value invariant `treasuryIn == treasuryOut + Σ evacuated` holds
  *     across the whole run, in any order).
  *
  * Like test A this is a deterministic example test (seeded `MultiNodeConfig`, branching in the
  * `Scenario` monad, not ScalaCheck). Each `EvacuationTx` **spends its fee utxo** (and re-sends
  * collateral rather than spending it), so every evacuation step gets its own fee utxo; one
  * collateral is reused. Evacuation has no time-validity bound, so (unlike test A) no
  * deadline/sleep is involved.
  *
  * `numEvacuees` is kept small (the exhaustive `N!` fan-out × on-chain BLS membership checks is
  * expensive); larger maps are covered by the bounded-trace ScalaCheck Commands test.
  */
class EvacuationScenarioTest extends AnyFunSuite {

    /** A single, deterministic multi-peer fixture (seeded). */
    private val env =
        MultiNodeConfig.generateWithCoil().pureApply(Gen.Parameters.default, Seed(0L))

    /** Materialize a generator deterministically from a fixed seed. */
    private def fixed[A](gen: Gen[A], seed: Long): A =
        gen.pureApply(Gen.Parameters.default, Seed(seed))

    private val config: NodeConfig = env.nodeConfigs.head._2
    private val ownWallet: PeerWallet = env.nodePrivateConfigs.head._2.ownWallet
    private val ownKeyHash = ownWallet.exportVerificationKey.addrKeyHash
    private val ownAddr = ownWallet.exportVerificationKey.shelleyAddress()(using env.headConfig)
    private val treasuryAddr = HydrozoaBlueprint.mkTreasuryAddress(env.headConfig.network)

    // Small on purpose: the test explores all N! evacuation orders, each step an on-chain KZG
    // membership check. Larger maps belong to the bounded-trace ScalaCheck Commands test.
    private val numEvacuees = 2

    private val treasuryToken = Value.asset(
      env.headConfig.headMultisigScript.policyId,
      env.headConfig.headTokenNames.treasuryTokenName,
      1
    )
    private val fallbackTxId = fixed(Arbitrary.arbitrary[TransactionHash], 1)
    private val now = realTimeQuantizedInstant(env.headConfig.slotConfig).unsafeRunSync()

    /** The full evacuation map M to drain. */
    private val evacMap: EvacuationMap = fixed(genEvacuationMap(numEvacuees)(using env), 2)

    // Resolved treasury: accumulator = full-set commitment; value = base (beacon + min-ada +
    // buffer) + M.totalValue, so draining all of M leaves exactly `treasuryBaseValue`.
    private val resolvedDatum = Resolved(
      evacuationActive = evacMap.kzgCommitment,
      version = (BigInt(100), BigInt(2)),
      setupG2 = TrustedSetup
          .takeSrsG2(EvacuationTx.Assumptions.maxEvacuationsPerTx + 1)
          .map(p2 => G2Element(p2).toCompressedByteString)
    )
    private val treasuryBaseValue = Value(Coin.ada(5)) + treasuryToken + Value(Coin.ada(200))
    private val treasury = RuleBasedTreasuryUtxo(
      utxoId = TransactionInput(fallbackTxId, 0),
      treasuryOutput =
          RuleBasedTreasuryOutput(resolvedDatum, treasuryBaseValue + evacMap.totalValue)
    )

    // One fee utxo per evacuation step (each EvacuationTx spends its fee utxo); one shared
    // collateral (evacuation re-sends collateral rather than spending it).
    private val feeUtxos: List[Utxo] =
        (0 until numEvacuees).toList.map(i =>
            fixed(
              genPubKeyUtxo(address = ownAddr, genValue = Gen.const(Value.ada(100)))(using
                env.headConfig
              ),
              20L + i
            )
        )
    private val collateral = fixed(genCollateralUtxo(ownKeyHash)(using env.headConfig), 4)

    private val initialUtxos: Utxos = (
      Map(
        (treasury.utxoId, treasury.treasuryOutput.toOutput(using config)),
        (collateral.input, collateral.collateralOutput.toOutput(using env))
      )
          ++ feeUtxos.map(_.toTuple)
          ++ config.scriptReferenceUtxos.toList.map(_.toTuple)
    )

    /** Drain `remaining` one obligation at a time, branching over which obligation goes next.
      * Threads the produced treasury forward and accumulates the evacuated outputs. Returns the
      * final (fully-drained) treasury and every output paid out on this branch.
      */
    private def evacuateDown(
        remaining: EvacuationMap,
        treasury: RuleBasedTreasuryUtxo,
        depth: Int,
        evacuated: List[TransactionOutput]
    ): Scenario[(RuleBasedTreasuryUtxo, List[TransactionOutput])] =
        async[Scenario] {
            if remaining.isEmpty then (treasury, evacuated)
            else {
                val key = Scenario.fromCollection(remaining.keys.toList).await
                val subset = remaining.removedAll(remaining.keys.filter(_ != key))
                val evac = EvacuationTx
                    .Build(
                      inputTreasuryUtxo = treasury,
                      evacuateesToTryNext = subset,
                      allRemainingEvacuatees = remaining,
                      collateralUtxo = collateral,
                      feeUtxos = Map(feeUtxos(depth).toTuple)
                    )
                    .result(using config)
                    .toOption
                    .get
                val r = Scenario.submit(ownWallet.signTx(evac.tx)).await
                Scenario.guard(r.isRight).await
                // EvacuationTx hard-codes treasuryUtxoProduced.utxoId to output index 0, but the
                // residual treasury is not at index 0 (the collateral-return output precedes it), so
                // re-read the real treasury input from the emulator before chaining.
                val emu = Scenario.currentEmulator.await
                val newTreasury = evac.treasuryUtxoProduced.copy(utxoId = currentTreasuryInput(emu))
                evacuateDown(
                  remaining.removed(key),
                  newTreasury,
                  depth + 1,
                  evacuated ++ evac.evacuatedOutputs
                ).await
            }
        }

    private val scenario: Scenario[(RuleBasedTreasuryUtxo, List[TransactionOutput])] =
        evacuateDown(evacMap, treasury, 0, Nil)

    private def bag(xs: List[TransactionOutput]): Map[TransactionOutput, Int] =
        xs.groupBy(identity).view.mapValues(_.size).toMap

    test("evacuation drains the full map to exactly M, in any order") {
        val emulator0 = mkEmulator(initialUtxos, now.toSlot)
        val results =
            Await.result(Scenario.runAll(emulator0.toEmulator)(scenario), Duration(600, "s"))

        val expectedOrders = (1 to numEvacuees).product // N!
        val expectedOutputs = bag(evacMap.outputsCooked.toList)

        val _ = assert(
          results.size == expectedOrders,
          s"expected $expectedOrders evacuation orders ($numEvacuees!), got ${results.size}"
        )
        val _ = assert(
          results.forall { case (_, (finalTreasury, evacuated)) =>
              bag(evacuated) == expectedOutputs &&
              finalTreasury.treasuryOutput.value == treasuryBaseValue
          },
          "every order must pay out exactly M (distribution == M) and drain the treasury to its " +
              s"base value; got sizes ${results.map(_._2._2.size)}"
        )
    }

    /** Mirror the Mock execution model: single CardanoMutator under EvaluateAndComputeCost. */
    private def mkEmulator(initialUtxos: Utxos, slot: Slot): ImmutableEmulator =
        ImmutableEmulator(
          state = State(utxos = initialUtxos),
          env = UtxoEnv(
            slot.slot,
            env.headConfig.cardanoProtocolParams,
            certState = CertState.empty,
            env.headConfig.network
          ),
          slotConfig = env.headConfig.slotConfig,
          evaluatorMode = EvaluateAndComputeCost,
          validators = Seq.empty,
          mutators = Seq(CardanoMutator)
        )

    /** The current treasury input in the emulator (the single utxo at the treasury address). */
    private def currentTreasuryInput(emu: ImmutableEmulator): TransactionInput =
        emu.utxos.collectFirst { case (i, o) if o.address == treasuryAddr => i }.get
}
