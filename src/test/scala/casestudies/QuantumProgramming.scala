package test.casestudies

import restrictedfn.{Multiplicity, RestrictedSelectable, ops, unrestricted}
import RestrictedSelectable.{given, *}
import munit.FunSuite
import test.TestUtils

/**
 * Case Study: Quantum Programming
 *
 * In a quantum computing DSL, a function generating conditional branches based on
 * measurement outcomes requires each branch to use all qubits exactly once
 * (per-element linear) while allowing the same qubits to appear in multiple branch
 * definitions (global unrestricted), since only one branch will be executed at runtime.
 *
 * Multiplicities:
 *   ForEach = Linear        (each branch must use every qubit exactly once)
 *   ForAll  = Unrestricted  (branches are alternatives, not parallel compositions)
 */

@ops
class QState():
  /** Combine two qubit states into a joint circuit operation. */
  def combine(other: QState): QState = QState()
  /** Apply a named gate to this qubit (does not introduce new dependencies). */
  def gate(@unrestricted name: String): QState = QState()

object QState:
  def qubit(name: String): QState = QState()

// Connective: ForEach-Linear, ForAll-Unrestricted
type BranchConnective[RQT <: Tuple] =
  RestrictedSelectable.CustomConnective[RQT, Multiplicity.Linear, Multiplicity.Unrestricted]

object BranchConnective:
  def apply[K, RQT <: Tuple](values: RQT) =
    RestrictedSelectable.CustomConnective[RQT, Multiplicity.Linear, Multiplicity.Unrestricted](values)

object QuantumDSL:
  def condBranch[K, QT <: Tuple, RQT <: Tuple](
    qubits: QT
  )(fns: RestrictedSelectable.RestrictedFn.RestrictedFn[K, QT, BranchConnective[RQT]])(
    using
      builder: RestrictedSelectable.RestrictedFn.RestrictedFnBuilder[K, QT, BranchConnective[RQT]]
  ): RestrictedSelectable.ExtractResultTypes[RQT] =
    builder.execute(fns)(qubits)


class QuantumProgrammingTest extends FunSuite:
  import QStateOps.{given, *}

  test("Conditional branch: 2 qubits, 2 branches (each uses both qubits exactly once)") {
    val q0 = QState.qubit("q0")
    val q1 = QState.qubit("q1")

    val result = QuantumDSL.condBranch((q0, q1))((a, b) =>
      BranchConnective.apply((
        a.gate("H").combine(b.gate("X")),   // Branch |0>: H(q0), X(q1)
        a.gate("X").combine(b.gate("H"))    // Branch |1>: X(q0), H(q1)
      ))
    )
    assert(result != null)
  }

  test("Conditional branch: 2 qubits, 3 branches (all use both qubits)") {
    val q0 = QState.qubit("q0")
    val q1 = QState.qubit("q1")

    // ForAll-Unrestricted: same qubits appear in all 3 branches (alternatives)
    val result = QuantumDSL.condBranch((q0, q1))((a, b) =>
      BranchConnective.apply((
        a.gate("H").combine(b.gate("X")),
        a.gate("X").combine(b.gate("H")),
        a.combine(b)                         // CNOT(q0, q1)
      ))
    )
    assert(result != null)
  }

  test("NEGATIVE: Branch missing a qubit (ForEach-Linear violation)") {
    val obtained = compileErrors("""
      import QStateOps.{given, *}
      import restrictedfn.RestrictedSelectable.{given, *}

      val q0 = QState.qubit("q0")
      val q1 = QState.qubit("q1")

      // Should fail: second branch only uses q0, missing q1
      val result = QuantumDSL.condBranch((q0, q1))((a, b) =>
        BranchConnective.apply((
          a.gate("H").combine(b.gate("X")),
          a.gate("X")                         // VIOLATION: q1 not used in this branch!
        ))
      )
    """)
    assert(obtained.contains(TestUtils.noGivenInstance), s"obtained: $obtained")
  }

  test("NEGATIVE: Branch uses qubit twice (ForEach-Linear violation)") {
    val obtained = compileErrors("""
      import QStateOps.{given, *}
      import restrictedfn.RestrictedSelectable.{given, *}

      val q0 = QState.qubit("q0")
      val q1 = QState.qubit("q1")

      // Should fail: first branch uses q0 twice
      val result = QuantumDSL.condBranch((q0, q1))((a, b) =>
        BranchConnective.apply((
          a.combine(a).combine(b),            // VIOLATION: q0 used twice!
          a.combine(b)
        ))
      )
    """)
    assert(obtained.contains(TestUtils.noGivenInstance), s"obtained: $obtained")
  }
