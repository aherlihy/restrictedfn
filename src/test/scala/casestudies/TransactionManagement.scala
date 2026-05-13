package test.casestudies

import restrictedfn.{Multiplicity, RestrictedSelectable, ops}
import RestrictedSelectable.{given, *}
import munit.FunSuite
import test.TestUtils

/**
 * Case Study: Transaction Management
 *
 * In transaction systems, a function organizing work across parallel transactions
 * allows internal reuse within each transaction (per-element unrestricted) while
 * ensuring each resource is claimed by at most one transaction (global affine),
 * preventing write conflicts while permitting some resources to remain unaccessed.
 *
 * Multiplicities:
 *   ForEach = Unrestricted  (a transaction can freely use its assigned resources)
 *   ForAll  = Affine        (no two transactions may operate on the same resource)
 */

@ops
class Slot():
  /** Include another resource in the same transaction. */
  def include(other: Slot): Slot = Slot()

object Slot:
  def resource(name: String): Slot = Slot()

// Connective: ForEach-Unrestricted, ForAll-Affine
type ScheduleConnective[RQT <: Tuple] =
  RestrictedSelectable.CustomConnective[RQT, Multiplicity.Unrestricted, Multiplicity.Affine]

object ScheduleConnective:
  def apply[K, RQT <: Tuple](values: RQT) =
    RestrictedSelectable.CustomConnective[RQT, Multiplicity.Unrestricted, Multiplicity.Affine](values)

object TxnDSL:
  def schedule[K, RT <: Tuple, RQT <: Tuple](
    resources: RT
  )(fns: RestrictedSelectable.RestrictedFn.RestrictedFn[K, RT, ScheduleConnective[RQT]])(
    using
      builder: RestrictedSelectable.RestrictedFn.RestrictedFnBuilder[K, RT, ScheduleConnective[RQT]]
  ): RestrictedSelectable.ExtractResultTypes[RQT] =
    builder.execute(fns)(resources)


class TransactionManagementTest extends FunSuite:
  import SlotOps.{given, *}

  test("Schedule 2 resources into 2 transactions (disjoint)") {
    val r1 = Slot.resource("accounts")
    val r2 = Slot.resource("inventory")

    val result = TxnDSL.schedule((r1, r2))((a, b) =>
      ScheduleConnective.apply((a, b))
    )
    assert(result != null)
  }

  test("Schedule 3 resources into 2 transactions (one resource unused - affine allows weakening)") {
    val r1 = Slot.resource("accounts")
    val r2 = Slot.resource("inventory")
    val r3 = Slot.resource("logs")

    // ForAll-Affine: r3 is not claimed by any transaction (allowed — weakening)
    val result = TxnDSL.schedule((r1, r2, r3))((a, b, c) =>
      ScheduleConnective.apply((a, b))
    )
    assert(result != null)
  }

  test("Schedule 2 resources into 1 transaction (combine in single transaction)") {
    val r1 = Slot.resource("accounts")
    val r2 = Slot.resource("inventory")

    // ForEach-Unrestricted: a single transaction can reference multiple resources
    // ForAll-Affine: each resource appears in at most one transaction
    val result = TxnDSL.schedule((r1, r2))((a, b) =>
      ScheduleConnective.apply(Tuple1(a.include(b)))
    )
    assert(result != null)
  }

  test("NEGATIVE: Two transactions claim same resource (ForAll-Affine violation)") {
    val obtained = compileErrors("""
      import SlotOps.{given, *}
      import restrictedfn.RestrictedSelectable.{given, *}

      val r1 = Slot.resource("accounts")
      val r2 = Slot.resource("inventory")

      // Should fail: r1 is claimed by both txn1 and txn2
      val result = TxnDSL.schedule((r1, r2))((a, b) =>
        ScheduleConnective.apply((a, a.include(b)))
      )
    """)
    assert(obtained.contains(TestUtils.forAllAffineFailed), s"obtained: $obtained")
  }

  test("NEGATIVE: All resources assigned to same transaction (ForAll-Affine violation)") {
    val obtained = compileErrors("""
      import SlotOps.{given, *}
      import restrictedfn.RestrictedSelectable.{given, *}

      val r1 = Slot.resource("accounts")
      val r2 = Slot.resource("inventory")

      // Should fail: both r1 and r2 appear in both transactions
      val result = TxnDSL.schedule((r1, r2))((a, b) =>
        ScheduleConnective.apply((a.include(b), a.include(b)))
      )
    """)
    assert(obtained.contains(TestUtils.forAllAffineFailed), s"obtained: $obtained")
  }
