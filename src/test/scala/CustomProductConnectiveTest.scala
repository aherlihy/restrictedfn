package test

import restrictedfn.{Multiplicity,ops, restricted, restrictedReturn, unrestricted}
import restrictedfn.RestrictedSelectable.{given, *}
import munit.FunSuite

/*
 * Mixed Constraint Analysis
 * ==========================
 *
 * ComposedConnective has two multiplicity parameters:
 * - ForEach: Constraint applied to each return value individually
 * - ForAll: Constraint applied across all return values collectively
 *
 * Multiplicity meanings:
 * - Linear: exactly once
 * - Affine: at most once (0 or 1 times)
 * - Relevant: at least once (1 or more times)
 * - Unrestricted: no constraint (0 or more times)
 *
 * For N arguments and M returns:
 *
 * ForEach-Linear: In each return, each argument must be used exactly once
 *   - Valid: Each of M returns uses all N arguments exactly once
 *   - Example (N=2, M=2): ((p1.combine(p2), p2.combine(p1)))
 *
 * ForEach-Affine: In each return, each argument used at most once
 *   - Valid: Each return can omit arguments or use each at most once
 *   - Example (N=2, M=2): ((p1, p2)) or ((p1, EmptyValue))
 *
 * ForEach-Relevant: In each return, each argument must be used at least once
 *   - Valid: Each return uses all N arguments (possibly multiple times)
 *   - Example (N=2, M=2): ((p1.combine(p2), p1.combine(p1).combine(p2)))
 *
 * ForAll-Linear: Across all returns, each argument used exactly once total
 *   - Valid: The N arguments are distributed across M returns, each appearing exactly once
 *   - Example (N=2, M=2): ((p1, p2)) - p1 in first return, p2 in second
 *
 * ForAll-Affine: Across all returns, each argument used at most once total
 *   - Valid: Each argument appears in at most one return
 *   - Example (N=2, M=2): ((p1, p2)) or ((p1, EmptyValue))
 *
 * ForAll-Relevant: Across all returns, each argument used at least once total
 *   - Valid: Every argument appears in at least one return
 *   - Example (N=2, M=2): ((p1, p2)) or ((p1.combine(p2), p2))
 *
 * Combination Analysis (with concrete reasoning):
 *
 * 1. ForAll-Unrestricted + ForEach-X:
 *    - Always POSSIBLE: ForAll doesn't constrain, only ForEach matters
 *    - Arguments can be reused across returns freely
 *
 * 2. ForEach-Unrestricted + ForAll-X:
 *    - Always POSSIBLE: ForEach doesn't constrain, only ForAll matters
 *    - Returns can use arguments in any way
 *
 * 3. ForAll-Linear + ForEach-Linear (N=2, M=2):
 *    - ForEach-Linear: Each return must use p1 and p2 exactly once
 *    - This means p1 appears in BOTH returns (twice total)
 *    - ForAll-Linear: Each arg must appear exactly once total
 *    - CONTRADICTORY for M > 1. Only possible when M = 1.
 *
 * 4. ForAll-Linear + ForEach-Affine (N=2, M=2):
 *    - Example: ((p1, p2)) - p1 in first return, p2 in second
 *    - Each arg appears exactly once total ✓
 *    - Each return uses args at most once ✓
 *    - POSSIBLE ✓
 *
 * 5. ForAll-Linear + ForEach-Relevant (N=2, M=2):
 *    - ForEach-Relevant: Each return must use both p1 and p2
 *    - Each arg appears at least twice
 *    - ForAll-Linear: Each arg must appear exactly once total
 *    - CONTRADICTORY for M > 1. Only possible when M = 1.
 *
 * 6. ForAll-Affine + ForEach-Linear (N=2, M=2):
 *    - ForEach-Linear: Each return must use p1 and p2 exactly once
 *    - Each arg appears twice (once per return)
 *    - ForAll-Affine: Each arg can appear at most once total
 *    - CONTRADICTORY for M > 1. Only possible when M = 1.
 *
 * 7. ForAll-Affine + ForEach-Affine (N=2, M=2):
 *    - Example: ((p1, p2))
 *    - p1 appears once, p2 appears once ✓
 *    - Each return uses args at most once ✓
 *    - POSSIBLE ✓
 *
 * 8. ForAll-Affine + ForEach-Relevant (N=2, M=2):
 *    - ForEach-Relevant: Each return must use both p1 and p2
 *    - Each arg appears twice
 *    - ForAll-Affine: Each arg can appear at most once total
 *    - CONTRADICTORY for M > 1. Only possible when M = 1.
 *
 * 9. ForAll-Relevant + ForEach-Linear (N=2, M=2):
 *    - Example: ((p1.combine(p2), p2.combine(p1)))
 *    - Each return uses both args exactly once ✓
 *    - Each arg appears at least once (twice) ✓
 *    - POSSIBLE ✓
 *
 * 10. ForAll-Relevant + ForEach-Affine (N=2, M=2):
 *     - Example: ((p1, p2))
 *     - Each arg appears at least once ✓
 *     - Each return uses args at most once ✓
 *     - POSSIBLE ✓
 *
 * 11. ForAll-Relevant + ForEach-Relevant (N=2, M=2):
 *     - Example: ((p1.combine(p2), p1.combine(p2)))
 *     - Each return uses all args ✓
 *     - All args appear in at least one return ✓
 *     - POSSIBLE ✓
 *
 * Summary of POSSIBLE combinations (for M > 1):
 * - ForAll-Unrestricted + ForEach-{Linear, Affine, Relevant}
 * - ForEach-Unrestricted + ForAll-{Linear, Affine, Relevant}
 * - ForAll-Linear + ForEach-Affine
 * - ForAll-Affine + ForEach-Affine
 * - ForAll-Relevant + ForEach-{Linear, Affine, Relevant}
 */

@ops
class ProductConnectiveFns(val s: String):
  def higherOrderCombine(@restrictedReturn f: String => ProductConnectiveFns): ProductConnectiveFns =
    combine(f("hof"))
  def combine(other: ProductConnectiveFns): ProductConnectiveFns =
    new ProductConnectiveFns(s"${this.s} + ${other.s}")


type ForEachLinearConnective[RT <: Tuple] = CustomConnective[RT, Multiplicity.Linear, Multiplicity.Unrestricted]
object ForEachLinearConnective:
  def apply[RT <: Tuple]
  (values: RT): ForEachLinearConnective[RT] =
    CustomConnective[RT, Multiplicity.Linear, Multiplicity.Unrestricted](values)

type ForEachAffineConnective[RT <: Tuple] = CustomConnective[RT, Multiplicity.Affine, Multiplicity.Unrestricted]
object ForEachAffineConnective:
  def apply[RT <: Tuple]
  (values: RT): ForEachAffineConnective[RT] =
    CustomConnective[RT, Multiplicity.Affine, Multiplicity.Unrestricted](values)

type ForEachRelevantConnective[RT <: Tuple] = CustomConnective[RT, Multiplicity.Relevant, Multiplicity.Unrestricted]
object ForEachRelevantConnective:
  def apply[RT <: Tuple]
  (values: RT): ForEachRelevantConnective[RT] =
    CustomConnective[RT, Multiplicity.Relevant, Multiplicity.Unrestricted](values)

// Mixed constraint connectives
type ForEachAffineForAllLinearConnective[RT <: Tuple] = CustomConnective[RT, Multiplicity.Affine, Multiplicity.Linear]
object ForEachAffineForAllLinearConnective:
  def apply[RT <: Tuple](values: RT): ForEachAffineForAllLinearConnective[RT] =
    CustomConnective[RT, Multiplicity.Affine, Multiplicity.Linear](values)

type ForEachLinearForAllAffineConnective[RT <: Tuple] = CustomConnective[RT, Multiplicity.Linear, Multiplicity.Affine]
object ForEachLinearForAllAffineConnective:
  def apply[RT <: Tuple](values: RT): ForEachLinearForAllAffineConnective[RT] =
    CustomConnective[RT, Multiplicity.Linear, Multiplicity.Affine](values)

type ForEachAffineForAllAffineConnective[RT <: Tuple] = CustomConnective[RT, Multiplicity.Affine, Multiplicity.Affine]
object ForEachAffineForAllAffineConnective:
  def apply[RT <: Tuple](values: RT): ForEachAffineForAllAffineConnective[RT] =
    CustomConnective[RT, Multiplicity.Affine, Multiplicity.Affine](values)

type ForEachLinearForAllRelevantConnective[RT <: Tuple] = CustomConnective[RT, Multiplicity.Linear, Multiplicity.Relevant]
object ForEachLinearForAllRelevantConnective:
  def apply[RT <: Tuple](values: RT): ForEachLinearForAllRelevantConnective[RT] =
    CustomConnective[RT, Multiplicity.Linear, Multiplicity.Relevant](values)

type ForEachAffineForAllRelevantConnective[RT <: Tuple] = CustomConnective[RT, Multiplicity.Affine, Multiplicity.Relevant]
object ForEachAffineForAllRelevantConnective:
  def apply[RT <: Tuple](values: RT): ForEachAffineForAllRelevantConnective[RT] =
    CustomConnective[RT, Multiplicity.Affine, Multiplicity.Relevant](values)

type ForEachRelevantForAllRelevantConnective[RT <: Tuple] = CustomConnective[RT, Multiplicity.Relevant, Multiplicity.Relevant]
object ForEachRelevantForAllRelevantConnective:
  def apply[K, RT <: Tuple](values: RT): ForEachRelevantForAllRelevantConnective[RT] =
    CustomConnective[RT, Multiplicity.Relevant, Multiplicity.Relevant](values)

object ProductConnectiveFns:
  def forAllLinearFn[K, QT <: Tuple, RT <: Tuple](
    bases: QT
  )(fns: RestrictedFn.RestrictedFn[K, QT, ForAllLinearConnective[RT]])(
    using builder: RestrictedFn.RestrictedFnBuilder[K,
      QT,
      ForAllLinearConnective[RT]
    ]
  ): ExtractResultTypes[RT] =
    builder.execute(fns)(bases)

  def forEachLinearFn[K, QT <: Tuple, RT <: Tuple](
    bases: QT
  )(fns: RestrictedFn.RestrictedFn[K, QT, ForEachLinearConnective[RT]])(
    using builder: RestrictedFn.RestrictedFnBuilder[K,
      QT,
      ForEachLinearConnective[RT]
    ]
  ): ExtractResultTypes[RT] =
    builder.execute(fns)(bases)

  def forAllAffineFn[K, QT <: Tuple, RT <: Tuple](
    bases: QT
  )(fns: RestrictedFn.RestrictedFn[K, QT, ForAllAffineConnective[RT]])(
    using builder: RestrictedFn.RestrictedFnBuilder[K,
      QT,
      ForAllAffineConnective[RT]
    ]
  ): ExtractResultTypes[RT] =
    builder.execute(fns)(bases)

  def forEachAffineFn[K, QT <: Tuple, RT <: Tuple](
    bases: QT
  )(fns: RestrictedFn.RestrictedFn[K, QT, ForEachAffineConnective[RT]])(
    using builder: RestrictedFn.RestrictedFnBuilder[K,
      QT,
      ForEachAffineConnective[RT]
    ]
  ): ExtractResultTypes[RT] =
    builder.execute(fns)(bases)

  def forAllRelevantFn[K, QT <: Tuple, RT <: Tuple](
    bases: QT
  )(fns: RestrictedFn.RestrictedFn[K, QT, ForAllRelevantConnective[RT]])(
    using builder: RestrictedFn.RestrictedFnBuilder[K,
      QT,
      ForAllRelevantConnective[RT]
    ]
  ): ExtractResultTypes[RT] =
    builder.execute(fns)(bases)

  def forEachRelevantFn[K, QT <: Tuple, RT <: Tuple](
    bases: QT
  )(fns: RestrictedFn.RestrictedFn[K, QT, ForEachRelevantConnective[RT]])(
    using builder: RestrictedFn.RestrictedFnBuilder[K,
      QT,
      ForEachRelevantConnective[RT]
    ]
  ): ExtractResultTypes[RT] =
    builder.execute(fns)(bases)

  def forEachAffineForAllLinearFn[K, QT <: Tuple, RT <: Tuple](
    bases: QT
  )(fns: RestrictedFn.RestrictedFn[K, QT, ForEachAffineForAllLinearConnective[RT]])(
    using builder: RestrictedFn.RestrictedFnBuilder[K,
      QT,
      ForEachAffineForAllLinearConnective[RT]
    ]
  ): ExtractResultTypes[RT] =
    builder.execute(fns)(bases)

  def forEachLinearForAllAffineFn[K, QT <: Tuple, RT <: Tuple](
    bases: QT
  )(fns: RestrictedFn.RestrictedFn[K, QT, ForEachLinearForAllAffineConnective[RT]])(
    using builder: RestrictedFn.RestrictedFnBuilder[K,
      QT,
      ForEachLinearForAllAffineConnective[RT]
    ]
  ): ExtractResultTypes[RT] =
    builder.execute(fns)(bases)

  def forEachAffineForAllAffineFn[K, QT <: Tuple, RT <: Tuple](
    bases: QT
  )(fns: RestrictedFn.RestrictedFn[K, QT, ForEachAffineForAllAffineConnective[RT]])(
    using builder: RestrictedFn.RestrictedFnBuilder[K,
      QT,
      ForEachAffineForAllAffineConnective[RT]
    ]
  ): ExtractResultTypes[RT] =
    builder.execute(fns)(bases)

  def forEachLinearForAllRelevantFn[K, QT <: Tuple, RT <: Tuple](
    bases: QT
  )(fns: RestrictedFn.RestrictedFn[K, QT, ForEachLinearForAllRelevantConnective[RT]])(
    using builder: RestrictedFn.RestrictedFnBuilder[K,
      QT,
      ForEachLinearForAllRelevantConnective[RT]
    ]
  ): ExtractResultTypes[RT] =
    builder.execute(fns)(bases)

  def forEachAffineForAllRelevantFn[K, QT <: Tuple, RT <: Tuple](
    bases: QT
  )(fns: RestrictedFn.RestrictedFn[K, QT, ForEachAffineForAllRelevantConnective[RT]])(
    using builder: RestrictedFn.RestrictedFnBuilder[K,
      QT,
      ForEachAffineForAllRelevantConnective[RT]
    ]
  ): ExtractResultTypes[RT] =
    builder.execute(fns)(bases)

  def forEachRelevantForAllRelevantFn[K, QT <: Tuple, RT <: Tuple](
    bases: QT
  )(fns: RestrictedFn.RestrictedFn[K, QT, ForEachRelevantForAllRelevantConnective[RT]])(
    using builder: RestrictedFn.RestrictedFnBuilder[K,
      QT,
      ForEachRelevantForAllRelevantConnective[RT]
    ]
  ): ExtractResultTypes[RT] =
    builder.execute(fns)(bases)

class CustomProductConnectiveTest extends FunSuite:
  import ProductConnectiveFnsOps.*
  test("Custom Product Connective with for-all-linear, one combined result") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forAllLinearFn((pcTest1, pcTest2))((p1, p2) =>
      ForAllLinearConnective(Tuple1(p1.combine(p2)))
    )
    assertEquals(result._1.s, "a + b")
  }
  test("Custom Product Connective with for-all-linear, one combined HOF result") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forAllLinearFn((pcTest1, pcTest2))((p1, p2) =>
      ForAllLinearConnective(Tuple1(p1.higherOrderCombine((i) => p2)))
    )
    assertEquals(result._1.s, "a + b")
  }
  test("Custom Product Connective with for-all-linear, two uncombined results") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forAllLinearFn((pcTest1, pcTest2))((p1, p2) =>
      ForAllLinearConnective((p1, p2))
    )
    assertEquals(result._1.s, "a")
    assertEquals(result._2.s, "b")
  }
  test("NEGATIVE: ForAll-Linear not relevant - missing argument") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forAllLinearFn((pcTest1, pcTest2))((p1, p2) =>
        ForAllLinearConnective(Tuple1(p1))  // Error: p2 not used, violates relevant
      )
    """)
    assert(
      obtained.contains(TestUtils.forAllLinearFailed),
      s"Expected ForAll-Linear Relevant error but got: $obtained"
    )
  }

  test("NEGATIVE: ForAll-Linear not affine - argument used twice") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forAllLinearFn((pcTest1, pcTest2))((p1, p2) =>
        ForAllLinearConnective(Tuple1(p1.combine(p2).combine(p1)))  // Error: p1 used twice, violates affine
      )
    """)
    assert(
      obtained.contains(TestUtils.forAllLinearFailed),
      s"Expected ForAll-Linear Affine error but got: $obtained"
    )
  }

  test("NEGATIVE: ForAll-Linear not relevant and not affine") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forAllLinearFn((pcTest1, pcTest2))((p1, p2) =>
        ForAllLinearConnective(Tuple1(p1.combine(p1)))  // Error: p1 used twice, p2 not used
      )
    """)
    assert(
      obtained.contains(TestUtils.forAllLinearFailed),
      s"Expected ForAll-Linear error but got: $obtained"
    )
  }

  test("ForAll-Linear with multiple returns - each argument used exactly once") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val pcTest3 = new ProductConnectiveFns("c")
    val result = ProductConnectiveFns.forAllLinearFn((pcTest1, pcTest2, pcTest3))((p1, p2, p3) =>
      ForAllLinearConnective((p1, p2, p3))  // OK: each arg used exactly once across all returns
    )
    assertEquals(result._1.s, "a")
    assertEquals(result._2.s, "b")
    assertEquals(result._3.s, "c")
  }

  test("NEGATIVE: ForAll-Linear with multiple returns - argument appears in two returns") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forAllLinearFn((pcTest1, pcTest2))((p1, p2) =>
        ForAllLinearConnective((p1, p1))  // Error: p1 used twice (in both returns), p2 not used
      )
    """)
    assert(
      obtained.contains(TestUtils.forAllLinearFailed),
      s"Expected ForAll-Linear error but got: $obtained"
    )
  }
  test("Custom Product Connective with for-each-linear, one combined result") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forEachLinearFn((pcTest1, pcTest2))((p1, p2) =>
      ForEachLinearConnective(Tuple1(p1.combine(p2)))
    )
    assertEquals(result._1.s, "a + b")
  }
  test("NEGATIVE: ForEach-Linear not relevant - missing argument in return") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forEachLinearFn((pcTest1, pcTest2))((p1, p2) =>
        ForEachLinearConnective(Tuple1(p1))  // Error: p2 not in return, violates relevant
      )
    """)
    assert(
      obtained.contains(TestUtils.forEachLinearFailed),
      s"Expected ForEach-Linear Relevant error but got: $obtained"
    )
  }

  test("NEGATIVE: ForEach-Linear not affine - argument used twice in same return") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forEachLinearFn((pcTest1, pcTest2))((p1, p2) =>
        ForEachLinearConnective(Tuple1(p1.combine(p1)))  // Error: p1 used twice in return, violates affine
      )
    """)
    assert(
      obtained.contains(TestUtils.forEachLinearFailed),
      s"Expected ForEach-Linear Affine error but got: $obtained"
    )
  }
  test("Custom Product Connective with for-each-linear, one combined HOF result") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forEachLinearFn((pcTest1, pcTest2))((p1, p2) =>
      ForEachLinearConnective(Tuple1(p1.higherOrderCombine(i => p2)))
    )
    assertEquals(result._1.s, "a + b")
  }
  test("Custom Product Connective with for-each-linear, two combined results") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forEachLinearFn((pcTest1, pcTest2))((p1, p2) =>
      ForEachLinearConnective((p1.combine(p2), p2.combine(p1)))
    )
    assertEquals(result._1.s, "a + b")
    assertEquals(result._2.s, "b + a")
  }
  test("Custom Product Connective with for-each-linear, two combined HOF results") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forEachLinearFn((pcTest1, pcTest2))((p1, p2) =>
      ForEachLinearConnective((p1.higherOrderCombine(i => p2), p2.higherOrderCombine(i => p1)))
    )
    assertEquals(result._1.s, "a + b")
    assertEquals(result._2.s, "b + a")
  }

  test("ForEach-Linear with three returns - each must use all arguments exactly once") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val pcTest3 = new ProductConnectiveFns("c")
    val result = ProductConnectiveFns.forEachLinearFn((pcTest1, pcTest2, pcTest3))((p1, p2, p3) =>
      ForEachLinearConnective((
        p1.combine(p2).combine(p3),  // All three args used exactly once
        p2.combine(p3).combine(p1),  // All three args used exactly once
        p3.combine(p1).combine(p2)   // All three args used exactly once
      ))
    )
    assertEquals(result._1.s, "a + b + c")
    assertEquals(result._2.s, "b + c + a")
    assertEquals(result._3.s, "c + a + b")
  }

  test("NEGATIVE: ForEach-Linear with multiple returns - one return violates linear") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      val pcTest3 = new ProductConnectiveFns("c")
      ProductConnectiveFns.forEachLinearFn((pcTest1, pcTest2, pcTest3))((p1, p2, p3) =>
        ForEachLinearConnective((p1.combine(p2).combine(p3), p1.combine(p2)))  // Error: second return missing p3
      )
    """)
    assert(
      obtained.contains(TestUtils.forEachLinearFailed),
      s"Expected ForEach-Linear Relevant error but got: $obtained"
    )
  }

  // ForAllAffine tests
  test("Custom Product Connective with for-all-affine, one combined result") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forAllAffineFn((pcTest1, pcTest2))((p1, p2) =>
      ForAllAffineConnective(Tuple1(p1.combine(p2)))
    )
    assertEquals(result._1.s, "a + b")
  }

  test("Custom Product Connective with for-all-affine, two uncombined results") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forAllAffineFn((pcTest1, pcTest2))((p1, p2) =>
      ForAllAffineConnective((p1, p2))
    )
    assertEquals(result._1.s, "a")
    assertEquals(result._2.s, "b")
  }

  test("NEGATIVE: ForAll-Affine not affine - argument used twice") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forAllAffineFn((pcTest1, pcTest2))((p1, p2) =>
        ForAllAffineConnective(Tuple1(p1.combine(p2).combine(p1)))  // Error: p1 used twice, violates affine
      )
    """)
    assert(
      obtained.contains(TestUtils.forAllAffineFailed),
      s"Expected ForAll-Affine error but got: $obtained"
    )
  }

  test("ForAll-Affine allows missing argument") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forAllAffineFn((pcTest1, pcTest2))((p1, p2) =>
      ForAllAffineConnective(Tuple1(p1))  // OK: p2 not used, affine doesn't require relevant
    )
    assertEquals(result._1.s, "a")
  }

  test("ForAll-Affine allows each argument used once across different returns") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val pcTest3 = new ProductConnectiveFns("c")
    val result = ProductConnectiveFns.forAllAffineFn((pcTest1, pcTest2, pcTest3))((p1, p2, p3) =>
      ForAllAffineConnective((p1, p2, p3))  // OK: each arg used exactly once across all returns
    )
    assertEquals(result._1.s, "a")
    assertEquals(result._2.s, "b")
    assertEquals(result._3.s, "c")
  }

  test("NEGATIVE: ForAll-Affine with multiple returns - argument used in two different returns") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forAllAffineFn((pcTest1, pcTest2))((p1, p2) =>
        ForAllAffineConnective((p1, p1))  // Error: p1 used in both returns, violates affine
      )
    """)
    assert(
      obtained.contains(TestUtils.forAllAffineFailed),
      s"Expected ForAll-Affine error but got: $obtained"
    )
  }

  // ForEachAffine tests
  test("Custom Product Connective with for-each-affine, one combined result") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forEachAffineFn((pcTest1, pcTest2))((p1, p2) =>
      ForEachAffineConnective(Tuple1(p1.combine(p2)))
    )
    assertEquals(result._1.s, "a + b")
  }

  test("Custom Product Connective with for-each-affine, two combined results") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forEachAffineFn((pcTest1, pcTest2))((p1, p2) =>
      ForEachAffineConnective((p1.combine(p2), p2.combine(p1)))
    )
    assertEquals(result._1.s, "a + b")
    assertEquals(result._2.s, "b + a")
  }

  test("NEGATIVE: ForEach-Affine not affine - argument used twice in same return") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forEachAffineFn((pcTest1, pcTest2))((p1, p2) =>
        ForEachAffineConnective(Tuple1(p1.combine(p1)))  // Error: p1 used twice in return, violates affine
      )
    """)
    assert(
      obtained.contains(TestUtils.forEachAffineFailed),
      s"Expected ForEach-Affine error but got: $obtained"
    )
  }

  test("ForEach-Affine allows missing argument in return") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forEachAffineFn((pcTest1, pcTest2))((p1, p2) =>
      ForEachAffineConnective(Tuple1(p1))  // OK: p2 not in return, affine doesn't require relevant
    )
    assertEquals(result._1.s, "a")
  }

  test("ForEach-Affine with three returns - each uses different subset") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val pcTest3 = new ProductConnectiveFns("c")
    val result = ProductConnectiveFns.forEachAffineFn((pcTest1, pcTest2, pcTest3))((p1, p2, p3) =>
      ForEachAffineConnective((p1.combine(p2), p2.combine(p3), p1.combine(p3)))  // OK: no duplicates within each return
    )
    assertEquals(result._1.s, "a + b")
    assertEquals(result._2.s, "b + c")
    assertEquals(result._3.s, "a + c")
  }

  test("NEGATIVE: ForEach-Affine with multiple returns - one return has duplicate") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forEachAffineFn((pcTest1, pcTest2))((p1, p2) =>
        ForEachAffineConnective((p1.combine(p2), p1.combine(p1)))  // Error: second return uses p1 twice
      )
    """)
    assert(
      obtained.contains(TestUtils.forEachAffineFailed),
      s"Expected ForEach-Affine error but got: $obtained"
    )
  }

  // ForAllRelevant tests
  test("Custom Product Connective with for-all-relevant, one combined result") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forAllRelevantFn((pcTest1, pcTest2))((p1, p2) =>
      ForAllRelevantConnective(Tuple1(p1.combine(p2)))
    )
    assertEquals(result._1.s, "a + b")
  }

  test("Custom Product Connective with for-all-relevant, two uncombined results") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forAllRelevantFn((pcTest1, pcTest2))((p1, p2) =>
      ForAllRelevantConnective((p1, p2))
    )
    assertEquals(result._1.s, "a")
    assertEquals(result._2.s, "b")
  }

  test("NEGATIVE: ForAll-Relevant not relevant - missing argument") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forAllRelevantFn((pcTest1, pcTest2))((p1, p2) =>
        ForAllRelevantConnective(Tuple1(p1))  // Error: p2 not used, violates relevant
      )
    """)
    assert(
      obtained.contains(TestUtils.forAllRelevantFailed),
      s"Expected ForAll-Relevant error but got: $obtained"
    )
  }

  test("ForAll-Relevant allows argument used twice") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forAllRelevantFn((pcTest1, pcTest2))((p1, p2) =>
      ForAllRelevantConnective(Tuple1(p1.combine(p2).combine(p1)))  // OK: p1 used twice, relevant doesn't require affine
    )
    assertEquals(result._1.s, "a + b + a")
  }

  test("ForAll-Relevant with multiple returns - allows argument reuse across returns") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val pcTest3 = new ProductConnectiveFns("c")
    val result = ProductConnectiveFns.forAllRelevantFn((pcTest1, pcTest2, pcTest3))((p1, p2, p3) =>
      ForAllRelevantConnective((p1.combine(p2), p2.combine(p3), p1.combine(p3)))  // OK: all args used, reuse allowed
    )
    assertEquals(result._1.s, "a + b")
    assertEquals(result._2.s, "b + c")
    assertEquals(result._3.s, "a + c")
  }

  test("NEGATIVE: ForAll-Relevant with multiple returns - one argument never used") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      val pcTest3 = new ProductConnectiveFns("c")
      ProductConnectiveFns.forAllRelevantFn((pcTest1, pcTest2, pcTest3))((p1, p2, p3) =>
        ForAllRelevantConnective((p1, p1))  // Error: p2 and p3 never used
      )
    """)
    assert(
      obtained.contains(TestUtils.forAllRelevantFailed),
      s"Expected ForAll-Relevant error but got: $obtained"
    )
  }

  // ForEachRelevant tests
  test("Custom Product Connective with for-each-relevant, one combined result") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forEachRelevantFn((pcTest1, pcTest2))((p1, p2) =>
      ForEachRelevantConnective(Tuple1(p1.combine(p2)))
    )
    assertEquals(result._1.s, "a + b")
  }

  test("Custom Product Connective with for-each-relevant, two combined results") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forEachRelevantFn((pcTest1, pcTest2))((p1, p2) =>
      ForEachRelevantConnective((p1.combine(p2), p2.combine(p1)))
    )
    assertEquals(result._1.s, "a + b")
    assertEquals(result._2.s, "b + a")
  }

  test("NEGATIVE: ForEach-Relevant not relevant - missing argument in return") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forEachRelevantFn((pcTest1, pcTest2))((p1, p2) =>
        ForEachRelevantConnective(Tuple1(p1))  // Error: p2 not in return, violates relevant
      )
    """)
    assert(
      obtained.contains(TestUtils.forEachRelevantFailed),
      s"Expected ForEach-Relevant error but got: $obtained"
    )
  }

  test("ForEach-Relevant allows argument used twice in same return") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forEachRelevantFn((pcTest1, pcTest2))((p1, p2) =>
      ForEachRelevantConnective(Tuple1(p1.combine(p2).combine(p1)))  // OK: p1 used twice, relevant doesn't require affine
    )
    assertEquals(result._1.s, "a + b + a")
  }

  test("ForEach-Relevant with three returns - each must use all arguments") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val pcTest3 = new ProductConnectiveFns("c")
    val result = ProductConnectiveFns.forEachRelevantFn((pcTest1, pcTest2, pcTest3))((p1, p2, p3) =>
      ForEachRelevantConnective((
        p1.combine(p2).combine(p3),  // All three args
        p2.combine(p1).combine(p3),  // All three args
        p3.combine(p1).combine(p2)   // All three args
      ))
    )
    assertEquals(result._1.s, "a + b + c")
    assertEquals(result._2.s, "b + a + c")
    assertEquals(result._3.s, "c + a + b")
  }

  test("NEGATIVE: ForEach-Relevant with multiple returns - one return missing an argument") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      val pcTest3 = new ProductConnectiveFns("c")
      ProductConnectiveFns.forEachRelevantFn((pcTest1, pcTest2, pcTest3))((p1, p2, p3) =>
        ForEachRelevantConnective((p1.combine(p2).combine(p3), p1.combine(p2)))  // Error: second return missing p3
      )
    """)
    assert(
      obtained.contains(TestUtils.forEachRelevantFailed),
      s"Expected ForEach-Relevant error but got: $obtained"
    )
  }

  // ============================================================================
  // Mixed Constraint Tests: ForAll with ForEach constraints
  // ============================================================================

  // ForAll-Unrestricted with ForEach-Linear
  test("Mixed: ForAll-Unrestricted ForEach-Linear - allows argument reuse across returns") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forEachLinearFn((pcTest1, pcTest2))((p1, p2) =>
      ForEachLinearConnective((p1.combine(p2), p2.combine(p1)))  // OK: each return uses both args exactly once
    )
    assertEquals(result._1.s, "a + b")
    assertEquals(result._2.s, "b + a")
  }

  test("NEGATIVE: Mixed ForAll-Unrestricted ForEach-Linear - one return violates linear") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forEachLinearFn((pcTest1, pcTest2))((p1, p2) =>
        ForEachLinearConnective(Tuple1(p1.combine(p1)))  // Error: p1 used twice in same return
      )
    """)
    assert(
      obtained.contains(TestUtils.forEachLinearFailed),
      s"Expected ForEach-Linear error but got: $obtained"
    )
  }

  // ForAll-Unrestricted with ForEach-Affine
  test("Mixed: ForAll-Unrestricted ForEach-Affine - allows missing args and reuse across returns") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forEachAffineFn((pcTest1, pcTest2))((p1, p2) =>
      ForEachAffineConnective((p1, p2))  // OK: each return uses each arg at most once
    )
    assertEquals(result._1.s, "a")
    assertEquals(result._2.s, "b")
  }

  test("NEGATIVE: Mixed ForAll-Unrestricted ForEach-Affine - duplicate in return") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forEachAffineFn((pcTest1, pcTest2))((p1, p2) =>
        ForEachAffineConnective(Tuple1(p1.combine(p1)))  // Error: p1 used twice in same return
      )
    """)
    assert(
      obtained.contains(TestUtils.forEachAffineFailed),
      s"Expected ForEach-Affine error but got: $obtained"
    )
  }

  // ForAll-Unrestricted with ForEach-Relevant
  test("Mixed: ForAll-Unrestricted ForEach-Relevant - allows argument reuse across returns") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forEachRelevantFn((pcTest1, pcTest2))((p1, p2) =>
      ForEachRelevantConnective((p1.combine(p2), p2.combine(p1)))  // OK: each return uses all args
    )
    assertEquals(result._1.s, "a + b")
    assertEquals(result._2.s, "b + a")
  }

  test("NEGATIVE: Mixed ForAll-Unrestricted ForEach-Relevant - missing arg in return") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forEachRelevantFn((pcTest1, pcTest2))((p1, p2) =>
        ForEachRelevantConnective(Tuple1(p1))  // Error: p2 not used in return
      )
    """)
    assert(
      obtained.contains(TestUtils.forEachRelevantFailed),
      s"Expected ForEach-Relevant error but got: $obtained"
    )
  }

  // ============================================================================
  // Mixed Constraint Tests: ForEach with ForAll constraints
  // ============================================================================

  // ForEach-Unrestricted with ForAll-Linear
  test("Mixed: ForEach-Unrestricted ForAll-Linear - each arg used exactly once across all returns") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forAllLinearFn((pcTest1, pcTest2))((p1, p2) =>
      ForAllLinearConnective((p1, p2))  // OK: each arg used exactly once across all returns
    )
    assertEquals(result._1.s, "a")
    assertEquals(result._2.s, "b")
  }

  test("NEGATIVE: Mixed ForEach-Unrestricted ForAll-Linear - arg used in multiple returns") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forAllLinearFn((pcTest1, pcTest2))((p1, p2) =>
        ForAllLinearConnective((p1, p1))  // Error: p1 used twice across returns, p2 not used
      )
    """)
    assert(
      obtained.contains(TestUtils.forAllLinearFailed),
      s"Expected ForAll-Linear error but got: $obtained"
    )
  }

  // ForEach-Unrestricted with ForAll-Affine
  test("Mixed: ForEach-Unrestricted ForAll-Affine - no arg used more than once across all returns") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forAllAffineFn((pcTest1, pcTest2))((p1, p2) =>
      ForAllAffineConnective((p1, p2))  // OK: each arg used at most once across all returns
    )
    assertEquals(result._1.s, "a")
    assertEquals(result._2.s, "b")
  }

  test("NEGATIVE: Mixed ForEach-Unrestricted ForAll-Affine - arg appears in multiple returns") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forAllAffineFn((pcTest1, pcTest2))((p1, p2) =>
        ForAllAffineConnective((p1, p1))  // Error: p1 appears in both returns
      )
    """)
    assert(
      obtained.contains(TestUtils.forAllAffineFailed),
      s"Expected ForAll-Affine error but got: $obtained"
    )
  }

  // ForEach-Unrestricted with ForAll-Relevant
  test("Mixed: ForEach-Unrestricted ForAll-Relevant - all args used at least once across all returns") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forAllRelevantFn((pcTest1, pcTest2))((p1, p2) =>
      ForAllRelevantConnective((p1, p2))  // OK: both args used at least once
    )
    assertEquals(result._1.s, "a")
    assertEquals(result._2.s, "b")
  }

  test("NEGATIVE: Mixed ForEach-Unrestricted ForAll-Relevant - arg never used") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forAllRelevantFn((pcTest1, pcTest2))((p1, p2) =>
        ForAllRelevantConnective(Tuple1(p1))  // Error: p2 never used across all returns
      )
    """)
    assert(
      obtained.contains(TestUtils.forAllRelevantFailed),
      s"Expected ForAll-Relevant error but got: $obtained"
    )
  }

  // ============================================================================
  // Both constrained: ForAll and ForEach both have non-Unrestricted constraints
  // ============================================================================
  // Note: Many combinations are contradictory for M > 1. See analysis at top of file.

  // ForAll-Linear + ForEach-Affine
  test("Both constrained: ForAll-Linear ForEach-Affine") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forEachAffineForAllLinearFn((pcTest1, pcTest2))((p1, p2) =>
      ForEachAffineForAllLinearConnective((p1, p2))  // OK: each arg used exactly once total, at most once per return
    )
    assertEquals(result._1.s, "a")
    assertEquals(result._2.s, "b")
  }

  test("NEGATIVE: Both constrained ForAll-Linear ForEach-Affine - violates ForAll-Linear") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forEachAffineForAllLinearFn((pcTest1, pcTest2))((p1, p2) =>
        ForEachAffineForAllLinearConnective((p1, p1))  // Error: p1 used twice total, p2 never used
      )
    """)
    assert(
      obtained.contains(TestUtils.forAllLinearFailed),
      s"Expected ForAll-Linear error but got: $obtained"
    )
  }

  // ForAll-Affine + ForEach-Affine
  test("Both constrained: ForAll-Affine ForEach-Affine") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forEachAffineForAllAffineFn((pcTest1, pcTest2))((p1, p2) =>
      ForEachAffineForAllAffineConnective((p1, p2))  // OK: each arg used at most once per return and at most once total
    )
    assertEquals(result._1.s, "a")
    assertEquals(result._2.s, "b")
  }

  test("NEGATIVE: Both constrained ForAll-Affine ForEach-Affine - violates ForAll-Affine") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forEachAffineForAllAffineFn((pcTest1, pcTest2))((p1, p2) =>
        ForEachAffineForAllAffineConnective((p1, p1))  // Error: p1 appears in both returns
      )
    """)
    assert(
      obtained.contains(TestUtils.forAllAffineFailed),
      s"Expected ForAll-Affine error but got: $obtained"
    )
  }

  // ForAll-Relevant + ForEach-Linear
  test("Both constrained: ForAll-Relevant ForEach-Linear") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forEachLinearForAllRelevantFn((pcTest1, pcTest2))((p1, p2) =>
      ForEachLinearForAllRelevantConnective((p1.combine(p2), p2.combine(p1)))  // OK: each return uses all args exactly once
    )
    assertEquals(result._1.s, "a + b")
    assertEquals(result._2.s, "b + a")
  }

  test("NEGATIVE: Both constrained ForAll-Relevant ForEach-Linear - violates ForAll-Relevant") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      val pcTest3 = new ProductConnectiveFns("c")
      ProductConnectiveFns.forEachLinearForAllRelevantFn((pcTest1, pcTest2, pcTest3))((p1, p2, p3) =>
        ForEachLinearForAllRelevantConnective((p1.combine(p2), p2.combine(p1)))  // Error: p3 never used
      )
    """)
    assert(
      obtained.contains(TestUtils.forAllRelevantFailed),
      s"Expected ForAll-Relevant error but got: $obtained"
    )
  }

  // ForAll-Relevant + ForEach-Affine
  test("Both constrained: ForAll-Relevant ForEach-Affine") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forEachAffineForAllRelevantFn((pcTest1, pcTest2))((p1, p2) =>
      ForEachAffineForAllRelevantConnective((p1, p2))  // OK: all args appear, each used at most once per return
    )
    assertEquals(result._1.s, "a")
    assertEquals(result._2.s, "b")
  }

  test("NEGATIVE: Both constrained ForAll-Relevant ForEach-Affine - violates ForAll-Relevant") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forEachAffineForAllRelevantFn((pcTest1, pcTest2))((p1, p2) =>
        ForEachAffineForAllRelevantConnective(Tuple1(p1))  // Error: p2 never used
      )
    """)
    assert(
      obtained.contains(TestUtils.forAllRelevantFailed),
      s"Expected ForAll-Relevant error but got: $obtained"
    )
  }

  // ForAll-Relevant + ForEach-Relevant
  test("Both constrained: ForAll-Relevant ForEach-Relevant") {
    val pcTest1 = new ProductConnectiveFns("a")
    val pcTest2 = new ProductConnectiveFns("b")
    val result = ProductConnectiveFns.forEachRelevantForAllRelevantFn((pcTest1, pcTest2))((p1, p2) =>
      ForEachRelevantForAllRelevantConnective((p1.combine(p2), p1.combine(p2)))  // OK: all args appear, each return uses all args
    )
    assertEquals(result._1.s, "a + b")
    assertEquals(result._2.s, "a + b")
  }

  test("NEGATIVE: Both constrained ForAll-Relevant ForEach-Relevant - violates ForEach-Relevant") {
    val obtained = compileErrors("""
      import ProductConnectiveFnsOps.*
      val pcTest1 = new ProductConnectiveFns("a")
      val pcTest2 = new ProductConnectiveFns("b")
      ProductConnectiveFns.forEachRelevantForAllRelevantFn((pcTest1, pcTest2))((p1, p2) =>
        ForEachRelevantForAllRelevantConnective((p1.combine(p2), p1))  // Error: second return doesn't use p2
      )
    """)
    assert(
      obtained.contains(TestUtils.forEachRelevantFailed),
      s"Expected ForEach-Relevant error but got: $obtained"
    )
  }
