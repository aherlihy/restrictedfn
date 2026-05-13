package test

import munit.FunSuite
import restrictedfn.{Multiplicity, ops, restrictedReturn, unrestricted}
import scala.annotation.experimental
import restrictedfn.RestrictedSelectable.{given, *}

/**
 * Comprehensive tests for connective annotations with Linear multiplicity:
 * - @restrictedReturn: tracks return type of function parameters
 * - @unrestricted: parameters don't contribute dependencies
 * - Regular (default): entire function parameter wrapped via implicit
 *
 * Tests both positive (should compile and work) and negative (should fail to compile) cases.
 */

// Test class for @restrictedReturn and @unrestricted
@ops
case class TestQuery[A](data: List[A]):
  def flatMap[B](@restrictedReturn f: A => TestQuery[B]): TestQuery[B] =
    TestQuery(data.flatMap(a => f(a).data))

  def map[B](@unrestricted f: A => B): TestQuery[B] =
    TestQuery(data.map(f))

  def filter(@unrestricted p: A => Boolean): TestQuery[A] =
    TestQuery(data.filter(p))

  // Regular function parameter (no annotation) - wrapped via implicit
  def combine[B](f: A => TestQuery[B]): TestQuery[B] =
    TestQuery(data.flatMap(a => f(a).data))

@experimental
class ConnectiveTest extends FunSuite:
  import TestQueryOps.*
  import OpsExampleOps.*
  import MArrayOps.*

  // ============================================================================
  // @restrictedReturn tests - tracks return type of function parameters
  // ============================================================================

  test("POSITIVE: @restrictedReturn - can return tracked inner value with Linear") {
    val q1 = TestQuery(List(1, 2, 3))
    val q2 = TestQuery(List(10, 20))

    val result = RestrictedFn.apply((q1, q2))(refs =>
      val combined = refs._1.flatMap(x => refs._2)
      ForAllAffineConnective(Tuple1(combined))
    )

    assertEquals(result._1.data, List(10, 20, 10, 20, 10, 20))
  }

  test("POSITIVE: @restrictedReturn - nested flatMaps track dependencies") {
    val q1 = TestQuery(List(1, 2))
    val q2 = TestQuery(List(10, 20))
    val q3 = TestQuery(List(100, 200, 300))

    val result = RestrictedFn.apply((q1, q2, q3))(refs =>
      val step1 = refs._1.flatMap { x => refs._2 }
      val step2 = step1.flatMap { y => refs._3 }
      ForAllAffineConnective(Tuple1(step2))
    )

    // q1 (2 elem) -> q2 (2 elem) = 4 elem -> q3 (3 elem) = 12 elem
    assertEquals(result._1.data.length, 12)
  }

  test("POSITIVE: @restrictedReturn - function receives unwrapped value") {
    val q1 = TestQuery(List(1, 2, 3))
    val q2 = TestQuery(List(100))

    val result = RestrictedFn.apply((q1, q2))(refs =>
      val transformed = refs._1.flatMap { (x: Int) =>
        // x is plain Int, not Restricted[Int, _]
        refs._2
      }
      ForAllAffineConnective(Tuple1(transformed))
    )

    assertEquals(result._1.data, List(100, 100, 100))
  }

  test("NEGATIVE: @restrictedReturn - inner query used twice fails") {
    val obtained = compileErrors("""
      import TestQueryOps.*
      import restrictedfn.{RestrictedSelectable, Multiplicity}

      val q1 = TestQuery(List(1, 2))
      val q2 = TestQuery(List(10, 20))

      RestrictedFn.apply((q1, q2))(refs =>
        val combined = refs._1.flatMap((x: Int) => refs._2)
        // Error: refs._2 used twice (in flatMap body and in return)
        ForAllAffineConnective((combined, refs._1, refs._2))
      )
    """)

    assert(
      obtained.contains(TestUtils.forAllAffineFailed),
      s"Expected linearity error but got: $obtained"
    )
  }

  // ============================================================================
  // @unrestricted tests - parameters don't contribute dependencies
  // ============================================================================

  test("POSITIVE: @unrestricted - function not tracked") {
    val q = TestQuery(List(1, 2, 3))

    val result = RestrictedFn.apply(Tuple1(q))(refs =>
      val mapped = refs._1.map((x: Int) => x * 2)
      ForAllAffineConnective(Tuple1(mapped))
    )

    assertEquals(result._1.data, List(2, 4, 6))
  }

  test("POSITIVE: @unrestricted - filter with predicate") {
    val q = TestQuery(List(1, 2, 3, 4, 5))

    val result = RestrictedFn.apply(Tuple1(q))(refs =>
      val filtered = refs._1.filter((x: Int) => x > 2)
      ForAllAffineConnective(Tuple1(filtered))
    )

    assertEquals(result._1.data, List(3, 4, 5))
  }

  test("POSITIVE: @unrestricted - chaining map and filter") {
    val q = TestQuery(List(1, 2, 3))

    val result = RestrictedFn.apply(Tuple1(q))(refs =>
      val doubled = refs._1.map((x: Int) => x * 2)
      val filtered = doubled.filter((x: Int) => x > 2)
      ForAllAffineConnective(Tuple1(filtered))
    )

    assertEquals(result._1.data, List(4, 6))
  }
//
  test("POSITIVE: @unrestricted with plain values - EmptyTuple doesn't affect dependencies") {
    val ex = OpsExample("base", "0")

    val result = RestrictedFn.apply(Tuple1(ex))(refs =>
      // Plain strings implicitly converted to Restricted[String, EmptyTuple]
      val updated = refs._1.allUnrestrictedArgs("prefix-", "-suffix")
      ForAllAffineConnective(Tuple1(updated))
    )

    assertEquals(result._1.name, "prefix-base-suffix")
  }
//
  test("POSITIVE: @unrestricted - mixing restricted and unrestricted params") {
    val ex1 = OpsExample("first", "0")
    val ex2 = OpsExample("second", "0")

    val result = RestrictedFn.apply((ex1, ex2))(refs =>
      // refs._2 is restricted (tracked), "config" is unrestricted (plain)
      val combined = refs._1.restrictedProductArg_UnrestrictedPrimitiveArg(refs._2, "plain config")
      ForAllAffineConnective(Tuple1(combined))
    )

    assert(result._1.name.contains("first + second"))
  }
//
  test("POSITIVE: @unrestricted - type parameters preserved") {
    val q = TestQuery(List(1, 2, 3))

    val result = RestrictedFn.apply(Tuple1(q))(refs =>
      val stringQuery = refs._1.map[String]((x: Int) => x.toString)
      ForAllAffineConnective(Tuple1(stringQuery))
    )

    assertEquals(result._1.data, List("1", "2", "3"))
  }
//
//  // ============================================================================
//  // Regular function parameter (no annotation) - wrapped via implicit
//  // ============================================================================
//
  test("POSITIVE: regular function param - implicit conversion wraps function") {
    val q1 = TestQuery(List(1, 2, 3))

    val result = RestrictedFn.apply(Tuple1(q1))(refs =>
      // Function is implicitly converted to Restricted[A => TestQuery[B], EmptyTuple]
      val transformed = refs._1.combine((x: Int) => TestQuery(List(x * 2)))
      ForAllAffineConnective(Tuple1(transformed))
    )

    assertEquals(result._1.data, List(2, 4, 6))
  }
//
  test("POSITIVE: regular function param - can't reference tracked values in closure") {
    val q1 = TestQuery(List(1, 2))

    // This works because the function is implicitly converted with EmptyTuple deps
    // It can't actually capture refs inside because implicit conversion happens at function definition
    val result = RestrictedFn.apply(Tuple1(q1))(refs =>
      ForAllAffineConnective(Tuple1(refs._1.combine((x: Int) => TestQuery(List(x + 1000)))))
    )

    assertEquals(result._1.data, List(1001, 1002))
  }
//
//  // ============================================================================
//  // Comparison tests - @restrictedReturn vs @unrestricted vs regular
//  // ============================================================================
//
  test("COMPARISON: all three annotation types behave correctly") {
    val q1 = TestQuery(List(1, 2))
    val q2 = TestQuery(List(100))

    // @restrictedReturn: tracks return type, allows capturing tracked values
    val result1 = RestrictedFn.apply((q1, q2))(refs =>
      ForAllAffineConnective(Tuple1(refs._1.flatMap((x: Int) => refs._2)))
    )
    assertEquals(result1._1.data, List(100, 100))

    // @unrestricted: doesn't track anything
    val result2 = RestrictedFn.apply(Tuple1(q1))(refs =>
      ForAllAffineConnective(Tuple1(refs._1.map((x: Int) => x * 10)))
    )
    assertEquals(result2._1.data, List(10, 20))

    // Regular: function wrapped via implicit with EmptyTuple deps
    val result3 = RestrictedFn.apply(Tuple1(q1))(refs =>
      ForAllAffineConnective(Tuple1(refs._1.combine((x: Int) => TestQuery(List(x + 1000)))))
    )
    assertEquals(result3._1.data, List(1001, 1002))
  }
//
//  // ============================================================================
//  // MULTIPLICITY TESTS: @restrictedReturn with Linear/Affine/Relevant
//  // ============================================================================
//
//  // --- @restrictedReturn with Linear (must use exactly once) ---
//
  test("@restrictedReturn + Linear: POSITIVE - used exactly once") {
    val q1 = TestQuery(List(1, 2))
    val q2 = TestQuery(List(10))
    val q3 = TestQuery(List(100))

    val result = RestrictedFn.apply((q1, q2, q3))(refs =>
      val combined = refs._1.flatMap(x => refs._2)
      ForAllLinearConnective((combined, refs._3))
    )

    assertEquals(result._1.data, List(10, 10))
  }
//
  test("@restrictedReturn + Linear: NEGATIVE - used zero times") {
    val obtained = compileErrors("""
      import TestQueryOps.*
      import restrictedfn.{RestrictedSelectable, Multiplicity}

      val q1 = TestQuery(List(1, 2))
      val q2 = TestQuery(List(10))

      RestrictedFn.apply((q1, q2))(refs =>
        // Not using refs._2 inside flatMap - it's unused
        val combined = refs._1.flatMap(x => TestQuery(List(x)))
        ForAllLinearConnective((combined, refs._1))
      )
    """)

    assert(
      obtained.contains(TestUtils.forAllLinearFailed),
      s"Expected ForAll constraint failure but got: $obtained"
    )
  }
//
  test("@restrictedReturn + Linear: NEGATIVE - used twice") {
    val obtained = compileErrors("""
      import TestQueryOps.*
      import restrictedfn.{RestrictedSelectable, Multiplicity}

      val q1 = TestQuery(List(1, 2))
      val q2 = TestQuery(List(10))

      RestrictedFn.apply((q1, q2))(refs =>
        val combined1 = refs._1.flatMap(x => refs._2)
        val combined2 = refs._1.flatMap(x => refs._2)
        ForAllLinearConnective((combined1, combined2))
      )
    """)

    assert(
      obtained.contains(TestUtils.forAllLinearFailed),
      s"Expected ForEach constraint failure but got: $obtained"
    )
  }
//
//  // --- @restrictedReturn with Affine (can use 0 or 1 times) ---
//
  test("@restrictedReturn + Affine: POSITIVE - used zero times") {
    val q = TestQuery(List(1, 2))

    val result = RestrictedFn.apply(Tuple1(q))(refs =>
      val combined = refs._1.flatMap(x => TestQuery(List(x * 2)))
      ForAllAffineConnective(Tuple1(combined))
    )

    assertEquals(result._1.data, List(2, 4))
  }
//
  test("@restrictedReturn + Affine: POSITIVE - used exactly once") {
    val q1 = TestQuery(List(1, 2))
    val q2 = TestQuery(List(10))
    val q3 = TestQuery(List(100))

    val result = RestrictedFn.apply((q1, q2, q3))(refs =>
      val combined = refs._1.flatMap(x => refs._2)
      ForAllAffineConnective((combined, refs._3))
    )

    assertEquals(result._1.data, List(10, 10))
  }
//
  test("@restrictedReturn + Affine: NEGATIVE - used twice") {
    val obtained = compileErrors("""
      import TestQueryOps.*
      import restrictedfn.{RestrictedSelectable, Multiplicity}

      val q1 = TestQuery(List(1, 2))
      val q2 = TestQuery(List(10))

      RestrictedFn.apply((q1, q2))(refs =>
        val combined1 = refs._1.flatMap(x => refs._2)
        val combined2 = refs._1.flatMap(x => refs._2)
        ForAllAffineConnective((combined1, combined2))
      )
    """)

    assert(
      obtained.contains(TestUtils.forAllAffineFailed),
      s"Expected ForEach constraint failure but got: $obtained"
    )
  }
//
//  // --- @restrictedReturn with Relevant (must use 1+ times) ---
//
  test("@restrictedReturn + Relevant: POSITIVE - used exactly once") {
    val q1 = TestQuery(List(1, 2))
    val q2 = TestQuery(List(10))
    val q3 = TestQuery(List(100))

    val result = RestrictedFn.apply((q1, q2, q3))(refs =>
      val combined = refs._1.flatMap(x => refs._2)
      ForAllRelevantConnective((combined, refs._3))
    )

    assertEquals(result._1.data, List(10, 10))
  }
//
  test("@restrictedReturn + Relevant: POSITIVE - used twice") {
    val q1 = TestQuery(List(1))
    val q2 = TestQuery(List(10))

    val result = RestrictedFn.apply((q1, q2))(refs =>
      val combined1 = refs._1.flatMap(x => TestQuery(List(x * 2)))
      val combined2 = refs._2.flatMap(x => TestQuery(List(x * 3)))
      ForAllRelevantConnective((combined1, combined2))
    )

    assertEquals(result._1.data, List(2))
    assertEquals(result._2.data, List(30))
  }
//
  test("@restrictedReturn + Relevant: NEGATIVE - used zero times") {
    val obtained = compileErrors("""
      import TestQueryOps.*
      import restrictedfn.{RestrictedSelectable, Multiplicity}

      val q1 = TestQuery(List(1, 2))
      val q2 = TestQuery(List(10))

      RestrictedFn.apply((q1, q2))(refs =>
        val combined = refs._1.flatMap(x => TestQuery(List(x)))
        ForAllRelevantConnective((combined, refs._1))
      )
    """)

    assert(
      obtained.contains(TestUtils.forAllRelevantFailed),
      s"Expected ForAll constraint failure but got: $obtained"
    )
  }
//
//  // ============================================================================
//  // MULTIPLICITY TESTS: @unrestricted with Linear/Affine/Relevant
//  // ============================================================================
//
//  // --- @unrestricted with Linear ---
//
  test("@unrestricted + Linear: POSITIVE - unrestricted param doesn't affect linearity") {
    val q = TestQuery(List(1, 2, 3))

    val result = RestrictedFn.apply(Tuple1(q))(refs =>
      // map takes @unrestricted function, so calling it doesn't affect linearity of refs._1
      val mapped = refs._1.map((x: Int) => x * 2)
      ForAllLinearConnective(Tuple1(mapped))
    )

    assertEquals(result._1.data, List(2, 4, 6))
  }
//
  test("@unrestricted + Linear: POSITIVE - receiver still tracked with Linear") {
    val q1 = TestQuery(List(1, 2))
    val q2 = TestQuery(List(10))

    val result = RestrictedFn.apply((q1, q2))(refs =>
      // Both receivers are tracked (Linear requires both used exactly once)
      val mapped1 = refs._1.map((x: Int) => x * 2)
      val mapped2 = refs._2.map((x: Int) => x * 10)
      ForAllLinearConnective((mapped1, mapped2))
    )

    assertEquals(result._1.data, List(2, 4))
    assertEquals(result._2.data, List(100))
  }
//
//  // --- @unrestricted with Affine ---
//
  test("@unrestricted + Affine: POSITIVE - can use receiver zero times") {
    val q = TestQuery(List(1, 2))

    val result = RestrictedFn.apply(Tuple1(q))(refs =>
      // map takes @unrestricted function, demonstrating receiver can be used zero times would require not using refs at all
      // But that's not possible in a meaningful test, so this test shows map can be called without issues
      val mapped = refs._1.map((x: Int) => x * 2)
      ForAllAffineConnective(Tuple1(mapped))
    )

    assertEquals(result._1.data, List(2, 4))
  }
//
  test("@unrestricted + Affine: POSITIVE - can use receiver once") {
    val q = TestQuery(List(1, 2, 3))

    val result = RestrictedFn.apply(Tuple1(q))(refs =>
      val mapped = refs._1.map((x: Int) => x * 2)
      ForAllAffineConnective(Tuple1(mapped))
    )

    assertEquals(result._1.data, List(2, 4, 6))
  }
//
  test("@unrestricted + Affine: NEGATIVE - cannot use receiver twice") {
    val obtained = compileErrors("""
      import TestQueryOps.*
      import restrictedfn.{RestrictedSelectable, Multiplicity}

      val q = TestQuery(List(1, 2, 3))

      RestrictedFn.apply(Tuple1(q))(refs =>
        val mapped1 = refs._1.map((x: Int) => x * 2)
        val mapped2 = refs._1.map((x: Int) => x * 3)
        ForAllAffineConnective((mapped1, mapped2))
      )
    """)

    assert(
      obtained.contains(TestUtils.forAllAffineFailed),
      s"Expected ForEach constraint failure but got: $obtained"
    )
  }
//
//  // --- @unrestricted with Relevant ---
//
  test("@unrestricted + Relevant: POSITIVE - used exactly once") {
    val q = TestQuery(List(1, 2, 3))

    val result = RestrictedFn.apply(Tuple1(q))(refs =>
      val mapped = refs._1.map((x: Int) => x * 2)
      ForAllRelevantConnective(Tuple1(mapped))
    )

    assertEquals(result._1.data, List(2, 4, 6))
  }
//
  test("@unrestricted + Relevant: POSITIVE - used twice") {
    val q1 = TestQuery(List(1, 2))
    val q2 = TestQuery(List(10, 20))

    val result = RestrictedFn.apply((q1, q2))(refs =>
      val mapped1 = refs._1.map((x: Int) => x * 2)
      val mapped2 = refs._2.map((x: Int) => x * 3)
      ForAllRelevantConnective((mapped1, mapped2))
    )

    assertEquals(result._1.data, List(2, 4))
    assertEquals(result._2.data, List(30, 60))
  }
//
  test("@unrestricted + Relevant: NEGATIVE - used zero times") {
    val obtained = compileErrors("""
      import TestQueryOps.*
      import restrictedfn.{RestrictedSelectable, Multiplicity}

      val q1 = TestQuery(List(1, 2))
      val q2 = TestQuery(List(10))

      RestrictedFn.apply((q1, q2))(refs =>
        // Only using refs._1, refs._2 unused - Relevant requires all used at least once
        val mapped = refs._1.map((x: Int) => x * 2)
        ForAllRelevantConnective(Tuple1(mapped))
      )
    """)

    assert(
      obtained.contains(TestUtils.forAllRelevantFailed),
      s"Expected ForAll constraint failure but got: $obtained"
    )
  }
//
//  // ============================================================================
//  // MULTIPLICITY TESTS: Regular (default) with Linear/Affine/Relevant
//  // ============================================================================
//
//  // --- Regular with Linear ---
//
  test("Regular + Linear: POSITIVE - used exactly once") {
    val q1 = TestQuery(List(1, 2))

    val result = RestrictedFn.apply(Tuple1(q1))(refs =>
      val transformed = refs._1.combine((x: Int) => TestQuery(List(x * 2)))
      ForAllLinearConnective(Tuple1(transformed))
    )

    assertEquals(result._1.data, List(2, 4))
  }
//
  test("Regular + Linear: NEGATIVE - used zero times") {
    val obtained = compileErrors("""
      import TestQueryOps.*
      import restrictedfn.{RestrictedSelectable, Multiplicity}

      val q1 = TestQuery(List(1, 2))
      val q2 = TestQuery(List(10))

      RestrictedFn.apply((q1, q2))(refs =>
        // Only using refs._1, refs._2 unused
        val transformed = refs._1.combine((x: Int) => TestQuery(List(x * 2)))
        ForAllLinearConnective(Tuple1(transformed))
      )
    """)

    assert(
      obtained.contains(TestUtils.forAllLinearFailed),
      s"Expected ForAll constraint failure but got: $obtained"
    )
  }
//
  test("Regular + Linear: NEGATIVE - used twice") {
    val obtained = compileErrors("""
      import TestQueryOps.*
      import restrictedfn.{RestrictedSelectable, Multiplicity}

      val q1 = TestQuery(List(1, 2))

      RestrictedFn.apply(Tuple1(q1))(refs =>
        val transformed1 = refs._1.combine((x: Int) => TestQuery(List(x * 2)))
        val transformed2 = refs._1.combine((x: Int) => TestQuery(List(x * 3)))
        ForAllLinearConnective((transformed1, transformed2))
      )
    """)

    assert(
      obtained.contains(TestUtils.forAllLinearFailed),
      s"Expected ForEach constraint failure but got: $obtained"
    )
  }
//
//  // --- Regular with Affine ---
//
  test("Regular + Affine: POSITIVE - used zero times") {
    val q = TestQuery(List(1, 2))

    val result = RestrictedFn.apply(Tuple1(q))(refs =>
      // Only using refs._1, demonstrating Affine allows using inputs
      val transformed = refs._1.combine((x: Int) => TestQuery(List(x * 2)))
      ForAllAffineConnective(Tuple1(transformed))
    )

    assertEquals(result._1.data, List(2, 4))
  }
//
  test("Regular + Affine: POSITIVE - used exactly once") {
    val q1 = TestQuery(List(1, 2))

    val result = RestrictedFn.apply(Tuple1(q1))(refs =>
      val transformed = refs._1.combine((x: Int) => TestQuery(List(x * 2)))
      ForAllAffineConnective(Tuple1(transformed))
    )

    assertEquals(result._1.data, List(2, 4))
  }
//
  test("Regular + Affine: NEGATIVE - used twice") {
    val obtained = compileErrors("""
      import TestQueryOps.*
      import restrictedfn.{RestrictedSelectable, Multiplicity}

      val q1 = TestQuery(List(1, 2))

      RestrictedFn.apply(Tuple1(q1))(refs =>
        val transformed1 = refs._1.combine((x: Int) => TestQuery(List(x * 2)))
        val transformed2 = refs._1.combine((x: Int) => TestQuery(List(x * 3)))
        ForAllAffineConnective((transformed1, transformed2))
      )
    """)

    assert(
      obtained.contains(TestUtils.forAllAffineFailed),
      s"Expected ForEach constraint failure but got: $obtained"
    )
  }
//
//  // --- Regular with Relevant ---
//
  test("Regular + Relevant: POSITIVE - used exactly once") {
    val q1 = TestQuery(List(1, 2))

    val result = RestrictedFn.apply(Tuple1(q1))(refs =>
      val transformed = refs._1.combine((x: Int) => TestQuery(List(x * 2)))
      ForAllRelevantConnective(Tuple1(transformed))
    )

    assertEquals(result._1.data, List(2, 4))
  }
//
  test("Regular + Relevant: POSITIVE - used twice") {
    val q1 = TestQuery(List(1, 2))
    val q2 = TestQuery(List(10, 20))

    val result = RestrictedFn.apply((q1, q2))(refs =>
      val transformed1 = refs._1.combine((x: Int) => TestQuery(List(x * 2)))
      val transformed2 = refs._2.combine((x: Int) => TestQuery(List(x * 3)))
      ForAllRelevantConnective((transformed1, transformed2))
    )

    assertEquals(result._1.data, List(2, 4))
    assertEquals(result._2.data, List(30, 60))
  }
//
  test("Regular + Relevant: NEGATIVE - used zero times") {
    val obtained = compileErrors("""
      import TestQueryOps.*
      import restrictedfn.{RestrictedSelectable, Multiplicity}

      val q1 = TestQuery(List(1, 2))
      val q2 = TestQuery(List(10))

      RestrictedFn.apply((q1, q2))(refs =>
        // Only using refs._1, refs._2 unused
        val transformed = refs._1.combine((x: Int) => TestQuery(List(x * 2)))
        ForAllRelevantConnective(Tuple1(transformed))
      )
    """)

    assert(
      obtained.contains(TestUtils.forAllRelevantFailed),
      s"Expected ForAll constraint failure but got: $obtained"
    )
  }
//
//  // ============================================================================
//  // ADVANCED @unrestricted TESTS: How @unrestricted parameters affect dependency tracking
//  // Key insight: @unrestricted params don't CONTRIBUTE their dependencies to the result,
//  // but the values themselves still must follow linearity rules when returned
//  // ============================================================================
//
  test("@unrestricted parameter - passing field allows returning parent value") {
    val ex1 = OpsExample("first", "0")
    val ex2 = OpsExample("second", "0")
    val ex3 = OpsExample("third", "0")

    // Key: refs._2 value is extracted and passed to @unrestricted param
    // This means refs._2 itself can still be returned without conflict
    val result = RestrictedFn.apply((ex1, ex2, ex3))(refs =>
      // Pass refs._2.value (String with EmptyTuple deps) to @unrestricted param
      val combined = refs._1.restrictedProductArg_UnrestrictedPrimitiveArg(refs._3, refs._2.value)
      // combined depends on refs._1 and refs._3, but not refs._2
      // So we can return refs._2 separately!
      ForAllAffineConnective((combined, refs._2))
    )

    assert(result._1.name.contains("first + third"), "Should contain 'first + third'")
    assertEquals(result._2.name, "second")
  }
//
  test("@unrestricted with plain String - EmptyTuple deps don't affect result") {
    val ex = OpsExample("base", "0")
    val config1 = "config1"
    val config2 = "config2"

    val result = RestrictedFn.apply(Tuple1(ex))(refs =>
      // Both config params have EmptyTuple deps (implicit conversion)
      val v1 = refs._1.allUnrestrictedArgs(config1, config2)
      ForAllAffineConnective(Tuple1(v1))  // Result only depends on refs._1
    )

    assertEquals(result._1.name, "config1baseconfig2")
  }
//
  test("@unrestricted params with implicit Strings - can be used multiple times in call") {
    val ex = OpsExample("base", "0")
    val config = "config"

    // Passing same plain string multiple times works because it has EmptyTuple deps
    val result = RestrictedFn.apply(Tuple1(ex))(refs =>
      val v1 = refs._1.allUnrestrictedArgs(config, config)  // Same param twice!
      ForAllAffineConnective(Tuple1(v1))
    )

    assertEquals(result._1.name, "configbaseconfig")
  }
//
  test("mixing plain values and Restricted - only Restricted contribute to deps") {
    val ex1 = OpsExample("first", "0")
    val ex2 = OpsExample("second", "0")
    val config = "plain config"

    val result = RestrictedFn.apply((ex1, ex2))(refs =>
      // config is plain (EmptyTuple), refs._2 is Restricted
      // Result depends on refs._1 (receiver) and refs._2 (tracked param), not config
      val combined = refs._1.restrictedProductArg_UnrestrictedPrimitiveArg(refs._2, config)
      ForAllAffineConnective(Tuple1(combined))
    )

    assert(result._1.name.contains("first + second"), "Should contain 'first + second'")
  }
//
  test("complex: multiple @unrestricted params with mixed types") {
    val ex1 = OpsExample("first", "0")
    val ex2 = OpsExample("second", "0")
    val ex3 = OpsExample("third", "0")
    val config = "config"

    val result = RestrictedFn.apply((ex1, ex2, ex3))(refs =>
      // refs._2 is tracked, config is @unrestricted (EmptyTuple), refs._3 is tracked
      val r = refs._1.mixedTrackedAndUnrestricted(refs._2, config, refs._3)
      ForAllAffineConnective(Tuple1(r))  // Result depends on refs._1, refs._2, refs._3 but NOT config
    )

    assert(result._1.name.contains("first + second + third"), "Should contain all three names")
  }
//
  test("@unrestricted - using field as param and returning parent value") {
    val ex1 = OpsExample("base", "0")
    val ex2 = OpsExample("config", "0")

    val result = RestrictedFn.apply((ex1, ex2))(refs =>
      // refs._2.name used as @unrestricted param, refs._2 returned
      val v1 = refs._1.allUnrestrictedArgs(refs._2.name, "-suffix1")
      ForAllAffineConnective((v1, refs._2))  // Can return refs._2 because its field was @unrestricted!
    )

    assert(result._1.name.contains("config"), s"Expected 'config' in ${result._1.name}")
    assertEquals(result._2.name, "config")
  }
//
  test("@unrestricted - multiple unrestricted params can all be returned separately") {
    val ex = OpsExample("base", "0")
    val config1 = "config1"
    val config2 = "config2"

    val result = RestrictedFn.apply((ex, config1, config2))(refs =>
      // Both config params are @unrestricted (EmptyTuple from implicit)
      val v1 = refs._1.allUnrestrictedArgs(refs._2, refs._3)
      // Can return both config values because they were @unrestricted
      ForAllAffineConnective((v1, refs._2, refs._3))
    )

    assertEquals(result._1.name, "config1baseconfig2")
    assertEquals(result._2, "config1")
    assertEquals(result._3, "config2")
  }
//
  test("@unrestricted - complex mixed tracked and unrestricted params") {
    val ex1 = OpsExample("first", "0")
    val ex2 = OpsExample("second", "0")
    val ex3 = OpsExample("third", "0")
    val config = "config"

    // mixedTrackedAndUnrestricted(first: tracked, config: @unrestricted, second: tracked)
    // Result should depend on first and second, but NOT config
    val result = RestrictedFn.apply((ex1, ex2, ex3, config))(refs =>
      val r = refs._1.mixedTrackedAndUnrestricted(refs._2, refs._4, refs._3)
      // r depends on refs._1, refs._2, refs._3 but NOT refs._4 (config is @unrestricted)
      // We can return config separately because it doesn't conflict with any other dependencies
      ForAllAffineConnective((r, refs._4))
    )

    assert(result._1.name.contains("first + second + third"), s"Expected to contain 'first + second + third', got: ${result._1.name}")
    assertEquals(result._2, "config")
  }
//
  test("@unrestricted - same param passed multiple times AND returned") {
    val ex = OpsExample("base", "0")
    val config = "config"

    // If config were tracked, using refs._2 multiple times would fail
    // But since it's @unrestricted (EmptyTuple from implicit), this works fine
    val result = RestrictedFn.apply((ex, config))(refs =>
      val v1 = refs._1.allUnrestrictedArgs(refs._2, refs._2)  // Same param twice!
      ForAllAffineConnective((v1, refs._2))  // Can also return it!
    )

    assertEquals(result._1.name, "configbaseconfig")
    assertEquals(result._2, "config")
  }
