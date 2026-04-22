package test

import munit.FunSuite
import restrictedfn.{Multiplicity, RestrictedSelectable}
import restrictedfn.RestrictedSelectable.{given, *}

/**
 * Tests for κ enforcement: the K type parameter on RestrictedFn ensures
 * that references from an outer restricted function cannot be returned
 * by an inner restricted function to satisfy its constraints.
 */
class KappaTest extends FunSuite:

  // ============================================================================
  // Positive tests: valid nested restricted functions
  // ============================================================================

  test("nested RestrictedFn.apply: inner uses its own refs, outer uses its own") {
    val (a, b, c) = (1, 2, 3)

    val result = RestrictedFn.apply((a, b))(outerRefs =>
      // Inner restricted function uses only its own ref
      val innerResult = RestrictedFn.apply(Tuple1(c))(innerRefs =>
        ForAllAffineConnective(Tuple1(innerRefs._1))
      )
      // Outer returns its own refs
      ForAllAffineConnective((outerRefs._1, outerRefs._2))
    )

    assertEquals(result._1, 1)
    assertEquals(result._2, 2)
  }

  test("single restricted function: all refs used once (affine + relevant)") {
    val (a, b) = (10, 20)

    val result = RestrictedFn.apply((a, b))(refs =>
      ForAllLinearConnective((refs._1, refs._2))
    )

    assertEquals(result._1, 10)
    assertEquals(result._2, 20)
  }

  // ============================================================================
  // Negative tests: κ violations — outer ref used inside inner body
  // ============================================================================

  test("NEGATIVE: inner restricted function returns outer ref") {
    val obtained = compileErrors("""
      import restrictedfn.{Multiplicity, RestrictedSelectable}
      import restrictedfn.RestrictedSelectable.{given, *}
      import test.{ForAllAffineConnective, ForAllLinearConnective}

      val (a, b, c) = (1, 2, 3)

      RestrictedFn.apply((a, b))(outerRefs =>
        // Inner tries to return outer._1 — K types are incompatible
        val innerResult = RestrictedFn.apply(Tuple1(c))(innerRefs =>
          ForAllAffineConnective(Tuple1(outerRefs._1))
        )
        ForAllAffineConnective((outerRefs._1, outerRefs._2))
      )
    """)
    assert(obtained.nonEmpty, s"expected κ compile error, got empty")
  }

  test("NEGATIVE: inner restricted function mixes outer and inner refs") {
    val obtained = compileErrors("""
      import restrictedfn.{Multiplicity, RestrictedSelectable}
      import restrictedfn.RestrictedSelectable.{given, *}
      import test.{ForAllAffineConnective, ForAllLinearConnective}

      val (a, b) = (1, 2)

      RestrictedFn.apply(Tuple1(a))(outerRefs =>
        // Inner tries to use outer._1 alongside its own ref
        RestrictedFn.apply(Tuple1(b))(innerRefs =>
          ForAllLinearConnective((outerRefs._1, innerRefs._1))
        )
        ForAllAffineConnective(Tuple1(outerRefs._1))
      )
    """)
    assert(obtained.nonEmpty, s"expected κ compile error, got empty")
  }

  test("NEGATIVE: inner function passes outer ref through an operation") {
    val obtained = compileErrors("""
      import restrictedfn.{Multiplicity, RestrictedSelectable}
      import restrictedfn.RestrictedSelectable.{given, *}
      import test.{ForAllAffineConnective, OpsExample}
      import OpsExampleOps.{given, *}

      val (a, b) = (OpsExample("a"), OpsExample("b"))

      RestrictedFn.apply(Tuple1(a))(outerRefs =>
        RestrictedFn.apply(Tuple1(b))(innerRefs =>
          // Outer ref flows through an operation into the inner connective
          ForAllAffineConnective(Tuple1(innerRefs._1.singleRestrictedProductArg(outerRefs._1)))
        )
        ForAllAffineConnective(Tuple1(outerRefs._1))
      )
    """)
    assert(obtained.nonEmpty, s"expected κ compile error, got empty")
  }
