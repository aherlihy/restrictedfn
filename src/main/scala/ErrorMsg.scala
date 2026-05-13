package restrictedfn

import scala.annotation.implicitNotFound

// Violation marker traits. These types have NO given instances anywhere, so
// implicit search for them always fails. Constraint-check match types reduce
// to one of these marker traits when a constraint is violated; the @implicitNotFound
// annotation then surfaces the domain-specific error message to the user.
//
// When a constraint is satisfied, the match types instead reduce to `true`
// (which has a given instance via trueEvidence in RestrictedFnBase). So
// satisfied constraints summon successfully; failed ones surface their
// annotated message.
@implicitNotFound(ErrorMsg.forAllRelevantFailed)
sealed trait ForAllRelevantViolation

@implicitNotFound(ErrorMsg.forAllAffineFailed)
sealed trait ForAllAffineViolation

@implicitNotFound(ErrorMsg.forAllLinearFailed)
sealed trait ForAllLinearViolation

@implicitNotFound(ErrorMsg.forEachRelevantFailed)
sealed trait ForEachRelevantViolation

@implicitNotFound(ErrorMsg.forEachAffineFailed)
sealed trait ForEachAffineViolation

@implicitNotFound(ErrorMsg.forEachLinearFailed)
sealed trait ForEachLinearViolation

object ErrorMsg:
  inline val forAllRelevantFailed =
    "ForAll Relevant constraint failed: All arguments must be used at least once across all values"
  inline val forAllAffineFailed =
    "ForAll Affine constraint failed: No argument may be used more than once across all values"
  inline val forAllLinearFailed =
    "ForAll Linear constraint failed: Every argument must be used exactly once across all values"
  inline val forEachRelevantFailed =
    "ForEach Relevant constraint failed: All arguments must be used at least once in each return value"
  inline val forEachAffineFailed =
    "ForEach Affine constraint failed: No argument may be used more than once in any return value"
  inline val forEachLinearFailed =
    "ForEach Linear constraint failed: Every argument must be used exactly once in each return value"
