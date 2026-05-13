package test

import restrictedfn.{ErrorMsg, Multiplicity }
import restrictedfn.RestrictedSelectable.{given, *}
object TestUtils:
  // Per-multiplicity error messages keyed off the failing constraint.
  val forAllRelevantFailed = ErrorMsg.forAllRelevantFailed
  val forAllAffineFailed = ErrorMsg.forAllAffineFailed
  val forAllLinearFailed = ErrorMsg.forAllLinearFailed
  val forEachRelevantFailed = ErrorMsg.forEachRelevantFailed
  val forEachAffineFailed = ErrorMsg.forEachAffineFailed
  val forEachLinearFailed = ErrorMsg.forEachLinearFailed
  val fixedPointReturnLengthFailed = "fixedPoint requires same number of arguments and returns"
  val fixedPointReturnTypesFailed = "fixedPoint requires return types to match argument types"
  val missingField = "is not a member of"
  // Substrings of the violation marker messages. After the constraint-check
  // refactor, the user sees a single-line domain-specific message like
  // "ForAll Relevant constraint failed: All arguments must be used at least
  // once across all values" delivered via @implicitNotFound on a violation
  // marker trait.
  val noGivenInstance = "constraint failed"
  val forAll = "ForAll"
  val forEach = "ForEach"
  val affine = "Affine"
  val relevant = "Relevant"
  val linear = "Linear"

type ForAllLinearConnective[RT <: Tuple] = CustomConnective[RT, Multiplicity.Unrestricted, Multiplicity.Linear]
object ForAllLinearConnective:
  def apply[RT <: Tuple]
  (values: RT): ForAllLinearConnective[RT] =
    CustomConnective[RT, Multiplicity.Unrestricted, Multiplicity.Linear](values)

type ForAllAffineConnective[RT <: Tuple] = CustomConnective[RT, Multiplicity.Unrestricted, Multiplicity.Affine]
object ForAllAffineConnective:
  def apply[RT <: Tuple]
  (values: RT): ForAllAffineConnective[RT] =
    CustomConnective[RT, Multiplicity.Unrestricted, Multiplicity.Affine](values)

type ForAllRelevantConnective[RT <: Tuple] = CustomConnective[RT, Multiplicity.Unrestricted, Multiplicity.Relevant]
object ForAllRelevantConnective:
  def apply[RT <: Tuple]
  (values: RT): ForAllRelevantConnective[RT] =
    CustomConnective[RT, Multiplicity.Unrestricted, Multiplicity.Relevant](values)

