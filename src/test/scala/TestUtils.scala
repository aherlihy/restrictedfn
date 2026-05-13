package test

import restrictedfn.{ErrorMsg, Multiplicity }
import restrictedfn.RestrictedSelectable.{given, *}
object TestUtils:
  // Per-multiplicity error messages from the @implicitNotFound annotations on
  // the violation marker traits. Tests assert the exact message that surfaces
  // for each failing constraint, so the user-visible diagnostics stay in
  // lockstep with the implementation.
  val forAllRelevantFailed = ErrorMsg.forAllRelevantFailed
  val forAllAffineFailed = ErrorMsg.forAllAffineFailed
  val forAllLinearFailed = ErrorMsg.forAllLinearFailed
  val forEachRelevantFailed = ErrorMsg.forEachRelevantFailed
  val forEachAffineFailed = ErrorMsg.forEachAffineFailed
  val forEachLinearFailed = ErrorMsg.forEachLinearFailed
  // Fixed-point evidence parameter messages (defined in LinearDatalog.scala).
  val fixedPointReturnLengthFailed = "fixedPoint requires same number of arguments and returns"
  val fixedPointReturnTypesFailed = "fixedPoint requires return types to match argument types"
  // Standard scalac error fragments used to match unrelated compile errors.
  val missingField = "is not a member of"

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

