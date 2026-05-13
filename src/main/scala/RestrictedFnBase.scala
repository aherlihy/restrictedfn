package restrictedfn

import restrictedfn.Utils.*
import scala.annotation.implicitNotFound

// ============================================================================
// Multiplicity Type Definitions
// ============================================================================

/**
 * Multiplicity constraints - track how many times a value can be consumed
 */
sealed trait Multiplicity
object Multiplicity:
  /** Must be consumed exactly once */
  sealed trait Linear extends Multiplicity
  /** Can be consumed at most once */
  sealed trait Affine extends Multiplicity
  /** Must be consumed at least once */
  sealed trait Relevant extends Multiplicity
  /** Can be consumed any number of times (no restrictions) */
  sealed trait Unrestricted extends Multiplicity

  // Witness objects for explicit multiplicity selection
  object Linear extends Linear
  object Affine extends Affine
  object Relevant extends Relevant
  object Unrestricted extends Unrestricted

// ============================================================================
// Custom Connective Type Definitions
// ============================================================================

/**
 * Abstract base for all RestrictedFn implementations.
 */

trait RestrictedBase[A, D <: Tuple]:
  def execute(): A

abstract class RestrictedFnBase:

  // ============================================================================
  // Restricted: Construct and Deconstruct Restricted types
  // ============================================================================

  /**
   * Restricted: Type that wraps restricted function arguments
   */
  type Restricted[A, D <: Tuple] <: RestrictedBase[A, D]

  /**
   * ComposedConnective: The result of composing Restricted values with a CustomConnective.
   */
  case class CustomConnective[
    RQT <: Tuple,
    ForEachM <: Multiplicity,
    ForAllM <: Multiplicity
  ](
    values: RQT
  ) extends RestrictedBase[ExtractResultTypes[RQT], ExtractDependencyTypes[RQT]]:
    def execute(): ExtractResultTypes[RQT] =
      tupleExecute(values).asInstanceOf[ExtractResultTypes[RQT]]

  // Factory method for creating RestrictedRef instances
  protected def makeRestrictedRef[A, D <: Tuple](fn: () => A): Restricted[A, D]

  // Unwrap a Restricted value
  protected def executeRestricted[A, D <: Tuple](r: Restricted[A, D]): A =
    r.execute()

  // Helper to recursively execute Restricted values inside nested containers
  // We can check against RestrictedBase since all Restricted types must extend it
  private def executeNested(value: Any): Any = value match
    // Check for containers BEFORE Restricted to handle nested cases
    case list: List[_] => list.map(executeNested)
    case opt: Option[_] => opt.map(executeNested)
    case vec: Vector[_] => vec.map(executeNested)
    case r: RestrictedBase[_, _] => r.execute()
    case other => other

  // Common tupleExecute implementation
  def tupleExecute[T <: Tuple](t: T): Tuple =
    t match
      case EmptyTuple => EmptyTuple
      case h *: tail => executeNested(h) *: tupleExecute(tail)

  // Construct restricted types from arguments.
  // Each argument index N becomes a κ-tagged identifier N & K, matching
  // the $a_\kappa$ identifiers in the paper. K is a fresh type per
  // restricted-function invocation (anonymous classes / value types in code).
  type ToRestrictedRef[AT <: Tuple, K] = Tuple.Map[ZipWithIndex[AT], [T] =>> T match
    case (elem, index) => Restricted[elem, Tuple1[index & K]]
  ]

  // Used to construct the Restricted types returned by the function
  // RT is the return tuple, DT is the tuple of dependency tuples
  type ToRestricted[RT <: Tuple, DT <: Tuple] =
    Tuple.Map[Tuple.Zip[RT, DT], [T] =>> ConstructRestricted[T]]

  // Recursive helper to reconstruct nested Restricted types
  type ReconstructRestricted[A, D <: Tuple] = A match
    case List[inner] => List[ReconstructRestricted[inner, D]]
    case Option[inner] => Option[ReconstructRestricted[inner, D]]
    case Vector[inner] => Vector[ReconstructRestricted[inner, D]]
    case _ => Restricted[A, D]

  type ConstructRestricted[T] = T match
    // Automatic lifting: construct containers of Restricted types (must come BEFORE general case)
    case (List[a], d) => ReconstructRestricted[List[a], d]
    case (Option[a], d) => ReconstructRestricted[Option[a], d]
    case (Vector[a], d) => ReconstructRestricted[Vector[a], d]
    case (a, d) => Restricted[a, d]


  // Helper match type to extract inner type and dependencies from potentially nested containers
  // Returns (innermost_type, dependencies)
  // This is the PRIMARY place to add new container types for lifting support
  type LiftInnerType[T] = T match
    case Restricted[a, d] => (a, d)
    case List[inner] => LiftInnerType[inner] match
      case (a, d) => (List[a], d)
    case Option[inner] => LiftInnerType[inner] match
      case (a, d) => (Option[a], d)
    case Vector[inner] => LiftInnerType[inner] match
      case (a, d) => (Vector[a], d)
    // Plain (unrestricted) values: treated as having no dependencies,
    // matching the LIFT rule in the formalism. Needed so the constraint
    // match types reduce cleanly even when a return tuple mixes Restricted
    // and plain values.
    case _ => (T, EmptyTuple)

  // Extract the wrapped type of a Restricted type
  type ExtractResultTypes[RQT <: Tuple] <: Tuple = RQT match
    case EmptyTuple => EmptyTuple
    case h *: tail => LiftInnerType[h] match
      case (a, _) => a *: ExtractResultTypes[tail]

  // Extract the dependencies of a Restricted type
  type ExtractDependencyTypes[RQT <: Tuple] <: Tuple = RQT match
    case EmptyTuple => EmptyTuple
    case h *: tail => LiftInnerType[h] match
      case (_, d) => d *: ExtractDependencyTypes[tail]

  // Combine dependencies of a Restricted type A and a dependency tuple D
  type CollateDeps[A, D <: Tuple] <: Tuple = A match
    case Restricted[a, d] => Tuple.Concat[d, D]
    case _ => D

  // ============================================================================
  // Constraint Checks - structural, match-type-based
  // ============================================================================
  //
  // Each check reduces to either `true` (constraint satisfied; summonable via
  // `trueEvidence` below) or one of the violation marker traits in ErrorMsg.scala
  // (no givens; @implicitNotFound surfaces the domain-specific message). The
  // Violation type parameter lets the same check helper produce a different
  // marker depending on whether it is being used in a ForAll or ForEach context.

  // ContainsType[Tup, Elem]: structural membership test on a tuple of
  // singleton (typically integer-singleton) types.
  type ContainsType[Tup <: Tuple, Elem] <: Boolean = Tup match
    case EmptyTuple => false
    case Elem *: _ => true
    case _ *: t    => ContainsType[t, Elem]

  // AllContained[Sub, Sup]: every element of Sub appears in Sup.
  type AllContained[Sub <: Tuple, Sup <: Tuple] <: Boolean = Sub match
    case EmptyTuple => true
    case h *: t => ContainsType[Sup, h] match
      case true  => AllContained[t, Sup]
      case false => false

  // HasNoDuplicates[Tup]: no two elements of Tup are the same type.
  type HasNoDuplicates[Tup <: Tuple] <: Boolean = Tup match
    case EmptyTuple => true
    case h *: t => ContainsType[t, h] match
      case true  => false
      case false => HasNoDuplicates[t]

  // CheckRelevant: every index in `Indices` must appear in `Deps`.
  // Reduces to `true` on success, to `Violation` on failure.
  type CheckRelevant[Indices <: Tuple, Deps <: Tuple, Violation] =
    AllContained[Indices, Deps] match
      case true  => true
      case false => Violation

  // CheckAffine: `Deps` must contain no duplicate elements.
  type CheckAffine[Deps <: Tuple, Violation] =
    HasNoDuplicates[Deps] match
      case true  => true
      case false => Violation

  // CheckLinear: combines both. Any failure produces the same Violation, so
  // a Linear violation always surfaces as the Linear-specific message rather
  // than leaking which sub-check failed.
  type CheckLinear[Indices <: Tuple, Deps <: Tuple, Violation] =
    AllContained[Indices, Deps] match
      case true => HasNoDuplicates[Deps] match
        case true  => true
        case false => Violation
      case false => Violation

  // ============================================================================
  // ForAll: Flatten all dependencies, then check once
  // ============================================================================

  // Helper: Flatten all dependencies into a single tuple
  type FlattenAllDependencies[RQT <: Tuple] <: Tuple = RQT match
    case EmptyTuple => EmptyTuple
    case h *: tail => LiftInnerType[h] match
      case (_, d) => Tuple.Concat[d, FlattenAllDependencies[tail]]

  // The K parameter is the fresh tag used to differentiate multiple invocations
  // of restricted functions. Argument indices are tagged via GenerateIndicesK,
  // producing identifiers of the form (i & K) that match the $a_\kappa$
  // identifiers in the paper.

  // Iterate over each dependency tuple and check the per-element constraint.
  // Folds to a single result: `true` if every element passes, or `Violation`
  // if any element fails. This avoids building a tuple of checks (which would
  // make scalac's cascade report the parametric tuple-deconstruction step
  // instead of the violation marker, losing the @implicitNotFound message).
  type CheckEach[
    Indices <: Tuple,
    DepTuples <: Tuple,
    M <: Multiplicity,
    Violation
  ] = DepTuples match
    case EmptyTuple => true
    case deps *: rest => CheckOne[Indices, deps, M] match
      case true  => CheckEach[Indices, rest, M, Violation]
      case false => Violation

  // Boolean-valued single-element check. Returns the boolean outcome of the
  // per-element constraint; CheckEach turns failure into the appropriate
  // Violation marker.
  type CheckOne[Indices <: Tuple, Deps <: Tuple, M <: Multiplicity] <: Boolean = M match
    case Multiplicity.Linear   => AllContainedAndNoDups[Indices, Deps]
    case Multiplicity.Affine   => HasNoDuplicates[Deps]
    case Multiplicity.Relevant => AllContained[Indices, Deps]
    case Multiplicity.Unrestricted => true

  type AllContainedAndNoDups[Indices <: Tuple, Deps <: Tuple] <: Boolean =
    AllContained[Indices, Deps] match
      case true  => HasNoDuplicates[Deps]
      case false => false

  // ============================================================================
  // κ-tagged check types: indices carry a fresh K per invocation
  // ============================================================================

  type GenerateIndicesK[N <: Int, Size <: Int, K] <: Tuple = N match
    case Size => EmptyTuple
    case _ => (N & K) *: GenerateIndicesK[compiletime.ops.int.S[N], Size, K]

  type CheckForAll[M <: Multiplicity, K, AT <: Tuple, RQT <: Tuple] = M match
    case Multiplicity.Linear =>
      CheckLinear[GenerateIndicesK[0, Tuple.Size[AT], K], FlattenAllDependencies[RQT], ForAllLinearViolation]
    case Multiplicity.Affine =>
      CheckAffine[FlattenAllDependencies[RQT], ForAllAffineViolation]
    case Multiplicity.Relevant =>
      CheckRelevant[GenerateIndicesK[0, Tuple.Size[AT], K], FlattenAllDependencies[RQT], ForAllRelevantViolation]
    case Multiplicity.Unrestricted => true

  type CheckForEach[M <: Multiplicity, K, AT <: Tuple, RQT <: Tuple] = M match
    case Multiplicity.Linear =>
      CheckEach[GenerateIndicesK[0, Tuple.Size[AT], K], ExtractDependencyTypes[RQT], Multiplicity.Linear, ForEachLinearViolation]
    case Multiplicity.Affine =>
      CheckEach[GenerateIndicesK[0, Tuple.Size[AT], K], ExtractDependencyTypes[RQT], Multiplicity.Affine, ForEachAffineViolation]
    case Multiplicity.Relevant =>
      CheckEach[GenerateIndicesK[0, Tuple.Size[AT], K], ExtractDependencyTypes[RQT], Multiplicity.Relevant, ForEachRelevantViolation]
    case Multiplicity.Unrestricted => true

  // Wrapper traits whose derive given uses summonInline to FORCE match-type
  // reduction at the call site. Without this, scalac's cascade resolution
  // displays the unreduced CheckForAll[...] type and misses the
  // @implicitNotFound annotation on the violation marker that the match type
  // would reduce to. summonInline expands during the inline derive's body and
  // surfaces the violation marker's annotation as a regular compile error.
  sealed trait CheckForAllMultiplicity[ForAllM <: Multiplicity, K, AT <: Tuple, RQT <: Tuple]
  sealed trait CheckForEachMultiplicity[ForEachM <: Multiplicity, K, AT <: Tuple, RQT <: Tuple]

  inline given deriveCheckForAllMultiplicity[
    ForAllM <: Multiplicity, K, AT <: Tuple, RQT <: Tuple
  ]: CheckForAllMultiplicity[ForAllM, K, AT, RQT] = {
    scala.compiletime.summonInline[CheckForAll[ForAllM, K, AT, RQT]]
    new CheckForAllMultiplicity[ForAllM, K, AT, RQT] {}
  }

  inline given deriveCheckForEachMultiplicity[
    ForEachM <: Multiplicity, K, AT <: Tuple, RQT <: Tuple
  ]: CheckForEachMultiplicity[ForEachM, K, AT, RQT] = {
    scala.compiletime.summonInline[CheckForEach[ForEachM, K, AT, RQT]]
    new CheckForEachMultiplicity[ForEachM, K, AT, RQT] {}
  }

  // ============================================================================
  // Evidence givens used to satisfy constraint-check match types
  // ============================================================================

  // For Unrestricted constraints (and successful Relevant/Affine/Linear) which
  // reduce to the singleton `true`.
  given trueEvidence: true = true

  // For tuple constraints (Linear's pair, ForEach's accumulator).
  given tupleEvidence[A, B](using A, B): (A, B) = (summon[A], summon[B])
  given emptyTupleEvidence: EmptyTuple = EmptyTuple
  given consTupleEvidence[H, T <: Tuple](using H, T): (H *: T) = summon[H] *: summon[T]

  // ============================================================================
  // RestrictedFn Methods: Combining ForEach and ForAll Constraints
  // ============================================================================

  object RestrictedFn:
    /**
     * LinearFn: A type alias for linear functions.
     *
     * This is the library's contribution - a clean name for linear functions
     * that take restricted references and return a ComposedConnective.
     */
    type RestrictedFn[K, AT <: Tuple, RQT] = ToRestrictedRef[AT, K] => RQT

    type ExtractReturnType[Connective] = Connective match
      case CustomConnective[rqt, forEachM, forAllM] =>
        ExtractResultTypes[rqt]

    // The user-visible domain-specific message is delivered by the
    // @implicitNotFound annotations on the violation marker traits in
    // ErrorMsg.scala, surfaced when a constraint-check match type reduces to
    // a violation marker. No annotation is needed on RestrictedFnBuilder
    // itself: the violation marker carries the actionable message.
    trait RestrictedFnBuilder[K, AT <: Tuple, Connective]:
      def execute(fns: RestrictedFn[K, AT, Connective])(args: AT): ExtractReturnType[Connective]

    object RestrictedFnBuilder:
      given connectiveBuilder[
        K,
        AT <: Tuple,
        RQT <: Tuple,
        ForEachM <: Multiplicity,
        ForAllM <: Multiplicity
      ](using
        evForAll: CheckForAllMultiplicity[ForAllM, K, AT, RQT],
        evForEach: CheckForEachMultiplicity[ForEachM, K, AT, RQT],
      ): RestrictedFnBuilder[K, AT, CustomConnective[RQT, ForEachM, ForAllM]] with
        def execute(fns: RestrictedFn[K, AT, CustomConnective[RQT, ForEachM, ForAllM]])(args: AT): ExtractResultTypes[RQT] =
          val restrictedRefs = (0 until args.size).map(i => makeRestrictedRef(() => args.productElement(i).asInstanceOf[Any])).toArray
          val restrictedRefsTuple = Tuple.fromArray(restrictedRefs).asInstanceOf[ToRestrictedRef[AT, K]]
          val resultConnective = fns(restrictedRefsTuple)
          val evaluated = resultConnective.execute()
          evaluated.asInstanceOf[ExtractResultTypes[RQT]]

    /**
     * apply: General-purpose linear function application with custom connectives.
     *
     * This is a convenience method for applying linear functions with the standard pattern:
     * 1. Wrap arguments in Restricted types
     * 2. Call the function
     * 3. Execute and unwrap the result
     *
     * The function must return results wrapped in a ComposedConnective that specifies
     * both ForEach and ForAll multiplicity constraints.
     *
     * @tparam AT The argument tuple type
     * @tparam RT The return tuple type (tuple of result types)
     * @tparam ForEachM The ForEach multiplicity constraint (applied per return value)
     * @tparam ForAllM The ForAll multiplicity constraint (applied across all returns)
     * @param args The argument tuple
     * @param fns The function from restricted references to ComposedConnective-wrapped returns
     * @return The tuple of executed results
     */
    def apply[K, AT <: Tuple, RT <: Tuple, ForEachM <: Multiplicity, ForAllM <: Multiplicity]
    (args: AT)(fns: RestrictedFn[K, AT, CustomConnective[RT, ForEachM, ForAllM]])(
      using builder: RestrictedFnBuilder[K, AT, CustomConnective[RT, ForEachM, ForAllM]]
    ): ExtractResultTypes[RT] =
      builder.execute(fns)(args)

