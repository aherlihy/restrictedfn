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

  // Construct restricted types from arguments
  // Converts argument to Restricted types with single-element dependency tuples
  // Each argument gets a unique index: arg0 → (0), arg1 → (1), etc.
  type ToRestrictedRef[AT <: Tuple] = Tuple.Map[ZipWithIndex[AT], [T] =>> T match
    case (elem, index) => Restricted[elem, Tuple1[index]]
  ]

  // κ-tagged variant: each index is intersected with K
  type ToRestrictedRefK[AT <: Tuple, K] = Tuple.Map[ZipWithIndex[AT], [T] =>> T match
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
  // Constraint Checks - Core logic that works on a single dependency tuple
  // ============================================================================

  // Check if all required indices appear in dependencies
  type CheckRelevant[Indices <: Tuple, Deps <: Tuple] =
    Tuple.Union[Indices] <:< Tuple.Union[Deps]

  // Check if dependencies have no duplicates
  type CheckAffine[Deps <: Tuple] =
    HasDuplicate[Deps] =:= Deps

  // ============================================================================
  // ForAll: Flatten all dependencies, then check once
  // ============================================================================

  // Helper: Flatten all dependencies into a single tuple
  type FlattenAllDependencies[RQT <: Tuple] <: Tuple = RQT match
    case EmptyTuple => EmptyTuple
    case h *: tail => LiftInnerType[h] match
      case (_, d) => Tuple.Concat[d, FlattenAllDependencies[tail]]

  type CheckForAll[M <: Multiplicity, AT <: Tuple, RQT <: Tuple] = M match
    case Multiplicity.Linear =>
      (CheckRelevant[GenerateIndices[0, Tuple.Size[AT]], FlattenAllDependencies[RQT]],
       CheckAffine[FlattenAllDependencies[RQT]])
    case Multiplicity.Affine =>
      CheckAffine[FlattenAllDependencies[RQT]]
    case Multiplicity.Relevant =>
      CheckRelevant[GenerateIndices[0, Tuple.Size[AT]], FlattenAllDependencies[RQT]]
    case Multiplicity.Unrestricted => true

  // ============================================================================
  // ForEach: Check each dependency tuple separately
  // ============================================================================

  type CheckForEach[M <: Multiplicity, AT <: Tuple, RQT <: Tuple] = M match
    case Multiplicity.Linear =>
      CheckEach[GenerateIndices[0, Tuple.Size[AT]], ExtractDependencyTypes[RQT], true, true]
    case Multiplicity.Affine =>
      CheckEach[GenerateIndices[0, Tuple.Size[AT]], ExtractDependencyTypes[RQT], false, true]
    case Multiplicity.Relevant =>
      CheckEach[GenerateIndices[0, Tuple.Size[AT]], ExtractDependencyTypes[RQT], true, false]
    case Multiplicity.Unrestricted => true

  // Helper: Iterate over each dependency tuple and check constraints
  // needRelevant = check that all indices are present
  // needAffine = check that there are no duplicates
  type CheckEach[
    Indices <: Tuple,
    DepTuples <: Tuple,
    NeedRelevant <: Boolean,
    NeedAffine <: Boolean
  ] <: Tuple = DepTuples match
    case EmptyTuple => EmptyTuple
    case deps *: rest =>
      CheckOne[Indices, deps, NeedRelevant, NeedAffine] *: CheckEach[Indices, rest, NeedRelevant, NeedAffine]

  // Check a single dependency tuple based on flags
  type CheckOne[
    Indices <: Tuple,
    Deps <: Tuple,
    NeedRelevant <: Boolean,
    NeedAffine <: Boolean
  ] = (NeedRelevant, NeedAffine) match
    case (true, true) => (CheckRelevant[Indices, Deps], CheckAffine[Deps])
    case (true, false) => CheckRelevant[Indices, Deps]
    case (false, true) => CheckAffine[Deps]
    case (false, false) => true

  // ============================================================================
  // κ-tagged variants: indices become `index & K`
  // ============================================================================

  type GenerateIndicesK[N <: Int, Size <: Int, K] <: Tuple = N match
    case Size => EmptyTuple
    case _ => (N & K) *: GenerateIndicesK[compiletime.ops.int.S[N], Size, K]

  type CheckForAllK[M <: Multiplicity, K, AT <: Tuple, RQT <: Tuple] = M match
    case Multiplicity.Linear =>
      (CheckRelevant[GenerateIndicesK[0, Tuple.Size[AT], K], FlattenAllDependencies[RQT]],
       CheckAffine[FlattenAllDependencies[RQT]])
    case Multiplicity.Affine =>
      CheckAffine[FlattenAllDependencies[RQT]]
    case Multiplicity.Relevant =>
      CheckRelevant[GenerateIndicesK[0, Tuple.Size[AT], K], FlattenAllDependencies[RQT]]
    case Multiplicity.Unrestricted => true

  type CheckForEachK[M <: Multiplicity, K, AT <: Tuple, RQT <: Tuple] = M match
    case Multiplicity.Linear =>
      CheckEach[GenerateIndicesK[0, Tuple.Size[AT], K], ExtractDependencyTypes[RQT], true, true]
    case Multiplicity.Affine =>
      CheckEach[GenerateIndicesK[0, Tuple.Size[AT], K], ExtractDependencyTypes[RQT], false, true]
    case Multiplicity.Relevant =>
      CheckEach[GenerateIndicesK[0, Tuple.Size[AT], K], ExtractDependencyTypes[RQT], true, false]
    case Multiplicity.Unrestricted => true

  type CheckForAllMultiplicityK[ForAllM <: Multiplicity, K, AT <: Tuple, RQT <: Tuple] =
    CheckForAllK[ForAllM, K, AT, RQT]

  type CheckForEachMultiplicityK[ForEachM <: Multiplicity, K, AT <: Tuple, RQT <: Tuple] =
    CheckForEachK[ForEachM, K, AT, RQT]

  // ============================================================================
  // Top-level constraint checks with error messages
  // ============================================================================

  // Given instance for true - used when Unrestricted multiplicity bypasses constraints
  given trueEvidence: true = true

  // Given instance for tuple constraints - used when CheckLinear returns a tuple
  given tupleEvidence[A, B](using A, B): (A, B) = (summon[A], summon[B])

  // Given instance for general tuples - used for ForEach checks that return tuple of evidences
  given emptyTupleEvidence: EmptyTuple = EmptyTuple
  given consTupleEvidence[H, T <: Tuple](using H, T): (H *: T) = summon[H] *: summon[T]

  // Just use the check types directly without wrappers
  type CheckForAllMultiplicity[
    ForAllM <: Multiplicity,
    AT <: Tuple,
    RQT <: Tuple
  ] = CheckForAll[ForAllM, AT, RQT]

  type CheckForEachMultiplicity[
    ForEachM <: Multiplicity,
    AT <: Tuple,
    RQT <: Tuple
  ] = CheckForEach[ForEachM, AT, RQT]

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
    type RestrictedFn[K, AT <: Tuple, RQT] = ToRestrictedRefK[AT, K] => RQT

    type ExtractReturnType[Connective] = Connective match
      case CustomConnective[rqt, forEachM, forAllM] =>
        ExtractResultTypes[rqt]

    trait RestrictedFnBuilder[K, AT <: Tuple, Connective]:
      def execute(fns: RestrictedFn[K, AT, Connective])(args: AT): ExtractReturnType[Connective]

    object RestrictedFnBuilder:
      // Builder for ComposedConnective - enforces custom connective constraints
      given connectiveBuilder[
        K,
        AT <: Tuple,
        RQT <: Tuple,
        ForEachM <: Multiplicity,
        ForAllM <: Multiplicity
      ](using
        @implicitNotFound(ErrorMsg.compositionForAllFailed)
        evForAll: CheckForAllMultiplicityK[ForAllM, K, AT, RQT],
        @implicitNotFound(ErrorMsg.compositionForEachFailed)
        evForEach: CheckForEachMultiplicityK[ForEachM, K, AT, RQT],
      ): RestrictedFnBuilder[K, AT, CustomConnective[RQT, ForEachM, ForAllM]] with
        def execute(fns: RestrictedFn[K, AT, CustomConnective[RQT, ForEachM, ForAllM]])(args: AT): ExtractResultTypes[RQT] =
          val restrictedRefs = (0 until args.size).map(i => makeRestrictedRef(() => args.productElement(i).asInstanceOf[Any])).toArray
          val restrictedRefsTuple = Tuple.fromArray(restrictedRefs).asInstanceOf[ToRestrictedRefK[AT, K]]
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

