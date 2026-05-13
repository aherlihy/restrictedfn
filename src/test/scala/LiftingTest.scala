package test

import munit.FunSuite
import scala.annotation.experimental
import restrictedfn.RestrictedSelectable.{given, *}

 /**
  * Tests for automatic lifting of nested types: T[Restricted[A, D]] => Restricted[T[A], D]
  *
  * This prevents containers of Restricted values from evading linearity checks.
  * Without lifting, `List[Restricted[A, D]]` would be a plain List that could be
  * returned multiple times, violating linearity. With lifting, it's automatically
  * converted to `Restricted[List[A], D]` which is properly tracked.
  */
 @experimental
 class LiftingTest extends FunSuite:

   import OpsExampleOps.*

   test("List[Restricted[A, D]] is automatically lifted in 2-tuple") {
     val ex1 = OpsExample("Alice", "30")
     val ex2 = OpsExample("Bob", "25")

     val result = RestrictedFn.apply((ex1, ex2))(refs =>
       // Create a list containing one Restricted element
       // The tuple conversion should automatically lift it
       ForAllLinearConnective((List(refs._1), refs._2))
     )

     assertEquals(result._1, List(ex1))
     assertEquals(result._2, ex2)
   }

   test("Option[Restricted[A, D]] is automatically lifted in 1-tuple") {
     val ex1 = OpsExample("Alice", "30")

     val result = RestrictedFn.apply(Tuple1(ex1))(refs =>
       // The tuple conversion should automatically lift the Option
      ForAllLinearConnective(Tuple1(Option(refs._1)))
     )

     assertEquals(result._1, Some(ex1))
   }

   test("Vector[Restricted[A, D]] is automatically lifted in 1-tuple") {
     val ex1 = OpsExample("Alice", "30")

     val result = RestrictedFn.apply(Tuple1(ex1))(refs =>
       // The tuple conversion should automatically lift the Vector
      ForAllLinearConnective(Tuple1(Vector(refs._1)))
     )

     assertEquals(result._1, Vector(ex1))
   }

   test("linearity violation: same ref in two Lists") {
     val obtained = compileErrors("""
       val ex1 = OpsExample("Alice", "30")
       val ex2 = OpsExample("Bob", "25")
       RestrictedFn.apply((ex1, ex2))(refs =>
         ForAllLinearConnective((List(refs._1), List(refs._1)))
       )
     """)
     // This should fail because refs._1 is used in two different lists
     // Both lists would have dependency Tuple1[0], violating linearity
     // Correct number of args (2 in, 2 out), but refs._1 used twice
     assert(obtained.contains(TestUtils.noGivenInstance) && obtained.contains(TestUtils.linear), s"obtained: $obtained")
   }

   test("linearity violation: returning List and the element inside it") {
     val obtained = compileErrors("""
       val ex1 = OpsExample("Alice", "30")
       val ex2 = OpsExample("Bob", "25")
       val ex3 = OpsExample("Charlie", "35")
       RestrictedFn.apply((ex1, ex2, ex3))(refs =>
         ForAllLinearConnective((List(refs._1), refs._1, refs._2))
       )
     """)
     // This should fail because we're returning both a List containing refs._1
     // and refs._1 itself - that's using refs._1 twice
     // Correct number of args (3 in, 3 out), but refs._1 used twice
     assert(obtained.contains(TestUtils.noGivenInstance) && obtained.contains(TestUtils.linear), s"obtained: $obtained")
   }

   test("linearity violation: same ref in Option and List") {
     val obtained = compileErrors("""
       val ex1 = OpsExample("Alice", "30")
       val ex2 = OpsExample("Bob", "25")
       RestrictedFn.apply((ex1, ex2))(refs =>
         ForAllLinearConnective((Option(refs._1), List(refs._1)))
       )
     """)
     // This should fail because refs._1 appears in both Option and List
     // Correct number of args (2 in, 2 out), but refs._1 used twice
     assert(obtained.contains(TestUtils.noGivenInstance) && obtained.contains(TestUtils.linear), s"obtained: $obtained")
   }

   test("linearity OK: different refs in different containers") {
     val ex1 = OpsExample("Alice", "30")
     val ex2 = OpsExample("Bob", "25")

     // This is fine - refs._1 in first container, refs._2 in second
     val result = RestrictedFn.apply((ex1, ex2))(refs =>
       ForAllLinearConnective((List(refs._1), Option(refs._2)))
     )

     assertEquals(result._1, List(ex1))
     assertEquals(result._2, Some(ex2))
   }

   test("nested List[List[Restricted[A, D]]] is automatically lifted") {
     val ex1 = OpsExample("Alice", "30")
     val ex2 = OpsExample("Bob", "25")

     val result = RestrictedFn.apply((ex1, ex2))(refs =>
       // Create a nested list structure
       val innerList = List(refs._1)
       val nestedList = List(innerList)
       ForAllLinearConnective((nestedList, refs._2))
     )

     assertEquals(result._1, List(List(ex1)))
     assertEquals(result._2, ex2)
   }

   test("nested List[Option[Restricted[A, D]]] is automatically lifted") {
     val ex1 = OpsExample("Alice", "30")

     val result = RestrictedFn.apply(Tuple1(ex1))(refs =>
       // Create nested List[Option[...]]
       val opt = Option(refs._1)
       val listOfOpt = List(opt)
       ForAllLinearConnective(Tuple1(listOfOpt))
     )

     assertEquals(result._1, List(Some(ex1)))
   }

   test("deeply nested List[List[List[Restricted[A, D]]]] is automatically lifted") {
     val ex1 = OpsExample("Alice", "30")

     val result = RestrictedFn.apply(Tuple1(ex1))(refs =>
       // Create deeply nested structure
       val inner = List(refs._1)
       val middle = List(inner)
       val outer = List(middle)
       ForAllLinearConnective(Tuple1(outer))
     )

     assertEquals(result._1, List(List(List(ex1))))
   }

   test("implicit conversion does not bypass lifting - dependencies properly tracked") {
     // This test verifies that List[Restricted[A, D]] is lifted to Restricted[List[A], D]
     // and not implicitly converted to Restricted[List[Restricted[A, D]], EmptyTuple]
     // If implicit conversion bypassed lifting, returning the list twice would work
     // (because EmptyTuple dependency wouldn't conflict)
     // But with proper lifting, the list has dependency Tuple1[0], so this should fail
     val obtained = compileErrors("""
       val ex1 = OpsExample("Alice", "30")
       val ex2 = OpsExample("Bob", "25")
       RestrictedFn.apply((ex1, ex2))(refs =>
         val list = List(refs._1)
         ForAllLinearConnective((list, list))  // Trying to return the same list twice
       )
     """)
     // If lifting works correctly, both list references have dependency Tuple1[0]
     // and returning them both violates linearity
     assert(obtained.contains(TestUtils.noGivenInstance) && obtained.contains(TestUtils.linear), s"obtained: $obtained")
   }

   test("unknown wrap types not ok without .lift") {
     val obtained = compileErrors(
       """
   case class Wrap[T](v: T)
   case class Person(name: String, age: Int):
     def combine(other: Person): Person =
       Person(s"${this.name} & ${other.name}", this.age + other.age)

   extension [D <: Tuple](p: Restricted[Person, D])
     def combine[D2 <: Tuple](other: Restricted[Person, D2]): Restricted[Person, Tuple.Concat[D, D2]] =
       p.stageCall[Person, Tuple.Concat[D, D2]]("combine", Tuple1(other))

   val person1 = Person("Alice", 30)
   val person2 = Person("Bob", 25)
   val result = RestrictedFn.apply((person1, person2))(refs =>
     val wrapped = Wrap(refs._1.combine(refs._2))
     ForAllLinearConnective((wrapped, refs._2))
   )
     """)
     // Either the constraint check fires its violation message, or the
     // unknown wrap type blocks LiftInnerType reduction (which surfaces
     // as a "No given instance of type CheckLinear[..., LiftInnerType[Wrap[...]]]"
     // error referencing the unreduced match type).
     assert(
       obtained.contains(TestUtils.noGivenInstance) ||
         obtained.contains("LiftInnerType") ||
         obtained.contains("CheckLinear"),
       s"obtained: $obtained"
     )
   }

   test("user-defined wrap types work with .lift and Liftable instance") {
     case class Wrap[T](v: T)

     given Restricted.Liftable[Wrap] with
       def map[A, B](fa: Wrap[A])(f: A => B): Wrap[B] = Wrap(f(fa.v))

     val ex1 = OpsExample("Alice", "30")
     val ex2 = OpsExample("Bob", "25")

     val result = RestrictedFn.apply((ex1, ex2))(refs =>
       val wrapped = Wrap(refs._1).lift
       ForAllLinearConnective((wrapped, refs._2))
     )

     assertEquals(result._1.v, ex1)
     assertEquals(result._2, ex2)
   }

   test("user-defined wrap types enforce linearity") {
     case class Wrap[T](v: T)

     given Restricted.Liftable[Wrap] with
       def map[A, B](fa: Wrap[A])(f: A => B): Wrap[B] = Wrap(f(fa.v))

     val obtained = compileErrors("""
       val ex1 = OpsExample("Alice", "30")
       val ex2 = OpsExample("Bob", "25")
       RestrictedFn.apply((ex1, ex2))(refs =>
         val wrapped = Wrap(refs._1).lift
         ForAllLinearConnective((wrapped, wrapped))  // Trying to return same wrapped value twice
       )
     """)
     // Should fail because both returns depend on refs._1
     assert(obtained.contains(TestUtils.noGivenInstance) && obtained.contains(TestUtils.linear), s"obtained: $obtained")
   }
