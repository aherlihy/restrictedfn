package test.casestudies

import restrictedfn.{Multiplicity, RestrictedSelectable, ops}
import RestrictedSelectable.{given, *}
import munit.FunSuite
import test.TestUtils

/**
 * Case Study: Stream Processing
 *
 * A stream-processing DSL that provides a function routing n input streams into m
 * output sinks. Every input must flow to at least one sink (global relevant), ensuring
 * no data is dropped, while each sink can sample or read from multiple inputs
 * (per-element unrestricted).
 *
 * Multiplicities:
 *   ForEach = Unrestricted  (each sink can freely reference any combination of inputs)
 *   ForAll  = Relevant      (every input stream must be consumed by at least one sink)
 */

@ops
class Channel[A]():
  /** Merge two channels, tracking dependencies from both. */
  def merge(other: Channel[A]): Channel[A] = Channel[A]()

object Channel:
  def source[A](name: String): Channel[A] = Channel[A]()

// Connective: ForEach-Unrestricted, ForAll-Relevant
type RouteConnective[RQT <: Tuple] =
  RestrictedSelectable.CustomConnective[RQT, Multiplicity.Unrestricted, Multiplicity.Relevant]

object RouteConnective:
  def apply[K, RQT <: Tuple](values: RQT) =
    RestrictedSelectable.CustomConnective[RQT, Multiplicity.Unrestricted, Multiplicity.Relevant](values)

object StreamDSL:
  def route[K, ST <: Tuple, RQT <: Tuple](
    streams: ST
  )(fns: RestrictedSelectable.RestrictedFn.RestrictedFn[K, ST, RouteConnective[RQT]])(
    using
      builder: RestrictedSelectable.RestrictedFn.RestrictedFnBuilder[K, ST, RouteConnective[RQT]]
  ): RestrictedSelectable.ExtractResultTypes[RQT] =
    builder.execute(fns)(streams)


class StreamProcessingTest extends FunSuite:
  import ChannelOps.{given, *}

  test("Route 2 streams to 2 sinks (disjoint)") {
    val s1 = Channel.source[Int]("clicks")
    val s2 = Channel.source[Int]("views")

    val result = StreamDSL.route((s1, s2))((a, b) =>
      RouteConnective.apply((a, b))
    )
    assert(result != null)
  }

  test("Route 2 streams to 2 sinks (one sink reads both - unrestricted per-element)") {
    val s1 = Channel.source[Int]("clicks")
    val s2 = Channel.source[Int]("views")

    // Each sink can freely reference multiple inputs (ForEach-Unrestricted)
    // Both inputs are consumed (ForAll-Relevant)
    val result = StreamDSL.route((s1, s2))((a, b) =>
      RouteConnective.apply((a.merge(b), b))
    )
    assert(result != null)
  }

  test("Route 3 streams to 2 sinks (all inputs consumed)") {
    val s1 = Channel.source[Int]("clicks")
    val s2 = Channel.source[Int]("views")
    val s3 = Channel.source[Int]("purchases")

    val result = StreamDSL.route((s1, s2, s3))((a, b, c) =>
      RouteConnective.apply((a.merge(b), c))
    )
    assert(result != null)
  }

  test("NEGATIVE: Route drops an input stream (ForAll-Relevant violation)") {
    val obtained = compileErrors("""
      import ChannelOps.{given, *}
      import restrictedfn.RestrictedSelectable.{given, *}

      val s1 = Channel.source[Int]("clicks")
      val s2 = Channel.source[Int]("views")

      // Should fail: s2 is never consumed by any sink
      val result = StreamDSL.route((s1, s2))((a, b) =>
        RouteConnective.apply((a, a))
      )
    """)
    assert(obtained.contains(TestUtils.forAll) && obtained.contains(TestUtils.relevant), s"obtained: $obtained")
  }

  test("NEGATIVE: Route drops all inputs (ForAll-Relevant violation)") {
    val obtained = compileErrors("""
      import ChannelOps.{given, *}
      import restrictedfn.RestrictedSelectable.{given, *}

      val s1 = Channel.source[Int]("clicks")
      val s2 = Channel.source[Int]("views")
      val s3 = Channel.source[Int]("purchases")

      // Should fail: none of the 3 inputs are consumed by any sink
      val result = StreamDSL.route((s1, s2, s3))((a, b, c) =>
        RouteConnective.apply(Tuple1(a))
      )
    """)
    assert(obtained.contains(TestUtils.forAll) && obtained.contains(TestUtils.relevant), s"obtained: $obtained")
  }
