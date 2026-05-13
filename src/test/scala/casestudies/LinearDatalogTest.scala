package test.casestudies

import restrictedfn.{Multiplicity, RestrictedSelectable}
import RestrictedSelectable.{given, *}
import munit.FunSuite
import test.TestUtils
import test.casestudies.{Query, QueryOps}
import QueryOps.{given, *}
import scala.NamedTuple.*

import scala.annotation.experimental

type IntRow = (i1: Int, i2: Int)

class LinearDatalogTest extends FunSuite:

  test("Construct normal query") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val q1 = Query.edb[IntRow]("q1", "i1", "i2")
    val q2 = Query.edb[IntRow]("q2", "i1", "i2")
    val query1 = for
      a1 <- q1
      a2 <- q2
    yield a1.i1 + a2.i2

    val query2 = q1.flatMap(a1 =>
      q2.map(a2 =>
        a1.i1 + a2.i1
      )
    )

    println(query2)
  }

  test("Transitive closure (classic recursive query)") {
    // Classic transitive closure: path(x,y) :- edge(x,y).
    //                             path(x,z) :- path(x,y), edge(y,z).
    val edges = Query.edb[IntRow]("edge", "i1", "i2")
    val path = Query.fixedPoint(Tuple1(edges))((pathTuple) =>
      DatalogConnective.apply(Tuple1(
        pathTuple._1.flatMap(p =>
          edges
            .filter(e => p.i2 == e.i1)
            .map(e => (i1 = p.i1, i2 = e.i2))
        )
      ))
    )(0)
    println(path)
  }

  test("Generate Datalog from simple query") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val edges = Query.edb[IntRow]("edges", "i1", "i2")
    val datalog = edges.peek()
    // EDB queries now generate rules
    val expected = "p0(v0, v1) :- edges(v0, v1)."
    assertEquals(datalog, expected)
  }

  test("Generate Datalog from union query") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val q1 = Query.edb[IntRow]("q1", "i1", "i2")
    val q2 = Query.edb[IntRow]("q2", "i1", "i2")
    val unionQuery = q1.union(q2)
    val datalog = unionQuery.peek()
    // Union generates intermediate predicates for each branch, then combines them
    val expected = """p1(v0, v1) :- q1(v0, v1).

p2(v2, v3) :- q2(v2, v3).

p0(v4, v5) :- p1(v4, v5).
p0(v4, v5) :- p2(v4, v5)."""
    assertEquals(datalog, expected)
  }

  test("Generate Datalog from map query") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val edges = Query.edb[IntRow]("edges", "i1", "i2")
    val mapped = edges.map(e => (i1 = e.i2, i2 = e.i1))
    val datalog = mapped.peek()
    // Should generate: intermediate predicate for edges, then map it
    val expected = """p1(v0, v1) :- edges(v0, v1).

p0(v3, v2) :- p1(v2, v3)."""
    assertEquals(datalog, expected)
  }
  
  test("Generate Datalog from constant map query") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val edges = Query.edb[IntRow]("edges", "i1", "i2")
    val mapped = edges.map(e => (i1 = e.i2, i2 = Expr.ExprLit(10)))
    val datalog = mapped.peek()
    // Should generate: intermediate predicate for edges, then map with constant
    val expected = """p1(v0, v1) :- edges(v0, v1).

p0(v3, 10) :- p1(v2, v3)."""
    assertEquals(datalog, expected)
  }

  test("Generate Datalog from identity map") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val edges = Query.edb[IntRow]("edges", "i1", "i2")
    val mapped = edges.map(e => (i1 = e.i1, i2 = e.i2))
    val datalog = mapped.peek()
    // Should generate: intermediate predicate for edges, then identity map
    val expected = """p1(v0, v1) :- edges(v0, v1).

p0(v2, v3) :- p1(v2, v3)."""
    assertEquals(datalog, expected)
  }

  test("Generate Datalog from complex query") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    // More complex: union then map
    val q1 = Query.edb[IntRow]("q1", "i1", "i2")
    val q2 = Query.edb[IntRow]("q2", "i1", "i2")
    val unionQuery = q1.union(q2)
    val mapped = unionQuery.map(e => (i1 = e.i2, i2 = e.i1))
    val datalog = mapped.peek()
    // Union creates intermediate predicates, then map swaps fields
    val expected = """p2(v0, v1) :- q1(v0, v1).

p3(v2, v3) :- q2(v2, v3).

p1(v4, v5) :- p2(v4, v5).
p1(v4, v5) :- p3(v4, v5).

p0(v7, v6) :- p1(v6, v7)."""
    assertEquals(datalog, expected)
  }

  test("Generate Datalog from constant filter query 1") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val edges = Query.edb[IntRow]("edges", "i1", "i2")
    val mapped = edges.filter(e => e.i2 == Expr.ExprLit(10))
    val datalog = mapped.peek()
    // Should generate: intermediate predicate for edges, then filter with constant
    val expected = """p1(v0, v1) :- edges(v0, v1).

p0(v2, v3) :- p1(v2, v3), v3 == 10."""
    assertEquals(datalog, expected)
  }
  test("Generate Datalog from constant filter query 2") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val edges = Query.edb[IntRow]("edges", "i1", "i2")
    val mapped = edges.filter(e => (e.i2 == Expr.ExprLit(10)) && (e.i1 == Expr.ExprLit(5)))
    val datalog = mapped.peek()
    // Should generate: intermediate predicate for edges, then filter with two constants
    val expected = """p1(v0, v1) :- edges(v0, v1).

p0(v2, v3) :- p1(v2, v3), v3 == 10, v2 == 5."""
    assertEquals(datalog, expected)
  }

  test("Generate Datalog from simple flatMap join") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val path = Query.edb[IntRow]("path", "i1", "i2")
    val query = path.flatMap(p1 =>
      path.filter(p2 => p1.i2 == p2.i1)
          .map(p2 => (i1 = p1.i1, i2 = p2.i2))
    )
    val datalog = query.peek()
    // Should generate: result(x, y) :- path(x, z), path(z, y)
    // Where p1.i2 == p2.i1 becomes the join condition (second field of first == first field of second)
    // And output is (p1.i1, p2.i2) which is (first of first, second of second)
    // Variables are unified inline: v6 is replaced with v3
    val expected = """p1(v0, v1) :- path(v0, v1).

p2(v4, v5) :- path(v4, v5).

p0(v2, v7) :- p1(v2, v3), p2(v3, v7)."""
    assertEquals(datalog, expected)
  }

  test("Generate Datalog from flatMap with two different EDBs") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val edges = Query.edb[IntRow]("edges", "i1", "i2")
    val nodes = Query.edb[IntRow]("nodes", "i1", "i2")
    val query = edges.flatMap(e =>
      nodes.filter(n => e.i2 == n.i1)
           .map(n => (i1 = e.i1, i2 = n.i2))
    )
    val datalog = query.peek()
    // Should generate: result(x, y) :- edges(x, z), nodes(z, y)
    // Variables are unified inline: v6 is replaced with v3
    val expected = """p1(v0, v1) :- edges(v0, v1).

p2(v4, v5) :- nodes(v4, v5).

p0(v2, v7) :- p1(v2, v3), p2(v3, v7)."""
    assertEquals(datalog, expected)
  }

  test("Generate Datalog from flatMap with join and constant constraint") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val edges = Query.edb[IntRow]("edges", "i1", "i2")
    val nodes = Query.edb[IntRow]("nodes", "i1", "i2")
    val query = edges.flatMap(e =>
      nodes.filter(n => (e.i2 == n.i1) && (n.i2 == Expr.ExprLit(10)))
           .map(n => (i1 = e.i1, i2 = n.i2))
    )
    val datalog = query.peek()
    // Should generate: result(x, y) :- edges(x, z), nodes(z, y), y == 10
    // Variables unified inline (e.i2 == n.i1 becomes shared variable)
    // Constant constraint kept (n.i2 == 10)
    val expected = """p1(v0, v1) :- edges(v0, v1).

p2(v4, v5) :- nodes(v4, v5).

p0(v2, v7) :- p1(v2, v3), p2(v3, v7), v7 == 10."""
    assertEquals(datalog, expected)
  }

  test("Generate Datalog from recursive fixedPoint query") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val edges = Query.edb[IntRow]("edges", "i1", "i2")
    val path = Query.fixedPoint(Tuple1(edges))((p) =>
      DatalogConnective.apply(Tuple1(
        p._1.flatMap(p1 =>
          edges.filter(e => p1.i2 == e.i1)
               .map(e => (i1 = p1.i1, i2 = e.i2))
        )
      ))
    )(0)
    val datalog = path.peek()
    // Should generate recursive path rules:
    // The structure creates intermediate predicates but the IDB predicate (idb0) is recursive:
    // - p1: base case (edges)
    // - p2: recursive case (join of p3 with edges)
    // - p3: reference to idb0
    // - idb0: union of p1 and p2, making it recursive
    // - p4: second occurrence of edges in the recursive case
    val expected = """p1(v0, v1) :- edges(v0, v1).

p3(v2, v3) :- idb0(v2, v3).

p4(v6, v7) :- edges(v6, v7).

p2(v4, v9) :- p3(v4, v5), p4(v5, v9).

idb0(v10, v11) :- p1(v10, v11).
idb0(v10, v11) :- p2(v10, v11)."""
    assertEquals(datalog, expected)
  }

  test("Generate Datalog from fixedPoint with 2 independent predicates") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    // Two independent recursive predicates: reachable and visited
    val edges = Query.edb[IntRow]("edges", "i1", "i2")
    val nodes = Query.edb[IntRow]("nodes", "i1", "i2")

    val (reachable, visited) = Query.fixedPoint((edges, nodes))((p) =>
      DatalogConnective.apply((
        // reachable: transitive closure of edges (independent of visited)
        p._1.flatMap(r =>
          edges.filter(e => r.i2 == e.i1)
               .map(e => (i1 = r.i1, i2 = e.i2))
        ),
        // visited: nodes that are reachable (independent of reachable)
        p._2.flatMap(v =>
          nodes.filter(n => v.i2 == n.i1)
               .map(n => (i1 = v.i1, i2 = n.i2))
        )
      ))
    )

    val datalog = reachable.peek()
    // Both predicates are in the same program, but they are independent
    // (idb0 doesn't reference idb1 and vice versa - they only reference themselves)
    val expected = """p1(v0, v1) :- edges(v0, v1).

p3(v2, v3) :- idb0(v2, v3).

p4(v6, v7) :- edges(v6, v7).

p2(v4, v9) :- p3(v4, v5), p4(v5, v9).

idb0(v10, v11) :- p1(v10, v11).
idb0(v10, v11) :- p2(v10, v11).

p5(v12, v13) :- nodes(v12, v13).

p7(v14, v15) :- idb1(v14, v15).

p8(v18, v19) :- nodes(v18, v19).

p6(v16, v21) :- p7(v16, v17), p8(v17, v21).

idb1(v22, v23) :- p5(v22, v23).
idb1(v22, v23) :- p6(v22, v23)."""
    assertEquals(datalog, expected)
  }

  test("Generate Datalog from fixedPoint with 2 predicates using union") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val edges1 = Query.edb[IntRow]("edges1", "i1", "i2")
    val edges2 = Query.edb[IntRow]("edges2", "i1", "i2")

    // Two predicates where second one unions the first
    val (path1, path2) = Query.fixedPoint((edges1, edges2))((p) =>
      DatalogConnective.apply((
        // path1: transitive closure of edges1
        p._1.flatMap(p1 =>
          edges1.filter(e => p1.i2 == e.i1)
                .map(e => (i1 = p1.i1, i2 = e.i2))
        ),
        // path2: combines path1 with transitive closure of edges2
        p._1.union(
          p._2.flatMap(p2 =>
            edges2.filter(e => p2.i2 == e.i1)
                  .map(e => (i1 = p2.i1, i2 = e.i2))
          )
        )
      ))
    )

    val datalog = path2.peek()
    // path2 references both idb0 (path1) and idb1 (itself)
    val expected = """p1(v0, v1) :- edges1(v0, v1).

p3(v2, v3) :- idb0(v2, v3).

p4(v6, v7) :- edges1(v6, v7).

p2(v4, v9) :- p3(v4, v5), p4(v5, v9).

idb0(v10, v11) :- p1(v10, v11).
idb0(v10, v11) :- p2(v10, v11).

p5(v12, v13) :- edges2(v12, v13).

p7(v14, v15) :- idb0(v14, v15).

p9(v16, v17) :- idb1(v16, v17).

p10(v20, v21) :- edges2(v20, v21).

p8(v18, v23) :- p9(v18, v19), p10(v19, v23).

p6(v24, v25) :- p7(v24, v25).
p6(v24, v25) :- p8(v24, v25).

idb1(v26, v27) :- p5(v26, v27).
idb1(v26, v27) :- p6(v26, v27)."""
    assertEquals(datalog, expected)
  }

  test("Generate Datalog from fixedPoint with 2 predicates using join") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val edges = Query.edb[IntRow]("edges", "i1", "i2")
    val labels = Query.edb[IntRow]("labels", "i1", "i2")

    // Two predicates where second one joins with the first
    val (path, labeledPath) = Query.fixedPoint((edges, labels))((p) =>
      DatalogConnective.apply((
        // path: transitive closure of edges
        p._1.flatMap(p1 =>
          edges.filter(e => p1.i2 == e.i1)
               .map(e => (i1 = p1.i1, i2 = e.i2))
        ),
        // labeledPath: joins path (p._1) with labels (p._2)
        p._1.flatMap(pth =>
          p._2.filter(l => pth.i2 == l.i1)
              .map(l => (i1 = pth.i1, i2 = l.i2))
        )
      ))
    )

    val datalog = labeledPath.peek()
    // labeledPath references idb0 (path) and idb1 (itself) via a join
    val expected = """p1(v0, v1) :- edges(v0, v1).

p3(v2, v3) :- idb0(v2, v3).

p4(v6, v7) :- edges(v6, v7).

p2(v4, v9) :- p3(v4, v5), p4(v5, v9).

idb0(v10, v11) :- p1(v10, v11).
idb0(v10, v11) :- p2(v10, v11).

p5(v12, v13) :- labels(v12, v13).

p7(v14, v15) :- idb0(v14, v15).

p8(v18, v19) :- idb1(v18, v19).

p6(v16, v21) :- p7(v16, v17), p8(v17, v21).

idb1(v22, v23) :- p5(v22, v23).
idb1(v22, v23) :- p6(v22, v23)."""
    assertEquals(datalog, expected)
  }

  test("Generate Datalog from fixedPoint with 3 predicates with dependencies") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val edges = Query.edb[IntRow]("edges", "i1", "i2")
    val nodes = Query.edb[IntRow]("nodes", "i1", "i2")
    val attrs = Query.edb[IntRow]("attrs", "i1", "i2")

    // Three predicates with complex dependencies
    val (path, reachableNodes, nodeAttrs) = Query.fixedPoint((edges, nodes, attrs))((p) =>
      DatalogConnective.apply((
        // path: transitive closure of edges
        p._1.flatMap(p1 =>
          edges.filter(e => p1.i2 == e.i1)
               .map(e => (i1 = p1.i1, i2 = e.i2))
        ),
        // reachableNodes: nodes reachable via path (uses p._1)
        p._1.flatMap(pth =>
          nodes.filter(n => pth.i2 == n.i1)
               .map(n => (i1 = pth.i1, i2 = n.i2))
        ),
        // nodeAttrs: combines reachableNodes with attrs (uses p._2 and p._3)
        p._2.flatMap(rn =>
          attrs.filter(a => rn.i2 == a.i1)
               .map(a => (i1 = rn.i1, i2 = a.i2))
        ).union(p._3)
      ))
    )

    val datalog = nodeAttrs.peek()
    // All three predicates (idb0, idb1, idb2) are in the program
    // nodeAttrs depends on reachableNodes (idb1) and attrs (idb2)
    val expected = """p1(v0, v1) :- edges(v0, v1).

p3(v2, v3) :- idb0(v2, v3).

p4(v6, v7) :- edges(v6, v7).

p2(v4, v9) :- p3(v4, v5), p4(v5, v9).

idb0(v10, v11) :- p1(v10, v11).
idb0(v10, v11) :- p2(v10, v11).

p5(v12, v13) :- nodes(v12, v13).

p7(v14, v15) :- idb0(v14, v15).

p8(v18, v19) :- nodes(v18, v19).

p6(v16, v21) :- p7(v16, v17), p8(v17, v21).

idb1(v22, v23) :- p5(v22, v23).
idb1(v22, v23) :- p6(v22, v23).

p9(v24, v25) :- attrs(v24, v25).

p12(v26, v27) :- idb1(v26, v27).

p13(v30, v31) :- attrs(v30, v31).

p11(v28, v33) :- p12(v28, v29), p13(v29, v33).

p14(v34, v35) :- idb2(v34, v35).

p10(v36, v37) :- p11(v36, v37).
p10(v36, v37) :- p14(v36, v37).

idb2(v38, v39) :- p9(v38, v39).
idb2(v38, v39) :- p10(v38, v39)."""
    assertEquals(datalog, expected)
  }

  test("Generate Datalog from fixedPoint with mutual recursion") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val edges = Query.edb[IntRow]("edges", "i1", "i2")
    val revEdges = Query.edb[IntRow]("revEdges", "i1", "i2")

    // Two mutually recursive predicates
    val (forward, backward) = Query.fixedPoint((edges, revEdges))((p) =>
      DatalogConnective.apply((
        // forward: uses both forward and backward paths
        p._1.flatMap(f =>
          edges.filter(e => f.i2 == e.i1)
               .map(e => (i1 = f.i1, i2 = e.i2))
        ).union(
          p._2.flatMap(b =>
            edges.filter(e => b.i2 == e.i1)
                 .map(e => (i1 = b.i1, i2 = e.i2))
          )
        ),
        // backward: uses both forward and backward paths
        p._2.flatMap(b =>
          revEdges.filter(e => b.i2 == e.i1)
                  .map(e => (i1 = b.i1, i2 = e.i2))
        ).union(
          p._1.flatMap(f =>
            revEdges.filter(e => f.i2 == e.i1)
                    .map(e => (i1 = f.i1, i2 = e.i2))
          )
        )
      ))
    )

    val datalog = forward.peek()
    // Both predicates reference each other (mutual recursion)
    val expected = """p1(v0, v1) :- edges(v0, v1).

p4(v2, v3) :- idb0(v2, v3).

p5(v6, v7) :- edges(v6, v7).

p3(v4, v9) :- p4(v4, v5), p5(v5, v9).

p7(v10, v11) :- idb1(v10, v11).

p8(v14, v15) :- edges(v14, v15).

p6(v12, v17) :- p7(v12, v13), p8(v13, v17).

p2(v18, v19) :- p3(v18, v19).
p2(v18, v19) :- p6(v18, v19).

idb0(v20, v21) :- p1(v20, v21).
idb0(v20, v21) :- p2(v20, v21).

p9(v22, v23) :- revEdges(v22, v23).

p12(v24, v25) :- idb1(v24, v25).

p13(v28, v29) :- revEdges(v28, v29).

p11(v26, v31) :- p12(v26, v27), p13(v27, v31).

p15(v32, v33) :- idb0(v32, v33).

p16(v36, v37) :- revEdges(v36, v37).

p14(v34, v39) :- p15(v34, v35), p16(v35, v39).

p10(v40, v41) :- p11(v40, v41).
p10(v40, v41) :- p14(v40, v41).

idb1(v42, v43) :- p9(v42, v43).
idb1(v42, v43) :- p10(v42, v43)."""
    assertEquals(datalog, expected)
  }

  // ============================================================================
  // NEGATIVE TESTS: These should fail to compile
  //
  // These tests verify that the type system catches violations of:
  // 1. ForEach-Affine: Each argument used at most once per return value
  // 2. ForAll-Relevant: Each argument used at least once across all returns
  //
  // Note: Wrong tuple sizes and type mismatches are also caught by these
  // multiplicity constraints, as they manifest as shape/usage violations.
  // ============================================================================

  test("NEGATIVE: too few returns - violates fixedPoint constraints") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val obtained = compileErrors("""
      import QueryOps.*

      val q1 = Query.edb[IntRow]("q1", "i1", "i2")
      val q2 = Query.edb[IntRow]("q2", "i1", "i2")

      // Should fail: 2 arguments but only 1 return
      val r = Query.fixedPoint((q1, q2))((a1, a2) =>
        DatalogConnective.apply(Tuple1(a1.union(a2)))  // Has both dependencies, but only 1 return
      )
    """)
    assert(obtained.contains(TestUtils.fixedPointReturnLengthFailed), s"obtained: $obtained")
  }

  test("NEGATIVE: too many returns - violates fixedPoint constraints") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val obtained = compileErrors("""
      import QueryOps.*
      import restrictedfn.RestrictedSelectable.Restricted

      val q1 = Query.edb[IntRow]("q1", "i1", "i2")
      val q2 = Query.edb[IntRow]("q2", "i1", "i2")
      val q3 = Query.edb[IntRow]("q3", "i1", "i2")

      // Should fail: 2 arguments but 3 returns
      // All arguments are used (ForAll-Relevant satisfied)
      // No argument used twice per return (ForEach-Affine satisfied)
      val r = Query.fixedPoint((q1, q2))((a1, a2) =>
        val q3Const: Restricted[Query[IntRow], EmptyTuple, EmptyTuple] = q3
        DatalogConnective.apply((a1, a2, q3Const))  // 3 returns from 2 args - wrong tuple size!
      )
    """)
    assert(obtained.contains(TestUtils.fixedPointReturnLengthFailed), s"obtained: $obtained")
  }

  test("NEGATIVE: wrong wrapped types") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val obtained = compileErrors(
      """
      import QueryOps.*

      val q1 = Query.edb[(k1: Int)]("q1")
      val q2 = Query.edb[(k1: String)]("q2")

      val r = Query.fixedPoint((q1, q2))((a1, a2) =>
        DatalogConnective.apply((a2, a1))  // Has both dependencies but wrong order
      )
    """)
    assert(obtained.contains(TestUtils.fixedPointReturnTypesFailed), s"obtained: $obtained")
  }

  test("NEGATIVE: ForEach-Affine - using argument twice in same return") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val obtained = compileErrors("""
      import QueryOps.*

      val q1 = Query.edb[IntRow]("q1", "i1", "i2")
      val q2 = Query.edb[IntRow]("q2", "i1", "i2")

      // Should fail: p._1 appears twice in the first return value (union with itself)
      val r = Query.fixedPoint((q1, q2))((p) =>
        DatalogConnective.apply((
          p._1.union(p._1),  // VIOLATION: p._1 used twice in same return!
          p._2
        ))
      )
    """)
    assert(obtained.contains(TestUtils.noGivenInstance), s"obtained: $obtained")
  }

  test("NEGATIVE: ForEach-Affine - using argument twice via intermediate") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val obtained = compileErrors("""
      import QueryOps.*

      val q1 = Query.edb[IntRow]("q1", "i1", "i2")
      val q2 = Query.edb[IntRow]("q2", "i1", "i2")

      // Should fail: p._1 appears twice in the first return value
      val r = Query.fixedPoint((q1, q2))((p) =>
        val temp = p._1  // intermediate reference
        DatalogConnective.apply((
          temp.union(p._1),  // VIOLATION: p._1 used twice (via temp and directly)
          p._2
        ))
      )
    """)
    assert(obtained.contains(TestUtils.noGivenInstance), s"obtained: $obtained")
  }

  test("NEGATIVE: ForAll-Relevant - forgetting to use an argument") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val obtained = compileErrors("""
      import QueryOps.*

      val q1 = Query.edb[IntRow]("q1", "i1", "i2")
      val q2 = Query.edb[IntRow]("q2", "i1", "i2")
      val q3 = Query.edb[IntRow]("q3", "i1", "i2")

      // Should fail: p._2 is never used in any return value
      val r = Query.fixedPoint((q1, q2))((p) =>
        DatalogConnective.apply((
          p._1,
          q3  // VIOLATION: Using q3 instead of p._2, so p._2 is unused!
        ))
      )
    """)
    println(s"obtailed: $obtained")
    // Both errors are valid signs that the constraint check rejected this code:
    // - The ForAll-Relevant violation (when match-type reduction reaches the
    //   violation marker)
    // - The fixedPoint return-type evidence failure (when LiftInnerType cannot
    //   reduce because q3 is a plain Query rather than a Restricted)
    assert(
      (obtained.contains(TestUtils.forAll) && obtained.contains(TestUtils.relevant)) ||
        obtained.contains(TestUtils.fixedPointReturnTypesFailed),
      s"obtained: $obtained"
    )
  }

  test("NEGATIVE: ForAll-Relevant - using external query instead") {
    Query.intensionalRefCount = 0
    Query.predCounter = 0

    val obtained = compileErrors("""
      import QueryOps.*

      val q1 = Query.edb[IntRow]("q1", "i1", "i2")
      val q2 = Query.edb[IntRow]("q2", "i1", "i2")
      val external = Query.edb[IntRow]("external", "i1", "i2")

      // Should fail: both arguments use external instead, so both p._1 and p._2 are unused
      val r = Query.fixedPoint((q1, q2))((p) =>
        DatalogConnective.apply((
          external,  // VIOLATION: should use p._1
          external   // VIOLATION: should use p._2
        ))
      )
    """)
    assert(
      (obtained.contains(TestUtils.forAll) && obtained.contains(TestUtils.relevant)) ||
        obtained.contains(TestUtils.fixedPointReturnTypesFailed),
      s"obtained: $obtained"
    )
  }
