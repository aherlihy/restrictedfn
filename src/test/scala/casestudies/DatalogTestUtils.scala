package test.casestudies

import scala.util.boundary

object DatalogTestUtils:

  /**
   * Compare two Datalog strings allowing variable name differences.
   *
   * Placeholders in `expected` use the syntax `name$KEY` (e.g., `p$A`, `v$X`).
   * The actual string uses concrete names (e.g., `p1`, `v42`). The comparator
   * checks that:
   *   - All literal text matches exactly
   *   - Each placeholder maps to a consistent concrete name
   *   - No two distinct placeholders map to the same concrete name (within the
   *     same prefix)
   *
   * Both strings are whitespace-normalized (leading/trailing stripped per line,
   * blank lines preserved).
   */
  def matchDatalog(expectedQuery: String, actualQuery: String): (Boolean, String) = boundary:
    val expected = normalize(expectedQuery)
    val actual = normalize(actualQuery)

    val placeholderPattern = "(\\w+)\\$(\\w+)".r

    val expectedParts = placeholderPattern.split(expected)
    val placeholders = placeholderPattern.findAllIn(expected).toList

    var transformed = actual
    var currentPosition = 0
    val mappings = collection.mutable.Map.empty[String, collection.mutable.Map[String, String]]

    for placeholder <- placeholders do
      val Array(varName, placeholderKey) = placeholder.split("\\$")
      mappings.getOrElseUpdate(varName, collection.mutable.Map.empty)

      val pattern = s"$varName\\d+".r
      pattern.findFirstMatchIn(transformed.substring(currentPosition)).foreach { m =>
        val actualNum = m.matched.stripPrefix(varName)
        val matchStart = m.start + currentPosition
        val matchEnd = m.end + currentPosition

        mappings(varName).get(placeholder) match
          case Some(mapped) =>
            if mapped != actualNum then
              boundary.break((false,
                s"Expected $mapped for $placeholder but found $actualNum"))
          case None =>
            if mappings(varName).values.exists(_ == actualNum) then
              boundary.break((false,
                s"Multiple placeholders pointing to the same number: $actualNum"))
            mappings(varName).addOne(placeholder, actualNum)

        transformed = transformed.substring(0, matchStart) +
          placeholder + transformed.substring(matchEnd)
        currentPosition = matchEnd
      }

    if transformed == expected then
      (true, "Match.")
    else
      val idx = transformed.zip(expected).indexWhere { case (a, b) => a != b }
      val ctx = 30
      val s = math.max(0, idx - ctx)
      val e = math.min(transformed.length, idx + ctx)
      (false,
        s"Mismatch at index $idx.\nExpected: '...${expected.slice(s, e)}...'\nActual  : '...${transformed.slice(s, e)}...'")

  private def normalize(s: String): String =
    s.linesIterator.map(_.trim).mkString("\n").trim
