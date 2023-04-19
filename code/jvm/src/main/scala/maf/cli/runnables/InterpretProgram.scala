package maf.cli.runnables

import maf.language.CScheme.*
import maf.language.change.CodeVersion.*
import maf.language.scheme.interpreter.*
import maf.language.scheme.primitives.SchemePrelude
import maf.util.Reader
import maf.util.benchmarks.Timeout

import scala.concurrent.duration.*

object InterpretProgram extends App:
  val text = Reader.loadFile("test/optimizations/constant-folding.scm")
  val interpreter = new SchemeInterpreter((_, _) => ())

  var nums: List[Long] = List()

  for (a <- 1 to 30) do
    try
      val start = System.currentTimeMillis()
      val res = interpreter.run(
        CSchemeParser.parseProgram(text),
        Timeout.start(Duration(10, MINUTES)),
        New
      )
      val end = System.currentTimeMillis()

      val diff: Long = end - start
      println(a + ": " + diff)
      if a >= 6 then
        nums = diff :: nums

    catch case ProgramError(msg) => System.err.nn.println(msg)

  println(nums)
