package maf.cli.runnables

import maf.bench.scheme.SchemeBenchmarkPrograms
import maf.language.CScheme.*
import maf.language.change.CodeVersion.*
import maf.language.scheme.interpreter.*
import maf.language.scheme.primitives.SchemePrelude
import maf.util.Reader
import maf.util.benchmarks.Timeout

import scala.concurrent.duration.*

object InterpretProgram extends App:
  def benchmarkFile(str: String) =
    //val text = Reader.loadFile("test/optimizations/constant-folding.scm")
    val text = Reader.loadFile(str)
    val interpreter = new SchemeInterpreter((_, _) => ())


    var nums: List[Long] = List()
    var optNums: List[Long] = List()

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

        //println(a + ": " + diff)
        if a >= 6 then
          nums = diff :: nums

      catch case ProgramError(msg) => System.err.nn.println(msg)
    println("------------")
    println(str)
    println(nums)
    /*for (a <- 1 to 30) do
      try
        val newText = OptimizeProgram.fullyOptimize(text, true, 1, false)
        val start2 = System.currentTimeMillis()
        val res2 = interpreter.run(
          CSchemeParser.parseProgram(newText),
          Timeout.start(Duration(10, MINUTES)),
          New
        )
        val end2 = System.currentTimeMillis()
        val diff2: Long = end2 - start2

        //println(a + ": " + diff)
        if a >= 6 then
          optNums = diff2 :: optNums

      catch case ProgramError(msg) => System.err.nn.println(msg)

    println("----------")
    println(str)
    println("regular: " + nums)
    println("optimized: " + nums)*/
  SchemeBenchmarkPrograms.bench3.foreach(benchmarkFile)
  //benchmarkFile("test/R5RS/scp-repeated/add-to-end.scm")