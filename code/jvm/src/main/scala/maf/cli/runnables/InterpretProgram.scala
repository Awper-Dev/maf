package maf.cli.runnables

import maf.language.CScheme.*
import maf.language.change.CodeVersion.*
import maf.language.scheme.interpreter.*
import maf.language.scheme.primitives.SchemePrelude
import maf.util.Reader
import maf.util.benchmarks.Timeout

import scala.collection.mutable.ArrayBuffer
import scala.concurrent.duration.*

object InterpretProgram extends App:
    val text = Reader.loadFile("optimizationBenchmarks/functionInlining/function-inlining-optimized-1.scm")
    val interpreter = new SchemeInterpreter((_, _) => ())

    val IGNORE_COUNT = 10

    try
        var times = new ArrayBuffer[Long]()
        for i <- 0 until 40 do
            val start = System.currentTimeMillis()
            val res = interpreter.run(
            CSchemeParser.parseProgram(text),
            Timeout.start(Duration(10, MINUTES)),
            New
            )
            val end = System.currentTimeMillis();
            val diff = end - start

            if i >= IGNORE_COUNT then
                times = times.addOne(diff)

            val seconds = diff / 1000
            val milliseconds = diff % 1000

            println("run " + i + ": " + res.toString + ", took: " + seconds + " seconds and " + milliseconds)

        /** The following variables will not be used as official numbers. They are here just to give the user an idea after the run. */
        var mean: Long = 0
        times.foreach((long) => {
            mean += long
        })
        mean /= times.size

        var stdVariance: Long = 0
        times.foreach((long) => {
            val squaredDeviation = (long - mean) * (long - mean)
            stdVariance += squaredDeviation
        })
        stdVariance /= times.size
        stdVariance = Math.sqrt(stdVariance.toDouble).asInstanceOf[Long]
        println(times.toString().replaceAll(", ", ","))
        println("Average run length (ignored first " + IGNORE_COUNT + " runs): " + mean + " Standard variance: " + stdVariance)

    catch case ProgramError(msg) => System.err.nn.println(msg)
