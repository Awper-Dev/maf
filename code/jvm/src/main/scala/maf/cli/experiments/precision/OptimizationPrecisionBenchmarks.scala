package maf.cli.experiments.precision

import maf.bench.scheme.SchemeBenchmarkPrograms
import maf.cli.experiments.SchemeAnalyses
import maf.cli.experiments.precision.AnalysisComparisonAlt1.Benchmark
import maf.cli.experiments.precision.DailyPrecisionBenchmarks.Analysis
import maf.cli.runnables.OptimizeProgram
import maf.core.Address
import maf.language.CScheme.CSchemeParser
import maf.language.scheme.lattices.ModularSchemeLattice
import maf.language.scheme.primitives.SchemePrelude
import maf.language.scheme.{SchemeExp, SchemeLet, SchemeMutableVarBoxer, SchemeRenamer, SchemeSet}
import maf.lattice.ConstantPropagation
import maf.lattice.ConstantPropagation.{B, C, I, R, S, Sym}
import maf.modular.{AnalysisEntry, AnalysisResults}
import maf.modular.scheme.{ModularSchemeDomain, ModularSchemeLatticeWrapper, SchemeConstantPropagationDomain}
import maf.modular.scheme.modflocal.{SchemeModFLocal, SchemeModFLocalAnalysisResults, SchemeModFLocalCallSiteSensitivity}
import maf.modular.worklist.FIFOWorklistAlgorithm
import maf.util.{Reader, Writer}
import maf.util.benchmarks.{Table, Timeout}

import scala.concurrent.duration.{Duration, MINUTES, SECONDS}

object OptimizationPrecisionBenchmarks extends AnalysisComparisonAlt[
  ConstantPropagation.I,
  ConstantPropagation.R,
  ConstantPropagation.B,
  ConstantPropagation.C,
  ConstantPropagation.S,
  ConstantPropagation.Sym
]:

  def benchmarks = SchemeBenchmarkPrograms.scp1Working

  type Analysis2 = Analysis & SchemeModFLocal & SchemeModFLocalAnalysisResults & SchemeModFLocalCallSiteSensitivity

  // timeout configuration
  override def timeout() = Timeout.start(Duration(15, MINUTES)) //timeout for (non-base) analyses

  //override def concreteTimeout() = Timeout.start(Duration(20, SECONDS))

  def baseAnalysis(prg: SchemeExp): Analysis2 =
    val analysis = SchemeAnalyses.modflocalAnalysis(prg, 0)
    analysis.setGarbageCollection(false)
    analysis

  def baseParams(): (Boolean, Int) = (false, 0)

  def getAnalysis1(): (SchemeExp => Analysis2, String) =
    ((exp: SchemeExp) => {
      val analysis = SchemeAnalyses.modflocalAnalysis(exp, 1)
      analysis.setGarbageCollection(false)
      analysis
    }, "K1-NO_GC")

  def getAnalysis2(): (SchemeExp => Analysis2, String) =
    ((exp: SchemeExp) => {
      val analysis = SchemeAnalyses.modflocalAnalysis(exp, 2)
      analysis.setGarbageCollection(false)
      analysis
    }, "K2-NO_GC")

  def getAnalysis3(): (SchemeExp => Analysis2, String) =
    ((exp: SchemeExp) => {
      val analysis = SchemeAnalyses.modflocalAnalysis(exp, 3)
      analysis.setGarbageCollection(false)
      analysis
    }, "K3-NO_GC")

  def getAnalysis4(): (SchemeExp => Analysis2, String) =
    ((exp: SchemeExp) => {
      val analysis = SchemeAnalyses.modflocalAnalysis(exp, 0)
      analysis.setGarbageCollection(true)
      analysis
    }, "K0-GC")

  def getAnalysis5(): (SchemeExp => Analysis2, String) =
    ((exp: SchemeExp) => {
      val analysis = SchemeAnalyses.modflocalAnalysis(exp, 1)
      analysis.setGarbageCollection(true)
      analysis
    }, "K1-GC")

  def getAnalysis6(): (SchemeExp => Analysis2, String) =
    ((exp: SchemeExp) => {
      val analysis = SchemeAnalyses.modflocalAnalysis(exp, 2)
      analysis.setGarbageCollection(true)
      analysis
    }, "K2-GC")

  def getAnalysis7(): (SchemeExp => Analysis2, String) =
    ((exp: SchemeExp) => {
      val analysis = SchemeAnalyses.modflocalAnalysis(exp, 3)
      analysis.setGarbageCollection(true)
      analysis
    }, "K3-GC")

  override def analyses: List[(SchemeExp => Analysis2, String)] = List(
    getAnalysis1(),
    getAnalysis2(),
    getAnalysis3(),
    getAnalysis4(),
    getAnalysis5(),
    getAnalysis6(),
    getAnalysis7()
  )

  def otherAnalysesParams(): List[(Boolean, Int)] = List(
    (false, 1),
    (false, 2),
    (false, 3),
    (true, 0),
    (true, 1),
    (true, 2),
    (true, 3)
  )


  var optimizationResults: Table[(Int, Map[String, Int])] = Table.empty[(Int, Map[String, Int])]

  def optimizeBenchmark(benchmark: Benchmark) =
    println("---------------------")
    println(";;; working on " + benchmark + "\n")
    val txt = Reader.loadFile(benchmark)

    val res: (Int, Map[String, Int], Int) = OptimizeProgram.fullyOptimize(txt, baseParams()._1, baseParams()._2)
    //optimizationResults = optimizationResults.add(benchmark, "Base Analysis", res)
    println("base: k0 GC OFF" + res)
    OptimizeProgram.reset()

    // run the other analyses on the benchmark
    otherAnalysesParams().foreach { case (gc, k) =>
      val res: (Int, Map[String, Int], Int) = OptimizeProgram.fullyOptimize(txt, gc, k)
      OptimizeProgram.reset()
      println("other: k: "+ k + " gc: " + gc + " res: " + res)
      //optimizationResults = optimizationResults.add(benchmark, name, res)
    }

  override def parseProgram(txt: Benchmark): SchemeExp =
    val parsed = CSchemeParser.parse(txt)
    val prelud = SchemePrelude.addPrelude(parsed, incl = Set("__toplevel_cons", "__toplevel_cdr", "__toplevel_set-cdr!"))
    val transf = SchemeMutableVarBoxer.transform(prelud)
    val program = CSchemeParser.undefine(transf)
    SchemeRenamer.rename(program)

  def main(args: Array[String]) =
    //benchmarks.foreach(optimizeBenchmark)

    //println(results.prettyString(format = _.map(_.toString()).getOrElse("TIMEOUT")))
    //val writer = Writer.open("benchOutput/precision/optimization-benchmarks-counts.csv")
    //Writer.write(writer, results.toCSVString(format = _.map(_.toString()).getOrElse("TIMEOUT"), rowName = "benchmark"))
    //Writer.close(writer)

    runBenchmarks(benchmarks)

  def runBenchmarks(benchmarks: Set[Benchmark]) =
    benchmarks.foreach(runBenchmark)
    val cols = analyses.map(_._2)
    println(results.prettyString(columns = cols))
    val writer = Writer.open("benchOutput/precision/precision-benchmarks.csv")
    Writer.write(writer, results.toCSVString(rowName = "benchmark", columns = cols))
    Writer.close(writer)
