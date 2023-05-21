package maf.cli.experiments.precision

import maf.bench.scheme.SchemeBenchmarkPrograms
import maf.cli.experiments.SchemeAnalyses
import maf.cli.experiments.precision.DailyPrecisionBenchmarks.Analysis
import maf.cli.runnables.OptimizeProgram
import maf.core.Address
import maf.language.CScheme.CSchemeParser
import maf.language.scheme.lattices.ModularSchemeLattice
import maf.language.scheme.primitives.SchemePrelude
import maf.language.scheme.{SchemeExp, SchemeMutableVarBoxer, SchemeRenamer}
import maf.lattice.ConstantPropagation
import maf.lattice.ConstantPropagation.{B, C, I, R, S, Sym}
import maf.modular.{AnalysisEntry, AnalysisResults}
import maf.modular.scheme.{ModularSchemeDomain, ModularSchemeLatticeWrapper, SchemeConstantPropagationDomain}
import maf.modular.scheme.modflocal.{SchemeModFLocal, SchemeModFLocalAnalysisResults, SchemeModFLocalCallSiteSensitivity}
import maf.modular.worklist.FIFOWorklistAlgorithm
import maf.util.{Reader, Writer}
import maf.util.benchmarks.{Table, Timeout}

import scala.concurrent.duration.{Duration, MINUTES, SECONDS}

object OptimizationPrecisionBenchmarks extends AnalysisComparison[
  ConstantPropagation.I,
  ConstantPropagation.R,
  ConstantPropagation.B,
  ConstantPropagation.C,
  ConstantPropagation.S,
  ConstantPropagation.Sym
]:

  def benchmarks = SchemeBenchmarkPrograms.gabriel

  type Analysis2 = Analysis & SchemeModFLocal & SchemeModFLocalAnalysisResults

  // timeout configuration
  override def analysisTimeout() = Timeout.start(Duration(5, MINUTES)) //timeout for (non-base) analyses

  override def concreteTimeout() = Timeout.start(Duration(20, SECONDS))

  def baseAnalysis(prg: SchemeExp): Analysis2 =
    val analysis = SchemeAnalyses.modflocalAnalysis(prg, 0)
    analysis.setGarbageCollection(false)
    analysis

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

  def otherAnalyses(): List[(SchemeExp => Analysis2, String)] = List(
    getAnalysis1(),
    getAnalysis2(),
    getAnalysis3(),
    getAnalysis4(),
    getAnalysis5(),
    getAnalysis6(),
    getAnalysis7()
  )


  var optimizationResults: Table[(Int, Map[String, Int])] = Table.empty[(Int, Map[String, Int])]

  def optimizeBenchmark(benchmark: Benchmark) =
    val txt = Reader.loadFile(benchmark)
    val parsed = CSchemeParser.parse(txt)
    val prelud = SchemePrelude.addPrelude(parsed, incl = Set("__toplevel_cons", "__toplevel_cdr", "__toplevel_set-cdr!"))
    val transf = SchemeMutableVarBoxer.transform(prelud)
    val program = CSchemeParser.undefine(transf)
    val renamed: SchemeExp = SchemeRenamer.rename(program)

    print(renamed)


    var res: (Int, Map[String, Int]) = OptimizeProgram.optimizeProgramWithAnalysis(txt, baseAnalysis(renamed))
    optimizationResults = optimizationResults.add(benchmark, "Base Analysis", res)
    OptimizeProgram.reset()

    // run the other analyses on the benchmark
    otherAnalyses().foreach { case (analysis, name) =>
      val res: (Int, Map[String, Int]) = OptimizeProgram.optimizeProgramWithAnalysis(txt, analysis(renamed))
      OptimizeProgram.reset()

      optimizationResults = optimizationResults.add(benchmark, name, res)
    }

  override def parseProgram(txt: Benchmark): SchemeExp =
    val parsed = CSchemeParser.parse(txt)
    val prelud = SchemePrelude.addPrelude(parsed, incl = Set("__toplevel_cons", "__toplevel_cdr", "__toplevel_set-cdr!"))
    val transf = SchemeMutableVarBoxer.transform(prelud)
    val program = CSchemeParser.undefine(transf)
    SchemeRenamer.rename(program)

  def main(args: Array[String]) =
    benchmarks.foreach(runBenchmark)
    println(results.prettyString(format = _.map(_.toString()).getOrElse("TIMEOUT")))
    val writer = Writer.open("benchOutput/precision/optimization-benchmarks.csv")
    Writer.write(writer, results.toCSVString(format = _.map(_.toString()).getOrElse("TIMEOUT"), rowName = "benchmark"))
    Writer.close(writer)
