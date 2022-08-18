package maf.cli.runnables

import maf.bench.scheme.SchemeBenchmarkPrograms
import maf.cli.experiments.incremental.*
import maf.language.CScheme.*
import maf.language.change.CodeVersion.*
import maf.language.scheme.SchemeExp
import maf.language.scheme.interpreter.*
import maf.language.scheme.primitives.SchemePrelude
import maf.modular.*
import maf.modular.incremental.IncrementalConfiguration.*
import maf.modular.scheme.modf.*
import maf.modular.incremental.*
import maf.modular.incremental.scheme.IncrementalSchemeAnalysisInstantiations.*
import maf.modular.incremental.scheme.lattice.*
import maf.modular.incremental.scheme.modf.IncrementalSchemeModFBigStepSemantics
import maf.modular.scheme.*
import maf.modular.worklist.*
import maf.util.*
import maf.util.Writer.Writer
import maf.util.benchmarks.*

import scala.concurrent.duration.*

object IncrementalRun extends App:

    def newAnalysis(text: SchemeExp, configuration: IncrementalConfiguration) =
        new IncrementalSchemeModFAnalysisCPLattice(text, configuration)
            with IncrementalLogging[SchemeExp]
            //with IncrementalDataFlowVisualisation[SchemeExp]
            {
            override def focus(a: Addr): Boolean = a.toString == "VarAddr(x@<=:1:13)[Some(ε)]"
            mode = Mode.Coarse
            override def intraAnalysis(
                cmp: SchemeModFComponent
              ) = new IntraAnalysis(cmp)
                with IncrementalSchemeModFBigStepIntra
                with IncrementalGlobalStoreCYIntraAnalysis
                //  with AssertionModFIntra
                with IncrementalLoggingIntra
            //with IncrementalVisualIntra
        }

    // Performance benchmarks
    def perfAnalysis(e: SchemeExp, config: IncrementalConfiguration) = new IncrementalSchemeModFAnalysisTypeLattice(e, config)
        with SplitPerformance[SchemeExp]
        with IncrementalLogging[SchemeExp] {
        mode = Mode.Summary
        var cnt = 0
        override def run(timeout: Timeout.T) =
            super.run(timeout)
            println(cnt)
        override def intraAnalysis(cmp: Component) =
            new IntraAnalysis(cmp)
                with IncrementalSchemeModFBigStepIntra
                with IncrementalGlobalStoreCYIntraAnalysis
                with SplitPerformanceIntra
                with IncrementalLoggingIntra {
                override def analyzeWithTimeout(timeout: Timeout.T): Unit =
                    cnt = cnt + 1
                    super.analyzeWithTimeout(timeout)
            }
    }

    // Analysis from soundness tests.
    def base(program: SchemeExp) = new ModAnalysis[SchemeExp](program)
        with StandardSchemeModFComponents
        with SchemeModFNoSensitivity
        with SchemeModFSemanticsM
        with LIFOWorklistAlgorithm[SchemeExp]
        with IncrementalSchemeModFBigStepSemantics
        with IncrementalSchemeTypeDomain // IncrementalSchemeConstantPropagationDomain
        with IncrementalGlobalStoreCY[SchemeExp]
        with IncrementalLogging[SchemeExp]
        //with IncrementalDataFlowVisualisation[SchemeExp]
        {
        override def focus(a: Addr): Boolean = false // a.toString.contains("VarAddr(n")
        var configuration: IncrementalConfiguration = ci
        mode = Mode.Fine
        override def intraAnalysis(
            cmp: Component
          ) = new IntraAnalysis(cmp) with IncrementalSchemeModFBigStepIntra with IncrementalGlobalStoreCYIntraAnalysis with IncrementalLoggingIntra
        //with IncrementalVisualIntra
    }

    abstract class BaseModFAnalysisIncremental(prg: SchemeExp, var configuration: IncrementalConfiguration)
        extends ModAnalysis[SchemeExp](prg)
        with StandardSchemeModFComponents
        with SchemeModFNoSensitivity
        with SchemeModFSemanticsM
        with IncrementalSchemeModFBigStepSemantics
        with IncrementalSchemeTypeDomain
        with IncrementalGlobalStoreCY[SchemeExp]
        with IncrementalLogging[SchemeExp] {
        override def focus(a: Addr): Boolean = a.toString.contains("VarAddr(l@map:1:16)")
        mode = Mode.Fine // Mode.Select
        override def warn(msg: String): Unit = ()
        override def intraAnalysis(cmp: Component) =
            new IntraAnalysis(cmp) with IncrementalSchemeModFBigStepIntra with IncrementalGlobalStoreCYIntraAnalysis with IncrementalLoggingIntra
    }

    def lifoAnalysis(b: SchemeExp) = new BaseModFAnalysisIncremental(b, ci_di_wi) with LIFOWorklistAlgorithm[SchemeExp]
    def fifoAnalysis(b: SchemeExp) = new BaseModFAnalysisIncremental(b, ci_di_wi) with FIFOWorklistAlgorithm[SchemeExp]

    // Runs the program with a concrete interpreter, just to check whether it makes sense (i.e., if the concrete interpreter does not error).
    // Useful when reducing a program when debugging the analysis.
    def interpretProgram(file: String): Unit =
        val prog = CSchemeParser.parseProgram(Reader.loadFile(file))
        val i = new SchemeInterpreter((_, _) => ())
        List(Old, New).foreach { version =>
            try
                print("*")
                i.run(prog, Timeout.start(Duration(3, MINUTES)), version)
            catch {
                case ProgramError(e) => System.err.nn.println(e)
            }
        }
        println("Done interpreting.")

    def checkEqState(a: BaseModFAnalysisIncremental, b: BaseModFAnalysisIncremental, message: String): Unit =
        (a.store.keySet ++ b.store.keySet).foreach { addr =>
            val valA = a.store.getOrElse(addr, a.lattice.bottom)
            val valB = b.store.getOrElse(addr, b.lattice.bottom)
            if valA != valB then System.err.nn.println(addr.toString + "\n" + a.lattice.compare(valA, valB))
        }
        assert(a.store.filterNot(_._2 == a.lattice.bottom) == b.store.filterNot(_._2 == b.lattice.bottom), message + " (store mismatch)")
        assert(a.visited == b.visited, message + " (visited set mismatch)")
        (a.deps.keySet ++ b.deps.keySet).foreach { dep =>
            val dA = a.deps.getOrElse(dep, Set())
            val dB = b.deps.getOrElse(dep, Set())
            if dA != dB then System.err.nn.println(dep.toString + "\n" + dA.mkString(" ") + "\n" + dB.mkString(" "))
        }
    // println(a.deps.toList.map(_.toString).sorted)
    // println(b.deps.toList.map(_.toString).sorted)
    /* assert(a.deps == b.deps, message + " (dependency mismatch)")
        assert(a.mapping == b.mapping, message + " (mapping mismatch)")
        assert(a.cachedReadDeps == b.cachedReadDeps, message + " (read deps mismatch)")
        assert(a.cachedSpawns == b.cachedSpawns, message + " (spawns mismatch)")
        assert(a.provenance == b.provenance, message + " (provenance mismatch)")
        assert(a.cachedWrites == b.cachedWrites, message + " (write cache mismatch)")
        //assert(a.implicitFlows == b.implicitFlows, message + " (flow mismatch)") // TODO Readd?
        assert(a.dataFlowR == b.dataFlowR, message + " (reverse flow mismatch)") */

    val modFbenchmarks: List[String] = List(
       "test/DEBUG1.scm"
     // "test/changes/scheme/reinforcingcycles/cycleCreation.scm",
      // "test/changes/scheme/satMiddle.scm",
       //"test/changes/scheme/satFine.scm",
      //"test/changes/scheme/reinforcingcycles/implicit-paths.scm",
       //"test/DEBUG3.scm",
       //"test/changes/scheme/nbody-processed.scm"
    )

    def newTimeout(): Timeout.T = Timeout.start(Duration(20, MINUTES))
    val configs = List(noOptimisations)

    modFbenchmarks.foreach { bench =>
        try {
            println(s"***** $bench *****")
            //interpretProgram(bench)
            val text = CSchemeParser.parseProgram(Reader.loadFile(bench))
            // println(text.prettyString())

            val l = lifoAnalysis(text)
            l.configuration = allOptimisations
            println("init")
            l.analyzeWithTimeout(newTimeout())
            assert(l.finished)
            //val scas = l.computeSCAs()
            // scas.foreach({ sca =>
            //    sca.foreach(a => println(l.store(a)))
            //     println
            // })
            println("upd")
            l.updateAnalysis(newTimeout())

            println("rean")
            val f = lifoAnalysis(text)
            f.version = New
            f.configuration = allOptimisations
            f.analyzeWithTimeout(newTimeout())
            assert(f.finished)

            //checkEqState(f, l,"")

            //val noOpt = a.deepCopy()
            //noOpt.configuration = noOptimisations
            //noOpt.logger.logU("***** NO OPT *****")
            //noOpt.updateAnalysis(newTimeout())
            //assert(noOpt.finished)

            //val full = newAnalysis(text, noOptimisations)
            //full.version = New
            //full.logger.logU("***** FULL *****")
            //full.analyzeWithTimeout(newTimeout())
            //assert(full.finished)
            /*
            configs.foreach { config =>
                println(config)
                val opt = l.deepCopy()
                opt.configuration = config
                //opt.logger.logU(s"***** ${config.toString} *****")
                opt.updateAnalysis(newTimeout())
                assert(opt.finished)

            // compareAnalyses(opt, full, s"${opt.configuration.toString} vs. Full")
            //compareAnalyses(opt, noOpt, s"${opt.configuration.toString} vs. No Opt")
            }
             */

        } catch {
            case e: Exception =>
                e.printStackTrace(System.out)
        }
    }

    println("\n\n**Done**\n\n")
end IncrementalRun

// Prints the maximal heap size.
object JVMMemorySize extends App:
    def formatSize(v: Long): String =
        if v < 1024 then return s"$v B"
        val z = (63 - java.lang.Long.numberOfLeadingZeros(v)) / 10
        s"${v.toDouble / (1L << (z * 10))} ${" KMGTPE".charAt(z)}B"

    println(formatSize(Runtime.getRuntime.nn.maxMemory()))

object IncrementalExtraction extends App:

    val text: String = "test/changes/scheme/satCoarse.scm"
    val version: Version = New

    val program = CSchemeParser.parseProgram(Reader.loadFile(text))
    println((if version == New then ProgramVersionExtracter.getUpdated(program) else ProgramVersionExtracter.getInitial(program)).prettyString())
