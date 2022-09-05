package maf.modular.scheme.modflocal

import maf.core.*
import maf.core.Monad.*
import maf.util.Monoid.*
import maf.util.MonoidImplicits.*
import maf.modular.Dependency
import maf.util.Lens
import maf.core.worklist.WorkList
import maf.util.benchmarks.Timeout

trait EffectLens[C, S] extends Lens[S]:
    /** "write" effects */
    def putWrites(s: S, w: Set[Dependency]): S
    def getWrites(s: S): Set[Dependency]
    def writes = (putWrites, getWrites)

    /** "read" effects */
    def putReads(s: S, w: Set[Dependency]): S
    def getReads(s: S): Set[Dependency]
    def reads = (putReads, getReads)

    /** "call" effects */
    def putCalls(s: S, c: Set[C]): S
    def getCalls(s: S): Set[C]
    def calls = (putCalls, getCalls)

    /** access to a field called "self" */
    def getSelfCmp(s: S): C

type EffectLensC = [C] =>> [S] =>> EffectLens[C, S]

trait EffectsM[M[_], Cmp, S] extends Monad[M]:
    /** The set of write effects */
    def ws: M[Set[Dependency]]

    /** The set of read effects */
    def rs: M[Set[Dependency]]

    /** The set of call effects */
    def cs: M[Set[Cmp]]

    /** Register a write effect */
    def trigger(w: Dependency): M[Unit]

    /** Register a read effect */
    def register(d: Dependency): M[Unit]

    /** Spawn a new component for analysis */
    def spawn(cmp: Cmp): M[Unit]

    /** Returns the component that is currently under analysis */
    def selfCmp: M[Cmp]

    /** Runs the effect-driven intra-analysis on cmp */
    def run(cmp: Cmp, m: M[Unit]): Set[S]

type EffectsMC[Cmp, S] = [M[_]] =>> EffectsM[M, Cmp, S]

object EffectsM:
    trait Configuration[C, V, Intra, Inter]:
        val emptyWL: WorkList[C]
        def sync(intra: Intra, inter: Inter): Inter
        val initialState: Inter
        val timeout: Timeout.T
        def inject(inter: Inter, cmp: C): DynMonad[V, EffectsMC[C, Intra]]

    enum AnalysisResult[Inter]:
        case Finished(i: Inter)
        case Timeout(i: Inter)

    /**
     * Run the evaluation of the given Monad until a fixed point is reached using a worklist algorithm based on effects.
     *
     * cf. Effect-Driven Flow Analysis p. 14.
     *
     * @param inject
     *   a function that injects a component in the intra-analysis monad
     * @param initial
     *   the initial component
     * @param wl
     *   the worklist implementation to use (usually initially empty)
     * @param sync
     *   a function that maps intra-analysis state to an inter-analysis state
     * @tparam M
     *   the monad to run the analysis in. Must implement the EffectsM typeclass
     * @tparam C
     *   the type of the components used in the analysis
     * @tparam IS
     *   the type of intra-analysis state
     * @tparam OS
     *   the type of outer-analysis state
     * @tparam V
     *   the type of abstract values used in the analysis
     */
    def fixWL[C, IS: EffectLensC[C], OS, V](initial: C, conf: Configuration[C, V, IS, OS]): AnalysisResult[OS] =
        import maf.util.Logger
        import maf.util.LogOps.*
        given Logger.Logger = Logger.DisabledLog()
        def loop(seen: Set[C], wl: WorkList[C], dep: Map[Dependency, Set[C]], interState: OS): AnalysisResult[OS] =
            if wl.isEmpty then AnalysisResult.Finished(interState)
            else if conf.timeout.reached then AnalysisResult.Timeout(interState)
            else
                val work = wl.head
                val nextWL = wl.tail
                val dyn = conf.inject(interState, work)
                val lens = summon[EffectLens[C, IS]]

                log(s"++ inter - analyzing component $work")
                val intras: Set[IS] = dyn.dynMonadInstance.run(work, dyn.contents.map(_ => ()))

                // perform a pointwise union
                val (ws: Set[Dependency], rs: Set[Dependency], cs: Set[C]) =
                    intras.foldLeft((Set.empty[Dependency], Set.empty[Dependency], Set.empty[C])) { case ((ws, rs, cs), intra) =>
                        (ws ++ lens.getWrites(intra), rs ++ lens.getReads(intra), cs ++ lens.getCalls(intra))
                    }

                log(s"=== read dep ===")
                rs.foreach(r => log(r.toString))
                log(s"=== write dep ===")
                ws.foreach(w => log(w.toString))
                log(s"=== spawns ===")
                cs.foreach(c => log(c.toString()))
                log("==============")

                // spawn all needed components
                val toSpawn = cs -- seen
                // register all read dependencies
                val depNew = dep ++ (rs.map(r => (r -> (dep.get(r).getOrElse(Set()) + work))))
                // reanalyze all components that are triggered by a dependency
                val toReanalyze = ws.flatMap(depNew.get(_).getOrElse(Set()))
                // synchronize the obtained state to the inter-analysis
                val newInter = intras.foldLeft(interState)((inter, intra) => conf.sync(intra, inter))
                // continue the analysis
                loop(seen ++ toSpawn, nextWL ++ toReanalyze ++ toSpawn, depNew, newInter)

        loop(Set(), conf.emptyWL + initial, Map(), conf.initialState)

/** Represents an effect-producing computation by using a state monad for tracking its state */
trait EffectsStateM[M[_], Cmp, S: EffectLensC[Cmp]] extends EffectsM[M, Cmp, S], StateOps[S, M]:
    private given Monad[M] = this

    private val lens: EffectLens[Cmp, S] = summon[EffectLens[Cmp, S]]

    /** The set of write effects */
    def ws: M[Set[Dependency]] =
        get.map(lens.getWrites)

    /** The set of read effects */
    def rs: M[Set[Dependency]] =
        get.map(lens.getReads)

    /** The set of call effects */
    def cs: M[Set[Cmp]] =
        get.map(lens.getCalls)

    /** Register a write effect */
    def trigger(w: Dependency): M[Unit] =
        get.map(lens.modify(lens.writes)(_ + w)) >>= put

    /** Register a read effect */
    def register(d: Dependency): M[Unit] =
        get.map(lens.modify(lens.reads)(_ + d)) >>= put

    /** Returns the component that is currently under analysis */
    def selfCmp: M[Cmp] =
        get.map(lens.getSelfCmp)

    def spawn(cmp: Cmp): M[Unit] =
        get.map(lens.modify(lens.calls)(_ + cmp)) >>= put
