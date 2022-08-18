package maf.modular.incremental.scheme.modf

import maf.core.IdentityMonad
import maf.language.change.CodeVersion.*
import maf.core.*
import maf.language.scheme.*
import maf.language.sexp
import maf.modular.incremental.IncrementalGlobalStoreCY
import maf.modular.incremental.scheme.IncrementalSchemeSemantics
import maf.modular.incremental.scheme.lattice.IncrementalAbstractDomain
import maf.modular.scheme.*
import maf.modular.scheme.modf.*
import maf.util.benchmarks.Timeout

/** Implements big-step semantics for an incremental Scheme analysis. * */
trait IncrementalSchemeModFBigStepSemantics extends BigStepModFSemantics with IncrementalSchemeSemantics with IncrementalGlobalStoreCY[SchemeExp]:

    override def warn(msg: String): Unit = ()

    trait IncrementalSchemeModFBigStepIntra extends BigStepModFIntra with IncrementalIntraAnalysis with IncrementalGlobalStoreCYIntraAnalysis:
        override protected def eval(exp: SchemeExp): EvalM[Value] = exp match
            case SchemeCodeChange(e, _, _) if version == Old =>
                registerComponent(e, component)
                eval(e) // This could also be a super call if we assume no nesting of change expressions (which could be expected).
            case SchemeCodeChange(_, e, _) if version == New =>
                registerComponent(e, component)
                eval(e) // Same than above.
            case _ =>
                registerComponent(exp, component)
                super.eval(exp)

        /**
         * Evaluation of a conditional that handles implicit value flows.
         * @note
         *   See [Liu et al. 2010].
         */
        override protected def evalIf(prd: SchemeExp, csq: SchemeExp, alt: SchemeExp): EvalM[Value] =
            for
                prdVal <- eval(prd)
                // Implicit flows go from the predicate to the branches of the conditional.
                // When CY is disabled, no addresses will be present (and implicitFlows will be a list of empty sets).
                _ = { implicitFlows = lattice.getAddresses(prdVal) :: implicitFlows }
                adr = implicitFlows.flatten.toSet
                resVal <- cond(prdVal, eval(csq), eval(alt))
                _ = { implicitFlows = implicitFlows.tail }
            // Implicit flows need to be added to the return value of the if as well, as this value depends on the predicate.
            yield lattice.addAddresses(resVal, adr)

        /** Evaluation of a literal value that adds a "literal address" as source. */
        override protected def evalLiteralValue(literal: sexp.Value, exp: SchemeExp): M[Value] =
            // sorry for the Monad, Jens...
            // TODO: add to data flow, or add to provenance? (can't be part of SCC anyway, so best just to add to provenance?)
            if configuration.cyclicValueInvalidation
            then
                val a = LitAddr(exp)
                for
                    value <- super.evalLiteralValue(literal, exp).map(lattice.addAddress(_, a)) // Attach the address to the value for flow tracking.
                // _ = { if !lattice.isBottom(value) then intraProvenance += (a -> value) } // We can just overwrite any previous value as it will be the same.
                yield value
            else super.evalLiteralValue(literal, exp)

    override def intraAnalysis(cmp: Component): IncrementalSchemeModFBigStepIntra

    override def configString(): String = super.configString() + "\n  applying incremental big-step ModF Scheme semantics"
