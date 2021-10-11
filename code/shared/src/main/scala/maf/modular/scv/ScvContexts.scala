package maf.modular.scv

import maf.core.*
import maf.core.Position.*
import maf.language.scheme.*
import maf.modular.scheme.modf.*

/*
 * Soft contract verification uses the following forms of
 * context:
 *
 * - Contract call: if a function that is beinig monitored by a particular
 *   contract is called, the pre-condition and post-condition contracts
 *   are part of the context, and can be used during the analysis such
 *   that the preconditions can be assumed, and the post-condition
 *   can be checked, after the analysis of a particular component
 * - k-path conditions: during the analysis, the path conditions
 *    from the previous "k" components are added to the context
 *    to enable more precise symbolic information to be available during the
 *    analysis.
 */
sealed trait ScvContext[L]

/** Used when the function call is originating from applying a monitor */
case class ContractCallContext[L](domains: List[L], rangeContract: L, args: List[SchemeExp], idn: Identity) extends ScvContext[L]

/** Keeps track of the path conditions from the last k components */
case class KPathCondition[L](pc: List[List[SchemeExp]], numOfVars: Int) extends ScvContext[L]

case class NoContext[L]() extends ScvContext[L]

trait ScvContextSensitivity extends SchemeModFSensitivity:
    type ComponentContext = ScvContext[Value]

    def contractContext(cmp: Component): Option[ContractCallContext[Value]] = context(cmp).flatMap {
      case c: ContractCallContext[_] =>
        // safety: the ComponentContext is constrained to ScvContext[Value] (where
        // the type paremeter is invariant) which
        // means that ContractCallContext is always in L = Value otherwise
        // it does not type check. But unfortunately type parameters are erased
        // at runtime, and the isInstanceOf check cannot garuantee the type
        //  of the type parameter at runtime.
        Some(c.asInstanceOf[ContractCallContext[Value]])

      case _ => None
    }

    override def allocCtx(
        clo: (SchemeLambdaExp, Environment[Address]),
        args: List[Value],
        call: Position,
        caller: Component
      ): ComponentContext = NoContext() // contexts will be created by overriding them in the semantics

trait ScvKContextSensitivity extends ScvContextSensitivity with ScvModAnalysis:
    protected def k: Int
    protected def usingContract[X](cmp: Component)(f: Option[(List[Value], Value, List[SchemeExp], Identity)] => X): X = contractContext(cmp) match
        case Some(context) => f(Some(context.domains, context.rangeContract, context.args, context.idn))
        case _             => f(None)

    override def pathConditionFromContext(cmp: Component): (List[SchemeExp], Int) = context(cmp) match
        case Some(KPathCondition(pc, numVars)) => (pc.flatten, numVars)
        case _                                 => (List(), 0)

trait ScvOneContextSensitivity extends ScvKContextSensitivity:
    protected val k: Int = 1
