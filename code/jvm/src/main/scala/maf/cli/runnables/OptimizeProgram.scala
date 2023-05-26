package maf.cli.runnables

import maf.cli.experiments.SchemeAnalyses
import maf.cli.runnables.OptimizeProgram.args
import maf.core.{Address, Expression, Identifier, Identity}
import maf.language.CScheme.CSchemeParser
import maf.language.ContractScheme.ContractSchemeMutableVarBoxer.rewrite
import maf.language.scheme.lattices.ModularSchemeLattice
import maf.language.scheme.*
import maf.language.scheme.primitives.SchemePrelude
import maf.language.sexp.Value
import maf.lattice.ConstantPropagation.*
import maf.lattice.interfaces.IntLattice
import maf.lattice.{ConstantPropagation, HMap, HMapKey}
import maf.modular.DependencyTracking
import maf.modular.scheme.modf.{SchemeModFComponent, SchemeModFNoSensitivity, SimpleSchemeModFAnalysis}
import maf.modular.scheme.modflocal.{SchemeModFLocal, SchemeModFLocalAnalysisResults, SchemeModFLocalCallSiteSensitivity}
import maf.modular.scheme.{ModularSchemeLatticeWrapper, SchemeConstantPropagationDomain, VarAddr}
import maf.modular.worklist.FIFOWorklistAlgorithm
import maf.util.{Default, Reader}
import maf.util.benchmarks.{Table, Timeout}

import scala.concurrent.duration.{Duration, MINUTES}

// TODO slides:
// 3 optimalisaties
// moeilijkheden tegengekomen
// wat ik nog zal doen : optimilisaties evalueren
// geef 2 mogelijkheden voor wat we nog zullen doen

object OptimizeProgram extends App:
    def hasUse(id: Identifier, inside: SchemeExp): Boolean = hasUse(id, List(inside)).nonEmpty

    /**
     *
     * @param id, list of identifiers to check use for
     * @param inside, list of expressions to check for uses
     * @return List of identifiers that have a use in the 'inside' List
     */
    def hasUse(id: Identifier, inside: List[SchemeExp]): Set[Identifier] =
        var dependencies: Set[Identifier] = Set()
        def iterList(current: List[SchemeExp], above: Set[Identifier]): Unit =
            current.foreach((expr: SchemeExp) => iter(expr, above))
            //current.exists((expr: SchemeExp) => iter(expr, above)) // TODO join

        def iter(current: SchemeExp, above: Set[Identifier]): Unit =
            current match {
                case SchemeLambda(name, args, body, ann, idn) => iterList(body, above) //hasUse(id, body)
                case SchemeVarArgLambda(name, args, vararg, body, ann, idn) => iterList(body, above)//hasUse(id, body)
                case SchemeFuncall(f, args, idn) => iterList(List.concat(List(f), args), above)// hasUse(id, f) || hasUse(id, args)
                case SchemeIf(cond, cons, alt, idn) => iterList(List(cond, cons, alt), above) // hasUse(id, cond) || hasUse(id, cons) || hasUse(id, alt)
                case SchemeLet(bindings, body, idn) =>
                    iterList(body, above)
                    bindings.foreach((identifier: Identifier, exp: SchemeExp) => {
                        iter(exp, above + identifier)
                    })
                    //iterList(List.concat(body, bindings.map((_, exp: SchemeExp) => exp)), above) // TODO
                case SchemeLetStar(bindings, body, idn) => iterList(List.concat(body, bindings.map((_, exp: SchemeExp) => exp)), above) // TODO
                case SchemeLetrec(bindings, body, idn) => iterList(List.concat(body, bindings.map((_, exp: SchemeExp) => exp)), above) // TODO
                case SchemeSet(variable, value, idn) => iter(value, above)// hasUse(id, value)
                case SchemeBegin(exps, idn) => iterList(exps, above) // exps.exists((exp: SchemeExp) => hasUse(id, exp))
                case SchemeDefineVariable(name, value, idn) => iter(value, above) // hasUse(id, value) // TODO ADD
                case SchemeVar(idn) =>
                    if identityCompare(id, idn) then
                        above.foreach((identifier: Identifier) => dependencies = dependencies + identifier)
                case SchemeValue(value, idn) => {}
                case other: Any => {}
            }

        iterList(inside, Set())
        dependencies

    // HERE
    def hasActualUse(id: Identifier, inside: List[SchemeExp]): Boolean =
        var result = false
        def iterList(current: List[SchemeExp]): Unit =
            current.foreach((expr: SchemeExp) => iter(expr))
        //current.exists((expr: SchemeExp) => iter(expr, above)) // TODO join

        def iter(current: SchemeExp): Unit =
            current match {
                case SchemeLambda(name, args, body, ann, idn) => iterList(body) //hasUse(id, body)
                case SchemeVarArgLambda(name, args, vararg, body, ann, idn) => iterList(body) //hasUse(id, body)
                case SchemeFuncall(f, args, idn) => iterList(List.concat(List(f), args)) // hasUse(id, f) || hasUse(id, args)
                case SchemeIf(cond, cons, alt, idn) => iterList(List(cond, cons, alt)) // hasUse(id, cond) || hasUse(id, cons) || hasUse(id, alt)
                case SchemeLet(bindings, body, idn) =>
                    iterList(body)
                    bindings.foreach((identifier: Identifier, exp: SchemeExp) => {
                        iter(exp)
                    })
                //iterList(List.concat(body, bindings.map((_, exp: SchemeExp) => exp)), above) // TODO
                case SchemeLetStar(bindings, body, idn) => iterList(List.concat(body, bindings.map((_, exp: SchemeExp) => exp))) // TODO
                case SchemeLetrec(bindings, body, idn) => iterList(List.concat(body, bindings.map((_, exp: SchemeExp) => exp))) // TODO
                case SchemeSet(variable, value, idn) => iter(value) // hasUse(id, value)
                case SchemeBegin(exps, idn) => iterList(exps) // exps.exists((exp: SchemeExp) => hasUse(id, exp))
                case SchemeDefineVariable(name, value, idn) => iter(value) // hasUse(id, value) // TODO ADD
                case SchemeVar(idn) =>
                    if identityCompare(id, idn) then
                        result = true
                case SchemeValue(value, idn) => {}
                case other: Any => {}
            }

        iterList(inside)
        result

    /**
     * Compares two identifiers based on their names
     * @param id1, first Identifier to compare
     * @param id2, second Identifier to compare
     * @return Boolean, whether the identifiers are equal based on their names
     */
    def identityCompare(id1: Identifier, id2: Identifier): Boolean = id1.name.equals(id2.name)

    /** Checks whether a list contains a given identifier
     *
     * @param id, the identifier to check for
     * @param inside, the list to check for the identifier
     * @return Boolean, whether the list contains the identifier
     */
    def identifierContains(id: Identifier, inside: List[Identifier]): Boolean =
        if inside.isEmpty then
            false
        else identityCompare(inside.head, id) || identifierContains(id, inside.tail)


    def isSet(schemeVar: SchemeVar): Boolean = schemeVar.toString.equalsIgnoreCase("___toplevel_set-cdr!0")

    def isSetOf(exp: SchemeExp, identifier: Identifier): Boolean =
        exp match {
            case SchemeFuncall(f, args, idn) =>
                val schemeVar: SchemeVar = f.asInstanceOf[SchemeVar]
                if isSet(schemeVar) && args.nonEmpty then
                    val id: Identifier = args.head.asInstanceOf[SchemeVar].id
                    identityCompare(id, identifier)
                else false
            case _ => false
        }

    def isAccess(schemeVar: SchemeVar): Boolean = schemeVar.toString.equalsIgnoreCase("___toplevel_cdr0")

    /** Removes all set!s of identifiers in the given list
     *
     * @param ids, identifiers that need their set!s removed
     * @param current, the expression to check for set!s
     * @return SchemeExp, the modified resulting expression
     */
    def removeSets(ids: List[Identifier], current: SchemeExp, sideEffects: List[SchemeExp]): SchemeExp =
        def remove(schemeExp: SchemeExp): Boolean =
            schemeExp match {
                case SchemeSet(variable, value, idn) => identifierContains(variable, ids)
                case _ => false
            }

        //def isSet(schemeVar: SchemeVar): Boolean = schemeVar.toString.equalsIgnoreCase("___toplevel_set-cdr!0")
        //def isAccess(schemeVar: SchemeVar): Boolean = schemeVar.toString.equalsIgnoreCase("___toplevel_cdr0")

        current match {
            case SchemeLambda(name, args, body, ann, idn) => SchemeLambda(name, args, body.filter((expr) => !remove(expr)), ann, idn)
            case SchemeVarArgLambda(name, args, vararg, body, ann, idn) => SchemeVarArgLambda(name, args, vararg, body.filter((expr) => !remove(expr)), ann, idn)
            case SchemeFuncall(f, args, idn) =>
                val schemeVar: SchemeVar = f.asInstanceOf[SchemeVar]
                // is set
                if ids.exists((identifier:Identifier) => isSetOf(current, identifier)) then SchemeValue(Value.Symbol("removed"), idn)
                else SchemeFuncall(removeSets(ids, f, sideEffects), args.map((exp: SchemeExp) => removeSets(ids, exp, sideEffects)), idn)
            case SchemeIf(cond, cons, alt, idn) => SchemeIf(removeSets(ids, cond, sideEffects), removeSets(ids, cons, sideEffects), removeSets(ids, alt, sideEffects), idn)
            case SchemeLet(bindings, body, idn) =>
                val bindingIdentifiers = bindings.map((identifier, _) => identifier)
                val modifiedBody = body.filter((expr) => !remove(expr)).map((expr) => removeSets(ids, expr, sideEffects))

                if modifiedBody.isEmpty then SchemeValue(Value.Symbol("removed"), idn)
                else SchemeLet(bindings.map((identifier, expr) => (identifier, removeSets(ids, expr, sideEffects))), modifiedBody, idn)
            case SchemeLetStar(bindings, body, idn) =>
                val bindingIdentifiers = bindings.map((identifier, _) => identifier)
                val modifiedBody = body.filter((expr) => !remove(expr)).map((expr) => removeSets(ids, expr, sideEffects))

                if modifiedBody.isEmpty then SchemeValue(Value.Symbol("removed"), idn)
                else SchemeLetStar(bindings.map((identifier, expr) => (identifier, removeSets(ids, expr, sideEffects))), modifiedBody, idn)
                //SchemeLetStar(bindings, body, idn)
            //SchemeLetStar(bindings.filter((identifier, expr) => hasUse(identifier, body) || hasUse(identifier, bindings.map((identifier, expr) => expr))), body, idn)
            case SchemeLetrec(bindings, body, idn) =>
                val modifiedBody = body.filter((expr) => !remove(expr)).map((expr) => removeSets(ids, expr, sideEffects))

                if modifiedBody.isEmpty then SchemeValue(Value.Symbol("removed"), idn)
                else SchemeLet(bindings.map((identifier, expr) => (identifier, removeSets(ids, expr, sideEffects))), modifiedBody, idn)
                //SchemeLetrec(bindings.map((identifier, expr) => (identifier, removeUnusedVariables(expr, sideEffects))), body, idn)
            case SchemeSet(variable, value, idn) =>
                if ids.exists((identifier: Identifier) => identityCompare(identifier, variable)) then
                    SchemeValue(Value.Symbol("removed"), idn)
                else
                    SchemeSet(variable, value, idn)
            case SchemeBegin(exps, idn) => SchemeBegin(exps.map((exp: SchemeExp) => removeSets(ids, exp, sideEffects)), idn)
            case SchemeDefineVariable(name, value, idn) =>
                SchemeDefineVariable(name, removeSets(ids, value, sideEffects), idn)
            case SchemeVar(id) => SchemeVar(id)
            case SchemeValue(value, idn) => SchemeValue(value, idn)
            case other: Any => other
        }

    def findUnusedVariables(dependencyMap: Map[Identifier, Set[Identifier]], identifiers: List[Identifier]): Unit =
        var change = false // TODO possible false
        def iter(): Unit =
            dependencyMap.keySet.foreach((identifier: Identifier) => {
                if !unUsedVariables.contains(identifier) then
                    dependencyMap.get(identifier) match {
                        case Some(deps: Set[Identifier]) =>
                            if deps.isEmpty then
                                unUsedVariables = identifier :: unUsedVariables
                                change = true
                            else
                                if deps.forall((identifier: Identifier) => unUsedVariables.contains(identifier)) then
                                    unUsedVariables = identifier :: unUsedVariables
                                    change = true
                        case _ => {}
                    }
            })

            if change then
                change = false
                iter()

        iter()


    /** Removes all unused variables of an expression
     *
     * @param current
     * @return
     */
    def removeUnusedVariables(current: List[SchemeExp], sideEffects: List[SchemeExp]): List[SchemeExp] = current.map((expr) => removeUnusedVariables(expr, sideEffects))


    var dependencyMap: Map[Identifier, Set[Identifier]] = Map()
    var unUsedVariables: List[Identifier] = List()

    def reset(): Unit =
        dependencyMap = Map()
        unUsedVariables = List()
        counter = 0
        expressionCounter = Map()
        variableRemoveCount = 0

    def fillDependencyMap(current: SchemeExp): Unit = // TODO MOET LOPEN OVER HELE AST
        current match {
            case SchemeLambda(name, args, body, ann, idn) => SchemeLambda(name, args, body, ann, idn)
            case SchemeVarArgLambda(name, args, vararg, body, ann, idn) => SchemeVarArgLambda(name, args, vararg, body, ann, idn)
            case SchemeFuncall(f, args, idn) => SchemeFuncall(f, args, idn)
            case SchemeIf(cond, cons, alt, idn) => SchemeIf(cond, cons, alt, idn)
            case SchemeLet(bindings, body, idn) =>
                val bindingIdentifiers = bindings.map((identifier, expr) =>
                    fillDependencyMap(expr)
                    identifier)
                body.foreach((expr: SchemeExp) => fillDependencyMap(expr))
                bindingIdentifiers.foreach((identifier: Identifier) => dependencyMap = dependencyMap + (identifier -> hasUse(identifier, body)))

            // removeSets(unUsedBindings, SchemeLet(modifiedBindings, modifiedBody, idn))
            case SchemeLetStar(bindings, body, idn) => SchemeLetStar(bindings, body, idn)
            case SchemeLetrec(bindings, body, idn) =>
                bindings.foreach((identifier, expr) => fillDependencyMap(expr))
                //SchemeLetrec(bindings.map((identifier, expr) => (identifier, removeUnusedVariables(expr))), body, idn)
            case SchemeSet(variable, value, idn) => SchemeSet(variable, value, idn)
            case SchemeBegin(exps, idn) => SchemeBegin(exps, idn)
            case SchemeDefineVariable(name, value, idn) => SchemeDefineVariable(name, value, idn)
            case SchemeVar(id) => SchemeVar(id)
            case SchemeValue(value, idn) => SchemeValue(value, idn)
            case other: Any => other
        }

    def hasBodyUse(current: List[SchemeExp], identifier: Identifier): Boolean =
        current.exists((exp: SchemeExp) => hasBodyUse(exp, identifier))
    def hasBodyUse(current: SchemeExp, identifier: Identifier): Boolean =
        //println("currnet: " + current)
        current match {
            case SchemeVarLex(id, lex) =>
                //println("VAR LEX")
                identityCompare(id, identifier)
            case SchemeSetLex(id, lex, vexp, idn) =>
                if (identityCompare(id, identifier)) then
                    false
                else
                    //println("INSIDE BODY USE")
                    hasBodyUse(vexp, identifier)
            case SchemeLambda(name, args, body, ann, idn) => hasBodyUse(body, identifier)
            case SchemeVarArgLambda(name, args, vararg, body, ann, idn) => hasBodyUse(body, identifier)//SchemeVarArgLambda(name, args, vararg, body, ann, idn)
            case SchemeFuncall(f, args, idn) =>
                val schemeVar: SchemeVar = f.asInstanceOf[SchemeVar]

                if isSet(schemeVar) && args.nonEmpty then
                    val id: Identifier = args.head.asInstanceOf[SchemeVar].id
                    if (identityCompare(id, identifier)) then
                        false
                    else
                        hasBodyUse(List.concat(args, List(f)), identifier)
                else if isAccess(schemeVar) && args.nonEmpty then
                    val id: Identifier = args.head.asInstanceOf[SchemeVar].id
                    identityCompare(id, identifier)

                else hasBodyUse(List.concat(args, List(f)), identifier)
            case SchemeIf(cond, cons, alt, idn) => hasBodyUse(List(cond, cons, alt), identifier)
            case SchemeLet(bindings, body, idn) => hasBodyUse(body, identifier)
            case SchemeLetStar(bindings, body, idn) => hasBodyUse(body, identifier)
            case SchemeLetrec(bindings, body, idn) => hasBodyUse(body, identifier)
            case SchemeSet(variable, value, idn) =>
                if (identityCompare(variable, identifier)) then
                    false
                else
                    //println("INSIDE SET BODY USE")
                    hasBodyUse(value, identifier)
            case SchemeBegin(exps, idn) => hasBodyUse(exps, identifier)
            case SchemeDefineVariable(name, value, idn) => false
            case SchemeVar(id) =>
                //println("VAR")
                identityCompare(identifier, id)
            case SchemeValue(value, idn) => false
            case other: Any =>
                //println("OTHEEEEEEER " + other)
                false
        }

    def removeUnusedVariables(current: SchemeExp, sideEffects: List[SchemeExp]): SchemeExp =
        current match {
            case SchemeLambda(name, args, body, ann, idn) => SchemeLambda(name, args, body, ann, idn)
            case SchemeVarArgLambda(name, args, vararg, body, ann, idn) => SchemeVarArgLambda(name, args, vararg, body, ann, idn)
            case SchemeFuncall(f, args, idn) => SchemeFuncall(f, args, idn)
            case SchemeIf(cond, cons, alt, idn) => SchemeIf(cond, cons, alt, idn)
            case SchemeLet(bindings, body, idn) =>
                val bindingIdentifiers = bindings.map((identifier, _) => identifier)
                findUnusedVariables(dependencyMap, bindingIdentifiers)
                var modifiedBody = removeUnusedVariables(body, sideEffects)
                val modifiedBindings = bindings.filter((identifier, _) =>
                    //println("working on " + current)
                    //println("ic : " + !identifierContains(identifier, unUsedVariables))
                    //println("bu : " + hasBodyUse(body, identifier))
                    //println("se : " + sideEffects.contains(current))
                    val boolRes = !identifierContains(identifier, unUsedVariables) || hasBodyUse(body, identifier) || sideEffects.exists((exp: SchemeExp) => exp.idn == current.idn)
                    if !boolRes then variableRemoveCount +=1
                    boolRes)
                val usedIdentifiers = modifiedBindings.map((identifier: Identifier, _) => identifier)
                val unUsedIdentifiers = bindings.filter((identifier: Identifier, exp: SchemeExp) => !usedIdentifiers.contains(identifier)).map((identifier: Identifier, _) => identifier)
                //println("REMOVING SETS OF " + unUsedIdentifiers)
                modifiedBody = modifiedBody.map((exp: SchemeExp) => removeSets(unUsedIdentifiers, exp, sideEffects))
                SchemeLet(modifiedBindings, modifiedBody, idn)
                // removeSets(unUsedBindings, SchemeLet(modifiedBindings, modifiedBody, idn))
            case SchemeLetStar(bindings, body, idn) => SchemeLetStar(bindings, body, idn)
                /*val bindingIdentifiers = bindings.map((identifier, _) => identifier)
                val bindingExpressions = bindings.map((_, expr) => expr)
                val usedBindings = haveUse(bindingIdentifiers, List.concat(body, bindingExpressions))
                val unUsedBindings = bindingIdentifiers.filter((id) => !identifierContains(id, usedBindings))
                val modifiedBody = removeUnusedVariables(body)
                val modifiedBindings = bindings.filter((identifier, _) => identifierContains(identifier, usedBindings))
                removeSets(unUsedBindings, SchemeLetStar(modifiedBindings, modifiedBody, idn))*/

                //SchemeLetStar(bindings.filter((identifier, expr) => hasUse(identifier, body) || hasUse(identifier, bindings.map((identifier, expr) => expr))), body, idn)
            case SchemeLetrec(bindings, body, idn) => SchemeLetrec(bindings.map((identifier, expr) => (identifier, removeUnusedVariables(expr, sideEffects))), body, idn)
                /*val bindingIdentifiers = bindings.map((identifier, _) => identifier)
                val bindingExpressions = bindings.map((_, expr) => expr)
                val usedBindings = haveUse(bindingIdentifiers, List.concat(body, bindingExpressions))
                val unUsedBindings = bindingIdentifiers.filter((id) => !identifierContains(id, usedBindings))
                val modifiedBody = removeUnusedVariables(body)
                val modifiedBindings = bindings.filter((identifier, _) => identifierContains(identifier, usedBindings))
                removeSets(unUsedBindings, SchemeLetrec(modifiedBindings, modifiedBody, idn))*/
                //SchemeLetrec(bindings.map((identifier, expr) => (identifier, removeUnusedVariables(expr))), body, idn)
            case SchemeSet(variable, value, idn) => SchemeSet(variable, value, idn)
            case SchemeBegin(exps, idn) => SchemeBegin(exps, idn)
            case SchemeDefineVariable(name, value, idn) => SchemeDefineVariable(name, value, idn)
            case SchemeVar(id) => SchemeVar(id)
            case SchemeValue(value, idn) => SchemeValue(value, idn)
            case other: Any => other
        }

    var variableRemoveCount = 0
    var counter = 0
    var expressionCounter: Map[String, Int] = Map.empty

    //def optimize(program: SchemeExp, store: Map[Address, HMap], identities: Map[Identity, Address], lattice: ModularSchemeLattice[Address, ConstantPropagation.S, ConstantPropagation.B, ConstantPropagation.I, ConstantPropagation.R, ConstantPropagation.C, ConstantPropagation.Sym]): SchemeExp =
    def optimize(program: SchemeExp, mapping: Map[SchemeExp, Option[SchemeExp]]): SchemeExp =
        def optimizeExpressions(expressions: List[SchemeExp]) = expressions.map((expr: SchemeExp) => optimize(expr, mapping))
        def optimizeExpression(expression: SchemeExp) = optimize(expression, mapping)
        def optimizeSubExpressions(): SchemeExp =
            //println("optimizing sub expressions")
            //val newfac = Math.max(1, (Math.log(factor) / Math.log(2)).toInt)
            //val newfac = (factor / 3).toInt
            //println("newfac: " + newfac)
            program match {
                case SchemeLambda(name, args, body, ann, idn) => SchemeLambda(name, args, optimizeExpressions(body), ann, idn)
                case SchemeVarArgLambda(name, args, vararg, body, ann, idn) => SchemeVarArgLambda(name, args, vararg, optimizeExpressions(body), ann, idn)
                case SchemeFuncall(f, args, idn) => SchemeFuncall(optimizeExpression(f), optimizeExpressions(args), idn)
                case SchemeIf(cond, cons, alt, idn) => SchemeIf(optimizeExpression(cond), optimizeExpression(cons), optimizeExpression(alt), idn)
                case SchemeLet(bindings, body, idn) => SchemeLet(bindings.map((identifier, expr) => (identifier, optimizeExpression(expr))), optimizeExpressions(body), idn)
                case SchemeLetStar(bindings, body, idn) => SchemeLetStar(bindings.map((identifier, expr) => (identifier, optimizeExpression(expr))), optimizeExpressions(body), idn)
                case SchemeLetrec(bindings, body, idn) => SchemeLetrec(bindings.map((identifier, expr) => (identifier, optimizeExpression(expr))), optimizeExpressions(body), idn)
                case SchemeSet(variable, value, idn) => SchemeSet(variable, optimizeExpression(value), idn)
                case SchemeBegin(exps, idn) => SchemeBegin(optimizeExpressions(exps), idn)
                case SchemeDefineVariable(name, value, idn) => SchemeDefineVariable(name, optimizeExpression(value), idn)
                case SchemeVar(id) => SchemeVar(id)
                case SchemeValue(value, idn) => SchemeValue(value, idn)
                case other: Any => other
            }
       // println("Working on: " + program.getClass)
        // See if current expression can be folded

        mapping.get(program) match {
            case Some(replacement: Option[SchemeExp]) =>
                replacement match {
                    case Some(expr: SchemeExp) =>
                        if expr != program then
                            expressionCounter.get(program.getOptimizationPlaceName) match {
                                case Some(counter: Int) => expressionCounter = expressionCounter.updated(program.getOptimizationPlaceName, counter + 1)
                                case _ => expressionCounter = expressionCounter.updated(program.getOptimizationPlaceName, 1)
                            }
                            //expressionCounter = expressionCounter + program.getOptimizationPlaceName
                            counter += program.size + 1
                        expr
                    case _ => optimizeSubExpressions()
                }
            case _ => optimizeSubExpressions()
        }

    // + - / * met lexicale detectie

    type optimizationAnalysis = SchemeModFLocal & SchemeConstantPropagationDomain & SchemeModFLocalCallSiteSensitivity & FIFOWorklistAlgorithm[SchemeExp] & SchemeModFLocalAnalysisResults

    def renameProgram(text: String): String =
        val parsed: SchemeExp = CSchemeParser.parseProgram(text)
        val renamed: SchemeExp = SchemeRenamer.rename(parsed)

        renamed.prettyString()

    def optimizeUnusedProgram(text: String, gc: Boolean, k: Int, processed: Boolean): String =
        //val origParsed = SchemeParser.parseProgram(text)
        var renamed = CSchemeParser.parseProgram(text)

        if !processed then
            val parsed = CSchemeParser.parse(text)
            val prelud = SchemePrelude.addPrelude(parsed, incl = Set("__toplevel_cons", "__toplevel_cdr", "__toplevel_set-cdr!"))
            val transf = SchemeMutableVarBoxer.transform(prelud)
            val program = CSchemeParser.undefine(transf)
            renamed = SchemeRenamer.rename(program)
        //val origRenamed: SchemeExp = SchemeRenamer.rename(origParsed)

        val garbageCollection = gc
        val analysis = SchemeAnalyses.modflocalAnalysis(renamed, k)
        analysis.setGarbageCollection(garbageCollection)
        analysis.analyzeWithTimeout(Timeout.start(Duration(15, MINUTES)))

        fillDependencyMap(renamed)
        //println("map:")
        //println(dependencyMap)
        //println("side effects: ")
        //println(analysis.sideEffectedExpressions)
        val removed = removeUnusedVariables(renamed, analysis.sideEffectedExpressions)//analysis.sideEffectedExpressions)

        removed.prettyString()

    def optimizeUnusedProgramWithSpecific(text: String, gc: Boolean, k: Int, processed: Boolean): String =
        //val origParsed = SchemeParser.parseProgram(text)
        var renamed = CSchemeParser.parseProgram(text)

        if !processed then
            val parsed = CSchemeParser.parse(text)
            val prelud = SchemePrelude.addPrelude(parsed, incl = Set("__toplevel_cons", "__toplevel_cdr", "__toplevel_set-cdr!"))
            val transf = SchemeMutableVarBoxer.transform(prelud)
            val program = CSchemeParser.undefine(transf)
            renamed = SchemeRenamer.rename(program)
        //val origRenamed: SchemeExp = SchemeRenamer.rename(origParsed)

        val garbageCollection = gc
        val analysis = SchemeAnalyses.modflocalAnalysis(renamed, k)
        analysis.setGarbageCollection(garbageCollection)
        analysis.analyze()

        fillDependencyMap(renamed)
        //println("map:")
        //println(dependencyMap)
        //println("side effects: ")
        //println(analysis.sideEffectedExpressions)
        val removed = removeUnusedVariables(renamed, analysis.sideEffectedExpressions) //analysis.sideEffectedExpressions)

        removed.prettyString()


    def optimizeProgramWithAnalysis(text: String, analysis: SchemeModFLocal & SchemeModFLocalAnalysisResults): (Int, Map[String, Int]) =
        val parsed = CSchemeParser.parse(text)
        val prelud = SchemePrelude.addPrelude(parsed, incl = Set("__toplevel_cons", "__toplevel_cdr", "__toplevel_set-cdr!"))
        val transf = SchemeMutableVarBoxer.transform(prelud)
        val program = CSchemeParser.undefine(transf)
        val renamed: SchemeExp = SchemeRenamer.rename(program)
        
        analysis.analyze()

        val result: SchemeExp = optimize(renamed, analysis.constantValueMap)
        (counter, expressionCounter)


    def fullyOptimize(text: String, gc: Boolean, k: Int): (Int, Map[String, Int], Int) =
        val folded = optimizeProgram(text, gc, k, false)
        val latest: String = optimizeUnusedProgram(folded, gc, k, true)
        // TODO omdraaien
        //optimizeUnusedProgram(folded, gc, k, true)
        //println(folded)
        (counter, expressionCounter, variableRemoveCount)


    def optimizeProgram(text: String, gc: Boolean, k: Int, processed: Boolean): String =
       // println("parsing...")

        var renamed = CSchemeParser.parseProgram(text)

        if !processed then
            val parsed = CSchemeParser.parse(text)
            val prelud = SchemePrelude.addPrelude(parsed, incl = Set("__toplevel_cons", "__toplevel_cdr", "__toplevel_set-cdr!"))
            val transf = SchemeMutableVarBoxer.transform(prelud)
            val program = CSchemeParser.undefine(transf)

            renamed = SchemeRenamer.rename(program)
            //val analysis = SchemeAnalyses.contextInsensitiveAnalysis(renamed)
        System.err.nn.println(renamed.prettyString())
        val garbageCollection = gc
        val analysis = SchemeAnalyses.modflocalAnalysis(renamed, k)
        analysis.setGarbageCollection(garbageCollection)

        //val lat: ModularSchemeLattice[Address, ConstantPropagation.S, ConstantPropagation.B, ConstantPropagation.I, ConstantPropagation.R, ConstantPropagation.C, ConstantPropagation.Sym] = analysis.modularLattice
        //println(renamed.prettyString())
        //println("analyzing...")
        analysis.analyzeWithTimeout(Timeout.start(Duration(15, MINUTES)))
        //println("optimizing...")
        //println(analysis.constantValueMap)

        analysis.constantValueMap.foreach(println)


        val result: SchemeExp = optimize(renamed, analysis.constantValueMap)
        "\n" + "Parameters: " + "k: " + k + " garbage collection: " + garbageCollection + "\n" + "Amount of optimizations: " + counter + "\n" + "Expression counts: " + expressionCounter + "\n" + result.prettyString()
        result.prettyString()

    //println(optimizeProgram(Reader.loadFile("test/optimizations/constant-folding.scm"), true, 1, false))
    println(optimizeProgram(Reader.loadFile("test/R5RS/scp1/haha.scm"), false, 1, false))
    //println(fullyOptimize(Reader.loadFile("test/optimizations/constant-folding.scm"), true, 1))
    //fullyOptimize(Reader.loadFile("test/optimizations/constant-folding.scm"), false, 0)

    /*

    k  = 0 -< alle function calls naar zelfde function samen.
    k = 1 -> onderscheiden op basis van call site (probleem bij fibonacci) garbage collection fixt het soms (door op te kuisen)
    -> gc uitzetten als k testen
    k > 1 -> k laatste call sites worden gebruikt -> factorial 3 -> recursie diepte 3 dus k 3 nodig (denk fac aux -> )

    no gc k 0
    no gc hogere k
    met garbage collection

    aantal optimalisaties bekijken

    precisie waarden uit PrecisionBenchmarks vergelijken met eigen resultaten

    background sectie -> constant propagation sectie uitleggen

    andere lattices: PowerSetLattice

    variables removal: deels op basis van AST, deels op analyze
    -> vergelijking geven tussen approaches van full analyse of deels
    -> bespreek de trade off, future work,...

    inhoudstabel van BT rapport

    optimize(optimize(p)) = optimize(p)
    */
