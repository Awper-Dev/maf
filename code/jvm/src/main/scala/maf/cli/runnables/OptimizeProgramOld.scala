package maf.cli.runnables

import maf.cli.experiments.SchemeAnalyses
import maf.cli.runnables.OptimizeProgram.args
import maf.core.{Address, Expression, Identifier, Identity}
import maf.language.CScheme.CSchemeParser
import maf.language.scheme.lattices.ModularSchemeLattice
import maf.language.scheme.*
import maf.language.scheme.primitives.SchemePrelude
import maf.language.sexp.Value
import maf.lattice.ConstantPropagation.*
import maf.lattice.interfaces.IntLattice
import maf.lattice.{ConstantPropagation, HMap, HMapKey}
import maf.modular.DependencyTracking
import maf.modular.scheme.modf.{SchemeModFComponent, SchemeModFNoSensitivity, SimpleSchemeModFAnalysis}
import maf.modular.scheme.{ModularSchemeLatticeWrapper, SchemeConstantPropagationDomain, VarAddr}
import maf.modular.worklist.FIFOWorklistAlgorithm
import maf.util.{Default, Reader}

// TODO slides:
// 3 optimalisaties
// moeilijkheden tegengekomen
// wat ik nog zal doen : optimilisaties evalueren
// geef 2 mogelijkheden voor wat we nog zullen doen

object OptimizeProgramOld extends App:
 /* def hasUse(id: Identifier, inside: SchemeExp): Boolean = haveUse(List(id), List(inside)).nonEmpty

  /**
   *
   * @param id, list of identifiers to check use for
   * @param inside, list of expressions to check for uses
   * @return List of identifiers that have a use in the 'inside' List
   */
  def haveUse(id: List[Identifier], inside: List[SchemeExp], dependencies: Map[Identifier, Set[]]): List[Identifier] =
    def iterList(current: List[SchemeExp], acc: List[Identifier]): List[Identifier] =
      if current.isEmpty then
        acc
      else
        iterList(current.tail, List.concat(iter(current.head, Nil), acc))

    def iter(expr: SchemeExp, acc: List[Identifier]): List[Identifier] =
      expr match {
        case SchemeLambda(name, args, body, ann, idn) => iterList(body, acc) //hasUse(id, body)
        case SchemeVarArgLambda(name, args, vararg, body, ann, idn) => iterList(body, acc)//hasUse(id, body)
        case SchemeFuncall(f, args, idn) => iterList(List.concat(List(f), args), acc)// hasUse(id, f) || hasUse(id, args)
        case SchemeIf(cond, cons, alt, idn) => iterList(List(cond, cons, alt), acc) // hasUse(id, cond) || hasUse(id, cons) || hasUse(id, alt)
        case SchemeLet(bindings, body, idn) => iterList(List.concat(body, bindings.map((_, exp: SchemeExp) => exp)), acc) // hasUse(id, bindings.map((_, exp: SchemeExp) => exp)) || hasUse(id, body)
        case SchemeLetStar(bindings, body, idn) => iterList(List.concat(body, bindings.map((_, exp: SchemeExp) => exp)), acc)
        case SchemeLetrec(bindings, body, idn) => iterList(List.concat(body, bindings.map((_, exp: SchemeExp) => exp)), acc) // hasUse(id, bindings.map((_, exp: SchemeExp) => exp)) || hasUse(id, body)
        case SchemeSet(variable, value, idn) => iter(value, acc)// hasUse(id, value)
        case SchemeBegin(exps, idn) => iterList(exps, acc) // exps.exists((exp: SchemeExp) => hasUse(id, exp))
        case SchemeDefineVariable(name, value, idn) => iter(value, acc) // hasUse(id, value)
        case SchemeVar(idn) =>
          if id.exists((identifier) => identityCompare(identifier, idn)) && !acc.exists((identifier) => identityCompare(identifier, idn)) then
            idn :: acc
          else acc
        case SchemeValue(value, idn) => acc
        case other: Any => acc
      }

    iterList(inside, Nil)

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

  /** Removes all set!s of identifiers in the given list
   *
   * @param ids, identifiers that need their set!s removed
   * @param current, the expression to check for set!s
   * @return SchemeExp, the modified resulting expression
   */
  def removeSets(ids: List[Identifier], current: SchemeExp): SchemeExp =
    def remove(schemeExp: SchemeExp): Boolean =
      schemeExp match {
        case SchemeSet(variable, value, idn) => identifierContains(variable, ids)
        case _ => false
      }

    current match {
      case SchemeLambda(name, args, body, ann, idn) => SchemeLambda(name, args, body.filter((expr) => !remove(expr)), ann, idn)
      case SchemeVarArgLambda(name, args, vararg, body, ann, idn) => SchemeVarArgLambda(name, args, vararg, body.filter((expr) => !remove(expr)), ann, idn)
      case SchemeFuncall(f, args, idn) =>
        SchemeFuncall(removeSets(ids, f), args, idn)
      case SchemeIf(cond, cons, alt, idn) => SchemeIf(cond, cons, alt, idn)
      case SchemeLet(bindings, body, idn) =>
        val bindingIdentifiers = bindings.map((identifier, _) => identifier)
        val modifiedBody = body.filter((expr) => !remove(expr)).map((expr) => removeSets(ids, expr))

        if modifiedBody.isEmpty then SchemeValue(Value.Symbol("removed"), idn)
        else SchemeLet(bindings.map((identifier, expr) => (identifier, removeSets(ids, expr))), modifiedBody, idn)
      case SchemeLetStar(bindings, body, idn) =>
        val bindingIdentifiers = bindings.map((identifier, _) => identifier)
        val modifiedBody = body.filter((expr) => !remove(expr)).map((expr) => removeSets(ids, expr))

        if modifiedBody.isEmpty then SchemeValue(Value.Symbol("removed"), idn)
        else SchemeLetStar(bindings.map((identifier, expr) => (identifier, removeSets(ids, expr))), modifiedBody, idn)
      //SchemeLetStar(bindings, body, idn)
      //SchemeLetStar(bindings.filter((identifier, expr) => hasUse(identifier, body) || hasUse(identifier, bindings.map((identifier, expr) => expr))), body, idn)
      case SchemeLetrec(bindings, body, idn) =>
        SchemeLetrec(bindings.map((identifier, expr) => (identifier, removeUnusedVariables(expr))), body, idn)
      case SchemeSet(variable, value, idn) => SchemeSet(variable, value, idn)
      case SchemeBegin(exps, idn) => SchemeBegin(exps, idn)
      case SchemeDefineVariable(name, value, idn) =>
        SchemeDefineVariable(name, value, idn)
      case SchemeVar(id) => SchemeVar(id)
      case SchemeValue(value, idn) => SchemeValue(value, idn)
      case other: Any => other
    }

  /** Removes all unused variables of an expression
   *
   * @param current
   * @return
   */
  def removeUnusedVariables(current: List[SchemeExp]): List[SchemeExp] = current.map((expr) => removeUnusedVariables(expr))

  def removeUnusedVariables(current: SchemeExp): SchemeExp =
    current match {
      case SchemeLambda(name, args, body, ann, idn) => SchemeLambda(name, args, body, ann, idn)
      case SchemeVarArgLambda(name, args, vararg, body, ann, idn) => SchemeVarArgLambda(name, args, vararg, body, ann, idn)
      case SchemeFuncall(f, args, idn) => SchemeFuncall(f, args, idn)
      case SchemeIf(cond, cons, alt, idn) => SchemeIf(cond, cons, alt, idn)
      case SchemeLet(bindings, body, idn) =>
        val bindingIdentifiers = bindings.map((identifier, _) => identifier)
        val usedBindings = haveUse(bindingIdentifiers, body)
        val unUsedBindings = bindingIdentifiers.filter((id) => !identifierContains(id, usedBindings))
        val modifiedBody = removeUnusedVariables(body)
        val modifiedBindings = bindings.filter((identifier, _) => identifierContains(identifier, usedBindings))
        removeSets(unUsedBindings, SchemeLet(modifiedBindings, modifiedBody, idn))
      case SchemeLetStar(bindings, body, idn) =>
        val bindingIdentifiers = bindings.map((identifier, _) => identifier)
        val bindingExpressions = bindings.map((_, expr) => expr)
        val usedBindings = haveUse(bindingIdentifiers, List.concat(body, bindingExpressions))
        val unUsedBindings = bindingIdentifiers.filter((id) => !identifierContains(id, usedBindings))
        val modifiedBody = removeUnusedVariables(body)
        val modifiedBindings = bindings.filter((identifier, _) => identifierContains(identifier, usedBindings))
        removeSets(unUsedBindings, SchemeLetStar(modifiedBindings, modifiedBody, idn))
      //SchemeLetStar(bindings.filter((identifier, expr) => hasUse(identifier, body) || hasUse(identifier, bindings.map((identifier, expr) => expr))), body, idn)
      case SchemeLetrec(bindings, body, idn) =>
        val bindingIdentifiers = bindings.map((identifier, _) => identifier)
        val bindingExpressions = bindings.map((_, expr) => expr)
        val usedBindings = haveUse(bindingIdentifiers, List.concat(body, bindingExpressions))
        val unUsedBindings = bindingIdentifiers.filter((id) => !identifierContains(id, usedBindings))
        val modifiedBody = removeUnusedVariables(body)
        val modifiedBindings = bindings.filter((identifier, _) => identifierContains(identifier, usedBindings))
        removeSets(unUsedBindings, SchemeLetrec(modifiedBindings, modifiedBody, idn))
      //SchemeLetrec(bindings.map((identifier, expr) => (identifier, removeUnusedVariables(expr))), body, idn)
      case SchemeSet(variable, value, idn) => SchemeSet(variable, value, idn)
      case SchemeBegin(exps, idn) => SchemeBegin(exps, idn)
      case SchemeDefineVariable(name, value, idn) => SchemeDefineVariable(name, value, idn)
      case SchemeVar(id) => SchemeVar(id)
      case SchemeValue(value, idn) => SchemeValue(value, idn)
      case other: Any => other
    }

  //def optimize(program: SchemeExp, store: Map[Address, HMap], identities: Map[Identity, Address], lattice: ModularSchemeLattice[Address, ConstantPropagation.S, ConstantPropagation.B, ConstantPropagation.I, ConstantPropagation.R, ConstantPropagation.C, ConstantPropagation.Sym]): SchemeExp =
  def optimize(program: SchemeExp, mapping: Map[SchemeExp, Option[SchemeExp]]): SchemeExp =
    def optimizeExpressions(expressions: List[SchemeExp]) = expressions.map((expr: SchemeExp) => optimize(expr, mapping))
    def optimizeExpression(expression: SchemeExp) = optimize(expression, mapping)
    def optimizeSubExpressions(): SchemeExp =
      println("optimizing sub expressions")
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
    println("Working on: " + program.getClass)
    // See if current expression can be folded

    mapping.get(program) match {
      case Some(replacement: Option[SchemeExp]) =>
        replacement match {
          case Some(expr: SchemeExp) => expr
          case _ => optimizeSubExpressions()
        }
      case _ => optimizeSubExpressions()
    }

  /*program match {
      case schemeVariable: SchemeVar =>
          identities.get(program.idn) match {
              case Some(address: Address) =>
                  val value = store.get(address)
                  // benchmarks voor analyses
                  value match {
                      case Some(map: HMap) =>
                          val elements = map.elements

                          if elements.size == 1 then
                              val elem: lattice.Value = elements.last
                              elem match {
                                  // int bool symbol reals character emptylist
                                  case lattice.Int(i) =>
                                      i match {
                                          case Constant(bigInt) => SchemeValue(maf.language.sexp.Value.Integer(bigInt), program.idn)
                                          case _ => optimizeSubExpressions()
                                      }
                                  case lattice.Str(s) =>
                                      s match {
                                          case Constant(str) => SchemeValue(maf.language.sexp.Value.String(str), program.idn)
                                          case _ => optimizeSubExpressions()
                                      }
                                  case _ => optimizeSubExpressions()
                              }
                          else
                              optimizeSubExpressions()
                      case None => optimizeSubExpressions()
                  }

              case None => optimizeSubExpressions() // Optimize children
          }
      case _ => optimizeSubExpressions()
  }*/

  // + - / * met lexicale detectie

  def optimizeProgram(text: String): String =
    println("parsing...")

    val parsed = CSchemeParser.parse(text)
    val prelud = SchemePrelude.addPrelude(parsed, incl = Set("__toplevel_cons", "__toplevel_cdr", "__toplevel_set-cdr!"))
    val transf = SchemeMutableVarBoxer.transform(prelud)
    val program = CSchemeParser.undefine(transf)

    val renamed: SchemeExp = SchemeRenamer.rename(program)
    //val removedVariables: SchemeExp = removeUnusedVariables(renamed)
    //val analysis = SchemeAnalyses.contextInsensitiveAnalysis(renamed)
    val analysis = SchemeAnalyses.modflocalAnalysis(renamed, 1)

    //val lat: ModularSchemeLattice[Address, ConstantPropagation.S, ConstantPropagation.B, ConstantPropagation.I, ConstantPropagation.R, ConstantPropagation.C, ConstantPropagation.Sym] = analysis.modularLattice
    println(renamed.prettyString())
    println("analyzing...")
    analysis.analyze()
    println("optimizing...")
    println(analysis.constantValueMap)


    val result: SchemeExp = optimize(renamed, analysis.constantValueMap)
    //var result = renamed
    result.prettyString()

  println(optimizeProgram(Reader.loadFile("test/optimizations/constant-folding.scm")))
*/


  print("ok")