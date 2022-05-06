package maf.language.symbolic

import maf.language.scheme.*
import maf.core.*
import maf.core.Position.*
import maf.core.Monad.MonadSyntaxOps
import maf.core.Monad.MonadIterableOps

object Formula:
    def join(formulas: Formula*): Formula =
        import FormulaAux.*
        DNF.dnf(disj(formulas: _*))

/** A formula that can occur on the path condition */
sealed trait Formula:
    /** Returns the consistuents of the formula */
    def elements: Set[Formula]

    /** Map a function over all the assertions in the formula. Returns a new formula where the assertions are mapped using the mapping function */
    def mapOptionM[M[_]: Monad](f: SchemeExp => M[Option[SchemeExp]]): M[Option[Formula]]

    def mapOption(f: SchemeExp => Option[SchemeExp]): Option[Formula] =
        mapOptionM[IdentityMonad.Id](f)

    def map(f: SchemeExp => SchemeExp): Formula =
        mapOptionM[IdentityMonad.Id](e => Some(f(e))).get

    /** Split the formula into its constituents if it is a conjunction */
    def splitConj: List[Formula]

    /** Split the formula into its constituents if it is a disjunction */
    def splitDisj: List[Formula]

    /** The number of assertions in the path condition */
    def size: Int

    /** Replace a particular symbolic expression with another one */
    def replace(from: SchemeExp, to: SchemeExp): Formula

/** An empty formula */
case object EmptyFormula extends Formula:
    def elements: Set[Formula] = Set(this)

    def mapOptionM[M[_]: Monad](f: SchemeExp => M[Option[SchemeExp]]): M[Option[Formula]] = Monad[M].unit(Some(this))
    def splitConj: List[Formula] = List()
    def splitDisj: List[Formula] = List()
    def size: Int = 0
    def replace(from: SchemeExp, to: SchemeExp): Formula = EmptyFormula

object Symbolic:
    type Symbolic = SchemeExp

    import maf.language.sexp.*
    import scala.util.control.TailCalls._

    export maf.language.scheme.{SchemeFuncall => Funcall, SchemeValue => Value, SchemeVar => Var}

    /** Returns a set of symbolic variables (eg. identifiers starting with x) in the given symbolic expression. */
    def variables(sym: Symbolic): List[String] = sym match
        case Funcall(fexp, fargs, _) =>
            variables(fexp) ++ fargs.flatMap(variables)
        case VarId(s) if s.startsWith("x") => List(s)
        case _                             => List()

    object VarId:
        def apply(id: String): SchemeVar = SchemeVar(Identifier(id, Identity.none))
        def unapply(other: Any): Option[String] =
            other match
                case SchemeVar(Identifier(name, _))       => Some(name)
                case SchemeVarLex(Identifier(name, _), _) => Some(name)
                case _                                    => None

    object SymbolicCompiler extends BaseSchemeCompiler:
        override def _compile(exp: SExp): TailRec[SchemeExp] = exp match
            case SExpId(Identifier("□", _)) => done(□)
            case _                          => super._compile(exp)

    object Parser:
        def parse(s: String, tag: PTag = noTag): List[SchemeExp] = SExpParser.parse(s, tag).map(SymbolicCompiler.compile)

    /** An alias for a Hole. */
    def `□` : Symbolic = Hole(SchemeVar(Identifier("fresh", Identity.none)))
    def `□`(v: Symbolic): Symbolic = Hole(v)

    /**
     * A hole is a symbolic representation that must be later filled in with an actual fresh symbolic variable.
     *
     * Holes can have a rank, that can be used to identify multiple occurances of the same hole
     */
    object Hole:
        def unapply(v: SchemeExp): Option[(Symbolic)] = v match
            case SymbolicHole(v) => Some(v)
            case _               => None

        def apply(v: SchemeExp): SchemeExp =
            SymbolicHole(v)

    /**
     * The semantics of a hole is that it is "absorbing", which means that if it is joined with a particular symbolic expression (or assertion) it can
     * absorb matching parts of that expression (i.e. replace it with a hole).
     *
     * Example: □(+ x0 1) matches (+ (+ (+ x0 1) 1) 1) such that □ absorbs everything and (+ (+ x0 1) □) is returned.
     */

    /** Checks whether the given assertion has a valid form */
    def isValid(ass: SchemeExp): Boolean = ass match
        // Any assertion of the form (x e e) is valid
        case SchemeFuncall(SchemeVar(_), fargs, _) =>
            fargs.foldLeft(true)((acc, farg) => acc && isValid(farg))
        // Any identifier is a valid assertion
        case SchemeVar(_) => true
        // Any literal value is a valid assertion
        case SchemeValue(_, _) => true
        // A hole is a valid assertion
        case Hole(_) => true
        // Anything else is not a valid assertion
        case _ => false

    /** Strips any identity information from the given symbolic expression */
    def stripIdn(sym: Symbolic): Symbolic = sym match
        case SchemeFuncall(f, args, _)            => SchemeFuncall(f, args, Identity.none)
        case SchemeVar(Identifier(name, _))       => SchemeVar(Identifier(name, Identity.none))
        case SchemeVarLex(Identifier(name, _), _) => SchemeVar(Identifier(name, Identity.none))
        case SchemeValue(value, _)                => SchemeValue(value, Identity.none)

    /** Strips any identity information from the assertions in the formula */
    def stripIdn(formula: Formula): Formula =
        import FormulaAux.*
        formula match
            case Conjunction(cs) => conj(cs.map(stripIdn).toList: _*)
            case Disjunction(ds) => disj(ds.map(stripIdn).toList: _*)
            case Assertion(ass)  => Assertion(stripIdn(ass))
            case EmptyFormula    => EmptyFormula

/** An assertion formed by constructing a scheme expression that can be interpreted as a boolean assertion */
case class Assertion(contents: SchemeExp) extends Formula:
    val elements: Set[Formula] = Set(this)
    override def toString = s"$contents"

    def mapOptionM[M[_]: Monad](f: SchemeExp => M[Option[SchemeExp]]): M[Option[Formula]] =
        f(contents).map(_.map(Assertion(_)))

    /** Split the formula into its constituents if it is a conjunction */
    def splitConj: List[Formula] = List(this)

    /** Split the formula into its constituents if it is a disjunction */
    def splitDisj: List[Formula] = List(this)

    def size: Int = 1

    def replace(from: SchemeExp, to: SchemeExp) =
        def replaceContents(contents: SchemeExp): SchemeExp = contents match
            case e if e == from              => to
            case SchemeFuncall(f, args, idn) => SchemeFuncall(replaceContents(f), args.map(replaceContents), idn)
            case e                           => e

        if from == to then this else Assertion(replaceContents(contents))

/**
 * A conjunction of two (or more) formulas
 *
 * Use the auxiliary <code>conj</code> function to create an instance of this class.
 *
 * @see
 *   maf.language.symbolic.FormulaAux.conj
 */
case class Conjunction(val elements: Set[Formula]) extends Formula:
    override def toString: String = s"(${elements.mkString(" /\\ ")})"

    def mapOptionM[M[_]: Monad](f: SchemeExp => M[Option[SchemeExp]]): M[Option[Formula]] =
        elements.mapM(_.mapOptionM(f)).map(_.flatten).map(elms => if elms.size == 0 then None else Some(Conjunction(elms.toSet)))

    /** Split the formula into its constituents if it is a conjunction */
    def splitConj: List[Formula] = elements.toList

    /** Split the formula into its constituents if it is a disjunction */
    def splitDisj: List[Formula] = List(this)

    def size: Int = elements.map(_.size).sum

    def replace(from: SchemeExp, to: SchemeExp): Formula = Conjunction(elements.map(_.replace(from, to)))

/**
 * A disjunction of two (or more) formulas
 *
 * Use the auxiliary <code>disj</code> function to create an instance of this class
 *
 * @see
 *   maf.language.symbolic.FormulaAux.disj
 */
case class Disjunction(val elements: Set[Formula]) extends Formula:
    override def toString: String = if elements.size >= 1 then s"(${elements.mkString(" \\/ ")})"
    else "(empty-or)"

    def mapOptionM[M[_]: Monad](f: SchemeExp => M[Option[SchemeExp]]): M[Option[Formula]] =
        elements.mapM(_.mapOptionM(f)).map(_.flatten).map(elms => if elms.size == 0 then None else Some(Disjunction(elms.toSet)))

    /** Split the formula into its constituents if it is a conjunction */
    def splitConj: List[Formula] = List(this)

    /** Split the formula into its constituents if it is a disjunction */
    def splitDisj: List[Formula] = elements.toList

    def size: Int = elements.map(_.size).sum

    def replace(from: SchemeExp, to: SchemeExp): Formula = Disjunction(elements.map(_.replace(from, to)))

/** Auxiliary functions */
object FormulaAux:

    /**
     * Helper function to construct a conjunction from a variable number of arguments
     *
     * @param as
     *   the formula(s) that will be combined into a conjunction
     */
    def conj(as: Formula*): Formula =
        conj(as.toList)

    /**
     * More generic form of <code>conj(Formula*)</code> but only accepts a list of formulas instead of a variable number of formulas
     *
     * @param as
     *   the list of formulas to combine into a conjunction
     * @param flatten
     *   true if the conjunction needs to be flattened (default)
     */
    def conj(as: List[Formula], flatten: Boolean = true): Formula =
        val asCleared = as.filterNot { _ == EmptyFormula }
        if asCleared.size == 0 then EmptyFormula
        else if asCleared.size == 1 then asCleared.head
        else if flatten then flatConj(asCleared.toSet)
        else Conjunction(asCleared.toSet)

    /** Same as <code>conj</code> but constructs a disjunction instead */
    def disj(as: Formula*): Formula =
        disj(as.toList)

    /** Same as <code>conj</code> but constructs a disjunction instead */
    def disj(as: List[Formula], doFlat: Boolean = true): Formula =
        val asCleared = as.filterNot { _ == EmptyFormula }
        if asCleared.size == 0 then EmptyFormula
        else if asCleared.size == 1 then asCleared.head
        else if doFlat then flatten(asCleared.toSet)
        else Disjunction(asCleared.toSet)

    /** Constructs an (isTrue? expr) expression */
    def isTrue(expr: SchemeExp): SchemeExp =
        SchemeFuncall(SchemeVar(Identifier("true?", Identity.none)), List(expr), Identity.none)

    /** Constructs an application (id vls ...) */
    def ap(id: SchemeExp, vls: SchemeExp*): SchemeExp =
        SchemeFuncall(id, vls.toList, Identity.none)

    /** Constructs an identifier (as a SchemeVar) from the given name */
    def id(name: String): SchemeExp =
        SchemeVar(Identifier(name, Identity.none))

    /** Constructs a number literal */
    def num(n: Int): SchemeExp =
        SchemeValue(maf.language.sexp.Value.Integer(n), Identity.none)

    def ass(assertion: SchemeExp): Formula =
        Assertion(assertion)

    /**
     * Flattens a list of conjunctions into a single conjunctions
     *
     * @param conjunctions
     *   the list of formulas that should occur in a conjunction
     */
    def flatConj(conjunctions: Set[Formula]): Formula = conj(
      (conjunctions flatMap {
          case Conjunction(vs) =>
              flatConj(vs) match
                  case Conjunction(vss) => vss
                  case v                => List(v)
          case v => List(v)
      }).toSet.toList,
      false
    )

    /** Flatten a list of disjunctions into a single disjunctions */
    def flatten(disjunctions: Set[Formula]): Formula = disj(
      (disjunctions flatMap {
          case Disjunction(djs) =>
              flatten(djs) match
                  case Disjunction(rss) => rss
                  case l                => List(l)

          case a @ Assertion(_) => List(disj(a))
          case v =>
              List(
                v
              ) // throw new Exception(s"only a list of disjunctions can be flattened, but got $v")
      }).toSet.toList,
      false
    )

    // From: https://rosettacode.org/wiki/Cartesian_product_of_two_or_more_lists
    private def cartesianProduct[T](lst: List[T]*): List[List[T]] = {

        /**
         * Prepend single element to all lists of list
         * @param e
         *   single elemetn
         * @param ll
         *   list of list
         * @param a
         *   accumulator for tail recursive implementation
         * @return
         *   list of lists with prepended element e
         */
        def pel(e: T, ll: List[List[T]], a: List[List[T]] = Nil): List[List[T]] =
            ll match {
                case Nil     => a.reverse
                case x :: xs => pel(e, xs, (e :: x) :: a)
            }

        lst.toList match {
            case Nil      => Nil
            case x :: Nil => List(x)
            case x :: _ =>
                x match {
                    case Nil => Nil
                    case _ =>
                        lst
                            .foldRight(List(x))((l, a) => l.flatMap(pel(_, a)))
                            .map(_.dropRight(x.size))
                }
        }
    }

    /** Distribute the a conjunction of disjunctions */
    def distribute(disjunctions: List[Formula]): Formula =
        val res = disjunctions.map(_.elements)
        disj(cartesianProduct(disjunctions.map(_.elements.toList): _*).map(conj(_)))
