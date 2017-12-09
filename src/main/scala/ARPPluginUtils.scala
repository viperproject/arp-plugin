/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.{StrategyBuilder, Traverse, TreeRegexBuilder, n}
import viper.silver.verifier.reasons.ErrorNode

class ARPPluginUtils(plugin: ARPPlugin) {

  def getMethod(program: Program, method: String): Option[Method] = {
    program.methods.find(m => m.name == method)
  }

  def getPredicate(program: Program, predicate: String): Option[Predicate] = {
    program.predicates.find(p => p.name == predicate)
  }

  def getFunction(program: Program, function: String): Option[Function] = {
    program.functions.find(f => f.name == function)
  }

  def getDomain(program: Program, domain: String): Option[Domain] = {
    program.domains.find(d => d.name == domain)
  }

  def getDomainFunction(domain: Domain, function: String): Option[DomainFunc] = {
    domain.functions.find(f => f.name == function)
  }

  def constrainRdExp(methodRdName: String)(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): Exp =
    And(
      PermLtCmp(
        NoPerm()(pos, info, errT),
        LocalVar(methodRdName)(Perm, pos, info, errT)
      )(pos, info, errT),
      PermLtCmp(
        LocalVar(methodRdName)(Perm, pos, info, errT),
        FullPerm()(pos, info, errT)
      )(pos, info, errT)
    )(pos, info, errT)

  def rewriteOldExpr[T <: Node](labelName: String, oldLabel: Boolean = true, fieldAccess: Boolean = true, includeNonpure: Boolean = false)(node: T): T = {
    def rewriteFieldAccess(fa: FieldAccess): FieldAccess = {
      fa.rcv match {
        case _: LabelledOld => fa
        case _: LocalVar => fa
        case rcv =>
          FieldAccess(
            LabelledOld(rcv, labelName)(rcv.pos, rcv.info, NodeTrafo(rcv)),
            fa.field
          )(fa.pos, fa.info, NodeTrafo(fa))
      }
    }

    def rewritePredicateAccess(pa: PredicateAccess): PredicateAccess = {
      PredicateAccess(pa.args.map(rewriteOldExpr(labelName, oldLabel, fieldAccess)), pa.predicateName)(pa.pos, pa.info, NodeTrafo(pa))
    }

    def rewritePerm(perm: Exp): Exp = {
      StrategyBuilder.Ancestor[Node]({
        case (l: LabelledOld, ctx) => ctx.noRec(l)
        case (c: CurrentPerm, ctx) => ctx.noRec(c)
        case (fa: FieldAccess, ctx) => ctx.noRec(LabelledOld(fa, labelName)(fa.pos, fa.info, NodeTrafo(fa)))
        case (u: Unfolding, ctx) =>
          ctx.noRec(LabelledOld(u, labelName)(u.pos, u.info, u.errT + NodeTrafo(u)))
      }).execute[Exp](perm)
    }

    val nodePrime = if (oldLabel) {
      StrategyBuilder.Ancestor[Node]({
        case (l: LabelledOld, ctx) => ctx.noRec(l)
        case (o@Old(exp), ctx) => LabelledOld(exp, labelName)(o.pos, o.info, NodeTrafo(o))
      }).execute[T](node)
    } else {
      node
    }

    def isPure(pureNode: Node): Boolean = {
      includeNonpure ||
        !pureNode.exists(n =>
          n.isInstanceOf[AccessPredicate] ||
            n.isInstanceOf[CurrentPerm] ||
            n.isInstanceOf[ForPerm])
    }

    val nodePrimePrime = if (fieldAccess) {
      StrategyBuilder.Ancestor[Node]({
        case (l: LabelledOld, ctx) => ctx.noRec(l)
        case (f@FieldAccessPredicate(fa: FieldAccess, perm), ctx) =>
          ctx.noRec(FieldAccessPredicate(rewriteFieldAccess(fa), rewritePerm(perm))(f.pos, f.info, NodeTrafo(f)))
        case (p@PredicateAccessPredicate(loc, perm), ctx) =>
          ctx.noRec(PredicateAccessPredicate(rewritePredicateAccess(loc), rewritePerm(perm))(p.pos, p.info, NodeTrafo(p)))
        case (c@CurrentPerm(fa: FieldAccess), ctx) =>
          ctx.noRec(CurrentPerm(rewriteFieldAccess(fa))(c.pos, c.info, NodeTrafo(c)))
        case (c: CurrentPerm, ctx) => ctx.noRec(c)
        case (f: ForPerm, ctx) => ctx.noRec(f)
        case (u: Unfolding, ctx) =>
          ctx.noRec(LabelledOld(u, labelName)(u.pos, u.info, u.errT + NodeTrafo(u)))
        case (a: AbstractAssign, ctx) =>
          ctx.noRec(a.lhs)
          a
        case (f@DomainFuncApp(name, args, typVarMap), ctx) if f.domainName == plugin.naming.logDomainName && f.funcname == plugin.naming.logDomainCons =>
          ctx.noRec(DomainFuncApp(name, args.map({
            case fa: FieldAccess => LabelledOld(fa, labelName)(fa.pos, fa.info, NodeTrafo(fa))
            case default => default
          }), typVarMap)(f.pos, f.info, f.typ, f.formalArgs, f.domainName, f.errT))
        case (l: LocalVar, ctx) => ctx.noRec(l)
        case (n: Exp, ctx) if isPure(n) => ctx.noRec(LabelledOld(n, labelName)(n.pos, n.info, NodeTrafo(n)))
        case (f: FieldAccess, ctx) =>
          ctx.noRec(LabelledOld(f, labelName)(f.pos, f.info, f.errT + NodeTrafo(f)))
        case (f: FuncApp, ctx) =>
          ctx.noRec(LabelledOld(f, labelName)(f.pos, f.info, f.errT + NodeTrafo(f)))
        case (f: DomainFuncApp, ctx) =>
          ctx.noRec(LabelledOld(f, labelName)(f.pos, f.info, f.errT + NodeTrafo(f)))
      }).execute[T](nodePrime)
    } else {
      nodePrime
    }

    nodePrimePrime
  }

  def rewriteRd[T <: Node](contextRdName: String, wildcardRdNames: Seq[String] = Seq())(node: T): T = {
    var remainingWildcardRdNames = wildcardRdNames
    StrategyBuilder.Slim[Node]({
      case f@FuncApp(plugin.naming.rdName, Seq()) => LocalVar(contextRdName)(Perm, f.pos, f.info, NodeTrafo(f))
      case f@FuncApp(plugin.naming.rdCountingName, Seq(arg: Exp)) =>
        PermMul(
          arg,
          FuncApp(plugin.naming.rdEpsilonName, Seq())(f.pos, f.info, f.typ, f.formalArgs, NoTrafos)
        )(f.pos, f.info, NodeTrafo(f))
      case f@FuncApp(plugin.naming.rdWildcardName, Seq()) =>
        val wildcardRdName = if (remainingWildcardRdNames.nonEmpty) {
          val head = remainingWildcardRdNames.head
          remainingWildcardRdNames = remainingWildcardRdNames.tail
          head
        } else {
          plugin.naming.getNewName(suffix = "not_enough_names")
        }
        LocalVar(wildcardRdName)(Perm, f.pos, f.info, NodeTrafo(f))
    }).execute[T](node)
  }

  def rewriteRdForDummyMethod[T <: Node](node: T): T = {
    val strat = TreeRegexBuilder.simple[Node] &> n.r[AccessPredicate] >> n.P[FuncApp](f =>
      f.funcname == plugin.naming.rdName || f.funcname == plugin.naming.rdCountingName || f.funcname == plugin.naming.rdWildcardName
    ) |-> {
      case f@FieldAccessPredicate(loc, perm) => FieldAccessPredicate(loc, PermDiv(IntLit(1)(), IntLit(2)())())(f.pos, f.info, NodeTrafo(f))
      case p@PredicateAccessPredicate(loc, perm) => PredicateAccessPredicate(loc, PermDiv(IntLit(1)(), IntLit(2)())())(p.pos, p.info, NodeTrafo(p))
    }
    strat.execute[T](node)
  }

  def havoc(lvar: LocalVar): Stmt = {
    // this does not work (see method_havoc.sil)
    //    if (plugin.naming.havocNames.contains(lvar.typ)) {
    //      LocalVarAssign(lvar, FuncApp(plugin.naming.havocNames(lvar.typ), Seq())(lvar.pos, lvar.info, lvar.typ, Seq(), NoTrafos))(lvar.pos, lvar.info)
    //    } else {
    val tmpName = plugin.naming.getNewName(suffix = "havoc")
    Seqn(
      Seq(
        // TODO: Why is this declStmt needed?
        LocalVarDeclStmt(LocalVarDecl(tmpName, lvar.typ)(lvar.pos, lvar.info))(lvar.pos, lvar.info),
        LocalVarAssign(lvar, LocalVar(tmpName)(lvar.typ, lvar.pos, lvar.info))(lvar.pos, lvar.info)
      ),
      Seq(LocalVarDecl(tmpName, lvar.typ)(lvar.pos, lvar.info))
    )(lvar.pos, lvar.info)
    //    }
  }

  def getAccessDomainFuncApp(input: Program, l: LocationAccess)(pos: Position, info: Info, errT: ErrorTrafo = NoTrafos): DomainFuncApp ={
    val arpFieldFunctionDomain = plugin.utils.getDomain(input, plugin.naming.fieldFunctionDomainName).get
    def getFieldFun(f: Field) = getDomainFunction(arpFieldFunctionDomain, plugin.naming.getFieldFunctionName(f)).get
    def getPredicateFun(p: String) = getDomainFunction(arpFieldFunctionDomain, plugin.naming.getPredicateFunctionName(getPredicate(input, p).get)).get
    l match {
      case FieldAccess(_, f) => DomainFuncApp(getFieldFun(f), Seq(), Map[TypeVar, Type]())(pos, info, errT)
      case PredicateAccess(args, p) => DomainFuncApp(getPredicateFun(p), args, Map[TypeVar, Type]())(pos, info, errT)
    }
  }

  def getAccessRcv(l: LocationAccess)(pos: Position, info: Info, errT: ErrorTrafo = NoTrafos): Exp ={
    l match {
      case f: FieldAccess => f.rcv
      case p: PredicateAccess => NullLit()(pos, info, errT)
    }
  }

  // Simplify int expressions
  def simplify(exp: Exp): Exp = {
    if (plugin.Optimize.simplifyExpressions) {
      /* Always simplify children first, then treat parent. */
      StrategyBuilder.Slim[Node]({
        case root@Minus(IntLit(literal)) => IntLit(-literal)(root.pos, root.info, NodeTrafo(root))
        case Minus(Minus(single)) => single
        case root@PermMinus(IntLit(literal)) => IntLit(-literal)(root.pos, root.info, NodeTrafo(root))
        case PermMinus(PermMinus(single)) => single

        case root@Add(IntLit(left), IntLit(right)) =>
          IntLit(left + right)(root.pos, root.info, NodeTrafo(root))
        case root@Sub(IntLit(left), IntLit(right)) =>
          IntLit(left - right)(root.pos, root.info, NodeTrafo(root))
        case root@Mul(IntLit(left), IntLit(right)) =>
          IntLit(left * right)(root.pos, root.info, NodeTrafo(root))
        case root@Div(IntLit(left), IntLit(right)) if right != bigIntZero =>
          IntLit(left / right)(root.pos, root.info, NodeTrafo(root))
        case root@Mod(IntLit(left), IntLit(right)) if right != bigIntZero =>
          IntLit(left % right)(root.pos, root.info, NodeTrafo(root))
        case root@PermAdd(IntLit(left), IntLit(right)) =>
          IntLit(left + right)(root.pos, root.info, NodeTrafo(root))
        case root@PermSub(IntLit(left), IntLit(right)) =>
          IntLit(left - right)(root.pos, root.info, NodeTrafo(root))
        case root@PermMul(IntLit(left), IntLit(right)) =>
          IntLit(left * right)(root.pos, root.info, NodeTrafo(root))
        case PermMul(_: FullPerm, e: Exp) => e
        case PermMul(e: Exp, _: FullPerm) => e
        case PermMul(e: NoPerm, _: Exp) => e
        case PermMul(_: Exp, e: NoPerm) => e
      }, Traverse.BottomUp).execute[Exp](exp)
    } else {
      exp
    }
  }

  def getZeroEquivalent(exp: Exp): Exp = {
    val intLit = IntLit(bigIntZero)(exp.pos, exp.info)
    val permLit = NoPerm()(exp.pos, exp.info)
    exp match {
      case _: PermAdd => permLit
      case _: PermSub => permLit
      case _: PermMul => permLit
      case _: PermDiv => permLit
      case _: AbstractConcretePerm => permLit
      case v: LocalVar if v.typ == Perm => permLit
      case _: CurrentPerm => permLit
      case _ =>
        intLit
    }
  }

  private val bigIntZero = BigInt(0)
}
