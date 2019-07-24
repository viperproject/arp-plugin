// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.rewriter._
import viper.silver.plugin.ARPPlugin.ARPContext

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

  def getARPLogType(program: Program): DomainType = {
    DomainType(getDomain(program, plugin.naming.logDomainName).get, Map[TypeVar, Type]())
  }

  def getARPLogFunction(program: Program, name: String): DomainFunc = {
    getDomainFunction(getDomain(program, plugin.naming.logDomainName).get, name).get
  }

  def constrainRdExp(methodRdName: String)(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): Exp =
    And(
      PermLtCmp(
        NoPerm()(pos, info, errT),
        LocalVar(methodRdName, Perm)(pos, info, errT)
      )(pos, info, errT),
      PermLtCmp(
        LocalVar(methodRdName, Perm)(pos, info, errT),
        FullPerm()(pos, info, errT)
      )(pos, info, errT)
    )(pos, info, errT)

  def rewriteLabelledOldExpr[T <: Node](node: T): T = {
    StrategyBuilder.Slim[Node]({
      case l@LabelledOld(exp, _) => Old(exp)(l.pos, l.info, NodeTrafo(l))
    }).execute[T](node)
  }

  def rewriteOldExpr[T <: Node](program: Program, labelName: String, oldLabel: Boolean = true, fieldAccess: Boolean = true, includeNonpure: Boolean = false)(node: T): T = {
    def rewriteFieldAccess(fa: FieldAccess): FieldAccess = {
      fa.rcv match {
        case _: LabelledOld => fa
        case _: Old => fa
        case _: LocalVar => fa
        case rcv =>
          FieldAccess(
            LabelledOld(rcv, labelName)(rcv.pos, rcv.info, NodeTrafo(rcv)),
            fa.field
          )(fa.pos, fa.info, NodeTrafo(fa))
      }
    }

    def rewritePredicateAccess(pa: PredicateAccess): PredicateAccess = {
      PredicateAccess(pa.args.map(rewriteOldExpr(program, labelName, oldLabel, fieldAccess)), pa.predicateName)(pa.pos, pa.info, NodeTrafo(pa))
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

    def removeOld(trigger: Trigger): Trigger = {
      StrategyBuilder.Slim[Node]({
        case Old(e) => e
      }).execute[Trigger](trigger)
    }

    val nodePrime = if (oldLabel) {
      StrategyBuilder.Ancestor[Node]({
        case (f: Forall, ctx) =>
          Forall(
            f.variables, f.triggers.map(removeOld).map(ctx.noRec[Trigger]), f.exp
          )(f.pos, f.info, NodeTrafo(f))
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
            //n.isInstanceOf[LocationAccess] ||
            n.isInstanceOf[CurrentPerm] ||
            n.isInstanceOf[ForPerm] ||
            n.isInstanceOf[MagicWand]
        )
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
        case (m: MagicWand, ctx) => ctx.noRec(m)
        case (u: Unfolding, ctx) =>
          ctx.noRec(LabelledOld(u, labelName)(u.pos, u.info, u.errT + NodeTrafo(u)))
        case (f: Forall, ctx) =>
          f.triggers.foreach(ctx.noRec[Trigger])
          f
        case (a: AbstractAssign, ctx) =>
          ctx.noRec(a.lhs)
          a
        case (f@DomainFuncApp(name, args, typVarMap), ctx) if f.domainName == plugin.naming.logDomainName && f.funcname == plugin.naming.logDomainCons =>
          ctx.noRec(DomainFuncApp(name, args.map({
            case fa: FieldAccess => LabelledOld(fa, labelName)(fa.pos, fa.info, NodeTrafo(fa))
            case default => default
          }), typVarMap)(f.pos, f.info, f.typ, f.domainName, f.errT))
        case (l: LocalVar, ctx) => ctx.noRec(l)
        case (n: Exp, ctx) if isPure(n) && n.isHeapDependent(program) => ctx.noRec(LabelledOld(n, labelName)(n.pos, n.info, NodeTrafo(n)))
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
      case f@FuncApp(plugin.naming.rdName, Seq()) => LocalVar(contextRdName, Perm)(f.pos, f.info, NodeTrafo(f))
      case f@FuncApp(plugin.naming.rdCountingName, Seq(arg: Exp)) =>
        arg match {
          case IntLit(x) if x == 1 =>
            FuncApp(plugin.naming.rdEpsilonName, Seq())(f.pos, f.info, f.typ, NoTrafos)
          case default =>
            IntPermMul(
              default,
              FuncApp(plugin.naming.rdEpsilonName, Seq())(f.pos, f.info, f.typ, NoTrafos)
            )(f.pos, f.info, NodeTrafo(f))
        }
      case f@FuncApp(plugin.naming.rdWildcardName, Seq()) =>
        val wildcardRdName = if (remainingWildcardRdNames.nonEmpty) {
          val head = remainingWildcardRdNames.head
          remainingWildcardRdNames = remainingWildcardRdNames.tail
          head
        } else {
          plugin.naming.getNewName(suffix = "not_enough_names")
        }
        LocalVar(wildcardRdName, Perm)(f.pos, f.info, NodeTrafo(f))
      case f@FuncApp(plugin.naming.rdTokenFresh, args) =>
        FuncApp(plugin.naming.rdToken, args)(f.pos, f.info, f.typ, NodeTrafo(f))
    }).execute[T](node)
  }

  def rewriteRdPredicate[T <: Node](node: T): T = {
    StrategyBuilder.Slim[Node]({
      case f@FuncApp(plugin.naming.rdName, Seq()) => FuncApp(plugin.naming.rdGlobalName, Seq())(f.pos, f.info, Perm, NodeTrafo(f))
      case f@FuncApp(plugin.naming.rdCountingName, Seq(arg: Exp)) =>
        arg match {
          case IntLit(x) if x == 1 =>
            FuncApp(plugin.naming.rdEpsilonName, Seq())(f.pos, f.info, f.typ, NoTrafos)
          case default =>
            IntPermMul(
              default,
              FuncApp(plugin.naming.rdEpsilonName, Seq())(f.pos, f.info, f.typ, NoTrafos)
            )(f.pos, f.info, NodeTrafo(f))
        }
    }).execute[T](node)
  }

  def rewriteRdSimple[T <: Node](rdName: String)(node: T): T = {
    StrategyBuilder.Slim[Node]({
      case f@FuncApp(plugin.naming.rdName, Seq()) => LocalVar(rdName, Perm)(f.pos, f.info, NodeTrafo(f))
    }).execute[T](node)
  }

  def rewriteRdForDummyMethodSlow[T <: Node](node: T): T = {
    plugin.performance.start()
    val strat = TreeRegexBuilder.simple[Node] &> n.r[AccessPredicate] >> n.P[FuncApp](f =>
      f.funcname == plugin.naming.rdName || f.funcname == plugin.naming.rdCountingName || f.funcname == plugin.naming.rdWildcardName
    ) |-> {
      case f@FieldAccessPredicate(loc, perm) => FieldAccessPredicate(loc, FractionalPerm(IntLit(1)(), IntLit(2)())())(f.pos, f.info, NodeTrafo(f))
      case p@PredicateAccessPredicate(loc, perm) => PredicateAccessPredicate(loc, FractionalPerm(IntLit(1)(), IntLit(2)())())(p.pos, p.info, NodeTrafo(p))
    }
    val result = strat.execute[T](node)
    plugin.performance.stop("rewriteRdForDummyMethodSlow")
    result
  }

  def rewriteRdForDummyMethod[T <: Node](rdName: String)(node: T): T = {
    val strat = StrategyBuilder.Slim[Node]({
      case ap: AccessPredicate if ap.perm.exists({
        case f: FuncApp => f.funcname == plugin.naming.rdName || f.funcname == plugin.naming.rdCountingName || f.funcname == plugin.naming.rdWildcardName
        case _ => false
      }) =>
        val perm = ap.perm match {
          case f@FuncApp(plugin.naming.rdName, Seq()) => LocalVar(rdName, Perm)(f.pos, f.info, NodeTrafo(f))
          case _ => FractionalPerm(IntLit(1)(ap.pos, ap.info), IntLit(2)(ap.pos, ap.info))(ap.pos, ap.info)
        }
        ap match {
          case f@FieldAccessPredicate(loc, _) => FieldAccessPredicate(loc, perm)(f.pos, f.info, NodeTrafo(f))
          case p@PredicateAccessPredicate(loc, _) => PredicateAccessPredicate(loc, perm)(p.pos, p.info, NodeTrafo(p))
        }
    })
    strat.execute[T](node)
  }

  def havoc(lvar: LocalVar, ctx: ContextC[Node, ARPContext]): Stmt = {
    if (plugin.naming.havocNames.contains(lvar.typ)) {
      ctx.noRec(MethodCall(plugin.naming.havocNames(lvar.typ), Seq(), Seq(lvar))(lvar.pos, lvar.info, lvar.errT))
    } else {
      val tmpName = plugin.naming.getNewName(suffix = "havoc")
      Seqn(
        Seq(
          LocalVarAssign(lvar, LocalVar(tmpName, lvar.typ)(lvar.pos, lvar.info))(lvar.pos, lvar.info)
        ),
        Seq(LocalVarDecl(tmpName, lvar.typ)(lvar.pos, lvar.info))
      )(lvar.pos, lvar.info)
    }
  }

  def getAccessDomainFuncApp(input: Program, l: ResourceAccess)(pos: Position, info: Info, errT: ErrorTrafo = NoTrafos): DomainFuncApp = {
    val arpFieldFunctionDomain = plugin.utils.getDomain(input, plugin.naming.fieldFunctionDomainName).get

    def getFieldFun(f: Field) = {
      val maybeFunc = getDomainFunction(arpFieldFunctionDomain, plugin.naming.getFieldFunctionName(f))
      if (maybeFunc.isDefined) {
        maybeFunc.get
      } else {
        throw new NoSuchElementException("FieldFunction for " + f.toString() + " / " + plugin.naming.getFieldFunctionName(f)
          + " / " + input.fields.mkString(" ; ")
          + " / " + arpFieldFunctionDomain.functions.mkString(" ; "))
      }
    }

    def getPredicateFun(p: String) = {
      val maybeFunc = getDomainFunction(arpFieldFunctionDomain, plugin.naming.getPredicateFunctionName(getPredicate(input, p).get))
      if (maybeFunc.isDefined) {
        maybeFunc.get
      } else {
        throw new NoSuchElementException("FieldFunction for predicate " + p + " / " + plugin.naming.getPredicateFunctionName(getPredicate(input, p).get)
          + " / " + input.predicates.mkString(" ; ")
          + " / " + arpFieldFunctionDomain.functions.mkString(" ; "))
      }
    }

    l match {
      case FieldAccess(_, f) => DomainFuncApp(getFieldFun(f), Seq(), Map[TypeVar, Type]())(pos, info, errT)
      case PredicateAccess(args, p) => DomainFuncApp(getPredicateFun(p), args, Map[TypeVar, Type]())(pos, info, errT)
    }
  }

  def getAccessRcv(l: ResourceAccess)(pos: Position, info: Info, errT: ErrorTrafo = NoTrafos): Exp = {
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
        case root@Mul(IntLit(left), o) if left == 1 => o
        case root@Mul(IntLit(left), o) if left == -1 => Minus(o)(root.pos, root.info, NodeTrafo(root))
        case root@Mul(o, IntLit(right)) if right == 1 => o
        case root@Mul(o, IntLit(right)) if right == -1 => Minus(o)(root.pos, root.info, NodeTrafo(root))

        case PermMul(_: FullPerm, e: PermExp) => e
        case PermMul(e: PermExp, _: FullPerm) => e
        case PermMul(e: NoPerm, _: Exp) => e
        case PermMul(_: Exp, e: NoPerm) => e
        case IntPermMul(IntLit(x), p) if x == 1 => p
        case root@IntPermMul(IntLit(x), p) if x == -1 => PermMinus(p)(root.pos, root.info, NodeTrafo(root))
      }, Traverse.BottomUp).execute[Exp](exp)
    } else {
      exp
    }
  }

  def containsRd(exp: Exp): Boolean = {
    exp.exists(n => n.isInstanceOf[FuncApp] && (
      n.asInstanceOf[FuncApp].funcname == plugin.naming.rdGlobalName
      || n.asInstanceOf[FuncApp].funcname == plugin.naming.rdName
      || n.asInstanceOf[FuncApp].funcname == plugin.naming.rdEpsilonName
      || n.asInstanceOf[FuncApp].funcname == plugin.naming.rdWildcardName
      ))
  }

  def getZeroEquivalent(exp: Exp): Exp = {
    val intLit = IntLit(bigIntZero)(exp.pos, exp.info)
    val permLit = NoPerm()(exp.pos, exp.info)
    exp match {
      case default if plugin.utils.isPermExp(default) => permLit
      case _ => intLit
    }
  }

  def isPermExp(exp: Exp): Boolean = {
    exp match {
      case _: PermExp => true
      case v: LocalVar if v.typ == Perm => true
      case x: CondExp => isPermExp(x.thn)
      case _ => false
    }
  }

  private val bigIntZero = BigInt(0)
}
