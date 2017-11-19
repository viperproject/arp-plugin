/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.{StrategyBuilder, Traverse}

class ARPPluginUtils(plugin: ARPPlugin) {

  def getMethod(program: Program, method: String): Option[Method] = {
    program.methods.find(m => m.name == method)
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

  def rewriteOldExpr[T <: Node](labelName: String, oldLabel: Boolean = true, fieldAccess: Boolean = true)(node: T): T = {
    StrategyBuilder.Ancestor[Node]({
      case (l: LabelledOld, ctx) => ctx.noRec(l)
      case (o@Old(exp), ctx) if oldLabel => LabelledOld(exp, labelName)(o.pos, o.info, o.errT + NodeTrafo(o))
      case (f@FieldAccessPredicate(fa@FieldAccess(rcv, field), perm), ctx) if fieldAccess =>
        rcv match {
          case _: LabelledOld => ctx.noRec(f)
          case _ =>
            ctx.noRec(
              FieldAccessPredicate(
                FieldAccess(
                  LabelledOld(rcv, labelName)(rcv.pos, rcv.info, rcv.errT + NodeTrafo(rcv)),
                  field
                )(fa.pos, fa.info, fa.errT + NodeTrafo(fa)),
                perm
              )(f.pos, f.info, f.errT + NodeTrafo(f))
            )
        }
      case (c@CurrentPerm(fa@FieldAccess(rcv, field)), ctx) if fieldAccess =>
        rcv match {
          case _: LabelledOld => ctx.noRec(c)
          case _ =>
            ctx.noRec(
              CurrentPerm(
                FieldAccess(
                  LabelledOld(rcv, labelName)(rcv.pos, rcv.info, rcv.errT + NodeTrafo(rcv)),
                  field
                )(fa.pos, fa.info, fa.errT + NodeTrafo(fa))
              )(c.pos, c.info, c.errT + NodeTrafo(c))
            )
        }
      case (f@ForPerm(variable, access, body), ctx) if fieldAccess =>
        ctx.noRec(
          ForPerm(variable, access, rewriteOldExpr(labelName, oldLabel, fieldAccess)(body))(f.pos, f.info, f.errT + NodeTrafo(f))
        )
      case (f@FieldAccess(rcv, field), ctx) if fieldAccess =>
        rcv match {
          case _ =>
            ctx.noRec(
              LabelledOld(
                FieldAccess(
                  rcv,
                  field
                )(f.pos, f.info, f.errT + NodeTrafo(f)),
                labelName
              )(f.pos, f.info, f.errT + NodeTrafo(f))
            )
        }
    }).execute[T](node)
  }

  def rewriteRd[T <: Node](contextRdName: String, wildcardRdNames: Seq[String] = Seq())(node: T): T = {
    var remainingWildcardRdNames = wildcardRdNames
    StrategyBuilder.Slim[Node]({
      case f@FuncApp(plugin.naming.rdName, Seq()) => LocalVar(contextRdName)(Perm, f.pos, f.info, f.errT + NodeTrafo(f))
      case f@FuncApp(plugin.naming.rdCountingName, Seq(arg: Exp)) =>
        PermMul(
          arg,
          FuncApp(plugin.naming.rdEpsilonName, Seq())(f.pos, f.info, f.typ, f.formalArgs, f.errT)
        )(f.pos, f.info, f.errT + NodeTrafo(f))
      case f@FuncApp(plugin.naming.rdWildcardName, Seq()) =>
        val wildcardRdName = if (remainingWildcardRdNames.nonEmpty) {
          val head = remainingWildcardRdNames.head
          remainingWildcardRdNames = remainingWildcardRdNames.tail
          head
        } else {
          plugin.naming.getNewName(suffix = "not_enough_names")
        }
        LocalVar(wildcardRdName)(Perm, f.pos, f.info, f.errT + NodeTrafo(f))
    }).execute[T](node)
  }

  // Simplify int expressions
  def simplify(exp: Exp): Exp ={
    if (plugin.Optimize.simplifyExpressions) {
      /* Always simplify children first, then treat parent. */
      StrategyBuilder.Slim[Node]({
        case root@Minus(IntLit(literal)) => IntLit(-literal)(root.pos, root.info, root.errT + NodeTrafo(root))
        case Minus(Minus(single)) => single
        case root@PermMinus(IntLit(literal)) => IntLit(-literal)(root.pos, root.info, root.errT + NodeTrafo(root))
        case PermMinus(PermMinus(single)) => single

        case root@Add(IntLit(left), IntLit(right)) =>
          IntLit(left + right)(root.pos, root.info, root.errT + NodeTrafo(root))
        case root@Sub(IntLit(left), IntLit(right)) =>
          IntLit(left - right)(root.pos, root.info, root.errT + NodeTrafo(root))
        case root@Mul(IntLit(left), IntLit(right)) =>
          IntLit(left * right)(root.pos, root.info, root.errT + NodeTrafo(root))
        case root@Div(IntLit(left), IntLit(right)) if right != bigIntZero =>
          IntLit(left / right)(root.pos, root.info, root.errT + NodeTrafo(root))
        case root@Mod(IntLit(left), IntLit(right)) if right != bigIntZero =>
          IntLit(left % right)(root.pos, root.info, root.errT + NodeTrafo(root))
        case root@PermAdd(IntLit(left), IntLit(right)) =>
          IntLit(left + right)(root.pos, root.info, root.errT + NodeTrafo(root))
        case root@PermSub(IntLit(left), IntLit(right)) =>
          IntLit(left - right)(root.pos, root.info, root.errT + NodeTrafo(root))
        case root@PermMul(IntLit(left), IntLit(right)) =>
          IntLit(left * right)(root.pos, root.info, root.errT + NodeTrafo(root))
      }, Traverse.BottomUp).execute[Exp](exp)
    } else {
      exp
    }
  }

  def getZeroEquivalent(exp: Exp): Exp ={
    val intLit = IntLit(bigIntZero)(exp.pos, exp.info)
    val permLit = NoPerm()(exp.pos, exp.info)
    exp match {
      case _: PermAdd => permLit
      case _: PermSub => permLit
      case _: PermMul => permLit
      case _: PermDiv => permLit
      case _: AbstractConcretePerm => permLit
      case v: LocalVar if v.typ == Perm => permLit
      case _ =>
        intLit
    }
  }

  private val bigIntZero = BigInt(0)
}
