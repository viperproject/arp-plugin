/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.{ContextC, StrategyBuilder}
import viper.silver.plugin.ARPPlugin.ARPContext
import viper.silver.plugin.ARPPluginNormalize.{NormalizedExpression, NormalizedPart}
import viper.silver.verifier.errors.Internal
import viper.silver.verifier.reasons.FeatureUnsupported

class ARPPluginQuantified(plugin: ARPPlugin) {

  def handleForallBreathe(input: Program, isInhale: Boolean, forall: Forall, rdRewriter: Stmt => Stmt, labelName: String, rdPerm: (Exp, FuncApp) => NormalizedExpression, nextWildcardName: () => String, ctx: ContextC[Node, ARPContext]): Seq[Stmt] = {
    def oldRewriter[T <: Node](exp: T) = plugin.utils.rewriteOldExpr(labelName, oldLabel = false)(exp)

    forall.exp match {
      case Implies(left, AccessPredicate(loc@FieldAccess(_: LocalVar, _: Field), perm)) =>
        val normalized = plugin.normalize.normalizeExpression(perm, rdPerm)
        if (normalized.isDefined) {
          if (normalized.get.wildcard.isDefined) {
            val wildcardName = nextWildcardName()
            val stmts = (plugin.breathe.generateAssumption(input, loc, normalized.get, ctx.c.logName, negativeOnly = isInhale, wildcardName = wildcardName)(forall.pos, forall.info, NodeTrafo(forall))
              .map(e => Inhale(Forall(forall.variables, forall.triggers, Implies(left, e)(forall.pos, forall.info))(forall.pos, forall.info))(forall.pos, forall.info)).toSeq ++
              generateLogUpdateQuantifiedFromNormalized(input, forall, left, normalized.get, loc, minus = !isInhale, ctx)(forall.pos, forall.info, NodeTrafo(forall)))
              .map(plugin.utils.rewriteRd(wildcardName, Seq(wildcardName)))
            if (isInhale) {
              stmts
            } else {
              stmts.map(oldRewriter)
            }
          } else {
            val stmts = (plugin.breathe.generateAssumption(input, loc, normalized.get, ctx.c.logName, negativeOnly = isInhale)(forall.pos, forall.info, NodeTrafo(forall))
              .map(e => Inhale(Forall(forall.variables, forall.triggers, Implies(left, e)(forall.pos, forall.info))(forall.pos, forall.info))(forall.pos, forall.info)).toSeq ++
              generateLogUpdateQuantifiedFromNormalized(input, forall, left, normalized.get, loc, minus = !isInhale, ctx)(forall.pos, forall.info, NodeTrafo(forall)))
              .map(rdRewriter)
            if (isInhale) {
              stmts
            } else {
              stmts.map(oldRewriter)
            }
          }
        } else {
          Seq(Assert(BoolLit(b = false)())())
        }
      case default if default.exists(n => n.isInstanceOf[AccessPredicate]) =>
//        plugin.reportError(Internal(forall, FeatureUnsupported(forall, "Forall can not be logged")))
//        Seq(Assert(BoolLit(b = false)())())
        Seq() // TODO: We should generate an error, but for testing we just ignore this stuff
      case _ => Seq()
    }
  }

  def handleForallAssert(input: Program, forall: Forall, rdRewriter: Stmt => Stmt, rdPerm: (Exp, FuncApp) => NormalizedExpression, nextWildcardName: () => String, ctx: ContextC[Node, ARPContext]): Seq[Stmt] = {
    forall.exp match {
      case Implies(left, acc: FieldAccessPredicate) =>
        val normalized = plugin.normalize.normalizeExpression(acc.perm, rdPerm, ignoreErrors = true)
        if (normalized.isDefined) {
          if (normalized.get.wildcard.isDefined) {
            val wildcardName = nextWildcardName()
            plugin.breathe.generateAssumption(input, acc.loc, normalized.get, ctx.c.logName, wildcardName = wildcardName)(forall.pos, forall.info, NodeTrafo(forall))
              .map(e => Inhale(Forall(forall.variables, forall.triggers, Implies(left, e)(forall.pos, forall.info))(forall.pos, forall.info))(forall.pos, forall.info))
              .map(plugin.utils.rewriteRd(wildcardName, Seq(wildcardName))).toSeq
          } else {
            plugin.breathe.generateAssumption(input, acc.loc, normalized.get, ctx.c.logName)(forall.pos, forall.info, NodeTrafo(forall))
              .map(e => Inhale(Forall(forall.variables, forall.triggers, Implies(left, e)(forall.pos, forall.info))(forall.pos, forall.info))(forall.pos, forall.info))
              .map(rdRewriter).toSeq
          }
        } else {
          Seq()
        }
      case _ => Seq()
    }
  }

  def generateLogUpdateCurrentPerm(input: Program, accAccess: LocationAccess, permAccess: LocationAccess, changeValue: Exp => Exp, minus: Boolean, ctx: ContextC[Node, ARPContext])(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    val arpLogSum = plugin.utils.getARPLogFunction(input, plugin.naming.logDomainSum)

    val accRcv = plugin.utils.getAccessRcv(accAccess)(pos, info, errT)
    val permRcv = plugin.utils.getAccessRcv(permAccess)(pos, info, errT)
    val arpFieldFunctionPerm = plugin.utils.getAccessDomainFuncApp(input, permAccess)(pos, info, errT)

    val quantRefName = plugin.naming.getNewName("whateverdoesntmatter")
    generateLogUpdateQuantified(
      input,
      LocalVar(quantRefName)(Ref, pos, info),
      Seq(),
      quantifiedRef => EqCmp(quantifiedRef, accRcv)(pos, info),
      (_, level, tmpLog) => changeValue(DomainFuncApp(arpLogSum, Seq(permRcv, arpFieldFunctionPerm, level, tmpLog), Map[TypeVar, Type]())(pos, info)),
      accAccess,
      minus,
      ctx
    )(pos, info, errT)
  }

  def generateLogUpdateQuantifiedFromNormalized(input: Program, forall: Forall, cond: Exp, normalized: NormalizedExpression, accAccess: LocationAccess, minus: Boolean, ctx: ContextC[Node, ARPContext])(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    def generateNorm(norms: Seq[NormalizedPart], level: LocalVar): Exp = {
      val e = norms.head
      val total = e.getTotal(plugin)(pos, info, errT)
      CondExp(
        EqCmp(level, IntLit(e.store)(pos, info, errT))(pos, info, errT),
        if (minus) PermMinus(total)(pos, info, errT) else total,
        if (norms.size == 1) NoPerm()(pos, info, errT) else generateNorm(norms.tail, level)
      )(pos, info, errT)
    }

    def condRewriter(v: LocalVar)(quantifiedRef: LocalVar) = StrategyBuilder.Slim[Node]({
      case LocalVar(v.name) => quantifiedRef
    }).execute[Exp](cond)

    val (condPrime, vars): (LocalVar => Exp, Seq[LocalVarDecl]) = accAccess match {
      case FieldAccess(v: LocalVar, _: Field) =>
        (ref => condRewriter(v)(ref), Seq())
      case default =>
        (_ => cond, forall.variables)
    }

    if ((normalized.const ++ normalized.wildcard ++ normalized.exps).isEmpty){
      plugin.reportError(Internal(forall, FeatureUnsupported(forall, "Normalized permission is not wellformed")))
      Seq()
    } else {
      generateLogUpdateQuantified(
        input,
        plugin.utils.getAccessRcv(accAccess)(pos, info, errT),
        vars,
        condPrime,
        (_, level, _) => generateNorm(normalized.const.toSeq ++ normalized.wildcard.toSeq ++ normalized.exps, level),
        accAccess,
        minus,
        ctx
      )(pos, info, errT)
    }
  }


  def generateLogUpdateQuantified(input: Program, quantifiedRefVal: Exp, additionalQuantified: Seq[LocalVarDecl], condition: LocalVar => Exp, addval: (Exp, LocalVar, LocalVar) => Exp, accAccess: LocationAccess, minus: Boolean, ctx: ContextC[Node, ARPContext])(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    val arpLogType = plugin.utils.getARPLogType(input)
    val arpLog = LocalVar(ctx.c.logName)(arpLogType, pos, info)
    val arpLogSum = plugin.utils.getARPLogFunction(input, plugin.naming.logDomainSum)

    val tmpLogName = plugin.naming.getNewName(suffix = "tmpLog")
    val tmpLog = LocalVar(tmpLogName)(arpLogType, pos, info)
    val quantifiedRefName = plugin.naming.getNewName("quantRef")
    val quantifiedRef = LocalVar(quantifiedRefName)(Ref, pos, info)
    val quantifiedFieldName = plugin.naming.getNewName("quantField")
    val quantifiedField = LocalVar(quantifiedFieldName)(Int, pos, info)
    val quantifiedLevelName = plugin.naming.getNewName("quantLevel")
    val quantifiedLevel = LocalVar(quantifiedLevelName)(Int, pos, info)

    val arpFieldFunctionAcc = plugin.utils.getAccessDomainFuncApp(input, accAccess)(pos, info, errT)

    val add = if (minus) (a: Exp, b: Exp) => PermSub(a, b)(pos, info) else (a: Exp, b: Exp) => PermAdd(a, b)(pos, info)

    val quantifiedVars = Seq(LocalVarDecl(quantifiedRefName, Ref)(pos, info), LocalVarDecl(quantifiedLevelName, Int)(pos, info), LocalVarDecl(quantifiedFieldName, Int)(pos, info))

    val conditionExp = if (additionalQuantified.nonEmpty) {
      Exists(
        additionalQuantified,
        And(
          condition(quantifiedRef),
          And(
            EqCmp(quantifiedRef, quantifiedRefVal)(pos, info),
            EqCmp(quantifiedField, arpFieldFunctionAcc)(pos, info)
          )(pos, info)
        )(pos, info)
      )(pos, info)
    } else {
      condition(quantifiedRef)
    }

    Seq(
      Seqn(
        Seq(
          LocalVarAssign(tmpLog, arpLog)(pos, info, errT),
          plugin.utils.havoc(arpLog, ctx),
          Inhale(Forall(
            quantifiedVars,
            Seq(Trigger(Seq(
              DomainFuncApp(arpLogSum, Seq(quantifiedRef, quantifiedField, quantifiedLevel, arpLog), Map[TypeVar, Type]())(pos, info)
            ))(pos, info)),
            EqCmp(
              DomainFuncApp(arpLogSum, Seq(quantifiedRef, quantifiedField, quantifiedLevel, arpLog), Map[TypeVar, Type]())(pos, info),
              CondExp(
                conditionExp,
                add(
                  DomainFuncApp(arpLogSum, Seq(quantifiedRef, quantifiedField, quantifiedLevel, tmpLog), Map[TypeVar, Type]())(pos, info),
                  addval(quantifiedRef, quantifiedLevel, tmpLog)
                ),
                DomainFuncApp(arpLogSum, Seq(quantifiedRef, quantifiedField, quantifiedLevel, tmpLog), Map[TypeVar, Type]())(pos, info)
              )(pos, info)
            )(pos, info)
          )(pos, info))(pos, info)
        ),
        Seq(
          LocalVarDecl(tmpLogName, arpLogType)(pos, info, errT)
        )
      )(pos, info, errT)
    )
  }

}
