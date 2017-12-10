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
import viper.silver.verifier.errors.{AssertFailed, Internal}
import viper.silver.verifier.reasons.FeatureUnsupported

class ARPPluginQuantified(plugin: ARPPlugin) {

  def handleForallBreathe(input: Program, isInhale: Boolean, forall: Forall, rdPerm: (Exp, FuncApp) => NormalizedExpression, nextWildcardName: => String, ctx: ContextC[Node, ARPContext]): Seq[Stmt] = {
    forall.exp match {
      case Implies(left, acc: FieldAccessPredicate) =>
        val normalized = plugin.normalize.normalizeExpression(acc.perm, rdPerm)
        val quantifiedReference = getQuantifiedReference(acc.loc)
        if (normalized.isDefined) {
          if (normalized.get.wildcard.isDefined) {
            val wildcardName = nextWildcardName
            (plugin.breathe.generateAssumption(input, acc.loc, normalized.get, ctx.c.logName, negativeOnly = isInhale, wildcardName = wildcardName)(forall.pos, forall.info, NodeTrafo(forall))
              .map(e => Inhale(Forall(forall.variables, forall.triggers, Implies(left, e)(forall.pos, forall.info))(forall.pos, forall.info))(forall.pos, forall.info)).toSeq ++
              generateLogUpdateQuantifiedFromNormalized(input, forall, left, normalized.get, quantifiedReference.name, acc.loc, minus = !isInhale, ctx)(forall.pos, forall.info, NodeTrafo(forall)))
              .map(plugin.utils.rewriteRd(wildcardName, Seq(wildcardName)))
          } else {
            (plugin.breathe.generateAssumption(input, acc.loc, normalized.get, ctx.c.logName, negativeOnly = isInhale)(forall.pos, forall.info, NodeTrafo(forall))
              .map(e => Inhale(Forall(forall.variables, forall.triggers, Implies(left, e)(forall.pos, forall.info))(forall.pos, forall.info))(forall.pos, forall.info)).toSeq ++
              generateLogUpdateQuantifiedFromNormalized(input, forall, left, normalized.get, quantifiedReference.name, acc.loc, minus = !isInhale, ctx)(forall.pos, forall.info, NodeTrafo(forall)))
              .map(plugin.utils.rewriteRd(ctx.c.rdName))
          }
        } else {
          Seq(Assert(BoolLit(b = false)())())
        }
      case default if default.exists(n => n.isInstanceOf[AccessPredicate]) =>
        plugin.reportError(Internal(forall, FeatureUnsupported(forall, "Forall can not be logged")))
        Seq(Assert(BoolLit(b = false)())())
      case _ => Seq()
    }
  }

  def handleForallAssert(input: Program, forall: Forall, rdPerm: (Exp, FuncApp) => NormalizedExpression, nextWildcardName: => String, ctx: ContextC[Node, ARPContext]): Seq[Stmt] = {
    forall.exp match {
      case Implies(left, acc: FieldAccessPredicate) =>
        val normalized = plugin.normalize.normalizeExpression(acc.perm, rdPerm, ignoreErrors = true)
        if (normalized.isDefined) {
          if (normalized.get.wildcard.isDefined) {
            val wildcardName = nextWildcardName
            plugin.breathe.generateAssumption(input, acc.loc, normalized.get, ctx.c.logName, wildcardName = wildcardName)(forall.pos, forall.info, NodeTrafo(forall))
              .map(e => Inhale(Forall(forall.variables, forall.triggers, Implies(left, e)(forall.pos, forall.info))(forall.pos, forall.info))(forall.pos, forall.info))
              .map(plugin.utils.rewriteRd(wildcardName, Seq(wildcardName))).toSeq
          } else {
            plugin.breathe.generateAssumption(input, acc.loc, normalized.get, ctx.c.logName)(forall.pos, forall.info, NodeTrafo(forall))
              .map(e => Inhale(Forall(forall.variables, forall.triggers, Implies(left, e)(forall.pos, forall.info))(forall.pos, forall.info))(forall.pos, forall.info))
              .map(plugin.utils.rewriteRd(ctx.c.logName)).toSeq
          }
        } else {
          Seq()
        }
      case _ => Seq()
    }
  }

  def getQuantifiedReference(exp: FieldAccess): LocalVar = {
    exp.rcv match {
      case l: LocalVar => l
      case f: FieldAccess => getQuantifiedReference(f)
    }
  }

  def generateLogUpdateCurrentPerm(input: Program, accAccess: LocationAccess, permAccess: LocationAccess, minus: Boolean, ctx: ContextC[Node, ARPContext])(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    val arpLogSum = plugin.utils.getARPLogFunction(input, plugin.naming.logDomainSum)

    val accRcv = plugin.utils.getAccessRcv(accAccess)(pos, info, errT)
    val permRcv = plugin.utils.getAccessRcv(permAccess)(pos, info, errT)
    val arpFieldFunctionPerm = plugin.utils.getAccessDomainFuncApp(input, permAccess)(pos, info, errT)

    val quantRefName = plugin.naming.getNewName(suffix = "quantRef")
    generateLogUpdateQuantified(
      input,
      quantRefName,
      LocalVar(quantRefName)(Perm, pos, info),
      Seq(),
      quantifiedRef => EqCmp(quantifiedRef, accRcv)(pos, info),
      (_, level, tmpLog) => DomainFuncApp(arpLogSum, Seq(permRcv, arpFieldFunctionPerm, level, tmpLog), Map[TypeVar, Type]())(pos, info),
      accAccess,
      minus,
      ctx
    )(pos, info, errT)
  }

  def generateLogUpdateQuantifiedFromNormalized(input: Program, forall: Forall, cond: Exp, normalized: NormalizedExpression, quantifiedReferenceName: String, accAccess: LocationAccess, minus: Boolean, ctx: ContextC[Node, ARPContext])(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    def generateNorm(norms: Seq[NormalizedPart], level: LocalVar): Exp = {
      val e = norms.head
      val total = e.getTotal(plugin)(pos, info, errT)
      CondExp(
        EqCmp(level, IntLit(e.store)(pos, info, errT))(pos, info, errT),
        if (minus) PermMinus(total)(pos, info, errT) else total,
        if (norms.size == 1) NoPerm()(pos, info, errT) else generateNorm(norms.tail, level)
      )(pos, info, errT)
    }

    generateLogUpdateQuantified(
      input,
      quantifiedReferenceName,
      plugin.utils.getAccessRcv(accAccess)(pos, info, errT),
      forall.variables.filterNot(v => v.name == quantifiedReferenceName),
      _ => cond,
      (_, level, _) => generateNorm(normalized.const.toSeq ++ normalized.exps, level),
      accAccess,
      minus,
      ctx
    )(pos, info, errT)
  }


  def generateLogUpdateQuantified(input: Program, quantifiedRefName: String, quantifiedRefValue: Exp, additionalQuantified: Seq[LocalVarDecl], condition: Exp => Exp, addval: (Exp, LocalVar, LocalVar) => Exp, accAccess: LocationAccess, minus: Boolean, ctx: ContextC[Node, ARPContext])(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    val arpLogType = plugin.utils.getARPLogType(input)
    val arpLog = LocalVar(ctx.c.logName)(arpLogType, pos, info)
    val arpLogSum = plugin.utils.getARPLogFunction(input, plugin.naming.logDomainSum)
    val arpLogMaxLevel = plugin.utils.getARPLogFunction(input, plugin.naming.logDomainMaxLevel)

    val tmpLogName = plugin.naming.getNewName(suffix = "tmpLog")
    val tmpLog = LocalVar(tmpLogName)(arpLogType, pos, info)
    val quantifiedRef = quantifiedRefValue
    val quantifiedIntName = plugin.naming.getNewName(suffix = "quantInt")
    val quantifiedInt = LocalVar(quantifiedIntName)(Int, pos, info)

    val arpFieldFunctionAcc = plugin.utils.getAccessDomainFuncApp(input, accAccess)(pos, info, errT)

    val add = if (minus) (a: Exp, b: Exp) => PermSub(a, b)(pos, info) else (a: Exp, b: Exp) => PermAdd(a, b)(pos, info)

    Seq(
      Seqn(
        Seq(
          LocalVarAssign(tmpLog, arpLog)(pos, info, errT),
          plugin.utils.havoc(arpLog, ctx),
          Inhale(Forall(
            Seq(LocalVarDecl(quantifiedRefName, Ref)(pos, info), LocalVarDecl(quantifiedIntName, Int)(pos, info)) ++ additionalQuantified,
            Seq(Trigger(Seq(
              DomainFuncApp(arpLogSum, Seq(quantifiedRef, arpFieldFunctionAcc, quantifiedInt, arpLog), Map[TypeVar, Type]())(pos, info)
            ))(pos, info)),
            Implies(
              And(
                LeCmp(IntLit(0)(pos, info), quantifiedInt)(pos, info),
                LeCmp(quantifiedInt, DomainFuncApp(arpLogMaxLevel, Seq(tmpLog), Map[TypeVar, Type]())(pos, info))(pos, info)
              )(pos, info),
              EqCmp(
                DomainFuncApp(arpLogSum, Seq(quantifiedRef, arpFieldFunctionAcc, quantifiedInt, arpLog), Map[TypeVar, Type]())(pos, info),
                CondExp(
                  condition(quantifiedRef),
                  add(
                    DomainFuncApp(arpLogSum, Seq(quantifiedRef, arpFieldFunctionAcc, quantifiedInt, tmpLog), Map[TypeVar, Type]())(pos, info),
                    addval(quantifiedRef, quantifiedInt, tmpLog)
                  ),
                  DomainFuncApp(arpLogSum, Seq(quantifiedRef, arpFieldFunctionAcc, quantifiedInt, tmpLog), Map[TypeVar, Type]())(pos, info)
                )(pos, info)
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
