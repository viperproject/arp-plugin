/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.ContextC
import viper.silver.plugin.ARPPlugin.ARPContext
import viper.silver.plugin.ARPPluginNormalize.{NormalizedExpression, NormalizedPart}
import viper.silver.verifier.errors.Internal
import viper.silver.verifier.reasons.FeatureUnsupported

class ARPPluginQuantified(plugin: ARPPlugin) {

  def handleForallBreathe(input: Program, isInhale: Boolean, forall: Forall, rdPerm: (Exp, FuncApp) => NormalizedExpression, nextWildcardName: () => String, ctx: ContextC[Node, ARPContext]): Seq[Stmt] = {
    forall.exp match {
      case Implies(left, acc: AccessPredicate) =>
        val normalized = plugin.normalize.normalizeExpression(acc.perm, rdPerm)
        if (normalized.isDefined) {
          if (normalized.get.wildcard.isDefined) {
            val wildcardName = nextWildcardName()
            (plugin.breathe.generateAssumption(input, acc.loc, normalized.get, ctx.c.logName, negativeOnly = isInhale, wildcardName = wildcardName)(forall.pos, forall.info, NodeTrafo(forall))
              .map(e => Inhale(Forall(forall.variables, forall.triggers, Implies(left, e)(forall.pos, forall.info))(forall.pos, forall.info))(forall.pos, forall.info)).toSeq ++
              generateLogUpdateQuantifiedFromNormalized(input, forall, left, normalized.get, acc.loc, minus = !isInhale, ctx)(forall.pos, forall.info, NodeTrafo(forall)))
              .map(plugin.utils.rewriteRd(wildcardName, Seq(wildcardName)))
          } else {
            (plugin.breathe.generateAssumption(input, acc.loc, normalized.get, ctx.c.logName, negativeOnly = isInhale)(forall.pos, forall.info, NodeTrafo(forall))
              .map(e => Inhale(Forall(forall.variables, forall.triggers, Implies(left, e)(forall.pos, forall.info))(forall.pos, forall.info))(forall.pos, forall.info)).toSeq ++
              generateLogUpdateQuantifiedFromNormalized(input, forall, left, normalized.get, acc.loc, minus = !isInhale, ctx)(forall.pos, forall.info, NodeTrafo(forall)))
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

  def handleForallAssert(input: Program, forall: Forall, rdPerm: (Exp, FuncApp) => NormalizedExpression, nextWildcardName: () => String, ctx: ContextC[Node, ARPContext]): Seq[Stmt] = {
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
      case _ =>
        plugin.reportError(Internal(exp, FeatureUnsupported(exp, "Could not find quantified reference " + exp + " " + exp.rcv.getClass)))
        LocalVar("COULD_NOT_FIND_REF")(Ref)
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

    generateLogUpdateQuantified(
      input,
      plugin.utils.getAccessRcv(accAccess)(pos, info, errT),
      forall.variables,
      _ => cond,
      (_, level, _) => generateNorm(normalized.const.toSeq ++ normalized.exps, level),
      accAccess,
      minus,
      ctx
    )(pos, info, errT)
  }


  def generateLogUpdateQuantified(input: Program, quantifiedRefVal: Exp, additionalQuantified: Seq[LocalVarDecl], condition: Exp => Exp, addval: (Exp, LocalVar, LocalVar) => Exp, accAccess: LocationAccess, minus: Boolean, ctx: ContextC[Node, ARPContext])(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    val isSeqIndex = quantifiedRefVal.isInstanceOf[SeqIndex]
    val isPredicate = accAccess.isInstanceOf[PredicateAccess]
    val isFieldAccess = !isSeqIndex && !isPredicate
    val quantifiedRefProposedName = if (isFieldAccess) Some(getQuantifiedReference(accAccess.asInstanceOf[FieldAccess]).name) else None

    val arpLogType = plugin.utils.getARPLogType(input)
    val arpLog = LocalVar(ctx.c.logName)(arpLogType, pos, info)
    val arpLogSum = plugin.utils.getARPLogFunction(input, plugin.naming.logDomainSum)
    val arpLogMaxLevel = plugin.utils.getARPLogFunction(input, plugin.naming.logDomainMaxLevel)

    val tmpLogName = plugin.naming.getNewName(suffix = "tmpLog")
    val tmpLog = LocalVar(tmpLogName)(arpLogType, pos, info)
    val quantifiedRefName = quantifiedRefProposedName.getOrElse(plugin.naming.getNewName("quantRef"))
    val quantifiedRef = LocalVar(quantifiedRefName)(Ref, pos, info)
    val quantifiedFieldName = plugin.naming.getNewName("quantField")
    val quantifiedField = LocalVar(quantifiedFieldName)(Int, pos, info)
    val quantifiedLevelName = plugin.naming.getNewName("quantLevel")
    val quantifiedLevel = LocalVar(quantifiedLevelName)(Int, pos, info)

    val arpFieldFunctionAcc = plugin.utils.getAccessDomainFuncApp(input, accAccess)(pos, info, errT)

    val add = if (minus) (a: Exp, b: Exp) => PermSub(a, b)(pos, info) else (a: Exp, b: Exp) => PermAdd(a, b)(pos, info)

    val baseQuantifiedVars = Seq(LocalVarDecl(quantifiedRefName, Ref)(pos, info), LocalVarDecl(quantifiedLevelName, Int)(pos, info), LocalVarDecl(quantifiedFieldName, Int)(pos, info))
    // TODO: additionalQuantified is probably not a good idea
    val quantifiedVars = if (isSeqIndex) {
      baseQuantifiedVars
    } else if (isPredicate){
      baseQuantifiedVars ++ additionalQuantified
    } else {
      baseQuantifiedVars
    }

    val conditionExp = if (isSeqIndex) {
      // TODO restore original condition
      SeqContains(quantifiedRef, quantifiedRefVal.asInstanceOf[SeqIndex].s)(pos, info)
    } else if (isPredicate){
      condition(quantifiedRef)
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
            Implies(
              And(
                LeCmp(IntLit(0)(pos, info), quantifiedLevel)(pos, info),
                LeCmp(quantifiedLevel, DomainFuncApp(arpLogMaxLevel, Seq(tmpLog), Map[TypeVar, Type]())(pos, info))(pos, info)
              )(pos, info),
              EqCmp(
                DomainFuncApp(arpLogSum, Seq(quantifiedRef, quantifiedField, quantifiedLevel, arpLog), Map[TypeVar, Type]())(pos, info),
                CondExp(
                  And(
                    conditionExp,
                    EqCmp(quantifiedField, arpFieldFunctionAcc)(pos, info)
                  )(pos, info),
                  add(
                    DomainFuncApp(arpLogSum, Seq(quantifiedRef, quantifiedField, quantifiedLevel, tmpLog), Map[TypeVar, Type]())(pos, info),
                    addval(quantifiedRef, quantifiedLevel, tmpLog)
                  ),
                  DomainFuncApp(arpLogSum, Seq(quantifiedRef, quantifiedField, quantifiedLevel, tmpLog), Map[TypeVar, Type]())(pos, info)
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