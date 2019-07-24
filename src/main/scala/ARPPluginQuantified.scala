// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.rewriter.{ContextC, SimpleContext, Strategy, StrategyBuilder}
import viper.silver.plugin.ARPPlugin.ARPContext
import viper.silver.plugin.ARPPluginNormalize.{NormalizedExpression, NormalizedPart}
import viper.silver.verifier.errors.{ExhaleFailed, InhaleFailed, Internal}
import viper.silver.verifier.reasons.FeatureUnsupported

class ARPPluginQuantified(plugin: ARPPlugin) {

  def handleForallBreathe(input: Program, isInhale: Boolean, forall: Forall, rdRewriter: Stmt => Stmt, labelName: String, rdPerm: (Exp, FuncApp) => NormalizedExpression, nextWildcardName: () => String, ctx: ContextC[Node, ARPContext]): Seq[Stmt] = {
    def oldRewriter[T <: Node](exp: T) = plugin.utils.rewriteOldExpr(input, labelName, oldLabel = false)(exp)

    forall.exp match {
      case Implies(left, AccessPredicate(loc@FieldAccess(_: LocalVar, _: Field), perm)) if !plugin.isAccIgnored(loc) =>
        val normalized = plugin.normalize.normalizeExpression(perm, rdPerm)
        val inahelFaildedTrafo = ErrTrafo({
          case InhaleFailed(node, reason, cached) => ExhaleFailed(Exhale(forall)(forall.pos, forall.info), reason, cached)
        })
        if (normalized.isDefined) {
          if (normalized.get.wildcard.isDefined) {
            val wildcardName = nextWildcardName()
            val stmts = (plugin.breathe.generateAssumption(input, loc, normalized.get, ctx.c.logName, negativeOnly = isInhale, wildcardName = wildcardName)(forall.pos, forall.info, NodeTrafo(forall))
              .map(e => Inhale(Forall(forall.variables, forall.triggers, Implies(left, e)(forall.pos, forall.info))(forall.pos, forall.info))(forall.pos, forall.info)).toSeq ++
              generateLogUpdateQuantifiedFromNormalized(input, forall, left, normalized.get, loc, minus = !isInhale, ctx)(forall.pos, forall.info, NodeTrafo(forall) + inahelFaildedTrafo))
              .map(plugin.utils.rewriteRd(wildcardName, Seq(wildcardName)))
            if (isInhale) {
              stmts
            } else {
              stmts.map(oldRewriter)
            }
          } else {
            val stmts = (plugin.breathe.generateAssumption(input, loc, normalized.get, ctx.c.logName, negativeOnly = isInhale)(forall.pos, forall.info, NodeTrafo(forall))
              .map(e => Inhale(Forall(forall.variables, forall.triggers, Implies(left, e)(forall.pos, forall.info))(forall.pos, forall.info))(forall.pos, forall.info)).toSeq ++
              generateLogUpdateQuantifiedFromNormalized(input, forall, left, normalized.get, loc, minus = !isInhale, ctx)(forall.pos, forall.info, NodeTrafo(forall) + inahelFaildedTrafo))
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
      case Implies(left, acc: FieldAccessPredicate) if !plugin.isAccIgnored(acc.loc) =>
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

  def generateLogUpdateCurrentPerm(input: Program, accAccess: LocationAccess, permAccess: ResourceAccess, changeValue: Exp => Exp, minus: Boolean, ctx: ContextC[Node, ARPContext])(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    val arpLogSum = plugin.utils.getARPLogFunction(input, plugin.naming.logDomainSum)

    val accRcv = plugin.utils.getAccessRcv(accAccess)(pos, info, errT)
    val permRcv = plugin.utils.getAccessRcv(permAccess)(pos, info, errT)
    val arpFieldFunction = plugin.utils.getAccessDomainFuncApp(input, permAccess)(pos, info, errT)

    val quantRefName = plugin.naming.getNewName("whateverdoesntmatter")
    generateLogUpdateQuantified(
      input,
      LocalVar(quantRefName, Ref)(pos, info),
      Seq(),
      quantifiedRef => EqCmp(quantifiedRef, accRcv)(pos, info, errT),
      (_, level, tmpLog) => changeValue(DomainFuncApp(arpLogSum, Seq(permRcv, arpFieldFunction, level, tmpLog), Map[TypeVar, Type]())(pos, info, errT)),
      accAccess,
      minus,
      ctx
    )(pos, info, errT)
  }

  def generateLogUpdateQuantifiedFromNormalized(input: Program, forall: Forall, cond: Exp, normalized: NormalizedExpression, accAccess: LocationAccess, minus: Boolean, ctx: ContextC[Node, ARPContext])(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    def getRewriter(quantVar: LocalVar): LocalVar => Strategy[Node, SimpleContext[Node]] = {
      def rewriter(quantifiedRef: LocalVar): Strategy[Node, SimpleContext[Node]] = {
        StrategyBuilder.Slim[Node]({
          case LocalVar(quantVar.name, _) => quantifiedRef
        })
      }

      rewriter
    }

    def condRewriter(v: LocalVar)(quantifiedRef: LocalVar) = getRewriter(v)(quantifiedRef).execute[Exp](cond)

    val (quantVar, condPrime, vars): (Option[LocalVar], LocalVar => Exp, Seq[LocalVarDecl]) = accAccess match {
      case FieldAccess(v: LocalVar, _: Field) =>
        (Some(v), ref => condRewriter(v)(ref), Seq())
      case default =>
        (None, _ => cond, forall.variables)
    }

    def generateNorm(norms: Seq[NormalizedPart], quantifiedRef: LocalVar, level: LocalVar): Exp = {
      val e = norms.head
      val total = if (quantVar.isDefined) {
        getRewriter(quantVar.get)(quantifiedRef).execute[Exp](e.getTotal(plugin)(pos, info, errT))
      } else {
        e.getTotal(plugin)(pos, info, errT)
      }
      CondExp(
        EqCmp(level, IntLit(e.store)(pos, info, errT))(pos, info, errT),
        total,
        if (norms.size == 1) NoPerm()(pos, info, errT) else generateNorm(norms.tail, quantifiedRef, level)
      )(pos, info, errT)
    }

    if ((normalized.const ++ normalized.wildcard ++ normalized.exps).isEmpty) {
      plugin.reportError(Internal(forall, FeatureUnsupported(forall, "Normalized permission is not wellformed")))
      Seq()
    } else {
      generateLogUpdateQuantified(
        input,
        plugin.utils.getAccessRcv(accAccess)(pos, info, errT),
        vars,
        condPrime,
        (quantifiedRef, level, _) => generateNorm(normalized.const.toSeq ++ normalized.wildcard.toSeq ++ normalized.exps, quantifiedRef, level),
        accAccess,
        minus,
        ctx
      )(pos, info, errT)
    }
  }


  def generateLogUpdateQuantified(input: Program, quantifiedRefVal: Exp, additionalQuantified: Seq[LocalVarDecl], condition: LocalVar => Exp, addval: (LocalVar, LocalVar, LocalVar) => Exp, accAccess: LocationAccess, minus: Boolean, ctx: ContextC[Node, ARPContext])(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    val arpLogType = plugin.utils.getARPLogType(input)
    val arpLog = LocalVar(ctx.c.logName, arpLogType)(pos, info)
    val arpLogSum = plugin.utils.getARPLogFunction(input, plugin.naming.logDomainSum)

    val tmpLogName = plugin.naming.getNewName(suffix = "tmpLog")
    val tmpLog = LocalVar(tmpLogName, arpLogType)(pos, info)
    val quantifiedRefName = plugin.naming.getNewName("quantRef")
    val quantifiedRef = LocalVar(quantifiedRefName, Ref)(pos, info)
    val quantifiedFieldName = plugin.naming.getNewName("quantField")
    val quantifiedField = LocalVar(quantifiedFieldName, Int)(pos, info)
    val quantifiedLevelName = plugin.naming.getNewName("quantLevel")
    val quantifiedLevel = LocalVar(quantifiedLevelName, Int)(pos, info)

    val arpFieldFunctionAcc = plugin.utils.getAccessDomainFuncApp(input, accAccess)(pos, info, errT)

    val add = if (minus) (a: Exp, b: Exp) => PermSub(a, b)(pos, info, errT) else (a: Exp, b: Exp) => PermAdd(a, b)(pos, info, errT)

    val quantifiedVars = Seq(LocalVarDecl(quantifiedRefName, Ref)(pos, info, errT), LocalVarDecl(quantifiedLevelName, Int)(pos, info, errT), LocalVarDecl(quantifiedFieldName, Int)(pos, info, errT))

    val conditionExp = if (additionalQuantified.nonEmpty) {
      Exists(
        additionalQuantified,
        Seq(),
        And(
          condition(quantifiedRef),
          And(
            EqCmp(quantifiedRef, quantifiedRefVal)(pos, info, errT),
            EqCmp(quantifiedField, arpFieldFunctionAcc)(pos, info, errT)
          )(pos, info, errT)
        )(pos, info, errT)
      )(pos, info, errT)
    } else {
      And(
        condition(quantifiedRef),
        EqCmp(quantifiedField, arpFieldFunctionAcc)(pos, info, errT)
      )(pos, info, errT)
    }

    Seq(
      Seqn(
        Seq(
          LocalVarAssign(tmpLog, arpLog)(pos, info, errT),
          plugin.utils.havoc(arpLog, ctx),
          Inhale(Forall(
            quantifiedVars,
            Seq(Trigger(Seq(
              DomainFuncApp(arpLogSum, Seq(quantifiedRef, quantifiedField, quantifiedLevel, arpLog), Map[TypeVar, Type]())(pos, info, errT)
            ))(pos, info, errT)),
            EqCmp(
              DomainFuncApp(arpLogSum, Seq(quantifiedRef, quantifiedField, quantifiedLevel, arpLog), Map[TypeVar, Type]())(pos, info, errT),
              CondExp(
                conditionExp,
                add(
                  DomainFuncApp(arpLogSum, Seq(quantifiedRef, quantifiedField, quantifiedLevel, tmpLog), Map[TypeVar, Type]())(pos, info, errT),
                  addval(quantifiedRef, quantifiedLevel, tmpLog)
                ),
                DomainFuncApp(arpLogSum, Seq(quantifiedRef, quantifiedField, quantifiedLevel, tmpLog), Map[TypeVar, Type]())(pos, info, errT)
              )(pos, info, errT)
            )(pos, info, errT)
          )(pos, info, errT))(pos, info, errT)
        ),
        Seq(
          LocalVarDecl(tmpLogName, arpLogType)(pos, info, errT)
        )
      )(pos, info, errT)
    )
  }

}
