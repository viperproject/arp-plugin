/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast.utility.Rewriter.ContextC
import viper.silver.ast._
import viper.silver.plugin.ARPPluginNormalize.NormalizedExpression

object ARPPluginBreathe {

  def handleInhale(input: Program, inhale: Inhale, ctx: ContextC[Node, String]): Node = {
    def rdRewriter[T <: Node](exp: T) = ARPPluginUtils.rewriteRd(ctx.c)(exp)

    val i = Inhale(rdRewriter(inhale.exp))(inhale.pos, inhale.info, inhale.errT + NodeTrafo(inhale))
    ctx.noRec(i)
    Seqn(
      Seq(i) ++
        splitBreathing(inhale.exp).map({
          case accessPredicate: FieldAccessPredicate =>
            val normalized = ARPPluginNormalize.normalizeExpression(accessPredicate.perm, ARPPluginNormalize.rdPermContext)
            if (normalized.isDefined) {
              Some(generateLogUpdate(input, accessPredicate, normalized.get, minus = false, ctx)(accessPredicate.pos, accessPredicate.info, accessPredicate.errT).map(rdRewriter))
            } else {
              Some(Seq(Assert(BoolLit(b = false)())()))
            }
          case _ =>
            None
        }).filter(_.isDefined).flatMap(_.get),
      Seq()
    )(inhale.pos, inhale.info, inhale.errT + NodeTrafo(inhale))
  }

  def handleExhale(input: Program, exhale: Exhale, ctx: ContextC[Node, String]): Node = {
    val labelName = ARPPluginNaming.getNewName(suffix = "exhale_label")

    def rdRewriter[T <: Node](exp: T) = ARPPluginUtils.rewriteRd(ctx.c)(exp)

    def oldRewriter[T <: Node](exp: T) = ARPPluginUtils.rewriteOldExpr(labelName, oldLabel = false)(exp)

    Seqn(
      Seq(Label(labelName, Seq())(exhale.pos, exhale.info)) ++
        splitBreathing(exhale.exp).map {
          case accessPredicate: FieldAccessPredicate =>
            val normalized = ARPPluginNormalize.normalizeExpression(accessPredicate.perm, ARPPluginNormalize.rdPermContext)
            if (normalized.isDefined) {
              val e = Exhale(
                oldRewriter(rdRewriter(accessPredicate))
              )(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale))
              ctx.noRec(e)

              Seqn(
                Seq(rdRewriter(generateAssumption(input, accessPredicate, normalized.get)(exhale.pos, exhale.info, exhale.errT))) ++
                  generateLogUpdate(
                    input, accessPredicate, normalized.get, minus = true, ctx
                  )(accessPredicate.pos, accessPredicate.info, accessPredicate.errT)
                    .map(rdRewriter).map(oldRewriter) ++
                  Seq(e),
                Seq()
              )(exhale.pos, exhale.info)
            } else {
              Assert(BoolLit(b = false)())()
            }
          case default =>
            val e = Exhale(
              oldRewriter(rdRewriter(default))
            )(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale))
            ctx.noRec(e)
            e
        },
      Seq(Label(labelName, Seq())(exhale.pos, exhale.info))
    )(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale))
  }

  def splitBreathing(breath: Exp): Seq[Exp] = {
    breath match {
      case And(left, right) => splitBreathing(left) ++ splitBreathing(right)
      case default => Seq(default)
    }
  }

  def generateAssumption(input: Program, accessPredicate: FieldAccessPredicate, normalized: NormalizedExpression)(pos: Position, info: Info, errT: ErrorTrafo): Stmt = {
    // FieldAcces
    val fieldAccess = accessPredicate.loc
    val field = fieldAccess.field
    val fieldFunctionName = ARPPluginNaming.getNameFor(field)
    val rcv = fieldAccess.rcv
    val arpFieldFunctionDomain = ARPPluginUtils.getDomain(input, ARPPluginNaming.fieldFunctionDomainName).get
    val arpFieldFunction = ARPPluginUtils.getDomainFunction(arpFieldFunctionDomain, fieldFunctionName).get

    // ARPLog
    val arpLogDomain = ARPPluginUtils.getDomain(input, ARPPluginNaming.logDomainName).get
    val arpLogType = DomainType(arpLogDomain, Map[TypeVar, Type]() /* TODO: What's the deal with this? */)
    val arpLogSum = ARPPluginUtils.getDomainFunction(arpLogDomain, ARPPluginNaming.logDomainSum).get
    val arpLog = LocalVar(ARPPluginNaming.logName)(arpLogType, accessPredicate.pos, accessPredicate.info)

    def getSumCall(level: Int): DomainFuncApp = DomainFuncApp(
      arpLogSum,
      Seq(
        rcv,
        DomainFuncApp(arpFieldFunction, Seq(), Map[TypeVar, Type]())(pos, info, errT),
        IntLit(level)(pos, info, errT),
        arpLog
      ),
      Map[TypeVar, Type]() /* TODO: What's the deal with this? */
    )(pos, info, errT)

    generateAssumptionWorker(fieldAccess, getSumCall, normalized, None)(pos, info, errT)
  }

  def generateAssumptionWorker(fieldAccess: FieldAccess, getSumCall: Int => DomainFuncApp, normalized: NormalizedExpression, assumption: Option[Exp])(pos: Position, info: Info, errT: ErrorTrafo): Stmt = {
    def addAssumption(exp: Exp) = if (assumption.isDefined) Some(PermAdd(exp, assumption.get)(pos, info, errT)) else Some(exp)

    def recursive(n: NormalizedExpression = normalized, a: Option[Exp] = assumption) = generateAssumptionWorker(fieldAccess, getSumCall, n, a)(pos, info, errT)

    val currentPerm = CurrentPerm(fieldAccess)(pos, info, errT)
    if (normalized.wildcard.isDefined) {
      Inhale(PermLtCmp(normalized.wildcard.get.unit.get, currentPerm)(pos, info, errT))(pos, info, errT)
    } else {
      if (normalized.exps.isEmpty) {
        if (normalized.const.isEmpty) {
          if (assumption.isDefined) {
            Inhale(PermLtCmp(assumption.get, currentPerm)(pos, info, errT))(pos, info, errT)
          } else {
            Inhale(BoolLit(b = true)(pos, info, errT))(pos, info, errT)
          }
        } else {
          val newNormalized = NormalizedExpression(Seq(), None, None)
          val const = normalized.const.get
          If(
            And(
              PermLtCmp(NoPerm()(pos, info, errT), const.exp)(pos, info, errT),
              PermLtCmp(const.exp, getSumCall(const.check))(pos, info, errT)
            )(pos, info, errT),
            Seqn(
              Seq(recursive(newNormalized, addAssumption(const.exp))),
              Seq()
            )(pos, info, errT),
            Seqn(
              Seq(recursive(newNormalized)),
              Seq()
            )(pos, info, errT)
          )(pos, info, errT)
        }
      } else {
        val cur = normalized.exps.head
        val newNormalized = NormalizedExpression(normalized.exps.tail, normalized.const, None)
        If(
          PermLeCmp(IntLit(0)(pos, info, errT), cur.exp)(pos, info, errT),
          // 0 <= exp
          Seqn(
            Seq(
              If(
                PermLtCmp(NoPerm()(pos, info, errT), getSumCall(cur.check))(pos, info, errT),
                // none < sum(check)
                Seqn(
                  Seq(recursive(newNormalized, addAssumption(cur.getTotal(pos, info, errT)))),
                  Seq()
                )(pos, info, errT),
                // none >= sum(check)
                Seqn(
                  Seq(recursive(newNormalized)),
                  Seq()
                )(pos, info, errT)
              )(pos, info, errT)
            ),
            Seq()
          )(pos, info, errT),
          // 0 > exp
          Seqn(
            Seq(),
            Seq()
          )(pos, info, errT)
        )(pos, info, errT)
      }
    }
  }

  def generateLogUpdate(input: Program, fieldAccessPredicate: FieldAccessPredicate, normalized: NormalizedExpression, minus: Boolean, ctx: ContextC[Node, String])(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {

    // ARPLog
    val arpLogDomain = ARPPluginUtils.getDomain(input, ARPPluginNaming.logDomainName).get
    val arpLogType = DomainType(arpLogDomain, Map[TypeVar, Type]() /* TODO: What's the deal with this? */)
    val arpLog = LocalVar(ARPPluginNaming.logName)(arpLogType, fieldAccessPredicate.pos, fieldAccessPredicate.info)
    val arpLogCons = ARPPluginUtils.getDomainFunction(arpLogDomain, ARPPluginNaming.logDomainCons).get

    // FieldAccess
    val fieldAccess = fieldAccessPredicate.loc
    val field = fieldAccess.field
    val fieldFunctionName = ARPPluginNaming.getNameFor(field)
    val rcv = fieldAccess.rcv
    val arpFieldFunctionDomain = ARPPluginUtils.getDomain(input, ARPPluginNaming.fieldFunctionDomainName).get
    val arpFieldFunction = ARPPluginUtils.getDomainFunction(arpFieldFunctionDomain, fieldFunctionName).get

    def getConsCall(level: Int, permission: Exp): LocalVarAssign = {
      LocalVarAssign(
        arpLog,
        DomainFuncApp(
          arpLogCons, Seq(
            rcv,
            DomainFuncApp(arpFieldFunction, Seq(), Map[TypeVar, Type]())(pos, info, errT),
            if (minus) Minus(permission)(pos, info, errT) else permission,
            IntLit(level)(pos, info, errT),
            arpLog
          ),
          Map[TypeVar, Type]() /* TODO: What's the deal with this? */
        )(pos, info, errT)
      )(pos, info, errT)
    }

    var logSeq = Seq[Stmt]()
    (normalized.const ++ normalized.wildcard ++ normalized.exps).foreach(e => logSeq :+= getConsCall(e.store, e.getTotal(pos, info, errT)))
    logSeq
  }

}