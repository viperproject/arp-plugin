/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast.utility.Rewriter.ContextC
import viper.silver.ast._

class ARPPluginBreathe(plugin: ARPPlugin) {

  private type NormalizedExpression = plugin.normalize.NormalizedExpression

  def handleInhale(input: Program, inhale: Inhale, ctx: ContextC[Node, String]): Node = {
    def rdRewriter[T <: Node](exp: T) = plugin.utils.rewriteRd(ctx.c)(exp)

    val i = Inhale(rdRewriter(inhale.exp))(inhale.pos, inhale.info, inhale.errT + NodeTrafo(inhale))
    ctx.noRec(i)
    Seqn(
      Seq(i) ++
        splitBreathing(inhale.exp).map({
          case (accessPredicate: FieldAccessPredicate, constraint) =>
            val normalized = plugin.normalize.normalizeExpression(accessPredicate.perm, plugin.normalize.rdPermContext)
            if (normalized.isDefined) {
              Some(putInIf(
                generateLogUpdate(input, accessPredicate, normalized.get, minus = false, ctx)(accessPredicate.pos, accessPredicate.info, accessPredicate.errT).map(rdRewriter),
                constraint
              )(accessPredicate.pos, accessPredicate.info, accessPredicate.errT))
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
    val labelName = plugin.naming.getNewName(suffix = "exhale_label")

    def rdRewriter[T <: Node](exp: T) = plugin.utils.rewriteRd(ctx.c)(exp)

    def oldRewriter[T <: Node](exp: T) = plugin.utils.rewriteOldExpr(labelName, oldLabel = false)(exp)

    Seqn(
      Seq(Label(labelName, Seq())(exhale.pos, exhale.info)) ++
        splitBreathing(exhale.exp).map {
          case (accessPredicate: FieldAccessPredicate, constraint) =>
            val normalized = plugin.normalize.normalizeExpression(accessPredicate.perm, plugin.normalize.rdPermContext)
            if (normalized.isDefined) {
              val e = Exhale(oldRewriter(rdRewriter(accessPredicate)))(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale))
              ctx.noRec(e)

              Seqn(putInIf(
                generateAssumption(input, accessPredicate, normalized.get)(exhale.pos, exhale.info, exhale.errT).map(rdRewriter) ++
                  generateLogUpdate(
                    input, accessPredicate, normalized.get, minus = true, ctx
                  )(accessPredicate.pos, accessPredicate.info, accessPredicate.errT)
                    .map(rdRewriter).map(oldRewriter) ++
                  Seq(e),
                constraint
              )(exhale.pos, exhale.info, exhale.errT),
                Seq()
              )(exhale.pos, exhale.info)
            } else {
              Assert(BoolLit(b = false)())()
            }
          case (default, constraint) =>
            val e = Exhale(oldRewriter(rdRewriter(default)))(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale))
            ctx.noRec(e)
            putInIf(e, constraint)(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale))
        },
      Seq(Label(labelName, Seq())(exhale.pos, exhale.info))
    )(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale))
  }

  def putInIf(seq: Seq[Stmt], constraint: Option[Exp])(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    if (constraint.isDefined && seq.nonEmpty) {
      Seq(If(constraint.get, Seqn(seq, Seq())(pos, info, errT), Seqn(Seq(), Seq())(pos, info, errT))(pos, info, errT))
    } else {
      seq
    }
  }

  def putInIf(s: Stmt, constraint: Option[Exp])(pos: Position, info: Info, errT: ErrorTrafo): Stmt = {
    if (constraint.isDefined) {
      If(constraint.get, Seqn(Seq(s), Seq())(pos, info, errT), Seqn(Seq(), Seq())(pos, info, errT))(pos, info, errT)
    } else {
      s
    }
  }

  def splitBreathing(breath: Exp): Seq[(Exp, Option[Exp])] = splitBreathing(breath, None)

  def splitBreathing(breath: Exp, constraint: Option[Exp]): Seq[(Exp, Option[Exp])] = {
    def addConstraint(c: Exp) = if (constraint.isDefined) {
      Some(And(constraint.get, c)(breath.pos, breath.info))
    } else {
      Some(c)
    }

    breath match {
      case And(left, right) => splitBreathing(left, constraint) ++ splitBreathing(right, constraint)
      case Implies(left, right) => splitBreathing(right, addConstraint(left))
      case CondExp(cond, thn, els) => splitBreathing(thn, addConstraint(cond)) ++ splitBreathing(els, addConstraint(Not(cond)(breath.pos, breath.info)))
      case default => Seq((default, constraint))
    }
  }

  def generateAssumption(input: Program, accessPredicate: FieldAccessPredicate, normalized: NormalizedExpression)(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    // FieldAcces
    val fieldAccess = accessPredicate.loc
    val field = fieldAccess.field
    val fieldFunctionName = plugin.naming.getNameFor(field)
    val rcv = fieldAccess.rcv
    val arpFieldFunctionDomain = plugin.utils.getDomain(input, plugin.naming.fieldFunctionDomainName).get
    val arpFieldFunction = plugin.utils.getDomainFunction(arpFieldFunctionDomain, fieldFunctionName).get

    // ARPLog
    val arpLogDomain = plugin.utils.getDomain(input, plugin.naming.logDomainName).get
    val arpLogType = DomainType(arpLogDomain, Map[TypeVar, Type]() /* TODO: What's the deal with this? */)
    val arpLogSum = plugin.utils.getDomainFunction(arpLogDomain, plugin.naming.logDomainSum).get
    val arpLog = LocalVar(plugin.naming.logName)(arpLogType, accessPredicate.pos, accessPredicate.info)

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

  def generateAssumptionWorker(fieldAccess: FieldAccess, getSumCall: Int => DomainFuncApp, normalized: NormalizedExpression, assumption: Option[Exp])(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    def addAssumption(exp: Exp) = if (assumption.isDefined) Some(PermAdd(exp, assumption.get)(pos, info, errT)) else Some(exp)

    def recursive(n: NormalizedExpression = normalized, a: Option[Exp] = assumption) =
      generateAssumptionWorker(fieldAccess, getSumCall, n, a)(pos, info, errT)

    def recursiveNegative(n: NormalizedExpression = normalized, a: Option[Exp] = assumption) =
      generateAssumptionWorkerNegative(fieldAccess, getSumCall, n, a, foundPositive = false)(pos, info, errT)

    val currentPerm = CurrentPerm(fieldAccess)(pos, info, errT)
    if (normalized.wildcard.isDefined) {
      Seq(Inhale(PermLtCmp(normalized.wildcard.get.unit.get, currentPerm)(pos, info, errT))(pos, info, errT))
    } else {
      if (normalized.exps.isEmpty) {
        if (normalized.const.isEmpty) {
          // we are done, emit the gathered assumption
          if (assumption.isDefined) {
            Seq(Inhale(PermLtCmp(assumption.get, currentPerm)(pos, info, errT))(pos, info, errT))
          } else {
            Seq()
          }
        } else {
          // only const left to do
          val newNormalized = plugin.normalize.NormalizedExpression(Seq(), None, None)
          val const = normalized.const.get
          Seq(If(
            And(
              PermLtCmp(NoPerm()(pos, info, errT), const.exp)(pos, info, errT),
              PermLtCmp(const.exp, getSumCall(const.check))(pos, info, errT)
            )(pos, info, errT),

            Seqn(
              recursive(newNormalized, addAssumption(const.exp)),
              Seq()
            )(pos, info, errT),
            Seqn(
              recursive(newNormalized),
              Seq()
            )(pos, info, errT)
          )(pos, info, errT))
        }
      } else {
        // process normalized list
        val cur = normalized.exps.head
        val newNormalized = plugin.normalize.NormalizedExpression(normalized.exps.tail, normalized.const, None)
        val expGe0 = Seq(If(
          PermLtCmp(NoPerm()(pos, info, errT), getSumCall(cur.check))(pos, info, errT),
          // none < sum(check)
          Seqn(
            recursive(newNormalized, addAssumption(cur.getTotal(pos, info, errT))),
            Seq()
          )(pos, info, errT),
          // none >= sum(check)
          Seqn(
            recursive(newNormalized),
            Seq()
          )(pos, info, errT)
        )(pos, info, errT))
        val expLt0 = recursiveNegative(newNormalized, addAssumption(cur.getTotal(pos, info, errT)))
        cur.exp match {
          case IntLit(x) if x >= 0 => expGe0
          case IntLit(x) if x < 0 => expLt0
          case default =>
            Seq(If(
              PermLeCmp(IntLit(0)(pos, info, errT), default)(pos, info, errT),
              // 0 <= exp
              Seqn(
                expGe0,
                Seq()
              )(pos, info, errT),
              // 0 > exp
              Seqn(
                expLt0,
                Seq()
              )(pos, info, errT)
            )(pos, info, errT))
        }
      }
    }
  }

  def generateAssumptionWorkerNegative(fieldAccess: FieldAccess, getSumCall: Int => DomainFuncApp, normalized: NormalizedExpression, assumption: Option[Exp], foundPositive: Boolean)(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    def addAssumption(exp: Exp) = if (assumption.isDefined) Some(PermAdd(exp, assumption.get)(pos, info, errT)) else Some(exp)

    def recursive(n: NormalizedExpression = normalized, a: Option[Exp] = assumption, f: Boolean = foundPositive) =
      generateAssumptionWorkerNegative(fieldAccess, getSumCall, n, a, f)(pos, info, errT)

    if (normalized.const.isEmpty) {
      if (normalized.exps.isEmpty) {
        // we are done, emit the gathered assumption
        if (assumption.isDefined && foundPositive) {
          Seq(Inhale(PermLtCmp(NoPerm()(pos, info, errT), assumption.get)(pos, info, errT))(pos, info, errT))
        } else {
          Seq()
        }
      } else {
        // process normalized list
        val cur = normalized.exps.takeRight(1).head
        val newNormalized = plugin.normalize.NormalizedExpression(normalized.exps.dropRight(1), None, None)

        Seq(
          If(
            PermLtCmp(IntLit(0)(pos, info, errT), cur.getTotal(pos, info, errT))(pos, info, errT),
            // 0 < cur
            Seqn(
              recursive(newNormalized, addAssumption(cur.exp), f = true),
              Seq()
            )(pos, info, errT),
            // 0 >= cur
            Seqn(
              Seq(
                If(
                  EqCmp(IntLit(0)(pos, info, errT), cur.exp)(pos, info, errT),
                  // 0 == cur
                  Seqn(
                    recursive(newNormalized),
                    Seq()
                  )(pos, info, errT),
                  // 0 > cur
                  Seqn(
                    Seq(),
                    Seq()
                  )(pos, info, errT)
                )(pos, info, errT)
              ),
              Seq()
            )(pos, info, errT)
          )(pos, info, errT)
        )
      }
    } else {
      // start with const
      val newNormalized = plugin.normalize.NormalizedExpression(normalized.exps, None, None)
      val const = normalized.const.get
      Seq(If(
        PermLtCmp(NoPerm()(pos, info, errT), const.exp)(pos, info, errT),
        // none < q
        Seqn(
          recursive(newNormalized, addAssumption(const.exp), f = true),
          Seq()
        )(pos, info, errT),
        // none >= q
        Seqn(
          Seq(
            If(
              EqCmp(NoPerm()(pos, info, errT), const.exp)(pos, info, errT),
              // none == q
              Seqn(
                recursive(newNormalized),
                Seq()
              )(pos, info, errT),
              // none > q
              Seqn(
                Seq(),
                Seq()
              )(pos, info, errT)
            )(pos, info, errT)
          ),
          Seq()
        )(pos, info, errT)
      )(pos, info, errT))
    }
  }

  def generateLogUpdate(input: Program, fieldAccessPredicate: FieldAccessPredicate, normalized: NormalizedExpression, minus: Boolean, ctx: ContextC[Node, String])(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {

    // ARPLog
    val arpLogDomain = plugin.utils.getDomain(input, plugin.naming.logDomainName).get
    val arpLogType = DomainType(arpLogDomain, Map[TypeVar, Type]() /* TODO: What's the deal with this? */)
    val arpLog = LocalVar(plugin.naming.logName)(arpLogType, fieldAccessPredicate.pos, fieldAccessPredicate.info)
    val arpLogCons = plugin.utils.getDomainFunction(arpLogDomain, plugin.naming.logDomainCons).get

    // FieldAccess
    val fieldAccess = fieldAccessPredicate.loc
    val field = fieldAccess.field
    val fieldFunctionName = plugin.naming.getNameFor(field)
    val rcv = fieldAccess.rcv
    val arpFieldFunctionDomain = plugin.utils.getDomain(input, plugin.naming.fieldFunctionDomainName).get
    val arpFieldFunction = plugin.utils.getDomainFunction(arpFieldFunctionDomain, fieldFunctionName).get

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