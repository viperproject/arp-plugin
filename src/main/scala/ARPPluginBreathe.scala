/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast.utility.Rewriter.ContextC
import viper.silver.ast._
import viper.silver.plugin.ARPPlugin._

class ARPPluginBreathe(plugin: ARPPlugin) {

  private type NormalizedExpression = plugin.normalize.NormalizedExpression

  def handleInhale(input: Program, inhale: Inhale, ctx: ContextC[Node, ARPContext]): Node = {

    val wildcardNames = getWildcardNames(inhale.exp)
    var currentWildcardNames = wildcardNames

    def rdRewriter[T <: Node](exp: T) = plugin.utils.rewriteRd(ctx.c.rdName, wildcardNames)(exp)

    def nextWildcardName = if (currentWildcardNames.nonEmpty) {
      val head = currentWildcardNames.head
      currentWildcardNames = currentWildcardNames.tail
      head
    } else {
      plugin.naming.getNewName(suffix = "not_enough_names")
    }

    ctx.noRec(
      Seqn(
        Seq(Inhale(rdRewriter(inhale.exp))(inhale.pos, inhale.info, inhale.errT + NodeTrafo(inhale))) ++
          splitBreathing(inhale.exp).map({
            case (accessPredicate: FieldAccessPredicate, constraint) =>
              val normalized = plugin.normalize.normalizeExpression(accessPredicate.perm, getRdLevel(inhale))
              if (normalized.isDefined) {
                if (normalized.get.wildcard.isDefined) {
                  val wildcardName = nextWildcardName
                  Some(putInIf(
                    (generateAssumption(input, accessPredicate, normalized.get, ctx.c.logName, wildcardName = wildcardName)(inhale.pos, inhale.info, NodeTrafo(inhale)) ++
                      generateLogUpdate(
                        input, accessPredicate, normalized.get, minus = false, ctx
                      )(accessPredicate.pos, accessPredicate.info, NoTrafos))
                      .map(plugin.utils.rewriteRd(wildcardName, Seq(wildcardName))),
                    constraint
                  )(inhale.pos, inhale.info, NodeTrafo(inhale)))
                } else {
                  Some(putInIf(
                    generateAssumption(input, accessPredicate, normalized.get, ctx.c.logName, negativeOnly = true)(accessPredicate.pos, accessPredicate.info, NoTrafos).map(rdRewriter) ++
                      generateLogUpdate(input, accessPredicate, normalized.get, minus = false, ctx)(accessPredicate.pos, accessPredicate.info, NoTrafos).map(rdRewriter),
                    constraint
                  )(inhale.pos, inhale.info, NodeTrafo(inhale)))
                }
              } else {
                Some(Seq(Assert(BoolLit(b = false)())()))
              }
            case _ =>
              None
          }).filter(_.isDefined).flatMap(_.get),
        wildcardNames.map(n => LocalVarDecl(n, Perm)(inhale.pos, inhale.info))
      )(inhale.pos, inhale.info, NodeTrafo(inhale))
    )
  }

  def handleExhale(input: Program, exhale: Exhale, ctx: ContextC[Node, ARPContext]): Node = {
    val labelName = plugin.naming.getNewName(suffix = "exhale_label")

    val wildcardNames = getWildcardNames(exhale.exp)
    var currentWildcardNames = wildcardNames

    def rdRewriter[T <: Node](exp: T) = plugin.utils.rewriteRd(ctx.c.rdName, wildcardNames)(exp)

    def nextWildcardName = if (currentWildcardNames.nonEmpty) {
      val head = currentWildcardNames.head
      currentWildcardNames = currentWildcardNames.tail
      head
    } else {
      plugin.naming.getNewName(suffix = "not_enough_names")
    }

    def oldRewriter[T <: Node](exp: T) = plugin.utils.rewriteOldExpr(labelName, oldLabel = false)(exp)

    ctx.noRec(
      Seqn(
        Seq(Label(labelName, Seq())(exhale.pos, exhale.info)) ++
          splitBreathing(exhale.exp).map {
            case (accessPredicate: FieldAccessPredicate, constraint) =>
              val normalized = plugin.normalize.normalizeExpression(accessPredicate.perm, getRdLevel(exhale))
              if (normalized.isDefined) {
                if (normalized.get.wildcard.isDefined) {
                  val wildcardName = nextWildcardName
                  Seqn(putInIf(
                    (generateAssumption(input, accessPredicate, normalized.get, ctx.c.logName, wildcardName = wildcardName)(exhale.pos, exhale.info, NodeTrafo(exhale)) ++
                      generateLogUpdate(input, accessPredicate, normalized.get, minus = true, ctx)(exhale.pos, exhale.info, NodeTrafo(exhale)))
                      .map(plugin.utils.rewriteRd(wildcardName, Seq(wildcardName))) ++
                      Seq(Exhale(oldRewriter(plugin.utils.rewriteRd(wildcardName, Seq(wildcardName))(accessPredicate)))(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale))),
                    constraint
                  )(exhale.pos, exhale.info, NodeTrafo(exhale)),
                    Seq()
                  )(exhale.pos, exhale.info, NodeTrafo(exhale))
                } else {
                  Seqn(putInIf(
                    (if (plugin.Optimize.noAssumptionForPost && exhale.info.getUniqueInfo[WasMethodCondition].isDefined) {
                      Seq()
                    } else {
                      generateAssumption(input, accessPredicate, normalized.get, ctx.c.logName)(exhale.pos, exhale.info, NoTrafos).map(rdRewriter) ++
                        generateLogUpdate(
                          input, accessPredicate, normalized.get, minus = true, ctx
                        )(exhale.pos, exhale.info, NoTrafos)
                          .map(rdRewriter).map(oldRewriter)
                    }) ++
                      Seq(Exhale(oldRewriter(rdRewriter(accessPredicate)))(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale))),
                    constraint
                  )(exhale.pos, exhale.info, NoTrafos),
                    Seq()
                  )(exhale.pos, exhale.info)
                }
              } else {
                Assert(BoolLit(b = false)())()
              }
            case (default, constraint) =>
              putInIf(
                Exhale(oldRewriter(rdRewriter(default)))(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale)),
                constraint
              )(exhale.pos, exhale.info, NodeTrafo(exhale))
          },
        Seq(Label(labelName, Seq())(exhale.pos, exhale.info)) ++
          wildcardNames.map(n => LocalVarDecl(n, Perm)(exhale.pos, exhale.info))
      )(exhale.pos, exhale.info, NodeTrafo(exhale))
    )
  }

  def handleAssert(input: Program, assert: Assert, ctx: ContextC[Node, ARPContext]): Node = {
    val wildcardNames = getWildcardNames(assert.exp)
    var currentWildcardNames = wildcardNames

    def rdRewriter[T <: Node](exp: T) = plugin.utils.rewriteRd(ctx.c.rdName, wildcardNames)(exp)

    def nextWildcardName = if (currentWildcardNames.nonEmpty) {
      val head = currentWildcardNames.head
      currentWildcardNames = currentWildcardNames.tail
      head
    } else {
      plugin.naming.getNewName(suffix = "not_enough_names")
    }

    ctx.noRec(
      Seqn(
        splitBreathing(assert.exp).filter(_._1.isInstanceOf[FieldAccessPredicate]).map {
          case (accessPredicate: FieldAccessPredicate, constraint) =>
            val normalized = plugin.normalize.normalizeExpression(accessPredicate.perm, getRdLevel(assert))
            if (normalized.isDefined) {
              if (normalized.get.wildcard.isDefined) {
                val wildcardName = nextWildcardName
                Seqn(putInIf(
                  generateAssumption(input, accessPredicate, normalized.get, ctx.c.logName, wildcardName = wildcardName)(assert.pos, assert.info, NodeTrafo(assert))
                    .map(plugin.utils.rewriteRd(wildcardName, Seq(wildcardName))),
                  constraint
                )(assert.pos, assert.info, NodeTrafo(assert)),
                  Seq()
                )(assert.pos, assert.info, NodeTrafo(assert))
              } else {
                Seqn(putInIf(
                  generateAssumption(input, accessPredicate, normalized.get, ctx.c.logName)(assert.pos, assert.info, NoTrafos).map(rdRewriter),
                  constraint
                )(assert.pos, assert.info, NodeTrafo(assert)),
                  Seq()
                )(assert.pos, assert.info, NodeTrafo(assert))
              }
            } else {
              Assert(BoolLit(b = false)())()
            }
          case (_, _) => Assert(BoolLit(b = false)())()
        } ++
          Seq(
            Assert(
              plugin.utils.rewriteRd(ctx.c.rdName, wildcardNames)(
                plugin.utils.rewriteOldExpr(ctx.c.oldLabelName, fieldAccess = false)(
                  assert.exp
                )
              )
            )(assert.pos, assert.info, assert.errT + NodeTrafo(assert))
          ),
        wildcardNames.map(n => LocalVarDecl(n, Perm)(assert.pos, assert.info))
      )(assert.pos, assert.info)
    )
  }

  def handleFold(input: Program, fold: Fold, ctx: ContextC[Node, ARPContext]): Node = {
    ctx.noRec(handlePredicateFolding(input, fold, fold.acc, minus = false, ctx))
  }

  def handleUnfold(input: Program, unfold: Unfold, ctx: ContextC[Node, ARPContext]): Node = {
    ctx.noRec(handlePredicateFolding(input, unfold, unfold.acc, minus = true, ctx))
  }

  def handlePredicateFolding(input: Program, fold: Stmt, acc: PredicateAccessPredicate, minus: Boolean, ctx: ContextC[Node, ARPContext]): Node = {
    def newPerm(exp: Exp) = PermMul(acc.perm, exp)(exp.pos, exp.info)

    // TODO: handle arguments correctly

    acc.loc.predicateBody(input) match {
      case Some(body) =>
        Seqn(
          Seq(
            fold
          ) ++
          splitBreathing(body).map({
            case (accessPredicate: FieldAccessPredicate, constraint) =>
              val normalized = plugin.normalize.normalizeExpression(newPerm(accessPredicate.perm), plugin.normalize.rdPermContext)
              if (normalized.isDefined){
                Some(putInIf(
                  generateLogUpdate(input, accessPredicate, normalized.get, minus, ctx)(fold.pos, fold.info, NoTrafos),
                  constraint
                )(fold.pos, fold.info, NodeTrafo(fold)))
              } else {
                Some(Seq(Assert(BoolLit(b = false)())()))
              }
            case _ =>
              None
          }).filter(_.isDefined).flatMap(_.get),
          Seq()
        )(fold.pos, fold.info, NodeTrafo(fold))
      case None => fold
    }
  }

  def getWildcardNames(exp: Exp): Seq[String] = {
    splitBreathing(exp).map({
      case (accessPredicate: FieldAccessPredicate, _) =>
        val normalized = plugin.normalize.normalizeExpression(accessPredicate.perm, plugin.normalize.rdPermContext)
        if (normalized.isDefined && normalized.get.wildcard.isDefined) {
          Some(plugin.naming.getNewName(suffix = "wildcard"))
        } else {
          None
        }
      case _ => None
    }).filter(_.isDefined).map(_.get)
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

  private def getRdLevel(infoed: Infoed): (Exp, FuncApp) => plugin.normalize.NormalizedExpression = {
    if ((infoed.info.getUniqueInfo[WasCallCondition] ++ infoed.info.getUniqueInfo[WasInvariantOutside]).nonEmpty) {
      plugin.normalize.rdPermFresh
    } else {
      plugin.normalize.rdPermContext
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

  def generateAssumption(input: Program, accessPredicate: FieldAccessPredicate, normalized: NormalizedExpression, logName: String, negativeOnly: Boolean = false, wildcardName: String = "")(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    // FieldAcces
    val fieldAccess = accessPredicate.loc
    val field = fieldAccess.field
    val fieldFunctionName = plugin.naming.getNameFor(field, "field", field.name)
    val rcv = fieldAccess.rcv
    val arpFieldFunctionDomain = plugin.utils.getDomain(input, plugin.naming.fieldFunctionDomainName).get
    val arpFieldFunction = plugin.utils.getDomainFunction(arpFieldFunctionDomain, fieldFunctionName).get

    // ARPLog
    val arpLogDomain = plugin.utils.getDomain(input, plugin.naming.logDomainName).get
    val arpLogType = DomainType(arpLogDomain, Map[TypeVar, Type]() /* TODO: What's the deal with this? */)
    val arpLogSum = plugin.utils.getDomainFunction(arpLogDomain, plugin.naming.logDomainSum).get
    val arpLog = LocalVar(logName)(arpLogType, accessPredicate.pos, accessPredicate.info)

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

    if (normalized.wildcard.isDefined) {
      Seq(
        Inhale(
          And(
            PermLtCmp(
              NoPerm()(pos, info, errT),
              LocalVar(wildcardName)(Perm, pos, info, errT)
            )(pos, info, errT),
            Implies(
              And(
                PermLtCmp(NoPerm()(pos, info, errT), getSumCall(normalized.wildcard.get.check))(pos, info, errT),
                PermLtCmp(NoPerm()(pos, info, errT), CurrentPerm(accessPredicate.loc)(pos, info, errT))(pos, info, errT)
              )(pos, info, errT),
              PermLtCmp(
                LocalVar(wildcardName)(Perm, pos, info, errT),
                CurrentPerm(accessPredicate.loc)(pos, info, errT)
              )(pos, info, errT)
            )(pos, info, errT)
          )(pos, info, errT)
        )(pos, info, errT)
      )
    } else {
      if (normalized.exps.isEmpty) {
        Seq()
      } else {
        if (negativeOnly) {
          generateAssumptionWorkerNegative(fieldAccess, getSumCall, normalized, None, foundPositive = false)(pos, info, errT)
        } else {
          generateAssumptionWorker(fieldAccess, getSumCall, normalized, None, onlyPositive = false)(pos, info, errT)
        }
      }
    }
  }

  def generateAssumptionWorker(fieldAccess: FieldAccess, getSumCall: Int => DomainFuncApp, normalized: NormalizedExpression, assumption: Option[Exp], onlyPositive: Boolean)(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    def addAssumption(exp: Exp) = if (assumption.isDefined) Some(PermAdd(exp, assumption.get)(pos, info, errT)) else Some(exp)

    def recursive(n: NormalizedExpression = normalized, a: Option[Exp] = assumption, p: Boolean = onlyPositive) =
      generateAssumptionWorker(fieldAccess, getSumCall, n, a, p)(pos, info, errT)

    def recursiveNegative(n: NormalizedExpression = normalized, a: Option[Exp] = assumption) =
      generateAssumptionWorkerNegative(fieldAccess, getSumCall, n, a, foundPositive = false)(pos, info, errT)

    def generateIf(exp: Exp, ge0: Seq[Stmt], lt0: Seq[Stmt]): Seq[Stmt] = {
      plugin.utils.simplify(exp) match {
        case IntLit(x) if x >= 0 && plugin.Optimize.removeProvableIf => ge0
        case IntLit(x) if x < 0 && plugin.Optimize.removeProvableIf => lt0
        case PermDiv(IntLit(left), IntLit(right)) if right != 0 && plugin.Optimize.removeProvableIf =>
          if (left == 0 || ((left > 0) == (right > 0))) {
            ge0
          } else {
            lt0
          }
        case default =>
          Seq(If(
            PermLeCmp(plugin.utils.getZeroEquivalent(default), default)(pos, info, errT),
            // 0 <= exp
            Seqn(
              ge0,
              Seq()
            )(pos, info, errT),
            // 0 > exp
            Seqn(
              lt0,
              Seq()
            )(pos, info, errT)
          )(pos, info, errT))
      }
    }

    val currentPerm = CurrentPerm(fieldAccess)(pos, info, errT)
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
        if (assumption.isDefined) {
          generateIf(const.exp,
            Seq(If(
              PermLtCmp(const.exp, getSumCall(const.check))(pos, info, errT),
              Seqn(
                recursive(newNormalized, addAssumption(const.exp)),
                Seq()
              )(pos, info, errT),
              Seqn(
                recursive(newNormalized),
                Seq()
              )(pos, info, errT)
            )(pos, info, errT)),
            Seq())
        } else {
          Seq()
        }
      }
    } else {
      // process normalized list
      val cur = normalized.exps.head
      val newNormalized = plugin.normalize.NormalizedExpression(normalized.exps.tail, normalized.const, None)
      lazy val expGe0 = Seq(If(
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
      lazy val expLt0 = if (onlyPositive) {
        recursive(newNormalized)
      } else {
        recursiveNegative(newNormalized, addAssumption(cur.getTotal(pos, info, errT))) ++
          recursive(newNormalized, p = true)
      }
      generateIf(cur.exp, expGe0, expLt0)
    }
  }

  def generateAssumptionWorkerNegative(fieldAccess: FieldAccess, getSumCall: Int => DomainFuncApp, normalized: NormalizedExpression, assumption: Option[Exp], foundPositive: Boolean)(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    def addAssumption(exp: Exp) = if (assumption.isDefined) Some(PermAdd(exp, assumption.get)(pos, info, errT)) else Some(exp)

    def recursive(n: NormalizedExpression = normalized, a: Option[Exp] = assumption, f: Boolean = foundPositive) =
      generateAssumptionWorkerNegative(fieldAccess, getSumCall, n, a, f)(pos, info, errT)

    def generateIf(exp: Exp, gt0: Seq[Stmt], eq0: Seq[Stmt], lt0: Seq[Stmt]): Seq[Stmt] = {
      plugin.utils.simplify(exp) match {
        case IntLit(x) if x > 0 && plugin.Optimize.removeProvableIf => gt0
        case IntLit(x) if x == 0 && plugin.Optimize.removeProvableIf => eq0
        case IntLit(x) if x < 0 && plugin.Optimize.removeProvableIf => lt0
        case PermDiv(IntLit(left), IntLit(right)) if right != 0 && plugin.Optimize.removeProvableIf =>
          if (left == 0) {
            eq0
          } else if ((left > 0) == (right > 0)) {
            gt0
          } else {
            lt0
          }
        case default =>
          Seq(If(
            PermLtCmp(plugin.utils.getZeroEquivalent(default), default)(pos, info, errT),
            // 0 < cur
            Seqn(gt0, Seq())(pos, info, errT),
            // 0 >= cur
            Seqn(
              Seq(If(
                EqCmp(plugin.utils.getZeroEquivalent(default), default)(pos, info, errT),
                // 0 == cur
                Seqn(eq0, Seq())(pos, info, errT),
                // 0 > cur
                Seqn(lt0, Seq())(pos, info, errT)
              )(pos, info, errT)),
              Seq()
            )(pos, info, errT)
          )(pos, info, errT))
      }
    }

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

        lazy val expGt0 = if (foundPositive) {
          recursive(newNormalized)
        } else {
          recursive(newNormalized, addAssumption(cur.getTotal(pos, info, errT)), f = true)
        }
        lazy val expEq0 = recursive(newNormalized)
        lazy val expLt0 = if (foundPositive) {
          recursive(newNormalized, addAssumption(cur.getTotal(pos, info, errT)))
        } else {
          Seq()
        }
        generateIf(cur.exp, expGt0, expEq0, expLt0)
      }
    } else {
      // start with const
      val newNormalized = plugin.normalize.NormalizedExpression(normalized.exps, None, None)
      val const = normalized.const.get
      lazy val expGt0 = recursive(newNormalized, addAssumption(const.exp), f = true)
      lazy val expEq0 = recursive(newNormalized)
      lazy val expLt0 = Seq()
      generateIf(const.exp, expGt0, expEq0, expLt0)
    }
  }

  def generateLogUpdate(input: Program, fieldAccessPredicate: FieldAccessPredicate, normalized: NormalizedExpression, minus: Boolean, ctx: ContextC[Node, ARPContext])(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {

    // ARPLog
    val arpLogDomain = plugin.utils.getDomain(input, plugin.naming.logDomainName).get
    val arpLogType = DomainType(arpLogDomain, Map[TypeVar, Type]() /* TODO: What's the deal with this? */)
    val arpLog = LocalVar(ctx.c.logName)(arpLogType, fieldAccessPredicate.pos, fieldAccessPredicate.info)
    val arpLogCons = plugin.utils.getDomainFunction(arpLogDomain, plugin.naming.logDomainCons).get

    // FieldAccess
    val fieldAccess = fieldAccessPredicate.loc
    val field = fieldAccess.field
    val fieldFunctionName = plugin.naming.getNameFor(field, "field", field.name)
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