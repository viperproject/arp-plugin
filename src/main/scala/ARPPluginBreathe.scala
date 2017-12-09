/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast.utility.Rewriter.{ContextC, StrategyBuilder}
import viper.silver.ast._
import viper.silver.plugin.ARPPlugin._
import viper.silver.verifier.AbstractVerificationError
import viper.silver.verifier.errors.{AssertFailed, Internal}
import viper.silver.verifier.reasons.{AssertionFalse, FeatureUnsupported}

class ARPPluginBreathe(plugin: ARPPlugin) {

  private type NormalizedExpression = plugin.normalize.NormalizedExpression

  def handleInhale(input: Program, inhale: Inhale, ctx: ContextC[Node, ARPContext]): Node = {
    val labelName = plugin.naming.getNewName(suffix = "inhale_label")

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
        Seq(Label(labelName, Seq())(inhale.pos, inhale.info)) ++
          Seq(Inhale(rdRewriter(inhale.exp))(inhale.pos, inhale.info, inhale.errT + NodeTrafo(inhale))) ++
          splitBreathing(inhale.exp, Some(true), {
            case f@FieldAccessPredicate(floc, CurrentPerm(loc)) if !plugin.isFieldIgnored(floc.field) =>
              generateLogUpdateCurrentPerm(input, floc, loc, minus = false, ctx)(f.pos, f.info, NodeTrafo(f))
            case p@PredicateAccessPredicate(ploc, CurrentPerm(loc)) if !plugin.isPredicateIgnored(ploc.predicateName) =>
              generateLogUpdateCurrentPerm(input, ploc, loc, minus = false, ctx)(p.pos, p.info, NodeTrafo(p))
            case accessPredicate: AccessPredicate if !plugin.isAccIgnored(accessPredicate.loc) =>
              val normalized = plugin.normalize.normalizeExpression(accessPredicate.perm, getRdLevel(inhale))
              if (normalized.isDefined) {
                if (normalized.get.wildcard.isDefined) {
                  val wildcardName = nextWildcardName
                  (generateAssumptionInhale(input, accessPredicate.loc, normalized.get, ctx.c.logName, wildcardName = wildcardName)(accessPredicate.pos, accessPredicate.info, NodeTrafo(accessPredicate)) ++
                    generateLogUpdate(
                      input, accessPredicate.loc, normalized.get, minus = false, ctx
                    )(accessPredicate.pos, accessPredicate.info, NoTrafos))
                    .map(plugin.utils.rewriteRd(wildcardName, Seq(wildcardName)))
                } else {
                  generateAssumptionInhale(input, accessPredicate.loc, normalized.get, ctx.c.logName, negativeOnly = true)(accessPredicate.pos, accessPredicate.info, NoTrafos).map(rdRewriter) ++
                    generateLogUpdate(input, accessPredicate.loc, normalized.get, minus = false, ctx)(accessPredicate.pos, accessPredicate.info, NoTrafos).map(rdRewriter)
                }
              } else {
                Seq(Assert(BoolLit(b = false)())())
              }
            case _ => Seq()
          }),
        Seq(Label(labelName, Seq())(inhale.pos, inhale.info)) ++
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
          splitBreathing(exhale.exp, Some(false), {
            case f@FieldAccessPredicate(floc, CurrentPerm(loc)) if !plugin.isFieldIgnored(floc.field) =>
              generateLogUpdateCurrentPerm(input, floc, loc, minus = true, ctx)(f.pos, f.info, NodeTrafo(f)) ++
                Seq(Exhale(oldRewriter(rdRewriter(f)))(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale)))
            case p@PredicateAccessPredicate(ploc, CurrentPerm(loc)) if !plugin.isPredicateIgnored(ploc.predicateName) =>
              generateLogUpdateCurrentPerm(input, ploc, loc, minus = true, ctx)(p.pos, p.info, NodeTrafo(p)) ++
                Seq(Exhale(oldRewriter(rdRewriter(p)))(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale)))
            case accessPredicate: AccessPredicate if !plugin.isAccIgnored(accessPredicate.loc) =>
              val normalized = plugin.normalize.normalizeExpression(accessPredicate.perm, getRdLevel(exhale))
              if (normalized.isDefined) {
                if (normalized.get.wildcard.isDefined) {
                  val wildcardName = nextWildcardName
                  (generateAssumptionInhale(input, accessPredicate.loc, normalized.get, ctx.c.logName, wildcardName = wildcardName)(exhale.pos, exhale.info, NodeTrafo(exhale)) ++
                    generateLogUpdate(input, accessPredicate.loc, normalized.get, minus = true, ctx)(exhale.pos, exhale.info, NodeTrafo(exhale)))
                    .map(plugin.utils.rewriteRd(wildcardName, Seq(wildcardName))) ++
                    Seq(Exhale(oldRewriter(plugin.utils.rewriteRd(wildcardName, Seq(wildcardName))(accessPredicate)))(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale)))
                } else {
                  (if (plugin.Optimize.noAssumptionForPost && exhale.info.getUniqueInfo[WasMethodCondition].isDefined) {
                    Seq()
                  } else {
                    generateAssumptionInhale(input, accessPredicate.loc, normalized.get, ctx.c.logName)(exhale.pos, exhale.info, NoTrafos).map(rdRewriter) ++
                      generateLogUpdate(
                        input, accessPredicate.loc, normalized.get, minus = true, ctx
                      )(exhale.pos, exhale.info, NoTrafos)
                        .map(rdRewriter).map(oldRewriter)
                  }) ++
                    Seq(Exhale(oldRewriter(rdRewriter(accessPredicate)))(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale)))
                }
              } else {
                Seq(Assert(BoolLit(b = false)())())
              }
            case default =>
              Seq(Exhale(oldRewriter(rdRewriter(default)))(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale)))
          }),
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
        splitBreathing(assert.exp, Some(false), {
          case accessPredicate: AccessPredicate if !plugin.isAccIgnored(accessPredicate.loc) =>
            val normalized = plugin.normalize.normalizeExpression(accessPredicate.perm, getRdLevel(assert), ignoreErrors = true)
            if (normalized.isDefined) {
              if (normalized.get.wildcard.isDefined) {
                val wildcardName = nextWildcardName
                generateAssumptionInhale(input, accessPredicate.loc, normalized.get, ctx.c.logName, wildcardName = wildcardName)(assert.pos, assert.info, NodeTrafo(assert))
                  .map(plugin.utils.rewriteRd(wildcardName, Seq(wildcardName)))
              } else {
                generateAssumptionInhale(input, accessPredicate.loc, normalized.get, ctx.c.logName)(assert.pos, assert.info, NoTrafos).map(rdRewriter)
              }
            } else {
              Seq()
            }
          case _ => Seq()
        }) ++
          Seq(
            Assert(
              plugin.utils.rewriteRd(ctx.c.rdName, wildcardNames)(assert.exp)
            )(assert.pos, assert.info, assert.errT + NodeTrafo(assert))
          ),
        wildcardNames.map(n => LocalVarDecl(n, Perm)(assert.pos, assert.info))
      )(assert.pos, assert.info)
    )
  }

  def handleFold(input: Program, fold: Fold, ctx: ContextC[Node, ARPContext]): Node = {
    ctx.noRec(handlePredicateFolding(input, fold, fold.acc, foldBefore = false, minus = true, ctx))
  }

  def handleUnfold(input: Program, unfold: Unfold, ctx: ContextC[Node, ARPContext]): Node = {
    ctx.noRec(handlePredicateFolding(input, unfold, unfold.acc, foldBefore = true, minus = false, ctx))
  }

  def handlePredicateFolding(input: Program, fold: Stmt, acc: PredicateAccessPredicate, foldBefore: Boolean, minus: Boolean, ctx: ContextC[Node, ARPContext]): Node = {
    val wildcardNames = getWildcardNames(acc)

    def newPerm(exp: Exp) = plugin.utils.simplify(PermMul(acc.perm, exp)(exp.pos, exp.info))

    acc.loc.predicateBody(input) match {
      case Some(body) =>
        val wildcardNamesAll = wildcardNames ++ getWildcardNames(body)
        Seqn(
          (if (foldBefore) {
            Seq(
              fold
            )
          } else {
            Seq()
          }) ++
            splitBreathing(body, None, {
              case accessPredicate: AccessPredicate if !plugin.isAccIgnored(accessPredicate.loc) =>
                val normalized = plugin.normalize.normalizeExpression(newPerm(accessPredicate.perm), plugin.normalize.rdPermContext)
                if (normalized.isDefined) {
                  generateLogUpdate(input, accessPredicate.loc, normalized.get, minus, ctx)(fold.pos, fold.info, NoTrafos)
                    .map(plugin.utils.rewriteRd(ctx.c.rdName, wildcardNamesAll))
                } else {
                  Seq(Assert(BoolLit(b = false)())())
                }
              case _ =>
                Seq()
            }) ++
            (if (!foldBefore) {
              Seq(
                fold
              )
            } else {
              Seq()
            }),
          wildcardNamesAll.map(n => LocalVarDecl(n, Perm)(fold.pos, fold.info))
        )(fold.pos, fold.info, NodeTrafo(fold))
      case None => fold
    }
  }

  def getWildcardNames(exp: Exp): Seq[String] = {
    var wildcardNames = Seq[String]()
    StrategyBuilder.SlimVisitor[Node]({
      case accessPredicate: AccessPredicate =>
        val normalized = plugin.normalize.normalizeExpression(accessPredicate.perm, plugin.normalize.rdPermContext, ignoreErrors = true)
        if (normalized.isDefined && normalized.get.wildcard.isDefined) {
          wildcardNames :+= plugin.naming.getNewName(suffix = "wildcard")
        }
      case _ =>
    }).visit(exp)
    wildcardNames
  }

  private def getRdLevel(infoed: Infoed): (Exp, FuncApp) => plugin.normalize.NormalizedExpression = {
    if ((infoed.info.getUniqueInfo[WasCallCondition] ++ infoed.info.getUniqueInfo[WasInvariantOutside]).nonEmpty) {
      plugin.normalize.rdPermFresh
    } else {
      plugin.normalize.rdPermContext
    }
  }

  def splitBreathing(breath: Exp, isInhale: Option[Boolean], handle: Exp => Seq[Stmt]): Seq[Stmt] = {
    def recursive(b: Exp) = splitBreathing(b, isInhale, handle)

    breath match {
      case And(left, right) => recursive(left) ++ recursive(right)
      case Implies(left, right) =>
        val rightRec = recursive(right)
        if (rightRec.nonEmpty) {
          Seq(If(left,
            Seqn(rightRec, Seq())(right.pos, right.info, NodeTrafo(right)),
            Seqn(Seq(), Seq())(breath.pos, breath.info)
          )(breath.pos, breath.info, NodeTrafo(breath)))
        } else {
          Seq()
        }
      case CondExp(cond, thn, els) =>
        val thnRec = recursive(thn)
        val elsRec = recursive(els)
        if (thnRec.nonEmpty || elsRec.nonEmpty) {
          Seq(If(cond,
            Seqn(thnRec, Seq())(thn.pos, thn.info, NodeTrafo(thn)),
            Seqn(elsRec, Seq())(els.pos, els.info, NodeTrafo(els))
          )(breath.pos, breath.info, NodeTrafo(breath)))
        } else {
          Seq()
        }
      case InhaleExhaleExp(in, ex) if isInhale.isDefined => if (isInhale.get) recursive(in) else recursive(ex)
      case _: InhaleExhaleExp => Seq(Assert(BoolLit(b = false)(breath.pos, breath.info))(breath.pos, breath.info))
      case fa@FieldAccessPredicate(loc, perm) => splitAccessPredicate(perm, recursive, handle, fa, FieldAccessPredicate(loc, _)(fa.pos, fa.info, NodeTrafo(fa)))
      case pa@PredicateAccessPredicate(loc, perm) => splitAccessPredicate(perm, recursive, handle, pa, PredicateAccessPredicate(loc, _)(pa.pos, pa.info, NodeTrafo(pa)))
      case default => handle(default)
    }
  }

  def splitAccessPredicate(perm: Exp, recursiveCall: Exp => Seq[Stmt], handle: Exp => Seq[Stmt], orig: AccessPredicate, wrapper: Exp => Exp): Seq[Stmt] = {
    // TODO: arbitrary conditionals in acc (e.g. (a ? b : c) + (d ? e : f)

    perm match {
      case CondExp(cond, thn, els) => recursiveCall(CondExp(cond, wrapper(thn), wrapper(els))(perm.pos, perm.info, NodeTrafo(perm)))
      case _ => handle(orig)
    }
  }

  def generateAssumptionInhale(input: Program, acc: LocationAccess,  normalized: NormalizedExpression, logName: String, negativeOnly: Boolean = false, wildcardName: String = "")(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    generateAssumption(input, acc, normalized, logName, negativeOnly, wildcardName)(pos, info, errT).map(Inhale(_)(pos, info, errT)).toSeq
  }

  def generateAssumption(input: Program, acc: LocationAccess, normalized: NormalizedExpression, logName: String, negativeOnly: Boolean = false, wildcardName: String = "")(pos: Position, info: Info, errT: ErrorTrafo): Option[Exp] = {
    val arpFieldFunction = plugin.utils.getAccessDomainFuncApp(input, acc)(pos, info, errT)
    val rcv = plugin.utils.getAccessRcv(acc)(pos, info, errT)

    // ARPLog
    val arpLogDomain = plugin.utils.getDomain(input, plugin.naming.logDomainName).get
    val arpLogType = DomainType(arpLogDomain, Map[TypeVar, Type]())
    val arpLogSum = plugin.utils.getDomainFunction(arpLogDomain, plugin.naming.logDomainSumGt).get
    val arpLog = LocalVar(logName)(arpLogType, acc.pos, acc.info)

    def getSumCall(level: Int): DomainFuncApp = DomainFuncApp(
      arpLogSum,
      Seq(
        rcv,
        arpFieldFunction,
        IntLit(level)(pos, info, errT),
        arpLog
      ),
      Map[TypeVar, Type]()
    )(pos, info, errT)

    if (normalized.wildcard.isDefined) {
      Some(
        And(
          PermLtCmp(
            NoPerm()(pos, info, errT),
            LocalVar(wildcardName)(Perm, pos, info, errT)
          )(pos, info, errT),
          Implies(
            And(
              PermLtCmp(NoPerm()(pos, info, errT), getSumCall(normalized.wildcard.get.check))(pos, info, errT),
              PermLtCmp(NoPerm()(pos, info, errT), CurrentPerm(acc)(pos, info, errT))(pos, info, errT)
            )(pos, info, errT),
            PermLtCmp(
              LocalVar(wildcardName)(Perm, pos, info, errT),
              CurrentPerm(acc)(pos, info, errT)
            )(pos, info, errT)
          )(pos, info, errT)
        )(pos, info, errT)
      )
    } else {
      if (normalized.exps.isEmpty) {
        None
      } else {
        if (negativeOnly) {
          generateAssumptionWorkerNegative(acc, getSumCall, normalized, None, foundPositive = false)(pos, info, errT)
        } else {
          generateAssumptionWorker(acc, getSumCall, normalized, None, onlyPositive = false)(pos, info, errT)
        }
      }
    }
  }

  def putInCond(cond: Exp, thn: Option[Exp], els: Option[Exp])(pos: Position, info: Info, errT: ErrorTrafo): Option[Exp] = {
    if ((thn ++ els).nonEmpty) {
      if (els.isEmpty) {
        Some(Implies(cond, thn.get)(pos, info, errT))
      } else if (thn.isEmpty) {
        Some(Implies(Not(cond)(pos, info, errT), els.get)(pos, info, errT))
      } else {
        Some(CondExp(cond, thn.get, els.get)(pos, info, errT))
      }
    } else {
      None
    }
  }

  def combineAssumptions(a: Option[Exp], b: Option[Exp])(pos: Position, info: Info, errT: ErrorTrafo): Option[Exp] = {
    if ((a ++ b).nonEmpty) {
      if (a.isEmpty) {
        b
      } else if (b.isEmpty) {
        a
      } else {
        Some(And(a.get, b.get)(pos, info, errT))
      }
    } else {
      None
    }
  }

  def generateAssumptionWorker(fieldAccess: LocationAccess, getSumCall: Int => DomainFuncApp, normalized: NormalizedExpression, assumption: Option[Exp], onlyPositive: Boolean)(pos: Position, info: Info, errT: ErrorTrafo): Option[Exp] = {
    def addAssumption(exp: Exp) = if (assumption.isDefined) Some(PermAdd(exp, assumption.get)(pos, info, errT)) else Some(exp)

    def recursive(n: NormalizedExpression = normalized, a: Option[Exp] = assumption, p: Boolean = onlyPositive) =
      generateAssumptionWorker(fieldAccess, getSumCall, n, a, p)(pos, info, errT)

    def recursiveNegative(n: NormalizedExpression = normalized, a: Option[Exp] = assumption) =
      generateAssumptionWorkerNegative(fieldAccess, getSumCall, n, a, foundPositive = false)(pos, info, errT)

    def generateCond(exp: Exp, ge0: Option[Exp], lt0: Option[Exp]): Option[Exp] = {
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
          putInCond(PermLeCmp(plugin.utils.getZeroEquivalent(default), default)(pos, info, errT), ge0, lt0)(pos, info, errT)
      }
    }

    val currentPerm = CurrentPerm(fieldAccess)(pos, info, errT)
    if (normalized.exps.isEmpty) {
      if (normalized.const.isEmpty) {
        // we are done, emit the gathered assumption
        if (assumption.isDefined) {
          Some(PermLtCmp(assumption.get, currentPerm)(pos, info, errT))
        } else {
          None
        }
      } else {
        // only const left to do
        val newNormalized = plugin.normalize.NormalizedExpression(Seq(), None, None)
        val const = normalized.const.get
        if (assumption.isDefined) {
          generateCond(const.exp,
            putInCond(
              PermLtCmp(const.exp, getSumCall(const.check))(pos, info, errT),
              recursive(newNormalized, addAssumption(const.exp)),
              recursive(newNormalized)
            )(pos, info, errT),
            None)
        } else {
          None
        }
      }
    } else {
      // process normalized list
      val cur = normalized.exps.head
      val newNormalized = plugin.normalize.NormalizedExpression(normalized.exps.tail, normalized.const, None)
      lazy val expGe0 = putInCond(
        PermLtCmp(NoPerm()(pos, info, errT), getSumCall(cur.check))(pos, info, errT),
        recursive(newNormalized, addAssumption(cur.getTotal(pos, info, errT))),
        recursive(newNormalized)
      )(pos, info, errT)
      lazy val expLt0 = if (onlyPositive) {
        recursive(newNormalized)
      } else {
        combineAssumptions(recursiveNegative(newNormalized, addAssumption(cur.getTotal(pos, info, errT))),
          recursive(newNormalized, p = true))(pos, info, errT)
      }
      generateCond(cur.exp, expGe0, expLt0)
    }
  }

  def generateAssumptionWorkerNegative(fieldAccess: LocationAccess, getSumCall: Int => DomainFuncApp, normalized: NormalizedExpression, assumption: Option[Exp], foundPositive: Boolean)(pos: Position, info: Info, errT: ErrorTrafo): Option[Exp] = {
    def addAssumption(exp: Exp) = if (assumption.isDefined) Some(PermAdd(exp, assumption.get)(pos, info, errT)) else Some(exp)

    def recursive(n: NormalizedExpression = normalized, a: Option[Exp] = assumption, f: Boolean = foundPositive) =
      generateAssumptionWorkerNegative(fieldAccess, getSumCall, n, a, f)(pos, info, errT)

    def generateCond(exp: Exp, gt0: Option[Exp], eq0: Option[Exp], lt0: Option[Exp]): Option[Exp] = {
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
        case NoPerm() if plugin.Optimize.removeProvableIf => eq0
        case FullPerm() if plugin.Optimize.removeProvableIf => gt0
        case default =>
          putInCond(
            PermLtCmp(plugin.utils.getZeroEquivalent(default), default)(pos, info, errT),
            gt0,
            putInCond(
              EqCmp(plugin.utils.getZeroEquivalent(default), default)(pos, info, errT),
              eq0,
              lt0
            )(pos, info, errT)
          )(pos, info, errT)
      }
    }

    if (normalized.const.isEmpty) {
      if (normalized.exps.isEmpty) {
        // we are done, emit the gathered assumption
        if (assumption.isDefined && foundPositive) {
          Some(PermLtCmp(NoPerm()(pos, info, errT), assumption.get)(pos, info, errT))
        } else {
          None
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
          None
        }
        generateCond(cur.exp, expGt0, expEq0, expLt0)
      }
    } else {
      // start with const
      val newNormalized = plugin.normalize.NormalizedExpression(normalized.exps, None, None)
      val const = normalized.const.get
      lazy val expGt0 = recursive(newNormalized, addAssumption(const.exp), f = true)
      lazy val expEq0 = recursive(newNormalized)
      lazy val expLt0 = None
      generateCond(const.exp, expGt0, expEq0, expLt0)
    }
  }

  def generateLogUpdateCurrentPerm(input: Program, accAccess: LocationAccess, permAccess: LocationAccess, minus: Boolean, ctx: ContextC[Node, ARPContext])(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    // ARPLog
    val arpLogDomain = plugin.utils.getDomain(input, plugin.naming.logDomainName).get
    val arpLogType = DomainType(arpLogDomain, Map[TypeVar, Type]())
    val arpLog = LocalVar(ctx.c.logName)(arpLogType, pos, info)
    val arpLogSum = plugin.utils.getDomainFunction(arpLogDomain, plugin.naming.logDomainSum).get
    val arpLogMaxLevel = plugin.utils.getDomainFunction(arpLogDomain, plugin.naming.logDomainMaxLevel).get
    val tmpLogName = plugin.naming.getNewName(suffix = "tmpLog")
    val tmpLog = LocalVar(tmpLogName)(arpLogType, pos, info)
    val quantifiedRefName = plugin.naming.getNewName(suffix = "quantRef")
    val quantifiedRef = LocalVar(quantifiedRefName)(Ref, pos, info)
    val quantifiedIntName = plugin.naming.getNewName(suffix = "quantInt")
    val quantifiedInt = LocalVar(quantifiedIntName)(Int, pos, info)

    val arpFieldFunctionAcc = plugin.utils.getAccessDomainFuncApp(input, accAccess)(pos, info, errT)
    val arpFieldFunctionPerm = plugin.utils.getAccessDomainFuncApp(input, permAccess)(pos, info, errT)
    val accRcv = plugin.utils.getAccessRcv(accAccess)(pos, info, errT)
    val permRcv = plugin.utils.getAccessRcv(permAccess)(pos, info, errT)

    val add = if (minus) (a: Exp, b: Exp) => PermSub(a, b)(pos, info) else (a: Exp, b: Exp) => PermAdd(a, b)(pos, info)

    Seq(
      Seqn(
        Seq(
          LocalVarAssign(tmpLog, arpLog)(pos, info, errT),
          plugin.utils.havoc(arpLog),
          Inhale(Forall(
            Seq(LocalVarDecl(quantifiedRefName, Ref)(pos, info), LocalVarDecl(quantifiedIntName, Int)(pos, info)),
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
                  EqCmp(
                    quantifiedRef,
                    accRcv
                  )(pos, info),
                  add(
                    DomainFuncApp(arpLogSum, Seq(quantifiedRef, arpFieldFunctionAcc, quantifiedInt, tmpLog), Map[TypeVar, Type]())(pos, info),
                    DomainFuncApp(arpLogSum, Seq(permRcv, arpFieldFunctionPerm, quantifiedInt, tmpLog), Map[TypeVar, Type]())(pos, info)
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

  def generateLogUpdate(input: Program, acc: LocationAccess, normalized: NormalizedExpression, minus: Boolean, ctx: ContextC[Node, ARPContext])(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {

    // ARPLog
    val arpLogDomain = plugin.utils.getDomain(input, plugin.naming.logDomainName).get
    val arpLogType = DomainType(arpLogDomain, Map[TypeVar, Type]())
    val arpLog = LocalVar(ctx.c.logName)(arpLogType, pos, info)
    val arpLogCons = plugin.utils.getDomainFunction(arpLogDomain, plugin.naming.logDomainCons).get

    val rcv = plugin.utils.getAccessRcv(acc)(pos, info, errT)
    val arpFieldFunction = plugin.utils.getAccessDomainFuncApp(input, acc)(pos, info, errT)

    def getConsCall(level: Int, permission: Exp): LocalVarAssign = {
      LocalVarAssign(
        arpLog,
        DomainFuncApp(
          arpLogCons, Seq(
            rcv,
            arpFieldFunction,
            plugin.utils.simplify(if (minus) Minus(permission)(pos, info, errT) else permission),
            IntLit(level)(pos, info, errT),
            arpLog
          ),
          Map[TypeVar, Type]()
        )(pos, info, errT)
      )(pos, info, errT)
    }

    var logSeq = Seq[Stmt]()
    (normalized.const ++ normalized.wildcard ++ normalized.exps).foreach(e => logSeq :+= getConsCall(e.store, e.getTotal(pos, info, errT)))
    logSeq
  }

}