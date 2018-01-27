/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.{ContextC, StrategyBuilder}
import viper.silver.plugin.ARPPlugin._
import viper.silver.plugin.ARPPluginNormalize.NormalizedExpression

class ARPPluginBreathe(plugin: ARPPlugin) {

  def handleInhale(input: Program, inhale: Inhale, ctx: ContextC[Node, ARPContext]): Node = {
    val wildcardNames = getWildcardNames(inhale.exp)
    var currentWildcardNames = wildcardNames

    def rdRewriter[T <: Node](exp: T) = plugin.utils.rewriteRd(ctx.c.rdName, wildcardNames)(exp)

    def nextWildcardName() = if (currentWildcardNames.nonEmpty) {
      val head = currentWildcardNames.head
      currentWildcardNames = currentWildcardNames.tail
      head
    } else {
      plugin.naming.getNewName(suffix = "not_enough_names")
    }

    ctx.noRec(
      Seqn(
        splitBreathing(inhale.exp, complete = false, Some(true), exp => {
          val inSeq = Seq(Inhale(rdRewriter(exp))(inhale.pos, inhale.info, inhale.errT + NodeTrafo(inhale)))
          inSeq ++
            splitBreathing(exp, complete = true, Some(true), {
              case f@FieldAccessPredicate(floc, CurrentPerm(loc)) if !plugin.isFieldIgnored(floc.field) =>
                plugin.quantified.generateLogUpdateCurrentPerm(input, floc, loc, e => e, minus = false, ctx)(f.pos, f.info, NodeTrafo(f))
              case p@PredicateAccessPredicate(ploc, CurrentPerm(loc)) if !plugin.isPredicateIgnored(ploc.predicateName) =>
                plugin.quantified.generateLogUpdateCurrentPerm(input, ploc, loc, e => e, minus = false, ctx)(p.pos, p.info, NodeTrafo(p))
              case f@FieldAccessPredicate(floc, PermSub(FullPerm(), CurrentPerm(loc))) if !plugin.isFieldIgnored(floc.field) =>
                plugin.quantified.generateLogUpdateCurrentPerm(input, floc, loc, e => PermSub(FullPerm()(f.pos, f.info), e)(f.pos, f.info), minus = false, ctx)(f.pos, f.info, NodeTrafo(f))
              case p@PredicateAccessPredicate(ploc, PermSub(FullPerm(), CurrentPerm(loc))) if !plugin.isPredicateIgnored(ploc.predicateName) =>
                plugin.quantified.generateLogUpdateCurrentPerm(input, ploc, loc, e => PermSub(FullPerm()(p.pos, p.info), e)(p.pos, p.info), minus = false, ctx)(p.pos, p.info, NodeTrafo(p))
              case accessPredicate: AccessPredicate if !plugin.isAccIgnored(accessPredicate.loc) =>
                assumeAndLog(input, isInhale = true, accessPredicate, getRdLevel(inhale), rdRewriter, "", nextWildcardName, ctx)
              case f: Forall =>
                plugin.quantified.handleForallBreathe(input, isInhale = true, f, rdRewriter, "", getRdLevel(inhale), nextWildcardName, ctx)
              case _ => Seq()
            })
        }),
        wildcardNames.map(n => LocalVarDecl(n, Perm)(inhale.pos, inhale.info))
      )(inhale.pos, inhale.info, NodeTrafo(inhale))
    )
  }

  def handleExhale(input: Program, exhale: Exhale, ctx: ContextC[Node, ARPContext]): Node = {
    val labelName = plugin.naming.getNewName(suffix = "exhale_label")

    val wildcardNames = getWildcardNames(exhale.exp)
    var currentWildcardNames = wildcardNames
    var lastWildcardName = "NOT_YET_INITIALIZED"

    def rdRewriter[T <: Node](exp: T) = plugin.utils.rewriteRd(ctx.c.rdName, wildcardNames)(exp)

    def nextWildcardName() = if (currentWildcardNames.nonEmpty) {
      val head = currentWildcardNames.head
      currentWildcardNames = currentWildcardNames.tail
      lastWildcardName = head
      head
    } else {
      plugin.naming.getNewName(suffix = "not_enough_names")
    }

    def oldRewriter[T <: Node](exp: T) = plugin.utils.rewriteOldExpr(input, labelName, oldLabel = false)(exp)

    ctx.noRec(
      Seqn(
        Seq(Label(labelName, Seq())(exhale.pos, exhale.info)) ++
          splitBreathing(exhale.exp, complete = false, Some(false), exp => {
            val exSeq = Seq(Exhale(oldRewriter(rdRewriter(exp)))(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale)))
            splitBreathing(exp, complete = true, Some(false), {
              case f@FieldAccessPredicate(floc, CurrentPerm(loc)) if !plugin.isFieldIgnored(floc.field) =>
                plugin.quantified.generateLogUpdateCurrentPerm(input, floc, loc, e => e, minus = true, ctx)(f.pos, f.info, NodeTrafo(f))
              case p@PredicateAccessPredicate(ploc, CurrentPerm(loc)) if !plugin.isPredicateIgnored(ploc.predicateName) =>
                plugin.quantified.generateLogUpdateCurrentPerm(input, ploc, loc, e => e, minus = true, ctx)(p.pos, p.info, NodeTrafo(p))
              case f@FieldAccessPredicate(floc, PermSub(FullPerm(), CurrentPerm(loc))) if !plugin.isFieldIgnored(floc.field) =>
                plugin.quantified.generateLogUpdateCurrentPerm(input, floc, loc, e => PermSub(FullPerm()(f.pos, f.info), e)(f.pos, f.info), minus = false, ctx)(f.pos, f.info, NodeTrafo(f))
              case p@PredicateAccessPredicate(ploc, PermSub(FullPerm(), CurrentPerm(loc))) if !plugin.isPredicateIgnored(ploc.predicateName) =>
                plugin.quantified.generateLogUpdateCurrentPerm(input, ploc, loc, e => PermSub(FullPerm()(p.pos, p.info), e)(p.pos, p.info), minus = false, ctx)(p.pos, p.info, NodeTrafo(p))
              case accessPredicate: AccessPredicate if !plugin.isAccIgnored(accessPredicate.loc) =>
                val normalized = plugin.normalize.normalizeExpression(accessPredicate.perm, plugin.normalize.rdPermContext)
                if (plugin.Optimize.noAssumptionForPost && exhale.info.getUniqueInfo[WasMethodCondition].isDefined && !(normalized.isDefined && normalized.get.wildcard.isDefined)) {
                  Seq()
                } else {
                  assumeAndLog(input, isInhale = false, accessPredicate, getRdLevel(exhale), rdRewriter, labelName, nextWildcardName, ctx)
                }
              case f: Forall =>
                if (plugin.Optimize.noAssumptionForPost && exhale.info.getUniqueInfo[WasMethodCondition].isDefined) {
                  Seq()
                } else {
                  plugin.quantified.handleForallBreathe(input, isInhale = false, f, rdRewriter, labelName, getRdLevel(exhale), nextWildcardName, ctx)
                }
              case default => Seq()
            }) ++ exSeq
          }),
        Seq(Label(labelName, Seq())(exhale.pos, exhale.info)) ++
          wildcardNames.map(n => LocalVarDecl(n, Perm)(exhale.pos, exhale.info))
      )(exhale.pos, exhale.info, NodeTrafo(exhale))
    )
  }

  def assumeAndLog(input: Program, isInhale: Boolean, accessPredicate: AccessPredicate, rdPerm: (Exp, FuncApp) => NormalizedExpression, rdRewriter: Stmt => Stmt, labelName: String, nextWildcardName: () => String, ctx: ContextC[Node, ARPContext]): Seq[Stmt] = {
    val normalized = plugin.normalize.normalizeExpression(accessPredicate.perm, rdPerm)

    def oldRewriter[T <: Node](exp: T) = plugin.utils.rewriteOldExpr(input, labelName, oldLabel = false)(exp)

    if (normalized.isDefined) {
      if (normalized.get.wildcard.isDefined) {
        val wildcardName = nextWildcardName()
        val stmts = (generateAssumptionInhale(input, accessPredicate.loc, normalized.get, ctx.c.logName, negativeOnly = isInhale, wildcardName = wildcardName)(accessPredicate.pos, accessPredicate.info, NodeTrafo(accessPredicate)) ++
          generateLogUpdate(input, accessPredicate.loc, normalized.get, minus = !isInhale, ctx)(accessPredicate.pos, accessPredicate.info, NodeTrafo(accessPredicate)))
          .map(plugin.utils.rewriteRd(wildcardName, Seq(wildcardName)))
        if (isInhale) {
          stmts
        } else {
          stmts.map(oldRewriter)
        }
      } else {
        val stmts = (generateAssumptionInhale(input, accessPredicate.loc, normalized.get, ctx.c.logName, negativeOnly = isInhale)(accessPredicate.pos, accessPredicate.info, NoTrafos) ++
          generateLogUpdate(input, accessPredicate.loc, normalized.get, minus = !isInhale, ctx)(accessPredicate.pos, accessPredicate.info, NoTrafos)).map(rdRewriter)
        if (isInhale) {
          stmts
        } else {
          stmts.map(oldRewriter)
        }
      }
    } else {
      Seq(Assert(BoolLit(b = false)())())
    }
  }

  def handleAssert(input: Program, assert: Assert, ctx: ContextC[Node, ARPContext]): Node = {
    val wildcardNames = getWildcardNames(assert.exp)
    var currentWildcardNames = wildcardNames

    def rdRewriter[T <: Node](exp: T) = plugin.utils.rewriteRd(ctx.c.rdName, wildcardNames)(exp)

    def nextWildcardName() = if (currentWildcardNames.nonEmpty) {
      val head = currentWildcardNames.head
      currentWildcardNames = currentWildcardNames.tail
      head
    } else {
      plugin.naming.getNewName(suffix = "not_enough_names")
    }

    ctx.noRec(
      Seqn(
        splitBreathing(assert.exp, complete = true, Some(false), {
          case accessPredicate: AccessPredicate if !plugin.isAccIgnored(accessPredicate.loc) =>
            val normalized = plugin.normalize.normalizeExpression(accessPredicate.perm, getRdLevel(assert), ignoreErrors = true)
            if (normalized.isDefined) {
              if (normalized.get.wildcard.isDefined) {
                val wildcardName = nextWildcardName()
                generateAssumptionInhale(input, accessPredicate.loc, normalized.get, ctx.c.logName, wildcardName = wildcardName)(assert.pos, assert.info, NodeTrafo(assert))
                  .map(plugin.utils.rewriteRd(wildcardName, Seq(wildcardName)))
              } else {
                generateAssumptionInhale(input, accessPredicate.loc, normalized.get, ctx.c.logName)(assert.pos, assert.info, NoTrafos).map(rdRewriter)
              }
            } else {
              Seq()
            }
          case f: Forall =>
            plugin.quantified.handleForallAssert(input, f, rdRewriter, getRdLevel(assert), nextWildcardName, ctx)
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

  def handlePredicate(input: Program, predicate: Predicate, ctx: ContextC[Node, ARPContext]): Predicate = {
    if (predicate.body.isDefined && plugin.utils.containsRd(predicate.body.get)){
      var assumption: Option[Exp] = None
      def add(exp: Option[Exp]): Unit ={
        if (exp.isDefined) {
          if (assumption.isDefined) {
            assumption = Some(And(assumption.get, exp.get)(predicate.pos, predicate.info))
          } else {
            assumption = exp
          }
        }
      }
      splitBreathing(predicate.body.get, true, None, {
        case accessPredicate: AccessPredicate =>
          add(generatePredicateAssumption(input, accessPredicate.perm)(accessPredicate.pos, accessPredicate.info, NoTrafos))
          Seq()
        case _ => Seq()
      })
      if (assumption.isDefined) {
        Predicate(
          predicate.name,
          predicate.formalArgs,
          Some(And(assumption.get, predicate.body.get)(predicate.pos, predicate.info, NodeTrafo(predicate.body.get)))
        )(predicate.pos, predicate.info, NodeTrafo(predicate))
      } else {
        predicate
      }
    } else {
      predicate
    }
  }

  def handleFold(input: Program, fold: Fold, ctx: ContextC[Node, ARPContext]): Node = {
    ctx.noRec(handlePredicateFolding(input, fold, fold.acc, foldBefore = false, minus = true, ctx))
  }

  def handleUnfold(input: Program, unfold: Unfold, ctx: ContextC[Node, ARPContext]): Node = {
    ctx.noRec(handlePredicateFolding(input, unfold, unfold.acc, foldBefore = true, minus = false, ctx))
  }

  def handleUnfolding(input: Program, unfolding: Unfolding, ctx: ContextC[Node, ARPContext]): Node = {
    ctx.noRec(plugin.utils.rewriteRd(ctx.c.rdName, Seq())(unfolding))
  }

  def handlePredicateFolding(input: Program, fold: Stmt, acc: PredicateAccessPredicate, foldBefore: Boolean, minus: Boolean, ctx: ContextC[Node, ARPContext]): Node = {
    val wildcardNames = getWildcardNames(acc)
    val normalizedPred = plugin.normalize.normalizeExpression(acc.perm, plugin.normalize.rdPermContext)
    val predLogUpdate = if (normalizedPred.isDefined) {
      generateLogUpdate(input, acc.loc, normalizedPred.get, minus = !minus, ctx)(fold.pos, fold.info, NoTrafos).map(plugin.utils.rewriteRd(ctx.c.rdName, wildcardNames))
    } else {
      Seq(Assert(BoolLit(b = false)())())
    }

    def newPerm(exp: Exp) = plugin.utils.simplify(PermMul(acc.perm, exp)(exp.pos, exp.info))

    acc.loc.predicateBody(input) match {
      case Some(body) =>
        val bodyWildcardNames = getWildcardNames(body)
        val wildcardNamesAll = wildcardNames ++ bodyWildcardNames

        var currentWildcardNames = bodyWildcardNames

        def nextWildcardName() = if (currentWildcardNames.nonEmpty) {
          val head = currentWildcardNames.head
          currentWildcardNames = currentWildcardNames.tail
          head
        } else {
          plugin.naming.getNewName(suffix = "not_enough_names")
        }

        val assumption = splitBreathing(body, complete = true, None, {
          case accessPredicate: AccessPredicate if !plugin.isAccIgnored(accessPredicate.loc) =>
            val normalized = plugin.normalize.normalizeExpression(newPerm(accessPredicate.perm), plugin.normalize.rdPermContext)
            if (normalized.isDefined) {
              if (normalized.get.wildcard.isDefined) {
                val wildcardName = if (wildcardNames.nonEmpty) wildcardNames.head else nextWildcardName()
                generateAssumptionInhale(input, accessPredicate.loc, normalized.get, ctx.c.logName)(accessPredicate.pos, accessPredicate.info, NoTrafos)
                  .map(plugin.utils.rewriteRd(wildcardName, Seq(wildcardName)))
              } else {
                generateAssumptionInhale(input, accessPredicate.loc, normalized.get, ctx.c.logName)(accessPredicate.pos, accessPredicate.info, NoTrafos)
                  .map(plugin.utils.rewriteRd(ctx.c.rdName, Seq()))
              }
            } else {
              Seq(Assert(BoolLit(b = false)())())
            }
          case _ =>
            Seq()
        })

        currentWildcardNames = bodyWildcardNames

        Seqn(
          assumption ++
            (if (foldBefore) {
              Seq(
                fold
              )
            } else {
              Seq()
            }) ++
            splitBreathing(body, complete = true, None, {
              case accessPredicate: AccessPredicate if !plugin.isAccIgnored(accessPredicate.loc) =>
                val normalized = plugin.normalize.normalizeExpression(newPerm(accessPredicate.perm), plugin.normalize.rdPermContext)
                if (normalized.isDefined) {
                  if (normalized.get.wildcard.isDefined) {
                    val wildcardName = if (wildcardNames.nonEmpty) wildcardNames.head else nextWildcardName()
                    generateLogUpdate(input, accessPredicate.loc, normalized.get, minus, ctx)(fold.pos, fold.info, NoTrafos)
                      .map(plugin.utils.rewriteRd(wildcardName, Seq(wildcardName)))
                  } else {
                    generateLogUpdate(input, accessPredicate.loc, normalized.get, minus, ctx)(fold.pos, fold.info, NoTrafos)
                      .map(plugin.utils.rewriteRd(ctx.c.rdName, Seq()))
                  }
                } else {
                  Seq(Assert(BoolLit(b = false)())())
                }
              case _ =>
                Seq()
            }) ++
            predLogUpdate ++
            (if (!foldBefore) {
              Seq(
                fold
              )
            } else {
              Seq()
            }),
          wildcardNamesAll.map(n => LocalVarDecl(n, Perm)(fold.pos, fold.info))
        )(fold.pos, fold.info, NodeTrafo(fold))
      case None =>
        Seqn(
          (if (foldBefore) {
            Seq(fold)
          } else {
            Seq()
          }) ++
            predLogUpdate ++
            (if (!foldBefore) {
              Seq(
                fold
              )
            } else {
              Seq()
            }),
          Seq()
        )(fold.pos, fold.info, NodeTrafo(fold))
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

  private def getRdLevel(infoed: Infoed): (Exp, FuncApp) => NormalizedExpression = {
    if ((infoed.info.getUniqueInfo[WasCallCondition] ++ infoed.info.getUniqueInfo[WasInvariantOutside]).nonEmpty) {
      plugin.normalize.rdPermFresh
    } else {
      plugin.normalize.rdPermContext
    }
  }

  def splitBreathing(breath: Exp, complete: Boolean, isInhale: Option[Boolean], handle: Exp => Seq[Stmt]): Seq[Stmt] = {
    def recursive(b: Exp) = splitBreathing(b, complete, isInhale, handle)

    def needSplit(exp: Exp): Boolean = {
      exp.exists({
        case ap: AccessPredicate =>
          ap.perm.exists({
            case cp: CurrentPerm => true
            case FuncApp(name, _) =>
              name == plugin.naming.rdName || name == plugin.naming.rdWildcardName || name == plugin.naming.rdCountingName
            case _ => false
          })
        case _ => false
      })
    }

    if (complete || needSplit(breath)) {
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
        case InhaleExhaleExp(in, ex) => recursive(in) ++ recursive(ex)
        case fa@FieldAccessPredicate(loc, perm) => splitAccessPredicate(perm, recursive, handle, fa, FieldAccessPredicate(loc, _)(fa.pos, fa.info, NodeTrafo(fa)))
        case pa@PredicateAccessPredicate(loc, perm) => splitAccessPredicate(perm, recursive, handle, pa, PredicateAccessPredicate(loc, _)(pa.pos, pa.info, NodeTrafo(pa)))
        case default => handle(default)
      }
    } else {
      handle(breath)
    }
  }

  def splitAccessPredicate(perm: Exp, recursiveCall: Exp => Seq[Stmt], handle: Exp => Seq[Stmt], orig: AccessPredicate, wrapper: Exp => Exp): Seq[Stmt] = {
    // TODO: arbitrary conditionals in acc (e.g. (a ? b : c) + (d ? e : f)

    perm match {
      case CondExp(cond, thn, els) => recursiveCall(CondExp(cond, wrapper(thn), wrapper(els))(perm.pos, perm.info, NodeTrafo(perm)))
      case _ => handle(orig)
    }
  }

  def generateAssumptionInhale(input: Program, acc: LocationAccess, normalized: NormalizedExpression, logName: String, negativeOnly: Boolean = false, wildcardName: String = "")(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    generateAssumption(input, acc, normalized, logName, negativeOnly, wildcardName)(pos, info, errT).map(Inhale(_)(pos, info, errT)).toSeq
  }

  def generateAssumption(input: Program, acc: LocationAccess, normalized: NormalizedExpression, logName: String, negativeOnly: Boolean = false, wildcardName: String = "")(pos: Position, info: Info, errT: ErrorTrafo): Option[Exp] = {
    val arpFieldFunction = plugin.utils.getAccessDomainFuncApp(input, acc)(pos, info, errT)
    val rcv = plugin.utils.getAccessRcv(acc)(pos, info, errT)

    val arpLogType = plugin.utils.getARPLogType(input)
    val arpLogSum = plugin.utils.getARPLogFunction(input, plugin.naming.logDomainSumGt)
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
      val rdOrderAssumption = generateRdOrderAssumption(normalized)(pos, info, errT)

      if (normalized.exps.isEmpty) {
        None
      } else {
        if (negativeOnly) {
          combineAssumptions(
            rdOrderAssumption,
            generateAssumptionWorkerNegative(acc, getSumCall, normalized, None, foundPositive = false)(pos, info, errT)
          )(pos, info, errT)
        } else {
          combineAssumptions(
            rdOrderAssumption,
            generateAssumptionWorker(acc, getSumCall, normalized, None, onlyPositive = false)(pos, info, errT)
          )(pos, info, errT)
        }
      }
    }
  }

  def generateRdOrderAssumption(normalizedExpression: NormalizedExpression)(pos: Position, info: Info, errT: ErrorTrafo): Option[Exp] = {
    val exps = normalizedExpression.exps ++ normalizedExpression.const
    if (exps.size < 2) {
      None
    } else {
      val newCmp = PermLtCmp(
        exps.head.getAbsTotal(plugin)(pos, info, errT),
        exps.tail.head.getAbsTotal(plugin)(pos, info, errT)
      )(pos, info, errT)
      val newNormalized = NormalizedExpression(normalizedExpression.exps.tail, normalizedExpression.const, None)
      combineAssumptions(Some(newCmp), generateRdOrderAssumption(newNormalized)(pos, info, errT))(pos, info, errT)
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
        val newNormalized = NormalizedExpression(Seq(), None, None)
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
      val newNormalized = NormalizedExpression(normalized.exps.tail, normalized.const, None)
      lazy val expGe0 = putInCond(
        PermLtCmp(NoPerm()(pos, info, errT), getSumCall(cur.check))(pos, info, errT),
        recursive(newNormalized, addAssumption(cur.getTotal(plugin)(pos, info, errT))),
        recursive(newNormalized)
      )(pos, info, errT)
      lazy val expLt0 = if (onlyPositive) {
        recursive(newNormalized)
      } else {
        combineAssumptions(
          recursiveNegative(newNormalized, addAssumption(cur.getTotal(plugin)(pos, info, errT))),
          recursive(newNormalized, p = true)
        )(pos, info, errT)
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
        val newNormalized = NormalizedExpression(normalized.exps.dropRight(1), None, None)

        lazy val expGt0 = if (foundPositive) {
          recursive(newNormalized)
        } else {
          recursive(newNormalized, addAssumption(cur.getTotal(plugin)(pos, info, errT)), f = true)
        }
        lazy val expEq0 = recursive(newNormalized)
        lazy val expLt0 = if (foundPositive) {
          recursive(newNormalized, addAssumption(cur.getTotal(plugin)(pos, info, errT)))
        } else {
          None
        }
        generateCond(cur.exp, expGt0, expEq0, expLt0)
      }
    } else {
      // start with const
      val newNormalized = NormalizedExpression(normalized.exps, None, None)
      val const = normalized.const.get
      lazy val expGt0 = recursive(newNormalized, addAssumption(const.exp), f = true)
      lazy val expEq0 = recursive(newNormalized)
      lazy val expLt0 = None
      generateCond(const.exp, expGt0, expEq0, expLt0)
    }
  }

  def generatePredicateAssumption(input: Program,  perm: Exp)(pos: Position, info: Info, errT: ErrorTrafo): Option[Exp] ={
    val normalizedMaybe = plugin.normalize.normalizeExpression(perm, plugin.normalize.globalPerm)
    if (normalizedMaybe.isEmpty || normalizedMaybe.get.wildcard.isDefined){
      None
    } else {
      val normalized = normalizedMaybe.get
      if (normalized.exps.isEmpty){
        None
      } else {
        val rdOrderAssumption = generateRdOrderAssumption(normalized)(pos, info, errT)

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

        val assumption = generateCond(
          normalized.exps.last.exp,
          Some(And(
            PermLeCmp(NoPerm()(pos, info, errT), perm)(pos, info, errT),
            PermLtCmp(perm, FullPerm()(pos, info, errT))(pos, info, errT)
          )(pos, info, errT)),
          Some(And(
            PermLtCmp(NoPerm()(pos, info, errT), perm)(pos, info, errT),
            PermLeCmp(perm, FullPerm()(pos, info, errT))(pos, info, errT)
          )(pos, info, errT))
        )

        combineAssumptions(rdOrderAssumption, assumption)(pos, info, errT)
      }
    }
  }

  def generateLogUpdate(input: Program, acc: LocationAccess, normalized: NormalizedExpression, minus: Boolean, ctx: ContextC[Node, ARPContext])(pos: Position, info: Info, errT: ErrorTrafo): Seq[Stmt] = {
    val arpLogType = plugin.utils.getARPLogType(input)
    val arpLog = LocalVar(ctx.c.logName)(arpLogType, pos, info)
    val arpLogCons = plugin.utils.getARPLogFunction(input, plugin.naming.logDomainCons)

    val rcv = plugin.utils.getAccessRcv(acc)(pos, info, errT)
    val arpFieldFunction = plugin.utils.getAccessDomainFuncApp(input, acc)(pos, info, errT)

    def getConsCall(level: Int, permission: Exp): LocalVarAssign = {
      LocalVarAssign(
        arpLog,
        DomainFuncApp(
          arpLogCons, Seq(
            rcv,
            arpFieldFunction,
            plugin.utils.simplify(if (minus) PermMinus(permission)(pos, info, errT) else permission),
            IntLit(level)(pos, info, errT),
            arpLog
          ),
          Map[TypeVar, Type]()
        )(pos, info, errT)
      )(pos, info, errT)
    }

    var logSeq = Seq[Stmt]()
    (normalized.const ++ normalized.wildcard ++ normalized.exps).foreach(e => logSeq :+= getConsCall(e.store, e.getTotal(plugin)(pos, info, errT)))
    logSeq
  }

}