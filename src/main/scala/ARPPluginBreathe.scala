/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast.utility.Rewriter.ContextC
import viper.silver.ast._

object ARPPluginBreathe {

  // TODO: Adjust log levels
  // TODO: Adjust sum levels

  def handleInhale(input: Program, inhale: Inhale, ctx: ContextC[Node, String]): Node = {
    val i = Inhale(ARPPluginUtils.rewriteRd(ctx.c)(inhale.exp))(inhale.pos, inhale.info, inhale.errT + NodeTrafo(inhale))
    ctx.noRec(i)
    Seqn(
      Seq(i) ++
        splitBreathing(i.exp).map({
          case accessPredicate: FieldAccessPredicate =>
            val normalized = ARPPluginNormalize.normalizeExpression(accessPredicate.perm)
            Some(generateLogUpdate(input, accessPredicate, normalized, minus = false, ctx))
          case _ =>
            None
        }).filter(_.isDefined).flatMap(_.get),
      Seq()
    )(inhale.pos, inhale.info, inhale.errT + NodeTrafo(inhale))
  }

  def handleExhale(input: Program, exhale: Exhale, ctx: ContextC[Node, String]): Node = {
    val labelName = ARPPluginNaming.getNameFor(exhale, suffix = "exhale_label")
    Seqn(
      Seq(Label(labelName, Seq())(exhale.pos, exhale.info)) ++
      splitBreathing(exhale.exp).map {
        case accessPredicate: FieldAccessPredicate =>
          val normalized = ARPPluginNormalize.normalizeExpression(accessPredicate.perm)
          val e = Exhale(
            ARPPluginUtils.rewriteOldExpr(labelName, oldLabel = false)(
              ARPPluginUtils.rewriteRd(ctx.c)(accessPredicate)
            )
          )(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale))
          ctx.noRec(e)

          Seqn(
            generateAssumption(input, accessPredicate, normalized, ctx) ++
              Seq(e) ++
              generateLogUpdate(input, accessPredicate, normalized, minus = true, ctx),
            Seq()
          )(exhale.pos, exhale.info)
        case default =>
          val e = Exhale(ARPPluginUtils.rewriteRd(ctx.c)(default))(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale))
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

  def generateAssumption(input: Program, accessPredicate: FieldAccessPredicate, normalized: NormalizedExpression, ctx: ContextC[Node, String]): Seq[Stmt] = {

    // ************** //
    // * init stuff * //
    // ************** //

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

    // Helpers
    val zeroLit = IntLit(0)(accessPredicate.pos, accessPredicate.info)
    val noPermLit = NoPerm()(accessPredicate.pos, accessPredicate.info)
    val emptySeqn = Seqn(Seq(), Seq())(accessPredicate.pos, accessPredicate.info)
    val epsilonRd = FuncApp(ARPPluginUtils.getFunction(input, ARPPluginNaming.rdEpsilonName).get, Seq())(accessPredicate.pos, accessPredicate.info)
    val currentPerm = CurrentPerm(fieldAccess)(accessPredicate.pos, accessPredicate.info)
    val localRd = LocalVar(ctx.c)(Perm, accessPredicate.pos, accessPredicate.info)

    def getSumCall(level: Int): DomainFuncApp = DomainFuncApp(
      arpLogSum,
      Seq(
        rcv,
        DomainFuncApp(arpFieldFunction, Seq(), Map[TypeVar, Type]())(accessPredicate.pos, accessPredicate.info),
        IntLit(level)(accessPredicate.pos, accessPredicate.info),
        arpLog
      ),
      Map[TypeVar, Type]() /* TODO: What's the deal with this? */
    )(accessPredicate.pos, accessPredicate.info)

    if (normalized.wildcard.isDefined) {
      // ************* //
      // * wildcards * //
      // ************* //
      Seq()
    } else {
      // ************************** //
      // * no counting permission * //
      // ************************** //

      // n == 0 && (0 < n_rd && none < sum()) && (0 < q && q < sum())
      val countingEq0RdGt0ConstOk = Seqn(
        Seq(
          // assume q + n_rd * rd < perm()
          Inhale(
            PermLtCmp(
              PermAdd(
                normalized.const.get,
                PermMul(
                  normalized.read.get,
                  localRd
                )(accessPredicate.pos, accessPredicate.info)
              )(accessPredicate.pos, accessPredicate.info),
              currentPerm
            )(accessPredicate.pos, accessPredicate.info)
          )(accessPredicate.pos, accessPredicate.info)
        ),
        Seq()
      )(accessPredicate.pos, accessPredicate.info)

      // n == 0 && (0 < n_rd && none < sum()) && (!(0 < q && q < sum()))
      val countingEq0RdGt0ConstNok = Seqn(
        Seq(
          // assume n_rd * rd < perm()
          Inhale(
            PermLtCmp(
              PermMul(
                normalized.read.get,
                localRd
              )(accessPredicate.pos, accessPredicate.info),
              currentPerm
            )(accessPredicate.pos, accessPredicate.info)
          )(accessPredicate.pos, accessPredicate.info)
        ),
        Seq()
      )(accessPredicate.pos, accessPredicate.info)

      // n == 0 && (0 < n_rd && none < sum())
      val countingEq0RdGt0 = if (normalized.const.isDefined) {
        Seqn(
          Seq(
            If(
              And(
                LtCmp(zeroLit, normalized.const.get)(accessPredicate.pos, accessPredicate.info),
                PermLtCmp(normalized.const.get, getSumCall(-1))(accessPredicate.pos, accessPredicate.info)
              )(accessPredicate.pos, accessPredicate.info),
              // if (0 < q && q < sum())
              countingEq0RdGt0ConstOk,
              // else
              countingEq0RdGt0ConstNok
            )(accessPredicate.pos, accessPredicate.info)
          ),
          Seq()
        )(accessPredicate.pos, accessPredicate.info)
      } else {
        countingEq0RdGt0ConstNok
      }

      // n == 0 && (n_rd < 0 && 0 < q)
      val countingEq0RdLt0 = Seqn(
        Seq(
          // assume none < q + n_rd * rd
          Inhale(
            PermLtCmp(
              noPermLit,
              PermAdd(
                normalized.const.get,
                PermMul(
                  normalized.read.get,
                  localRd
                )(accessPredicate.pos, accessPredicate.info)
              )(accessPredicate.pos, accessPredicate.info)
            )(accessPredicate.pos, accessPredicate.info)
          )(accessPredicate.pos, accessPredicate.info)
        ),
        Seq()
      )(accessPredicate.pos, accessPredicate.info)

      // n == 0
      val countingEq0 = if (normalized.read.isDefined) {
        Seqn(
          Seq(
            If(
              And(
                LtCmp(zeroLit, normalized.read.get)(accessPredicate.pos, accessPredicate.info),
                PermLtCmp(noPermLit, getSumCall(-1))(accessPredicate.pos, accessPredicate.info)
              )(accessPredicate.pos, accessPredicate.info),
              // if (0 < n_rd && none < sum())
              countingEq0RdGt0,
              Seqn(
                Seq(
                  If(
                    And(
                      LtCmp(normalized.read.get, zeroLit)(accessPredicate.pos, accessPredicate.info),
                      PermLtCmp(noPermLit, normalized.const.get)(accessPredicate.pos, accessPredicate.info)
                    )(accessPredicate.pos, accessPredicate.info),
                    // if (n_rd < 0 && 0 < q)
                    countingEq0RdLt0,
                    emptySeqn
                  )(accessPredicate.pos, accessPredicate.info)
                ),
                Seq()
              )(accessPredicate.pos, accessPredicate.info)
            )(accessPredicate.pos, accessPredicate.info)
          ),
          Seq()
        )(accessPredicate.pos, accessPredicate.info)
      } else {
        emptySeqn
      }

      // ******************************** //
      // * positive counting permission * //
      // ******************************** //

      // n > 0 && (none < sum()) && (!(0 < n_rd && none < sum()))
      val countingGt0SumOkRdLe0 = Seqn(
        Seq(
          Inhale(
            PermLtCmp(
              PermMul(
                normalized.counting.get,
                epsilonRd
              )(accessPredicate.pos, accessPredicate.info),
              currentPerm
            )(accessPredicate.pos, accessPredicate.info)
          )(accessPredicate.pos, accessPredicate.info)
        ),
        Seq()
      )(accessPredicate.pos, accessPredicate.info)

      // n > 0 && (none < sum()) && (0 < n_rd && none < sum()) && (0 < q && q < sum())
      val countingGt0SumOkRdGt0ConstOk = Seqn(
        Seq(
          Inhale(
            PermLtCmp(
              PermAdd(
                normalized.const.get,
                PermAdd(
                  PermMul(
                    normalized.read.get,
                    localRd
                  )(accessPredicate.pos, accessPredicate.info),
                  PermMul(
                    normalized.counting.get,
                    epsilonRd
                  )(accessPredicate.pos, accessPredicate.info)
                )(accessPredicate.pos, accessPredicate.info)
              )(accessPredicate.pos, accessPredicate.info),
              currentPerm
            )(accessPredicate.pos, accessPredicate.info)
          )(accessPredicate.pos, accessPredicate.info)
        ),
        Seq()
      )(accessPredicate.pos, accessPredicate.info)

      // n > 0 && (none < sum()) && (0 < n_rd && none < sum()) && (!(0 < q && q < sum()))
      val countingGt0SumOkRdGt0ConstNok = Seqn(
        Seq(
          Inhale(
            PermLtCmp(
              PermAdd(
                PermMul(
                  normalized.read.get,
                  localRd
                )(accessPredicate.pos, accessPredicate.info),
                PermMul(
                  normalized.counting.get,
                  epsilonRd
                )(accessPredicate.pos, accessPredicate.info)
              )(accessPredicate.pos, accessPredicate.info),
              currentPerm
            )(accessPredicate.pos, accessPredicate.info)
          )(accessPredicate.pos, accessPredicate.info)
        ),
        Seq()
      )(accessPredicate.pos, accessPredicate.info)

      // n > 0 && (none < sum()) && (0 < n_rd && none < sum())
      val countingGt0SumOkRdGt0 = Seqn(
        Seq(
          If(
            And(
              PermLtCmp(noPermLit, normalized.const.get)(accessPredicate.pos, accessPredicate.info),
              PermLtCmp(normalized.const.get, getSumCall(-1))(accessPredicate.pos, accessPredicate.info)
            )(accessPredicate.pos, accessPredicate.info),
            // if (0 < q && q < sum())
            countingGt0SumOkRdGt0ConstOk,
            // else
            countingGt0SumOkRdGt0ConstNok
          )(accessPredicate.pos, accessPredicate.info)
        ),
        Seq()
      )(accessPredicate.pos, accessPredicate.info)

      // n > 0 && (none < sum())
      val countingGt0SumOk = Seqn(
        Seq(
          If(
            And(
              LtCmp(zeroLit, normalized.read.get)(accessPredicate.pos, accessPredicate.info),
              PermLtCmp(noPermLit, getSumCall(-1))(accessPredicate.pos, accessPredicate.info)
            )(accessPredicate.pos, accessPredicate.info),
            // if (0 < n_rd && none < sum())
            countingGt0SumOkRdGt0,
            // else
            countingGt0SumOkRdLe0
          )(accessPredicate.pos, accessPredicate.info)
        ),
        Seq()
      )(accessPredicate.pos, accessPredicate.info)

      // n > 0
      val countingGt0 = Seqn(
        Seq(
          If(
            PermLtCmp(noPermLit, getSumCall(-1))(accessPredicate.pos, accessPredicate.info),
            // if (none < sum())
            countingGt0SumOk,
            // else
            emptySeqn
          )(accessPredicate.pos, accessPredicate.info)
        ),
        Seq()
      )(accessPredicate.pos, accessPredicate.info)

      // ******************************** //
      // * negative counting permission * //
      // ******************************** //

      // n < 0 && (0 == q && 0 < n_rd)
      val countingLt0RdGt0 = Seqn(
        Seq(
          Inhale(
            PermLtCmp(
              noPermLit,
              PermAdd(
                PermMul(
                  normalized.read.get,
                  localRd
                )(accessPredicate.pos, accessPredicate.info),
                PermMul(
                  normalized.counting.get,
                  epsilonRd
                )(accessPredicate.pos, accessPredicate.info)
              )(accessPredicate.pos, accessPredicate.info)
            )(accessPredicate.pos, accessPredicate.info)
          )(accessPredicate.pos, accessPredicate.info)
        ),
        Seq()
      )(accessPredicate.pos, accessPredicate.info)

      // n < 0 && !(0 == q && 0 < n_rd) && (0 < q) && (0 < rd_n)
      val countingLt0ConstGt0RdGt0 = Seqn(
        Seq(
          Inhale(
            PermLtCmp(
              noPermLit,
              PermAdd(
                normalized.const.get,
                PermAdd(
                  PermMul(
                    normalized.read.get,
                    localRd
                  )(accessPredicate.pos, accessPredicate.info),
                  PermMul(
                    normalized.counting.get,
                    epsilonRd
                  )(accessPredicate.pos, accessPredicate.info)
                )(accessPredicate.pos, accessPredicate.info)
              )(accessPredicate.pos, accessPredicate.info)
            )(accessPredicate.pos, accessPredicate.info)
          )(accessPredicate.pos, accessPredicate.info)
        ),
        Seq()
      )(accessPredicate.pos, accessPredicate.info)

      // n < 0 && !(0 == q && 0 < n_rd) && (0 < q) && (!(0 < rd_n))
      val countingLt0ConstGt0RdLe0 = Seqn(
        Seq(
          Inhale(
            PermLtCmp(
              noPermLit,
              PermAdd(
                normalized.const.get,
                PermMul(
                  normalized.counting.get,
                  epsilonRd
                )(accessPredicate.pos, accessPredicate.info)
              )(accessPredicate.pos, accessPredicate.info)
            )(accessPredicate.pos, accessPredicate.info)
          )(accessPredicate.pos, accessPredicate.info)
        ),
        Seq()
      )(accessPredicate.pos, accessPredicate.info)

      // n < 0 && !(0 == q && 0 < n_rd) && (0 < q)
      val countingLt0ConstGt0 = Seqn(
        Seq(
          If(
            LtCmp(zeroLit, normalized.read.get)(accessPredicate.pos, accessPredicate.info),
            // if (0 < rd_n)
            countingLt0ConstGt0RdGt0,
            // else
            countingLt0ConstGt0RdLe0
          )(accessPredicate.pos, accessPredicate.info)
        ),
        Seq()
      )(accessPredicate.pos, accessPredicate.info)

      // n < 0 && !(0 == q && 0 < n_rd)
      val countingLt0MaybeConstGt0 = Seqn(
        Seq(
          If(
            PermLtCmp(noPermLit, normalized.const.get)(accessPredicate.pos, accessPredicate.info),
            // if (0 < q)
            countingLt0ConstGt0,
            // else
            emptySeqn
          )(accessPredicate.pos, accessPredicate.info)
        ),
        Seq()
      )(accessPredicate.pos, accessPredicate.info)

      // n < 0
      val countingLt0 = Seqn(
        Seq(
          If(
            And(
              EqCmp(zeroLit, normalized.const.get)(accessPredicate.pos, accessPredicate.info),
              LtCmp(zeroLit, normalized.read.get)(accessPredicate.pos, accessPredicate.info)
            )(accessPredicate.pos, accessPredicate.info),
            // if (0 == q && 0 < n_rd)
            countingLt0RdGt0,
            // else
            countingLt0MaybeConstGt0
          )(accessPredicate.pos, accessPredicate.info)
        ),
        Seq()
      )(accessPredicate.pos, accessPredicate.info)

      // ************* //
      // * merge ifs * //
      // ************* //

      var assumptionSeq = Seq[Stmt]()

      if (normalized.counting.isDefined) {
        // 0 != n
        val countingNeq0 = Seqn(
          Seq(
            If(
              LtCmp(zeroLit, normalized.counting.get)(accessPredicate.pos, accessPredicate.info),
              // if (0 < n)
              countingGt0,
              // if (0 > n)
              countingLt0
            )(accessPredicate.pos, accessPredicate.info)
          ),
          Seq()
        )(accessPredicate.pos, accessPredicate.info)

        val countingIf = If(
          EqCmp(zeroLit, normalized.counting.get)(accessPredicate.pos, accessPredicate.info),
          // if (0 == n)
          countingEq0,
          // if (0 != n)
          countingNeq0
        )(accessPredicate.pos, accessPredicate.info)

        assumptionSeq ++= Seq(countingIf)
      } else {
        assumptionSeq ++= Seq(countingEq0)
      }
      assumptionSeq
    }
  }

  def generateLogUpdate(input: Program, fieldAccessPredicate: FieldAccessPredicate, normalized: NormalizedExpression, minus: Boolean, ctx: ContextC[Node, String]): Seq[Stmt] = {

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
            DomainFuncApp(arpFieldFunction, Seq(), Map[TypeVar, Type]())(fieldAccessPredicate.pos, fieldAccessPredicate.info),
            if (minus) Minus(permission)(fieldAccessPredicate.pos, fieldAccessPredicate.info) else permission,
            IntLit(level)(fieldAccessPredicate.pos, fieldAccessPredicate.info),
            arpLog
          ),
          Map[TypeVar, Type]() /* TODO: What's the deal with this? */
        )(fieldAccessPredicate.pos, fieldAccessPredicate.info)
      )(fieldAccessPredicate.pos, fieldAccessPredicate.info)
    }

    var logSeq = Seq[Stmt]()

    if (normalized.const.isDefined) {
      logSeq :+= getConsCall(-1, normalized.const.get)
    }
    if (normalized.predicate.isDefined) {
      logSeq :+= getConsCall(-1, normalized.predicate.get)
    }
    if (normalized.counting.isDefined) {
      logSeq :+= getConsCall(-1, normalized.counting.get)
    }
    if (normalized.read.isDefined) {
      logSeq :+= getConsCall(-1, normalized.read.get)
    }
    if (normalized.wildcard.isDefined) {
      logSeq :+= getConsCall(-1, normalized.wildcard.get)
    }
    logSeq
  }

}