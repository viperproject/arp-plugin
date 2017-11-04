/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast.utility.Rewriter.ContextC
import viper.silver.ast._

object ARPPluginBreathe {

  // TODO: Add label before not yet split inhales/exhales
  // TODO: Adjust log levels
  // TODO: Normalize expressions
  // TODO: Adjust sum levels
  // TODO: Only output if when option is defined
  // TODO: Handle wildcards

  def handleInhale(input: Program, inhale: Inhale, ctx: ContextC[Node, String]): Node = {
    val i = Inhale(ARPPluginUtils.rewriteRd(ctx.c)(inhale.exp))(inhale.pos, inhale.info, inhale.errT + NodeTrafo(inhale))
    ctx.noRec(i)
    i
  }

  def handleExhale(input: Program, exhale: Exhale, ctx: ContextC[Node, String]): Node = {
    Seqn(
      splitBreathing(exhale.exp).map {
        case accessPredicate: FieldAccessPredicate =>
          val e = Exhale(ARPPluginUtils.rewriteRd(ctx.c)(accessPredicate))(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale))
          ctx.noRec(e)
          generateAssumption(input, e, accessPredicate, ctx)
        case default =>
          val e = Exhale(ARPPluginUtils.rewriteRd(ctx.c)(default))(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale))
          ctx.noRec(e)
          e
      },
      Seq()
    )(exhale.pos, exhale.info, exhale.errT + NodeTrafo(exhale))
  }

  def splitBreathing(breath: Exp): Seq[Exp] = {
    breath match {
      case And(left, right) => splitBreathing(left) ++ splitBreathing(right)
      case default => Seq(default)
    }
  }

  def generateAssumption(input: Program, breath: Stmt, fieldAccessPredicate: FieldAccessPredicate, ctx: ContextC[Node, String]): Stmt = {

    // ************** //
    // * init stuff * //
    // ************** //

    val normalized = normalizeExpression(fieldAccessPredicate.perm)
    val fieldAccess = fieldAccessPredicate.loc
    val field = fieldAccess.field
    val fieldFunctionName = ARPPluginUtils.getNewNameForWithSuffix(field)
    val rcv = fieldAccess.rcv

    val arpLogDomain = ARPPluginUtils.getDomain(input, ARPPluginUtils.getARPLogDomainName).get
    val arpLogType = DomainType(arpLogDomain, Map[TypeVar, Type]() /* TODO: What's the deal with this? */)
    val arpLogCons = ARPPluginUtils.getDomainFunction(arpLogDomain, "ARPLog_Cons").get
    val arpLogSum = ARPPluginUtils.getDomainFunction(arpLogDomain, "ARPLog_sum").get

    val arpFieldFunctionDomain = ARPPluginUtils.getDomain(input, ARPPluginUtils.getFieldFunctionDomainName).get
    val arpFieldFunction = ARPPluginUtils.getDomainFunction(arpFieldFunctionDomain, fieldFunctionName).get

    val arpLog = LocalVar(ARPPluginUtils.getARPLogName)(arpLogType, breath.pos, breath.info)
    val zeroLit = IntLit(0)(breath.pos, breath.info)
    val noPermLit = NoPerm()(breath.pos, breath.info)
    val emptySeqn = Seqn(Seq(), Seq())(breath.pos, breath.info)
    val epsilonRd = FuncApp(ARPPluginUtils.getFunction(input, "epsilonRd").get, Seq())(breath.pos, breath.info)
    val currentPerm = CurrentPerm(fieldAccess)(breath.pos, breath.info)
    val localRd = LocalVar(ctx.c)(Perm, breath.pos, breath.info)

    def getSumCall(level: Int): DomainFuncApp = DomainFuncApp(
      arpLogSum,
      Seq(
        rcv,
        DomainFuncApp(arpFieldFunction, Seq(), Map[TypeVar, Type]())(breath.pos, breath.info),
        IntLit(level)(breath.pos, breath.info),
        arpLog
      ),
      Map[TypeVar, Type]() /* TODO: What's the deal with this? */
    )(breath.pos, breath.info)

    def getConsCall(level: Int, permission: Exp, minus: Boolean): LocalVarAssign ={
      LocalVarAssign(
        arpLog,
        DomainFuncApp(
          arpLogCons, Seq(
            rcv,
            DomainFuncApp(arpFieldFunction, Seq(), Map[TypeVar, Type]())(breath.pos, breath.info),
            if (minus) Minus(permission)(breath.pos, breath.info) else permission,
            IntLit(level)(breath.pos, breath.info),
            arpLog
          ),
          Map[TypeVar, Type]() /* TODO: What's the deal with this? */
        )(breath.pos, breath.info)
      )(breath.pos, breath.info)
    }

    if (normalized.wildcard.isDefined) {
      // ************* //
      // * wildcards * //
      // ************* //
      breath
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
                )(breath.pos, breath.info)
              )(breath.pos, breath.info),
              currentPerm
            )(breath.pos, breath.info)
          )(breath.pos, breath.info)
        ),
        Seq()
      )(breath.pos, breath.info)

      // n == 0 && (0 < n_rd && none < sum()) && (!(0 < q && q < sum()))
      val countingEq0RdGt0ConstNok = Seqn(
        Seq(
          // assume n_rd * rd < perm()
          Inhale(
            PermLtCmp(
              PermMul(
                normalized.read.get,
                localRd
              )(breath.pos, breath.info),
              currentPerm
            )(breath.pos, breath.info)
          )(breath.pos, breath.info)
        ),
        Seq()
      )(breath.pos, breath.info)

      // n == 0 && (0 < n_rd && none < sum())
      val countingEq0RdGt0 = if (normalized.const.isDefined) {
        Seqn(
          Seq(
            If(
              And(
                LtCmp(zeroLit, normalized.const.get)(breath.pos, breath.info),
                PermLtCmp(normalized.const.get, getSumCall(-1))(breath.pos, breath.info)
              )(breath.pos, breath.info),
              // if (0 < q && q < sum())
              countingEq0RdGt0ConstOk,
              // else
              countingEq0RdGt0ConstNok
            )(breath.pos, breath.info)
          ),
          Seq()
        )(breath.pos, breath.info)
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
                )(breath.pos, breath.info)
              )(breath.pos, breath.info)
            )(breath.pos, breath.info)
          )(breath.pos, breath.info)
        ),
        Seq()
      )(breath.pos, breath.info)

      // n == 0
      val countingEq0 = if (normalized.read.isDefined) {
        Seqn(
          Seq(
            If(
              And(
                LtCmp(zeroLit, normalized.read.get)(breath.pos, breath.info),
                PermLtCmp(noPermLit, getSumCall(-1))(breath.pos, breath.info)
              )(breath.pos, breath.info),
              // if (0 < n_rd && none < sum())
              countingEq0RdGt0,
              Seqn(
                Seq(
                  If(
                    And(
                      LtCmp(normalized.read.get, zeroLit)(breath.pos, breath.info),
                      PermLtCmp(noPermLit, normalized.const.get)(breath.pos, breath.info)
                    )(breath.pos, breath.info),
                    // if (n_rd < 0 && 0 < q)
                    countingEq0RdLt0,
                    emptySeqn
                  )(breath.pos, breath.info)
                ),
                Seq()
              )(breath.pos, breath.info)
            )(breath.pos, breath.info)
          ),
          Seq()
        )(breath.pos, breath.info)
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
              )(breath.pos, breath.info),
              currentPerm
            )(breath.pos, breath.info)
          )(breath.pos, breath.info)
        ),
        Seq()
      )(breath.pos, breath.info)

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
                  )(breath.pos, breath.info),
                  PermMul(
                    normalized.counting.get,
                    epsilonRd
                  )(breath.pos, breath.info)
                )(breath.pos, breath.info)
              )(breath.pos, breath.info),
              currentPerm
            )(breath.pos, breath.info)
          )(breath.pos, breath.info)
        ),
        Seq()
      )(breath.pos, breath.info)

      // n > 0 && (none < sum()) && (0 < n_rd && none < sum()) && (!(0 < q && q < sum()))
      val countingGt0SumOkRdGt0ConstNok = Seqn(
        Seq(
          Inhale(
            PermLtCmp(
              PermAdd(
                PermMul(
                  normalized.read.get,
                  localRd
                )(breath.pos, breath.info),
                PermMul(
                  normalized.counting.get,
                  epsilonRd
                )(breath.pos, breath.info)
              )(breath.pos, breath.info),
              currentPerm
            )(breath.pos, breath.info)
          )(breath.pos, breath.info)
        ),
        Seq()
      )(breath.pos, breath.info)

      // n > 0 && (none < sum()) && (0 < n_rd && none < sum())
      val countingGt0SumOkRdGt0 = Seqn(
        Seq(
          If(
            And(
              PermLtCmp(noPermLit, normalized.const.get)(breath.pos, breath.info),
              PermLtCmp(normalized.const.get, getSumCall(-1))(breath.pos, breath.info)
            )(breath.pos, breath.info),
            // if (0 < q && q < sum())
            countingGt0SumOkRdGt0ConstOk,
            // else
            countingGt0SumOkRdGt0ConstNok
          )(breath.pos, breath.info)
        ),
        Seq()
      )(breath.pos, breath.info)

      // n > 0 && (none < sum())
      val countingGt0SumOk = Seqn(
        Seq(
          If(
            And(
              LtCmp(zeroLit, normalized.read.get)(breath.pos, breath.info),
              PermLtCmp(noPermLit, getSumCall(-1))(breath.pos, breath.info)
            )(breath.pos, breath.info),
            // if (0 < n_rd && none < sum())
            countingGt0SumOkRdGt0,
            // else
            countingGt0SumOkRdLe0
          )(breath.pos, breath.info)
        ),
        Seq()
      )(breath.pos, breath.info)

      // n > 0
      val countingGt0 = Seqn(
        Seq(
          If(
            PermLtCmp(noPermLit, getSumCall(-1))(breath.pos, breath.info),
            // if (none < sum())
            countingGt0SumOk,
            // else
            emptySeqn
          )(breath.pos, breath.info)
        ),
        Seq()
      )(breath.pos, breath.info)

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
                )(breath.pos, breath.info),
                PermMul(
                  normalized.counting.get,
                  epsilonRd
                )(breath.pos, breath.info)
              )(breath.pos, breath.info)
            )(breath.pos, breath.info)
          )(breath.pos, breath.info)
        ),
        Seq()
      )(breath.pos, breath.info)

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
                  )(breath.pos, breath.info),
                  PermMul(
                    normalized.counting.get,
                    epsilonRd
                  )(breath.pos, breath.info)
                )(breath.pos, breath.info)
              )(breath.pos, breath.info)
            )(breath.pos, breath.info)
          )(breath.pos, breath.info)
        ),
        Seq()
      )(breath.pos, breath.info)

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
                )(breath.pos, breath.info)
              )(breath.pos, breath.info)
            )(breath.pos, breath.info)
          )(breath.pos, breath.info)
        ),
        Seq()
      )(breath.pos, breath.info)

      // n < 0 && !(0 == q && 0 < n_rd) && (0 < q)
      val countingLt0ConstGt0 = Seqn(
        Seq(
          If(
            LtCmp(zeroLit, normalized.read.get)(breath.pos, breath.info),
            // if (0 < rd_n)
            countingLt0ConstGt0RdGt0,
            // else
            countingLt0ConstGt0RdLe0
          )(breath.pos, breath.info)
        ),
        Seq()
      )(breath.pos, breath.info)

      // n < 0 && !(0 == q && 0 < n_rd)
      val countingLt0MaybeConstGt0 = Seqn(
        Seq(
          If(
            PermLtCmp(noPermLit, normalized.const.get)(breath.pos, breath.info),
            // if (0 < q)
            countingLt0ConstGt0,
            // else
            emptySeqn
          )(breath.pos, breath.info)
        ),
        Seq()
      )(breath.pos, breath.info)

      // n < 0
      val countingLt0 = Seqn(
        Seq(
          If(
            And(
              EqCmp(zeroLit, normalized.const.get)(breath.pos, breath.info),
              LtCmp(zeroLit, normalized.read.get)(breath.pos, breath.info)
            )(breath.pos, breath.info),
            // if (0 == q && 0 < n_rd)
            countingLt0RdGt0,
            // else
            countingLt0MaybeConstGt0
          )(breath.pos, breath.info)
        ),
        Seq()
      )(breath.pos, breath.info)

      // ************* //
      // * merge ifs * //
      // ************* //

      var assumptionSeq = Seq[Stmt]()
      var logSeq = Seq[Stmt]()

      // TODO: Build huge if construct
      if (normalized.counting.isDefined) {
        // 0 != n
        val countingNeq0 = Seqn(
          Seq(
            If(
              LtCmp(zeroLit, normalized.counting.get)(breath.pos, breath.info),
              // if (0 < n)
              countingGt0,
              // if (0 > n)
              countingLt0
            )(breath.pos, breath.info)
          ),
          Seq()
        )(breath.pos, breath.info)

        val countingIf = If(
          EqCmp(zeroLit, normalized.counting.get)(breath.pos, breath.info),
          // if (0 == n)
          countingEq0,
          // if (0 != n)
          countingNeq0
        )(breath.pos, breath.info)

        assumptionSeq ++= Seq(countingIf)
      } else {
        assumptionSeq ++= Seq(countingEq0)
      }

      // ******************* //
      // * log permissions * //
      // ******************* //

      if (normalized.const.isDefined) {
        logSeq :+= getConsCall(-1, normalized.const.get, minus = true)
      }
      if (normalized.predicate.isDefined) {
        logSeq :+= getConsCall(-1, normalized.predicate.get, minus = true)
      }
      if (normalized.counting.isDefined) {
        logSeq :+= getConsCall(-1, normalized.counting.get, minus = true)
      }
      if (normalized.read.isDefined) {
        logSeq :+= getConsCall(-1, normalized.read.get, minus = true)
      }
      if (normalized.wildcard.isDefined) {
        logSeq :+= getConsCall(-1, normalized.wildcard.get, minus = true)
      }

      // **************** //
      // * finish stuff * //
      // **************** //

      Seqn(
        assumptionSeq
          ++ Seq(breath)
          ++ logSeq,
        Seq()
      )(breath.pos, breath.info)
    }
  }

  def normalizeExpression(exp: Exp): NormalizedExpression = {
    NormalizedExpression(Some(LocalVar("q")(Perm)), Some(LocalVar("prd")(Perm)), Some(LocalVar("n")(Perm)), Some(LocalVar("n_rd")(Perm)), None)
  }

  def perm(a: Int, b: Int): FractionalPerm = {
    FractionalPerm(IntLit(a)(), IntLit(b)())()
  }

}

case class NormalizedExpression(const: Option[Exp], predicate: Option[Exp], counting: Option[Exp], read: Option[Exp], wildcard: Option[Exp])