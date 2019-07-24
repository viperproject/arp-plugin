// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin

import viper.silver.ast.utility.rewriter.StrategyBuilder
import viper.silver.ast.{Add, CondExp, Div, DomainBinExp, DomainFuncApp, EpsilonPerm, ErrorTrafo, Exp, FieldAccess, FractionalPerm, FullPerm, FuncApp, Info, IntLit, IntPermMul, LabelledOld, LocalVar, LtCmp, Minus, Mul, NoPerm, NoTrafos, Node, NodeTrafo, Perm, PermAdd, PermDiv, PermExp, PermLtCmp, PermMinus, PermMul, PermSub, Position, Sub, WildcardPerm}
import viper.silver.plugin.ARPPluginNormalize.{NormalizedExpression, NormalizedPart}
import viper.silver.verifier.errors.Internal
import viper.silver.verifier.reasons.FeatureUnsupported

class ARPPluginNormalize(plugin: ARPPlugin) {

  def normalizeExpression(exp: Exp, rdPerm: (Exp, FuncApp) => NormalizedExpression, ignoreErrors: Boolean = false): Option[NormalizedExpression] = {
    collect(exp, rdPerm, ignoreErrors)
  }

  def collect(exp: Exp, rdPerm: (Exp, FuncApp) => NormalizedExpression, ignoreErrors: Boolean = false): Option[NormalizedExpression] = {
    def recursive(e: Exp) = collect(e, rdPerm, ignoreErrors)

    exp match {
      case PermMinus(left) => op(recursive(left), Some(constPerm(IntLit(-1)(left.pos, left.info))), _ *? _, exp)
      case PermAdd(left, right) => op(recursive(left), recursive(right), _ +? _, exp)
      case PermSub(left, right) => recursive(PermAdd(left, PermMinus(right)(right.pos, right.info, NodeTrafo(right)))(left.pos, left.info, NodeTrafo(left)))
      case PermMul(left, right) => op(recursive(left), recursive(right), _ *? _, exp)
      case IntPermMul(left, right) => op(recursive(left), recursive(right), _ *? _, exp)
      case PermDiv(left, right) => op(recursive(left), recursive(right), _ /? _, exp)
      case Minus(left) => op(recursive(left), Some(constPerm(IntLit(-1)(left.pos, left.info))), _ *? _, exp)
      case Add(left, right) => op(recursive(left), recursive(right), _ +? _, exp)
      case Sub(left, right) => recursive(PermAdd(left, PermMinus(right)(right.pos, right.info, NodeTrafo(right)))())
      case Mul(left, right) => op(recursive(left), recursive(right), _ *? _, exp)
      case Div(left, right) => op(recursive(left), recursive(right), _ /? _, exp)
      case i: IntLit => Some(constPerm(i))
      case FractionalPerm(left, right) => op(recursive(left), recursive(right), _ /? _, exp)
      case p: NoPerm => Some(constPerm(p))
      case p: FullPerm => Some(constPerm(p))
      case p: WildcardPerm =>
        Some(wildcardPerm(IntLit(1)(), FuncApp(plugin.naming.rdWildcardName, Seq())(p.pos, p.info, Perm, NoTrafos)))
      case p: EpsilonPerm =>
        Some(rdcPerm(IntLit(1)(), FuncApp(plugin.naming.rdCountingName, Seq())(p.pos, p.info, Perm, NoTrafos)))
      case l@LocalVar(name, _) => Some(constPerm(l))
      case f: FieldAccess => Some(constPerm(f))
      case LabelledOld(l: LocalVar, _) => Some(constPerm(l))
      case l@LabelledOld(fa: FieldAccess, _) => Some(constPerm(l))
      case f@FuncApp(plugin.naming.rdName, _) => Some(rdPerm(IntLit(1)(), f))
      case f@FuncApp(plugin.naming.rdCountingName, Seq(arg)) => Some(rdcPerm(arg, FuncApp(plugin.naming.rdEpsilonName, Seq())(f.pos, f.info, f.typ, NodeTrafo(f))))
      case f@FuncApp(plugin.naming.rdEpsilonName, _) => Some(rdcPerm(IntLit(1)(), f))
      case f@FuncApp(plugin.naming.rdTokenFresh, args) => Some(tokenFreshPerm(IntLit(1)(), FuncApp(plugin.naming.rdToken, args)(f.pos, f.info, f.typ, NodeTrafo(f))))
      case f@FuncApp(plugin.naming.rdToken, _) => Some(tokenPerm(IntLit(1)(), f))
      case f@FuncApp(plugin.naming.rdWildcardName, _) => Some(wildcardPerm(IntLit(1)(), f))
      case f@FuncApp(plugin.naming.rdGlobalName, _) => Some(globalPerm(IntLit(1)(), f))
      case f: FuncApp => Some(constPerm(f))
      case f: DomainFuncApp => Some(constPerm(f))
      case e if !containsNonConst(e) => Some(constPerm(e))
      case _ if ignoreErrors => None
      case default =>
        plugin.reportError(Internal(default, FeatureUnsupported(default, "Can't normalize expression. " + default.getClass)))
        None
    }
  }

  def containsNonConst(exp: Exp): Boolean = {
    var nonConst = false

    StrategyBuilder.SlimVisitor[Node]({
      case FuncApp(plugin.naming.rdName, _) => nonConst = true
      case FuncApp(plugin.naming.rdCountingName, Seq(_)) => nonConst = true
      case FuncApp(plugin.naming.rdWildcardName, _) => nonConst = true
      case _ =>
    }).visit(exp)

    nonConst
  }

  def op(a: Option[NormalizedExpression], b: Option[NormalizedExpression], f: (NormalizedExpression, NormalizedExpression) => Option[NormalizedExpression], exp: Exp): Option[NormalizedExpression] =
    if (a.isDefined && b.isDefined) {
      val result = f(a.get, b.get)
      if (result.isEmpty) {
        plugin.reportError(Internal(exp, FeatureUnsupported(exp, "Nonlinear expression")))
      }
      result
    } else {
      None
    }

  def rdPermFresh(exp: Exp, f: FuncApp): NormalizedExpression = {
    NormalizedExpression(Seq(NormalizedPart(exp, 1, 1, Some(f))), None, None)
  }

  def rdPermOld(exp: Exp, f: FuncApp): NormalizedExpression = {
    NormalizedExpression(Seq(NormalizedPart(exp, 3, 3, Some(f))), None, None)
  }

  def rdPermContext(exp: Exp, f: FuncApp): NormalizedExpression = {
    NormalizedExpression(Seq(NormalizedPart(exp, 4, 4, Some(f))), None, None)
  }

  def tokenFreshPerm(exp: Exp, f: FuncApp): NormalizedExpression = {
    NormalizedExpression(Seq(NormalizedPart(exp, 3, 1, Some(f))), None, None)
  }

  def tokenPerm(exp: Exp, f: FuncApp): NormalizedExpression = {
    NormalizedExpression(Seq(NormalizedPart(exp, 3, 4, Some(f))), None, None)
  }

  def rdcPerm(exp: Exp, f: FuncApp): NormalizedExpression = {
    NormalizedExpression(Seq(NormalizedPart(exp, 0, 0, Some(f))), None, None)
  }

  def globalPerm(exp: Exp, f: FuncApp): NormalizedExpression = {
    NormalizedExpression(Seq(NormalizedPart(exp, 5, 5, Some(f))), None, None)
  }

  def constPerm(exp: Exp): NormalizedExpression = {
    NormalizedExpression(Seq(), Some(NormalizedPart(exp, 6, 5, None)), None)
  }

  def wildcardPerm(exp: Exp, f: FuncApp): NormalizedExpression = {
    NormalizedExpression(Seq(), None, Some(NormalizedPart(exp, 2, 0, Some(f))))
  }
}

object ARPPluginNormalize {

  case class NormalizedPart(exp: Exp, store: Int, check: Int, unit: Option[Exp]) {
    def setExp(e: Exp): NormalizedPart = {
      NormalizedPart(e, store, check, unit)
    }

    def setStore(s: Int): NormalizedPart = {
      NormalizedPart(exp, s, check, unit)
    }

    def setCheck(c: Int): NormalizedPart = {
      NormalizedPart(exp, store, c, unit)
    }

    def setUnit(u: Option[Exp]): NormalizedPart = {
      NormalizedPart(exp, store, check, u)
    }

    def getAbsTotal(plugin: ARPPlugin)(pos: Position, info: Info, errT: ErrorTrafo): Exp = {
      def negate(e: Exp): Exp = {
        e match {
          case Minus(ee) => ee
          case PermMinus(ee) => ee
          case IntLit(x) => IntLit(-x)(e.pos, e.info, e.errT)
          case default if plugin.utils.isPermExp(default) => PermMinus(default)(e.pos, e.info, e.errT)
          case default => Minus(default)(e.pos, e.info, e.errT)
        }
      }

      val simplified = plugin.utils.simplify(exp)
      val absVal = simplified match {
        case IntLit(x) if x >= 0 => simplified
        case IntLit(x) if x < 0 => negate(simplified)
        case PermDiv(IntLit(x), IntLit(y)) if (x >= 0) == (y >= 0) => simplified
        case PermDiv(IntLit(x), IntLit(y)) if (x >= 0) != (y >= 0) => negate(simplified)
        case FractionalPerm(IntLit(x), IntLit(y)) if (x >= 0) == (y >= 0) => simplified
        case FractionalPerm(IntLit(x), IntLit(y)) if (x >= 0) != (y >= 0) => negate(simplified)
        case FullPerm() => simplified
        case NoPerm() => simplified
        case default if plugin.utils.isPermExp(default) =>
          CondExp(
            PermLtCmp(default, plugin.utils.getZeroEquivalent(default))(pos, info, errT),
            negate(default),
            default
          )(pos, info, errT)
        case default =>
          CondExp(
            LtCmp(default, plugin.utils.getZeroEquivalent(default))(pos, info, errT),
            negate(default),
            default
          )(pos, info, errT)
      }
      if (unit.isDefined) {
        absVal match {
          case IntLit(x) if x == 1 => unit.get
          case default if plugin.utils.isPermExp(default) => PermMul(default, unit.get)(pos, info, errT)
          case default => IntPermMul(default, unit.get)(pos, info, errT)
        }
      } else {
        absVal
      }
    }

    def getTotal(plugin: ARPPlugin)(pos: Position, info: Info, errT: ErrorTrafo): Exp = {
      val simplified = plugin.utils.simplify(exp)
      if (unit.isDefined) {
        simplified match {
          case IntLit(x) if x == 1 => unit.get
          case default if plugin.utils.isPermExp(default) => PermMul(default, unit.get)(pos, info, errT)
          case default => IntPermMul(default, unit.get)(pos, info, errT)
        }
      } else {
        simplified
      }
    }
  }

  case class NormalizedExpression(exps: Seq[NormalizedPart], const: Option[NormalizedPart], wildcard: Option[NormalizedPart]) {

    def isnonconst() = exps.nonEmpty || wildcard.isDefined

    def isconst() = !isnonconst()

    def +?(other: NormalizedExpression): Option[NormalizedExpression] = {
      def add(a: Exp, b: Exp): Exp = {
        if (a.typ == Perm && b.typ == Perm) {
          PermAdd(a, b)()
        } else {
          Add(a, b)()
        }
      }

      if (wildcard.isDefined || other.wildcard.isDefined) {
        None
      } else {
        var exps1 = exps
        var exps2 = other.exps
        var newExps = Seq[NormalizedPart]()
        while (exps1.nonEmpty && exps2.nonEmpty) {
          val h1 = exps1.head
          val h2 = exps2.head
          if (h1.store == h2.store) {
            if (h1.check == h2.check) {
              newExps :+= h1.setExp(add(h1.exp, h2.exp))
              exps1 = exps1.tail
              exps2 = exps2.tail
            } else if (h1.check < h2.check) {
              newExps :+= h1
              exps1 = exps1.tail
            } else {
              newExps :+= h2
              exps2 = exps2.tail
            }
          } else if (h1.store < h2.store) {
            newExps :+= h1
            exps1 = exps1.tail
          } else {
            newExps :+= h2
            exps2 = exps2.tail
          }
        }
        newExps ++= exps1 ++ exps2

        val newConst =
          if (const.isDefined && other.const.isDefined) {
            Some(const.get.setExp(add(const.get.exp, other.const.get.exp)))
          } else if (const.isDefined) {
            const
          } else {
            other.const
          }
        val newWildcard = if (wildcard.isDefined && other.wildcard.isDefined) {
          Some(wildcard.get.setExp(add(wildcard.get.exp, other.wildcard.get.exp)))
        } else if (wildcard.isDefined) {
          wildcard
        } else {
          other.wildcard
        }

        Some(NormalizedExpression(newExps, newConst, newWildcard))
      }
    }

    def *?(other: NormalizedExpression): Option[NormalizedExpression] = {
      if (this.isnonconst() && other.isnonconst()) {
        None
      } else {
        val (const, nonconst) = if (other.isconst()) (other, this) else (this, other)
        val exp = const.const.get.exp

        def multiply(e: NormalizedPart): NormalizedPart = {
          if (e.exp.typ == Perm && exp.typ == Perm) {
            e.setExp(PermMul(e.exp, exp)())
          } else if (exp.typ == Perm) {
            e.setExp(IntPermMul(e.exp, exp)())
          } else if (e.exp.typ == Perm) {
            e.setExp(IntPermMul(exp, e.exp)())
          } else {
            e.setExp(Mul(e.exp, exp)())
          }
        }

        Some(NormalizedExpression(nonconst.exps.map(e => multiply(e)), nonconst.const.map(e => multiply(e)), nonconst.wildcard.map(e => multiply(e))))
      }
    }

    def /?(other: NormalizedExpression): Option[NormalizedExpression] = {
      if (other.isnonconst() || other.const.isEmpty || wildcard.isDefined || other.wildcard.isDefined) {
        None
      } else {
        val exp = other.const.get.exp

        def divide(e: NormalizedPart): NormalizedPart = {
          if (e.exp.typ == Perm && exp.typ == Perm) {
            e.setExp(PermDiv(e.exp, exp)())
          } else {
            e.setExp(FractionalPerm(e.exp, exp)())
          }
        }

        Some(NormalizedExpression(exps.map(e => divide(e)), const.map(e => divide(e)), wildcard.map(e => divide(e))))
      }
    }
  }

}