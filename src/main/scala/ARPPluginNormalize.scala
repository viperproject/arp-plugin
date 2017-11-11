/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast.{ErrorTrafo, Exp, FractionalPerm, FullPerm, FuncApp, Info, IntLit, NoInfo, NoPerm, NoPosition, Perm, PermAdd, PermDiv, PermMinus, PermMul, PermSub, Position}

object ARPPluginNormalize {

  def normalizeExpression(exp: Exp, rdPerm: (Exp, FuncApp) => NormalizedExpression): Option[NormalizedExpression] = {
    collect(exp, None, rdPerm)
  }

  def collect(exp: Exp, mult: Option[Exp], rdPerm: (Exp, FuncApp) => NormalizedExpression): Option[NormalizedExpression] = {
    exp match {
      case PermMinus(left) => collect(left, Some(PermMinus(mult.getOrElse(IntLit(1)()))()), rdPerm)
      case PermAdd(left, right) => op(collect(left, mult, rdPerm), collect(right, mult, rdPerm), _ +? _)
      case PermSub(left, right) => collect(PermAdd(left, PermMinus(right)())(), mult, rdPerm)
      case PermMul(left, right) => op(collect(left, mult, rdPerm), collect(right, mult, rdPerm), _ *? _)
      case PermDiv(left, right) => op(collect(left, mult, rdPerm), collect(right, mult, rdPerm), _ /? _)
      case i: IntLit => Some(constPerm(i))
      case FractionalPerm(left, right) => op(collect(left, mult, rdPerm), collect(right, mult, rdPerm), _ /? _)
      case p: NoPerm => Some(constPerm(p))
      case p: FullPerm => Some(constPerm(p))
      case f@FuncApp(ARPPluginNaming.rdName, _) => Some(rdPerm(IntLit(1)(), f))
      case f@FuncApp(ARPPluginNaming.rdCountingName, Seq(arg)) => Some(rdcPerm(arg, f))
      case f@FuncApp(ARPPluginNaming.rdWildcardName, _) => Some(wildcardPerm(IntLit(1)(), f))
      case _ => None
    }
  }

  def op(a: Option[NormalizedExpression], b: Option[NormalizedExpression], f: (NormalizedExpression, NormalizedExpression) => Option[NormalizedExpression]): Option[NormalizedExpression] =
    if (a.isDefined && b.isDefined) f(a.get, b.get) else None

  def rdPermFresh(exp: Exp, f: FuncApp): NormalizedExpression = {
    NormalizedExpression(Seq(NormalizedPart(exp, 1, 1, Some(f))), None, None)
  }

  def rdPermOld(exp: Exp, f: FuncApp): NormalizedExpression = {
    NormalizedExpression(Seq(NormalizedPart(exp, 3, 3, Some(f))), None, None)
  }

  def rdPermContext(exp: Exp, f: FuncApp): NormalizedExpression = {
    NormalizedExpression(Seq(NormalizedPart(exp, 4, 4, Some(f))), None, None)
  }

  def rdcPerm(exp: Exp, f: FuncApp): NormalizedExpression = {
    NormalizedExpression(Seq(NormalizedPart(exp, 0, 0, Some(f))), None, None)
  }

  def constPerm(exp: Exp): NormalizedExpression = {
    NormalizedExpression(Seq(), Some(NormalizedPart(exp, 6, 5, None)), None)
  }

  def wildcardPerm(exp: Exp, f: FuncApp): NormalizedExpression = {
    NormalizedExpression(Seq(), None, Some(NormalizedPart(exp, 2, 0, Some(f))))
  }

  case class NormalizedPart(exp: Exp, store: Int, check: Int, unit: Option[Exp]) {
    def setExp(e: Exp): NormalizedPart ={
      NormalizedPart(e, store, check, unit)
    }

    def setStore(s: Int): NormalizedPart ={
      NormalizedPart(exp, s, check, unit)
    }

    def setCheck(c: Int): NormalizedPart ={
      NormalizedPart(exp, store, c, unit)
    }

    def setUnit(u: Option[Exp]): NormalizedPart ={
      NormalizedPart(exp, store, check, u)
    }

    def getTotal(pos: Position, info: Info, errT: ErrorTrafo): Exp = if (unit.isDefined) PermMul(exp, unit.get)(pos, info, errT) else exp
  }

  case class NormalizedExpression(exps: Seq[NormalizedPart], const: Option[NormalizedPart], wildcard: Option[NormalizedPart]) {

    def isnonconst() = exps.nonEmpty || wildcard.isDefined

    def isconst() = !isnonconst()

    def +?(other: NormalizedExpression): Option[NormalizedExpression] = {
      var exps1 = exps
      var exps2 = other.exps
      var newExps = Seq[NormalizedPart]()
      while (exps1.nonEmpty && exps2.nonEmpty) {
        val h1 = exps1.head
        val h2 = exps2.head
        if (h1.store == h2.store) {
          if (h1.check == h2.check) {
            newExps +:= h1.setExp(PermAdd(h1.exp, h2.exp)())
            exps1 = exps1.tail
            exps2 = exps2.tail
          } else if (h1.check < h2.check) {
            newExps +:= h1
            exps1 = exps1.tail
          } else {
            newExps +:= h2
            exps2 = exps2.tail
          }
        } else if (h1.store < h2.store) {
          newExps +:= h1
          exps1 = exps1.tail
        } else {
          newExps +:= h2
          exps2 = exps2.tail
        }
      }
      newExps ++= exps1 ++ exps2

      val newConst =
        if (const.isDefined && other.const.isDefined) {
          Some(const.get.setExp(PermAdd(const.get.exp, other.const.get.exp)()))
        } else if (const.isDefined) {
          const
        } else {
          other.const
        }
      val newWildcard = if (wildcard.isDefined && other.wildcard.isDefined) {
        Some(wildcard.get.setExp(PermAdd(wildcard.get.exp, other.wildcard.get.exp)()))
      } else if (wildcard.isDefined) {
        wildcard
      } else {
        other.wildcard
      }

      Some(NormalizedExpression(newExps, newConst, newWildcard))
    }

    def *?(other: NormalizedExpression): Option[NormalizedExpression] = {
      if (this.isnonconst() && other.isnonconst()) {
        None
      } else {
        val (const, nonconst) = if (other.isconst()) (other, this) else (this, other)
        if (const.const.isEmpty) {
          Some(constPerm(NoPerm()()))
        } else {
          val exp = const.const.get.exp
          def multiply(e: NormalizedPart) = e.setExp(PermMul(e.exp, exp)())
          Some(NormalizedExpression(nonconst.exps.map(e => multiply(e)), nonconst.const.map(e => multiply(e)), nonconst.wildcard.map(e => multiply(e))))
        }
      }
    }

    def /?(other: NormalizedExpression): Option[NormalizedExpression] = {
      if (other.isnonconst() || other.const.isEmpty) {
        None
      } else {
        val exp = other.const.get.exp
        def divide(e: NormalizedPart) = e.setExp(PermDiv(e.exp, exp)())

        Some(NormalizedExpression(exps.map(e => divide(e)), const.map(e => divide(e)), wildcard.map(e => divide(e))))
      }
    }
  }

}