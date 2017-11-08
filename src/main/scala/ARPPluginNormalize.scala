/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast.{Exp, FractionalPerm, IntLit}

object ARPPluginNormalize {
  def normalizeExpression(exp: Exp): NormalizedExpression = {
//    NormalizedExpression(Some(LocalVar("q")(Perm)), Some(LocalVar("prd")(Perm)), Some(LocalVar("n")(Perm)), Some(LocalVar("n_rd")(Perm)), None)
    NormalizedExpression(Some(perm(0, 1)), Some(IntLit(0)()), Some(IntLit(0)()), Some(IntLit(0)()), None)
  }

  def perm(a: Int, b: Int): FractionalPerm = {
    FractionalPerm(IntLit(a)(), IntLit(b)())()
  }
}

case class NormalizedExpression(const: Option[Exp], predicate: Option[Exp], counting: Option[Exp], read: Option[Exp], wildcard: Option[Exp])
