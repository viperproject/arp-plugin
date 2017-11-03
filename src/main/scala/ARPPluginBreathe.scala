/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast.utility.Rewriter.ContextC
import viper.silver.ast._

object ARPPluginBreathe {

  // TODO: rewrite inhale/exhale statements (to if-construct from writeup)
  // TODO: Add inhales/exhales to Log
  // TODO: constrain methodRd further

  def handleInhale(input: Program, inhale: Inhale, ctx: ContextC[Node, String]): Node = {
    inhale
  }

  def handleExhale(input: Program, exhale: Exhale, ctx: ContextC[Node, String]): Node = {
    exhale
  }

  def splitBreathing(breath: Exp): Unit ={

  }

  def normalizeExpression(exp: Exp): Unit = {
    NormalizedExpression(perm(0, 1), 0, 0, 0, 0)
  }

  def perm(a: Int, b: Int): FractionalPerm ={
    FractionalPerm(IntLit(a)(), IntLit(b)())()
  }

}

case class NormalizedExpression(fractionalPerm: FractionalPerm, predicate: Int, counting: Int, read: Int, wildcard: Int)