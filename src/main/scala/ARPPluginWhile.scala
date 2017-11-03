/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.ContextC
import viper.silver.verifier.errors.{ExhaleFailed, LoopInvariantNotEstablished, LoopInvariantNotPreserved}

object ARPPluginWhile {

  def handleWhile(input: Program, w: While, ctx: ContextC[Node, String]): Node = {
    if (w.invs.isEmpty) {
      w
    } else {
      val whileRdName = ARPPluginUtils.getNewNameFor(w, "_rd")
      val newErrTrafo = w.errT + NodeTrafo(w)
      val whilePrime = While(w.cond, Seq(),
        Seqn(
          w.invs.map(i => Inhale(
            ARPPluginUtils.rewriteRd(whileRdName)(i)
          )(i.pos, i.info, i.errT + NodeTrafo(i))) ++
            Seq(w.body) ++
            w.invs.map(i => Exhale(
              ARPPluginUtils.rewriteRd(whileRdName)(i)
            )(i.pos, i.info, i.errT + NodeTrafo(i) + ErrTrafo({
              case ExhaleFailed(_, reason, cached) =>
                LoopInvariantNotPreserved(i, reason, cached)
            }))),
          Seq()
        )(w.pos, w.info, newErrTrafo)
      )(w.pos, w.info, newErrTrafo)

      ctx.noRec(whilePrime)

      Seqn(
        Seq(
          Inhale(ARPPluginUtils.constrainRdExp(whileRdName)(w.pos, w.info, newErrTrafo))(w.pos, w.info, newErrTrafo)
        ) ++
          w.invs.map(i => Exhale(
            ARPPluginUtils.rewriteRd(whileRdName)(i)
          )(i.pos, i.info, i.errT + NodeTrafo(i) + ErrTrafo({
            case ExhaleFailed(_, reason, cached) =>
              LoopInvariantNotEstablished(i, reason, cached)
          }))) ++
          Seq(
            whilePrime
          ) ++
          w.invs.map(i => Inhale(
            ARPPluginUtils.rewriteRd(whileRdName)(i)
          )(i.pos, i.info, i.errT + NodeTrafo(i))),
        Seq(LocalVarDecl(whileRdName, Perm)(w.pos, w.info, newErrTrafo))
      )(w.pos, w.info, newErrTrafo)
    }
  }
}
