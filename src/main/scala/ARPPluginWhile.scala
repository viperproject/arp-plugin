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
      val whileRdName = ARPPluginNaming.getNameFor(w, suffix = "while_rd")
      val condName = ARPPluginNaming.getNewName(suffix = "while_cond")
      val newErrTrafo = w.errT + NodeTrafo(w)
      val condVar = LocalVar(condName)(Bool, w.pos, w.info, newErrTrafo)

      val whilePrime = While(condVar, Seq(),
        Seqn(
          w.invs.map(i => Inhale(i)(i.pos, i.info, i.errT + NodeTrafo(i))) ++
            Seq(
              Inhale(w.cond)(w.pos, w.info, newErrTrafo),
              w.body,
              LocalVarAssign(condVar, w.cond)()
            ) ++
            w.invs.map(i => Exhale(i)(i.pos, i.info, i.errT + NodeTrafo(i) + ErrTrafo({
              case ExhaleFailed(_, reason, cached) =>
                LoopInvariantNotPreserved(i, reason, cached)
            }))),
          Seq()
        )(w.pos, w.info, newErrTrafo)
      )(w.pos, w.info, newErrTrafo)

      ARPPluginNaming.storeName(whilePrime, whileRdName)

      Seqn(
        Seq(
          Inhale(ARPPluginUtils.constrainRdExp(whileRdName)(w.pos, w.info, newErrTrafo))(w.pos, w.info, newErrTrafo),
          LocalVarAssign(condVar, w.cond)(w.pos, w.info, newErrTrafo)
        ) ++
          w.invs.map(i => Exhale(i)(i.pos, i.info, i.errT + NodeTrafo(i) + ErrTrafo({
            case ExhaleFailed(_, reason, cached) =>
              LoopInvariantNotEstablished(i, reason, cached)
          }))) ++
          Seq(
            whilePrime
          ) ++
          w.invs.map(i => Inhale(i)(i.pos, i.info, i.errT + NodeTrafo(i))) ++
          Seq(Inhale(Not(w.cond)(w.pos, w.info, newErrTrafo))(w.pos, w.info, newErrTrafo)),
        Seq(
          LocalVarDecl(whileRdName, Perm)(w.pos, w.info, newErrTrafo),
          LocalVarDecl(condName, Bool)(w.pos, w.info, newErrTrafo)
        )
      )(w.pos, w.info, newErrTrafo)
    }
  }
}
