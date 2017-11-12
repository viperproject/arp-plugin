/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.ContextC
import viper.silver.verifier.errors.{ExhaleFailed, LoopInvariantNotEstablished, LoopInvariantNotPreserved}

class ARPPluginWhile(plugin: ARPPlugin) {

  def handleWhile(input: Program, w: While, ctx: ContextC[Node, String]): Node = {
    if (w.invs.isEmpty) {
      w
    } else {
      val whileRdName = plugin.naming.getNameFor(w, suffix = "while_rd")
      val condName = plugin.naming.getNewName(suffix = "while_cond")
      val newErrTrafo = w.errT + NodeTrafo(w)
      val condVar = LocalVar(condName)(Bool, w.pos, w.info, newErrTrafo)
      val whileStartLabelName = plugin.naming.getNewName("while", "start_label")
      val whileEndLabelName = plugin.naming.getNewName("while", "end_label")

      val whilePrime = While(condVar, Seq(),
        Seqn(
          w.invs.map(i => Inhale(i)(i.pos, i.info, i.errT + NodeTrafo(i))) ++
            Seq(
              Inhale(w.cond)(w.pos, w.info, newErrTrafo),
              w.body,
              LocalVarAssign(condVar, w.cond)(),
              Label(whileEndLabelName, Seq())(w.pos, w.info, newErrTrafo)
            ) ++
            w.invs.map(i => Exhale(
              plugin.utils.rewriteOldExpr(whileEndLabelName, oldLabel = false)(i)
            )(i.pos, i.info, i.errT + NodeTrafo(i) + ErrTrafo({
              case ExhaleFailed(_, reason, cached) =>
                LoopInvariantNotPreserved(i, reason, cached)
            }))),
          Seq(
            Label(whileEndLabelName, Seq())(w.pos, w.info, newErrTrafo)
          )
        )(w.pos, w.info, newErrTrafo)
      )(w.pos, w.info, newErrTrafo)

      plugin.naming.storeName(whilePrime, whileRdName)

      Seqn(
        Seq(
          Inhale(plugin.utils.constrainRdExp(whileRdName)(w.pos, w.info, newErrTrafo))(w.pos, w.info, newErrTrafo),
          LocalVarAssign(condVar, w.cond)(w.pos, w.info, newErrTrafo),
          Label(whileStartLabelName, Seq())(w.pos, w.info, newErrTrafo)
        ) ++
          w.invs.map(i => Exhale(
            plugin.utils.rewriteOldExpr(whileStartLabelName, oldLabel = false)(i)
          )(i.pos, i.info, i.errT + NodeTrafo(i) + ErrTrafo({
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
          LocalVarDecl(condName, Bool)(w.pos, w.info, newErrTrafo),
          Label(whileStartLabelName, Seq())(w.pos, w.info, newErrTrafo)
        )
      )(w.pos, w.info, newErrTrafo)
    }
  }
}
