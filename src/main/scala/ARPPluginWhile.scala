/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast.{ErrTrafo, _}
import viper.silver.ast.utility.Rewriter.ContextC
import viper.silver.plugin.ARPPlugin.{ARPContext, TransformedWhile, WasInvariantInside, WasInvariantOutside}
import viper.silver.verifier.errors.{WhileFailed, _}

class ARPPluginWhile(plugin: ARPPlugin) {

  def handleWhile(input: Program, w: While, ctx: ContextC[Node, ARPContext]): Node = {
    if (w.info.getUniqueInfo[TransformedWhile].isDefined) {
      w
    } else {
      val whileRdName = plugin.naming.getNameFor(w, suffix = "while_rd")
      val condName = plugin.naming.getNewName(suffix = "while_cond")
      val condVar = LocalVar(condName)(Bool, w.cond.pos, w.cond.info, w.cond.errT + NodeTrafo(w.cond))
      val whileStartLabelName = plugin.naming.getNewName("while", "start_label")
      val whileEndLabelName = plugin.naming.getNewName("while", "end_label")
      val newLogName = plugin.naming.getNameFor(w, suffix = "while_log")

      val arpLogDomain = plugin.utils.getDomain(input, plugin.naming.logDomainName).get
      val arpLogType = DomainType(arpLogDomain, Map[TypeVar, Type]() /* TODO: What's the deal with this? */)
      val arpLogNil = plugin.utils.getDomainFunction(arpLogDomain, plugin.naming.logDomainNil).get

      val whilePrime = While(condVar, Seq(),
        Seqn(
          Seq(
            LocalVarAssign(
              LocalVar(newLogName)(arpLogType, w.pos, w.info, w.errT + NodeTrafo(w)),
              DomainFuncApp(arpLogNil, Seq(), Map[TypeVar, Type]())(w.pos, w.info, w.errT + NodeTrafo(w))
            )(w.cond.pos, w.cond.info)
          ) ++
            w.invs.map(i => Inhale(i)(i.pos, ConsInfo(i.info, WasInvariantInside()), i.errT + NodeTrafo(i) + ErrTrafo({
              case InhaleFailed(_, reason, cached) =>
                WhileFailed(i, reason, cached)
            }))) ++
            Seq(
              Inhale(w.cond)(w.cond.pos, w.cond.info, w.cond.errT + NodeTrafo(w.cond) + ErrTrafo({
                case InhaleFailed(_, reason, cached) =>
                  WhileFailed(w.cond, reason, cached)
              })),
              w.body,
              LocalVarAssign(condVar, w.cond)(w.cond.pos, w.cond.info, w.cond.errT + NodeTrafo(w.cond) + ErrTrafo({
                case AssignmentFailed(_, reason, cached) =>
                  WhileFailed(w.cond, reason, cached)
              })),
              Label(whileEndLabelName, Seq())(w.pos, w.info)
            ) ++
            w.invs.map(i => Exhale(
              plugin.utils.rewriteOldExpr(whileEndLabelName, oldLabel = false)(i)
            )(i.pos, ConsInfo(i.info, WasInvariantInside()), i.errT + NodeTrafo(i) + ErrTrafo({
              case ExhaleFailed(_, reason, cached) =>
                LoopInvariantNotPreserved(i, reason, cached)
            }))),
          Seq(
            Label(whileEndLabelName, Seq())(w.pos, w.info),
            LocalVarDecl(newLogName, arpLogType)(w.pos, w.info)
          )
        )(w.pos, w.info, w.errT + NodeTrafo(w))
      )(w.pos, ConsInfo(w.info, TransformedWhile()), w.errT + NodeTrafo(w))

      plugin.naming.storeName(whileRdName, whilePrime, suffix = "while_rd")
      plugin.naming.storeName(newLogName, whilePrime, suffix = "while_log")

      Seqn(
        Seq(
          Inhale(plugin.utils.constrainRdExp(whileRdName)(w.pos, w.info, w.errT + NodeTrafo(w)))(w.pos, w.info),
          LocalVarAssign(condVar, w.cond)(w.cond.pos, w.cond.info, w.cond.errT + NodeTrafo(w.cond) + ErrTrafo({
            case AssignmentFailed(_, reason, cached) =>
              WhileFailed(w.cond, reason, cached)
          })),
          Label(whileStartLabelName, Seq())(w.pos, w.info, w.errT + NodeTrafo(w))
        ) ++
          w.invs.map(i => Exhale(
            plugin.utils.rewriteOldExpr(whileStartLabelName, oldLabel = false)(i)
          )(i.pos, ConsInfo(i.info, WasInvariantOutside()), i.errT + NodeTrafo(i) + ErrTrafo({
            case ExhaleFailed(_, reason, cached) =>
              LoopInvariantNotEstablished(i, reason, cached)
          }))) ++
          Seq(
            whilePrime
          ) ++
          w.invs.map(i => Inhale(i)(i.pos, ConsInfo(i.info, WasInvariantOutside()), i.errT + NodeTrafo(i) + ErrTrafo({
            case InhaleFailed(_, reason, cached) =>
              WhileFailed(i, reason, cached)
          }))) ++
          Seq(Inhale(Not(w.cond)(w.pos, w.info, w.errT + NodeTrafo(w)))(w.pos, w.info, w.errT + NodeTrafo(w))),
        Seq(
          LocalVarDecl(whileRdName, Perm)(w.pos, w.info, w.errT + NodeTrafo(w)),
          LocalVarDecl(condName, Bool)(w.pos, w.info, w.errT + NodeTrafo(w)),
          Label(whileStartLabelName, Seq())(w.pos, w.info, w.errT + NodeTrafo(w))
        )
      )(w.pos, w.info, w.errT + NodeTrafo(w))
    }
  }
}
