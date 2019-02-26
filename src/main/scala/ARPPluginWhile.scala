// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin

import viper.silver.ast.{ErrTrafo, _}
import viper.silver.ast.utility.Rewriter.ContextC
import viper.silver.plugin.ARPPlugin.{ARPContext, TransformedWhile, WasInvariantInside, WasInvariantOutside}
import viper.silver.verifier.AbstractVerificationError
import viper.silver.verifier.errors.{WhileFailed, _}

class ARPPluginWhile(plugin: ARPPlugin) {

  def handleWhile(input: Program, w: While, ctx: ContextC[Node, ARPContext]): Node = {
    if (w.info.getUniqueInfo[TransformedWhile].isDefined) {
      w
    } else {
      val whileRdName = plugin.naming.getNewNameFor(w, suffix = "while_rd")
      val condName = plugin.naming.getNewName(suffix = "while_cond")
      val condVar = LocalVar(condName)(Bool, w.cond.pos, w.cond.info, NodeTrafo(w.cond))
      val whileStartLabelName = plugin.naming.getNewName("while", "start_label")
      val whileEndLabelName = plugin.naming.getNewName("while", "end_label")
      val newLogName = plugin.naming.getNewNameFor(w, suffix = "while_log")

      val arpLogType = plugin.utils.getARPLogType(input)
      val arpLogNil = plugin.utils.getARPLogFunction(input, plugin.naming.logDomainNil)

      val whilePrime = While(condVar, Seq(),
        Seqn(
          Seq(
            LocalVarAssign(
              LocalVar(newLogName)(arpLogType, w.pos, w.info, NodeTrafo(w)),
              DomainFuncApp(arpLogNil, Seq(), Map[TypeVar, Type]())(w.pos, w.info, NodeTrafo(w))
            )(w.cond.pos, w.cond.info)
          ) ++
            w.invs.map(i => Inhale(i)(i.pos, ConsInfo(i.info, WasInvariantInside()), ErrTrafo({
              case InhaleFailed(_, reason, cached) =>
                WhileFailed(i, reason, cached)
              case error: AbstractVerificationError => error.withNode(i).asInstanceOf[AbstractVerificationError]
            }))) ++
            Seq(
              Inhale(w.cond)(w.cond.pos, w.cond.info, ErrTrafo({
                case InhaleFailed(_, reason, cached) =>
                  WhileFailed(w.cond, reason, cached)
                case error: AbstractVerificationError => error.withNode(w.cond).asInstanceOf[AbstractVerificationError]
              })),
              w.body,
              Label(whileEndLabelName, Seq())(w.pos, w.info)
            ) ++
            w.invs.map(i => Exhale(
              plugin.utils.rewriteOldExpr(input, whileEndLabelName, oldLabel = false)(i)
            )(i.pos, ConsInfo(i.info, WasInvariantInside()), ErrTrafo({
              case ExhaleFailed(_, reason, cached) =>
                LoopInvariantNotPreserved(i, reason, cached)
              case error: AbstractVerificationError => error.withNode(i).asInstanceOf[AbstractVerificationError]
            }))) ++
            Seq(
              LocalVarAssign(condVar, LabelledOld(w.cond, whileEndLabelName)(w.cond.pos, w.cond.info))(w.cond.pos, w.cond.info, ErrTrafo({
                case AssignmentFailed(_, reason, cached) =>
                  WhileFailed(w.cond, reason, cached)
                case error: AbstractVerificationError => error.withNode(w.cond).asInstanceOf[AbstractVerificationError]
              }))
            ),
          Seq(
            Label(whileEndLabelName, Seq())(w.pos, w.info),
            LocalVarDecl(newLogName, arpLogType)(w.pos, w.info)
          )
        )(w.pos, w.info, NodeTrafo(w))
      )(w.pos, ConsInfo(w.info, TransformedWhile()), NodeTrafo(w))

      plugin.naming.storeName(whileRdName, whilePrime, suffix = "while_rd")
      plugin.naming.storeName(newLogName, whilePrime, suffix = "while_log")

      Seqn(
        Seq(
          Inhale(plugin.utils.constrainRdExp(whileRdName)(w.pos, w.info, NodeTrafo(w)))(w.pos, w.info),
          Label(whileStartLabelName, Seq())(w.pos, w.info, NodeTrafo(w))
        ) ++
          w.invs.map(i => Exhale(
            plugin.utils.rewriteOldExpr(input, whileStartLabelName, oldLabel = false)(i)
          )(i.pos, ConsInfo(i.info, WasInvariantOutside()), ErrTrafo({
            case ExhaleFailed(_, reason, cached) =>
              LoopInvariantNotEstablished(i, reason, cached)
            case error: AbstractVerificationError => error.withNode(i).asInstanceOf[AbstractVerificationError]
          }))) ++
          Seq(
            LocalVarAssign(condVar, LabelledOld(w.cond, whileStartLabelName)(w.cond.pos, w.cond.info))(w.cond.pos, w.cond.info, ErrTrafo({
              case AssignmentFailed(_, reason, cached) =>
                WhileFailed(w.cond, reason, cached)
              case error: AbstractVerificationError => error.withNode(w.cond).asInstanceOf[AbstractVerificationError]
            }))
          ) ++
          Seq(
            whilePrime
          ) ++
          w.invs.map(i => Inhale(i)(i.pos, ConsInfo(i.info, WasInvariantOutside()), ErrTrafo({
            case InhaleFailed(_, reason, cached) =>
              WhileFailed(i, reason, cached)
            case error: AbstractVerificationError => error.withNode(i).asInstanceOf[AbstractVerificationError]
          }))) ++
          Seq(Inhale(Not(w.cond)(w.pos, w.info, NodeTrafo(w)))(w.pos, w.info, NodeTrafo(w))),
        Seq(
          LocalVarDecl(whileRdName, Perm)(w.pos, w.info, NodeTrafo(w)),
          LocalVarDecl(condName, Bool)(w.pos, w.info, NodeTrafo(w)),
          Label(whileStartLabelName, Seq())(w.pos, w.info, NodeTrafo(w))
        )
      )(w.pos, w.info, NodeTrafo(w))
    }
  }
}
