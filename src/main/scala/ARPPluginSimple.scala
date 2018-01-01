/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.StrategyBuilder

import scala.collection.immutable.{HashMap, HashSet}

class ARPPluginSimple(plugin: ARPPlugin) {

  def transform(input: Program): Program = {
    plugin.naming.init(plugin.naming.collectUsedNames(input))

    val inputPrime = StrategyBuilder.Context[Node, ARPContextSimple]({
      case (m: Method, ctx) =>
        val rdName = plugin.naming.getNewNameFor(m, m.name, "rd")
        Method(
          m.name,
          m.formalArgs :+ LocalVarDecl(rdName, Perm)(m.pos, m.info),
          m.formalReturns,
          plugin.utils.constrainRdExp(rdName)(m.pos, m.info) +: m.pres,
          m.posts,
          m.body
        )(m.pos, m.info, NodeTrafo(m))
      case (f@FuncApp(plugin.naming.rdName, _), ctx) => LocalVar(ctx.c.rdName)(Perm, f.pos, f.info, NodeTrafo(f))
      case (m: MethodCall, ctx) =>
        val rdName = plugin.naming.getNewNameFor(m, m.methodName, "call_rd")
        val method = plugin.utils.getMethod(input, m.methodName).get
        ctx.noRec(
          Seqn(
            Seq(Inhale(plugin.utils.constrainRdExp(rdName)(m.pos, m.info))(m.pos, m.info)) ++
              method.pres.flatMap(p =>
                plugin.breathe.splitBreathing(p, Some(false), {
                  case a: AccessPredicate if isRdCall(a.perm) => Seq(Inhale(PermLtCmp(
                    LocalVar(rdName)(Perm, m.pos, m.info),
                    CurrentPerm(transformLoc(method, m, a.loc))(m.pos, m.info)
                  )(m.pos, m.info))(m.pos, m.info))
                  case _ => Seq()
                })
              ) ++
              Seq(
                MethodCall(m.methodName, m.args :+ LocalVar(rdName)(Perm, m.pos, m.info), m.targets)(m.pos, m.info, NodeTrafo(m))
              ),
            Seq(
              LocalVarDecl(rdName, Perm)(m.pos, m.info)
            )
          )(m.pos, m.info, NodeTrafo(m))
        )
      case (w: While, ctx) =>
        val rdName = plugin.naming.getNewNameFor(w, suffix = "while_rd")
        ctx.noRec(
          Seqn(
            Seq(Inhale(plugin.utils.constrainRdExp(rdName)(w.pos, w.info))(w.pos, w.info)) ++
              w.invs.flatMap(inv =>
                plugin.breathe.splitBreathing(inv, None, {
                  case a: AccessPredicate if isRdCall(a.perm) => Seq(Inhale(PermLtCmp(
                    LocalVar(rdName)(Perm, w.pos, w.info),
                    CurrentPerm(a.loc)(w.pos, w.info)
                  )(w.pos, w.info))(w.pos, w.info))
                  case _ => Seq()
                })
              ) ++
              Seq(
                While(w.cond, w.invs.map(plugin.utils.rewriteRdSimple(rdName)), w.body)(w.pos, w.info, NodeTrafo(w))
              ),
            Seq(
              LocalVarDecl(rdName, Perm)(w.pos, w.info)
            )
          )(w.pos, w.info, NodeTrafo(w))
        )
    },
      ARPContextSimple(""),
      {
        case (m: Method, ctx) => ARPContextSimple(plugin.naming.getNameFor(m, m.name, "rd"))
      }
    ).execute[Program](input)

    inputPrime
  }

  def transformLoc(m: Method, mc: MethodCall, loc: LocationAccess): LocationAccess ={
    val mapping = m.formalArgs.map(_.name).zip(mc.args).toMap
    StrategyBuilder.Slim[Node]({
      case LocalVar(name) => mapping(name)
    }).execute[LocationAccess](loc)
  }

  def isRdCall(e: Exp): Boolean ={
    e match {
      case FuncApp(plugin.naming.rdName, _) => true
      case _ => false
    }
  }

  case class ARPContextSimple(rdName: String)

}
