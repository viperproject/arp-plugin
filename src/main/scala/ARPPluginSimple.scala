/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.StrategyBuilder
import viper.silver.plugin.ARPPlugin.TransformedWhile

class ARPPluginSimple(plugin: ARPPlugin) {

  def transform(input: Program): Program = {
    plugin.naming.init(plugin.naming.collectUsedNames(input))
    transformNode(input, input)
  }

  def transformNode[T <: Node](input: Program, toTransform: T): T ={
    val methodPrime = StrategyBuilder.Context[Node, ARPContextSimple]({
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
                plugin.breathe.splitBreathing(p, complete = true, Some(false), {
                  case a: AccessPredicate if isRdCall(a.perm) =>
                    Seq(constrainRdInhale(rdName, transformLoc(method, m, a.loc))(m.pos, m.info))
                  case f@Forall(vars, triggers, Implies(exp, a: AccessPredicate)) =>
                    Seq(Inhale(Forall(vars, triggers.map{case Trigger(exps) => Trigger(exps.map(texp => transformLoc(method, m, texp)))()}, Implies(transformLoc(method, m, exp), constrainRdExp(rdName, transformLoc(method, m, a.loc))(f.pos, f.info))(f.pos, f.info))(f.pos, f.info))(f.pos, f.info))
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
        if (w.info.getUniqueInfo[TransformedWhile].isDefined) {
          w
        } else {
          Seqn(
            Seq(Inhale(plugin.utils.constrainRdExp(rdName)(w.pos, w.info))(w.pos, w.info)) ++
              w.invs.flatMap(inv =>
                plugin.breathe.splitBreathing(inv, complete = true, None, {
                  case a: AccessPredicate if isRdCall(a.perm) => Seq(constrainRdInhale(rdName, a.loc)(w.pos, w.info))
                  case _ => Seq()
                })
              ) ++
              Seq(
                While(w.cond, w.invs.map(plugin.utils.rewriteRdSimple(rdName)), w.body)(w.pos, ConsInfo(w.info, ARPPlugin.TransformedWhile()), NodeTrafo(w))
              ),
            Seq(
              LocalVarDecl(rdName, Perm)(w.pos, w.info)
            )
          )(w.pos, w.info, NodeTrafo(w))
        }
    },
      ARPContextSimple(""),
      {
        case (m: Method, ctx) => ARPContextSimple(plugin.naming.getNameFor(m, m.name, "rd"))
        case (w: While, ctx) if w.info.getUniqueInfo[TransformedWhile].isEmpty => ARPContextSimple(plugin.naming.getNameFor(w, suffix = "while_rd"))
      }
    ).execute[T](toTransform)

    methodPrime
  }

  def constrainRdInhale(rdName: String, loc: LocationAccess)(pos: Position, info: Info, errT: ErrorTrafo = NoTrafos): Stmt = {
    Inhale(constrainRdExp(rdName, loc)(pos, info))(pos, info)
  }

  def constrainRdExp(rdName: String, loc: LocationAccess)(pos: Position, info: Info, errT: ErrorTrafo = NoTrafos): Exp = {
    Implies(
      PermLtCmp(
        NoPerm()(pos, info),
        CurrentPerm(loc)(pos, info)
      )(pos, info),
      PermLtCmp(
        LocalVar(rdName)(Perm, pos, info),
        CurrentPerm(loc)(pos, info)
      )(pos, info)
    )(pos, info)
  }

  def transformLoc[T <: Node](m: Method, mc: MethodCall, loc: T): T = {
    val mapping = m.formalArgs.map(_.name).zip(mc.args).toMap
    StrategyBuilder.Slim[Node]({
      case l@LocalVar(name) => mapping.getOrElse(name, l) // might not be in mapping if quantifier
    }).execute[T](loc)
  }

  def isRdCall(e: Exp): Boolean = {
    e match {
      case FuncApp(plugin.naming.rdName, _) => true
      case _ => false
    }
  }

  case class ARPContextSimple(rdName: String)

}
