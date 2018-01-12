/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast.utility.Rewriter.{ContextC, StrategyBuilder, Traverse}
import viper.silver.ast._
import viper.silver.plugin.ARPPlugin.{ARPContext, WasCallCondition, WasMethodCondition}
import viper.silver.verifier.AbstractVerificationError
import viper.silver.verifier.errors._

import scala.collection.immutable.HashMap

class ARPPluginMethods(plugin: ARPPlugin) {

  // add rd argument to method
  // init ARPLog
  // desugar method contracts into explicit inhales/exhales
  def handleMethod(input: Program, m: Method, ctx: ContextC[Node, ARPContext]): Node = {
    val methodName = plugin.naming.getNewNameFor(m, m.name, "ARP_TRANSFORMED")
    val methodRdName = plugin.naming.getNewNameFor(m, m.name, "rd")
    val methodStartLabelName = plugin.naming.getNewNameFor(m, m.name, "start_label")
    val methodEndLabelName = plugin.naming.getNewName(m.name, "end_label")
    val logName = plugin.naming.getNewNameFor(m, m.name, "log")
    val rdArg = LocalVarDecl(methodRdName, Perm)(m.pos, m.info)
    val arpLogType = plugin.utils.getARPLogType(input)
    val arpLogNil = plugin.utils.getARPLogFunction(input, plugin.naming.logDomainNil)

    Method(
      methodName,
      // add rd argument
      m.formalArgs :+ rdArg,
      m.formalReturns,
      Seq(),
      Seq(),
      m.body.map(b => {
        Seqn(
          Seq(
            // init arp perm log
            LocalVarAssign(
              LocalVar(logName)(arpLogType, b.pos, b.info, NodeTrafo(b)),
              DomainFuncApp(arpLogNil, Seq(), Map[TypeVar, Type]())(b.pos, b.info, NodeTrafo(b))
            )(b.pos, b.info, NodeTrafo(b)),
            // inhale rd constraints for rd argument
            Inhale(plugin.utils.constrainRdExp(methodRdName)(m.pos, m.info))(m.pos, m.info)
          ) ++
            // inhale preconditions
            m.pres.map(p => Inhale(p)(p.pos, ConsInfo(p.info, WasMethodCondition()))) ++
            // start label
            Seq(Label(methodStartLabelName, Seq())(m.pos, m.info)) ++
            // method body
            Seq(Seqn(
              b.ss.map(plugin.utils.rewriteOldExpr(methodStartLabelName, fieldAccess = false)),
              b.scopedDecls
            )(b.pos, b.info, NodeTrafo(b))) ++
            Seq(
              Label(methodEndLabelName, Seq())(m.pos, m.info)
            ) ++
            // exhale postconditions
            m.posts.map(p => Exhale(
              plugin.utils.rewriteOldExpr(methodEndLabelName, oldLabel = false)(
                plugin.utils.rewriteOldExpr(methodStartLabelName, fieldAccess = false)(p)
              )
            )(p.pos, ConsInfo(p.info, WasMethodCondition()), ErrTrafo({
              case ExhaleFailed(_, reason, cached) =>
                PostconditionViolated(p, m, reason, cached)
              case error: AbstractVerificationError => error.withNode(p).asInstanceOf[AbstractVerificationError]
            }))),
          // variable declarations
          Seq(
            Label(methodStartLabelName, Seq())(m.pos, m.info),
            Label(methodEndLabelName, Seq())(m.pos, m.info),
            LocalVarDecl(logName, arpLogType)(m.pos, m.info)
          )
        )(m.pos, m.info, NodeTrafo(b))
      })
    )(m.pos, m.info, NodeTrafo(m))
  }

  // desugar method calls into explicit inhales/exhales
  def handleMethodCall(input: Program, m: MethodCall, ctx: ContextC[Node, ARPContext]): Node = {
    plugin.utils.getMethod(input, m.methodName) match {
      case Some(method) =>
        val labelName = plugin.naming.getNewName(method.name, "call_label")
        val methodRdName = plugin.naming.getNewNameFor(m, method.name, "call_rd")
        val argumentNames = method.formalArgs.map(v => plugin.naming.getNewName("arg", v.localVar.name))
        val localVars = method.formalArgs.zip(m.args).zip(argumentNames).map(z => LocalVar(z._2)(z._1._1.localVar.typ, m.pos, m.info, NodeTrafo(z._1._2)))

        def argRenamer = renameArguments(m, method, localVars)

        Seqn(
          Seq(
            // call label
            Label(labelName, Seq())(m.pos, m.info),
            // inhale rd constraints for call rd
            Inhale(plugin.utils.constrainRdExp(methodRdName)(m.pos, m.info))(m.pos, m.info)
          ) ++
            localVars.zip(m.args).map(z => LocalVarAssign(z._1, z._2)(m.pos, m.info, ErrTrafo({
              case AssignmentFailed(_, reason, cached) => CallFailed(m, reason, cached)
            }))) ++
            // exhale preconditions
            method.pres.map(p => Exhale(
              plugin.utils.rewriteOldExpr(labelName)(argRenamer(p))
            )(p.pos, ConsInfo(p.info, WasCallCondition()), ErrTrafo({
              case ExhaleFailed(_, reason, cached) =>
                PreconditionInCallFalse(m, reason, cached)
              case error: AbstractVerificationError => error.withNode(p).asInstanceOf[AbstractVerificationError]
            }))) ++
            m.targets.map(t => plugin.utils.havoc(t, ctx)) ++
            // inhale postconditions
            method.posts.map(p => Inhale(
              plugin.utils.rewriteOldExpr(labelName, fieldAccess = false)(argRenamer(p))
            )(p.pos, ConsInfo(p.info, WasCallCondition()))),
          // variable declarations
          Seq(
            LocalVarDecl(methodRdName, Perm)(m.pos, m.info),
            Label(labelName, Seq())(m.pos, m.info)
          ) ++
            localVars.map(v => LocalVarDecl(v.name, v.typ)(m.pos, m.info))
        )(m.pos, m.info, NodeTrafo(m))
      case None => m
    }
  }

  def renameArguments(call: MethodCall, method: Method, vars: Seq[LocalVar]): Exp => Exp = {
    val argMapping = method.formalArgs.zip(vars).foldLeft(HashMap[String, Exp]())((m, c) =>
      m + (c._1.name -> c._2)
    )

    val allMapping = method.formalReturns.zip(call.targets).foldLeft(argMapping)((m, c) =>
      m + (c._1.name -> c._2)
    )

    val strategy = StrategyBuilder.Slim[Node]({
      case l@LocalVar(name) => allMapping.getOrElse(name, l)
    }, Traverse.BottomUp)

    def renamer(exp: Exp): Exp = {
      strategy.execute[Exp](exp)
    }

    renamer
  }

  def joinBreathing(breath: Seq[Exp]): Exp = {
    if (breath.isEmpty) {
      FalseLit()()
    } else if (breath.tail.isEmpty) {
      breath.head
    } else {
      And(breath.head, joinBreathing(breath.tail))(breath.head.pos, breath.head.info)
    }
  }
}
