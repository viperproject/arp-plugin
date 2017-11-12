/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast.utility.Rewriter.ContextC
import viper.silver.ast._
import viper.silver.verifier.errors.{ExhaleFailed, PostconditionViolated, PreconditionInCallFalse}

class ARPPluginMethods(plugin: ARPPlugin) {

  // add rd argument to method
  // init ARPLog
  // desugar method contracts into explicit inhales/exhales
  def handleMethod(input: Program, m: Method, ctx: ContextC[Node, String]): Node = {
    val methodRdName = plugin.naming.getNameFor(m, m.name, "rd")
    val methodStartLabelName = plugin.naming.getNewName(m.name, "start_label")
    val methodEndLabelName = plugin.naming.getNewName(m.name, "end_label")
    val rdArg = LocalVarDecl(methodRdName, Perm)(m.pos, m.info)
    val arpLogDomain = plugin.utils.getDomain(input, plugin.naming.logDomainName).get
    val arpLogType = DomainType(arpLogDomain, Map[TypeVar, Type]() /* TODO: What's the deal with this? */)
    val arpLogNil = plugin.utils.getDomainFunction(arpLogDomain, plugin.naming.logDomainNil).get

    Method(
      m.name,
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
              LocalVar(plugin.naming.logName)(arpLogType, b.pos, b.info, b.errT + NodeTrafo(b)),
              DomainFuncApp(arpLogNil, Seq(), Map[TypeVar, Type]())(b.pos, b.info, b.errT + NodeTrafo(b))
            )(b.pos, b.info, b.errT + NodeTrafo(b)),
            // inhale rd constraints for rd argument
            Inhale(plugin.utils.constrainRdExp(methodRdName)(m.pos, m.info))(m.pos, m.info)
          ) ++
            // inhale preconditions
            m.pres.map(p => Inhale(p)(p.pos, p.info, p.errT + NodeTrafo(p))) ++
            // start label
            Seq(Label(methodStartLabelName, Seq())(m.pos, m.info)) ++
            // method body
            b.ss ++
            Seq(
              Label(methodEndLabelName, Seq())(m.pos, m.info)
            ) ++
            // exhale postconditions
            m.posts.map(p => Exhale(
              plugin.utils.rewriteOldExpr(methodEndLabelName, oldLabel = false)(
                plugin.utils.rewriteOldExpr(methodStartLabelName, fieldAccess = false)(p)
              )
            )(p.pos, p.info, p.errT + NodeTrafo(p) + ErrTrafo({
              case ExhaleFailed(_, reason, cached) =>
                PostconditionViolated(p, m, reason, cached)
            }))),
          // variable declarations
          b.scopedDecls ++ Seq(
            Label(methodStartLabelName, Seq())(m.pos, m.info),
            Label(methodEndLabelName, Seq())(m.pos, m.info),
            LocalVarDecl(plugin.naming.logName, arpLogType)(m.pos, m.info)
          )
        )(m.pos, m.info, m.errT + NodeTrafo(b))
      })
    )(m.pos, m.info, m.errT + NodeTrafo(m))
  }

  // desugar method calls into explicit inhales/exhales
  def handleMethodCall(input: Program, m: MethodCall, ctx: ContextC[Node, String]): Node = {
    plugin.utils.getMethod(input, m.methodName) match {
      case Some(method) =>
        val newErrTrafo = m.errT + NodeTrafo(m)
        val labelName = plugin.naming.getNewName(method.name, "call_label")
        val methodRdName = plugin.naming.getNewName(method.name, "call_rd")
        Seqn(
          Seq(
            // call label
            Label(labelName, Seq())(m.pos, m.info, newErrTrafo),
            // inhale rd constraints for call rd
            Inhale(plugin.utils.constrainRdExp(methodRdName)(m.pos, m.info, newErrTrafo))(m.pos, m.info, newErrTrafo)
          ) ++
            // exhale preconditions
            method.pres.map(p => Exhale(
              plugin.utils.rewriteOldExpr(labelName, fieldAccess = false)(p)
            )(p.pos, p.info, p.errT + NodeTrafo(p) + ErrTrafo({
              case ExhaleFailed(_, reason, cached) =>
                PreconditionInCallFalse(m, reason, cached)
            }))) ++
            // inhale postconditions
            method.posts.map(p => Inhale(
              plugin.utils.rewriteOldExpr(labelName, fieldAccess = false)(p)
            )(p.pos, p.info, p.errT + NodeTrafo(p))),
          // variable declarations
          Seq(
            Label(labelName, Seq())(m.pos, m.info),
            LocalVarDecl(methodRdName, Perm)(m.pos, m.info)
          )
        )(m.pos, m.info, newErrTrafo)
      case None => m
    }
  }
}
