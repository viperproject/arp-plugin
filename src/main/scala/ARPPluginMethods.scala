/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast.utility.Rewriter.ContextC
import viper.silver.ast._
import viper.silver.verifier.errors.{ExhaleFailed, PostconditionViolated, PreconditionInCallFalse}

object ARPPluginMethods {

  // add rd argument to method
  // init ARPLog
  // desugar method contracts into explicit inhales/exhales
  def handleMethod(input: Program, m: Method, ctx: ContextC[Node, String]): Node = {
    val methodRdName = ARPPluginUtils.getNewNameFor(m, "_rd")
    val methodLabelName = ARPPluginUtils.getNewName + "_label"
    val rdArg = LocalVarDecl(methodRdName, Perm)(m.pos, m.info)
    val arpLogDomain = ARPPluginUtils.getDomain(input, "ARPLog").get
    val arpLogType = DomainType(arpLogDomain, Map[TypeVar, Type]() /* TODO: What's the deal with this? */)
    val arpLogNil = ARPPluginUtils.getDomainFunction(arpLogDomain, "ARPLog_Nil").get
    Method(
      m.name,
      m.formalArgs :+ rdArg,
      m.formalReturns,
      Seq(),
      Seq(),
      m.body.map(b => {
        Seqn(
          Seq(
            LocalVarAssign(
              LocalVar(ARPPluginUtils.getARPLogName)(arpLogType, b.pos, b.info, b.errT + NodeTrafo(b)),
              DomainFuncApp(arpLogNil, Seq(), Map[TypeVar, Type]())(b.pos, b.info, b.errT + NodeTrafo(b))
            )(b.pos, b.info, b.errT + NodeTrafo(b)),
            Inhale(ARPPluginUtils.constrainRdExp(methodRdName)(m.pos, m.info))(m.pos, m.info)
          )
            ++ m.pres.map(p => Inhale(ARPPluginUtils.rewriteRd(methodRdName)(p))(p.pos, p.info, p.errT + NodeTrafo(p)))
            ++ Seq(Label(methodLabelName, Seq())(m.pos, m.info))
            ++ b.ss
            ++ m.posts.map(p => Exhale(
            ARPPluginUtils.rewriteOldExpr(methodLabelName)(ARPPluginUtils.rewriteRd(methodRdName)(p))
          )(p.pos, p.info, p.errT + NodeTrafo(p) + ErrTrafo({
            case ExhaleFailed(_, reason, cached) =>
              PostconditionViolated(p, m, reason, cached)
          }))),
          b.scopedDecls ++ Seq(
            Label(methodLabelName, Seq())(m.pos, m.info),
            LocalVarDecl(ARPPluginUtils.getARPLogName, arpLogType)(m.pos, m.info)
          )
        )(m.pos, m.info, m.errT + NodeTrafo(b))
      })
    )(m.pos, m.info, m.errT + NodeTrafo(m))
  }

  // desugar method calls into explicit inhales/exhales
  def handleMethodCall(input: Program, m: MethodCall, ctx: ContextC[Node, String]): Node = {
    ARPPluginUtils.getMethod(input, m.methodName) match {
      case Some(method) =>
        val newErrTrafo = m.errT + NodeTrafo(m)
        val labelName = ARPPluginUtils.getNewName + "_label"
        val methodRdName = ARPPluginUtils.getNewNameFor(m, "_rd")
        Seqn(
          Seq(
            Label(labelName, Seq())(m.pos, m.info, newErrTrafo),
            Inhale(ARPPluginUtils.constrainRdExp(methodRdName)(m.pos, m.info, newErrTrafo))(m.pos, m.info, newErrTrafo)
          ) ++
            method.pres.map(p => Exhale(
              ARPPluginUtils.rewriteRd(methodRdName)(ARPPluginUtils.rewriteOldExpr(labelName)(p))
            )(p.pos, p.info, p.errT + NodeTrafo(p) + ErrTrafo({
              case ExhaleFailed(_, reason, cached) =>
                PreconditionInCallFalse(m, reason, cached)
            }))) ++
            method.posts.map(p => Inhale(
              ARPPluginUtils.rewriteRd(methodRdName)(ARPPluginUtils.rewriteOldExpr(labelName, onlyOld = true)(p))
            )(p.pos, p.info, p.errT + NodeTrafo(p))),
          Seq(
            Label(labelName, Seq())(m.pos, m.info),
            LocalVarDecl(methodRdName, Perm)(m.pos, m.info)
          )
        )(m.pos, m.info, newErrTrafo)
      case None => m
    }
  }
}
