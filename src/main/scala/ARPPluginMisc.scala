// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.rewriter.{ContextC, StrategyBuilder}
import viper.silver.plugin.ARPPlugin.ARPContext
import viper.silver.verifier.errors.{AssertFailed, Internal}
import viper.silver.verifier.reasons.FeatureUnsupported

class ARPPluginMisc(plugin: ARPPlugin) {

  def handleAssignment(input: Program, a: AbstractAssign, ctx: ContextC[Node, ARPContext]): Node = {

    if (a.lhs.typ == Perm) {
      var perms = Seq[Stmt]()

      val arpLogType = plugin.utils.getARPLogType(input)
      val arpLog = LocalVar(ctx.c.logName, arpLogType)(a.pos, a.info)
      val arpLogSumGt = plugin.utils.getARPLogFunction(input, plugin.naming.logDomainSumGt)
      val arpLogSum = plugin.utils.getARPLogFunction(input, plugin.naming.logDomainSum)
      val maxLevelFunction = plugin.utils.getARPLogFunction(input, plugin.naming.logDomainMaxLevel)

      val arpFieldFunctionDomain = plugin.utils.getDomain(input, plugin.naming.fieldFunctionDomainName).get

      StrategyBuilder.SlimVisitor[Node]({
        case CurrentPerm(loc: FieldAccess) =>
          val fieldFunctionName = plugin.naming.getFieldFunctionName(loc.field)
          val arpFieldFunction = plugin.utils.getDomainFunction(arpFieldFunctionDomain, fieldFunctionName).get
          perms :+= Assert(
            EqCmp(
              DomainFuncApp(
                arpLogSum,
                Seq(
                  loc.rcv,
                  DomainFuncApp(
                    arpFieldFunction, Seq(), Map[TypeVar, Type]()
                  )(a.pos, a.info),
                  DomainFuncApp(
                    maxLevelFunction,
                    Seq(arpLog),
                    Map[TypeVar, Type]()
                  )(a.pos, a.info),
                  arpLog
                ),
                Map[TypeVar, Type]()
              )(a.pos, a.info),
              DomainFuncApp(
                arpLogSumGt,
                Seq(
                  loc.rcv,
                  DomainFuncApp(
                    arpFieldFunction, Seq(), Map[TypeVar, Type]()
                  )(a.pos, a.info),
                  IntLit(-1)(a.pos, a.info),
                  arpLog
                ),
                Map[TypeVar, Type]()
              )(a.pos, a.info)
            )(a.pos, a.info)
          )(a.pos, a.info, ErrTrafo({
            case _: AssertFailed => Internal(a, FeatureUnsupported(a, "It is not allowed to store an ARP anywhere"))
          }))
        case _ =>
      }).visit(a.rhs)

      if (perms.nonEmpty) {
        Seqn(perms ++ Seq[Stmt](ctx.noRec(a)), Seq())(a.pos, a.info, NodeTrafo(a))
      } else {
        a
      }
    } else {
      a
    }
  }

}
