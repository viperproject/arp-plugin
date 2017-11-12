/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.StrategyBuilder

import scala.collection.immutable.HashMap

class ARPPluginUtils(plugin: ARPPlugin) {

  def getMethod(program: Program, method: String): Option[Method] = {
    program.methods.find(m => m.name == method)
  }

  def getFunction(program: Program, function: String): Option[Function] = {
    program.functions.find(f => f.name == function)
  }

  def getDomain(program: Program, domain: String): Option[Domain] = {
    program.domains.find(d => d.name == domain)
  }

  def getDomainFunction(domain: Domain, function: String): Option[DomainFunc] = {
    domain.functions.find(f => f.name == function)
  }

  def constrainRdExp(methodRdName: String)(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): Exp =
    And(
      PermLtCmp(
        NoPerm()(pos, info, errT),
        LocalVar(methodRdName)(Perm, pos, info, errT)
      )(pos, info, errT),
      PermLtCmp(
        LocalVar(methodRdName)(Perm, pos, info, errT),
        FullPerm()(pos, info, errT)
      )(pos, info, errT)
    )(pos, info, errT)

  def rewriteOldExpr[T <: Node](labelName: String, oldLabel: Boolean = true, fieldAccess: Boolean = true)(node: T): T = {
    StrategyBuilder.Slim[Node]({
      case o@Old(exp) if oldLabel => LabelledOld(exp, labelName)(o.pos, o.info, o.errT + NodeTrafo(o))
      case f@FieldAccess(exp, field) if fieldAccess =>
        exp match {
          case _: LabelledOld => f
          case _ =>
            FieldAccess(
              LabelledOld(exp, labelName)(f.pos, f.info, f.errT + NodeTrafo(exp)),
              field
            )(f.pos, f.info, f.errT + NodeTrafo(f))
        }
      case c@CurrentPerm(FieldAccess(rcv, field)) =>
        rcv match {
          case _: LabelledOld => c
          case _ =>
            CurrentPerm(
              FieldAccess(
                LabelledOld(rcv, labelName)(c.pos, c.info, c.errT + NodeTrafo(c)),
                field
              )(c.pos, c.info, c.errT + NodeTrafo(c))
            )(c.pos, c.info, c.errT + NodeTrafo(c))
        }
    }).execute[T](node)
  }

  def rewriteRd[T <: Node](contextRdName: String)(node: T): T = {
    StrategyBuilder.Slim[Node]({
      case f@FuncApp(plugin.naming.rdName, Seq()) => LocalVar(contextRdName)(Perm, f.pos, f.info, f.errT + NodeTrafo(f))
      case f@FuncApp(plugin.naming.rdCountingName, Seq(arg: Exp)) =>
        PermMul(
          arg,
          FuncApp(plugin.naming.rdEpsilonName, Seq())(f.pos, f.info, f.typ, f.formalArgs, f.errT)
        )(f.pos, f.info, f.errT + NodeTrafo(f))
    }).execute[T](node)
  }
}
