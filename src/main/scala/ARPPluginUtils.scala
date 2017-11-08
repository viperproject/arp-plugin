/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.StrategyBuilder

import scala.collection.immutable.HashMap

object ARPPluginUtils {

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

  def rewriteOldExpr(labelName: String, onlyOld: Boolean = false)(node: Exp): Exp = {
    StrategyBuilder.Slim[Node]({
      case o@Old(exp) => LabelledOld(exp, labelName)(o.pos, o.info, o.errT + NodeTrafo(o))
      case f@FieldAccessPredicate(fa@FieldAccess(exp, field), perm) if !onlyOld =>
        FieldAccessPredicate(
          FieldAccess(
            LabelledOld(exp, labelName)(f.pos, f.info, f.errT + NodeTrafo(exp)),
            field
          )(f.pos, f.info, f.errT + NodeTrafo(fa)),
          perm
        )(f.pos, f.info, f.errT + NodeTrafo(f))
    }).execute[Exp](node)
  }

  def rewriteRd(contextRdName: String)(node: Exp): Exp = {
    StrategyBuilder.Slim[Node]({
      case f@FuncApp(ARPPluginNaming.rdName, Seq()) => LocalVar(contextRdName)(Perm, f.pos, f.info, f.errT + NodeTrafo(f))
      case f@FuncApp(ARPPluginNaming.rdCountingName, Seq(arg: Exp)) =>
        PermMul(
          arg,
          FuncApp(ARPPluginNaming.rdEpsilonName, Seq())(f.pos, f.info, f.typ, f.formalArgs, f.errT)
        )(f.pos, f.info, f.errT + NodeTrafo(f))
    }).execute[Exp](node)
  }
}
