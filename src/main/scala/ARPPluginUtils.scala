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

  var newNameMap = new HashMap[Node, String]
  var newNameSuffix = new HashMap[Node, String]

  var nameIndex = 0

  def getMethod(program: Program, method: String): Option[Method] = {
    program.methods.find(m => m.name == method)
  }

  def getFunction(program: Program, function: String): Option[Function] = {
    program.functions.find(f => f.name == function)
  }

  def getDomain(program: Program, domain: String): Option[Domain] = {
    program.domains.find(d => d.name == domain)
  }

  def getDomainFunction(domain: Domain, function: String): Option[DomainFunc] ={
    domain.functions.find(f => f.name == function)
  }

  def getARPLogName: String = "ARPPlugin_pl"

  def getARPLogDomainName: String = "ARPLog"

  def getFieldFunctionDomainName: String = "ARPPlugin_field_functions"

  def getName(suffix: String): String = "ARPPlugin_NAME_" + suffix

  def getLastNewName: String = getName(nameIndex.toString)

  def getNewName: String = {
    nameIndex += 1
    // TODO: figure out a way to generate unique names (i.e. don't just hope no one else uses the name)
    // TODO: use the same name for whiles of the same scope
    getName(nameIndex.toString)
  }

  def getNewNameFor(node: Node, suffix: String = ""): String = {
    if (newNameMap.contains(node)) {
      newNameMap(node) + suffix
    } else {
      val newName = getNewName
      newNameMap += node -> newName
      newNameSuffix += node -> suffix
      newName + suffix
    }
  }

  def getNewNameForWithSuffix(node: Node): String = {
    if (newNameMap.contains(node)) {
      newNameMap(node) + newNameSuffix(node)
    } else {
      getNewNameFor(node, "_no_suffix_found")
    }
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
      case f@FuncApp("rd", Seq()) => LocalVar(contextRdName)(Perm, f.pos, f.info, f.errT + NodeTrafo(f))
      case f@FuncApp("rdc", Seq(arg: Exp)) =>
        PermMul(
          arg,
          FuncApp("epsilonRd", Seq())(f.pos, f.info, f.typ, f.formalArgs, f.errT)
        )(f.pos, f.info, f.errT + NodeTrafo(f))
    }).execute[Exp](node)
  }
}
