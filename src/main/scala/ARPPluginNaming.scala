/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.StrategyBuilder

import scala.collection.immutable.{HashMap, HashSet}

class ARPPluginNaming(plugin: ARPPlugin) {

  var usedNames = new HashSet[String]
  var nodeNameMap = new HashMap[(Node, Position, String, String), String]
  var anyNameMap = new HashMap[(Any, String, String), String]

  val logDomainName = "ARPLog"
  val logDomainNil = "ARPLog_Nil"
  val logDomainCons = "ARPLog_Cons"
  val logDomainSumGt = "ARPLog_sum_gt"
  val logDomainSum = "ARPLog_sum"
  val logDomainMaxLevel = "ARPLog_max_level"
  val rdName = "rd"
  val rdCountingName = "rdc"
  val rdWildcardName = "rdw"
  val rdEpsilonName = "epsilonRd"
  val rdGlobalName = "epsilonRd"
  val blacklistName = "ARP_IGNORE"
  private var havocNames_ = HashMap[Type, String]()
  def havocNames: HashMap[Type, String] = havocNames_
  private var fieldFunctionDomainName_ = "ARP_field_functions"
  def fieldFunctionDomainName: String = fieldFunctionDomainName_
  val arpDomainFile = "/ARPDomain.sil"

  def init(usedNames: Set[String]): Unit = {
    this.usedNames = HashSet[String]()
    this.usedNames ++= usedNames
    fieldFunctionDomainName_ = getNewName("ARP_field_functions")
    havocNames_ += (Bool -> getNewName("HavocBool"))
    havocNames_ += (Int -> getNewName("HavocInt"))
    havocNames_ += (Ref -> getNewName("HavocRef"))
    havocNames_ += (Perm -> getNewName("HavocPerm"))
  }

  def getNewName(prefix: String = "ARP", suffix: String = ""): String ={
    def conc(i: Integer) = prefix + "_" + i.toString + (if (suffix.nonEmpty) "_" + suffix else "")

    var name = if (suffix.isEmpty) prefix else prefix +  "_" + suffix
    if (usedNames.contains(name)) {
      var i = 0
      while (usedNames contains conc(i)) {
        i += 1
      }
      name = conc(i)
    }
    usedNames += name
    name
  }

  def getNameFor(node: Node with Positioned, prefix: String = "ARP", suffix: String = ""): String ={
    if (!nodeNameMap.contains((node, node.pos, prefix, suffix))){
      nodeNameMap += (node, node.pos, prefix, suffix) -> getNewName(prefix, suffix)
    }
    nodeNameMap((node, node.pos, prefix, suffix))
  }

  def getAnyNameFor(any: Any, prefix: String = "ARP", suffix: String = ""): String ={
    if (!anyNameMap.contains((any, prefix, suffix))){
      anyNameMap += (any, prefix, suffix) -> getNewName(prefix, suffix)
    }
    anyNameMap((any, prefix, suffix))
  }

  def getFieldFunctionName(f: Field): String ={
    getAnyNameFor(f, "field", f.name)
  }

  def getPredicateFunctionName(p: Predicate): String ={
    getAnyNameFor(p, "predicate", p.name)
  }

  def storeName(name: String, node: Node with Positioned, prefix: String = "ARP", suffix: String = ""): Unit ={
    usedNames += name
    nodeNameMap += (node, node.pos, prefix, suffix) -> name
  }

  def storeAnyName(name: String, any: Any, prefix: String = "ARP", suffix: String = ""): Unit ={
    usedNames += name
    anyNameMap += (any, prefix, suffix) -> name
  }

  def collectUsedNames(node: Node): Set[String] = {
    var names = Set[String]()

    StrategyBuilder.SlimVisitor[Node]{
      case Domain(name, _, _, _) => names += name
      case Field(name, _) => names += name
      case Function(name, _, _, _, _, _, _) => names += name
      case Predicate(name, _, _) => names += name
      case Method(name, _, _, _, _, _) => names += name
      case LocalVar(name) => names += name
      case LocalVarDecl(name, _) => names += name
      case Label(name, _) => names += name
      case DomainFunc(name, _, _, _) => names += name
      case DomainAxiom(name, _) => names += name
      case _ =>
    }.visit(node)

    names
  }
}
