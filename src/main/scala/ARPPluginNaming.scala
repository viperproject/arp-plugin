/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.StrategyBuilder

import scala.collection.immutable.{HashMap, HashSet}

object ARPPluginNaming {

  var usedNames = new HashSet[String]
  var nameMap = new HashMap[Node, String]

  private var logName_ = "ARP_pl"
  def logName: String = logName_
  val logDomainName = "ARPLog"
  val logDomainNil = "ARPLog_Nil"
  val logDomainCons = "ARPLog_Cons"
  val logDomainSum = "ARPLog_sum"
  val rdName = "rd"
  val rdCountingName = "rdc"
  val rdWildcardName = "rdw"
  val rdEpsilonName = "epsilonRd"
  val rdGlobalName = "epsilonRd"
  private var fieldFunctionDomainName_ = "ARP_field_functions"
  def fieldFunctionDomainName = fieldFunctionDomainName_
  val arpDomainFile = "/ARPDomain.sil"

  def init(usedNames: Set[String]): Unit = {
    this.usedNames = HashSet[String]()
    this.usedNames ++= usedNames
    logName_ = getNewName("ARP_pl")
    fieldFunctionDomainName_ = getNewName("ARP_field_functions")
  }

  def getNewName(prefix: String = "ARP", suffix: String = ""): String ={
    def conc(i: Integer) = prefix + "_" + i.toString + "_" + suffix

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

  def getNameFor(node: Node, prefix: String = "ARP", suffix: String = ""): String ={
    if (!nameMap.contains(node)){
      nameMap += node -> getNewName(prefix, suffix)
    }
    nameMap(node)
  }

  def storeName(node: Node, name: String): Unit ={
    usedNames += name
    nameMap += node -> name
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
    }.execute(node)

    names
  }
}
