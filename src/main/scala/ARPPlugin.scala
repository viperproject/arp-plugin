/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import java.nio.file.Paths

import viper.silver.ast.{Inhale, _}
import viper.silver.ast.utility.Rewriter.{StrategyBuilder, Traverse}
import viper.silver.parser._
import viper.silver.verifier._

class ARPPlugin extends SilverPlugin {

  var _errors: Seq[AbstractError] = Seq[AbstractError]()

  override def beforeResolve(input: PProgram): PProgram = {

    val rdFunction = PFunction(PIdnDef(ARPPluginNaming.rdName), Seq(), TypeHelper.Perm, Seq(), Seq(), None, None)

    val argument = Seq(PFormalArgDecl(PIdnDef("x"), TypeHelper.Int))
    val epsilonFunction = PFunction(PIdnDef(ARPPluginNaming.rdCountingName), argument, TypeHelper.Perm, Seq(), Seq(), None, None)

    // inject functions for rd() and rdc()
    val inputWithFunctions = PProgram(
      input.imports,
      input.macros,
      input.domains,
      input.fields,
      input.functions :+ rdFunction :+ epsilonFunction,
      input.predicates,
      input.methods,
      input.errors
    )

    // replace all rd with rd()
    val rdRewriter = StrategyBuilder.Slim[PNode]({
      case PIdnUse(ARPPluginNaming.rdName) => PCall(PIdnUse(ARPPluginNaming.rdName), Seq(), None)
    }, Traverse.BottomUp)

    val inputPrime = rdRewriter.execute[PProgram](inputWithFunctions)

    inputPrime
  }

  override def beforeVerify(input: Program): Program = {
    val inputWithARPDomain = addARPDomain(input)
    ARPPluginNaming.init(ARPPluginNaming.collectUsedNames(inputWithARPDomain))
    val enhancedInput = addFieldFunctions(inputWithARPDomain)

    val arpRewriter = StrategyBuilder.Context[Node, String](
      {
        case (m : Method, ctx) =>
          ARPPluginMethods.handleMethod(enhancedInput, m, ctx)
        case (m : MethodCall, ctx) =>
          ARPPluginMethods.handleMethodCall(enhancedInput, m, ctx)
        case (w : While, ctx) =>
          ARPPluginWhile.handleWhile(enhancedInput, w, ctx)
        case (a@Assert(exp), ctx) =>
          Assert(ARPPluginUtils.rewriteRd(ctx.c)(exp))(a.pos, a.info, a.errT + NodeTrafo(a))
        case (e: Exhale, ctx) =>
          ARPPluginBreathe.handleExhale(enhancedInput, e, ctx)
        case (i: Inhale, ctx) =>
          ARPPluginBreathe.handleInhale(enhancedInput, i, ctx)
      },
      "", // default context
      {
        case (m@Method(name, _, _, _, _, _), _) =>
          ARPPluginNaming.getNameFor(m, suffix = "rd")
        case (w@While(_, _, _), _) =>
          // TODO: reuse previous rd name
          ARPPluginNaming.getNameFor(w, suffix = "rd")
      }
    )

    val inputPrime = arpRewriter.execute[Program](enhancedInput)

    println(inputPrime)
    inputPrime
  }

  override def beforeFinish(input: VerificationResult): VerificationResult = {
    input match {
      case Success =>
        if (_errors.isEmpty) Success else Failure(_errors)
      case Failure(errors) =>
        Failure(errors.map {
          case ParseError(msg, pos) => ParseError(msg + s" ($pos)", pos)
          case AbortedExceptionally(cause) => ParseError(s"Exception: $cause", NoPosition) // Is not really a parse error...
          case TypecheckerError(msg, pos) => TypecheckerError(msg.replace("<undefined position>", "<ARP Plugin>"), pos)
          case error: AbstractVerificationError => error.transformedError() // TODO: Add ErrorTransformation Information to AST
          case default => default
        } ++ _errors)
    }
  }

  def loadSilFile(file: String): Program = {
    val path = Paths.get(getClass.getResource(file).toURI)
    val arpFrontend = new ARPFrontend
    arpFrontend.loadFile(path) match {
      case Some(program) => program
      case None => Program(Seq(), Seq(), Seq(), Seq(), Seq())() // TODO: Probably not the best way to do it
    }
  }

  def addARPDomain(input: Program): Program = {
    val arpDomainFile = loadSilFile(ARPPluginNaming.arpDomainFile)

    val newProgram = Program(
      input.domains ++ arpDomainFile.domains,
      input.fields ++ arpDomainFile.fields,
      input.functions.filterNot(f => f.name == ARPPluginNaming.rdName || f.name == ARPPluginNaming.rdCountingName) ++ arpDomainFile.functions,
      input.predicates ++ arpDomainFile.predicates,
      input.methods ++ arpDomainFile.methods
    )(input.pos, input.info, input.errT + NodeTrafo(input))

    checkUniqueNames(input, arpDomainFile)

    // if there was an error, give back an empty program
    if (_errors.isEmpty) newProgram else Program(Seq(), Seq(), Seq(), Seq(), Seq())()
  }

  def addFieldFunctions(input: Program): Program = {
    val domainName = ARPPluginNaming.fieldFunctionDomainName
    val fieldDomain = Domain(
      domainName,
      input.fields.map(f => DomainFunc(
        ARPPluginNaming.getNameFor(f, prefix = "field", suffix = f.name),
        Seq(), Int, unique = true
      )(input.pos, input.info, domainName, input.errT)),
      Seq(),
      Seq()
    )(input.pos, input.info, input.errT + NodeTrafo(input))

    val newProgram = Program(
      input.domains :+ fieldDomain,
      input.fields,
      input.functions,
      input.predicates,
      input.methods
    )(input.pos, input.info, input.errT + NodeTrafo(input))

    newProgram
  }

  def checkUniqueNames(input: Program, inputPrime: Program): Unit ={
    // TODO: There is no easy way report back errors from within a plugin
    // TODO: Is there a better way to check for duplicates?
    // check name clashes
    input.domains.filter(d => inputPrime.domains.exists(dd => dd.name == d.name)).foreach(d => {
      _errors :+= TypecheckerError(s"Duplicate domain '${d.name}'", d.pos)
    })
    input.fields.filter(f => inputPrime.fields.exists(ff => ff.name == f.name)).foreach(f => {
      _errors :+= TypecheckerError(s"Duplicate field '${f.name}'", f.pos)
    })
    input.functions.filterNot(f => f.name == ARPPluginNaming.rdName || f.name == ARPPluginNaming.rdCountingName)
      .filter(f => inputPrime.functions.exists(ff => ff.name == f.name)).foreach(f => {
      _errors :+= TypecheckerError(s"Duplicate function '${f.name}'", f.pos)
    })
    input.predicates.filter(p => inputPrime.predicates.exists(pp => pp.name == p.name)).foreach(p => {
      _errors :+= TypecheckerError(s"Duplicate predicate '${p.name}'", p.pos)
    })
    input.methods.filter(m => inputPrime.methods.exists(mm => mm.name == m.name)).foreach(m => {
      _errors :+= TypecheckerError(s"Duplicate method '${m.name}'", m.pos)
    })
  }
}
