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
import viper.silver.plugin.ARPPlugin.{ARPContext, TransformedWhile}
import viper.silver.verifier._
import viper.silver.verifier.errors._
import viper.silver.verifier.reasons.FeatureUnsupported

class ARPPlugin extends SilverPlugin {

  // TODO: implement globalRd in predicates
  // TODO: Maybe Conjunct conditions to get rid of duplicate labels
  // TODO: Maybe reuse previous rd name for while

  val utils = new ARPPluginUtils(this)
  val naming = new ARPPluginNaming(this)
  val methods = new ARPPluginMethods(this)
  val while_ = new ARPPluginWhile(this)
  val breathe = new ARPPluginBreathe(this)
  val normalize = new ARPPluginNormalize(this)

  object Optimize {
    val simplifyExpressions = true
    val removeProvableIf = true
    val noAssumptionForPost = true
  }

  override def beforeResolve(input: PProgram): PProgram = {

    val rdFunction = PFunction(PIdnDef(naming.rdName), Seq(), TypeHelper.Perm, Seq(), Seq(), None, None)

    val argument = Seq(PFormalArgDecl(PIdnDef("ARP_LongAndIrrelevantNameToPreventCollisions_314159265358979323846264"), TypeHelper.Int))
    val epsilonFunction = PFunction(PIdnDef(naming.rdCountingName), argument, TypeHelper.Perm, Seq(), Seq(), None, None)

    val wildcardFunction = PFunction(PIdnDef(naming.rdWildcardName), Seq(), TypeHelper.Perm, Seq(), Seq(), None, None)

    // If a program already contains a definition for rd we can't use our arp rd
    var alreadyContainsRd = false
    var alreadyContainsRdc = false
    var alreadyContainsRdw = false
    StrategyBuilder.SlimVisitor[PNode]({
      case PIdnDef(naming.rdName) => alreadyContainsRd = true
      case PIdnDef(naming.rdCountingName) => alreadyContainsRdc = true
      case PIdnDef(naming.rdWildcardName) => alreadyContainsRdw = true
      case _ =>
    }).visit(input)

    val sanitizedInput = StrategyBuilder.Slim[PNode]({
      case PIdnUse(naming.rdName) if alreadyContainsRd => PIdnUse("WAS_RD_BUT_IS_NOT_ARP_RD")
      case PIdnDef(naming.rdName) if alreadyContainsRd => PIdnDef("WAS_RD_BUT_IS_NOT_ARP_RD")
      case PIdnUse(naming.rdCountingName) if alreadyContainsRdc => PIdnUse("WAS_RDC_BUT_IS_NOT_ARP_RDC")
      case PIdnDef(naming.rdCountingName) if alreadyContainsRdc => PIdnDef("WAS_RDC_BUT_IS_NOT_ARP_RDC")
      case PIdnUse(naming.rdWildcardName) if alreadyContainsRdw => PIdnUse("WAS_RDW_BUT_IS_NOT_ARP_RDW")
      case PIdnDef(naming.rdWildcardName) if alreadyContainsRdw => PIdnDef("WAS_RDW_BUT_IS_NOT_ARP_RDW")
    }).execute[PProgram](input)

    // inject functions for rd() and rdc()
    val inputWithFunctions = PProgram(
      sanitizedInput.imports,
      sanitizedInput.macros,
      sanitizedInput.domains,
      sanitizedInput.fields,
      sanitizedInput.functions :+ rdFunction :+ epsilonFunction :+ wildcardFunction,
      sanitizedInput.predicates,
      sanitizedInput.methods,
      sanitizedInput.errors
    )

    // replace all rd with rd()
    val rdRewriter = StrategyBuilder.Ancestor[PNode]({
      case (PIdnUse(naming.rdName), ctx) if !ctx.parent.isInstanceOf[PCall] => PCall(PIdnUse(naming.rdName), Seq(), None)
      case (PIdnUse(naming.rdWildcardName), ctx) if !ctx.parent.isInstanceOf[PCall] => PCall(PIdnUse(naming.rdWildcardName), Seq(), None)
    }, Traverse.BottomUp)

    val inputPrime = rdRewriter.execute[PProgram](inputWithFunctions)

    inputPrime
  }

  override def beforeVerify(input: Program): Program = {
    val inputWithARPDomain = addARPDomain(input)
    naming.init(naming.collectUsedNames(inputWithARPDomain))
    val enhancedInput = addFieldFunctions(inputWithARPDomain)

    val arpRewriter = StrategyBuilder.Context[Node, ARPContext](
      {
        case (m: Method, ctx) =>
          methods.handleMethod(enhancedInput, m, ctx)
        case (m: MethodCall, ctx) =>
          methods.handleMethodCall(enhancedInput, m, ctx)
        case (w: While, ctx) =>
          while_.handleWhile(enhancedInput, w, ctx)
        case (a: Assert, ctx) =>
          breathe.handleAssert(enhancedInput, a, ctx)
        case (e: Exhale, ctx) =>
          breathe.handleExhale(enhancedInput, e, ctx)
        case (i: Inhale, ctx) =>
          breathe.handleInhale(enhancedInput, i, ctx)
        case (f: Fold, ctx) =>
          breathe.handleFold(enhancedInput, f, ctx)
        case (f: Unfold, ctx) =>
          breathe.handleUnfold(enhancedInput, f, ctx)
        case (c: Constraining, ctx) => ctx.noRec(rewriteMethodCallsToDummyMethods(enhancedInput, c))
      },
      ARPContext("", "", ""), // default context
      {
        case (m@Method(name, _, _, _, _, _), _) =>
          ARPContext(naming.getNameFor(m, m.name, "rd"), naming.getNameFor(m, m.name, "log"), naming.getNameFor(m, m.name, "start_label"))
        case (w@While(_, _, _), ctx) if w.info.getUniqueInfo[TransformedWhile].isEmpty =>
          ARPContext(naming.getNameFor(w, suffix = "while_rd"), ctx.logName, ctx.oldLabelName)
        case (w@While(_, _, _), ctx) if w.info.getUniqueInfo[TransformedWhile].isDefined =>
          ARPContext(ctx.rdName, naming.getNameFor(w, suffix = "while_log"), ctx.oldLabelName)
        case (m@MethodCall(name, _, _), ctx) =>
          ARPContext(naming.getNameFor(m, name, "call_rd"), ctx.logName, ctx.oldLabelName)
      }
    )

    val rewrittenInput = arpRewriter.execute[Program](enhancedInput)
    val inputPrime = addDummyMethods(input, rewrittenInput)

    if (System.getProperty("DEBUG", "").equals("1")) {
      println(inputPrime)
    }

    inputPrime
  }

  override def mapVerificationResult(input: VerificationResult): VerificationResult = {
    input match {
      case Success => Success
      case Failure(errors) =>
        val errorsPrime = errors.map({
          case ParseError(msg, pos) => ParseError(msg + s" ($pos)", pos)
          case AbortedExceptionally(cause) => ParseError(s"Exception: $cause", NoPosition) // Is not really a parse error...
          case TypecheckerError(msg, pos) => TypecheckerError(msg.replace("<undefined position>", "<ARP Plugin>"), pos)
          case error: AbstractVerificationError => error.transformedError() // TODO: Add ErrorTransformation Information to AST
          case default => default
        })
        Failure(errorsPrime.filterNot({
          case ep: PostconditionViolated => errorsPrime.exists(e => e.isInstanceOf[ContractNotWellformed] && e.pos == ep.pos)
          case ep: WhileFailed => errorsPrime.exists(e => e.isInstanceOf[ContractNotWellformed] && e.pos == ep.pos)
          case ep: LoopInvariantNotEstablished => errorsPrime.exists(e => e.isInstanceOf[ContractNotWellformed] && e.pos == ep.pos)
          case ep: LoopInvariantNotPreserved => errorsPrime.exists(e => e.isInstanceOf[ContractNotWellformed] && e.pos == ep.pos)
          case _ => false
        }))
    }
  }

  def loadSilFile(file: String): Program = {
    val path = Paths.get(getClass.getResource(file).toURI)
    val arpFrontend = new ARPFrontend
    arpFrontend.loadFile(path) match {
      case Some(program) => program
      case None =>
        val empty = Program(Seq(), Seq(), Seq(), Seq(), Seq())()
        reportError(Internal(FeatureUnsupported(empty, "Could not load ARP Domain")))
        empty
    }
  }

  def addARPDomain(input: Program): Program = {
    val arpDomainFile = loadSilFile(naming.arpDomainFile)

    val newProgram = Program(
      input.domains ++ arpDomainFile.domains,
      input.fields ++ arpDomainFile.fields,
      input.functions.filterNot(f =>
        f.name == naming.rdName ||
          f.name == naming.rdCountingName ||
          f.name == naming.rdWildcardName
      ) ++ arpDomainFile.functions,
      input.predicates ++ arpDomainFile.predicates,
      input.methods ++ arpDomainFile.methods
    )(input.pos, input.info, NodeTrafo(input))

    checkUniqueNames(input, arpDomainFile)

    // if there was an error, give back an empty program
    if (_errors.isEmpty) newProgram else Program(Seq(), Seq(), Seq(), Seq(), Seq())()
  }

  def addFieldFunctions(input: Program): Program = {
    val domainName = naming.fieldFunctionDomainName
    val fieldDomain = Domain(
      domainName,
      input.fields.map(f => DomainFunc(
        naming.getNameFor(f, "field", f.name),
        Seq(), Int, unique = true
      )(input.pos, input.info, domainName)),
      Seq(),
      Seq()
    )(input.pos, input.info, NodeTrafo(input))

    val newProgram = Program(
      input.domains :+ fieldDomain,
      input.fields,
      input.functions,
      input.predicates,
      input.methods
    )(input.pos, input.info, NodeTrafo(input))

    newProgram
  }

  def addDummyMethods(originalInput: Program, input: Program): Program = {
    // ensures false is not checked if there is no body, so would not need handle this

    var whileMethods = Seq[Method]()
    StrategyBuilder.AncestorVisitor[Node]({
      case (w: While, ctx) if w.invs.nonEmpty =>
        var args = Seq[LocalVarDecl]()
        w.invs.foreach(wi =>
          StrategyBuilder.SlimVisitor[Node]({
            case l@LocalVar(name) => if(!args.exists(a => a.localVar.name == name)) args :+= LocalVarDecl(name, l.typ)(l.pos, l.info)
            case _ =>
          }).visit(wi)
        )
        whileMethods :+= Method(
          naming.getNameFor(w, suffix = "invariant_wellformed_dummy_method"),
          args,
          Seq(),
          w.invs.filterNot(_.isInstanceOf[BoolLit]).map(utils.rewriteRdForDummyMethod),
          Seq(),
          None
        )(w.pos, w.info)
      case _ =>
    }).visit(originalInput)

    val newProgram = Program(
      input.domains,
      input.fields,
      input.functions,
      input.predicates,
      input.methods ++ whileMethods ++ originalInput.methods
        .filter(m => m.pres.nonEmpty || m.posts.nonEmpty)
        .map(m =>
          Method(
            naming.getNameFor(m, m.name, "contract_wellformed_dummy_method"),
            m.formalArgs,
            m.formalReturns,
            m.pres.filterNot(_.isInstanceOf[BoolLit]).map(utils.rewriteRdForDummyMethod),
            m.posts.filterNot(_.isInstanceOf[BoolLit]).map(utils.rewriteRdForDummyMethod),
            None
          )(m.pos, m.info, NodeTrafo(input))
        )
    )(input.pos, input.info, NodeTrafo(input))

    newProgram
  }

  def rewriteMethodCallsToDummyMethods(input: Program, node: Node): Node ={
    StrategyBuilder.Slim[Node]({
      case m@MethodCall(methodName, args, targets) =>
        val maybeMethod = utils.getMethod(input, methodName)
        if (maybeMethod.isDefined) {
          MethodCall(
            naming.getNameFor(maybeMethod.get, methodName, "contract_wellformed_dummy_method"),
            args,
            targets
          )(m.pos, m.info, NodeTrafo(m))
        } else {
          m
        }
    }).execute(node)
  }

  def checkUniqueNames(input: Program, inputPrime: Program): Unit = {
    // check name clashes
    input.domains.filter(d => inputPrime.domains.exists(dd => dd.name == d.name)).foreach(d => {
      reportError(TypecheckerError(s"Duplicate domain '${d.name}'", d.pos))
    })
    input.fields.filter(f => inputPrime.fields.exists(ff => ff.name == f.name)).foreach(f => {
      reportError(TypecheckerError(s"Duplicate field '${f.name}'", f.pos))
    })
    input.functions.filterNot(f =>
      f.name == naming.rdName ||
        f.name == naming.rdCountingName ||
        f.name == naming.rdWildcardName
    ).filter(f => inputPrime.functions.exists(ff => ff.name == f.name)).foreach(f => {
      reportError(TypecheckerError(s"Duplicate function '${f.name}'", f.pos))
    })
    input.predicates.filter(p => inputPrime.predicates.exists(pp => pp.name == p.name)).foreach(p => {
      reportError(TypecheckerError(s"Duplicate predicate '${p.name}'", p.pos))
    })
    input.methods.filter(m => inputPrime.methods.exists(mm => mm.name == m.name)).foreach(m => {
      reportError(TypecheckerError(s"Duplicate method '${m.name}'", m.pos))
    })
  }
}

object ARPPlugin {

  case class ARPContext(rdName: String, logName: String, oldLabelName: String)

  case class WasMethodCondition() extends Info {
    lazy val comment = Nil
  }

  case class WasInvariantOutside() extends Info {
    lazy val comment = Nil
  }

  case class WasInvariantInside() extends Info {
    lazy val comment = Nil
  }

  case class WasCallCondition() extends Info {
    lazy val comment = Nil
  }

  case class TransformedWhile() extends Info {
    lazy val comment = Nil
  }

}