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

import scala.collection.immutable

class ARPPlugin extends SilverPlugin {

  // TODO: Fix Perm/Int mess
  // TODO: old in while loops?
  // TODO: Fix log update for quantified expressions
  // TODO: Fix quantified x.f.g
  // TODO: Fix quantified xs[i]
  // TODO: Fix quantified predicates
  // TODO: Fix nested old (e.g. issues/silicon/0120a.sil)
  // TODO: Check c := perm(x.f) calls (Rewriter thinks assignment was already rewritten)
  // TODO: Handle magic wands correctly
  // TODO: fix all/issues/silicon/unofficial006.sil (LocalVarDecl gets lost)
  // TODO: Make sure rd is only used in valid positions (in acc predicates) (i.e. rewriteRd is only called at valid positions)
  // TODO: Make sure error transformation works everywhere
  // TODO: implement globalRd in predicates
  // TODO: Maybe Conjunct conditions to get rid of duplicate labels
  // TODO: Maybe reuse previous rd name for while

  val utils = new ARPPluginUtils(this)
  val naming = new ARPPluginNaming(this)
  val methods = new ARPPluginMethods(this)
  val loops = new ARPPluginWhile(this)
  val breathe = new ARPPluginBreathe(this)
  val normalize = new ARPPluginNormalize(this)
  val quantified = new ARPPluginQuantified(this)
  val wands = new ARPPluginWands(this)
  val misc = new ARPPluginMisc(this)
  var ignoredFields = Seq[String]()

  object Optimize {
    val simplifyExpressions = true
    val removeProvableIf = true
    val noAssumptionForPost = true
  }

  def setIgnoredFields(fields: Seq[String]): Unit = {
    ignoredFields = fields
  }

  def isAccIgnored(acc: LocationAccess): Boolean ={
    acc match {
      case f: FieldAccess => isFieldIgnored(f.field)
      case p: PredicateAccess => isPredicateIgnored(p.predicateName)
    }
  }

  def isFieldIgnored(field: Field): Boolean ={
    ignoredFields.contains(field.name)
  }

  def isPredicateIgnored(predicate: String): Boolean ={
    ignoredFields.contains(predicate)
  }

  def isPredicateIgnored(predicate: Predicate): Boolean = {
    ignoredFields.contains(predicate.name)
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
      case p@PIdnUse(naming.rdName) if alreadyContainsRd => PIdnUse("WAS_RD_BUT_IS_NOT_ARP_RD").setPos(p)
      case p@PIdnDef(naming.rdName) if alreadyContainsRd => PIdnDef("WAS_RD_BUT_IS_NOT_ARP_RD").setPos(p)
      case p@PIdnUse(naming.rdCountingName) if alreadyContainsRdc => PIdnUse("WAS_RDC_BUT_IS_NOT_ARP_RDC").setPos(p)
      case p@PIdnDef(naming.rdCountingName) if alreadyContainsRdc => PIdnDef("WAS_RDC_BUT_IS_NOT_ARP_RDC").setPos(p)
      case p@PIdnUse(naming.rdWildcardName) if alreadyContainsRdw => PIdnUse("WAS_RDW_BUT_IS_NOT_ARP_RDW").setPos(p)
      case p@PIdnDef(naming.rdWildcardName) if alreadyContainsRdw => PIdnDef("WAS_RDW_BUT_IS_NOT_ARP_RDW").setPos(p)
    }).execute[PProgram](input)

    val blacklistMethod = sanitizedInput.methods.find(p => p.idndef.name == naming.blacklistName)
    if (blacklistMethod.isDefined && blacklistMethod.get.body.isDefined) {
      blacklistMethod.get.body.get.childStmts.foreach({
        case PMethodCall(_, PIdnUse(name), _) => ignoredFields :+= name
        case _ =>
      })
    }

    // inject functions for rd() and rdc()
    val inputWithFunctions = PProgram(
      sanitizedInput.imports,
      sanitizedInput.macros,
      sanitizedInput.domains,
      sanitizedInput.fields,
      sanitizedInput.functions :+ rdFunction :+ epsilonFunction :+ wildcardFunction,
      sanitizedInput.predicates,
      sanitizedInput.methods.filterNot(p => p.idndef.name == naming.blacklistName),
      sanitizedInput.errors
    )

    // replace all rd with rd()
    val rdRewriter = StrategyBuilder.Ancestor[PNode]({
      case (p@PIdnUse(naming.rdName), ctx) if !ctx.parent.isInstanceOf[PCall] => PCall(p, Seq(), None).setPos(p)
      case (p@PIdnUse(naming.rdWildcardName), ctx) if !ctx.parent.isInstanceOf[PCall] => PCall(p, Seq(), None).setPos(p)
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
          loops.handleWhile(enhancedInput, w, ctx)
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
        case (a: AbstractAssign, ctx) =>
          misc.handleAssignment(enhancedInput, a, ctx)
        case (c: Constraining, ctx) => ctx.noRec(rewriteMethodCallsToDummyMethods(enhancedInput, c))
        case (a: Apply, ctx) => wands.handleApply(enhancedInput, a, ctx)
        case (p: Package, ctx) => wands.handlePackage(enhancedInput, p, ctx)
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
    val inputPrime = addHavocMethods(addDummyMethods(input, rewrittenInput))

    checkAllRdTransformed(inputPrime)

    if (System.getProperty("DEBUG", "").equals("1")) {
      println(inputPrime)
    }

    if (_errors.isEmpty) {
      if (inputPrime.checkTransitively.nonEmpty) {
        inputPrime.checkTransitively.foreach(ce => reportError(ConsistencyError(ce.message + s" (${ce.pos})", ce.pos)))
      }
    }

    inputPrime
  }

  override def mapVerificationResult(input: VerificationResult): VerificationResult = {
    input match {
      case Success => Success
      case Failure(errors) =>
        val errorsPrime = errors.map({
          case ParseError(msg, pos) => ParseError(msg + s" ($pos)", pos)
          case AbortedExceptionally(cause) => ParseError(s"Exception: $cause (${cause.getStackTrace})", NoPosition) // Is not really a parse error...
          case TypecheckerError(msg, pos) => TypecheckerError(msg.replace("<undefined position>", "<ARP Plugin>"), pos)
          case error: AbstractVerificationError => error.transformedError()
          case default => default
        })
        Failure(errorsPrime.filterNot({
          case ep: PostconditionViolated => errorsPrime.exists(e => e.isInstanceOf[ContractNotWellformed] && e.pos == ep.pos)
          case ep: WhileFailed => errorsPrime.exists(e => e.isInstanceOf[ContractNotWellformed] && e.pos == ep.pos)
          case ep: LoopInvariantNotEstablished => errorsPrime.exists(e => e.isInstanceOf[ContractNotWellformed] && e.pos == ep.pos)
          case ep: LoopInvariantNotPreserved => errorsPrime.exists(e => e.isInstanceOf[ContractNotWellformed] && e.pos == ep.pos)
          case ep: InhaleFailed => errorsPrime.exists(e => e.isInstanceOf[ContractNotWellformed] && e.pos == ep.pos)
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
    val fields = input.fields.filterNot(isFieldIgnored)
    val predicates = input.predicates.filterNot(isPredicateIgnored)

    def generateEqCmp(e1: Seq[Exp], e2: Seq[Exp]): Exp = {
      val eq = EqCmp(e1.head, e2.head)(input.pos, input.info)
      if (e1.size == 1) {
        eq
      } else {
        And(eq, generateEqCmp(e1.tail, e2.tail))(input.pos, input.info)
      }
    }

    val fieldDomain = Domain(
      domainName,
      fields.map(f => DomainFunc(
        naming.getFieldFunctionName(f),
        Seq(), Int, unique = true
      )(input.pos, input.info, domainName)) ++
        predicates.map(p => DomainFunc(
          naming.getPredicateFunctionName(p),
          p.formalArgs, Int, unique = p.formalArgs.isEmpty
        )(input.pos, input.info, domainName)),
      predicates.flatMap(p => if (p.formalArgs.nonEmpty) {
        val localArgs1 = p.formalArgs.map(v => LocalVar(v.name)(v.typ, input.pos, input.info))
        val app1 = DomainFuncApp(naming.getPredicateFunctionName(p), localArgs1, Map[TypeVar, Type]())(input.pos, input.info, Int, p.formalArgs, domainName, NoTrafos)
        val args2 = p.formalArgs.map(a => LocalVarDecl(naming.getNewName(prefix = a.name), a.typ)(input.pos, input.info))
        val localArgs2 = args2.map(v => LocalVar(v.name)(v.typ, input.pos, input.info))
        val app2 = DomainFuncApp(naming.getPredicateFunctionName(p), localArgs2, Map[TypeVar, Type]())(input.pos, input.info, Int, p.formalArgs, domainName, NoTrafos)
        fields.map(f =>
          DomainAxiom(
            naming.getNewName(suffix = p.name + "_" + f.name),
            Forall(
              p.formalArgs,
              Seq(Trigger(Seq(app1))(input.pos, input.info)),
              NeCmp(app1, DomainFuncApp(naming.getFieldFunctionName(f), Seq(), Map[TypeVar, Type]())(input.pos, input.info, Int, Seq(), domainName, NoTrafos))(input.pos, input.info)
            )(input.pos, input.info)
          )(input.pos, input.info, domainName)
        ) ++
          predicates.filterNot(_ == p).map(pp => {
            val args3 = pp.formalArgs.map(a => LocalVarDecl(naming.getNewName(prefix = a.name), a.typ)(input.pos, input.info))
            val localArgs3 = args3.map(v => LocalVar(v.name)(v.typ, input.pos, input.info))
            val app3 = DomainFuncApp(naming.getPredicateFunctionName(pp), localArgs3, Map[TypeVar, Type]())(input.pos, input.info, Int, pp.formalArgs, domainName, NoTrafos)
            DomainAxiom(
              naming.getNewName(suffix = p.name + "_" + pp.name),
              Forall(
                p.formalArgs ++ args3,
                Seq(Trigger(Seq(app1, app3))(input.pos, input.info)),
                NeCmp(app1, app3)(input.pos, input.info)
              )(input.pos, input.info)
            )(input.pos, input.info, domainName)
          }) ++
          Seq(
            DomainAxiom(
              naming.getNewName(suffix = p.name),
              Forall(
                p.formalArgs ++ args2,
                Seq(Trigger(Seq(app1, app2))(input.pos, input.info)),
                Implies(
                  EqCmp(app1, app2)(input.pos, input.info),
                  generateEqCmp(localArgs1, localArgs2)
                )(input.pos, input.info)
              )(input.pos, input.info)
            )(input.pos, input.info, domainName)
          )
      } else {
        Seq()
      }),
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

  def addHavocMethods(input: Program): Program = {
    val newMethods = naming.havocNames.toList.map(kv => {
      Method(kv._2, Seq(), Seq(LocalVarDecl(naming.getNewName("returnval"), kv._1)(input.pos, input.info)), Seq(), Seq(), None)(input.pos, input.info)
    })
    Program(
      input.domains,
      input.fields,
      input.functions,
      input.predicates,
      input.methods ++ newMethods
    )(input.pos, input.info, input.errT)
  }

  def addDummyMethods(originalInput: Program, input: Program): Program = {
    // ensures false is not checked if there is no body, so would not need handle this
    // invariants have other rules for wellformedness than methods, so this does not always work (see issues/silicon/0285.sil)

    var whileMethods = Seq[Method]()
    StrategyBuilder.AncestorVisitor[Node]({
      case (w: While, ctx) if w.invs.nonEmpty =>
        var args = Seq[LocalVarDecl]()
        var quantified = Seq[LocalVarDecl]()
        w.invs.foreach(wi =>
          StrategyBuilder.SlimVisitor[Node]({
            case l@LocalVar(name) => if (!args.exists(a => a.localVar.name == name)) args :+= LocalVarDecl(name, l.typ)(l.pos, l.info)
            case Forall(vars, _, _) => quantified ++= vars
            case Exists(vars, _) => quantified ++= vars
            case _ =>
          }).visit(wi)
        )
        args = args.filterNot(l => quantified.contains(l))
        whileMethods :+= Method(
          naming.getNameFor(w, suffix = "invariant_wellformed_dummy_method"),
          args,
          Seq(),
          Seq(),
          w.invs.filterNot(_.isInstanceOf[BoolLit]).map(utils.rewriteRdForDummyMethod),
//          Seq(utils.rewriteRdForDummyMethod(w.invs.filterNot(_.isInstanceOf[BoolLit]).reduce((a, b) => And(a, b)(a.pos, a.info)))),
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
//        .filter(m => m.pres.nonEmpty || m.posts.nonEmpty) // cant't do this as we need the method for constraining blocks
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

  def rewriteMethodCallsToDummyMethods(input: Program, node: Node): Node = {
    StrategyBuilder.Slim[Node]({
      case m@MethodCall(methodName, args, targets) =>
        val maybeMethod = utils.getMethod(input, methodName)
        if (maybeMethod.isDefined /*&& (maybeMethod.get.pres ++ maybeMethod.get.posts).nonEmpty*/) {
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

  def checkAllRdTransformed(input: Program): Unit = {
    StrategyBuilder.SlimVisitor[Node]({
      case f@FuncApp(naming.rdName, _) =>
        reportError(Internal(f, FeatureUnsupported(f, "rd is not allowed here.")))
      case f@FuncApp(naming.rdCountingName, _) =>
        reportError(Internal(f, FeatureUnsupported(f, "rdc is not allowed here.")))
      case f@FuncApp(naming.rdWildcardName, _) =>
        reportError(Internal(f, FeatureUnsupported(f, "rdw is not allowed here.")))
      case _ =>
    }).visit(input)
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