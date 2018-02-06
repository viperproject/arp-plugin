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

  // TODO: Fix label optimization
  // TODO: Fix while loop contract wellformedness checks
  // TODO: Fix quantified x.f.g
  // TODO: Fix quantified xs[i]
  // TODO: Fix quantified predicates
  // TODO: Check c := perm(x.f) calls (Rewriter thinks assignment was already rewritten)
  // TODO: Handle magic wands correctly

  val utils = new ARPPluginUtils(this)
  val naming = new ARPPluginNaming(this)
  val methods = new ARPPluginMethods(this)
  val loops = new ARPPluginWhile(this)
  val breathe = new ARPPluginBreathe(this)
  val normalize = new ARPPluginNormalize(this)
  val quantified = new ARPPluginQuantified(this)
  val wands = new ARPPluginWands(this)
  val misc = new ARPPluginMisc(this)
  val simple = new ARPPluginSimple(this)
  val performance = new ARPPerformance()
  var ignoredFields = Seq[String]()
  var difficulty = 0
  var methodCallDifficulty = Map[String, Int]()
  var methodBodyDifficulty = Map[String, Int]()
  var predicateBodyDifficulty = Map[String, Int]()

  object Optimize {
    val simplifyExpressions = true
    val removeProvableIf = true
    val noAssumptionForPost = false // this does not work if rd is only present in post condition
    val removeUnnecessaryLabels = true
    val mixSimpleEncoding = false
    val useSimpleEncodingIfPossible = false
    val onlyTransformIfRdUsed = false
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
    performance.start()

    val rdFunction = PFunction(PIdnDef(naming.rdName), Seq(), TypeHelper.Perm, Seq(), Seq(), None, None)

    val intArgument = Seq(PFormalArgDecl(PIdnDef("ARP_LongAndIrrelevantNameToPreventCollisions_314159265358979323846264"), TypeHelper.Int))
    val refArgument = Seq(PFormalArgDecl(PIdnDef("ARP_LongAndIrrelevantNameToPreventCollisions_314159265358979323846264"), TypeHelper.Ref))
    val epsilonFunction = PFunction(PIdnDef(naming.rdCountingName), intArgument, TypeHelper.Perm, Seq(), Seq(), None, None)
    val wildcardFunction = PFunction(PIdnDef(naming.rdWildcardName), Seq(), TypeHelper.Perm, Seq(), Seq(), None, None)
    val globalFunction = PFunction(PIdnDef(naming.rdGlobalName), Seq(), TypeHelper.Perm, Seq(), Seq(), None, None)
    val tokenFunction = PFunction(PIdnDef(naming.rdToken), refArgument, TypeHelper.Perm, Seq(), Seq(), None, None)
    val tokenFreshFunction = PFunction(PIdnDef(naming.rdTokenFresh), refArgument, TypeHelper.Perm, Seq(), Seq(), None, None)

    // If a program already contains a definition for rd we can't use our arp rd
    var alreadyContainsRd = false
    var alreadyContainsRdc = false
    var alreadyContainsRdw = false
    var alreadyContainsGlobalRd = false
    var alreadyContainsTokenRd = false
    var alreadyContainsTokenFreshRd = false
    StrategyBuilder.SlimVisitor[PNode]({
      case PIdnDef(naming.rdName) => alreadyContainsRd = true
      case PIdnDef(naming.rdCountingName) => alreadyContainsRdc = true
      case PIdnDef(naming.rdWildcardName) => alreadyContainsRdw = true
      case PIdnDef(naming.rdGlobalName) => alreadyContainsGlobalRd = true
      case PIdnDef(naming.rdToken) => alreadyContainsTokenRd = true
      case PIdnDef(naming.rdTokenFresh) => alreadyContainsTokenFreshRd = true
      case _ =>
    }).visit(input)

    val sanitizedInput = StrategyBuilder.Slim[PNode]({
      case p@PIdnUse(naming.rdName) if alreadyContainsRd => PIdnUse("WAS_RD_BUT_IS_NOT_ARP_RD").setPos(p)
      case p@PIdnDef(naming.rdName) if alreadyContainsRd => PIdnDef("WAS_RD_BUT_IS_NOT_ARP_RD").setPos(p)
      case p@PIdnUse(naming.rdCountingName) if alreadyContainsRdc => PIdnUse("WAS_RDC_BUT_IS_NOT_ARP_RDC").setPos(p)
      case p@PIdnDef(naming.rdCountingName) if alreadyContainsRdc => PIdnDef("WAS_RDC_BUT_IS_NOT_ARP_RDC").setPos(p)
      case p@PIdnUse(naming.rdWildcardName) if alreadyContainsRdw => PIdnUse("WAS_RDW_BUT_IS_NOT_ARP_RDW").setPos(p)
      case p@PIdnDef(naming.rdWildcardName) if alreadyContainsRdw => PIdnDef("WAS_RDW_BUT_IS_NOT_ARP_RDW").setPos(p)
      case p@PIdnUse(naming.rdWildcardName) if alreadyContainsRdw => PIdnUse("WAS_RDW_BUT_IS_NOT_ARP_RDW").setPos(p)
      case p@PIdnDef(naming.rdGlobalName) if alreadyContainsGlobalRd => PIdnDef("WAS_RDW_BUT_IS_NOT_ARP_GLOBALRD").setPos(p)
      case p@PIdnUse(naming.rdGlobalName) if alreadyContainsGlobalRd => PIdnUse("WAS_RDW_BUT_IS_NOT_ARP_GLOBALRD").setPos(p)
      case p@PIdnDef(naming.rdToken) if alreadyContainsGlobalRd => PIdnDef("WAS_RDTOKEN_BUT_IS_NOT_ARP_RDTOKEN").setPos(p)
      case p@PIdnUse(naming.rdToken) if alreadyContainsGlobalRd => PIdnUse("WAS_RDTOKEN_BUT_IS_NOT_ARP_RDTOKEN").setPos(p)
      case p@PIdnDef(naming.rdTokenFresh) if alreadyContainsGlobalRd => PIdnDef("WAS_RDTOKENFRESH_BUT_IS_NOT_ARP_RDTOKENFRESH").setPos(p)
      case p@PIdnUse(naming.rdTokenFresh) if alreadyContainsGlobalRd => PIdnUse("WAS_RDTOKENFRESH_BUT_IS_NOT_ARP_RDTOKENFRESH").setPos(p)
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
      sanitizedInput.functions :+ rdFunction :+ epsilonFunction :+ wildcardFunction :+ globalFunction :+ tokenFunction :+ tokenFreshFunction,
      sanitizedInput.predicates,
      sanitizedInput.methods.filterNot(p => p.idndef.name == naming.blacklistName),
      sanitizedInput.errors
    )

    // replace all rd with rd()
    val rdRewriter = StrategyBuilder.Ancestor[PNode]({
      case (p@PIdnUse(naming.rdName), ctx) if !ctx.parent.isInstanceOf[PCall] => PCall(p, Seq(), None).setPos(p)
      case (p@PIdnUse(naming.rdWildcardName), ctx) if !ctx.parent.isInstanceOf[PCall] => PCall(p, Seq(), None).setPos(p)
      case (p@PIdnUse(naming.rdGlobalName), ctx) if !ctx.parent.isInstanceOf[PCall] => PCall(p, Seq(), None).setPos(p)
    }, Traverse.BottomUp)

    val inputPrime = rdRewriter.execute[PProgram](inputWithFunctions)

    performance.stop("beforeResolve")

    inputPrime
  }

  override def beforeVerify(input: Program): Program = {
    performance.start()

    analyzeInput(input)

    val inputPrime = if (difficulty == 0 && Optimize.onlyTransformIfRdUsed) {
      input
    } else if (difficulty <= 1 && Optimize.useSimpleEncodingIfPossible) {
      beforeVerifySimple(input)
    } else {
      beforeVerifyFull(input)
    }

    checkAllRdTransformed(inputPrime)

    if (System.getProperty("DEBUG", "").equals("1")) {
      println(inputPrime)
    }

    if (_errors.isEmpty) {
      val checkResult = performance.measure("checkTransitively consistency")(inputPrime.checkTransitively)
      if (checkResult.nonEmpty) {
        checkResult.foreach(ce => reportError(ConsistencyError(ce.message + s" (${ce.pos})", ce.pos)))
      }
    }

    performance.stop("beforeVerify")

    inputPrime
  }

  def beforeVerifySimple(input: Program): Program ={
    simple.transform(input)
  }

  def beforeVerifyFull(input: Program): Program = {
    val inputWithARPDomain = addARPDomain(input)
    naming.init(naming.collectUsedNames(inputWithARPDomain))
    val enhancedInput = addFieldFunctions(rewriteRdPredicate(inputWithARPDomain))

    val arpRewriter = StrategyBuilder.Context[Node, ARPContext](
      {
        case (p: Predicate, ctx) =>
          breathe.handlePredicate(enhancedInput, p, ctx)
        case (m: Method, ctx) =>
          if (Optimize.mixSimpleEncoding && methodBodyDifficulty(m.name) <= 1){
            ctx.noRec(simple.transformNode(enhancedInput, m))
          } else {
            methods.handleMethod(enhancedInput, m, ctx)
          }
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
        case (f: Unfolding, ctx) =>
          breathe.handleUnfolding(enhancedInput, f, ctx)
        case (a: AbstractAssign, ctx) =>
          misc.handleAssignment(enhancedInput, a, ctx)
        case (c: Constraining, ctx) => ctx.noRec(rewriteMethodCallsToDummyMethods(enhancedInput, c))
        case (a: Apply, ctx) => wands.handleApply(enhancedInput, a, ctx)
        case (p: Package, ctx) => ctx.noRec(rewriteMethodCallsToDummyMethods(enhancedInput, wands.handlePackage(enhancedInput, p, ctx)))
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

    val rewrittenInput = performance.measure("arpRewriter")(arpRewriter.execute[Program](enhancedInput))
    val inputPrime = optimizeLabels(addHavocMethods(addDummyMethods(input, rewrittenInput)))
    inputPrime
  }

  override def mapVerificationResult(input: VerificationResult): VerificationResult = {
    if (difficulty == 0 && Optimize.onlyTransformIfRdUsed){
      input
    } else {
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
          val errorsUnique = errorsPrime.map(e => (e, e.pos)).distinct.map(t => t._1)
          Failure(errorsUnique.filterNot({
            case ep: PostconditionViolated => errorsPrime.exists(e => e.isInstanceOf[ContractNotWellformed] && e.pos == ep.pos)
            case ep: WhileFailed => errorsPrime.exists(e => e.isInstanceOf[ContractNotWellformed] && e.pos == ep.pos)
            case ep: LoopInvariantNotEstablished => errorsPrime.exists(e => e.isInstanceOf[ContractNotWellformed] && e.pos == ep.pos)
            case ep: LoopInvariantNotPreserved => errorsPrime.exists(e => e.isInstanceOf[ContractNotWellformed] && e.pos == ep.pos)
            case ep: InhaleFailed => errorsPrime.exists(e => e.isInstanceOf[ContractNotWellformed] && e.pos == ep.pos)
            case _ => false
          }))
      }
    }
  }

  def getDifficulty(node: Node): Int ={
    var difficulty = 0
    def dif(x: Int) = difficulty = math.max(difficulty, x)
    StrategyBuilder.AncestorVisitor[Node]({
      case (FuncApp(naming.rdName, _), ctx) =>
        dif(1)
        if (!ctx.parent.isInstanceOf[AccessPredicate]) {
          dif(2)
        }
      case (FuncApp(naming.rdCountingName, _), ctx) => dif(2)
      case (FuncApp(naming.rdWildcardName, _), ctx) => dif(2)
      case (FuncApp(naming.rdGlobalName, _), ctx) => dif(2)
      case (FuncApp(naming.rdToken, _), ctx) => dif(2)
      case (FuncApp(naming.rdTokenFresh, _), ctx) => dif(2)
      case (MethodCall(method, _, _), ctx) => dif(methodCallDifficulty(method))
      case (Fold(PredicateAccessPredicate(PredicateAccess(_, predicate), _)), ctx) => dif(predicateBodyDifficulty(predicate))
      case (Unfold(PredicateAccessPredicate(PredicateAccess(_, predicate), _)), ctx) => dif(predicateBodyDifficulty(predicate))
      case _ =>
    }).visit(node)
    difficulty
  }

  def analyzeInput(input: Program): Unit ={
    performance.start()
    input.methods.foreach(m => {
      methodCallDifficulty += m.name -> (m.pres ++ m.posts).map(getDifficulty).fold(0)(math.max)
    })
    input.predicates.foreach(p => {
      predicateBodyDifficulty += p.name -> p.body.map(getDifficulty).map(d => if (d == 1) 2 else d).getOrElse(0)
    })
    input.methods.foreach(m => {
      methodBodyDifficulty += m.name -> math.max(m.body.map(getDifficulty).getOrElse(0), methodCallDifficulty(m.name))
    })
    difficulty = (methodCallDifficulty ++ methodBodyDifficulty ++ predicateBodyDifficulty).values.fold(0)(math.max)
    performance.stop("analyzeInput")
  }

  def loadSilFile(file: String): Program = {
    performance.start()
    val path = getClass.getResourceAsStream(file)
    val arpFrontend = new ARPFrontend(this)
    performance.measure("loadSilFile " + file)(arpFrontend.loadFile(file, path) match {
      case Some(program) => program
      case None =>
        val empty = Program(Seq(), Seq(), Seq(), Seq(), Seq())()
        reportError(Internal(FeatureUnsupported(empty, "Could not load ARP Domain")))
        empty
    })
  }

  def addARPDomain(input: Program): Program = {
    performance.start()
    val arpDomainFile = loadSilFile(naming.arpDomainFile)

    val newProgram = Program(
      input.domains ++ arpDomainFile.domains,
      input.fields ++ arpDomainFile.fields,
      input.functions.filterNot(f =>
        f.name == naming.rdName ||
          f.name == naming.rdCountingName ||
          f.name == naming.rdWildcardName ||
          f.name == naming.rdGlobalName ||
          f.name == naming.rdToken ||
          f.name == naming.rdTokenFresh
      ) ++ arpDomainFile.functions,
      input.predicates ++ arpDomainFile.predicates,
      input.methods ++ arpDomainFile.methods
    )(input.pos, input.info, NodeTrafo(input))

    checkUniqueNames(input, arpDomainFile)

    performance.stop("addARPDomain")

    // if there was an error, give back an empty program
    if (_errors.isEmpty) newProgram else Program(Seq(), Seq(), Seq(), Seq(), Seq())()
  }

  def rewriteRdPredicate(input: Program): Program = {
    Program(
      input.domains,
      input.fields,
      input.functions,
      input.predicates.map(utils.rewriteRdPredicate),
      input.methods
    )(input.pos, input.info, NodeTrafo(input))
  }

  def addFieldFunctions(input: Program): Program = {
    performance.start()

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
            val triggers = Seq(app1) ++ (if (args3.nonEmpty) Seq(app3) else Seq())
            DomainAxiom(
              naming.getNewName(suffix = p.name + "_" + pp.name),
              Forall(
                p.formalArgs ++ args3,
                Seq(Trigger(triggers)(input.pos, input.info)),
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

    performance.stop("addFieldFunctions")

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
    performance.start()

    // ensures false is not checked if there is no body, so would not need handle this
    // invariants have other rules for wellformedness than methods, so this does not always work (see issues/silicon/0285.sil)

//    var whileMethods = Seq[Method]()
//    StrategyBuilder.ContextVisitor[Node, Method]({
//      case (w: While, ctx) if w.invs.nonEmpty =>
//        var args = Seq[LocalVarDecl]()
//        var quantified = Seq[LocalVarDecl]()
//        w.invs.foreach(wi =>
//          StrategyBuilder.SlimVisitor[Node]({
//            case l@LocalVar(name) => if (!args.exists(a => a.localVar.name == name)) args :+= LocalVarDecl(name, l.typ)(l.pos, l.info)
//            case Forall(vars, _, _) => quantified ++= vars
//            case Exists(vars, _) => quantified ++= vars
//            case ForPerm(vars, _, _) => quantified :+= vars
//            case _ =>
//          }).visit(wi)
//        )
//        args = args.filterNot(quantified.contains) ++ ctx.c.formalArgs.filterNot(args.contains)
//        whileMethods :+= Method(
//          naming.getNewNameFor(w, suffix = "invariant_wellformed_dummy_method"),
//          args,
//          Seq(),
//          ctx.c.pres.map(utils.rewriteRdForDummyMethod), // precondition of the current method seem to play a role for the contracts as well
//          w.invs.filterNot(_.isInstanceOf[BoolLit]).map(utils.rewriteRdForDummyMethod).map(utils.rewriteLabelledOldExpr),
//          Seq(utils.rewriteRdForDummyMethod(w.invs.filterNot(_.isInstanceOf[BoolLit]).reduce((a, b) => And(a, b)(a.pos, a.info)))),
//          None
//        )(w.pos, w.info)
//      case _ =>
//    },
//      null,
//      {
//        case (m: Method, ctx) => m
//      }
//    ).visit(originalInput)

    val filteredMethods = if (Optimize.mixSimpleEncoding){
      originalInput.methods.filter(m => methodBodyDifficulty(m.name) > 1)
    } else {
      originalInput.methods
    }

    performance.start()
    val methodMethods = filteredMethods.map(m => {
      val rdName = naming.getNewNameFor(m, m.name, "rd")
      Method(
        m.name,
        m.formalArgs :+ LocalVarDecl(rdName, Perm)(m.pos, m.info),
        m.formalReturns,
        utils.constrainRdExp(rdName)(m.pos, m.info) +: m.pres.map(utils.rewriteRdForDummyMethod(rdName)),
        m.posts.map(utils.rewriteRdForDummyMethod(rdName)),
        None
      )(m.pos, m.info, NodeTrafo(input))
    })
    performance.stop("addDummyMethods generate methods")

    val newProgram = Program(
      input.domains,
      input.fields,
      input.functions,
      input.predicates,
      input.methods ++ /*whileMethods ++*/ methodMethods
    )(input.pos, input.info, NodeTrafo(input))

    performance.stop("addDummyMethods")

    newProgram
  }

  def optimizeLabels(input: Program): Program = {
    if (Optimize.removeUnnecessaryLabels){
      performance.measure("optimizeLabels")(Program(
        input.domains,
        input.fields,
        input.functions,
        input.predicates,
        input.methods.map(m => {
          var usedLabels = Set[String]()
          var targetLabels = Set[String]()
          var labelMapping = Map[String, String]()
          StrategyBuilder.SlimVisitor[Node]({
            case LabelledOld(_, name) => usedLabels += name
            case Goto(target) => targetLabels += target
            case _ =>
          }).visit(m)
          StrategyBuilder.SlimVisitor[Node]({
            case Seqn(ss, _) =>
              def collectFollowup(s: Seq[Stmt]): Unit = {
                if (s.size >= 2) {
                  s.head match {
                    case headLabel: Label =>
                      s.tail.head match {
                        case tailLabel: Label if !targetLabels.contains(headLabel.name) && !targetLabels.contains(tailLabel.name) =>
                          labelMapping += tailLabel.name -> labelMapping.getOrElse(headLabel.name, headLabel.name)
                          collectFollowup(s.tail)
                        case Seqn(stmts, _) if stmts.nonEmpty => collectFollowup(Seq(s.head) ++ stmts ++ s.tail)
                        case _ => collectFollowup(s.tail)
                      }
                    case Seqn(stmts, _) if stmts.nonEmpty => collectFollowup(stmts ++ s.tail)
                    case _ => collectFollowup(s.tail)
                  }
                }
              }

              collectFollowup(ss)
            case _ =>
          }).visit(m)
          usedLabels = usedLabels.map(u => labelMapping.getOrElse(u, u))
          val removeLabelStrategy = StrategyBuilder.Slim[Node]({
            case s@Seqn(ss, decls) =>
              def isNodeNeeded(st: Any): Boolean = st match {
                case Label(name, Seq()) => usedLabels.contains(name) || targetLabels.contains(name)
                case _ => true
              }

              Seqn(ss.filter(isNodeNeeded), decls.filter(isNodeNeeded))(s.pos, s.info, NodeTrafo(s))
            case l@LabelledOld(exp, name) if labelMapping.contains(name) =>
              LabelledOld(exp, labelMapping(name))(l.pos, l.info, NodeTrafo(l))
          })
          // do it twice for good measure
          // it seems like creating a nested Seqn does sometimes flatten it and the rewriter does not recurse anymore
          // TODO figure out why this is necessary
          val mPrime = removeLabelStrategy.execute[Method](removeLabelStrategy.execute[Method](m))
          mPrime
        })
      )(input.pos, input.info, NodeTrafo(input)))
    } else {
      input
    }
  }

  def rewriteMethodCallsToDummyMethods(input: Program, node: Node): Node = {
    StrategyBuilder.Slim[Node]({
      case m@MethodCall(methodName, args, targets) =>
        MethodCall(
          methodName,
          args :+ FractionalPerm(IntLit(1)(m.pos, m.info), IntLit(2000)(m.pos, m.info))(m.pos, m.info),
          targets
        )(m.pos, m.info, NodeTrafo(m))
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
        f.name == naming.rdWildcardName ||
        f.name == naming.rdGlobalName ||
        f.name == naming.rdToken ||
        f.name == naming.rdTokenFresh
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