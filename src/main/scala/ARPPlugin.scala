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
import viper.silver.verifier.errors.{ExhaleFailed, LoopInvariantNotEstablished, PreconditionInCallFalse}

import scala.collection.immutable.HashMap

class ARPPlugin extends SilverPlugin {

  val ARP_DOMAIN_FILE = "/ARPDomain.sil"

  var _errors: Seq[AbstractError] = Seq[AbstractError]()

  var nameIndex = 0

  var newNameMap = new HashMap[Node, String]

  def getMethod(program: Program, method: String): Option[Method] = {
    program.methods.find(m => m.name == method)
  }

  def getName(suffix: String): String = "ARP_FRESHNAME_" + suffix

  def getLastNewName: String = getName(nameIndex.toString)

  def getNewName: String = {
    nameIndex += 1
    // TODO: figure out a way to generate unique names (i.e. don't just hope no one else uses the name)
    // TODO: use the same name for whiles of the same scope
    "ARP_FRESHNAME_" + nameIndex
  }

  def getNewNameFor(node: Node, suffix: String = ""): String = {
    if (newNameMap.contains(node)) {
      newNameMap(node) + suffix
    } else {
      val newName = getNewName
      newNameMap += node -> newName
      newName + suffix
    }
  }

  def constrainRdExp(methodRdName: String)(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): Exp =
    And(
      PermLtCmp(
        NoPerm()(pos, info, errT),
        LocalVar(methodRdName)(Perm, pos, info, errT)
      )(pos, info, errT),
      PermLeCmp(
        LocalVar(methodRdName)(Perm, pos, info, errT),
        FullPerm()(pos, info, errT)
      )(pos, info, errT)
    )(pos, info, errT)

  def loadSilFile(file: String): Program = {
    val path = Paths.get(getClass.getResource(file).toURI)
    val arpFrontend = new ARPFrontend
    arpFrontend.loadFile(path) match {
      case Some(program) => program
      case None => Program(Seq(), Seq(), Seq(), Seq(), Seq())() // TODO: Probably not the best way to do it
    }
  }

  def addARPDomain(input: Program): Program = {
    val arpDomainFile = loadSilFile(ARP_DOMAIN_FILE)

    val newProgram = Program(
      input.domains ++ arpDomainFile.domains,
      input.fields ++ arpDomainFile.fields,
      input.functions.filterNot(f => f.name == "rd" || f.name == "rdc") ++ arpDomainFile.functions,
      input.predicates ++ arpDomainFile.predicates,
      input.methods ++ arpDomainFile.methods
    )(input.pos, input.info, input.errT)

    // TODO: There is no easy way report back errors from within a plugin
    // TODO: Is there a better way to check for duplicates?
    // check name clashes
    input.domains.filter(d => arpDomainFile.domains.exists(dd => dd.name == d.name)).foreach(d => {
      _errors :+= TypecheckerError(s"Duplicate domain '${d.name}'", d.pos)
    })
    input.fields.filter(f => arpDomainFile.fields.exists(ff => ff.name == f.name)).foreach(f => {
      _errors :+= TypecheckerError(s"Duplicate field '${f.name}'", f.pos)
    })
    input.functions.filterNot(f => f.name == "rd" || f.name == "rdc")
      .filter(f => arpDomainFile.functions.exists(ff => ff.name == f.name)).foreach(f => {
      _errors :+= TypecheckerError(s"Duplicate function '${f.name}'", f.pos)
    })
    input.predicates.filter(p => arpDomainFile.predicates.exists(pp => pp.name == p.name)).foreach(p => {
      _errors :+= TypecheckerError(s"Duplicate predicate '${p.name}'", p.pos)
    })
    input.methods.filter(m => arpDomainFile.methods.exists(mm => mm.name == m.name)).foreach(m => {
      _errors :+= TypecheckerError(s"Duplicate method '${m.name}'", m.pos)
    })

    newProgram
  }

  override def beforeResolve(input: PProgram): PProgram = {

    val rdFunction = PFunction(
      PIdnDef("rd"),
      Seq(),
      TypeHelper.Perm,
      Seq(PBoolLit(false)), // make sure all references to rd are transformed
      Seq(),
      None,
      None
    )

    val epsilonFunction = PFunction(
      PIdnDef("rdc"),
      Seq(PFormalArgDecl(PIdnDef("x"), TypeHelper.Int)),
      TypeHelper.Perm,
      Seq(PBoolLit(false)), // make sure all references to rdc are transformed
      Seq(),
      None,
      None
    )

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
      case PIdnUse("rd") => PCall(PIdnUse("rd"), Seq(), None)
    }, Traverse.BottomUp)

    val inputPrime = rdRewriter.execute[PProgram](inputWithFunctions)

    inputPrime
  }

  override def beforeVerify(input: Program): Program = {
    val enhancedInput = addARPDomain(input)

    def rewriteOldExpr(labelName: String)(node: Exp) = {
      StrategyBuilder.Slim[Node]({
        case o@Old(exp) => LabelledOld(exp, labelName)(o.pos, o.info, o.errT + NodeTrafo(o))
      }).execute[Exp](node)
    }

    def rewriteRd(contextRdName: String)(node: Exp) = {
      StrategyBuilder.Slim[Node]({
        case f@FuncApp("rd", Seq()) => LocalVar(contextRdName)(Perm, f.pos, f.info, f.errT + NodeTrafo(f))
        case f@FuncApp("rdc", Seq(arg: Exp)) =>
          PermMul(
            arg,
            FuncApp("epsilonRd", Seq())(f.pos, f.info, f.typ, f.formalArgs, f.errT)
          )(f.pos, f.info, f.errT + NodeTrafo(f))
      }).execute[Exp](node)
    }

    val arpRewriter = StrategyBuilder.Context[Node, String](
      {
        // add rd argument to method
        case (m@Method(name, formalArgs, formalReturns, pres, posts, body), ctx) =>
          val methodRdName = getNewNameFor(m, "_rd")
          val rdArg = LocalVarDecl(methodRdName, Perm)(m.pos, m.info, m.errT)
          Method(
            name,
            formalArgs :+ rdArg,
            formalReturns,
            constrainRdExp(methodRdName)(m.pos, m.info, m.errT) +: pres.map(rewriteRd(methodRdName)),
            posts.map(rewriteRd(methodRdName)),
            body // TODO: init Log
          )(m.pos, m.info, m.errT + NodeTrafo(m))

        // desugar method calls into explicit inhales/exhales
        case (m@MethodCall(methodName, args, targets), ctx) =>
          getMethod(enhancedInput, methodName) match {
            case Some(method) =>
              val newErrTrafo = m.errT + NodeTrafo(m)
              val labelName = "label_" + getNewName
              val methodRdName = getNewNameFor(m, "_rd")
              Seqn(
                Seq(
                  Label(labelName, Seq())(m.pos, m.info, newErrTrafo),
                  LocalVarDeclStmt(LocalVarDecl(methodRdName, Perm)(m.pos, m.info, newErrTrafo))(m.pos, m.info, newErrTrafo),
                  Inhale(constrainRdExp(methodRdName)(m.pos, m.info, newErrTrafo))(m.pos, m.info, newErrTrafo)
                  // TODO: constrain methodRd further
                ) ++
                  // TODO: Add inhales/exhales to Log
                  method.pres.map(p => Exhale(
                    rewriteRd(methodRdName)(rewriteOldExpr(labelName)(p))
                  )(p.pos, p.info, p.errT + NodeTrafo(p) + ErrTrafo({
                    case ExhaleFailed(node, reason, cached) =>
                      PreconditionInCallFalse(m, reason, cached)
                  }))) ++
                  method.posts.map(p => Inhale(
                    rewriteRd(methodRdName)(rewriteOldExpr(labelName)(p))
                  )(p.pos, p.info, p.errT + NodeTrafo(p))),
                Seq() /* TODO: What's the deal with this? Labels are mentioned here? */
              )(m.pos, m.info, newErrTrafo)
            case None => m
          }
        case (w@While(cond, invs, body), ctx) =>
          if (invs.isEmpty) {
            w
          } else {
            val whileRdName = getNewNameFor(w, "_rd")
            val newErrTrafo = w.errT + NodeTrafo(w)
            Seqn(
              Seq(
                LocalVarDeclStmt(LocalVarDecl(whileRdName, Perm)(w.pos, w.info, newErrTrafo))(w.pos, w.info, newErrTrafo),
                Inhale(constrainRdExp(whileRdName)(w.pos, w.info, newErrTrafo))(w.pos, w.info, newErrTrafo)
              ) ++
                invs.map(i => Exhale(
                  rewriteRd(whileRdName)(i)
                )(i.pos, i.info, i.errT + NodeTrafo(i) + ErrTrafo({
                  case ExhaleFailed(node, reason, cached) =>
                    LoopInvariantNotEstablished(i, reason, cached)
                }))) ++
                Seq(
                  While(cond, Seq(),
                    Seqn(
                      invs.map(i => Inhale(
                        rewriteRd(whileRdName)(i)
                      )(i.pos, i.info, i.errT + NodeTrafo(i))) ++
                        Seq(body) ++
                        invs.map(i => Exhale(
                          rewriteRd(whileRdName)(i)
                        )(i.pos, i.info, i.errT + NodeTrafo(i) + ErrTrafo({
                          case ExhaleFailed(node, reason, cached) =>
                            LoopInvariantNotEstablished(i, reason, cached)
                        }))),
                      Seq() /* TODO: What's the deal with this? */
                    )(w.pos, w.info, newErrTrafo)
                  )(w.pos, w.info, newErrTrafo)
                ) ++
                invs.map(i => Inhale(
                  rewriteRd(whileRdName)(i)
                )(i.pos, i.info, i.errT + NodeTrafo(i))),
              Seq() /* TODO: What's the deal with this? */
            )(w.pos, w.info, newErrTrafo)
          }

        case (a@Assert(exp), ctx) =>
          Assert(rewriteRd(ctx.c)(exp))(a.pos, a.info, a.errT + NodeTrafo(a))
        case (e@Exhale(exp), ctx) =>
          e
        case (i@Inhale(exp), ctx) =>
          i

        // TODO: rewrite inhale/exhale statements (to if-construct from writeup)
      },
      "", // default context
      {
        case (m@Method(name, _, _, _, _, _), _) =>
          getNewNameFor(m, "_rd")
        case (w@While(_, _, _), _) =>
          getNewNameFor(w, "_rd")
      }
    )

    val arpRewriterOld = StrategyBuilder.Slim[Node]({
      case m@MethodCall(methodName, args, targets) =>
        getMethod(enhancedInput, methodName) match {
          case Some(method) =>
            val labelName = "label_" + getNewName
            Seqn(
              Seq(Label(labelName, Seq())(m.pos, m.info, m.errT)) ++
                method.pres.map(p => Exhale(rewriteOldExpr(labelName)(p))(p.pos, p.info, p.errT)) ++
                method.posts.map(p => Inhale(rewriteOldExpr(labelName)(p))(p.pos, p.info, p.errT)),
              Seq() /* TODO: What's the deal with this? */)(m.pos, m.info, m.errT)
          case None => m
        }
    })

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
}
