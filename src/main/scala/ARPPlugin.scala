/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin
import viper.silver.ast
import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.{StrategyBuilder, Traverse}
import viper.silver.parser._
import viper.silver.verifier._
import viper.silver.verifier.errors.{ExhaleFailed, InhaleFailed, PostconditionViolated, PreconditionInCallFalse}

class ARPPlugin extends SilverPlugin{

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

    val rdcFunction = PFunction(
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
      input.functions :+ rdFunction :+ rdcFunction,
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
    def rewriteOldExpr(labelName: String)(node: Exp) ={
      StrategyBuilder.Slim[Node]({
        case o@Old(exp) => LabelledOld(exp, labelName)(o.pos, o.info, o.errT + NodeTrafo(o))
      }).execute[Exp](node)
    }

    def constrainRdExp(methodRdName: String)(pos: Position, info: Info, errT: ErrorTrafo) =
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

    def rewriteRd(contextRdName: String)(node: Exp) ={
      StrategyBuilder.Slim[Node]({
        case f@FuncApp("rd", Seq()) => LocalVar(contextRdName)(Perm, f.pos, f.info, f.errT)
      }).execute[Exp](node)
    }

    val arpRewriter = StrategyBuilder.Context[Node, String](
      {
        // add rd argument to method
        case (m@Method(name, formalArgs, formalReturns, pres, posts, body), ctx) =>
          val methodRdName = ARPPlugin.getName(name + "_rd")
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
          ARPPlugin.getMethod(input, methodName) match {
            case Some(method) =>
              val newErrTrafo = m.errT + NodeTrafo(m)
              val labelName = "label_" + ARPPlugin.getNewName
              val methodRdName = ARPPlugin.getNewName + "_rd"
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
                Seq() /* TODO: What's the deal with this? */
              )(m.pos, m.info, newErrTrafo)
            case None => m
          }

        case (a@Assert(exp), ctx) =>
          Assert(rewriteRd(ctx.c)(exp))(a.pos, a.info, a.errT + NodeTrafo(a))

        // TODO: rewrite inhale/exhale statements
        // TODO: rewrite while loops
      },
      "", // default context
      {
        case (m@Method(name, _, _, _, _, _), _) =>
          ARPPlugin.getName(name + "_rd")
        case (While(_, _, _), _) =>
          ARPPlugin.getNewName + "_rd"
      }
    )

    val arpRewriterOld = StrategyBuilder.Slim[Node]({
      case m@MethodCall(methodName, args, targets) =>
        ARPPlugin.getMethod(input, methodName) match {
          case Some(method) =>
            val labelName = "label_" + ARPPlugin.getNewName
            Seqn(
              Seq(Label(labelName, Seq())(m.pos, m.info, m.errT)) ++
              method.pres.map(p => Exhale(rewriteOldExpr(labelName)(p))(p.pos, p.info, p.errT)) ++
              method.posts.map(p => Inhale(rewriteOldExpr(labelName)(p))(p.pos, p.info, p.errT)),
              Seq() /* TODO: What's the deal with this? */)(m.pos, m.info, m.errT)
          case None => m
        }
    })

    val inputPrime = arpRewriter.execute[Program](input)

    println(inputPrime)
    inputPrime
  }

  override def beforeFinish(input: VerificationResult): VerificationResult = {
    input match {
      case Success =>
        Success
      case Failure(errors) =>
        Failure(errors.map {
          case TypecheckerError(msg, pos) => TypecheckerError(msg.replace("<undefined position>", "<ARP Plugin>"), pos)
          case error: AbstractVerificationError => error.transformedError() // TODO: Add ErrorTransformation Information to AST
          case default => default
        })
    }
  }
}

object ARPPlugin {

  var nameIndex = 0

  def getMethod(program: Program, method: String): Option[Method] = {
    program.methods.find(m => m.name == method)
  }

  def getName(suffix: String): String = "ARP_FRESHNAME_" + suffix

  def getLastNewName: String = "ARP_FRESHNAME_" + nameIndex

  def getNewName: String ={
    nameIndex += 1
    "ARP_FRESHNAME_" + nameIndex // TODO: figure out a way to generate unique names (i.e. don't just hope no one else uses the name
  }

}
