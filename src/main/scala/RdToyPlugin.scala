/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.{StrategyBuilder, Traverse}
import viper.silver.parser._
import viper.silver.verifier._

class RdToyPlugin extends SilverPlugin {

  override def beforeResolve(input: PProgram): PProgram = {
    if (false) {
      // replace all rd with rd()
      val pRdRewriter = StrategyBuilder.Slim[PNode]({
        case PIdnUse("rd") => PCall(PIdnUse("rd"), Seq(), None)
      }, Traverse.BottomUp)

      // inject functions for rd() and rdc()
      val inputPrime = pRdRewriter.execute[PProgram](PProgram(
        input.imports,
        input.macros,
        input.domains,
        input.fields,
        input.functions
          :+ PFunction(
          PIdnDef("rd"),
          Seq(),
          TypeHelper.Perm,
          Seq(),
          Seq(),
          None,
          None
        )
          :+ PFunction(
          PIdnDef("rdc"),
          Seq(PFormalArgDecl(PIdnDef("x"), TypeHelper.Int)),
          TypeHelper.Perm,
          Seq(PBinExp(PIdnUse("x"), ">", PIntLit(0))),
          Seq(),
          None,
          Some(PBinExp(PIdnUse("x"), "*", PBinExp(PIntLit(1), "/", PIntLit(1000000))))
        ),
        input.predicates,
        input.methods,
        input.errors
      ))

      inputPrime
    } else {
      input
    }
  }

  override def beforeMethodFilter(input: Program): Program = {
    if (false) {
      // add ghost parameter rd, replace rd() with rd
      val rdRewriter = StrategyBuilder.Slim[Node]({
        case m@Method(name, formalArgs, formalReturns, pres, posts, body) =>
          Method(
            name,
            formalArgs :+ LocalVarDecl("rd", Perm)(m.pos, m.info),
            formalReturns,
            And(
              PermLtCmp(
                NoPerm()(m.pos, m.info),
                LocalVar("rd")(Perm, m.pos, m.info)
              )(m.pos, m.info),
              PermLeCmp(
                LocalVar("rd")(Perm, m.pos, m.info),
                FullPerm()(m.pos, m.info)
              )(m.pos, m.info)
            )(m.pos, m.info)
              +: pres,
            posts,
            body
          )(m.pos, m.info)
        case m@MethodCall(methodName, args, targets) =>
          MethodCall(
            methodName,
            args
              :+ PermDiv(FuncApp("rd", Seq())(m.pos, m.info, Perm, Seq(), NoTrafos), IntLit(2)(m.pos, m.info, m.errT))(m.pos, m.info),
            targets
          )(m.pos, m.info, NoTrafos)
        case f@FuncApp("rd", Seq()) =>
          LocalVar("rd")(Perm, f.pos, f.info)
      })

      val programPrime = rdRewriter.execute[Program](input)
      println(programPrime)
      programPrime
    } else {
      val inputPrime = StrategyBuilder.Ancestor[Node]({
        case (l@LocalVarAssign(lhs, rhs), ctx) =>
          Seqn(
            Seq(
              Assert(NeCmp(lhs, rhs)())(),
              ctx.noRec[LocalVarAssign](l)
            ),
            Seq()
          )()
      }).execute[Program](input)

      println(inputPrime)

      inputPrime
    }
  }

  override def beforeFinish(input: VerificationResult): VerificationResult = {
    input match {
      case Success =>
        Success
      case Failure(errors) =>
        Failure(errors.map {
          case ParseError(msg, pos) => ParseError(s"Expected $msg ($pos)", pos)
          case TypecheckerError(msg, pos) => TypecheckerError(msg.replace("<undefined position>", "<RdToy Plugin>"), pos)
          case error: AbstractVerificationError => error.transformedError()
          case default => default
        })
    }
  }
}
