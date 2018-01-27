/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast._

class PerformanceParserExport extends SilverPlugin {
  override def beforeVerify(input: Program): Program = {
    val sb = new StringBuilder()
    dump(sb, input)
    println(sb)

    input
  }

  def dumpAll(sb: StringBuilder, things: Any*): Unit = {
    sb.append("(")
    if (things.nonEmpty){
      things.foreach(t => {
        dump(sb, t)
        sb.append("|")
      })
      sb.setLength(sb.length - 1)
    }
    sb.append(")")
  }

  def dump(sb: StringBuilder, node: Any): Unit = {
    val clazz = node.getClass.getCanonicalName
    def d(things: Any*): Unit = dumpAll(sb, clazz +: things:_*)
    node match {
      case s: String => sb.append(s)
      case s: Seq[Any] => dumpAll(sb, "Seq" +: s:_*)
      case Program(domains, fields, functions, predicats, methods) => d(domains, fields, functions, predicats, methods)
      // Member
      case Domain(name, functions, axioms, typVars) => d(name, functions, axioms, typVars)
      case Field(name, typ) => d(name, typ)
      case Function(name, formalArgs, typ, pres, posts, decs, body) => d(name, formalArgs, typ, pres, posts, decs, body)
      case Predicate(name, args, body) => d(name, args, body)
      case Method(name, formalArgs, formalReturns, pres, posts, body) => d(name, formalArgs, formalReturns, pres, posts, body)
      // DecClause
      case DecTuple(e) => d(e)
      case DecStar() => d()
      // Trigger
      case Trigger(exps) => d(exps)
      // Resource
      case MagicWand(left, right) => d(left, right)
      // Stmt
      case While(cond, invs, body) => d(cond, invs, body)
      case MethodCall(methodName, args, targets) => d(methodName, args, targets)
      case Unfold(acc) => d(acc)
      case Apply(exp) => d(exp)
      case Exhale(exp) => d(exp)
      case Label(name, invs) => d(name, invs)
      case LocalVarDeclStmt(decl) => d(decl)
      case Fresh(vars) => d(vars)
      case Inhale(exp) => d(exp)
      case Seqn(ss, scopedDecls) => d(ss, scopedDecls)
      case Constraining(vars, body) => d(vars, body)
      case If(cond, thn, els) => d(cond, thn, els)
      case FieldAssign(lhs, rhs) => d(lhs, rhs)
      case LocalVarAssign(lhs, rhs) => d(lhs, rhs)
      case Package(wand, proofScript) => d(wand, proofScript)
      case Goto(target) => d(target)
      case NewStmt(lhs, fields) => d(lhs, fields)
      case Assert(exp) => d(exp)
      case Fold(acc) => d(acc)
      // DomainMember
      case DomainFunc(name, formalArgs, typ, unique) => d(name, formalArgs, typ, unique)
      case DomainAxiom(name, exp) => d(name, exp)
      // Exp
      case BinExp(left, right) => d(left, right)
      case WildcardPerm() => d()
      case NoPerm() => d()
      case FullPerm() => d()
      case CurrentPerm(loc) => d(loc)
      case PermMinus(exp) => d(exp)
      case EpsilonPerm() => d()
      case ExplicitSet(elems) => d(elems)
      case AnySetCardinality(s) => d(s)
      case EmptySet(elemTyp) => d(elemTyp)
      case FuncApp(funcname, args) => d(funcname, args)
      case EmptyMultiset(elemTyp) => d(elemTyp)
      case ExplicitMultiset(elems) => d(elems)
      // TODO: Starting from SeqExp in PossibleTrigger
      // Type
      case DomainType(domainName, typVarsMap) => d(domainName, typVarsMap)
      case SetType(elementType) => d(elementType)
      case MultisetType(elementType) => d(elementType)
      case SeqType(elementType) => d(elementType)
      case Bool => d()
      case Int => d()
      case Wand => d()
      case InternalType => d()
      case Perm => d()
      case Ref => d()
      case TypeVar(name) => d(name)
      case LocalVarDecl(name, typ) => d(name, typ)
      // not found
      case _ => sb.append("NOT_IMPLEMENTED ").append(clazz)
    }
  }
}

class PerformanceParser extends SilverPlugin {

}