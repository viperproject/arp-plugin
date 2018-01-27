/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast._

class PerformanceParserExport extends SilverPlugin {
  override def beforeVerify(input: Program): Program = {
    val start = System.currentTimeMillis()
    val sb = new StringBuilder()
    dump(sb, input)
    val end = System.currentTimeMillis()
    println(sb)
    if (System.getProperty("DEBUGPERF", "").equals("1")) {
      println("Export finished in " + (end - start) / 1000.0 + " seconds.")
    }

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
//    val clazz = node.getClass.getCanonicalName
    val clazz = node.getClass.getSimpleName
    def d(things: Any*): Unit = dumpAll(sb, clazz +: things:_*)
    node match {
      case s: String => sb.append(s)
      case b: Boolean => sb.append("(b|").append(b).append(")")
      case b: BigInt => sb.append("(i|").append(b).append(")")
      case s: Seq[Any] => dumpAll(sb, "Seq" +: s:_*)
      case t: (Any, Any) => dumpAll(sb, "Tuple2", t._1, t._2)
      case m: Map[Any@unchecked , Any@unchecked ] => dumpAll(sb, "Map" +: m.toSeq:_*)
      case Some(x) => dumpAll(sb, "Some", x)
      case None => dumpAll(sb, "None")

      case DecStar() => d()
      case DecTuple(e) => d(e)
      case Domain(name, functions, axioms, typVars) => d(name, functions, axioms, typVars)
      case a@DomainAxiom(name, exp) => d(name, exp, a.domainName)
      case f@DomainFunc(name, formalArgs, typ, unique) => d(name, formalArgs, typ, unique, f.domainName)
      case Field(name, typ) => d(name, typ)
      case Function(name, formalArgs, typ, pres, posts, decs, body) => d(name, formalArgs, typ, pres, posts, decs, body)
      case LocalVarDecl(name, typ) => d(name, typ)
      case Method(name, formalArgs, formalReturns, pres, posts, body) => d(name, formalArgs, formalReturns, pres, posts, body)
      case Predicate(name, formalArgs, body) => d(name, formalArgs, body)
      case Program(domains, fields, functions, predicates, methods) => d(domains, fields, functions, predicates, methods)

      case Apply(exp) => d(exp)
      case Assert(exp) => d(exp)
      case Constraining(vars, body) => d(vars, body)
      case Exhale(exp) => d(exp)
      case FieldAssign(lhs, rhs) => d(lhs, rhs)
      case Fold(acc) => d(acc)
      case Fresh(vars) => d(vars)
      case Goto(target) => d(target)
      case If(cond, thn, els) => d(cond, thn, els)
      case Inhale(exp) => d(exp)
      case Label(name, invs) => d(name, invs)
      case LocalVarAssign(lhs, rhs) => d(lhs, rhs)
      case LocalVarDeclStmt(decl) => d(decl)
      case MethodCall(methodName, args, targets) => d(methodName, args, targets)
      case NewStmt(lhs, fields) => d(lhs, fields)
      case Package(wand, proofScript) => d(wand, proofScript)
      case Seqn(ss, scopedDecls) => d(ss, scopedDecls)
      case Unfold(acc) => d(acc)
      case While(cond, invs, body) => d(cond, invs, body)

      case Add(left, right) => d(left, right)
      case And(left, right) => d(left, right)
      case AnySetCardinality(s) => d(s)
      case AnySetContains(elem, s) => d(elem, s)
      case AnySetIntersection(left, right) => d(left, right)
      case AnySetMinus(left, right) => d(left, right)
      case AnySetSubset(left, right) => d(left, right)
      case AnySetUnion(left, right) => d(left, right)
      case Applying(wand, body) => d(wand, body)
      case CondExp(cond, thn, els) => d(cond, thn, els)
      case CurrentPerm(loc) => d(loc)
      case Div(left, right) => d(left, right)
      case f@DomainFuncApp(funcname, args, typVarMap) => d(funcname, args, typVarMap, f.typ, f.formalArgs, f.domainName)
      case EmptyMultiset(elemTyp) => d(elemTyp)
      case EmptySeq(elemTyp) => d(elemTyp)
      case EmptySet(elemTyp) => d(elemTyp)
      case EpsilonPerm() => d()
      case EqCmp(left, right) => d(left, right)
      case Exists(variables, exp) => d(variables, exp)
      case ExplicitMultiset(elems) => d(elems)
      case ExplicitSeq(elems) => d(elems)
      case ExplicitSet(elems) => d(elems)
      case FalseLit() => d()
      case FieldAccess(rcv, field) => d(rcv, field)
      case FieldAccessPredicate(loc, perm) => d(loc, perm)
      case ForPerm(variable, accessList, body) => d(variable, accessList, body)
      case Forall(variables, triggers, exp) => d(variables, triggers, exp)
      case FractionalPerm(left, right) => d(left, right)
      case FullPerm() => d()
      case f@FuncApp(funcname, args) => d(funcname, args, f.typ, f.formalArgs)
      case GeCmp(left, right) => d(left, right)
      case GtCmp(left, right) => d(left, right)
      case Implies(left, right) => d(left, right)
      case InhaleExhaleExp(in, ex) => d(in, ex)
      case IntLit(i) => d(i)
      case IntPermMul(left, right) => d(left, right)
      case LabelledOld(exp, oldLabel) => d(exp, oldLabel)
      case LeCmp(left, right) => d(left, right)
      case Let(variable, exp, body) => d(variable, exp, body)
      case l@LocalVar(name) => d(name, l.typ)
      case LtCmp(left, right) => d(left, right)
      case MagicWand(left, right) => d(left, right)
      case Minus(exp) => d(exp)
      case Mod(left, right) => d(left, right)
      case Mul(left, right) => d(left, right)
      case NeCmp(left, right) => d(left, right)
      case NoPerm() => d()
      case Not(exp) => d(exp)
      case NullLit() => d()
      case Old(exp) => d(exp)
      case Or(left, right) => d(left, right)
      case PermAdd(left, right) => d(left, right)
      case PermDiv(left, right) => d(left, right)
      case PermGeCmp(left, right) => d(left, right)
      case PermGtCmp(left, right) => d(left, right)
      case PermLeCmp(left, right) => d(left, right)
      case PermLtCmp(left, right) => d(left, right)
      case PermMinus(exp) => d(exp)
      case PermMul(left, right) => d(left, right)
      case PermSub(left, right) => d(left, right)
      case PredicateAccess(args, predicateName) => d(args, predicateName)
      case PredicateAccessPredicate(loc, perm) => d(loc, perm)
      case RangeSeq(low, high) => d(low, high)
      case r@Result() => d(r.typ)
      case SeqAppend(left, right) => d(left, right)
      case SeqContains(elem, s) => d(elem, s)
      case SeqDrop(s, n) => d(s, n)
      case SeqIndex(s, idx) => d(s, idx)
      case SeqLength(s) => d(s)
      case SeqTake(s, n) => d(s, n)
      case SeqUpdate(s, idx, elem) => d(s, idx, elem)
      case Sub(left, right) => d(left, right)
      case Trigger(exps) => d(exps)
      case TrueLit() => d()
      case Unfolding(acc, body) => d(acc, body)
      case WildcardPerm() => d()

      case Bool => d()
      case t@DomainType(domainName, typVarsMap) => d(domainName, typVarsMap, t.typeParameters)
      case Int => d()
      case InternalType => d()
      case MultisetType(elementType) => d(elementType)
      case Perm => d()
      case Ref => d()
      case SetType(elementType) => d(elementType)
      case SeqType(elementType) => d(elementType)
      case TypeVar(name) => d(name)
      case Wand => d()

      // not found
      case _ => sb.append("NOT_IMPLEMENTED ").append(clazz)
    }
  }
}

class PerformanceParser extends SilverPlugin {

  var parsed: Option[Program] = None
  var printDebug: Boolean = false

  override def beforeParse(input: String): String ={
    val inp = input.trim

    printDebug = System.getProperty("DEBUG", "").equals("1")

    if (inp.startsWith("(") && inp.endsWith(")")){
      val start = System.currentTimeMillis()
      parsed = Some(parse[Program](ParsePosition(inp)))
      val end = System.currentTimeMillis()
      if (System.getProperty("DEBUGPERF", "").equals("1")) {
        println("Parse finished in " + (end - start) / 1000.0 + " seconds.")
      }

      ""
    } else {
      println("Warning: No Performance Parser input found")
      input
    }
  }

  override def beforeVerify(input: Program): Program = {
    parsed.getOrElse(input)
  }

  def parse[T](pp: ParsePosition): T = {
    def p[S](): S = {
      val value = parse[S](pp)
      pp.advance()
      assert(pp.prev == '|' || pp.prev == ')')
      value
    }
    if (pp.current == '('){
      val start = pp.advance('|', ')')
      val typ = pp.subfrom(start+1)
      if (printDebug) {
        println(pp.pos + " " + typ)
      }
      pp.advance()
      (typ match {
        case "i" =>
          val istart = pp.advance(')')
          val result = BigInt(pp.subfrom(istart))
          pp.advance()
          result
        case "b" =>
          val istart = pp.advance(')')
          val result = pp.subfrom(istart) == "true"
          pp.advance()
          result
        case "Seq" =>
          var s = Seq[Any]()
          while(pp.prev != ')'){
            s :+= p()
          }
          s
        case "Tuple2" => (p(), p())
        case "Map" =>
          var m = Map[Any, Any]()
          while(pp.prev != ')'){
            m += p()
          }
          m
        case "Some" => Some(p())
        case "None" =>
          None

        case "DecStar" => DecStar()()
        case "DecTuple" => DecTuple(p[Seq[Exp]]() /* e */)()
        case "Domain" => Domain(p[String]() /* name */, p[Seq[DomainFunc]]() /* functions */, p[Seq[DomainAxiom]]() /* axioms */, p[Seq[TypeVar]]() /* typVars */)()
        case "DomainAxiom" => DomainAxiom(p[String]() /* name */, p[Exp]() /* exp */)(domainName = p[String]())
        case "DomainFunc" => DomainFunc(p[String]() /* name */, p[Seq[LocalVarDecl]]() /* formalArgs */, p[Type]() /* typ */, p[Boolean]() /* unique */)(domainName = p[String]())
        case "Field" => Field(p[String]() /* name */, p[Type]() /* typ */)()
        case "Function" => Function(p[String]() /* name */, p[Seq[LocalVarDecl]]() /* formalArgs */, p[Type]() /* typ */, p[Seq[Exp]]() /* pres */, p[Seq[Exp]]() /* posts */, p[Option[DecClause]]() /* decs */, p[Option[Exp]]() /* body */)()
        case "LocalVarDecl" => LocalVarDecl(p[String]() /* name */, p[Type]() /* typ */)()
        case "Method" => Method(p[String]() /* name */, p[Seq[LocalVarDecl]]() /* formalArgs */, p[Seq[LocalVarDecl]]() /* formalReturns */, p[Seq[Exp]]() /* pres */, p[Seq[Exp]]() /* posts */, p[Option[Seqn]]() /* body */)()
        case "Predicate" => Predicate(p[String]() /* name */, p[Seq[LocalVarDecl]]() /* formalArgs */, p[Option[Exp]]() /* body */)()
        case "Program" => Program(p[Seq[Domain]]() /* domains */, p[Seq[Field]]() /* fields */, p[Seq[Function]]() /* functions */, p[Seq[Predicate]]() /* predicates */, p[Seq[Method]]() /* methods */)()

        case "Apply" => Apply(p[MagicWand]() /* exp */)()
        case "Assert" => Assert(p[Exp]() /* exp */)()
        case "Constraining" => Constraining(p[Seq[LocalVar]]() /* vars */, p[Seqn]() /* body */)()
        case "Exhale" => Exhale(p[Exp]() /* exp */)()
        case "FieldAssign" => FieldAssign(p[FieldAccess]() /* lhs */, p[Exp]() /* rhs */)()
        case "Fold" => Fold(p[PredicateAccessPredicate]() /* acc */)()
        case "Fresh" => Fresh(p[Seq[LocalVar]]() /* vars */)()
        case "Goto" => Goto(p[String]() /* target */)()
        case "If" => If(p[Exp]() /* cond */, p[Seqn]() /* thn */, p[Seqn]() /* els */)()
        case "Inhale" => Inhale(p[Exp]() /* exp */)()
        case "Label" => Label(p[String]() /* name */, p[Seq[Exp]]() /* invs */)()
        case "LocalVarAssign" => LocalVarAssign(p[LocalVar]() /* lhs */, p[Exp]() /* rhs */)()
        case "LocalVarDeclStmt" => LocalVarDeclStmt(p[LocalVarDecl]() /* decl */)()
        case "MethodCall" => MethodCall(p[String]() /* methodName */, p[Seq[Exp]]() /* args */, p[Seq[LocalVar]]() /* targets */)(NoPosition, NoInfo, NoTrafos)
        case "NewStmt" => NewStmt(p[LocalVar]() /* lhs */, p[Seq[Field]]() /* fields */)()
        case "Package" => Package(p[MagicWand]() /* wand */, p[Seqn]() /* proofScript */)()
        case "Seqn" => Seqn(p[Seq[Stmt]]() /* ss */, p[Seq[Declaration]]() /* scopedDecls */)()
        case "Unfold" => Unfold(p[PredicateAccessPredicate]() /* acc */)()
        case "While" => While(p[Exp]() /* cond */, p[Seq[Exp]]() /* invs */, p[Seqn]() /* body */)()

        case "Add" => Add(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "And" => And(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "AnySetCardinality" => AnySetCardinality(p[Exp]() /* s */)()
        case "AnySetContains" => AnySetContains(p[Exp]() /* elem */, p[Exp]() /* s */)()
        case "AnySetIntersection" => AnySetIntersection(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "AnySetMinus" => AnySetMinus(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "AnySetSubset" => AnySetSubset(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "AnySetUnion" => AnySetUnion(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "Applying" => Applying(p[MagicWand]() /* wand */, p[Exp]() /* body */)()
        case "CondExp" => CondExp(p[Exp]() /* cond */, p[Exp]() /* thn */, p[Exp]() /* els */)()
        case "CurrentPerm" => CurrentPerm(p[LocationAccess]() /* loc */)()
        case "Div" => Div(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "DomainFuncApp" =>
          // some parameters are lazy and would have a bad influence
          val funcname = p[String]()
          val args = p[Seq[Exp]]()
          val typeVarMap = p[Map[TypeVar, Type]]()
          val typ = p[Type]()
          val formalArgs = p[Seq[LocalVarDecl]]()
          val domainName = p[String]()
          DomainFuncApp(funcname /* funcname */, args /* args */, typeVarMap /* typVarMap */)(NoPosition, NoInfo, typ, formalArgs, domainName, NoTrafos)
        case "EmptyMultiset" => EmptyMultiset(p[Type]() /* elemTyp */)()
        case "EmptySeq" => EmptySeq(p[Type]() /* elemTyp */)()
        case "EmptySet" => EmptySet(p[Type]() /* elemTyp */)()
        case "EpsilonPerm" => EpsilonPerm()()
        case "EqCmp" => EqCmp(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "Exists" => Exists(p[Seq[LocalVarDecl]]() /* variables */, p[Exp]() /* exp */)()
        case "ExplicitMultiset" => ExplicitMultiset(p[Seq[Exp]]() /* elems */)()
        case "ExplicitSeq" => ExplicitSeq(p[Seq[Exp]]() /* elems */)()
        case "ExplicitSet" => ExplicitSet(p[Seq[Exp]]() /* elems */)()
        case "FalseLit" => FalseLit()()
        case "FieldAccess" => FieldAccess(p[Exp]() /* rcv */, p[Field]() /* field */)()
        case "FieldAccessPredicate" => FieldAccessPredicate(p[FieldAccess]() /* loc */, p[Exp]() /* perm */)()
        case "ForPerm" => ForPerm(p[LocalVarDecl]() /* variable */, p[Seq[Location]]() /* accessList */, p[Exp]() /* body */)()
        case "Forall" => Forall(p[Seq[LocalVarDecl]]() /* variables */, p[Seq[Trigger]]() /* triggers */, p[Exp]() /* exp */)()
        case "FractionalPerm" => FractionalPerm(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "FullPerm" => FullPerm()()
        case "FuncApp" => FuncApp(p[String]() /* funcname */, p[Seq[Exp]]() /* args */)(NoPosition, NoInfo, p[Type](), p[Seq[LocalVarDecl]](), NoTrafos)
        case "GeCmp" => GeCmp(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "GtCmp" => GtCmp(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "Implies" => Implies(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "InhaleExhaleExp" => InhaleExhaleExp(p[Exp]() /* in */, p[Exp]() /* ex */)()
        case "IntLit" => IntLit(p[BigInt]() /* i */)()
        case "IntPermMul" => IntPermMul(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "LabelledOld" => LabelledOld(p[Exp]() /* exp */, p[String]() /* oldLabel */)()
        case "LeCmp" => LeCmp(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "Let" => Let(p[LocalVarDecl]() /* variable */, p[Exp]() /* exp */, p[Exp]() /* body */)()
        case "LocalVar" => LocalVar(p[String]() /* name */)(p[Type]())
        case "LtCmp" => LtCmp(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "MagicWand" => MagicWand(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "Minus" => Minus(p[Exp]() /* exp */)()
        case "Mod" => Mod(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "Mul" => Mul(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "NeCmp" => NeCmp(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "NoPerm" => NoPerm()()
        case "Not" => Not(p[Exp]() /* exp */)()
        case "NullLit" => NullLit()()
        case "Old" => Old(p[Exp]() /* exp */)()
        case "Or" => Or(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "PermAdd" => PermAdd(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "PermDiv" => PermDiv(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "PermGeCmp" => PermGeCmp(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "PermGtCmp" => PermGtCmp(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "PermLeCmp" => PermLeCmp(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "PermLtCmp" => PermLtCmp(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "PermMinus" => PermMinus(p[Exp]() /* exp */)()
        case "PermMul" => PermMul(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "PermSub" => PermSub(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "PredicateAccess" => PredicateAccess(p[Seq[Exp]]() /* args */, p[String]() /* predicateName */)()
        case "PredicateAccessPredicate" => PredicateAccessPredicate(p[PredicateAccess]() /* loc */, p[Exp]() /* perm */)()
        case "RangeSeq" => RangeSeq(p[Exp]() /* low */, p[Exp]() /* high */)()
        case "Result" => Result()(p[Type]())
        case "SeqAppend" => SeqAppend(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "SeqContains" => SeqContains(p[Exp]() /* elem */, p[Exp]() /* s */)()
        case "SeqDrop" => SeqDrop(p[Exp]() /* s */, p[Exp]() /* n */)()
        case "SeqIndex" => SeqIndex(p[Exp]() /* s */, p[Exp]() /* idx */)()
        case "SeqLength" => SeqLength(p[Exp]() /* s */)()
        case "SeqTake" => SeqTake(p[Exp]() /* s */, p[Exp]() /* n */)()
        case "SeqUpdate" => SeqUpdate(p[Exp]() /* s */, p[Exp]() /* idx */, p[Exp]() /* elem */)()
        case "Sub" => Sub(p[Exp]() /* left */, p[Exp]() /* right */)()
        case "Trigger" => Trigger(p[Seq[Exp]]() /* exps */)()
        case "TrueLit" => TrueLit()()
        case "Unfolding" => Unfolding(p[PredicateAccessPredicate]() /* acc */, p[Exp]() /* body */)()
        case "WildcardPerm" => WildcardPerm()()

        case "Bool$" => Bool
        case "DomainType" => DomainType(p[String](), p[Map[TypeVar, Type]]())(p[Seq[TypeVar]]())
        case "Int$" => Int
        case "InternalType" => InternalType
        case "MultisetType" => MultisetType(p[Type]())
        case "Perm$" => Perm
        case "Ref$" => Ref
        case "SetType" => SetType(p[Type]())
        case "SeqType" => SeqType(p[Type]())
        case "TypeVar" => TypeVar(p[String]())
        case "Wand$" => Wand

        case _ => throw new RuntimeException("Could not parse element " + typ)
      }).asInstanceOf[T]
    } else {
      val start = pp.advance('|', ')')
      // if it is not a string an exception will be thrown
      if (printDebug) {
        println(pp.pos + " " + pp.subfrom(start))
      }
      pp.subfrom(start).asInstanceOf[T]
    }
  }
}

class ParsePosition(input: String){
  var pos: Int = 0

  def prev: Char = input.charAt(pos - 1)
  def current: Char = input.charAt(pos)
  def at(p: Int) = input.charAt(p)
  def advance(): Unit ={
    pos += 1
  }
  def back(): Unit ={
    pos -= 1
  }
  def advance(c: Char*): Int ={
    val start = pos
    while(!c.contains(current)){
      advance()
    }
    start
  }
  def subfrom(start: Int): String ={
    sub(start, pos)
  }
  def sub(start: Int, end: Int): String ={
    input.substring(start, end)
  }
}

object ParsePosition{
  def apply(input: String): ParsePosition = new ParsePosition(input)
}