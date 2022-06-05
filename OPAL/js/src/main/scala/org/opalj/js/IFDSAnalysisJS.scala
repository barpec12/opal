/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj.js

import org.opalj.ai.domain.l1.DefaultStringValuesBinding
import org.opalj.br.Method
import org.opalj.br.analyses.SomeProject
import org.opalj.collection.immutable.IntTrieSet
import org.opalj.ifds.Dependees.Getter
import org.opalj.tac.{Assignment, Call, Expr, ExprStmt, FunctionCall, Stmt}
import org.opalj.tac.fpcf.analyses.ifds.{JavaIFDSProblem, JavaMethod, JavaStatement}
import org.opalj.tac.fpcf.analyses.ifds.taint.{ArrayElement, Fact, FlowFact, ForwardTaintProblem, InstanceField, NullFact, StaticField, Variable}

import scala.collection.mutable

class IFDSAnalysisJS(p: SomeProject) extends ForwardTaintProblem(p) {

  /**
   * Called, when the exit to return facts are computed for some `callee` with the null fact and
   * the callee's return value is assigned to a variable.
   * Creates a taint, if necessary.
   *
   * @param callee The called method.
   * @param call   The call.
   * @return Some variable fact, if necessary. Otherwise none.
   */
  override protected def createTaints(callee: Method, call: JavaStatement): Set[Fact] =
    if (callee.name == "source") Set(Variable(call.index))
    else Set.empty

  /**
   * Called, when the call to return facts are computed for some `callee`.
   * Creates a FlowFact, if necessary.
   *
   * @param callee The method, which was called.
   * @param call   The call.
   * @return Some FlowFact, if necessary. Otherwise None.
   */
  override protected def createFlowFact(
      callee: Method,
      call: JavaStatement,
      in: Fact
  ): Option[FlowFact] =
    if (callee.name == "sink" && in == Variable(-2))
      Some(FlowFact(Seq(JavaMethod(call.method), JavaMethod(callee))))
    else None

  /**
   * The entry points of this analysis.
   */
  override def entryPoints: Seq[(Method, Fact)] =
    (for {
      m <- p.allMethodsWithBody
      if m.name == "main"
    } yield m -> NullFact)

  /**
   * Checks, if some `callee` is a sanitizer, which sanitizes its return value.
   * In this case, no return flow facts will be created.
   *
   * @param callee The method, which was called.
   * @return True, if the method is a sanitizer.
   */
  override protected def sanitizesReturnValue(callee: Method): Boolean = callee.name == "sanitize"

  /**
   * Called in callToReturnFlow. This method can return whether the input fact
   * will be removed after `callee` was called. I.e. the method could sanitize parameters.
   *
   * @param call The call statement.
   * @param in   The fact which holds before the call.
   * @return Whether in will be removed after the call.
   */
  override protected def sanitizesParameter(call: JavaStatement, in: Fact): Boolean = false

  def killFlow(
      call: JavaStatement,
      successor: JavaStatement,
      in: Fact,
      dependeesGetter: Getter
  ): Set[Fact] = Set.empty

  /**
   * Checks whether we handle the method
   * @param method
   * @return True if function is handled by us
   */
  def invokesScriptFunction(method: Method): Boolean =
    method.classFile.fqn == "javax/script/Invocable" && method.name == "invokeFunction"

  /**
   * Checks whether we handle the method
   * @param callStmt
   * @return True if function is handled by us
   */
  def invokesScriptFunction(callStmt: Call[JavaIFDSProblem.V]): Boolean =
    callStmt.declaringClass.mostPreciseObjectType.fqn == "javax/script/Invocable" && callStmt.name == "invokeFunction"

  /**
   * If a parameter is tainted, the result will also be tainted.
   * We assume that the callee does not call the source method.
   */
  override def outsideAnalysisContext(callee: Method): Option[OutsideAnalysisContextHandler] = {
    if (invokesScriptFunction(callee)) {
      Some(killFlow _)
    } else {
      super.outsideAnalysisContext(callee)
    }
  }

  def isReferenceParameter(allParams: Seq[Expr[JavaIFDSProblem.V]], index: Int): Boolean = {
    allParams.find(p => p.asVar.definedBy.contains(index)) match {
      case Some(param) => param.asVar.value.isReferenceValue
      case None => false
    }
  }

  val NO_MATCH = 256
  def getParameterIndex(allParamsWithIndex: Seq[(Expr[JavaIFDSProblem.V], Int)], index: Int): Int = {
    allParamsWithIndex.find {
      case (param, paramI) => param.asVar.definedBy.contains(index)
    } match {
      case Some((param, paramI)) => JavaIFDSProblem.switchParamAndVariableIndex(paramI,isStaticMethod = false)
      case None => NO_MATCH
    }
  }

  def maybeCall(stmt: Stmt[JavaIFDSProblem.V]): Option[FunctionCall[JavaIFDSProblem.V]] = {
    def isCall(expr: Expr[JavaIFDSProblem.V]) = expr.isVirtualFunctionCall || expr.isStaticFunctionCall

    stmt match {
      case exprStmt: ExprStmt[JavaIFDSProblem.V] if (isCall(exprStmt.expr)) =>
        Some(exprStmt.expr.asFunctionCall)
      case assignStmt: Assignment[JavaIFDSProblem.V] if (isCall(assignStmt.expr)) =>
        Some(assignStmt.expr.asFunctionCall)
      case _ => None
    }
  }

  def findDeclarationOfEngine(method: Method, baseObject: JavaIFDSProblem.V) = {
    val nextJStmts = searchJStmts(method, baseObject.definedBy)
    nextJStmts.foreach(jstmt => if (jstmt.stmt.isAssignment) {
      val assignStmt = jstmt.stmt.asAssignment
      if (assignStmt.expr.isVirtualFunctionCall) {
        val callStmt = asCall(assignStmt)
        if (callStmt.name == "getEngineByName") {
          val engineObject = assignStmt.targetVar
          findEvalUsageOfEngine(method, engineObject)
        }
      }
    })
  }

  def findEvalUsageOfEngine(method: Method, baseObject: JavaIFDSProblem.V) = {
    val nextJStmts = searchJStmts(method, baseObject.usedBy)
    nextJStmts.foreach(jstmt => maybeCall(jstmt.stmt) match {
      case Some(call) =>
        val value = call.params.head.asVar.value
      case None =>
    })
  }

  /**
   * Finds all definiton/use sites inside the method.
   * @param method method
   * @param sites definition or use sites
   * @return sites as JavaStatement
   */
  def searchJStmts(method: Method, sites: IntTrieSet): Set[JavaStatement] = {
    var result = Set[JavaStatement]()
    val worklist = mutable.Stack[JavaStatement]()
    worklist.pushAll(this.icfg.startStatements(method))
    var visited = Set[JavaStatement]()
    while (worklist.nonEmpty) {
      val stmt = worklist.pop()
      visited += stmt
      if (sites.contains(stmt.index)) {
        result += stmt
      }
      val nextToVisit = this.icfg.nextStatements(stmt) -- visited
      worklist.pushAll(nextToVisit)
    }
    result
  }


  override def callToReturnFlow(call: JavaStatement, in: Fact): Set[Fact] = {
    val callStmt = asCall(call.stmt)
    val allParams = callStmt.allParams

    if (invokesScriptFunction(callStmt)) {
      val allParamsWithIndex = callStmt.allParams.zipWithIndex
      in match {
        // invokeFunction takes a function name and a variable length argument. This is always an array internally.
        case ArrayElement(index, taintedIndex) if getParameterIndex(allParamsWithIndex, index) == -3 =>
//          val taintedParam = allParams(2).asVar
          val baseObject = allParams.head
          findDeclarationOfEngine(call.method, baseObject.asVar)
        case _ =>
      }
    }

    // TODO: third parameter for callToReturn "hasCallee: boolean"?
    if (icfg.getCalleesIfCallStatement(call).isEmpty) {
      // If the call does not have any callees, the code is unknown
      // and we safely handle it as the identity
      Set(in)
    } else {
      // Otherwise use the java call semantics
      in match {
        // Local variables that are of a Reference type flow through the callee
        case Variable(index) if isReferenceParameter(allParams, index) => Set.empty
        case ArrayElement(index, taintedIndex) if isReferenceParameter(allParams, index) => Set.empty
        case InstanceField(index, declClass, taintedField) if allParams.zipWithIndex.exists(tpl => tpl._2 == index) => Set.empty
        case StaticField(_, _) => Set.empty
        case f: Fact => Set(f)
      }
    }
  }
}
