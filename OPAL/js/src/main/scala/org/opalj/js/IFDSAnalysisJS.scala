/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj.js

import org.opalj.br.{Method, ObjectType}
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
        call:   JavaStatement,
        in:     Fact
    ): Option[FlowFact] =
        if (callee.name == "sink" && in == Variable(-2))
            Some(FlowFact(Seq(JavaMethod(call.method), JavaMethod(callee))))
        else None

    /**
     * The entry points of this analysis.
     */
    override def entryPoints: Seq[(Method, Fact)] =
        (for {
            m ← p.allMethodsWithBody
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
        call:            JavaStatement,
        successor:       JavaStatement,
        in:              Fact,
        dependeesGetter: Getter
    ): Set[Fact] = Set.empty

    val scriptEngineMethods: Map[ObjectType, List[String]] = Map(
      ObjectType("javax/script/Invocable") -> List("invokeFunction"),
      ObjectType("javax/script/ScriptEngine") -> List("eval", "put")
    )

    /**
     * Checks whether we handle the method
     * @param objType type of the base object
     * @param methodName method name of the call
     * @return true if we have a rule for the method call
     */
    def invokesScriptFunction(objType: ObjectType, methodName: String): Boolean =
      scriptEngineMethods.exists(kv => objType.isSubtypeOf(kv._1)(p.classHierarchy) && kv._2.contains(methodName))

    def invokesScriptFunction(callStmt: Call[JavaIFDSProblem.V]): Boolean =
      invokesScriptFunction(callStmt.declaringClass.mostPreciseObjectType, callStmt.name)

    def invokesScriptFunction(method: Method): Boolean =
      invokesScriptFunction(method.classFile.thisType, method.name)

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

    val NO_MATCH = 256
    def getParameterIndex(allParamsWithIndex: Seq[(Expr[JavaIFDSProblem.V], Int)], index: Int): Int = {
        allParamsWithIndex.find {
            case (param, paramI) ⇒ param.asVar.definedBy.contains(index)
        } match {
            case Some((param, paramI)) ⇒ JavaIFDSProblem.switchParamAndVariableIndex(paramI, isStaticMethod = false)
            case None                  ⇒ NO_MATCH
        }
    }

    /**
     * Finds all definiton/use sites inside the method.
     *
     * @param method method to be searched in
     * @param sites  definition or use sites
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

    /**
     * If stmt is a call, return it as a FunctionCall
     * @param stmt
     * @return maybe a function call
     */
    def maybeCall(stmt: Stmt[JavaIFDSProblem.V]): Option[FunctionCall[JavaIFDSProblem.V]] = {
        def isCall(expr: Expr[JavaIFDSProblem.V]) = expr.isVirtualFunctionCall || expr.isStaticFunctionCall

        stmt match {
            case exprStmt: ExprStmt[JavaIFDSProblem.V] if (isCall(exprStmt.expr)) ⇒
                Some(exprStmt.expr.asFunctionCall)
            case assignStmt: Assignment[JavaIFDSProblem.V] if (isCall(assignStmt.expr)) ⇒
                Some(assignStmt.expr.asFunctionCall)
            case _ ⇒ None
        }
    }

    /**
     * In case of a snippet like this:
     * 1 ScriptEngine se = ...;
     * 2 se.eval("JS Code");
     * 3 ((Invocable) se).invokeFunction("myFunction", args...);
     * This functions finds "JS Code" given "se" at se.invokeFunction().
     *
     * @param method method to be searched in
     * @param obj ScriptEngine variable
     * @return javascript source code
     */
    def findJSSourceOnInvokeFunction(method: Method, obj: JavaIFDSProblem.V): Set[JavaScriptSource] = {
        def findCallOnObject(sites: IntTrieSet, methodName: String): Set[JavaStatement] = {
            searchJStmts(method, sites).map(jstmt ⇒ maybeCall(jstmt.stmt) match {
                case Some(call) if (call.name == methodName) ⇒ Some(jstmt)
                case _                                       ⇒ None
            }).filter(_.isDefined).map(_.get)
        }

        val decls = findCallOnObject(obj.definedBy, "getEngineByName")
        decls.flatMap(decl ⇒ {
            val evals = findCallOnObject(decl.stmt.asAssignment.targetVar.usedBy, "eval")
            evals.flatMap(eval ⇒ {
                val evalCall = asCall(eval.stmt)
                varToJavaScriptSource(method, evalCall.params.head.asVar)
            })
        })
    }

    /**
     * Tries to resolve a variable either to a string constant or a file path containing the variable's value
     * @param method method to be searched in
     * @param variable variable of interest
     * @return JavaScriptSource
     */
    def varToJavaScriptSource(method: Method, variable: JavaIFDSProblem.V): Set[JavaScriptSource] = {
        val nextJStmts = searchJStmts(method, variable.definedBy)

        // TODO: Find file
        // TODO: do not give up if it is not a constant
        nextJStmts.map(jstmt ⇒ jstmt.stmt match {
            case a: Assignment[JavaIFDSProblem.V] if a.expr.isStringConst ⇒ Some(JavaScriptStringSource(a.expr.asStringConst.value))
            case _ ⇒ None
        }).filter(_.isDefined).map(_.get)
    }

    override def callToReturnFlow(call: JavaStatement, in: Fact, successor: JavaStatement): Set[Fact] = {
        val callStmt = asCall(call.stmt)
        if (!invokesScriptFunction(callStmt))
          return super.callToReturnFlow(call, in, successor)

        val allParams = callStmt.allParams
        val allParamsWithIndex = callStmt.allParams.zipWithIndex

        in match {
            // invokeFunction takes a function name and a variable length argument. This is always an array in TACAI.
            case ArrayElement(index, taintedIndex) if callStmt.name == "invokeFunction" && getParameterIndex(allParamsWithIndex, index) == -3 ⇒
                val sourceSet = findJSSourceOnInvokeFunction(call.method, allParams.head.asVar)
                print(sourceSet)
            case Variable(index) if callStmt.name == "eval" && getParameterIndex(allParamsWithIndex, index) == -3 =>
                // TODO: Bindings
                // val sourceSet = varToJavaScriptSource(call.method, allParams(-2).asVar)
            case _ ⇒ // we do not handle this case, thus leave it to the default call semantics
        }

        Set()
    }
}
