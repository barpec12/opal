/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj.js

import org.opalj.br.{Method, ObjectType}
import org.opalj.br.analyses.SomeProject
import org.opalj.collection.immutable.IntTrieSet
import org.opalj.ifds.Dependees.Getter
import org.opalj.tac.fpcf.analyses.ifds.JavaIFDSProblem.{V}
import org.opalj.tac.{AITACode, ASTNode, Assignment, Call, ComputeTACAIKey, Expr, ExprStmt, MethodCall, ReturnValue, Stmt, TACMethodParameter, TACode}
import org.opalj.tac.fpcf.analyses.ifds.{JavaIFDSProblem, JavaMethod, JavaStatement}
import org.opalj.tac.fpcf.analyses.ifds.taint.{ArrayElement, FlowFact, ForwardTaintProblem, TaintFact, TaintNullFact, Variable}
import org.opalj.value.ValueInformation

import scala.collection.mutable

class IFDSAnalysisJS(p: SomeProject) extends ForwardTaintProblem(p) {
    final type TACAICode = TACode[TACMethodParameter, JavaIFDSProblem.V]
    val tacaiKey: Method => AITACode[TACMethodParameter, ValueInformation] = p.get(ComputeTACAIKey);

    /**
     * Called, when the exit to return facts are computed for some `callee` with the null fact and
     * the callee's return value is assigned to a variable.
     * Creates a taint, if necessary.
     *
     * @param callee The called method.
     * @param call   The call.
     * @return Some variable fact, if necessary. Otherwise none.
     */
    override protected def createTaints(callee: Method, call: JavaStatement): Set[TaintFact] =
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
        in:     TaintFact
    ): Option[FlowFact] =
        if (callee.name == "sink" && in == Variable(-2))
            Some(FlowFact(Seq(JavaMethod(call.method), JavaMethod(callee))))
        else None

    /**
     * The entry points of this analysis.
     */
    override def entryPoints: Seq[(Method, TaintFact)] =
        (for {
            m <- p.allMethodsWithBody
            if m.name == "main"
        } yield m -> TaintNullFact)

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
    override protected def sanitizesParameter(call: JavaStatement, in: TaintFact): Boolean = false

    override def callFlow(call: JavaStatement, callee: Method, in: TaintFact): Set[TaintFact] = {
        val callObject = JavaIFDSProblem.asCall(call.stmt)
        val allParams = callObject.allParams

        val allParamsWithIndices = allParams.zipWithIndex
        in match {
            case BindingFact(index, keyName) => allParamsWithIndices.flatMap {
                case (param, paramIndex) if param.asVar.definedBy.contains(index) =>
                    Some(BindingFact(JavaIFDSProblem.switchParamAndVariableIndex(
                        paramIndex,
                        callee.isStatic
                    ), keyName))
                case _ => None // Nothing to do
            }.toSet
            case _ => super.callFlow(call, callee, in)
        }
    }

    override def returnFlow(exit: JavaStatement, in: TaintFact, call: JavaStatement, callFact: TaintFact, successor: JavaStatement): Set[TaintFact] = {
        if (!isPossibleReturnFlow(exit, successor)) return Set.empty
        val callee = exit.callable
        if (sanitizesReturnValue(callee)) return Set.empty
        val callStatement = JavaIFDSProblem.asCall(call.stmt)
        val allParams = callStatement.allParams

        in match {
            case BindingFact(index, keyName) =>
                var flows: Set[TaintFact] = Set.empty
                if (index < 0 && index > -100) {
                    val param = allParams(
                        JavaIFDSProblem.switchParamAndVariableIndex(index, callee.isStatic)
                    )
                    flows ++= param.asVar.definedBy.map(i => BindingFact(i, keyName))
                }
                if (exit.stmt.astID == ReturnValue.ASTID && call.stmt.astID == Assignment.ASTID) {
                    val returnValueDefinedBy = exit.stmt.asReturnValue.expr.asVar.definedBy
                    if (returnValueDefinedBy.contains(index))
                        flows += BindingFact(call.index, keyName)
                }
                flows
            case _ => super.returnFlow(exit, in, call, callFact, successor)
        }
    }

    def killFlow(
        call:            JavaStatement,
        successor:       JavaStatement,
        in:              TaintFact,
        dependeesGetter: Getter
    ): Set[TaintFact] = Set.empty

    val scriptEngineMethods: Map[ObjectType, List[String]] = Map(
        ObjectType("javax/script/Invocable") -> List("invokeFunction"),
        ObjectType("javax/script/ScriptEngine") -> List("put", "get"),
        ObjectType("javax/script/Bindings") -> List("put", "get", "putAll", "remove"),
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
            case (param, paramI) => param.asVar.definedBy.contains(index)
        } match {
            case Some((param, paramI)) => JavaIFDSProblem.switchParamAndVariableIndex(paramI, isStaticMethod = false)
            case None                  => NO_MATCH
        }
    }

    /**
     * Finds all definiton/use sites inside the method.
     *
     * @param method method to be searched in
     * @param sites  definition or use sites
     * @return sites as JavaStatement
     */
    def searchStmts(method: Method, sites: IntTrieSet): Set[Stmt[JavaIFDSProblem.V]] = {
        val taCode = tacaiKey(method)
        sites.map(site => taCode.stmts.apply(site))
    }

    /**
     * If stmt is a call, return it as a FunctionCall
     * @param stmt
     * @return maybe a function call
     */
    def maybeCall(stmt: Stmt[JavaIFDSProblem.V]): Option[Call[JavaIFDSProblem.V]] = {
        def isCall(node: ASTNode[JavaIFDSProblem.V]) = node match {
            case expr: Expr[JavaIFDSProblem.V] => expr.isVirtualFunctionCall || expr.isStaticFunctionCall
            case stmt: Stmt[JavaIFDSProblem.V] => stmt.isNonVirtualMethodCall || stmt.isVirtualMethodCall || stmt.isStaticMethodCall
        }

        stmt match {
            case exprStmt: ExprStmt[JavaIFDSProblem.V] if isCall(exprStmt.expr) =>
                Some(exprStmt.expr.asFunctionCall)
            case assignStmt: Assignment[JavaIFDSProblem.V] if isCall(assignStmt.expr) =>
                Some(assignStmt.expr.asFunctionCall)
            case call: MethodCall[JavaIFDSProblem.V] if isCall(stmt) =>
                Some(call)
            case _ => None
        }
    }

    def findCallOnObject(method: Method, sites: IntTrieSet, methodName: String): Set[Stmt[JavaIFDSProblem.V]] = {
        val stmts = searchStmts(method, sites)
        stmts.map(stmt => maybeCall(stmt) match {
            case Some(call) if (call.name.equals(methodName)) => Some(stmt)
            case _                                            => None
        }).filter(_.isDefined).map(_.get)
    }

    val jsSourceCache: mutable.Map[(JavaStatement, Expr[V]), Set[JavaScriptSource]] = mutable.Map()

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
    def findJSSourceOnInvokeFunction(javaStmt: JavaStatement, arg: Expr[JavaIFDSProblem.V]): Set[JavaScriptSource] = {
        val decls = findCallOnObject(javaStmt.method, arg.asVar.definedBy, "getEngineByName")

        val maybeCached = jsSourceCache.get((javaStmt, arg))
        if (maybeCached.isDefined)
            maybeCached.get
        else
            decls.flatMap(decl => {
                val evals = findCallOnObject(javaStmt.method, decl.asAssignment.targetVar.usedBy, "eval")
                val jsSources = evals.flatMap(eval => {
                    val evalCall = JavaIFDSProblem.asCall(eval)
                    varToJavaScriptSource(javaStmt.method, evalCall.params.head.asVar)
                })
                jsSourceCache += (javaStmt, arg) -> jsSources
                jsSources
            })
    }

    val statementToJavaScriptSource: mutable.Map[Stmt[V], JavaScriptSource] = mutable.Map()

    /**
     * Tries to resolve a variable either to a string constant or a file path containing the variable's value
     * @param method method to be searched in
     * @param variable variable of interest
     * @return JavaScriptSource
     */
    def varToJavaScriptSource(method: Method, variable: JavaIFDSProblem.V): Set[JavaScriptSource] = {
        val resultSet: mutable.Set[JavaScriptSource] = mutable.Set()
        def findFileArg(sites: IntTrieSet): Unit = {
            val calls = findCallOnObject(method, sites, "<init>");
            calls.foreach(init => {
                val defSitesOfFileSrc = init.asInstanceMethodCall.params.head.asVar.definedBy
                val defs = searchStmts(method, defSitesOfFileSrc)
                defs.foreach {
                    /* new File("path/to/src"); */
                    case a: Assignment[JavaIFDSProblem.V] if a.expr.isStringConst =>
//                      JavaScriptFileSource(a.expr.asStringConst.value)
                        resultSet.add(statementToJavaScriptSource.getOrElseUpdate(a, JavaScriptFileSource(a.expr.asStringConst.value)))
                    /* File constructor argument is no string constant */
                    case _ =>
                }
            })
        }

        def findFileReaderArg(sites: IntTrieSet): Unit = {
            val calls = findCallOnObject(method, sites, "<init>");
            calls.foreach(init => {
                val defSitesOfFileReaderSrc = init.asInstanceMethodCall.params.head.asVar.definedBy
                val defs = searchStmts(method, defSitesOfFileReaderSrc);
                defs.foreach {
                    /* FileReader fr = new FileReader(new File("path/to/src")); */
                    case a: Assignment[JavaIFDSProblem.V] if a.expr.isStringConst =>
                      resultSet.add(statementToJavaScriptSource.getOrElseUpdate(a, JavaScriptFileSource(a.expr.asStringConst.value)))
                    /* new FileReader(new File(...)); */
                    case a: Assignment[JavaIFDSProblem.V] if a.expr.isNew =>
                        if (a.expr.asNew.tpe.isSubtypeOf(ObjectType("java/io/File"))(p.classHierarchy))
                            findFileArg(a.targetVar.usedBy)
                    // Unknown argument
                    case _ =>
                }
            })
        }

        val nextJStmts = searchStmts(method, variable.definedBy)
        nextJStmts.foreach {
            /* se.eval("function() ..."); */
            case a: Assignment[JavaIFDSProblem.V] if a.expr.isStringConst =>
              resultSet.add(statementToJavaScriptSource.getOrElseUpdate(a, JavaScriptStringSource(a.expr.asStringConst.value)))
            /* se.eval(new FileReader(...)); */
            case a: Assignment[JavaIFDSProblem.V] if a.expr.isNew =>
                if (a.expr.asNew.tpe.isSubtypeOf(ObjectType("java/io/FileReader"))(p.classHierarchy))
                    findFileReaderArg(a.targetVar.usedBy)
            case _ =>
        }

        resultSet.toSet
    }

    override def callToReturnFlow(call: JavaStatement, in: TaintFact, successor: JavaStatement): Set[TaintFact] = {
        val callStmt = JavaIFDSProblem.asCall(call.stmt)
        val allParams = callStmt.allParams
        val allParamsWithIndex = callStmt.allParams.zipWithIndex

        if (!invokesScriptFunction(callStmt)) {
            in match {
                case BindingFact(index, keyName) =>
                    if (getParameterIndex(allParamsWithIndex, index) == NO_MATCH)
                        return Set(in)
                    else
                        return Set()
                case _ => return super.callToReturnFlow(call, in, successor)
            }
        }

        in match {
            // invokeFunction takes a function name and a variable length argument. This is always an array in TACAI.
            case ArrayElement(index, taintedIndex) if callStmt.name == "invokeFunction" && getParameterIndex(allParamsWithIndex, index) == -3 =>
                val sourceSet = findJSSourceOnInvokeFunction(call, allParams.head.asVar)
                sourceSet.foreach(source => {
                    // TODO: Call JS analysis
                    if (source.asString.contains("check") && call.stmt.isAssignment) {
                        return Set(Variable(call.index))
                    }
                })
            /* put obj in Binding */
            case Variable(index) if callStmt.name == "put" && getParameterIndex(allParamsWithIndex, index) == -3 =>
                val taints = mutable.Set(in)
                searchStmts(call.method, allParams(1).asVar.definedBy).foreach {
                    case a: Assignment[JavaIFDSProblem.V] =>
                        val keyName = if (a.expr.isStringConst) a.expr.asStringConst.value else ""
                        val defSites = callStmt.receiverOption.get.asVar.definedBy
                        taints ++= defSites.map(i => BindingFact(i, keyName))
                    case _ =>
                }
                return taints.toSet
            /* putAll BindingFact to other BindingFact */
            case BindingFact(index, keyName) if callStmt.name == "putAll" && getParameterIndex(allParamsWithIndex, index) == -2 =>
                callStmt.receiverOption match {
                    case Some(baseObj) => return baseObj.asVar.definedBy.map(i => BindingFact(i, keyName)) ++ Set(in)
                    case None          => return Set(in)
                }
            /* Overwrite BindingFact */
            case BindingFact(index, keyName) if callStmt.name == "put" && getParameterIndex(allParamsWithIndex, index) == -1 =>
                if (keyName == "")
                    return Set(in)
                val possibleFields = mutable.Set[String]()
                searchStmts(call.method, allParams(1).asVar.definedBy).foreach {
                    case a: Assignment[JavaIFDSProblem.V] =>
                        possibleFields.add(if (a.expr.isStringConst) a.expr.asStringConst.value else "")
                    case _ =>
                }
                if (possibleFields.size == 1 && possibleFields.contains(keyName))
                    return Set()
                else
                    return Set(in)
            /* Remove BindingFact */
            case BindingFact(index, keyName) if callStmt.name == "remove" && getParameterIndex(allParamsWithIndex, index) == -1 =>
                if (keyName == "")
                    return Set(in)
                val possibleFields = mutable.Set[String]()
                searchStmts(call.method, allParams(1).asVar.definedBy).foreach {
                    case a: Assignment[JavaIFDSProblem.V] =>
                        possibleFields.add(if (a.expr.isStringConst) a.expr.asStringConst.value else "")
                    case _ =>
                }
                if (possibleFields.size == 1 && possibleFields.contains(keyName))
                    return Set()
                else
                    return Set(in)
            /* get from BindingFact */
            case BindingFact(index, keyName) if callStmt.name == "get" && getParameterIndex(allParamsWithIndex, index) == -1 =>
                if (keyName == "")
                    return Set(Variable(call.index), in)
                searchStmts(call.method, allParams(1).asVar.definedBy).foreach {
                    case a: Assignment[JavaIFDSProblem.V] =>
                        if ((!a.expr.isStringConst || a.expr.asStringConst.value == keyName)
                            && call.stmt.isAssignment)
                            return Set(Variable(call.index), in)
                    case _ =>
                }
            case Variable(index) if callStmt.name == "eval" && getParameterIndex(allParamsWithIndex, index) == -3 =>
            // TODO: Bindings?
            //             val sourceSet = varToJavaScriptSource(call.method, allParams(2).asVar)
            case BindingFact(index, keyName) if callStmt.receiverOption.isDefined && callStmt.receiverOption.get.asVar.definedBy.contains(index)
                && (callStmt.name == "eval" || callStmt.name == "invokeFunction") =>
            case _ => // should be unreachable
        }

        return Set()
    }

    override def isTainted(expression: Expr[V], in: TaintFact): Boolean = {
        val definedBy = expression.asVar.definedBy
        expression.isVar && (in match {
            case BindingFact(index, _) => definedBy.contains(index)
            case _                     => super.isTainted(expression, in)
        })
    }
}
