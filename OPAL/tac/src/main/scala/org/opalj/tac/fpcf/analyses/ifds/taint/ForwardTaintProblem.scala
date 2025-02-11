/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj.tac.fpcf.analyses.ifds.taint

import org.opalj.br.Method
import org.opalj.br.analyses.{DeclaredMethodsKey, SomeProject}
import org.opalj.ifds.Dependees.Getter
import org.opalj.tac._
import org.opalj.tac.fpcf.analyses.ifds.JavaIFDSProblem.V
import org.opalj.tac.fpcf.analyses.ifds.taint.summaries.TaintSummaries
import org.opalj.tac.fpcf.analyses.ifds.{JavaIFDSProblem, JavaMethod, JavaStatement}

import java.io.File

abstract class ForwardTaintProblem(project: SomeProject)
    extends JavaIFDSProblem[TaintFact](project)
    with TaintProblem[Method, JavaStatement, TaintFact] {
    val declaredMethods = project.get(DeclaredMethodsKey)

    def useSummaries: Boolean = false
    lazy val summaries: TaintSummaries = TaintSummaries(new File(getClass.getResource("/summaries/").getPath).listFiles().toList)

    override def nullFact: TaintFact = TaintNullFact

    override def needsPredecessor(statement: JavaStatement): Boolean = false

    /**
     * If a variable gets assigned a tainted value, the variable will be tainted.
     */
    override def normalFlow(statement: JavaStatement, in: TaintFact, predecessor: Option[JavaStatement]): Set[TaintFact] = {
        statement.stmt.astID match {
            case Assignment.ASTID =>
                Set(in) ++ createNewTaints(statement.stmt.asAssignment.expr, statement, in)
            case ArrayStore.ASTID =>
                val store = statement.stmt.asArrayStore
                val definedBy = store.arrayRef.asVar.definedBy
                val arrayIndex = TaintProblem.getIntConstant(store.index, statement.code)
                if (isTainted(store.value, in)) {
                    if (arrayIndex.isDefined) {
                        // Taint a known array index
                        Set(in) ++ definedBy.map { ArrayElement(_, arrayIndex.get) }
                    } else
                        // Taint the whole array if the index is unknown
                        Set(in) ++ definedBy.map { Variable(_) }
                } else if (arrayIndex.isDefined && definedBy.size == 1 && in == ArrayElement(definedBy.head, arrayIndex.get)) {
                    // untaint
                    Set()
                } else Set(in)
            case PutField.ASTID =>
                val put = statement.stmt.asPutField
                val definedBy = put.objRef.asVar.definedBy
                if (isTainted(put.value, in)) {
                    // RHS is tainted, thus the lhs as well
                    Set(in) ++ definedBy.map { InstanceField(_, put.declaringClass, put.name) }
                } else if (isTainted(put.objRef, in)) {
                    // the lhs is tainted and overwritten
                    Set()
                } else {
                    // if the taint is not affected, just leave it alive
                    Set(in)
                }
            case PutStatic.ASTID =>
                val put = statement.stmt.asPutStatic
                if (isTainted(put.value, in)) {
                    // RHS is tainted, thus the lhs as well
                    Set(in, StaticField(put.declaringClass, put.name))
                } else if (in == StaticField(put.declaringClass, put.name)) {
                    // If LHS is equal to the taint, untaint the field here
                    Set.empty
                } else {
                    // if the taint is not affected, just leave it alive
                    Set(in)
                }
            case _ => Set(in)
        }
    }

    /**
     * Propagates tainted parameters to the callee. If a call to the sink method with a tainted
     * parameter is detected, no call-to-start
     * edges will be created.
     */
    override def callFlow(call: JavaStatement, callee: Method, in: TaintFact): Set[TaintFact] = {
        val callObject = JavaIFDSProblem.asCall(call.stmt)
        val allParams = callObject.allParams

        val allParamsWithIndices = allParams.zipWithIndex
        in match {
            // Taint formal parameter if actual parameter is tainted
            case Variable(index) =>
                allParamsWithIndices.flatMap {
                    case (param, paramIndex) if param.asVar.definedBy.contains(index) =>
                        Some(Variable(JavaIFDSProblem.switchParamAndVariableIndex(
                            paramIndex,
                            callee.isStatic
                        )))
                    case _ => None // Nothing to do
                }.toSet

            // Taint element of formal parameter if element of actual parameter is tainted
            case ArrayElement(index, taintedIndex) =>
                allParamsWithIndices.flatMap {
                    case (param, paramIndex) if param.asVar.definedBy.contains(index) =>
                        Some(ArrayElement(
                            JavaIFDSProblem.switchParamAndVariableIndex(paramIndex, callee.isStatic),
                            taintedIndex
                        ))
                    case _ => None // Nothing to do
                }.toSet
            case InstanceField(index, declClass, taintedField) =>
                // Taint field of formal parameter if field of actual parameter is tainted
                // Only if the formal parameter is of a type that may have that field!
                allParamsWithIndices.flatMap {
                    case (param, pIndex) if param.asVar.definedBy.contains(index) &&
                        (JavaIFDSProblem.switchParamAndVariableIndex(pIndex, callee.isStatic) != -1 ||
                            project.classHierarchy.isSubtypeOf(declClass, declaredMethods(callee).declaringClassType)) =>
                        Some(InstanceField(
                            JavaIFDSProblem.switchParamAndVariableIndex(pIndex, callee.isStatic),
                            declClass, taintedField
                        ))
                    case _ => None // Nothing to do
                }.toSet

            case sf: StaticField => Set(sf)

            case _               => Set() // Nothing to do

        }
    }

    /**
     * Taints an actual parameter, if the corresponding formal parameter was tainted in the callee.
     * If the callee's return value was tainted and it is assigned to a variable in the callee, the
     * variable will be tainted.
     * If a FlowFact held in the callee, this method will be appended to a new FlowFact, which holds
     * at this method.
     * Creates new taints and FlowFacts, if necessary.
     * If the sanitize method was called, nothing will be tainted.
     */
    override def returnFlow(exit: JavaStatement, in: TaintFact, call: JavaStatement, callFact: TaintFact, successor: JavaStatement): Set[TaintFact] = {
        if (!isPossibleReturnFlow(exit, successor)) return Set.empty

        val callee = exit.callable
        if (sanitizesReturnValue(callee)) return Set.empty
        val callStatement = JavaIFDSProblem.asCall(call.stmt)
        val allParams = callStatement.allParams
        var flows: Set[TaintFact] = Set.empty
        in match {
            // Taint actual parameter if formal parameter is tainted
            case Variable(index) if index < 0 && index > -100 && JavaIFDSProblem.isRefTypeParam(callee, index) =>
                val param = allParams(
                    JavaIFDSProblem.switchParamAndVariableIndex(index, callee.isStatic)
                )
                flows ++= param.asVar.definedBy.iterator.map(Variable)

            // Taint element of actual parameter if element of formal parameter is tainted
            case ArrayElement(index, taintedIndex) if index < 0 && index > -100 =>
                val param = allParams(
                    JavaIFDSProblem.switchParamAndVariableIndex(index, callee.isStatic)
                )
                flows ++= param.asVar.definedBy.iterator.map(ArrayElement(_, taintedIndex))

            case InstanceField(index, declClass, taintedField) if index < 0 && index > -10 =>
                // Taint field of actual parameter if field of formal parameter is tainted
                val param =
                    allParams(JavaIFDSProblem.switchParamAndVariableIndex(index, callee.isStatic))
                param.asVar.definedBy.foreach { defSite =>
                    flows += InstanceField(defSite, declClass, taintedField)
                }

            case sf: StaticField => flows += sf

            // Track the call chain to the sink back
            case FlowFact(flow) if !flow.contains(JavaMethod(call.method)) =>
                flows += FlowFact(JavaMethod(call.method) +: flow)
            case _ =>
        }

        // Propagate taints of the return value
        if (exit.stmt.astID == ReturnValue.ASTID && call.stmt.astID == Assignment.ASTID) {
            val returnValueDefinedBy = exit.stmt.asReturnValue.expr.asVar.definedBy
            in match {
                case Variable(index) if returnValueDefinedBy.contains(index) =>
                    flows += Variable(call.index)
                case ArrayElement(index, taintedIndex) if returnValueDefinedBy.contains(index) =>
                    flows += ArrayElement(call.index, taintedIndex)
                case InstanceField(index, declClass, taintedField) if returnValueDefinedBy.contains(index) =>
                    flows += InstanceField(call.index, declClass, taintedField)
                case TaintNullFact =>
                    val taints = createTaints(callee, call)
                    if (taints.nonEmpty) flows ++= taints
                case _ => // Nothing to do
            }
        }
        val flowFact = createFlowFact(callee, call, in)
        if (flowFact.isDefined) flows += flowFact.get

        flows
    }

    /**
     * Removes taints according to `sanitizesParameter`.
     */

    override def callToReturnFlow(call: JavaStatement, in: TaintFact, successor: JavaStatement): Set[TaintFact] = {
        if (sanitizesParameter(call, in)) return Set.empty

        val callStmt = JavaIFDSProblem.asCall(call.stmt)
        val allParams = callStmt.allParams

        def isRefTypeParam(index: Int): Boolean = {
            allParams.find(p => p.asVar.definedBy.contains(index)) match {
                case Some(param) => param.asVar.value.isReferenceValue
                case None        => false
            }
        }

        if (useSummaries && summaries.isSummarized(callStmt)) {
            summaries.compute(call, callStmt, in)
        } else if (icfg.getCalleesIfCallStatement(call).isEmpty) {
            // If the call does not have any callees, the code is unknown
            // and we safely handle it as the identity
            Set(in)
        } else {
            // Otherwise use the java call semantics
            in match {
                // Local variables that are of a reference type flow through the callee
                case Variable(index) if isRefTypeParam(index) => Set.empty
                // Arrays are references passed-by-value, thus their contents might change in the callee
                case ArrayElement(index, _) if allParams.exists(p => p.asVar.definedBy.contains(index)) => Set.empty
                // Fields can be written by reference, thus always through through the callee
                case InstanceField(index, _, _) if allParams.exists(p => p.asVar.definedBy.contains(index)) => Set.empty
                // Static fields are accessible everywhere, thus have to flow through all callee.
                case StaticField(_, _) => Set.empty
                // All facts that do not match any parameter or base object, as well as primitives flow over a call
                case f: TaintFact => Set(f)
            }
        }
    }

    /**
     * Called, when the exit to return facts are computed for some `callee` with the null fact and
     * the callee's return value is assigned to a variable.
     * Creates a taint, if necessary.
     *
     * @param callee The called method.
     * @param call The call.
     * @return Some variable fact, if necessary. Otherwise none.
     */
    protected def createTaints(callee: Method, call: JavaStatement): Set[TaintFact]

    /**
     * Called, when the call to return facts are computed for some `callee`.
     * Creates a FlowFact, if necessary.
     *
     * @param callee The method, which was called.
     * @param call The call.
     * @return Some FlowFact, if necessary. Otherwise None.
     */
    protected def createFlowFact(callee: Method, call: JavaStatement,
                                 in: TaintFact): Option[FlowFact]

    /**
     * If a parameter is tainted, the result will also be tainted.
     * We assume that the callee does not call the source method.
     */
    override def outsideAnalysisContext(callee: Method): Option[OutsideAnalysisContextHandler] = {
        if (useSummaries && summaries.isSummarized(callee)) {
            /* Kill the flow and apply the summary in CallToReturn. */
            Some(((_: JavaStatement, _: JavaStatement, _: TaintFact, _: Getter) => Set.empty): OutsideAnalysisContextHandler)
        } else
            super.outsideAnalysisContext(callee) match {
                case Some(_) => Some(((call: JavaStatement, successor: JavaStatement, in: TaintFact, _: Getter) => {
                    val allParams = JavaIFDSProblem.asCall(call.stmt).receiverOption ++ JavaIFDSProblem.asCall(call.stmt).params
                    if (call.stmt.astID == Assignment.ASTID && (in match {
                        case Variable(index) =>
                            allParams.zipWithIndex.exists {
                                case (param, _) if param.asVar.definedBy.contains(index) => true
                                case _                                                   => false
                            }
                        case ArrayElement(index, _) =>
                            allParams.zipWithIndex.exists {
                                case (param, _) if param.asVar.definedBy.contains(index) => true
                                case _                                                   => false
                            }
                        case _ => false
                    })) Set(Variable(call.index))
                    else Set.empty
                }): OutsideAnalysisContextHandler)
                case None => None
            }
    }

    /**
     * Creates new facts for an assignment. A new fact for the assigned variable will be created,
     * if the expression contains a tainted variable
     *
     * @param expression The source expression of the assignment
     * @param statement The assignment statement
     * @param in The incoming facts
     * @return The new facts, created by the assignment
     */
    private def createNewTaints(expression: Expr[V], statement: JavaStatement, in: TaintFact): Set[TaintFact] = {
        expression.astID match {
            case Var.ASTID =>
                val definedBy = expression.asVar.definedBy
                in match {
                    case Variable(index) if definedBy.contains(index) =>
                        Set(Variable(statement.index))
                    case _ => Set()
                }
            case ArrayLoad.ASTID =>
                val loadExpression = expression.asArrayLoad
                val arrayDefinedBy = loadExpression.arrayRef.asVar.definedBy
                if (in match {
                    // One specific array element may be tainted
                    case ArrayElement(index, taintedElement) =>
                        val loadedIndex = TaintProblem.getIntConstant(loadExpression.index, statement.code)
                        arrayDefinedBy.contains(index) &&
                            (loadedIndex.isEmpty || taintedElement == loadedIndex.get)
                    // Or the whole array
                    case Variable(index) => arrayDefinedBy.contains(index)
                    case _               => false
                }) Set(Variable(statement.index))
                else
                    Set.empty
            case GetField.ASTID =>
                val get = expression.asGetField
                val objectDefinedBy = get.objRef.asVar.definedBy
                if (in match {
                    // The specific field may be tainted
                    case InstanceField(index, _, taintedField) =>
                        taintedField == get.name && objectDefinedBy.contains(index)
                    // Or the whole object
                    case Variable(index) => objectDefinedBy.contains(index)
                    case _               => false
                })
                    Set(Variable(statement.index))
                else
                    Set.empty
            case GetStatic.ASTID =>
                val get = expression.asGetStatic
                if (in == StaticField(get.declaringClass, get.name))
                    Set(Variable(statement.index))
                else Set.empty
            case BinaryExpr.ASTID | PrefixExpr.ASTID | Compare.ASTID | PrimitiveTypecastExpr.ASTID |
                NewArray.ASTID | ArrayLength.ASTID =>
                (0 until expression.subExprCount).foldLeft(Set.empty[TaintFact])((acc, subExpr) =>
                    acc ++ createNewTaints(expression.subExpr(subExpr), statement, in))
            case _ => Set.empty
        }
    }

    /**
     * Checks, if the result of some variable expression could be tainted.
     *
     * @param expression The variable expression.
     * @param in The current data flow facts.
     * @return True, if the expression could be tainted
     */
    protected def isTainted(expression: Expr[V], in: TaintFact): Boolean = {
        val definedBy = expression.asVar.definedBy
        expression.isVar && (in match {
            case Variable(index)            => definedBy.contains(index)
            case ArrayElement(index, _)     => definedBy.contains(index)
            case InstanceField(index, _, _) => definedBy.contains(index)
            case _                          => false
        })
    }
}