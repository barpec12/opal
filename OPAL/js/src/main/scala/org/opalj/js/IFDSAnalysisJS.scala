/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj.js

import org.opalj.br.Method
import org.opalj.br.analyses.SomeProject
import org.opalj.ifds.Dependees.Getter
import org.opalj.tac.Assignment
import org.opalj.tac.fpcf.analyses.ifds.{JavaMethod, JavaStatement}
import org.opalj.tac.fpcf.analyses.ifds.taint.{ArrayElement, Fact, FlowFact, ForwardTaintProblem, InstanceField, NullFact, StaticField, Variable}

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
    override protected def createFlowFact(callee: Method, call: JavaStatement, in: Fact): Option[FlowFact] =
        if (callee.name == "sink" && in == Variable(-2))
            Some(FlowFact(Seq(JavaMethod(call.method), JavaMethod(callee))))
        else None

    /**
     * The entry points of this analysis.
     */
    override def entryPoints: Seq[(Method, Fact)] = (for {
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

    def defaultOutsideAnalysisContextHandler(call: JavaStatement, in: Fact) = {
        val allParams = asCall(call.stmt).receiverOption ++ asCall(call.stmt).params
        if (call.stmt.astID == Assignment.ASTID && (in match {
            case Variable(index) ⇒
                allParams.zipWithIndex.exists {
                    case (param, _) if param.asVar.definedBy.contains(index) ⇒ true
                    case _                                                   ⇒ false
                }
            case ArrayElement(index, _) ⇒
                allParams.zipWithIndex.exists {
                    case (param, _) if param.asVar.definedBy.contains(index) ⇒ true
                    case _                                                   ⇒ false
                }
            case _ ⇒ false
        })) Set(Variable(call.index))
        else Set.empty
    }

    def matchCallArgument(call: JavaStatement, in: Fact): Set[Fact] = {
        val callStmt = asCall(call.stmt)
        val allParamsWithIndices = callStmt.allParams.zipWithIndex
        in match {
            // Taint formal parameter if actual parameter is tainted
            case Variable(index) ⇒
                allParamsWithIndices.flatMap {
                    case (param, paramIndex) if param.asVar.definedBy.contains(index) ⇒
                        Some(Variable(index)) // offset JNIEnv
                    case _ ⇒ None // Nothing to do
                }.toSet
            // Taint element of formal parameter if element of actual parameter is tainted
            case ArrayElement(index, taintedIndex) ⇒
                allParamsWithIndices.flatMap {
                    case (param, paramIndex) if param.asVar.definedBy.contains(index) ⇒
                        Some(ArrayElement(index, taintedIndex)) // offset JNIEnv
                    case _ ⇒ None // Nothing to do
                }.toSet

            case InstanceField(index, declaredClass, taintedField) ⇒
                // Taint field of formal parameter if field of actual parameter is tainted
                // Only if the formal parameter is of a type that may have that field!
                allParamsWithIndices.flatMap {
                    case (param, paramIndex) if param.asVar.definedBy.contains(index) ⇒
                        Some(InstanceField(index, declaredClass, taintedField))
                    case _ ⇒ None // Nothing to do
                }.toSet
            case StaticField(classType, fieldName) ⇒ Set.empty
            case NullFact                          ⇒ Set.empty
            case _                                 ⇒ Set.empty
        }
    }

    def handleScriptCall(call: JavaStatement, successor: JavaStatement, in: Fact, dependeesGetter: Getter): Set[Fact] = {
        val argSet = matchCallArgument(call, in)
        argSet
    }

    def invokesScriptFunction(callee: Method): Boolean =
        callee.classFile.fqn == "javax/script/Invocable" && callee.name == "invokeFunction"

    /**
     * If a parameter is tainted, the result will also be tainted.
     * We assume that the callee does not call the source method.
     */
    override def outsideAnalysisContext(callee: Method): Option[OutsideAnalysisContextHandler] = {
        if (invokesScriptFunction(callee)) {
            Some(handleScriptCall _)
        } else {
            super.outsideAnalysisContext(callee)
        }
    }
}
