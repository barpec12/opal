/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj.js

import org.opalj.br.Method
import org.opalj.br.analyses.SomeProject
import org.opalj.ifds.Dependees.Getter
import org.opalj.tac.Assignment
import org.opalj.tac.fpcf.analyses.ifds.{JavaMethod, JavaStatement}
import org.opalj.tac.fpcf.analyses.ifds.taint.{ArrayElement, Fact, FlowFact, ForwardTaintProblem, NullFact, Variable}

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

    /**
     * If a parameter is tainted, the result will also be tainted.
     * We assume that the callee does not call the source method.
     */
    override def outsideAnalysisContext(callee: Method): Option[OutsideAnalysisContextHandler] = {
        super.outsideAnalysisContext(callee) match {
            case Some(_) ⇒ Some(((call: JavaStatement, successor: JavaStatement, in: Fact, _: Getter) ⇒ {
                val baseObject = asCall(call.stmt).receiverOption
                if (baseObject.isDefined) {
                    System.out.println("BO TYPE: "+baseObject.get.cTpe)
                }
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
            }): OutsideAnalysisContextHandler)
            case None ⇒ None
        }

    }
}
