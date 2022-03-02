/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj.ll.fpcf.analyses.ifds.taint

import org.opalj.br.analyses.SomeProject
import org.opalj.br.DeclaredMethod
import org.opalj.fpcf.PropertyStore
import org.opalj.tac.fpcf.analyses.ifds.{ForwardIFDSAnalysis, IFDSAnalysis, JavaStatement}
import org.opalj.tac.fpcf.analyses.ifds.taint.{Fact, FlowFact, ForwardTaintProblem, NullFact, Variable}
import org.opalj.tac.fpcf.properties.{IFDSPropertyMetaInformation, Taint}

/**
 * An analysis that checks, if the return value of the method `source` can flow to the parameter of
 * the method `sink`.
 *
 * @author Mario Trageser
 * @author Marc Clement
 */
class MultilingualForwardTaintAnalysis private (implicit val project: SomeProject)
    extends ForwardIFDSAnalysis(new MultilingualForwardTaintProblem(project), Taint)

class MultilingualForwardTaintProblem(p: SomeProject) extends ForwardTaintProblem(p) {

    /**
     * The analysis starts with all public methods in TaintAnalysisTestClass.
     */
    override val entryPoints: Seq[(DeclaredMethod, Fact)] = (for {
        m ← p.allMethodsWithBody
        if (m.name == "main")
    } yield declaredMethods(m) -> NullFact)

    /**
     * The sanitize method is a sanitizer.
     */
    override protected def sanitizesReturnValue(callee: DeclaredMethod): Boolean =
        callee.name == "sanitize"

    /**
     * We do not sanitize paramters.
     */
    override protected def sanitizeParamters(call: JavaStatement, in: Set[Fact]): Set[Fact] = Set.empty

    /**
     * Creates a new variable fact for the callee, if the source was called.
     */
    override protected def createTaints(callee: DeclaredMethod, call: JavaStatement): Set[Fact] =
        if (callee.name == "source") Set(Variable(call.index))
        else Set.empty

    /**
     * Create a FlowFact, if sink is called with a tainted variable.
     * Note, that sink does not accept array parameters. No need to handle them.
     */
    override protected def createFlowFact(
        callee: DeclaredMethod,
        call:   JavaStatement,
        in:     Set[Fact]
    ): Option[FlowFact] =
        if (callee.name == "sink" && in.contains(Variable(-2))) Some(FlowFact(Seq(call.method)))
        else None

    // Multilingual additions here

    override def insideAnalysisContext(callee: DeclaredMethod): Boolean = {
        super.insideAnalysisContext(callee) //|| callee.definedMethod.isNative
    }

}

object MultilingualForwardTaintAnalysis extends IFDSAnalysis[Fact] {

    override def init(p: SomeProject, ps: PropertyStore) = new MultilingualForwardTaintAnalysis()(p)

    override def property: IFDSPropertyMetaInformation[Fact] = Taint
}
