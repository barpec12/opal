/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj
package tac
package fpcf
package properties

import org.opalj.fpcf.Property
import org.opalj.fpcf.PropertyMetaInformation
import org.opalj.value.KnownTypedValue
import org.opalj.tac.fpcf.analyses.ifds.JavaStatement

trait IFDSPropertyMetaInformation[DataFlowFact] extends PropertyMetaInformation {
    /**
     * Creates an IFDSProperty containing the result of this analysis.
     *
     * @param result Maps each exit statement to the facts, which hold after the exit statement.
     * @return An IFDSProperty containing the `result`.
     */
    def create(result: Map[JavaStatement, Set[DataFlowFact]]): IFDSProperty[DataFlowFact]
}

abstract class IFDSProperty[DataFlowFact]
    extends Property
    with IFDSPropertyMetaInformation[DataFlowFact] {

    /** The type of the TAC domain. */
    type V = DUVar[KnownTypedValue]

    /**
     * Maps exit statements to the data flow facts, which hold after them.
     */
    def flows: Map[JavaStatement, Set[DataFlowFact]]

    override def equals(other: Any): Boolean = other match {
        case that: IFDSProperty[DataFlowFact] ⇒
            // We cached the "hashCode" to make the following comparison more efficient;
            // note that all properties are eventually added to some set and therefore
            // the hashCode is required anyway!
            (this eq that) || (this.hashCode == that.hashCode && this.flows == that.flows)
        case _ ⇒
            false
    }

    override lazy val hashCode: Int = flows.hashCode()
}
