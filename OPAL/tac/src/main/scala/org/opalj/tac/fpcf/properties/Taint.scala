/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj.tac.fpcf.properties

import org.opalj.fpcf.PropertyKey
import org.opalj.tac.fpcf.analyses.ifds.JavaStatement
import org.opalj.tac.fpcf.analyses.ifds.taint.Fact

/**
 * The IFDSProperty for this analysis.
 */
case class Taint(flows: Map[JavaStatement, Set[Fact]]) extends IFDSProperty[Fact] {

    override type Self = Taint
    override def create(result: Map[JavaStatement, Set[Fact]]): IFDSProperty[Fact] = new Taint(result)

    override def key: PropertyKey[Taint] = Taint.key
}

object Taint extends IFDSPropertyMetaInformation[Fact] {

    override type Self = Taint
    override def create(result: Map[JavaStatement, Set[Fact]]): IFDSProperty[Fact] = new Taint(result)

    val key: PropertyKey[Taint] = PropertyKey.create("Taint", new Taint(Map.empty))
}
