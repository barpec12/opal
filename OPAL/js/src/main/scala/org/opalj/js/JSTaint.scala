/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj.js

import org.opalj.fpcf.PropertyKey
import org.opalj.ifds.{IFDSProperty, IFDSPropertyMetaInformation}
import org.opalj.tac.fpcf.analyses.ifds.JavaStatement

case class JSTaint(flows: Map[JavaStatement, Set[JSFact]], debugData: Map[JavaStatement, Set[JSFact]] = Map.empty) extends IFDSProperty[JavaStatement, JSFact] {

    override type Self = JSTaint
    override def create(result: Map[JavaStatement, Set[JSFact]]): IFDSProperty[JavaStatement, JSFact] = new JSTaint(result)
    override def create(result: Map[JavaStatement, Set[JSFact]], debugData: Map[JavaStatement, Set[JSFact]]): IFDSProperty[JavaStatement, JSFact] = new JSTaint(result, debugData)

    override def key: PropertyKey[JSTaint] = JSTaint.key
}

object JSTaint extends IFDSPropertyMetaInformation[JavaStatement, JSFact] {

    override type Self = JSTaint
    override def create(result: Map[JavaStatement, Set[JSFact]]): IFDSProperty[JavaStatement, JSFact] = new JSTaint(result)
    override def create(result: Map[JavaStatement, Set[JSFact]], debugData: Map[JavaStatement, Set[JSFact]]): IFDSProperty[JavaStatement, JSFact] = new JSTaint(result, debugData)

    val key: PropertyKey[JSTaint] = PropertyKey.create("JSTaint", new JSTaint(Map.empty))
}
