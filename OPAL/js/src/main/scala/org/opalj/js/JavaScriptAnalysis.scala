/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj.js

import com.ibm.wala.cast.js.ipa.callgraph.{JSCFABuilder, JSCallGraphUtil}
import com.ibm.wala.cast.js.translator.CAstRhinoTranslatorFactory
import com.ibm.wala.cast.js.util.JSCallGraphBuilderUtil
import com.ibm.wala.ipa.callgraph.CallGraph
import com.ibm.wala.ipa.cfg.BasicBlockInContext
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction
import com.ibm.wala.ssa.analysis.IExplodedBasicBlock
import org.opalj.br.analyses.SomeProject
import org.opalj.js.wala_ifds.WalaJavaScriptIFDSTaintAnalysis
import org.opalj.tac.fpcf.analyses.ifds.JavaStatement
import org.opalj.tac.fpcf.analyses.ifds.taint.TaintFact

import java.io.File
import scala.jdk.CollectionConverters._
import scala.util.matching.Regex

class JavaScriptAnalysis(p: SomeProject) {
    val sourceFinder = new LocalJSSourceFinder(p);

    def analyze(stmt: JavaStatement, in: BindingFact): Set[TaintFact] = {
        val sourceFiles = sourceFinder(stmt)
        sourceFiles.flatMap(s => analyzeFile(s, stmt, in))
    }

    def analyzeFile(sourceFile: JavaScriptSource, stmt: JavaStatement, in: BindingFact): Set[BindingFact] = {
        val beforeCode = s"function opal_source() { return \"secret\"; }\nfunction opal_sink(v) { }\n\nvar ${in.keyName} = opal_source();\n"
        val afterCode = s"\nopal_sink(${in.keyName});\n"
        val f: File = sourceFile.asFile(beforeCode, afterCode)

        JSCallGraphUtil.setTranslatorFactory(new CAstRhinoTranslatorFactory)
        val B: JSCFABuilder = JSCallGraphBuilderUtil.makeScriptCGBuilder(f.getParent, f.getName)
        val CG: CallGraph = B.makeCallGraph(B.getOptions)

        def sources(ebb: BasicBlockInContext[IExplodedBasicBlock]): Boolean = {
            val inst = ebb.getDelegate.getInstruction
            inst match {
                case i: SSAAbstractInvokeInstruction =>
                    CG.getPossibleTargets(ebb.getNode, i.getCallSite).forEach(target => {
                        if (target.getMethod.getDeclaringClass.getName.toString.endsWith("opal_source")) return true
                    })
                case _ =>
            }
            false
        }

        def sinks(bb: BasicBlockInContext[IExplodedBasicBlock]): Boolean = {
            val inst = bb.getDelegate.getInstruction
            inst match {
                case i: SSAAbstractInvokeInstruction =>
                    CG.getPossibleTargets(bb.getNode, i.getCallSite).forEach(target => {
                        if (target.getMethod.getDeclaringClass.getName.toString.endsWith("opal_sink")) return true
                    })
                case _ =>
            }
            false
        }

        val reachedSinks = WalaJavaScriptIFDSTaintAnalysis.startJSAnalysis(CG, sources, sinks)
        f.delete()
        sourceLinesToBindingFacts(reachedSinks.asScala, in.index)
    }

    def sourceLinesToBindingFacts(reachedSinks: IterableOnce[String], defSite: Integer): Set[BindingFact] = {
        val pattern: Regex = """opal_sink\((.*?)\)""".r
        var lst: Set[BindingFact] = Set()
        reachedSinks.iterator.foreach(s => {
          val res: Option[Regex.Match] = pattern.findFirstMatchIn(s)
          if (res.isDefined)
            lst += BindingFact(defSite, res.get.group(1))
        })
        lst
    }
}
