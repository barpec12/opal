/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj.js

import com.ibm.wala.cast.js.ipa.callgraph.{JSCFABuilder, JSCallGraphUtil}
import com.ibm.wala.cast.js.translator.CAstRhinoTranslatorFactory
import com.ibm.wala.cast.js.util.JSCallGraphBuilderUtil
import com.ibm.wala.dataflow.IFDS.TabulationDomain
import com.ibm.wala.ipa.callgraph.CallGraph
import com.ibm.wala.ipa.cfg.BasicBlockInContext
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction
import com.ibm.wala.ssa.analysis.IExplodedBasicBlock
import com.ibm.wala.util.collections.Pair
import com.ibm.wala.util.intset.{IntIterator, IntSet, IntSetUtil, MutableIntSet}
import org.opalj.br.analyses.SomeProject
import org.opalj.js.wala_ifds.WalaJavaScriptIFDSTaintAnalysis
import org.opalj.tac.fpcf.analyses.ifds.JavaStatement
import org.opalj.tac.fpcf.analyses.ifds.taint.TaintFact

import java.io.File

class JavaScriptAnalysis(p: SomeProject) {
    type Domain = TabulationDomain[Pair[Integer, BasicBlockInContext[IExplodedBasicBlock]], BasicBlockInContext[IExplodedBasicBlock]]

    val sourceFinder = new LocalJSSourceFinder(p)

    def analyze(stmt: JavaStatement, in: BindingFact): Set[TaintFact] = {
        val sourceFiles = sourceFinder(stmt)
        sourceFiles.flatMap(s => analyzeFile(s, in))
    }

    def analyzeFile(sourceFile: JavaScriptSource, in: BindingFact): Set[BindingFact] = {
        val beforeCode = s"function opal_source() { return \"secret\"; }\nfunction opal_last_stmt() { }\n\nvar ${in.keyName} = opal_source();\n"
        val afterCode = s"\nopal_last_stmt();\n"
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

        var varsAliveAfterJS: List[String] = List()

        def sinks(bb: BasicBlockInContext[IExplodedBasicBlock], r: IntSet, d: Domain): Void = {
            val inst = bb.getDelegate.getInstruction
            inst match {
                case invInst: SSAAbstractInvokeInstruction =>
                    CG.getPossibleTargets(bb.getNode, invInst.getCallSite).forEach(target => {
                        if (target.getMethod.getDeclaringClass.getName.toString.endsWith("opal_last_stmt")) {
                          /* Collect all tainted variables reaching the end of the JS script. */
                          val it: IntIterator = r.intIterator()
                          while (it.hasNext) {
                            val vn = d.getMappedObject(it.next())
                            varsAliveAfterJS ++= vn.snd.getNode.getIR.getLocalNames(1, vn.fst).toList
                          }
                        }
                        if (target.getMethod.getDeclaringClass.getName.toString.endsWith("opal_sink")) {
                          val it: IntIterator = r.intIterator()
                          val taints: MutableIntSet = IntSetUtil.make()
                          while (it.hasNext) {
                            val vn = d.getMappedObject(it.next())
                            taints.add(vn.fst)
                          }
                          val paramIdx: MutableIntSet = IntSetUtil.make()
                          for (i <- 1 until invInst.getNumberOfPositionalParameters) {
                            paramIdx.add(inst.getUse(i))
                          }
                          val taintedParams: IntSet = taints.intersection(paramIdx)
                          if (taintedParams.size() > 0) {
                            // TODO: taint ret val of ???
                          }
                        }
                    })
                case _ =>
            }
          null
        }

        WalaJavaScriptIFDSTaintAnalysis.startJSAnalysis(CG, sources, sinks)
        f.delete()
        varNamesToFacts(varsAliveAfterJS, in.index)
    }

    def varNamesToFacts(vars: List[String], defSite: Integer): Set[BindingFact] = {
        vars.map(v => BindingFact(defSite, v)).toSet
    }
}
