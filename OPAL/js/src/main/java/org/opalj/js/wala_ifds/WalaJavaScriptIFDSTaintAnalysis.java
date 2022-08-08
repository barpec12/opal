package org.opalj.js.wala_ifds;

import com.ibm.wala.cast.js.ipa.callgraph.JSCFABuilder;
import com.ibm.wala.cast.js.ipa.callgraph.JSCallGraphUtil;
import com.ibm.wala.cast.js.translator.CAstRhinoTranslatorFactory;
import com.ibm.wala.cast.js.util.JSCallGraphBuilderUtil;
import com.ibm.wala.cast.loader.AstMethod;
import com.ibm.wala.cast.tree.CAstSourcePositionMap;
import com.ibm.wala.cast.util.SourceBuffer;
import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.dataflow.IFDS.ICFGSupergraph;
import com.ibm.wala.dataflow.IFDS.PartiallyBalancedTabulationSolver;
import com.ibm.wala.dataflow.IFDS.TabulationResult;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.Entrypoint;
import com.ibm.wala.ipa.cfg.BasicBlockInContext;
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.analysis.IExplodedBasicBlock;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.intset.IntIterator;
import com.ibm.wala.util.intset.IntSet;
import org.opalj.tac.Call;

import java.io.IOException;
import java.net.URL;
import java.util.*;
import java.util.function.Function;

public class WalaJavaScriptIFDSTaintAnalysis {

    private final ICFGSupergraph supergraph;

    private final JSDomain domain;

    private final Function<BasicBlockInContext<IExplodedBasicBlock>, Boolean> sources;

    public WalaJavaScriptIFDSTaintAnalysis(CallGraph cg, Function<BasicBlockInContext<IExplodedBasicBlock>, Boolean> sources)
    {
        supergraph = ICFGSupergraph.make(cg);
        this.sources = sources;
        this.domain = new JSDomain();
    }

    public static void main(String... args) throws IllegalArgumentException, CancelException, WalaException, IOException {
//        String path = args[0];
//        String path = "file:///home/tim/Projects/wala-ifds/test.js";
        String path = "file:///tmp/opal7931685687191394247.js";
        JSCallGraphUtil.setTranslatorFactory(new CAstRhinoTranslatorFactory());
        URL url = new URL(path);
        JSCFABuilder B = JSCallGraphBuilderUtil.makeScriptCGBuilder("/tmp/", "opal7137384107899104585.js");
        AnalysisOptions opt = B.getOptions();
        CallGraph CG = B.makeCallGraph(opt);

        Function<BasicBlockInContext<IExplodedBasicBlock>, Boolean> sources = (ebb) -> {
            SSAInstruction inst = ebb.getDelegate().getInstruction();
            if (inst instanceof SSAAbstractInvokeInstruction) {
                for (CGNode target : CG.getPossibleTargets(ebb.getNode(), ((SSAAbstractInvokeInstruction) inst).getCallSite())) {
                    System.out.println(target.getMethod().getDeclaringClass().getName().toString());

                    if (target.getMethod().getDeclaringClass().getName().toString().endsWith("opal_source"))
                        return true;
                }
            }

            return false;
        };

        Function<BasicBlockInContext<IExplodedBasicBlock>, Boolean> sinks = (bb) -> {
            SSAInstruction inst = bb.getDelegate().getInstruction();
          if (inst instanceof SSAAbstractInvokeInstruction) {
                for (CGNode target : CG.getPossibleTargets(bb.getNode(), ((SSAAbstractInvokeInstruction) inst).getCallSite())) {
                    if (target.getMethod().getDeclaringClass().getName().toString().endsWith("opal_sink"))
                        return true;
                }
            }
            return false;
        };

        analyzeTaint(CG, sources, sinks).forEach(sinkPos -> {
            try {
                System.out.println(new SourceBuffer(sinkPos).toString());
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        });
    }

    /**
     * Call the WALA IFDS analysis with custom sources and sinks functions and then returns the sinks as source code
     * of the provided file. (Yeah, hacky, I know...)
     * @param CG Call Graph
     * @param sources Return true iff node is a source
     * @param sinks Return true iff node is a sink
     * @return sinks as source code of the provided file
     */
    public static List<String> startJSAnalysis(CallGraph CG,
                                               Function<BasicBlockInContext<IExplodedBasicBlock>, Boolean> sources,
                                               Function<BasicBlockInContext<IExplodedBasicBlock>, Boolean> sinks) {
        List<String> reachedSinks = new ArrayList<>();
        analyzeTaint(CG, sources, sinks).forEach(sinkPos -> {
            try {
                reachedSinks.add(new SourceBuffer(sinkPos).toString());
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        });
        return reachedSinks;
    }

    public TabulationResult<BasicBlockInContext<IExplodedBasicBlock>, CGNode, Pair<Integer,BasicBlockInContext<IExplodedBasicBlock>>> analyze() {
        PartiallyBalancedTabulationSolver<BasicBlockInContext<IExplodedBasicBlock>, CGNode, Pair<Integer, BasicBlockInContext<IExplodedBasicBlock>>> solver = PartiallyBalancedTabulationSolver
                .createPartiallyBalancedTabulationSolver(new JSProblem(domain, supergraph, sources), null);
        TabulationResult<BasicBlockInContext<IExplodedBasicBlock>, CGNode, Pair<Integer, BasicBlockInContext<IExplodedBasicBlock>>> result = null;
        try {
            result = solver.solve();
        } catch (CancelException e) {
            // this shouldn't happen
            assert false;
        }
        return result;
    }

    public static Set<CAstSourcePositionMap.Position> analyzeTaint(CallGraph CG, Function<BasicBlockInContext<IExplodedBasicBlock>, Boolean> sources, Function<BasicBlockInContext<IExplodedBasicBlock>, Boolean> sinks) {
        WalaJavaScriptIFDSTaintAnalysis A = new WalaJavaScriptIFDSTaintAnalysis(CG, sources);

        TabulationResult<BasicBlockInContext<IExplodedBasicBlock>,
                         CGNode, Pair<Integer, BasicBlockInContext<IExplodedBasicBlock>>> R = A.analyze();

        Set<CAstSourcePositionMap.Position> result = HashSetFactory.make();

        R.getSupergraphNodesReached().forEach((sbb) -> {
            if (sinks.apply(sbb)) {
                BasicBlockInContext<IExplodedBasicBlock> bb = sbb;
                SSAInstruction inst = bb.getDelegate().getInstruction();
                if (bb.getMethod() instanceof AstMethod) {
                    AstMethod.DebuggingInformation dbg = ((AstMethod)bb.getMethod()).debugInfo();
                    CAstSourcePositionMap.Position pos = dbg.getInstructionPosition(inst.iIndex());
                    result.add(pos);
                }
            }
        });
        return result;
    }
}
