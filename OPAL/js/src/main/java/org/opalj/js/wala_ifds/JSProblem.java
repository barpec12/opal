package org.opalj.js.wala_ifds;

import com.ibm.wala.dataflow.IFDS.*;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.cfg.BasicBlockInContext;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.analysis.IExplodedBasicBlock;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Pair;

import java.util.Collection;
import java.util.function.Function;

class JSProblem implements PartiallyBalancedTabulationProblem<BasicBlockInContext<IExplodedBasicBlock>, CGNode, Pair<Integer, BasicBlockInContext<IExplodedBasicBlock>>> {
    private ISupergraph<BasicBlockInContext<IExplodedBasicBlock>, CGNode> supergraph;
    private JSDomain domain;
    private Function<BasicBlockInContext<IExplodedBasicBlock>, Boolean> sources;
    /** path edges corresponding to taint sources */
    private final Collection<PathEdge<BasicBlockInContext<IExplodedBasicBlock>>> initialSeeds;

    private final JSFlowFunctions flowFunctions;

    public JSProblem(JSDomain domain, ISupergraph<BasicBlockInContext<IExplodedBasicBlock>, CGNode> supergraph, Function<BasicBlockInContext<IExplodedBasicBlock>, Boolean> sources)
    {
        this.supergraph = supergraph;
        this.domain = domain;
        this.sources = sources;
        this.initialSeeds = collectInitialSeeds();
        this.flowFunctions = new JSFlowFunctions(domain, supergraph);
    }

    /**
     * we use the entry block of the CGNode as the fake entry when propagating from
     * callee to caller with unbalanced parens
     */
    @Override
    public BasicBlockInContext<IExplodedBasicBlock> getFakeEntry(BasicBlockInContext<IExplodedBasicBlock> node) {
        final CGNode cgNode = node.getNode();
        return getFakeEntry(cgNode);
    }

    /**
     * we use the entry block of the CGNode as the "fake" entry when propagating
     * from callee to caller with unbalanced parens
     */
    private BasicBlockInContext<IExplodedBasicBlock> getFakeEntry(final CGNode cgNode) {
        BasicBlockInContext<IExplodedBasicBlock>[] entriesForProcedure = supergraph.getEntriesForProcedure(cgNode);
        assert entriesForProcedure.length == 1;
        return entriesForProcedure[0];
    }

    /**
     * collect sources of taint
     */
    private Collection<PathEdge<BasicBlockInContext<IExplodedBasicBlock>>> collectInitialSeeds() {
        Collection<PathEdge<BasicBlockInContext<IExplodedBasicBlock>>> result = HashSetFactory.make();
//        supergraph.getProcedureGraph().forEach(cgNode -> {
//            IMethod m = cgNode.getMethod();
//            if (m instanceof JavaScriptConstructorFunctions.JavaScriptConstructor) {
//                JavaScriptConstructorFunctions.JavaScriptConstructor ctor = (JavaScriptConstructorFunctions.JavaScriptConstructor) m;
//                System.out.println(ctor.constructedType().toString());
//                if (ctor.constructedType().getName().toString().endsWith("calledFromJava")) {
//                   BasicBlockInContext<IExplodedBasicBlock> bb = supergraph.getLocalBlock(cgNode, 0);
//                }
//            }
////            System.out.println(cgNode.getMethod().getClass().toString());
//        });

        for (BasicBlockInContext<IExplodedBasicBlock> bb : supergraph) {
//            System.out.println(bb.getMethod().getDeclaringClass().getName());
            IExplodedBasicBlock ebb = bb.getDelegate();
            SSAInstruction instruction = ebb.getInstruction();
            IR ir = bb.getNode().getIR();
            for(int v = 0; instruction != null && v < instruction.getNumberOfUses(); v++) {
                String[] arr = ir.getLocalNames(bb.getNumber(), instruction.getUse(v));
//                System.out.println(Arrays.toString(arr));
            }
            if (sources.apply(bb)) {
                Pair<Integer, BasicBlockInContext<IExplodedBasicBlock>> fact = Pair.make(instruction.getDef(), bb);
                final CGNode cgNode = bb.getNode();
                int factNum = domain.add(fact);
                BasicBlockInContext<IExplodedBasicBlock> fakeEntry = getFakeEntry(cgNode);
                // note that the fact number used for the source of this path edge doesn't
                // really matter
                result.add(PathEdge.createPathEdge(fakeEntry, factNum, bb, factNum));
            }
        }
        return result;
    }

    @Override
    public IPartiallyBalancedFlowFunctions<BasicBlockInContext<IExplodedBasicBlock>> getFunctionMap() {
        return flowFunctions;
    }

    @Override
    public JSDomain getDomain() {
        return domain;
    }

    /**
     * we don't need a merge function; the default unioning of tabulation works fine
     */
    @Override
    public IMergeFunction getMergeFunction() {
        return null;
    }

    @Override
    public ISupergraph<BasicBlockInContext<IExplodedBasicBlock>, CGNode> getSupergraph() {
        return supergraph;
    }

    @Override
    public Collection<PathEdge<BasicBlockInContext<IExplodedBasicBlock>>> initialSeeds() {
        return initialSeeds;
    }
}