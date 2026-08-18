import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.jimple.toolkits.invoke.SiteInliner;
import java.util.*;

public class SampleSceneTransform extends SceneTransformer {
    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        CallGraph cg = Scene.v().getCallGraph();

        for (SootClass sootClass : Scene.v().getApplicationClasses()) {
            for (SootMethod caller : sootClass.getMethods()) {
                if (!caller.hasActiveBody()) continue;

                Body body = caller.getActiveBody();
                // Use a snapshot iterator because SiteInliner modifies the UnitChain
                Iterator<Unit> it = body.getUnits().snapshotIterator();

                while (it.hasNext()) {
                    Unit unit = it.next();
                    Stmt stmt = (Stmt) unit;

                    if (stmt.containsInvokeExpr()) {
                        InvokeExpr invokeExpr = stmt.getInvokeExpr();

                        // 1. OO Reasoning: Target dynamic dispatch (virtual/interface calls)
                        if (invokeExpr instanceof VirtualInvokeExpr || invokeExpr instanceof InterfaceInvokeExpr) {
                            
                            // 2. Query Call Graph for this exact call site
                            Iterator<Edge> edges = cg.edgesOutOf(stmt);
                            List<SootMethod> targets = new ArrayList<>();
                            while (edges.hasNext()) {
                                targets.add(edges.next().tgt());
                            }

                            // 3. If strictly monomorphic, it is safe to inline
                            if (targets.size() == 1) {
                                SootMethod callee = targets.get(0);
                                
                                // 4. Safety checks before transformation
                                if (callee.hasActiveBody() && !callee.isNative() && callee.getDeclaringClass().isApplicationClass()) {
                                    
                                    // Optional: Add size threshold to avoid code bloat
                                    if (callee.getActiveBody().getUnits().size() < 25) {
                                        System.out.println("[Inlining] " + callee.getSignature() + " into " + caller.getSignature());
                                        
                                        // 5. The actual Bytecode Transformation
                                        SiteInliner.inlineSite(callee, stmt, caller);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}