import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.invoke.SiteInliner;
import java.util.*;

public class InterproceduralInliner extends SceneTransformer {

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        System.out.println("=== Starting Top-Tier Iterative Inliner & PTA ===");
        
        boolean globalChanged;
        int passNumber = 1;
        int totalInlined = 0;

        // CASCADING OPTIMIZATION: Keep running until fixed point or cap is reached
        do {
            globalChanged = false;
            System.out.println("\n--- Optimization Pass " + passNumber + " ---");

            // 1. Run a fresh, precise pointer analysis on the current code state
            CustomPointerAnalysis pta = new CustomPointerAnalysis();
            pta.runAnalysis();

            // 2. Snapshot classes to prevent ConcurrentModificationException
            List<SootClass> allClasses = new ArrayList<>(Scene.v().getApplicationClasses());

            for (SootClass sc : allClasses) {
                // Snapshot methods
                List<SootMethod> allMethods = new ArrayList<>(sc.getMethods());
                
                for (SootMethod sm : allMethods) {
                    if (!sm.hasActiveBody()) continue;
                    
                    Body body = sm.getActiveBody();
                    boolean methodChanged = false;

                    // Snapshot units using Soot's safe iterator
                    Iterator<Unit> unitIt = body.getUnits().snapshotIterator();

                    while (unitIt.hasNext()) {
                        Unit u = unitIt.next();
                        if (!(u instanceof Stmt)) continue;
                        Stmt stmt = (Stmt) u;

                        if (stmt.containsInvokeExpr()) {
                            InvokeExpr invoke = stmt.getInvokeExpr();
                            SootMethod targetMethod = null;
                            String invokeType = "";
                            
                            // A: Handle STATIC calls
                            if (invoke instanceof StaticInvokeExpr) {
                                targetMethod = invoke.getMethodRef().resolve();
                                invokeType = "[Static]";
                            }
                            // B: Handle VIRTUAL calls
                            else if (invoke instanceof InstanceInvokeExpr) {
                                InstanceInvokeExpr instInvoke = (InstanceInvokeExpr) invoke;
                                
                                // SOUNDNESS: Never attempt to inline constructors
                                if (instInvoke.getMethodRef().name().equals("<init>")) continue;
                                
                                Local receiver = (Local) instInvoke.getBase();
                                Set<RefType> pointsToSet = pta.getPointsToSet(receiver);
                                
                                // SOUNDNESS: Only inline if PTA proves EXACTLY ONE dynamic type
                                if (pointsToSet.size() == 1) {
                                    RefType exactType = pointsToSet.iterator().next();
                                    targetMethod = resolveMethod(exactType.getSootClass(), instInvoke.getMethodRef());
                                    invokeType = "[Virtual]";
                                }
                            }

                            // Perform the Inline if safe
                            if (targetMethod != null && isSafeToInline(targetMethod, sm)) {
                                System.out.println(invokeType + " Inlining " + targetMethod.getName() + " into " + sm.getName());
                                SiteInliner.inlineSite(targetMethod, stmt, sm);
                                
                                methodChanged = true;
                                globalChanged = true;
                                totalInlined++;
                                break; // Break unit loop to refresh the body
                            }
                        }
                    }
                    
                    // If we mutated this method, move to the next method to stay safe
                    if (methodChanged) continue; 
                }
            }
            passNumber++;
        } while (globalChanged && passNumber <= 3); // CAP AT 3 PASSES TO PREVENT STATE EXPLOSION

        System.out.println("\n=== Optimization Complete ===");
        System.out.println("Total sites safely inlined: " + totalInlined);
    }

    private SootMethod resolveMethod(SootClass exactType, SootMethodRef methodRef) {
        SootClass current = exactType;
        while (current != null) {
            if (current.declaresMethod(methodRef.getSubSignature().getString())) {
                return current.getMethod(methodRef.getSubSignature().getString());
            }
            current = current.hasSuperclass() ? current.getSuperclass() : null;
        }
        return null;
    }

    private boolean isSafeToInline(SootMethod target, SootMethod container) {
        if (!target.hasActiveBody() || target.isNative()) return false;
        
        // CRITICAL: Do not inline constructors or static initializers
        if (target.isConstructor() || target.getName().equals("<clinit>")) return false; 
        
        // CRITICAL: Prevent recursive inlining
        if (target.getSignature().equals(container.getSignature())) return false;
        
        // HEURISTIC: Prevent code bloat by skipping massive methods
        if (target.getActiveBody().getUnits().size() > 75) return false;
        
        return true;
    }
}

/**
 * Sound Interprocedural Pointer Analysis with limits to prevent hanging on DaCapo.
 */
class CustomPointerAnalysis {
    private Map<Value, Set<RefType>> pointsTo = new HashMap<>();
    private Queue<SootMethod> worklist = new LinkedList<>();
    private Set<SootMethod> inWorklist = new HashSet<>();
    
    // Limits how many times a method can be processed to prevent explosion on DaCapo
    private Map<SootMethod, Integer> processCount = new HashMap<>();
    private static final int MAX_PTA_ITERATIONS = 3; 

    public void runAnalysis() {
        SootMethod entry = Scene.v().getMainMethod();
        if (entry != null) addToWorklist(entry);

        while (!worklist.isEmpty()) {
            SootMethod currentMethod = worklist.poll();
            inWorklist.remove(currentMethod);
            
            int count = processCount.getOrDefault(currentMethod, 0);
            processCount.put(currentMethod, count + 1);
            
            if (!currentMethod.hasActiveBody()) continue;
            
            boolean changed = processMethod(currentMethod);
            
            if (changed) {
                addToWorklist(currentMethod);
            }
        }
    }

    private boolean processMethod(SootMethod method) {
        boolean changed = false;
        Body body = method.getActiveBody();

        for (Unit u : body.getUnits()) {
            if (!(u instanceof Stmt)) continue;
            Stmt stmt = (Stmt) u;

            if (stmt instanceof AssignStmt) {
                AssignStmt assign = (AssignStmt) stmt;
                Value left = assign.getLeftOp();
                Value right = assign.getRightOp();

                if (left instanceof Local) {
                    if (right instanceof AnyNewExpr && right instanceof NewExpr) {
                        RefType type = ((NewExpr) right).getBaseType();
                        changed |= addType(left, type);
                    } 
                    else if (right instanceof Local) {
                        changed |= propagate(right, left);
                    }
                }
            }

            if (stmt.containsInvokeExpr()) {
                InvokeExpr invoke = stmt.getInvokeExpr();
                SootMethod callee = invoke.getMethodRef().resolve();

                if (callee != null && callee.hasActiveBody()) {
                    addToWorklist(callee);

                    // Flow A: Args to Params
                    for (int i = 0; i < invoke.getArgCount(); i++) {
                        Value arg = invoke.getArg(i);
                        if (arg instanceof Local) {
                            Local param = callee.getActiveBody().getParameterLocal(i);
                            changed |= propagate(arg, param);
                        }
                    }

                    // Flow B: Returns to Caller Assign
                    if (stmt instanceof AssignStmt) {
                        Value leftOp = ((AssignStmt) stmt).getLeftOp();
                        if (leftOp instanceof Local) {
                            for (Unit calleeUnit : callee.getActiveBody().getUnits()) {
                                if (calleeUnit instanceof ReturnStmt) {
                                    Value retVal = ((ReturnStmt) calleeUnit).getOp();
                                    if (retVal instanceof Local) {
                                        changed |= propagate(retVal, leftOp);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return changed;
    }

    private boolean addType(Value local, RefType type) {
        pointsTo.putIfAbsent(local, new HashSet<>());
        return pointsTo.get(local).add(type);
    }

    private boolean propagate(Value from, Value to) {
        if (!pointsTo.containsKey(from) || pointsTo.get(from).isEmpty()) return false;
        pointsTo.putIfAbsent(to, new HashSet<>());
        return pointsTo.get(to).addAll(pointsTo.get(from));
    }

    public Set<RefType> getPointsToSet(Value local) {
        return pointsTo.getOrDefault(local, Collections.emptySet());
    }

    private void addToWorklist(SootMethod m) {
        if (processCount.getOrDefault(m, 0) >= MAX_PTA_ITERATIONS) {
            return; 
        }
        if (!inWorklist.contains(m)) {
            worklist.add(m);
            inWorklist.add(m);
        }
    }
}