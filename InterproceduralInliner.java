import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.invoke.SiteInliner;
import java.util.*;

public class InterproceduralInliner extends SceneTransformer {

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        System.out.println("--- Starting Iterative Inlining & Pointer Analysis ---");
        
        boolean globalChanged;
        int passNumber = 1;
        int totalInlined = 0;

        // Iterative optimization: Keep running until no more methods can be inlined
        do {
            globalChanged = false;
            System.out.println("\n--- Pass " + passNumber + " ---");

            // 1. Run a fresh pointer analysis on the current state of the code
            CustomPointerAnalysis pta = new CustomPointerAnalysis();
            pta.runAnalysis();

            for (SootClass sc : Scene.v().getApplicationClasses()) {
                for (SootMethod sm : sc.getMethods()) {
                    if (!sm.hasActiveBody()) continue;
                    
                    Body body = sm.getActiveBody();
                    boolean methodChanged = false;

                    // Copy units to a list to avoid ConcurrentModificationException during inlining
                    List<Unit> unitsToProcess = new ArrayList<>(body.getUnits());

                    for (Unit u : unitsToProcess) {
                        if (!(u instanceof Stmt)) continue;
                        Stmt stmt = (Stmt) u;

                        if (stmt.containsInvokeExpr()) {
                            InvokeExpr invoke = stmt.getInvokeExpr();
                            
                            // A: Handle STATIC calls (e.g., Factory.createOp())
                            if (invoke instanceof StaticInvokeExpr) {
                                SootMethod targetMethod = invoke.getMethod();
                                
                                if (isSafeToInline(targetMethod, sm)) {
                                    System.out.println("[Static] Inlining " + targetMethod.getName() + " into " + sm.getName());
                                    SiteInliner.inlineSite(targetMethod, stmt, sm);
                                    
                                    methodChanged = true;
                                    globalChanged = true;
                                    totalInlined++;
                                    break; // Break the unit loop to refresh the body in the next pass
                                }
                            }
                            // B: Handle VIRTUAL calls (e.g., op.execute(i))
                            else if (invoke instanceof InstanceInvokeExpr) {
                                InstanceInvokeExpr instInvoke = (InstanceInvokeExpr) invoke;
                                
                                // Skip constructor calls entirely during analysis
                                if (instInvoke.getMethodRef().name().equals("<init>")) continue;
                                
                                Local receiver = (Local) instInvoke.getBase();
                                Set<RefType> pointsToSet = pta.getPointsToSet(receiver);
                                
                                // Soundness: Only inline if there is exactly one dynamic type
                                if (pointsToSet != null && pointsToSet.size() == 1) {
                                    RefType exactType = pointsToSet.iterator().next();
                                    SootClass targetClass = exactType.getSootClass();
                                    
                                    SootMethod targetMethod = resolveMethod(targetClass, instInvoke.getMethodRef());
                                    
                                    if (targetMethod != null && isSafeToInline(targetMethod, sm)) {
                                        System.out.println("[Virtual] Inlining " + targetMethod.getName() + " into " + sm.getName());
                                        SiteInliner.inlineSite(targetMethod, stmt, sm);
                                        
                                        methodChanged = true;
                                        globalChanged = true;
                                        totalInlined++;
                                        break; // Break the unit loop to refresh the body in the next pass
                                    }
                                }
                            }
                        }
                    }
                    
                    // If we mutated this method, we break out and let the global loop re-analyze
                    if (methodChanged) {
                        break; 
                    }
                }
            }
            passNumber++;
        } while (globalChanged);

        System.out.println("\n--- Optimization Complete ---");
        System.out.println("Total sites inlined (Static + Virtual): " + totalInlined);
    }

    private SootMethod resolveMethod(SootClass exactType, SootMethodRef methodRef) {
        SootClass current = exactType;
        while (current != null) {
            if (current.declaresMethod(methodRef.getSubSignature().getString())) {
                return current.getMethod(methodRef.getSubSignature().getString());
            }
            if (current.hasSuperclass()) {
                current = current.getSuperclass();
            } else {
                break;
            }
        }
        return null;
    }

    private boolean isSafeToInline(SootMethod target, SootMethod container) {
        if (!target.hasActiveBody() || target.isNative()) return false;
        
        // CRITICAL FIX: Never inline constructors or static initializers
        if (target.isConstructor() || target.getName().equals("<clinit>")) return false; 
        
        // Prevent recursive inlining
        if (target.getSignature().equals(container.getSignature())) return false;
        
        // Prevent inlining massive methods (heuristic)
        if (target.getActiveBody().getUnits().size() > 100) return false;
        
        return true;
    }
}

class CustomPointerAnalysis {
    private Map<Local, Set<RefType>> pointsTo = new HashMap<>();
    private Queue<SootMethod> worklist = new LinkedList<>();
    private Set<SootMethod> inWorklist = new HashSet<>();

    public void runAnalysis() {
        SootMethod entry = Scene.v().getMainMethod();
        addToWorklist(entry);

        while (!worklist.isEmpty()) {
            SootMethod currentMethod = worklist.poll();
            inWorklist.remove(currentMethod);
            
            if (!currentMethod.hasActiveBody()) continue;
            processMethod(currentMethod);
        }
    }

    private boolean processMethod(SootMethod method) {
        boolean changed = false;
        Body body = method.getActiveBody();

        for (Unit u : body.getUnits()) {
            if (!(u instanceof AssignStmt)) continue;
            AssignStmt assign = (AssignStmt) u;
            Value left = assign.getLeftOp();
            Value right = assign.getRightOp();

            if (left instanceof Local) {
                Local lLeft = (Local) left;

                if (right instanceof AnyNewExpr) {
                    if (right instanceof NewExpr) {
                        RefType type = ((NewExpr) right).getBaseType();
                        changed |= addType(lLeft, type);
                    }
                } else if (right instanceof Local) {
                    Local lRight = (Local) right;
                    changed |= propagate(lRight, lLeft);
                }
            }
        }
        return changed;
    }

    private boolean addType(Local local, RefType type) {
        pointsTo.putIfAbsent(local, new HashSet<>());
        return pointsTo.get(local).add(type);
    }

    private boolean propagate(Local from, Local to) {
        if (!pointsTo.containsKey(from)) return false;
        pointsTo.putIfAbsent(to, new HashSet<>());
        return pointsTo.get(to).addAll(pointsTo.get(from));
    }

    public Set<RefType> getPointsToSet(Local local) {
        return pointsTo.getOrDefault(local, Collections.emptySet());
    }

    private void addToWorklist(SootMethod m) {
        if (!inWorklist.contains(m)) {
            worklist.add(m);
            inWorklist.add(m);
        }
    }
}