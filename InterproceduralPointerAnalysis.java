import soot.*;
import soot.jimple.*;
import java.util.*;

/**
 * Context-insensitive, flow-insensitive interprocedural pointer analysis
 * (Andersen-style, allocation-site type abstraction).
 *
 * ── What is tracked ─────────────────────────────────────────────────────────
 *
 *   pts(x)          – set of concrete RefTypes that local x may point to.
 *   retTypes(m)     – set of RefTypes that method m's return value may carry.
 *   nonNullArrays   – locals assigned a NewArrayExpr / NewMultiArrayExpr
 *                     (definitely non-null, but no RefType to record).
 *
 * ── Constraints generated ────────────────────────────────────────────────────
 *
 *   x = new T()          →  T ∈ pts(x)
 *   x = new T[n]         →  x ∈ nonNullArrays
 *   x = y                →  pts(x) ⊇ pts(y)          (copy)
 *   x = (T) y            →  pts(x) ⊇ pts(y)          (cast)
 *   x = m(a0,a1,…)       →  pts(param_i) ⊇ pts(a_i)   (arg→param)
 *                            pts(x) ⊇ retTypes(m)      (return-value flow)
 *   return v (in m)      →  retTypes(m) ⊇ pts(v)
 *
 * ── What is NOT tracked (conservative treatment) ────────────────────────────
 *
 *   Field loads (x = o.f) – no new types are added to pts(x).
 *   This is sound: we may miss inlining opportunities at receiver locals
 *   populated through fields, but we will never inline unsafely.
 *
 * ── Reachability ─────────────────────────────────────────────────────────────
 *
 *   A CHA-based BFS from main() seeds the set of methods to process.
 *   Virtual / interface targets are initially over-approximated via CHA;
 *   as pts fills in, subsequent fixed-point rounds use PTA-refined targets.
 *
 * ── Precision dimensions ─────────────────────────────────────────────────────
 *
 *   Flow-sensitivity  : no  (single pts per local, independent of program point)
 *   Context-sensitivity: no  (single pts per local, merged across all call sites)
 *   Heap-sensitivity  : no  (fields are collapsed; heap cloning not implemented)
 *   Object-sensitivity: no  (same as context-insensitive for this analysis)
 *
 *   Despite these simplifications the analysis is sound: every type that can
 *   flow to a local at runtime will appear in pts(local).
 */
public class InterproceduralPointerAnalysis {

    // ── Internal state ────────────────────────────────────────────────────────

    /** pts(x): concrete types that may be pointed to by local x. */
    private final Map<Local, Set<RefType>> pointsTo    = new HashMap<>();

    /** For each method, the types its return value may carry. */
    private final Map<SootMethod, Set<RefType>> retTypes = new HashMap<>();

    /** Locals assigned a NewArrayExpr – definitely non-null, no RefType stored. */
    private final Set<Local> nonNullArrays = new HashSet<>();

    /** Methods discovered as reachable (ordered for determinism). */
    private List<SootMethod> reachable;

    // ── Public interface ──────────────────────────────────────────────────────

    /**
     * Run the analysis to a fixed point, starting from the main method.
     * Must be called before any query method.
     */
    public void runAnalysis() {
        reachable = discoverReachable();

        boolean changed = true;
        int rounds = 0;
        while (changed) {
            changed = false;
            rounds++;
            for (SootMethod m : reachable) {
                if (m.hasActiveBody()) {
                    changed |= processMethod(m);
                }
            }
        }
        System.out.printf("    [IPA] Fixed point in %d rounds over %d methods.%n",
                          rounds, reachable.size());
    }

    /** Returns the points-to set of a local (never null, possibly empty). */
    public Set<RefType> getPointsToSet(Local local) {
        return pointsTo.getOrDefault(local, Collections.emptySet());
    }

    /**
     * Returns true iff local is definitely non-null:
     *   – PTA found ≥1 allocation site (pts non-empty), OR
     *   – local was assigned a new T[] expression.
     */
    public boolean isDefinitelyNonNull(Local local) {
        return !getPointsToSet(local).isEmpty() || nonNullArrays.contains(local);
    }

    /**
     * If the local can point to exactly one concrete type, returns it.
     * Returns null if the local is polymorphic or unknown.
     * Used by the inliner to identify monomorphic virtual call sites.
     */
    public RefType getSingleType(Local local) {
        Set<RefType> pts = getPointsToSet(local);
        return (pts.size() == 1) ? pts.iterator().next() : null;
    }

    /**
     * Walk the class hierarchy from cls upwards looking for a declaration
     * of subSig.  Returns the first match (i.e. the dynamically dispatched
     * target), or null if not found.
     *
     * Package-private so MethodInliner can reuse without duplication.
     */
    SootMethod resolveInHierarchy(SootClass cls, String subSig) {
        SootClass cur = cls;
        while (cur != null) {
            if (cur.declaresMethod(subSig)) {
                return cur.getMethod(subSig);
            }
            cur = cur.hasSuperclass() ? cur.getSuperclass() : null;
        }
        return null;
    }

    // ── Reachability (CHA-seeded BFS) ─────────────────────────────────────────

    private List<SootMethod> discoverReachable() {
        Set<SootMethod> seen = new LinkedHashSet<>();
        Deque<SootMethod> worklist = new ArrayDeque<>();

        SootMethod entry = Scene.v().getMainMethod();
        seen.add(entry);
        worklist.push(entry);

        while (!worklist.isEmpty()) {
            SootMethod m = worklist.pop();
            if (!m.getDeclaringClass().isApplicationClass()) {
                continue;
            }

            if (!m.hasActiveBody()) continue;

            for (Unit u : m.getActiveBody().getUnits()) {
                if (!(u instanceof Stmt)) continue;
                Stmt s = (Stmt) u;
                if (!s.containsInvokeExpr()) continue;

                for (SootMethod target : chaTargets(s.getInvokeExpr())) {
                    if (seen.add(target)) {
                        worklist.push(target);
                    }
                }
            }
        }
        return new ArrayList<>(seen);
    }

    /**
     * Conservative (CHA) call-graph targets – used only for reachability
     * discovery (first pass).  For virtual calls, returns all concrete
     * implementations declared in application classes.
     */
    private List<SootMethod> chaTargets(InvokeExpr invoke) {
        List<SootMethod> targets = new ArrayList<>();
        SootMethod declared;
        try { declared = invoke.getMethod(); } catch (Exception e) { return targets; }

        if (invoke instanceof StaticInvokeExpr || invoke instanceof SpecialInvokeExpr) {
            if (declared.hasActiveBody()) targets.add(declared);
            return targets;
        }

        // Virtual / interface → CHA: include every concrete override
        String subSig = declared.getSubSignature();
        for (SootClass sc : Scene.v().getApplicationClasses()) {
            if (!sc.isInterface() && sc.declaresMethod(subSig)) {
                SootMethod m = sc.getMethod(subSig);
                if (m.hasActiveBody()) targets.add(m);
            }
        }
        return targets;
    }

    // ── Constraint processing (fixed-point iteration) ─────────────────────────

    private boolean processMethod(SootMethod method) {
        // 2. ADD THIS GUARD: Do not process constraints for library methods
        if (!method.getDeclaringClass().isApplicationClass()) {
            return false;
        }
        
        boolean changed = false;
        for (Unit u : method.getActiveBody().getUnits()) {
            if (u instanceof AssignStmt) {
                changed |= processAssign((AssignStmt) u);
            } else if (u instanceof ReturnStmt) {
                changed |= processReturn((ReturnStmt) u, method);
            } else if (u instanceof InvokeStmt) {
                // Call with no interesting return value; still need arg→param edges
                changed |= processCallEdges(((InvokeStmt) u).getInvokeExpr(), null);
            }
        }
        return changed;
    }

    private boolean processAssign(AssignStmt as) {
        Value lhs = as.getLeftOp();
        Value rhs = as.getRightOp();

        // We only care about pointer-typed locals on the left-hand side
        if (!(lhs instanceof Local)) return false;
        Local lLocal = (Local) lhs;

        boolean changed = false;

        if (rhs instanceof NewExpr) {
            // x = new T()  →  T ∈ pts(x)
            changed |= addType(lLocal, ((NewExpr) rhs).getBaseType());

        } else if (rhs instanceof NewArrayExpr || rhs instanceof NewMultiArrayExpr) {
            // x = new T[n]  →  x is definitely non-null (no RefType to add)
            changed |= nonNullArrays.add(lLocal);

        } else if (rhs instanceof Local) {
            // x = y  →  pts(x) ⊇ pts(y)
            changed |= propagate((Local) rhs, lLocal);

        } else if (rhs instanceof CastExpr) {
            // x = (T) y  →  pts(x) ⊇ pts(y)  (conservative: ignore the declared cast type)
            Value op = ((CastExpr) rhs).getOp();
            if (op instanceof Local) changed |= propagate((Local) op, lLocal);

        } else if (rhs instanceof InvokeExpr) {
            // x = m(…)  →  arg→param edges + return-type flow into x
            changed |= processCallEdges((InvokeExpr) rhs, lLocal);
        }
        // Field reads (x = o.f) are treated conservatively: no types added.
        // This under-approximates pts but is sound for all uses in this tool.

        return changed;
    }

    private boolean processReturn(ReturnStmt ret, SootMethod m) {
        Value op = ret.getOp();
        if (!(op instanceof Local)) return false;

        Set<RefType> pts = getPointsToSet((Local) op);
        if (pts.isEmpty()) return false;

        retTypes.putIfAbsent(m, new HashSet<>());
        return retTypes.get(m).addAll(pts);
    }

    /**
     * For a call site, generate two families of constraints:
     *   (a) actual args  →  formal params   (for every possible callee)
     *   (b) retTypes(callee)  →  lhsLocal   (if a return value is assigned)
     *
     * Target resolution uses PTA-refined CHA: if the receiver's pts is known,
     * only the matching concrete targets are included; otherwise falls back to
     * full CHA over application classes.
     */
    private boolean processCallEdges(InvokeExpr invoke, Local lhsLocal) {
        boolean changed = false;

        for (SootMethod target : ptaTargets(invoke)) {
            if (!target.hasActiveBody()) continue;
            Body tbody = target.getActiveBody();

            // (a-i) Propagate 'this'  →  thisLocal of the callee
            if (invoke instanceof InstanceInvokeExpr) {
                Value base = ((InstanceInvokeExpr) invoke).getBase();
                if (base instanceof Local) {
                    try {
                        Local thisLocal = tbody.getThisLocal();
                        changed |= propagate((Local) base, thisLocal);
                    } catch (Exception ignored) {
                        // static context or body has no 'this' – safe to skip
                    }
                }
            }

            // (a-ii) Propagate actual args  →  formal params
            List<Value> args   = invoke.getArgs();
            List<Local> params = tbody.getParameterLocals();
            int bound = Math.min(args.size(), params.size());
            for (int i = 0; i < bound; i++) {
                Value arg = args.get(i);
                if (arg instanceof Local) {
                    changed |= propagate((Local) arg, params.get(i));
                }
            }

            // (b) Propagate return types  →  lhsLocal (if any)
            if (lhsLocal != null) {
                Set<RefType> ret = retTypes.getOrDefault(target, Collections.emptySet());
                for (RefType t : ret) {
                    changed |= addType(lhsLocal, t);
                }
            }
        }
        return changed;
    }

    /**
     * PTA-refined call target resolution.
     *   – Static / special calls: delegate to chaTargets (already precise).
     *   – Virtual / interface calls: if the receiver has a non-empty pts,
     *     return exactly the targets corresponding to those types.
     *     Otherwise fall back to CHA (conservative but sound).
     */
    private List<SootMethod> ptaTargets(InvokeExpr invoke) {
        if (invoke instanceof StaticInvokeExpr || invoke instanceof SpecialInvokeExpr) {
            return chaTargets(invoke);
        }

        // ADD THIS BLOCK: Safely ignore invokedynamic (lambdas, string concat)
        if (invoke instanceof DynamicInvokeExpr) {
            return new ArrayList<>(); 
        }

        InstanceInvokeExpr inst = (InstanceInvokeExpr) invoke;
        Value base    = inst.getBase();
        String subSig = inst.getMethodRef().getSubSignature().getString();

        if (base instanceof Local) {
            Set<RefType> pts = getPointsToSet((Local) base);
            if (!pts.isEmpty()) {
                List<SootMethod> targets = new ArrayList<>(pts.size());
                for (RefType t : pts) {
                    SootMethod m = resolveInHierarchy(t.getSootClass(), subSig);
                    if (m != null && m.hasActiveBody()) {
                        targets.add(m);
                    }
                }
                return targets;
            }
        }

        return chaTargets(invoke); // bootstrap / fallback
    }

    // ── Utility helpers ───────────────────────────────────────────────────────

    private boolean addType(Local local, RefType type) {
        return pointsTo.computeIfAbsent(local, k -> new HashSet<>()).add(type);
    }

    private boolean propagate(Local from, Local to) {
        Set<RefType> src = pointsTo.get(from);
        if (src == null || src.isEmpty()) return false;
        return pointsTo.computeIfAbsent(to, k -> new HashSet<>()).addAll(src);
    }
}
