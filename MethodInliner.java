import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.invoke.SiteInliner;
import java.util.*;

/**
 * Whole-program transformation: iterative method inlining guided by
 * interprocedural pointer analysis (IPA).
 *
 * ── Algorithm ────────────────────────────────────────────────────────────────
 *
 *   Repeat until no more inlining is possible (or MAX_ITERATIONS reached):
 *     1. Run a fresh IPA on the current state of all method bodies.
 *     2. For every application method (caller), attempt to inline each
 *        call site in its body:
 *          – Static calls       → exactly one target, inline directly.
 *          – Special calls      → non-constructor specials inlined directly.
 *          – Virtual / interface calls → inline only when PTA reports
 *            exactly one concrete type for the receiver (monomorphic site).
 *        After modifying the unit list of a method, restart the scan of
 *        that method from the top (the unit list has changed).
 *     3. If at least one site was inlined in this iteration, go to step 1.
 *        (Fresh IPA may reveal new monomorphic sites in the newly merged code.)
 *
 * ── Why iterating helps ──────────────────────────────────────────────────────
 *
 *   Inlining brings callee code into the caller.  That code may contain
 *   allocation sites (new T()) that were previously invisible to the caller's
 *   IPA.  In the next IPA round, those types flow to locals inside the now-
 *   expanded caller, potentially making previously polymorphic call sites
 *   monomorphic.  Example:
 *
 *     Before round 1:  main()  calls  factory.create()  – polymorphic
 *     Round 1 inlines: factory.create() body, revealing  x = new ConcreteA()
 *     IPA round 2:     pts(x) = {ConcreteA}  →  x.execute() is now monomorphic
 *     Round 2 inlines: ConcreteA.execute() as well
 *
 * ── Soundness conditions ─────────────────────────────────────────────────────
 *
 *   A virtual call site is inlined only when PTA certifies pts(receiver) = {T}
 *   (exactly one type).  Because Andersen-style PTA over-approximates,
 *   if the set has size 1 the actual runtime type MUST be T – inlining is safe.
 *
 *   Additional guards (isSafeToInline):
 *     • Target must have an active body (not abstract / interface stub).
 *     • Target must not be native.
 *     • Constructors and static initialisers are never inlined.
 *     • A method is never inlined into itself (direct recursion guard).
 *     • Methods larger than MAX_BODY_SIZE Jimple units are skipped (heuristic:
 *       inlining very large methods bloats the caller and may hurt icache).
 *
 * ── Limitations ──────────────────────────────────────────────────────────────
 *
 *   Mutual recursion is not detected; if A calls B and B calls A, the guard
 *   stops direct self-inlining but not the mutual case.  In practice Soot's
 *   SiteInliner will refuse to inline recursive call graphs gracefully.
 *
 *   Fields are not modelled by IPA, so factory patterns that return objects
 *   stored in fields may not benefit from virtual inlining (the receiver local
 *   loaded from a field will have an empty pts).
 */
public class MethodInliner extends SceneTransformer {

    // ── Tuning constants ──────────────────────────────────────────────────────

    /** Max body size (Jimple units) of a method eligible for inlining. */
    private static final int MAX_BODY_SIZE  = 80;

    /** Hard cap on outer IPA-reanalysis iterations (safety against loops). */
    private static final int MAX_ITERATIONS = 30;

    // ── Entry point ───────────────────────────────────────────────────────────

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        // banner("Pass 1: IPA-Guided Method Inliner");

        int totalInlined = 0;

        for (int iter = 1; iter <= MAX_ITERATIONS; iter++) {
            System.out.printf("%n  [Iter %2d] Running IPA…%n", iter);

            InterproceduralPointerAnalysis ipa = new InterproceduralPointerAnalysis();
            ipa.runAnalysis();

            int inlinedThisIter = 0;
            for (SootClass sc : new ArrayList<>(Scene.v().getApplicationClasses())) {
                for (SootMethod caller : new ArrayList<>(sc.getMethods())) {
                    if (!caller.hasActiveBody()) continue;
                    int n = inlineAllInMethod(caller, ipa);
                    inlinedThisIter += n;
                    totalInlined    += n;
                }
            }

            System.out.printf("  [Iter %2d] Inlined %d site(s).%n", iter, inlinedThisIter);
            if (inlinedThisIter == 0) {
                System.out.println("  Fixed point reached.");
                break;
            }
        }

        System.out.printf("%n  >>> Total sites inlined: %d%n", totalInlined);
    }

    // ── Per-method inlining loop ──────────────────────────────────────────────

    /**
     * Greedily inline all eligible call sites within {@code caller}.
     * After each successful inlining the unit list is stale, so we restart
     * the scan from the top of the method.
     *
     * @return number of sites inlined within this method in this call.
     */
    private int inlineAllInMethod(SootMethod caller,
                                  InterproceduralPointerAnalysis ipa) {
        int count    = 0;
        boolean more = true;

        while (more) {
            more = false;

            // Snapshot unit list: SiteInliner modifies body.getUnits() in place
            List<Unit> snapshot =
                new ArrayList<>(caller.getActiveBody().getUnits());

            for (Unit u : snapshot) {
                if (!(u instanceof Stmt)) continue;
                Stmt stmt = (Stmt) u;
                if (!stmt.containsInvokeExpr()) continue;

                InvokeExpr invoke = stmt.getInvokeExpr();
                SootMethod target = resolveUniqueTarget(invoke, ipa);

                if (target != null && isSafeToInline(target, caller)) {
                    try {
                        SiteInliner.inlineSite(target, stmt, caller);
                        System.out.printf("    ✓ [%-9s] %s.%s  ←  %s%n",
                            kindOf(invoke),
                            target.getDeclaringClass().getShortName(),
                            target.getName(),
                            caller.getName());
                        count++;
                        more = true;
                        break; // restart: unit list has changed
                    } catch (Exception e) {
                        // System.err.printf("    ✗ Could not inline %s: %s%n",
                        //                   target.getName(), e.getMessage());
                        // continue trying other sites
                    }
                }
            }
        }
        return count;
    }

    // ── Target resolution ─────────────────────────────────────────────────────

    /**
     * Return the single concrete callee if it can be determined uniquely,
     * or null when the site is polymorphic / unresolvable.
     *
     *   Static / Special → always uniquely resolved by the declared target.
     *   Virtual / Interface → resolved via PTA; require pts.size() == 1.
     */
    private SootMethod resolveUniqueTarget(InvokeExpr invoke,
                                           InterproceduralPointerAnalysis ipa) {
        // ── Static call: single declared target ──────────────────────────────
        if (invoke instanceof StaticInvokeExpr) {
            return safeGetMethod(invoke);
        }

        // ── Special call (super / private / constructor) ──────────────────────
        // Constructors are filtered out downstream by isSafeToInline.
        if (invoke instanceof SpecialInvokeExpr) {
            return safeGetMethod(invoke);
        }

        // ── Virtual / interface call: PTA-guided devirtualization ─────────────
        if (invoke instanceof InstanceInvokeExpr) {
            InstanceInvokeExpr inst = (InstanceInvokeExpr) invoke;

            // Constructors are called via SpecialInvoke in bytecode, but guard
            // against <init> appearing via VirtualInvoke just in case.
            if ("<init>".equals(inst.getMethodRef().name())) return null;

            Value base = inst.getBase();
            if (!(base instanceof Local)) return null;

            // PTA must show exactly one concrete type for the receiver
            RefType single = ipa.getSingleType((Local) base);
            if (single == null) return null; // polymorphic – cannot inline safely

            // Resolve the actual dispatched method in the concrete class hierarchy
            return ipa.resolveInHierarchy(
                single.getSootClass(),
                inst.getMethodRef().getSubSignature().getString());
        }

        return null;
    }

    private SootMethod safeGetMethod(InvokeExpr invoke) {
        try { return invoke.getMethod(); } catch (Exception e) { return null; }
    }

    // ── Safety predicates ─────────────────────────────────────────────────────

    // ── Safety predicates ─────────────────────────────────────────────────────

    private boolean isSafeToInline(SootMethod target, SootMethod caller) {
        if (target == null)                                        return false;
        // Must have a Jimple body to inline
        if (!target.hasActiveBody())                               return false;
        // JNI methods cannot be inlined
        if (target.isNative())                                     return false;
        // Constructors – SiteInliner cannot reliably inline them
        if (target.isConstructor())                                return false;
        // Static initialisers – must not be inlined
        if ("<clinit>".equals(target.getName()))                   return false;
        // Self-inlining would produce infinite expansion
        if (target.getSignature().equals(caller.getSignature()))   return false;
        // Size heuristic: avoid bloating the caller
        if (target.getActiveBody().getUnits().size() > MAX_BODY_SIZE) return false;
        
        // --- CRITICAL FIX: Soundness check for JVM access rules ---
        if (!hasValidAccess(target, caller))                       return false;

        return true;
    }

    /**
     * Checks if moving the target method's instructions into the caller's class
     * would violate JVM access modifiers (private, protected, package-private).
     */
    private boolean hasValidAccess(SootMethod target, SootMethod caller) {
        SootClass callerClass = caller.getDeclaringClass();
        SootClass targetClass = target.getDeclaringClass();

        // If they are in the same class, access is always safe.
        if (callerClass.equals(targetClass)) {
            return true;
        }

        // Check if the caller can even see the target's class
        if (!isClassVisible(targetClass, callerClass)) {
            return false;
        }

        // Scan the callee's body to ensure every field read/write and 
        // method call is legally accessible from the caller's class.
        for (Unit u : target.getActiveBody().getUnits()) {
            Stmt stmt = (Stmt) u;
            
            if (stmt.containsFieldRef()) {
                SootField field = stmt.getFieldRef().getField();
                if (!isFieldVisible(field, callerClass)) return false;
            }
            
            if (stmt.containsInvokeExpr()) {
                SootMethod method = stmt.getInvokeExpr().getMethod();
                if (!isMethodVisible(method, callerClass)) return false;
            }
        }
        return true;
    }

    private boolean isClassVisible(SootClass targetClass, SootClass callerClass) {
        if (targetClass.isPublic()) return true;
        // Package-private class
        return targetClass.getPackageName().equals(callerClass.getPackageName());
    }

    private boolean isFieldVisible(SootField field, SootClass callerClass) {
        if (field.isPublic()) return true;
        
        SootClass declaringClass = field.getDeclaringClass();
        if (declaringClass.equals(callerClass)) return true;
        
        if (field.isPrivate()) return false;
        
        // Package-private or protected (conservative check)
        String memberPkg = declaringClass.getPackageName();
        String callerPkg = callerClass.getPackageName();
        if (memberPkg.equals(callerPkg)) return true;
        
        if (field.isProtected()) {
            return isSubclass(callerClass, declaringClass);
        }
        return false;
    }

    private boolean isMethodVisible(SootMethod method, SootClass callerClass) {
        if (method.isPublic()) return true;
        
        SootClass declaringClass = method.getDeclaringClass();
        if (declaringClass.equals(callerClass)) return true;
        
        if (method.isPrivate()) return false;
        
        // Package-private or protected (conservative check)
        String memberPkg = declaringClass.getPackageName();
        String callerPkg = callerClass.getPackageName();
        if (memberPkg.equals(callerPkg)) return true;
        
        if (method.isProtected()) {
            return isSubclass(callerClass, declaringClass);
        }
        return false;
    }

    private boolean isSubclass(SootClass child, SootClass parent) {
        SootClass current = child;
        while (current.hasSuperclass()) {
            current = current.getSuperclass();
            if (current.equals(parent)) return true;
        }
        return false;
    }

    // ── Formatting helpers ────────────────────────────────────────────────────

    private static String kindOf(InvokeExpr invoke) {
        if (invoke instanceof StaticInvokeExpr)    return "Static";
        if (invoke instanceof SpecialInvokeExpr)   return "Special";
        if (invoke instanceof InterfaceInvokeExpr) return "Interface";
        return "Virtual";
    }

    private static void banner(String msg) {
        String line = "─".repeat(msg.length() + 4);
        System.out.println("\n┌" + line + "┐");
        System.out.println("│  " + msg + "  │");
        System.out.println("└" + line + "┘");
    }
}
