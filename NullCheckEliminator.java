import soot.*;
import soot.jimple.*;
import java.util.*;

/**
 * Whole-program transformation: eliminates redundant null checks using
 * interprocedural pointer analysis (IPA) results.
 *
 * ── Motivation ───────────────────────────────────────────────────────────────
 *
 *   After method inlining, callee bodies are merged into callers.  Many
 *   callees contain defensive null checks on their parameters or on factory
 *   return values:
 *
 *       if (op == null) throw new IllegalArgumentException(…);
 *
 *   If IPA shows that 'op' was allocated in the same method (or in a callee
 *   that was already inlined), it is guaranteed non-null and the check can be
 *   removed.  This has a compounding effect: each eliminated check is one
 *   fewer conditional branch the interpreter / JIT must evaluate.
 *
 * ── Patterns recognised ──────────────────────────────────────────────────────
 *
 *   (A)  if (x == null) goto L   ← condition is always false when x ≠ null
 *        → replaced with a NopStmt (fall-through behaviour preserved)
 *
 *   (B)  if (x != null) goto L   ← condition is always true when x ≠ null
 *        → replaced with an unconditional  goto L
 *
 *   In both cases the code that was guarded by the null branch becomes
 *   unreachable.  DeadCodePruner (pass 3) removes it.
 *
 * ── Soundness ────────────────────────────────────────────────────────────────
 *
 *   A check is eliminated only when IPA has positively proved non-nullness:
 *     • pts(x) is non-empty (≥1 allocation site flows to x), OR
 *     • x was assigned a new T[] expression (array allocations never return null).
 *
 *   IPA over-approximates pts, so the non-nullness proof is conservative:
 *   if we claim x is non-null, it truly is at every program point (because
 *   every object in a sound over-approximation of pts was indeed allocated
 *   at some point, and allocations never produce null in Java).
 *
 *   Cases we conservatively leave alone (pts(x) is empty):
 *     • x comes from a field load  (fields not modelled by IPA)
 *     • x is a formal parameter with no tracked allocation site
 *     • x originates outside the application (e.g. library return value)
 *
 * ── Why a fresh IPA is run here ──────────────────────────────────────────────
 *
 *   Pass 1 (MethodInliner) ran IPA multiple times but the last run was on
 *   the pre-inlining code.  After all inlining is complete the method bodies
 *   are structurally different; new locals have been introduced by SiteInliner
 *   (renamed to avoid conflicts).  A fresh IPA on the post-inlining code
 *   produces more accurate non-null information for these new locals.
 */
public class NullCheckEliminator extends SceneTransformer {

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        banner("Pass 2: Null-Check Eliminator");

        // Fresh IPA on the post-inlining code
        System.out.println("\n  Running post-inlining IPA…");
        InterproceduralPointerAnalysis ipa = new InterproceduralPointerAnalysis();
        ipa.runAnalysis();

        int totalElim = 0;

        for (SootClass sc : new ArrayList<>(Scene.v().getApplicationClasses())) {
            for (SootMethod sm : new ArrayList<>(sc.getMethods())) {
                if (!sm.hasActiveBody()) continue;
                int n = eliminateIn(sm, ipa);
                if (n > 0) {
                    System.out.printf("  [%s.%s] %d null check(s) eliminated%n",
                                      sc.getShortName(), sm.getName(), n);
                    totalElim += n;
                }
            }
        }

        System.out.printf("%n  >>> Total null checks eliminated: %d%n", totalElim);
    }

    // ─────────────────────────────────────────────────────────────────────────
    //  Per-method elimination
    // ─────────────────────────────────────────────────────────────────────────

    private int eliminateIn(SootMethod method, InterproceduralPointerAnalysis ipa) {
        Body body = method.getActiveBody();
        int count = 0;

        // Snapshot to avoid ConcurrentModificationException while we mutate the chain
        for (Unit u : new ArrayList<>(body.getUnits())) {
            if (!(u instanceof IfStmt)) continue;
            IfStmt ifStmt = (IfStmt) u;
            Value  cond   = ifStmt.getCondition();

            if (cond instanceof EqExpr) {
                // Pattern A: if (x == null) goto L
                //   x is definitely non-null  →  condition always false
                //   →  replace with Nop so execution always falls through
                EqExpr eq    = (EqExpr) cond;
                Local nonNull = extractNonNullLocal(eq.getOp1(), eq.getOp2(), ipa);
                if (nonNull != null) {
                    body.getUnits().swapWith(ifStmt, Jimple.v().newNopStmt());
                    count++;
                }

            } else if (cond instanceof NeExpr) {
                // Pattern B: if (x != null) goto L
                //   x is definitely non-null  →  condition always true
                //   →  replace with unconditional goto L
                NeExpr ne    = (NeExpr) cond;
                Local nonNull = extractNonNullLocal(ne.getOp1(), ne.getOp2(), ipa);
                if (nonNull != null) {
                    body.getUnits().swapWith(
                        ifStmt, Jimple.v().newGotoStmt(ifStmt.getTarget()));
                    count++;
                }
            }
        }

        return count;
    }

    /**
     * Given the two operands of an equality/inequality comparison, return the
     * Local operand if:
     *   (a) exactly one operand is a Local and the other is NullConstant, AND
     *   (b) IPA certifies that Local is definitely non-null.
     *
     * Returns null in all other cases (conservatively: check kept).
     */
    private Local extractNonNullLocal(Value op1, Value op2,
                                      InterproceduralPointerAnalysis ipa) {
        if (op1 instanceof Local && op2 instanceof NullConstant) {
            Local l = (Local) op1;
            if (ipa.isDefinitelyNonNull(l)) return l;
        }
        if (op2 instanceof Local && op1 instanceof NullConstant) {
            Local l = (Local) op2;
            if (ipa.isDefinitelyNonNull(l)) return l;
        }
        return null;
    }

    // ── Formatting helper ─────────────────────────────────────────────────────

    private static void banner(String msg) {
        String line = "─".repeat(msg.length() + 4);
        System.out.println("\n┌" + line + "┐");
        System.out.println("│  " + msg + "  │");
        System.out.println("└" + line + "┘");
    }
}
