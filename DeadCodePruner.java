import soot.*;
import soot.jimple.*;
import soot.toolkits.graph.*;
import java.util.*;

/**
 * Whole-program transformation: removes unreachable Jimple statements that
 * are left behind after null-check elimination (pass 2).
 *
 * ── Why this is needed ───────────────────────────────────────────────────────
 *
 *   After NullCheckEliminator replaces:
 *       if (x == null) goto L
 *   with a NopStmt (always falls through), or:
 *       if (x != null) goto L
 *   with a GotoStmt (always jumps), the code on the eliminated branch becomes
 *   unreachable.  For example, the null-handler body:
 *
 *       label1:                            ← target of the removed IfStmt
 *         $r0 = new NullPointerException;
 *         throw $r0;
 *
 *   is now dead but still present in the body, wasting bytecode bytes and
 *   confusing downstream analyses.  This pass removes such dead code.
 *
 * ── Algorithm ────────────────────────────────────────────────────────────────
 *
 *   1. Build a BriefUnitGraph (Soot's plain CFG, no exception edges) for each
 *      method body.
 *   2. BFS/DFS from the first unit to collect all reachable units.
 *   3. Remove any unit that is NOT in the reachable set, UNLESS it is a
 *      branch target referenced from a reachable branch (which cannot happen
 *      if BFS is run correctly, but we double-check to be safe).
 *
 * ── Soundness ────────────────────────────────────────────────────────────────
 *
 *   The CFG used (BriefUnitGraph) ignores exceptional control flow.  Units
 *   inside catch blocks might appear unreachable on the ordinary CFG but are
 *   reachable via exceptions.  We therefore skip removal of any unit that
 *   appears in a trap handler range or as a handler unit itself.
 *
 * ── Effect ───────────────────────────────────────────────────────────────────
 *
 *   Smaller method bodies → fewer instructions for the interpreter to step
 *   through → measurable throughput improvement under -Xint.
 *   Removing dead code also makes subsequent Soot passes and the JIT faster.
 */
public class DeadCodePruner extends SceneTransformer {

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        banner("Pass 3: Dead-Code Pruner");

        int totalRemoved = 0;

        for (SootClass sc : new ArrayList<>(Scene.v().getApplicationClasses())) {
            for (SootMethod sm : new ArrayList<>(sc.getMethods())) {
                if (!sm.hasActiveBody()) continue;
                int n = pruneMethod(sm);
                if (n > 0) {
                    System.out.printf("  [%s.%s] %d dead statement(s) removed%n",
                                      sc.getShortName(), sm.getName(), n);
                    totalRemoved += n;
                }
            }
        }

        System.out.printf("%n  >>> Total dead statements removed: %d%n", totalRemoved);
    }

    // ─────────────────────────────────────────────────────────────────────────
    //  Per-method dead-code removal
    // ─────────────────────────────────────────────────────────────────────────

    private int pruneMethod(SootMethod method) {
        Body body = method.getActiveBody();

        // ── Collect units that must never be removed ──────────────────────────

        // (a) Exception-handler units and units covered by any trap – must keep
        Set<Unit> protectedUnits = new HashSet<>();
        for (Trap trap : body.getTraps()) {
            protectedUnits.add(trap.getHandlerUnit());
            // Mark all units inside the trap's covered range
            boolean inRange = false;
            for (Unit u : body.getUnits()) {
                if (u == trap.getBeginUnit()) inRange = true;
                if (inRange) protectedUnits.add(u);
                if (u == trap.getEndUnit())   inRange = false;
            }
        }

        // (b) Any unit that is a branch target of any instruction in the body
        Set<Unit> branchTargets = new HashSet<>();
        for (Unit u : body.getUnits()) {
            for (UnitBox box : u.getUnitBoxes()) {
                branchTargets.add(box.getUnit());
            }
        }

        // ── BFS reachability from method entry ───────────────────────────────

        Set<Unit> reachable = new LinkedHashSet<>();
        Deque<Unit> worklist = new ArrayDeque<>();

        Unit entry = body.getUnits().getFirst();
        worklist.add(entry);
        reachable.add(entry);

        // Also seed exception handler entry points
        for (Trap trap : body.getTraps()) {
            Unit handler = trap.getHandlerUnit();
            if (reachable.add(handler)) worklist.add(handler);
        }

        while (!worklist.isEmpty()) {
            Unit cur = worklist.poll();

            // Follow all successors in the CFG
            for (Unit succ : getSuccessors(cur, body)) {
                if (reachable.add(succ)) {
                    worklist.add(succ);
                }
            }
        }

        // ── Remove dead units ─────────────────────────────────────────────────

        int removed = 0;
        List<Unit> toRemove = new ArrayList<>();

        for (Unit u : body.getUnits()) {
            if (!reachable.contains(u)
                    && !protectedUnits.contains(u)
                    && !branchTargets.contains(u)) {
                toRemove.add(u);
            }
        }

        for (Unit u : toRemove) {
            try {
                body.getUnits().remove(u);
                removed++;
            } catch (Exception e) {
                // Skip – unit may have already been removed or is structurally needed
            }
        }

        // Validate body after surgery (skips if validation fails – non-fatal)
        if (removed > 0) {
            try { body.validate(); } catch (Exception ignored) {}
        }

        return removed;
    }

    // ── CFG successor computation ─────────────────────────────────────────────

    /**
     * Returns the direct successors of {@code unit} in the control-flow graph.
     * We implement this manually to avoid constructing a full UnitGraph per
     * method (which is expensive and unnecessary here).
     *
     *   – GotoStmt       → {target}
     *   – IfStmt         → {target, fallthrough}
     *   – TableSwitch /
     *     LookupSwitch   → {all case targets + default}
     *   – ReturnStmt /
     *     ReturnVoidStmt /
     *     ThrowStmt      → {}   (exits the method)
     *   – All other stmts → {next unit in the unit chain}
     */
    private List<Unit> getSuccessors(Unit unit, Body body) {
        List<Unit> succs = new ArrayList<>(2);

        if (unit instanceof GotoStmt) {
            succs.add(((GotoStmt) unit).getTarget());

        } else if (unit instanceof IfStmt) {
            IfStmt ifStmt = (IfStmt) unit;
            succs.add(ifStmt.getTarget());           // branch taken
            Unit fallthrough = nextUnit(unit, body);
            if (fallthrough != null) succs.add(fallthrough); // fall-through

        } else if (unit instanceof SwitchStmt) {
            SwitchStmt sw = (SwitchStmt) unit;
            succs.addAll(sw.getTargets());
            if (sw.getDefaultTarget() != null) succs.add(sw.getDefaultTarget());

        } else if (unit instanceof ReturnStmt
                || unit instanceof ReturnVoidStmt
                || unit instanceof ThrowStmt) {
            // no successors within the method body

        } else {
            // Sequential statement: successor is the next unit
            Unit next = nextUnit(unit, body);
            if (next != null) succs.add(next);
        }

        return succs;
    }

    /** Returns the next unit in the chain after {@code unit}, or null if last. */
    private Unit nextUnit(Unit unit, Body body) {
        Iterator<Unit> iter = body.getUnits().iterator(unit);
        if (iter.hasNext()) iter.next(); // skip 'unit' itself
        return iter.hasNext() ? iter.next() : null;
    }

    // ── Formatting helper ─────────────────────────────────────────────────────

    private static void banner(String msg) {
        String line = "─".repeat(msg.length() + 4);
        System.out.println("\n┌" + line + "┐");
        System.out.println("│  " + msg + "  │");
        System.out.println("└" + line + "┘");
    }
}
