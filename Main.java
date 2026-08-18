import soot.*;
import soot.options.Options;
import java.util.*;

/**
 * PA4 – IPA-Guided Method Inlining + Null-Check Elimination + Dead-Code Pruning
 *
 * Usage:
 * java -cp soot-4.x.x.jar:. Main <soot-classpath> <main-class> [output-dir]
 */
public class Main {

    public static void main(String[] args) {
        if (args.length < 2) {
            System.err.println(
                "Usage: java Main <soot-classpath> <main-class> [output-dir]");
            System.exit(1);
        }

        String sootCp  = args[0];
        String mainCls = args[1];
        String outDir  = args.length > 2 ? args[2] : "sootOutput";

        configureSoot(sootCp, mainCls, outDir);
        registerPasses();

        Scene.v().loadNecessaryClasses();
        PackManager.v().runPacks();
        // CRITICAL FIX: Tell Soot to actually write the modified classes to the disk
        PackManager.v().writeOutput();
    }

    // ─────────────────────────────────────────────────────────────────────────
    //  Soot configuration
    // ─────────────────────────────────────────────────────────────────────────

    private static void configureSoot(String sootCp, String mainCls, String outDir) {
        Options opt = Options.v();

        // Classpath & output
        opt.set_prepend_classpath(true);
        opt.set_allow_phantom_refs(true);
        
        // REVERTED: No longer splitting the string. 
        // Passes the single argument directly.
        opt.set_process_dir(Arrays.asList(sootCp));
        opt.set_soot_classpath(sootCp);
        
        opt.set_output_format(Options.output_format_class);
        opt.set_output_dir(outDir);

        // Whole-program mode (required for wjtp passes)
        opt.set_whole_program(true);
        opt.set_app(true);

        // Entry point
        opt.set_main_class(mainCls);
        opt.classes().add(mainCls);

        // Keep line numbers for debugging
        opt.set_keep_line_number(true);

        // ── Ignore Library Classes ───────────────────────────────────────────
        // Prevent Soot from analyzing the bodies of standard Java libraries
        opt.set_no_bodies_for_excluded(true);
        opt.set_exclude(Arrays.asList(
            "java.*", 
            "javax.*", 
            "sun.*", 
            "jdk.*"
        ));
        // ─────────────────────────────────────────────────────────────────────

        // ── Disable Soot's own analysis/optimization passes ──────────────────
        // We run our own IPA; Soot's CG / WJO would interfere and slow things.
        opt.setPhaseOption("cg",   "enabled:false");
        opt.setPhaseOption("wjop", "enabled:false");
        opt.setPhaseOption("wjap", "enabled:false");

        // Keep original variable names where possible
        opt.setPhaseOption("jb.dae", "enabled:false");
    }

    // ─────────────────────────────────────────────────────────────────────────
    //  Pass registration (order matters – runs top-to-bottom in wjtp)
    // ─────────────────────────────────────────────────────────────────────────

    private static void registerPasses() {
        Pack wjtp = PackManager.v().getPack("wjtp");

        // Pass 1 – IPA-guided method inlining
        wjtp.add(new Transform("wjtp.inliner",   new MethodInliner()));

        // Pass 2 – null-check elimination
        wjtp.add(new Transform("wjtp.nullcheck", new NullCheckEliminator()));

        // Pass 3 – dead-code pruner
        wjtp.add(new Transform("wjtp.deadcode",  new DeadCodePruner()));
    }
}