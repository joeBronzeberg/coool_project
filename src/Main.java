import soot.*;
import soot.options.Options;
import java.util.ArrayList;
import java.util.List;

public class Main {
    public static void main(String[] args) {
        G.reset();

        // 1. Basic Soot Setup
        Options.v().set_keep_line_number(true);
        Options.v().set_whole_program(true); 
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_output_format(Options.output_format_class); 
        
        // 2. Classpath Configuration
        Options.v().set_soot_classpath("tests"); 
        Options.v().set_prepend_classpath(true);

        // =========================================================
        // 3. PERFORMANCE OPTIMIZATION: Exclude Library Classes
        // =========================================================
        List<String> excludeList = new ArrayList<>();
        excludeList.add("java.*");
        excludeList.add("javax.*");
        excludeList.add("sun.*");
        excludeList.add("sunw.*");
        excludeList.add("com.sun.*");
        excludeList.add("com.ibm.*");
        excludeList.add("com.apple.*");
        excludeList.add("jdk.*");
        
        Options.v().set_exclude(excludeList);
        
        // CRITICAL: Do not build Jimple bodies for the excluded packages.
        // This saves massive amounts of memory and CPU time.
        Options.v().set_no_bodies_for_excluded(true);
        // =========================================================

        Options.v().setPhaseOption("jb", "use-original-names:true");

        // 4. Register the Transformer
        InterproceduralInliner inliner = new InterproceduralInliner();
        PackManager.v().getPack("wjtp").add(new Transform("wjtp.custom_inliner", inliner));

        // 5. Run Soot with the arguments passed from the bash script
        soot.Main.main(args);
    }
}