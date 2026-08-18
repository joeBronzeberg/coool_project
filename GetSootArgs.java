public class GetSootArgs {
	public String[] getDaCapoArgs(String outDir) {
		String cp = outDir + ":" + "dacapo-9.12-MR1-bach.jar";
		String refl_log = "reflection-log:" + outDir + "/refl.log";
		String[] sootArgs = {
				"-whole-program",
				"-app",
				"-allow-phantom-refs",
				"-no-bodies-for-excluded",
				"-soot-classpath", cp,
				"-prepend-classpath",
				"-keep-line-number",
				"-main-class", "Harness",
				"-process-dir", outDir,
				"-p", "cg.spark", "on",
				"-p", "cg", refl_log,
				"-f", "n",
				"-ire",
				"-i", "org.apache.*",
				"-i", "org.dacapo.*",
				"-i", "jdt.*",
				"-i", "jdk.*",
				"-i", "java.*",
				"-i", "org.*",
				"-i", "com.*",
				// "-i", "sun.*",
				// "-i", "javax.*",
		};
		// Colors
		final String FLAG = "\033[1;33m";  // bright cyan
		final String VALUE = "\033[1;32m"; // light gray
		final String RESET = "\033[0m";

		StringBuilder sb = new StringBuilder();
		
		System.out.println("Soot Arguments are : \t ");
		for (int i = 0; i < sootArgs.length; i++) {
			String arg = sootArgs[i];

			if (arg.startsWith("-")) {
				sb.append(FLAG).append(arg).append(RESET).append("  ");
			} else {
				sb.append(VALUE).append(arg).append(RESET).append("  ");
			}
		}

		System.out.println("["+ sb.toString() + "]");
		return sootArgs;
	}
}
