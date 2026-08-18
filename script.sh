#!/bin/bash
set -e 

CP_SEP=":"

# Add src to the classpath so Java can find Main after compilation
SOOT_CP="soot-4.6.0-jar-with-dependencies.jar${CP_SEP}.${CP_SEP}src"

echo "Cleaning up old class files..."
rm -rf sootOutput src/*.class tests/*.class

echo "Compiling Source and Test code..."
javac -cp "$SOOT_CP" src/*.java
javac tests/*.java

echo "================================================================="
echo "       Performance Evaluation (JIT Disabled via -Xint)           "
echo "================================================================="
printf "%-12s | %-15s | %-15s | %-15s\n" "Testcase" "Original (ms)" "Optimized (ms)" "Improvement (%)"
echo "-----------------------------------------------------------------"

set +e 

for test_file in tests/Test*.java; do
    test_class=$(basename "$test_file" .java)
    
    # 1. Run Original Test
    start_orig=$(python3 -c 'import time; print(int(time.time() * 1000))')
    java -Xint -cp tests $test_class > /dev/null
    end_orig=$(python3 -c 'import time; print(int(time.time() * 1000))')
    time_orig=$((end_orig - start_orig))
    
    # 2. Run Soot Transformation (Silently)
    java -cp "$SOOT_CP" Main $test_class > /dev/null 2>&1
    
    # 3. Run Optimized Test
    start_opt=$(python3 -c 'import time; print(int(time.time() * 1000))')
    java -Xint -cp "sootOutput${CP_SEP}tests" $test_class > /dev/null
    end_opt=$(python3 -c 'import time; print(int(time.time() * 1000))')
    time_opt=$((end_opt - start_opt))
    
    # 4. Calculate Statistics
    if [ $time_orig -gt 0 ]; then
        improvement=$(echo "scale=2; (($time_orig - $time_opt) / $time_orig) * 100" | bc)
    else
        improvement="0.00"
    fi
    
    printf "%-12s | %-15s | %-15s | %-15s\n" "$test_class" "${time_orig}" "${time_opt}" "${improvement}%"
done
echo "================================================================="