#!/bin/bash
find src -name "*.rs" | grep -v "src/tests" | while read file; do
    # Find functions with pub or pub(crate)
    grep -E "^(    )*(pub(\(crate\))? )?fn [a-zA-Z0-9_]+" "$file" | while read -r line; do
        func=$(echo "$line" | sed -E 's/.*fn ([a-zA-Z0-9_]+).*/\1/')

        # Skip common names and test functions
        if [[ "$func" == "new" || "$func" == "default" || "$func" == "fmt" || "$func" == "from" || "$func" == "into" || "$func" == "clone" || "$func" == test_* ]]; then
            continue
        fi

        # Count usages in src directory
        count=$(grep -rw "$func" src | grep -v "fn $func" | wc -l)

        if [ "$count" -eq 0 ]; then
             # Check if it's used in tests (as tests might be in separate files)
             # But here tests are also under src/
             echo "UNUSED: $file : $func : $line"
        fi
    done
done
