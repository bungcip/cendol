#!/bin/bash
find src -name "*.rs" | grep -v "src/tests" | while read file; do
    grep -E "^(    )*(pub(\(crate\))? )?fn [a-zA-Z0-9_]+" "$file" | while read -r line; do
        func=$(echo "$line" | sed -E 's/.*fn ([a-zA-Z0-9_]+).*/\1/')
        if [[ "$func" == "new" || "$func" == "default" || "$func" == "fmt" || "$func" == "from" || "$func" == "into" || "$func" == "clone" || "$func" == test_* ]]; then
            continue
        fi
        count=$(grep -rw "$func" src | grep -v "fn $func" | wc -l)
        if [ "$count" -eq 0 ]; then
            echo "$file : $func : $line"
        fi
    done
done
