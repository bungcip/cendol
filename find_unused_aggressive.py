import subprocess
import os
import re

def get_all_functions():
    functions = []
    output = subprocess.check_output(['grep', '-r', 'fn ', 'src/']).decode('utf-8')
    for line in output.splitlines():
        if 'src/tests' in line:
            continue
        # Match fn function_name
        match = re.search(r'src/([^:]+):.*fn\s+([a-zA-Z0-9_]+)', line)
        if match:
            full_path = 'src/' + match.group(1)
            func_name = match.group(2)
            functions.append((full_path, func_name))
    return functions

def count_usages(func_name, full_path):
    try:
        pattern = r'\b' + func_name + r'\b'
        output = subprocess.check_output(['grep', '-r', func_name, 'src/']).decode('utf-8')
        lines = output.splitlines()

        usages = []
        for line in lines:
            # Exclude lines that are part of the function's own definition
            if 'fn ' + func_name in line and full_path in line:
                continue
            # Exclude comments
            content = line.split(':', 1)[1] if ':' in line else line
            if content.strip().startswith('//') or content.strip().startswith('/*'):
                 continue
            # Exclude doc comments
            if content.strip().startswith('///'):
                 continue

            usages.append(line)
        return len(usages)
    except subprocess.CalledProcessError:
        return 0

functions = get_all_functions()
for full_path, func_name in functions:
    if func_name in ['new', 'default', 'fmt', 'from', 'into', 'as_str', 'len', 'is_empty', 'id', 'span', 'main']:
        continue
    count = count_usages(func_name, full_path)
    if count == 0:
        print(f"STRICTLY UNUSED: {full_path}: {func_name}")
