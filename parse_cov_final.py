with open('cov_summary_base.txt') as f:
    for line in f:
        if "semantic/const_eval.rs" in line:
            base_line = line.strip()
with open('cov_summary_final.txt') as f:
    for line in f:
        if "semantic/const_eval.rs" in line:
            new_line = line.strip()

print("Base: ", base_line)
print("New:  ", new_line)
