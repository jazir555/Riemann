import re

with open('door3_cells_batchB.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

new_lines = []
skip_until_norm_num = False
in_scenter_proof = False

for i, line in enumerate(lines):
    stripped = line.strip()
    
    # Check if this is an unfold line for a sCenter theorem
    if 'unfold B' in stripped and '_sCenter CellProofEngine.Rect2D.center' in stripped:
        in_scenter_proof = True
        new_lines.append(line)
        new_lines.append(line.replace('unfold', '    norm_num', 1).replace('    norm_num', '    norm_num\n', 1))
        # Actually, let me just add norm_num on the next line
        new_lines.pop()  # Remove the bad line
        new_lines.append(line)
        new_lines.append('    norm_num\n')
        skip_until_norm_num = True
        continue
    
    if skip_until_norm_num:
        # Skip until we find norm_num
        if 'norm_num' in stripped and not stripped.startswith('--'):
            skip_until_norm_num = False
            in_scenter_proof = False
        continue
    
    new_lines.append(line)

with open('door3_cells_batchB.lean', 'w', encoding='utf-8') as f:
    f.writelines(new_lines)
print('Fixed sCenter proofs')
