import re

with open('door3_cells_batchB.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# Find the start and end of the addition
start_marker = '  /-! ## Factor decomposition for all 10 cells (B11-B20)'
end_marker = 'end Door3BatchB'

start_idx = content.find(start_marker)
end_idx = content.find(end_marker)

if start_idx == -1 or end_idx == -1:
    print(f"Start: {start_idx}, End: {end_idx}")
    exit(1)

# Keep everything before the addition and the end marker
before = content[:start_idx]
after = content[end_idx:]

# Build the new addition
new_content = before + build_addition() + after

with open('door3_cells_batchB.lean', 'w', encoding='utf-8') as f:
    f.write(new_content)
print('Rewrote addition')
