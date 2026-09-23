with open('door3_cells_batchB.lean', 'r', encoding='utf-8') as f:
    content = f.read()

with open('batchB_addition.lean', 'r', encoding='utf-8') as f:
    addition = f.read()

start_marker = '  /-! ## Factor decomposition for all 10 cells (B11-B20)'
end_marker = 'end Door3BatchB'

start_idx = content.find(start_marker)
end_idx = content.find(end_marker)

if start_idx == -1:
    print("ERROR: start marker not found")
    exit(1)
if end_idx == -1:
    print("ERROR: end marker not found")
    exit(1)

before = content[:start_idx]
after = content[end_idx:]

new_content = before + addition + '\n' + after

with open('door3_cells_batchB.lean', 'w', encoding='utf-8') as f:
    f.write(new_content)
print('Spliced in clean addition')
