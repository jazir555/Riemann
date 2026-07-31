import sys
sys.stdout.reconfigure(encoding='utf-8')

with open(r'C:\Users\mmeadow\Documents\Lean\mathlib4\riemann hypothesis.lean', 'rb') as f:
    data = f.read()

lines = data.split(b'\r\n')

# Find all lines with · character and check what Unicode code point it is
for i, line_bytes in enumerate(lines):
    try:
        line = line_bytes.decode('utf-8')
    except:
        continue
    for j, c in enumerate(line):
        if ord(c) in [0x00B7, 0x2219, 0x2022]:  # MIDDLE DOT, BULLET OPERATOR, BULLET
            print(f"Line {i+1}, Col {j}: U+{ord(c):04X} '{c}'")
            # Show context
            print(f"  Context: {line[max(0,j-5):j+10]}")
            break  # only report first per line
    # Also check for criticalStripCover14 area
    if 9253 <= i+1 <= 9256:
        print(f"Line {i+1}: {line}")
        for j, c in enumerate(line):
            if ord(c) > 127:
                print(f"  Col {j}: U+{ord(c):04X} '{c}'")
