import re

with open('door3_cells_batchB.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# Fix sCenter_re theorems: replace full proof with unfold + norm_num
def fix_sCenter_re(content):
    pattern = r'(theorem (B\d+_sCenter_re) : \2 = 0\.3 := by\s+)unfold (B\d+_sCenter) CellProofEngine\.Rect2D\.center\s+have h : \3_rect\.center\.re = \(\3_rect\.x0 \+ \3_rect\.x1\) / 2 := by\s+unfold CellProofEngine\.Rect2D\.center; ring\s+have h\' : \3_rect\.center\.im = \(\3_rect\.y0 \+ \3_rect\.y1\) / 2 := by\s+unfold CellProofEngine\.Rect2D\.center; ring\s+rw \[h, h\'\]\s+simp \[Complex\.add_re, Complex\.mul_re, Complex\.ofReal_re, Complex\.I_re\]\s+norm_num'
    def replacer(m):
        return m.group(1) + '    unfold ' + m.group(3) + ' CellProofEngine.Rect2D.center\n    norm_num'
    return re.sub(pattern, replacer, content)

# Fix sCenter_im theorems: replace full proof with unfold + norm_num
def fix_sCenter_im(content):
    pattern = r'(theorem (B\d+_sCenter_im) : \2 = ([-\d.]+) := by\s+)unfold (B\d+_sCenter) CellProofEngine\.Rect2D\.center\s+have h : \3_rect\.center\.re = \(\3_rect\.x0 \+ \3_rect\.x1\) / 2 := by\s+unfold CellProofEngine\.Rect2D\.center; ring\s+have h\' : \3_rect\.center\.im = \(\3_rect\.y0 \+ \3_rect\.y1\) / 2 := by\s+unfold CellProofEngine\.Rect2D\.center; ring\s+rw \[h, h\'\]\s+simp \[Complex\.add_im, Complex\.mul_im, Complex\.ofReal_im, Complex\.I_im\]\s+norm_num'
    def replacer(m):
        return m.group(1) + '    unfold ' + m.group(4) + ' CellProofEngine.Rect2D.center\n    norm_num'
    return re.sub(pattern, replacer, content)

content = fix_sCenter_re(content)
content = fix_sCenter_im(content)

with open('door3_cells_batchB.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('Fixed all sCenter theorems')
