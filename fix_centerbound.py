import re

with open('door3_cells_batchB.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# Fix center bound proofs for B13-B19
# Add radius conversion step before B_center_bound_of_components call

cells_info = [
    ('B13', '0.05', '0.07', 'R13'),
    ('B14', '0.05', '0.07', 'R14'),
    ('B15', '0.15', '0.06', 'R15'),
    ('B16', '0.15', '0.06', 'R16'),
    ('B17', '0.05', '0.07', 'R17'),
    ('B18', '0.05', '0.07', 'R18'),
    ('B19', '0.002', '0.07', 'R19'),
]

for cell, eps, m, rect_name in cells_info:
    # Pattern: have hsCenter : ... := rfl\n    exact B_center_bound_of_components
    old = f'''  have hsCenter : {cell}_sCenter = (1 / 2 : ℂ) + Complex.I * {cell}_rect.center := rfl
  exact B_center_bound_of_components'''
    
    new = f'''  have hsCenter : {cell}_sCenter = (1 / 2 : ℂ) + Complex.I * {cell}_rect.center := rfl
  have hrad_le : {cell}_rect.radius ≤ 1.26 := CentralCoverAssembly.{rect_name}_radius_lt
  have hbud : ({eps} : ℝ) + {m} * {cell}_rect.radius ≤ ({eps} : ℝ) + {m} * 1.26 := by
    linarith
  have hthreshold : ({eps} : ℝ) + {m} * 1.26 ≤ {cell}_threshold_check := {cell}_threshold_check
  exact B_center_bound_of_components'''
    
    content = content.replace(old, new)

with open('door3_cells_batchB.lean', 'w', encoding='utf-8') as f:
    f.write(content)
print('Fixed center bound proofs')
