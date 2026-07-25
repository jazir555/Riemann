import Mathlib
set_option maxHeartbeats 1000000

open Complex in
example (xi : ℂ) (t : ℝ) :
    2 * xi / (-(t ^ 2 + 1 / 4 : ℂ)) = -(2 / (t ^ 2 + 1 / 4 : ℂ)) * xi := by
  field_simp
  ring

-- The actual post-rewrite goal has coerced ℝ:
example (xi : ℂ) (t : ℝ) :
    2 * xi / -(↑(t ^ 2 + 1 / 4 : ℝ)) = -(↑(2 / (t ^ 2 + 1 / 4 : ℝ))) * xi := by
  push_cast
  field_simp
  ring
