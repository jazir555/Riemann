import door3_rational_certificates

open Set

/-! Purely geometric part of the exact-rational candidate table.  This file
records the open interior coverage independently of the analytic centre and
derivative fields. -/

def Door3RationalCandidate.contains (c : Door3RationalCandidate) (x y : ℝ) : Prop :=
  (c.x0 : ℝ) < x ∧ x < c.x1 ∧ (c.y0 : ℝ) < y ∧ y < c.y1

theorem door3_x_interval_cover {x : ℝ} (hx0 : -10 < x) (hx1 : x < 10) :
    (-10 < x ∧ x < (-7.5 : ℝ)) ∨
    (-8 < x ∧ x < (-5.5 : ℝ)) ∨
    (-6 < x ∧ x < (-3.5 : ℝ)) ∨
    (-4 < x ∧ x < (-1.5 : ℝ)) ∨
    (-2 < x ∧ x < (0.5 : ℝ)) ∨
    (0 < x ∧ x < 2.5) ∨
    (2 < x ∧ x < 4.5) ∨
    (4 < x ∧ x < 6.5) ∨
    (6 < x ∧ x < 8.5) ∨
    (7.5 < x ∧ x < 10) := by
  by_cases h : x < (-7.5 : ℝ)
  · left; exact ⟨hx0, h⟩
  by_cases h' : x < (-5.5 : ℝ)
  · right; left; exact ⟨by linarith, h'⟩
  by_cases h'' : x < (-3.5 : ℝ)
  · right; right; left; exact ⟨by linarith, h''⟩
  by_cases h''' : x < (-1.5 : ℝ)
  · right; right; right; left; exact ⟨by linarith, h'''⟩
  by_cases h'''' : x < (0.5 : ℝ)
  · right; right; right; right; left; exact ⟨by linarith, h''''⟩
  by_cases h''''' : x < (2.5 : ℝ)
  · right; right; right; right; right; left; exact ⟨by linarith, h'''''⟩
  by_cases h'''''' : x < (4.5 : ℝ)
  · right; right; right; right; right; right; left; exact ⟨by linarith, h''''''⟩
  by_cases h''''''' : x < (6.5 : ℝ)
  · right; right; right; right; right; right; right; left; exact ⟨by linarith, h'''''''⟩
  by_cases h'''''''' : x < (8.5 : ℝ)
  · right; right; right; right; right; right; right; right; left; exact ⟨by linarith, h''''''''⟩
  right; right; right; right; right; right; right; right; right; exact ⟨by linarith, hx1⟩

theorem door3_y_interval_cover {y : ℝ} (hy0 : (0.01 : ℝ) < y) (hy1 : y < 0.49) :
    ((0.01 : ℝ) < y ∧ y < 0.2) ∨
    ((0.1 : ℝ) < y ∧ y < 0.3) ∨
    ((0.2 : ℝ) < y ∧ y < 0.4) ∨
    ((0.3 : ℝ) < y ∧ y < 0.49) := by
  by_cases h : y < (0.2 : ℝ)
  · exact Or.inl ⟨hy0, h⟩
  by_cases h' : y < (0.3 : ℝ)
  · exact Or.inr (Or.inl ⟨by linarith, h'⟩)
  by_cases h'' : y < (0.4 : ℝ)
  · exact Or.inr (Or.inr (Or.inl ⟨by linarith, h''⟩))
  exact Or.inr (Or.inr (Or.inr ⟨by linarith, hy1⟩))

theorem door3_rational_open_grid_cover {x y : ℝ}
    (hx0 : -10 < x) (hx1 : x < 10)
    (hy0 : (0.01 : ℝ) < y) (hy1 : y < 0.49) :
    ∃ x0 x1 y0 y1 : ℝ,
      x0 < x ∧ x < x1 ∧ y0 < y ∧ y < y1 ∧
      ((x0, x1, y0, y1) = ((-10 : ℝ), -7.5, 0.01, 0.2) ∨
       (x0, x1, y0, y1) = ((-8 : ℝ), -5.5, 0.01, 0.2) ∨
       (x0, x1, y0, y1) = ((-6 : ℝ), -3.5, 0.01, 0.2) ∨
       (x0, x1, y0, y1) = ((-4 : ℝ), -1.5, 0.01, 0.2) ∨
       (x0, x1, y0, y1) = ((-2 : ℝ), 0.5, 0.01, 0.2) ∨
       (x0, x1, y0, y1) = ((0 : ℝ), 2.5, 0.01, 0.2) ∨
       (x0, x1, y0, y1) = ((2 : ℝ), 4.5, 0.01, 0.2) ∨
       (x0, x1, y0, y1) = ((4 : ℝ), 6.5, 0.01, 0.2) ∨
       (x0, x1, y0, y1) = ((6 : ℝ), 8.5, 0.01, 0.2) ∨
       (x0, x1, y0, y1) = ((7.5 : ℝ), 10, 0.01, 0.2) ∨
       (x0, x1, y0, y1) = ((-10 : ℝ), -7.5, 0.1, 0.3) ∨
       (x0, x1, y0, y1) = ((-8 : ℝ), -5.5, 0.1, 0.3) ∨
       (x0, x1, y0, y1) = ((-6 : ℝ), -3.5, 0.1, 0.3) ∨
       (x0, x1, y0, y1) = ((-4 : ℝ), -1.5, 0.1, 0.3) ∨
       (x0, x1, y0, y1) = ((-2 : ℝ), 0.5, 0.1, 0.3) ∨
       (x0, x1, y0, y1) = ((0 : ℝ), 2.5, 0.1, 0.3) ∨
       (x0, x1, y0, y1) = ((2 : ℝ), 4.5, 0.1, 0.3) ∨
       (x0, x1, y0, y1) = ((4 : ℝ), 6.5, 0.1, 0.3) ∨
       (x0, x1, y0, y1) = ((6 : ℝ), 8.5, 0.1, 0.3) ∨
       (x0, x1, y0, y1) = ((7.5 : ℝ), 10, 0.1, 0.3) ∨
       (x0, x1, y0, y1) = ((-10 : ℝ), -7.5, 0.2, 0.4) ∨
       (x0, x1, y0, y1) = ((-8 : ℝ), -5.5, 0.2, 0.4) ∨
       (x0, x1, y0, y1) = ((-6 : ℝ), -3.5, 0.2, 0.4) ∨
       (x0, x1, y0, y1) = ((-4 : ℝ), -1.5, 0.2, 0.4) ∨
       (x0, x1, y0, y1) = ((-2 : ℝ), 0.5, 0.2, 0.4) ∨
       (x0, x1, y0, y1) = ((0 : ℝ), 2.5, 0.2, 0.4) ∨
       (x0, x1, y0, y1) = ((2 : ℝ), 4.5, 0.2, 0.4) ∨
       (x0, x1, y0, y1) = ((4 : ℝ), 6.5, 0.2, 0.4) ∨
       (x0, x1, y0, y1) = ((6 : ℝ), 8.5, 0.2, 0.4) ∨
       (x0, x1, y0, y1) = ((7.5 : ℝ), 10, 0.2, 0.4) ∨
       (x0, x1, y0, y1) = ((-10 : ℝ), -7.5, 0.3, 0.49) ∨
       (x0, x1, y0, y1) = ((-8 : ℝ), -5.5, 0.3, 0.49) ∨
       (x0, x1, y0, y1) = ((-6 : ℝ), -3.5, 0.3, 0.49) ∨
       (x0, x1, y0, y1) = ((-4 : ℝ), -1.5, 0.3, 0.49) ∨
       (x0, x1, y0, y1) = ((-2 : ℝ), 0.5, 0.3, 0.49) ∨
       (x0, x1, y0, y1) = ((0 : ℝ), 2.5, 0.3, 0.49) ∨
       (x0, x1, y0, y1) = ((2 : ℝ), 4.5, 0.3, 0.49) ∨
       (x0, x1, y0, y1) = ((4 : ℝ), 6.5, 0.3, 0.49) ∨
       (x0, x1, y0, y1) = ((6 : ℝ), 8.5, 0.3, 0.49) ∨
       (x0, x1, y0, y1) = ((7.5 : ℝ), 10, 0.3, 0.49)) := by
  rcases door3_x_interval_cover hx0 hx1 with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx <;>
    rcases door3_y_interval_cover hy0 hy1 with hy | hy | hy | hy <;>
      first
      | exact ⟨_, _, _, _, hx.1, hx.2, hy.1, hy.2, by simp [hx, hy]⟩

#print axioms door3_x_interval_cover
#print axioms door3_y_interval_cover
#print axioms door3_rational_open_grid_cover
