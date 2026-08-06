import Mathlib

open Complex Real Topology
open scoped BigOperators

-- Test: norm of I * ↑t using have then rw
example (t : ℝ) : ‖I * ↑t‖ = |t| := by
  rw [Complex.norm_mul, Complex.norm_I, one_mul]
  have h := RCLike.norm_ofReal t
  rw [h]

-- Test: norm of I * ↑t using simp
example (t : ℝ) : ‖I * ↑t‖ = |t| := by
  simp [Complex.norm_mul, Complex.norm_I, RCLike.norm_ofReal]

-- Test: norm of I * ↑t using exact
example (t : ℝ) : ‖I * ↑t‖ = |t| := by
  rw [Complex.norm_mul, Complex.norm_I, one_mul]
  exact RCLike.norm_ofReal t

-- Test: norm from congr_arg using simp
example (t : ℝ) (z : ℂ) (h : z = -(I * ↑t : ℂ)) : ‖z‖ = |t| := by
  rw [h, norm_neg, Complex.norm_mul, Complex.norm_I, one_mul]
  exact RCLike.norm_ofReal t

-- Test: the full continuity mapsTo proof
-- After Set.mem_singleton_iff.mp, we get 1 + z + I * ↑t = 1
-- then z + I * ↑t = 0 via linear_combination
-- then z = -(I * ↑t) via linear_combination
-- then ‖z‖ = |t| via norm_neg + norm_mul + norm_I + one_mul + norm_ofReal
-- then ‖z‖ ≤ 1/2 (from closedBall) but |t| ≥ 1, contradiction

-- Test: hK with (0 : ℂ) explicit
example (f : ℂ → ℝ) (s : Set ℂ) (K : ℂ)
    (hK : ∀ ⦃y⦄, y ∈ s → f y ≤ f K)
    (hy : (0 : ℂ) ∈ s) : f 0 ≤ f K :=
  hK hy

-- Test: Metric.mem_closedBall_self
example : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) (1/2 : ℝ) :=
  Metric.mem_closedBall_self (by norm_num)

-- Test: mem_ball → mem_closedBall
example (z : ℂ) (h : z ∈ Metric.ball 0 (1/2 : ℝ)) : z ∈ Metric.closedBall 0 (1/2 : ℝ) :=
  Metric.mem_closedBall.mpr (Metric.mem_ball.mp h).le

-- Test: the linarith contradiction for final step
example (x : ℝ) (hx : x < 1/10) (hpos : 0 < 1/2 - x) :
    4 * x / (1/2 - x) < 1 := by
  rw [div_lt_one hpos]
  linarith

-- Test: hfz₀ proof structure
example (s : ℂ) (t : ℝ) (htdef : t = s.im) (hz : riemannZeta s = 0) :
    (fun z : ℂ => riemannZeta (1 + z + I * t) - riemannZeta (1 + I * t)) ↑(s.re - 1) =
    -riemannZeta (1 + I * t) := by
  simp only []
  have hmain : (1 : ℂ) + ↑(s.re - 1) + I * t = s := by
    rw [htdef, show (1 : ℂ) + ↑(s.re - 1) = ↑s.re from by push_cast; ring, mul_comm I]
    exact Complex.re_add_im s
  rw [hmain, hz]
  ring
