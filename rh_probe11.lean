import Mathlib
open Set Filter Topology Real
open scoped Topology

#check hasFPowerSeriesAt_iff
#check HasFPowerSeriesAt
#check AnalyticAt
#check AnalyticOnNhd
#check HasFPowerSeriesAt.analyticAt
#check AnalyticAt.analyticOnNhd
#check FormalMultilinearSeries.apply_eq_pow_smul_coeff
#check AnalyticOnNhd.mk
#check analyticOnNhd_iff

-- structure of AnalyticOnNhd
example (s : Set ℝ) (f : ℝ → ℝ) : AnalyticOnNhd ℝ f s ↔ ∀ x ∈ s, AnalyticAt ℝ f x := by
  rfl

-- structure of AnalyticAt
example (f : ℝ → ℝ) (x : ℝ) : AnalyticAt ℝ f x ↔ ∃ p : FormalMultilinearSeries ℝ ℝ ℝ, HasFPowerSeriesAt f p x := by
  rfl

-- structure of HasFPowerSeriesAt
example (f : ℝ → ℝ) (p : FormalMultilinearSeries ℝ ℝ ℝ) (x : ℝ) :
    HasFPowerSeriesAt f p x ↔ ∃ r : ℝ≥0∞, 0 < r ∧ HasFPowerSeriesOnBall f p x r := by
  rfl
