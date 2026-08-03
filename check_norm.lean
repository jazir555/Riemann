import Mathlib

open MeasureTheory

example {f : ℝ → ℂ} {a b : ℝ} (h : ContinuousOn f (Set.Icc a b)) (hab : a ≤ b) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact ContinuousOn.integrableOn_Icc h |>.mono_set Set.Ioc_subset_Icc_self
