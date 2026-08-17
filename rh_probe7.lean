import Mathlib
open Set Filter Topology Real MeasureTheory
open scoped Interval Topology

#check ContinuousOn.aestronglyMeasurable
#check measurableSet_uIoc
#check uIoc_subset_uIcc
#check ContinuousOn.mono
#check ContinuousAt.rpow_const
#check Real.continuousAt_log
#check continuousOn_rpow_const
#check continuousOn_of_forall_continuousAt
#check rpow_neg
#check exp_neg_mul_log
#check rpow_add
#check Real.exp_eq_exp_ℝ
#check Continuous.intervalIntegrable
#check ContinuousOn.intervalIntegrable

-- test the measurability pattern
example (n : ℕ) (s₀ : ℝ) (k : ℕ) :
    AEStronglyMeasurable (fun x : ℝ => (x - (n+1:ℝ)) * x ^ (-(s₀+1)) * (-1:ℝ)^k * (Real.log x)^k / (Nat.factorial k : ℝ) * (0:ℝ)^k)
      (volume.restrict (uIoc (n+1:ℝ) ((n+1:ℝ)+1))) := by
  have hxpos : ∀ x ∈ Icc (n + 1 : ℝ) ((n + 1 : ℝ) + 1), 0 < x := by
    intro x hx
    exact lt_of_lt_of_le (by positivity) hx.1
  have hcont : ContinuousOn (fun x : ℝ => (x - (n+1:ℝ)) * x ^ (-(s₀+1)) * (-1:ℝ)^k * (Real.log x)^k / (Nat.factorial k : ℝ) * (0:ℝ)^k) (Icc (n+1:ℝ) ((n+1:ℝ)+1)) := by
    refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
    have hxp : 0 < x := hxpos x hx
    refine (continuousAt_const.mul ?_).mul continuousAt_const |>.mul ?_ |>.div continuousAt_const |>.mul continuousAt_const
    · exact continuousAt_id.rpow_const (Or.inl (ne_of_gt hxp))
    · have hlogc : ContinuousAt (fun y : ℝ => Real.log y) x := Real.continuousAt_log (ne_of_gt hxp)
      simpa using hlogc.pow k
  exact ContinuousOn.aestronglyMeasurable hcont (by simpa using measurableSet_Icc : MeasurableSet (Icc (n+1:ℝ) ((n+1:ℝ)+1)))
