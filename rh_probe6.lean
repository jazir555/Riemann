import Mathlib
open Set Filter Topology Real
open scoped Topology

#check NormedSpace.expSeries_hasSum_exp_of_mem_ball'
#check NormedSpace.expSeries_div_hasSum_exp_of_mem_ball
#check expSeries_radius_eq_top
#check NormedSpace.expSeries_radius_eq_top

-- Try: real exp power series
example (u : ℝ) : HasSum (fun n : ℕ => u ^ n / (Nat.factorial n : ℝ)) (Real.exp u) := by
  have h := NormedSpace.expSeries_div_hasSum_exp_of_mem_ball (𝕂 := ℝ) (𝔸 := ℝ) u
    ((NormedSpace.expSeries_radius_eq_top ℝ ℝ).symm ▸ by simp : u ∈ Metric.eball (0 : ℝ) (NormedSpace.expSeries ℝ ℝ).radius)
  simpa [Real.exp_eq_exp_ℝ] using h
