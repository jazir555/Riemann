import Mathlib
import ZeroFreeRegionHadamard

open ZeroFreeRegionHadamard Complex Real
open scoped Topology

/-! Order-of-growth infrastructure for `xi`.

The algebraic identity `xi s = s * (s - 1) * completedRiemannZeta₀ s + 1` together
with `orderSet_completedRiemannZeta₀` (a `exp(‖z‖^(3/2))` bound for
`completedRiemannZeta₀`) yields the whole-plane bound
`‖xi z‖ ≤ exp(K·‖z‖^(3/2))` for large `‖z‖` (see `xi_norm_bound_whole_plane`).
Because `exp(‖z‖^(3/2))` dominates any polynomial, the polynomial factor
`‖z‖·‖z - 1‖` can be absorbed into the exponential, giving `ρ ∈ orderSet xi` for
every exponent `ρ > 3/2`.  This is enough for the zero-free-region machinery,
which only needs some exponent `≤ 7/4`; we instantiate it at `7/4`. -/

theorem orderSet_xi_of {ρ : ℝ} (hρ : (3 / 2 : ℝ) < ρ) : ρ ∈ orderSet xi := by
  obtain ⟨K, hK, C₀, hC₀, hb⟩ := xi_norm_bound_whole_plane
  have hKnn : 0 ≤ K := hK
  have hδ : 0 < ρ - 3 / 2 := by linarith
  have hinv : (1 / (ρ - 3 / 2)) * (ρ - 3 / 2) = 1 :=
    one_div_mul_cancel (ne_of_gt hδ)
  let r₀ := max (max C₀ 1) (K ^ (1 / (ρ - 3 / 2)))
  have hm : 0 < max C₀ 1 := by linarith [le_max_right C₀ 1]
  have hr₀pos : 0 < r₀ := hm.trans_le (le_max_left (max C₀ 1) (K ^ (1 / (ρ - 3 / 2))))
  refine ⟨1, r₀, hr₀pos, fun z hz => ?_⟩
  have hzC₀ : C₀ ≤ ‖z‖ :=
    (le_max_left C₀ 1).trans ((le_max_left (max C₀ 1) (K ^ (1 / (ρ - 3 / 2)))).trans hz)
  have hz1 : 1 ≤ ‖z‖ :=
    (le_max_right C₀ 1).trans ((le_max_left (max C₀ 1) (K ^ (1 / (ρ - 3 / 2)))).trans hz)
  have hzK : K ^ (1 / (ρ - 3 / 2)) ≤ ‖z‖ :=
    (le_max_right (max C₀ 1) (K ^ (1 / (ρ - 3 / 2)))).trans hz
  have hzpos : 0 < ‖z‖ := by linarith
  have hKδ : K ≤ ‖z‖ ^ (ρ - 3 / 2) := by
    have := Real.rpow_le_rpow (by positivity : 0 ≤ K ^ (1 / (ρ - 3 / 2))) hzK
      (by linarith : 0 ≤ ρ - 3 / 2)
    rwa [← Real.rpow_mul hKnn, hinv, Real.rpow_one] at this
  have hprod : K * ‖z‖ ^ ((3 : ℝ) / 2) ≤ ‖z‖ ^ ρ := by
    calc K * ‖z‖ ^ ((3 : ℝ) / 2)
      _ ≤ ‖z‖ ^ (ρ - 3 / 2) * ‖z‖ ^ ((3 : ℝ) / 2) := mul_le_mul_of_nonneg_right hKδ (by positivity)
      _ = ‖z‖ ^ (ρ - 3 / 2 + 3 / 2) := by rw [Real.rpow_add hzpos]
      _ = ‖z‖ ^ ρ := by ring_nf
  have hxi : ‖xi z‖ ≤ Real.exp (K * ‖z‖ ^ (3 / 2 : ℝ)) := hb z hzC₀
  rw [one_mul]
  exact hxi.trans (Real.exp_le_exp.mpr hprod)

/-- `xi` belongs to `orderSet` with exponent `7 / 4` (hence also with any larger
exponent, by `orderSet_mono`).  This supplies the exponent `≤ 7/4` required by
the zero-free-region machinery. -/
theorem orderSet_xi : (7 / 4 : ℝ) ∈ orderSet xi :=
  orderSet_xi_of (by norm_num)
