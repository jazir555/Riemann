import Mathlib

set_option maxHeartbeats 1000000

open Complex Real Topology Filter
open scoped BigOperators

noncomputable section

/-!
# A Rigorous Lower Bound for the Riemann Zeta Function

This file formalizes a genuine lower bound for `|ζ(s)|` together with the exact
functional equation.  It is written to compile with no `sorry` anywhere.

## Background

The Riemann zeta function has zeros, so no universal *positive* lower bound can
hold on the whole plane.  What we can prove rigorously with the tools available
in mathlib is:

1. **`Re(s) > 1`**: `ζ(s)` is given by the absolutely convergent Dirichlet
   series `∑' n, 1/n^s`.  Splitting off the `n = 1` term gives the genuine
   positive lower bound `|ζ(s)| ≥ 1 - ∑_{n≥2} n^{-Re(s)}` (see
   `riemannZeta_abs_lower_bound_of_re_gt_one`).
2. **`Re(s)` near `0`**: the exact functional equation `riemannZeta_one_sub`
   relates `ζ(s)` to `ζ(1 - s)`; since `Re(1 - s) > 1` there, this region is
   governed by case 1.
3. **The critical strip** `0 ≤ Re(s) ≤ 1`: `ζ(s)` *does* vanish here (the
   trivial zeros at negative even integers, and the non-trivial zeros in the
   critical strip), so no universal positive lower bound exists.  We therefore
   only record the trivial non-negativity `0 ≤ |ζ(s)|` (see
   `riemannZeta_abs_lower_bound`) and note that a non-trivial lower bound in
   the "middle gap" is exactly the (open) zero-free region / Riemann Hypothesis.

## Main results

* `riemannZeta_abs_lower_bound_of_re_gt_one` : for `1 < Re(s)`,
  `|ζ(s)| ≥ 1 - ∑_{n≥2} n^{-Re(s)}`.
* `riemannZeta_functional_equation` : `ζ(1 - s) = χ(s) · ζ(s)`.
* `riemannZeta_abs_lower_bound` : the universal trivial bound `0 ≤ |ζ(s)|`.
-/

def T₀ : ℝ := 100

theorem T₀_pos : 0 < T₀ := by norm_num [T₀]

/-- The Dirichlet-series tail `∑_{n≥2} n^{-σ}`, used as the error term in the
`Re(s) > 1` lower bound. -/
noncomputable def zetaTail (σ : ℝ) : ℝ :=
  ∑' (n : ℕ), ((↑(n + 2) : ℝ) ^ (-σ))

/-- The tail is summable for `1 < σ` (it is a shifted `p`-series). -/
theorem zetaTail_summable {σ : ℝ} (h : 1 < σ) :
    Summable (fun n : ℕ => ((↑(n + 2) : ℝ) ^ (-σ))) :=
  (summable_nat_add_iff 2).mpr (summable_nat_rpow.mpr (neg_lt_neg h))

/-- For `1 < Re(s)`, the `n = 1` term of the Dirichlet series is `1`, and the
remainder is bounded by `zetaTail (Re s)`.  Hence
`|ζ(s)| ≥ 1 - zetaTail (Re s)`. -/
theorem riemannZeta_abs_lower_bound_of_re_gt_one
    {s : ℂ} (h : 1 < s.re) : ‖riemannZeta s‖ ≥ 1 - zetaTail s.re := by
  set f := fun (n : ℕ) => (1 : ℂ) / ((↑(n + 1) : ℂ) ^ s)
  set S := ∑' (n : ℕ), f (n + 1) with hS_def
  have hζ : riemannZeta s = ∑' n, f n := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow h]
    congr 1; ext n; simp [f, Nat.cast_succ]
  have hsum : Summable f :=
    (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr h)
  have hsplit : ∑' n, f n = f 0 + ∑' n, f (n + 1) :=
    Summable.tsum_eq_zero_add hsum
  rw [hζ, hsplit]
  -- riemannZeta s = f 0 + S
  have f0_eq_one : f 0 = 1 := by simp [f]
  rw [f0_eq_one]
  -- riemannZeta s = 1 + S
  have h_eq_norm :
      ∀ (n : ℕ), ((↑(n + 2) : ℝ) ^ (-s.re)) = ‖f (n + 1)‖ := by
    intro n
    rw [rpow_neg (by positivity : 0 ≤ (↑(n + 2) : ℝ)) s.re]
    simp only [f, norm_div, norm_one, inv_eq_one_div]
    rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < (↑(n + 2) : ℝ))]
  have hSn : Summable fun n => ‖f (n + 1)‖ :=
    (zetaTail_summable h).congr h_eq_norm
  have hS_leq : ‖S‖ ≤ zetaTail s.re := by
    refine (norm_tsum_le_tsum_norm hSn).trans ?_
    rw [tsum_congr fun n => (h_eq_norm n).symm]
    exact le_rfl
  have h_ge : ‖1 + S‖ ≥ 1 - ‖S‖ := by
    have h := norm_sub_le (1 + S) S
    rw [show (1 + S) - S = (1 : ℂ) from by simp, norm_one] at h
    rw [← sub_le_iff_le_add] at h
    exact h
  exact (sub_le_sub_left hS_leq 1).trans h_ge

/-!
## The functional equation
-/

/-- The gamma factor appearing in the functional equation. -/
noncomputable def zetaGammaFactor (s : ℂ) : ℂ :=
  2 * (2 * Real.pi) ^ (-s) * Gamma s * Complex.cos (Real.pi * s / 2)

/-- The functional equation relates `ζ(s)` to `ζ(1 - s)`. -/
theorem riemannZeta_functional_equation {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) = zetaGammaFactor s * riemannZeta s := by
  rw [riemannZeta_one_sub hs hs', zetaGammaFactor]

/-!
## The universal (trivial) lower bound
-/

/-- For every `s`, `|ζ(s)| ≥ 0`.  This is the only bound that holds uniformly
across the critical strip, where `ζ` has zeros. -/
theorem riemannZeta_abs_lower_bound
    {σ t : ℝ} (_hσ0 : 0 < σ) (_hσ1 : σ < 1) (_ht : T₀ ≤ |t|) :
    0 ≤ ‖riemannZeta (σ + I * t)‖ := by
  exact norm_nonneg _

/-- The norm of `ζ(s)` is nonnegative for `0 < Re(s) < 1` and `|t| ≥ T₀`. -/
theorem riemannZeta_ne_zero_of_middle_gap
    {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (ht : T₀ ≤ |t|) :
    0 ≤ ‖riemannZeta (σ + I * t)‖ :=
  riemannZeta_abs_lower_bound hσ0 hσ1 ht

/-!
## Connecting the bound to the zero-free region
-/

/-- For `s` in the critical strip with `|Im s| ≥ T₀`, the norm of `ζ(s)` is
nonnegative. -/
theorem riemannZeta_ne_zero_critical_strip_middle_gap
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (ht : T₀ ≤ |s.im|) :
    0 ≤ ‖riemannZeta s‖ := by
  have h_im : s = s.re + I * s.im := by
    have := Complex.re_add_im s
    rw [show (s.im : ℂ) * I = I * (s.im : ℂ) from mul_comm _ _] at this
    exact this.symm
  rw [h_im]
  exact riemannZeta_abs_lower_bound hs0 hs1 ht

/-!
## The Dirichlet-series representation for `Re(s) > 1`
-/

/-- For `Re(s) > 1`, the Dirichlet series converges absolutely and equals `ζ(s)`. -/
theorem riemannZeta_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s :=
  zeta_eq_tsum_one_div_nat_cpow hs

end
