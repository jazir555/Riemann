import interval_arith

/-!
# Finite-product Gamma bounds for Door 3

The recurrence preserves the imaginary part in every denominator. Keeping the
real Gamma recurrence at the same real part avoids bounding the shifted real
Gamma function and the denominator independently.
-/

open scoped BigOperators

namespace Door3GammaProduct

theorem gamma_shift_norm {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ‖Complex.Gamma (z + n)‖ =
      ‖Complex.Gamma z‖ * ∏ k ∈ Finset.range n, ‖z + (k : ℂ)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hzn : z + (n : ℂ) ≠ 0 := by
      intro h
      have hRe := congrArg Complex.re h
      simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hRe
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hzn,
      norm_mul, ih, Finset.prod_range_succ]
    ring

theorem real_gamma_shift {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.Gamma (x + n) = Real.Gamma x * ∏ k ∈ Finset.range n, (x + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : x + (n : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hxn, ih,
      Finset.prod_range_succ]
    ring

/-- The finite-product bound before division; valid for every truncation. -/
theorem norm_gamma_mul_prod_le {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ‖Complex.Gamma z‖ * (∏ k ∈ Finset.range n, ‖z + (k : ℂ)‖) ≤
      Real.Gamma z.re * ∏ k ∈ Finset.range n, (z.re + k) := by
  have hpos : 0 < (z + (n : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    positivity
  have h := R00GammaLower.norm_Gamma_le_realGamma hpos
  rw [gamma_shift_norm hz, Complex.add_re, Complex.natCast_re,
    real_gamma_shift hz] at h
  exact h

/-- A computable finite product of real/norm ratios captures vertical decay. -/
theorem norm_gamma_le_prod {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re *
      ∏ k ∈ Finset.range n, ((z.re + k) / ‖z + (k : ℂ)‖) := by
  have hpos : 0 < ∏ k ∈ Finset.range n, ‖z + (k : ℂ)‖ := by
    apply Finset.prod_pos
    intro k hk
    apply norm_pos_iff.mpr
    intro h
    have hRe := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hRe
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  rw [Finset.prod_div_distrib, ← mul_div_assoc, le_div_iff₀ hpos]
  exact norm_gamma_mul_prod_le hz n

/-- Squared form: all factors are rational when the real and imaginary parts
are rational, so the truncation can be checked with exact arithmetic. -/
theorem norm_gamma_sq_le_prod {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ‖Complex.Gamma z‖ ^ 2 ≤ Real.Gamma z.re ^ 2 *
      ∏ k ∈ Finset.range n,
        ((z.re + k) ^ 2 / ((z.re + k) ^ 2 + z.im ^ 2)) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_gamma_le_prod hz n) 2
  rw [mul_pow, ← Finset.prod_pow] at h
  have hf : ∀ k : ℕ, ((z.re + k) / ‖z + (k : ℂ)‖) ^ 2 =
      (z.re + k) ^ 2 / ((z.re + k) ^ 2 + z.im ^ 2) := by
    intro k
    rw [div_pow, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.natCast_re, Complex.add_im,
      Complex.natCast_im, add_zero, ← pow_two]
  simp_rw [hf] at h
  exact h

end Door3GammaProduct

#print axioms Door3GammaProduct.norm_gamma_le_prod
#print axioms Door3GammaProduct.norm_gamma_sq_le_prod
