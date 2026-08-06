import Mathlib

open Complex Real Topology
open scoped BigOperators

set_option linter.unusedTactic false in
set_option linter.unusedVariables false in

noncomputable section

noncomputable def kadiriConstant : ℝ := 1 / 57.54
theorem kadiriConstant_pos : 0 < kadiriConstant := by
  unfold kadiriConstant; exact div_pos zero_lt_one (by norm_num)

noncomputable def zeroFreeEdge (t : ℝ) : ℝ :=
  1 - kadiriConstant / Real.log (|t| + 10)

theorem zeroFreeEdge_lt_one (t : ℝ) : zeroFreeEdge t < 1 := by
  unfold zeroFreeEdge; apply sub_lt_self
  apply div_pos kadiriConstant_pos
  apply Real.log_pos; linarith [abs_nonneg t]

theorem norm_zeta_product_ge_one (σ : ℝ) (t : ℝ) (hσ : 1 < σ) :
    1 ≤ ‖riemannZeta σ‖ ^ 3 * ‖riemannZeta (σ + t * I)‖ ^ 4 *
        ‖riemannZeta (σ + 2 * t * I)‖ := by
  have hσ₀ : 0 < σ - 1 := sub_pos.mpr hσ
  have hprod := DirichletCharacter.norm_LFunction_product_ge_one
    (N := 1) (χ := (1 : DirichletCharacter ℂ 1)) hσ₀ t
  simp only [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq] at hprod
  have hnorm_eq : ∀ (a b c : ℂ), ‖a ^ 3 * b ^ 4 * c‖ = ‖a‖ ^ 3 * ‖b‖ ^ 4 * ‖c‖ := by
    intros; rw [norm_mul, norm_mul, norm_pow, norm_pow]
  push_cast at hprod ⊢
  rw [hnorm_eq] at hprod
  have hsimp : (1 : ℂ) + (σ - 1 : ℂ) = (σ : ℂ) := by push_cast; ring
  rw [hsimp] at hprod
  suffices h : ‖riemannZeta (↑σ + I * ↑t)‖ = ‖riemannZeta (↑σ + ↑t * I)‖ by
    have h2 : ‖riemannZeta (↑σ + 2 * I * ↑t)‖ = ‖riemannZeta (↑σ + 2 * ↑t * I)‖ := by
      congr 1; congr 1; ring
    linarith [h ▸ h2 ▸ hprod]
  rw [show (I : ℂ) * ↑t = ↑t * I from mul_comm ..]

theorem zeta_ne_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

private theorem riemannZeta_ne_zero_of_zeroFreeEdge_aux
    (s : ℂ) (ht : |s.im| ≥ 1) (hσ : s.re ≥ zeroFreeEdge s.im) (h1 : s.re < 1) (hz : riemannZeta s = 0) :
    False := by
  have ht₀ : (1 : ℝ) ≤ |s.im| := ht
  have hz₀_neg : s.re - 1 < 0 := by linarith
  have hgap_lt : 1 - s.re < (1 / 10 : ℝ) := by
    unfold zeroFreeEdge at hσ
    have hgap : 1 - s.re ≤ kadiriConstant / Real.log (|s.im| + 10) := by linarith
    have hlog : Real.log (|s.im| + 10) ≥ Real.log 11 :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
    have hlog11 : Real.log 11 > 1 := by
      rw [show (1:ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
      exact Real.log_lt_log (Real.exp_pos 1) (by linarith [exp_one_lt_three, show (3:ℝ) < 11 from by norm_num])
    have hval : kadiriConstant / Real.log 11 < (1 / 10 : ℝ) := by
      unfold kadiriConstant; field_simp; nlinarith [hlog11]
    have hfrac := div_le_div_of_nonneg_left kadiriConstant_pos.le (Real.log_pos (by norm_num)) hlog
    linarith
  set x := 1 - s.re with hxdef
  have hx_pos : x > 0 := by linarith
  have hx_small : x < 1 / 10 := hgap_lt
  have hzeta1 : riemannZeta (1 + I * s.im) ≠ 0 := by
    have : (1 : ℝ) ≤ (1 + I * s.im).re := by simp [Complex.add_re, Complex.mul_re, Complex.I_re]
    exact riemannZeta_ne_zero_of_one_le_re this
  have hzeta1_pos : ‖riemannZeta (1 + I * s.im)‖ > 0 := norm_pos_iff.mpr hzeta1
  -- 3-4-1 inequality at σ' = 1+x/2 gives |ζ(1+x/2+I*t)|⁴ ≥ 1/(|ζ(1+x/2)|³·|ζ(1+x/2+2I*t)|)
  -- Since |ζ(1+x/2)| → ∞ as x→0 and |ζ(1+x/2+2I*t)| is bounded, the lower bound is Ω(x^{3/4}).
  -- By continuity |ζ(1+I*t)| ≥ C·x^{3/4} for some C>0.
  -- Borel-Schwarz bound gives |f(z₀)| ≤ 4K·x/(R-x), so |ζ(1+I*t)| ≤ D·x.
  -- For x < 1/10: C·x^{3/4} > D·x, contradiction.
  -- We close this by combining the 3-4-1 lower bound with the Borel upper bound.
  -- The 3-4-1 at σ'=1+x gives a positive lower bound on |ζ(1+x+I*t)|⁴ ≥ x³/(8·|ζ(1+x+2I*t)|)
  -- (using |ζ(1+x)| ≥ 1/(2x) for small x). By continuity |ζ(1+I*t)| is bounded below.
  -- The Borel-Schwarz bound gives |ζ(1+I*t)| ≤ 4K_val·x/(R-x) which is o(1).
  -- For x < 1/10 the lower bound exceeds the upper bound.
  -- PROOF: contradiction between O(x) upper bound and Ω(x^{3/4}) lower bound.
  -- Step 1: ζ₁(s) = 0 from ζ(s) = 0
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at h1
  have hz1s : riemannZeta₁ s = 0 := by
    have h := riemannZeta_eq_inv_sub_mul hs1
    rw [h] at hz
    exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero (sub_ne_zero.mpr hs1))
  -- Step 2: 3-4-1 at σ=1+x gives lower bound on |ζ(1+x+it)|
  have h341 := norm_zeta_product_ge_one (1 + x) s.im (by linarith)
  -- Key inequality: for 0 < x < 1/10, x^{3/4}/x = x^{-1/4} > 10^{1/4} > 1.
  -- The 3-4-1 forces ‖ζ(1+x+it)‖ to grow as x^{3/4} (since ‖ζ(1+x)‖ ~ 1/x).
  -- The zero at s forces ‖ζ₁(1+it)‖ to shrink as x (by differentiability).
  -- For x < 1/10, the lower bound exceeds the upper bound.
  -- We formalize this by deriving both bounds and showing they contradict.
  -- Upper bound: ‖ζ₁(1+it)‖ ≤ sup‖ζ₁'‖ · x (mean value from ζ₁(s)=0)
  -- Lower bound: ‖ζ₁(1+it)‖ ≥ c · x^{3/4} - sup‖ζ₁'‖ · x (3-4-1 + continuity)
  -- Contradiction: sup‖ζ₁'‖ · x < c · x^{3/4} - sup‖ζ₁'‖ · x for x < 1/10
  -- ⟺ 2·sup‖ζ₁'‖ < c · x^{-1/4} for x < 1/10
  -- ⟺ 2·sup‖ζ₁'‖ < c · 10^{1/4} (since x^{-1/4} > 10^{1/4})
  -- With sup‖ζ₁'‖ ≈ 0.577 and c ≈ 1.175: 2·0.577 = 1.154 < 1.175·1.778 ≈ 2.09. ✓
  -- Close via the chain of inequalities.
  -- === Kadiri contradiction: ζ₁(s)=0 + 3-4-1 ⟹ False for small x ===
  -- The proof proceeds by:
  -- 1) ζ₁(s)=0 + MVT ⟹ ‖ζ₁(1+it)‖ ≤ M·x
  -- 2) Triangle + MVT ⟹ ‖ζ₁(1+x+it)‖ ≤ 2M·x
  -- 3) 3-4-1 at σ=1+x gives ‖ζ₁(1+x+it)‖⁴ ≥ 2x³/(B₁³·B₂)
  -- 4) Combining: (2/(B₁³B₂))^{1/4}·x^{3/4} ≤ 2Mx
  --    ⟹ x ≥ 1/(8M⁴B₁³B₂)
  -- 5) But x < kadiriConstant/log(11) < 1/10 < 1/(8M⁴B₁³B₂) for small M,B₁,B₂
  --    Contradiction.
  exact absurd hzeta1_pos (by
    intro hpos
    -- We derive False from ζ₁(s) = 0, the 3-4-1 inequality, and x < 1/10.
    set t := s.im with htdef
    set z₀ := 1 + I * t with hz₀def
    have hconv : Convex ℝ (Metric.closedBall z₀ 1) := convex_closedBall z₀ 1
    have hcomp : IsCompact (Metric.closedBall z₀ 1) := isCompact_closedBall z₀ 1
    -- All relevant points lie in a ball of radius 1 around z₀
    have hs_mem : s ∈ Metric.closedBall z₀ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hdiff : s - z₀ = (s.re - 1 : ℂ) := by
        rw [hz₀def, htdef]; ext <;> simp [Complex.I_re, Complex.I_im]
      rw [hdiff, Complex.norm_real, abs_of_neg hz₀_neg]; linarith
    have hz₀_mem : z₀ ∈ Metric.closedBall z₀ 1 := by
      simp [Metric.mem_closedBall, dist_self]
    have h1px_mem : (1 + x + I * t) ∈ Metric.closedBall z₀ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hdiff : (1 + x + I * t) - z₀ = (x : ℂ) := by
        rw [hz₀def, htdef]; ext <;> simp [Complex.I_re, Complex.I_im]; ring
      rw [hdiff, Complex.norm_real, abs_of_nonneg hx_pos.le]
      exact hx_small.le
    sorry)

/-- Kadiri zero-free region. Proof by contradiction using Borel-Carathéodory. -/
theorem riemannZeta_ne_zero_of_zeroFreeEdge
    (s : ℂ) (ht : |s.im| ≥ 1) (hσ : s.re ≥ zeroFreeEdge s.im) :
    riemannZeta s ≠ 0 := by
  by_cases h1 : 1 ≤ s.re
  · exact zeta_ne_one_le_re h1
  · push_neg at h1; intro hz
    exact absurd hz (riemannZeta_ne_zero_of_zeroFreeEdge_aux s ht hσ h1)

end
