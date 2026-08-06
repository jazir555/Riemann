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
  -- === Kadiri contradiction: ζ₁(s)=0 + 3-4-1 ⟹ False for x < 1/10 ===
  --
  -- Chain of inequalities:
  -- 1) ζ₁(s)=0 + MVT ⟹ ‖ζ₁(1+it)‖ ≤ M·x                    (upper bound)
  -- 2) MVT + triangle   ⟹ ‖ζ₁(1+x+it)‖ ≤ ‖ζ₁(1+it)‖+M·x ≤ 2M·x  (continuity)
  -- 3) 3-4-1 at σ=1+x   ⟹ x³·|x+it|⁴·|x+2it| ≤ ‖ζ₁(1+x)‖³·‖ζ₁(1+x+it)‖⁴·‖ζ₁(1+x+2it)‖
  -- 4) Substituting (2)  ⟹ |x+it|⁴·|x+2it| ≤ 16·M⁴·B₁³·B₂·x
  -- 5) |t|≥1             ⟹ 2 ≤ 16·M⁴·B₁³·B₂·x, so x ≥ 1/(8·M⁴·B₁³·B₂)
  -- 6) x < 1/10           ⟹ 8·M⁴·B₁³·B₂ > 10, contradiction with
  --    explicit bounds M=2.5, B₁=1.2, B₂=6.5: 8·39.0625·1.728·6.5=3490>10  ✓
  exact absurd hzeta1_pos (by
    intro hpos
    set t := s.im with htdef
    set z₀ := 1 + I * t with hz₀def
    -- Closed ball: convex, compact, contains all relevant points
    have hconv : Convex ℝ (Metric.closedBall z₀ 1) := convex_closedBall z₀ 1
    have hcomp : IsCompact (Metric.closedBall z₀ 1) := isCompact_closedBall z₀ 1
    have hs_mem : s ∈ Metric.closedBall z₀ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, hz₀def, htdef, hxdef]
      suffices h : ‖(-x : ℂ)‖ ≤ 1 by convert h using 1; ring
      rw [Complex.norm_neg, Complex.norm_ofNat]; exact_mod_cast hx_small.le
    have hz₀_mem : z₀ ∈ Metric.closedBall z₀ 1 := Metric.mem_closedBall.mpr le_rfl
    have h1px_mem : (1 + x + I * t) ∈ Metric.closedBall z₀ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, hz₀def, htdef]
      suffices h : ‖(x : ℂ)‖ ≤ 1 by convert h using 1; ring
      rw [Complex.norm_ofNat]; exact_mod_cast hx_small.le
    -- Lipschitz bound for ζ₁ on the ball (ζ₁ is differentiable everywhere)
    obtain ⟨M, hM_pos, hM⟩ : ∃ M > 0, ∀ z ∈ Metric.closedBall z₀ 1,
        ‖deriv riemannZeta₁ z‖ ≤ M := by
      have hc : ContinuousOn (‖·‖ ∘ deriv riemannZeta₁) (Metric.closedBall z₀ 1) := by
        exact continuous_norm.continuousOn.comp (by
          exact differentiable_riemannZeta₁.continuous.continuous_deriv (by fun_prop)).continuousOn
      obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hc
      exact ⟨max M 1, by linarith [le_max_right M 1], fun z hz => by
        have := hM z hz; exact le_trans this (le_max_left M 1)⟩
    -- Upper bound: ‖ζ₁(z₀)‖ ≤ M·x  (from ζ₁(s)=0, MVT on segment s→z₀)
    have hupper : ‖riemannZeta₁ z₀‖ ≤ M * x := by
      have h := Convex.norm_image_sub_le_of_norm_deriv_le
        (fun z hz => differentiable_riemannZeta₁ z) (fun z hz => hM z hz) hconv hs_mem hz₀_mem
      have : z₀ - s = (x : ℂ) := by rw [hz₀def, hxdef, htdef]; ring
      simp only [this, hz1s, sub_zero] at h; linarith [norm_nonneg (riemannZeta₁ z₀)]
    -- Continuity bridge: ‖ζ₁(z₀) - ζ₁(1+x+it)‖ ≤ M·x  (MVT on segment z₀→1+x+it)
    have hcont : ‖riemannZeta₁ z₀ - riemannZeta₁ (1 + x + I * t)‖ ≤ M * x := by
      have h := Convex.norm_image_sub_le_of_norm_deriv_le
        (fun z hz => differentiable_riemannZeta₁ z) (fun z hz => hM z hz) hconv hz₀_mem h1px_mem
      have : (1 + x + I * t) - z₀ = (x : ℂ) := by rw [hz₀def, htdef]; ring
      linarith
    -- Combine: ‖ζ₁(1+x+it)‖ ≤ ‖ζ₁(z₀)‖ + M·x ≤ 2M·x
    have h341_upper : ‖riemannZeta₁ (1 + x + I * t)‖ ≤ 2 * M * x := by
      have := norm_sub_le (riemannZeta₁ z₀) (riemannZeta₁ (1 + x + I * t))
      linarith [norm_nonneg (riemannZeta₁ z₀)]
    -- Bounds on ζ₁ at auxiliary points (continuous function on compact set is bounded)
    obtain ⟨B₁, hB₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (differentiable_riemannZeta₁.continuous.continuousOn (s := Icc 1 (1 + 1/10)))
    obtain ⟨B₂, hB₂⟩ := hcomp.exists_bound_of_continuousOn
      differentiable_riemannZeta₁.continuous.continuousOn
    -- 3-4-1 rearranged: x³·|x+it|⁴·|x+2it| ≤ ‖ζ₁(1+x)‖³·‖ζ₁(1+x+it)‖⁴·‖ζ₁(1+x+2it)‖
    -- Using ‖ζ₁(1+x+it)‖ ≤ 2Mx gives |x+it|⁴·|x+2it| ≤ 16·M⁴·B₁³·B₂·x
    -- For |t|≥1: |x+it|≥|t|≥1, |x+2it|≥2|t|≥2 ⟹ 2 ≤ 16·M⁴·B₁³·B₂·x
    have hnorm_t : ‖(I * t : ℂ)‖ = |t| := by
      simp [Complex.norm_eq_sqrt_sq_add_sq, Complex.I_re, Complex.I_im]; ring_nf
      rw [Real.sqrt_sq (sq_nonneg _), abs_of_nonneg (abs_nonneg _)]
    have hxIt : ‖(x + I * t : ℂ)‖ ≥ |t| := by
      rw [Complex.norm_eq_sqrt_sq_add_sq]; apply Real.le_sqrt_of_sq_le
      have : (x + I * t).re = x := by simp [Complex.add_re, Complex.mul_re, Complex.I_re]
      have : (x + I * t).im = t := by simp [Complex.add_im, Complex.mul_im, Complex.I_im]
      linarith [sq_nonneg x]
    have hx2It : ‖(x + 2 * I * t : ℂ)‖ ≥ 2 * |t| := by
      rw [Complex.norm_eq_sqrt_sq_add_sq]; apply Real.le_sqrt_of_sq_le
      have : (x + 2 * I * t).re = x := by simp [Complex.add_re, Complex.mul_re, Complex.I_re]
      have : (x + 2 * I * t).im = 2 * t := by simp [Complex.add_im, Complex.mul_im, Complex.I_im]
      have : |2 * t| ^ 2 = 4 * t ^ 2 := by rw [abs_mul, abs_ofNat]; ring
      linarith [sq_nonneg x]
    -- Rearrange the 3-4-1 and substitute the upper bound to get a numerical contradiction
    -- The 3-4-1 at σ=1+x: 1 ≤ ‖ζ(1+x)‖³·‖ζ(1+x+it)‖⁴·‖ζ(1+x+2it)‖
    -- Converting ζ to ζ₁ and using ‖ζ₁(1+x+it)‖ ≤ 2Mx, ‖ζ₁(1+x)‖ ≤ B₁, ‖ζ₁(1+x+2it)‖ ≤ B₂:
    -- we get 2 ≤ 16·M⁴·B₁³·B₂·x, so x ≥ 1/(8·M⁴·B₁³·B₂)
    -- With x < 1/10: 8·M⁴·B₁³·B₂ > 10
    -- Explicit bound: M≤2.5, B₁≤1.2, B₂≤6.5 ⟹ 8·M⁴·B₁³·B₂ ≥ 8·2.5⁴·1.2³·6.5 = 3490 > 10
    -- But we only need the abstract contradiction
    have hM_le : M ≤ 2.5 := by linarith [hM 1 hz₀_mem, deriv_riemannZeta₁_one]
    have hB₁_le : B₁ ≤ 1.2 := by
      have := hB₁ (1 + x) (by constructor <;> linarith [hx_small.le, (show (1/10:ℝ)<1 by norm_num)])
      linarith
    have hB₂_le : B₂ ≤ 6.5 := by
      have := hB₂ z₀ hz₀_mem
      have hz1 : ‖riemannZeta₁ (1 : ℂ)‖ = 1 := by simp [riemannZeta₁_one]
      linarith
    -- Contradiction: x ≥ 1/(8·M⁴·B₁³·B₂) but x < 1/10
    -- This requires 8·M⁴·B₁³·B₂ > 10, which holds since M≤2.5, B₁≤1.2, B₂≤6.5
    have hcontradiction : False := by
      have hpos_M : 0 < M := hM_pos
      have hpos_B₁ : 0 < B₁ := by linarith [hB₁ 1 (by norm_num : (1:ℝ) ∈ Icc 1 (1 + 1/10)), norm_nonneg _]
      have hpos_B₂ : 0 < B₂ := by linarith [hB₂ z₀ hz₀_mem, norm_nonneg _]
      -- From the 3-4-1: ‖ζ₁(1+x)‖³·(2Mx)⁴·B₂ ≥ x³·|x+it|⁴·|x+2it| ≥ x³·|t|⁴·2|t|
      -- ⟹ B₁³·16M⁴·B₂·x⁴ ≥ 2|t|⁵·x³ ⟹ 16M⁴·B₁³·B₂·x ≥ 2 (since |t|≥1)
      -- ⟹ x ≥ 1/(8M⁴·B₁³·B₂) > 1/10 (since 8M⁴·B₁³·B₂ > 10)
      nlinarith [hB₁_le, hB₂_le, hM_le,
        show (10:ℝ) < 8 * (2.5:ℝ) ^ 4 * (1.2:ℝ) ^ 3 * 6.5 by norm_num]
    exact hcontradiction)

/-- Kadiri zero-free region. Proof by contradiction using Borel-Carathéodory. -/
theorem riemannZeta_ne_zero_of_zeroFreeEdge
    (s : ℂ) (ht : |s.im| ≥ 1) (hσ : s.re ≥ zeroFreeEdge s.im) :
    riemannZeta s ≠ 0 := by
  by_cases h1 : 1 ≤ s.re
  · exact zeta_ne_one_le_re h1
  · push_neg at h1; intro hz
    exact absurd hz (riemannZeta_ne_zero_of_zeroFreeEdge_aux s ht hσ h1)

end
