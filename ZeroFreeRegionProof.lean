import Mathlib

open Complex Real Topology Filter MeasureTheory
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

/-- Kadiri zero-free region. Proof by contradiction using Borel-Carathéodory. -/
theorem riemannZeta_ne_zero_of_zeroFreeEdge
    (s : ℂ) (ht : |s.im| ≥ 1) (hσ : s.re ≥ zeroFreeEdge s.im) :
    riemannZeta s ≠ 0 := by
  by_cases h1 : 1 ≤ s.re
  · exact zeta_ne_one_le_re h1
  · push_neg at h1; intro hz
    have hs1 : s ≠ 1 := by intro heq; rw [heq] at hz; exact riemannZeta_one_ne_zero hz
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
    -- Define f(z) = ζ(1+z+I*t) - ζ(1+I*t)
    let f : ℂ → ℂ := fun z => riemannZeta (1 + z + I * s.im) - riemannZeta (1 + I * s.im)
    have hf0 : f 0 = 0 := by unfold f; show riemannZeta _ - riemannZeta _ = 0; ring_nf
    -- f differentiable on ball 0 (1/2)
    have hdiff : DifferentiableOn ℂ f (Metric.ball 0 (1/2 : ℝ)) := by
      intro z hz
      have hne2 : 1 + I * s.im ≠ 1 := by
        intro heq
        have : (I : ℂ) * ↑s.im = 0 := by linear_combination heq
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h Complex.I_ne_zero
        · have : (s.im : ℝ) = 0 := Complex.ofReal_injective h
          rw [this, abs_zero] at ht₀; linarith
      have hne1 : 1 + z + I * s.im ≠ 1 := by
        intro heq
        have hzt : z + I * s.im = 0 := by linear_combination heq
        have hzn : ‖z‖ = |s.im| := by
          have := congr_arg (‖·‖ : ℂ → ℝ) (show z = -(I * s.im : ℂ) from by linear_combination hzt)
          simp [norm_neg, Complex.norm_mul, Complex.norm_I] at this; exact this
        have hball : dist z 0 < 1/2 := Metric.mem_ball.mp hz
        have hz_norm : ‖z‖ < (1/2 : ℝ) := by rwa [dist_eq_norm, sub_zero] at hball
        by_cases ht_nonneg : 0 ≤ s.im
        · rw [abs_of_nonneg ht_nonneg] at ht₀ hzn; linarith
        · rw [abs_of_neg (by linarith)] at ht₀ hzn; linarith
      unfold f
      have h1 : DifferentiableAt ℂ (fun w => riemannZeta (1 + w + I * s.im)) z :=
        (differentiableAt_riemannZeta hne1).comp z (by fun_prop)
      have h2 : DifferentiableAt ℂ (fun _ => riemannZeta (1 + I * s.im)) z :=
        differentiableAt_const _
      exact (h1.sub h2).differentiableWithinAt
    -- z₀ = s.re - 1 in ball 0 (1/2)
    have hz₀_mem : (↑(s.re - 1) : ℂ) ∈ Metric.ball 0 (1/2 : ℝ) := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      simp only [RCLike.norm_ofReal, abs_of_neg hz₀_neg]
      linarith
    -- f(z₀) = -ζ(1+I*t)
    have hfz₀ : f ↑(s.re - 1) = -riemannZeta (1 + I * s.im) := by
      unfold f
      have hmain : (1 : ℂ) + ↑(s.re - 1) + I * ↑s.im = s := by
        rw [Complex.ext_iff]; constructor
        · push_cast; ring_nf
        · push_cast; ring_nf
      rw [hmain, hz, zero_sub]
    -- K = max |ζ(1+w+I*t)| on closed ball, achieved by extreme value theorem
    have hcomp : IsCompact (Metric.closedBall (0 : ℂ) (1/2 : ℝ)) :=
      isCompact_closedBall 0 (1/2 : ℝ)
    have hcont : Continuous (fun z : ℂ => ‖riemannZeta (1 + z + I * s.im)‖) := by
      refine continuous_norm.comp ?_
      refine differentiableOn_riemannZeta.continuousOn.comp_continuous
        (continuous_const.add (continuous_id.mul continuous_const)) ?_
      intro z hz
      intro heq
      have hzt : z + I * s.im = 0 := by linear_combination heq
      have hzn : ‖z‖ = |s.im| := by
        have := congr_arg (‖·‖ : ℂ → ℝ) (show z = -(I * s.im : ℂ) from by linear_combination hzt)
        simp [norm_neg, Complex.norm_mul, Complex.norm_I] at this; exact this
      by_cases ht_nonneg : 0 ≤ s.im
      · rw [abs_of_nonneg ht_nonneg] at ht₀ hzn; linarith
      · rw [abs_of_neg (by linarith)] at ht₀ hzn; linarith
    obtain ⟨K, hK_mem, hK⟩ := hcomp.exists_isMaxOn
      (Set.nonempty_of_mem (Set.mem_closedBall_self (by norm_num : (0:ℝ) < 1/2))) hcont
    -- M = |ζ(1+K+I*t)| ≥ |ζ(1+I*t)| > 0
    have hK_pos : ‖riemannZeta (1 + K + I * s.im)‖ > 0 := by
      have := hK 0 (Set.mem_closedBall_self (by norm_num : (0:ℝ) < 1/2))
      have : ‖riemannZeta (1 + I * s.im)‖ > 0 :=
        norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by linarith))
      linarith
    -- Re(f(z)) ≤ 2 * M on ball where M = max |ζ|
    have hM : ∀ z ∈ Metric.ball 0 (1/2 : ℝ), (f z).re ≤ 2 * ‖riemannZeta (1 + K + I * s.im)‖ := by
      intro z hz
      have hzball : z ∈ Metric.closedBall 0 (1/2 : ℝ) :=
        Metric.closedBall_mem_closedBall (by norm_num : (0:ℝ) ≤ 1/2) (Metric.mem_ball.mp hz |>.le)
      have h1 := hK z hzball
      have h2 := hK 0 (Set.mem_closedBall_self (by norm_num : (0:ℝ) < 1/2))
      unfold f at *
      have hnf := norm_sub_le (riemannZeta (1 + z + I * s.im)) (riemannZeta (1 + I * s.im))
      have har := Complex.abs_re_le_abs ((riemannZeta (1 + z + I * s.im)) - (riemannZeta (1 + I * s.im)))
      linarith
    -- Apply Borel-Carathéodory
    have hM_pos : (0 : ℝ) < ‖riemannZeta (1 + K + I * s.im)‖ := hK_pos
    have hbc := Complex.borelCaratheodory_zero hM_pos hdiff hM
      (by norm_num : (0:ℝ) < 1/2) hz₀_mem hf0
    have hfz₀_norm : ‖f ↑(s.re - 1)‖ = ‖riemannZeta (1 + I * s.im)‖ := by
      simp only [hfz₀, norm_neg]
    have hfz₀_le_M : ‖f ↑(s.re - 1)‖ ≤ ‖riemannZeta (1 + K + I * s.im)‖ :=
      hfz₀_norm ▸ hK 0 (Set.mem_closedBall_self (by norm_num : (0:ℝ) < 1/2))
    have hz₀_norm : ‖(↑(s.re - 1) : ℂ)‖ = 1 - s.re := by
      simp only [RCLike.norm_ofReal, abs_of_neg hz₀_neg]
    -- The contradiction
    have h_bnd : ‖f ↑(s.re - 1)‖ ≤ 4 * ‖riemannZeta (1 + K + I * s.im)‖ * (1 - s.re) / ((1/2 : ℝ) - (1 - s.re)) := by
      rw [hz₀_norm] at hbc; exact hbc
    have hK_le : ‖riemannZeta (1 + K + I * s.im)‖ ≤ 4 * ‖riemannZeta (1 + K + I * s.im)‖ * (1 - s.re) / ((1/2 : ℝ) - (1 - s.re)) :=
      le_trans hfz₀_le_M h_bnd
    have h1_le : 1 ≤ 4 * (1 - s.re) / ((1/2 : ℝ) - (1 - s.re)) := by linarith
    have h4lt : 4 * (1 - s.re) / ((1/2 : ℝ) - (1 - s.re)) < 1 := by
      have hpos : 0 < (1/2 : ℝ) - (1 - s.re) := by linarith
      rw [div_lt_one hpos]; linarith
    linarith

end
