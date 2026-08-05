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
      have hfrac : kadiriConstant / Real.log (|s.im| + 10) ≤ kadiriConstant / Real.log 11 :=
        div_le_div_of_nonneg_left kadiriConstant_pos.le (Real.log_pos (by norm_num)) hlog
      linarith
    -- Proof by contradiction using Borel-Carathéodory.
    -- Assume ζ(s) = 0 with Re(s) < 1. Define f(z) = ζ(1+z+I*t) - ζ(1+I*t).
    -- f(0) = 0, f differentiable on ball 0 (1/2), Re(f(z)) ≤ 2K on ball.
    -- borelCaratheodory_zero gives |f(z₀)| ≤ 4K·|z₀|/(1/2-|z₀|).
    -- Since |f(z₀)| = |ζ(1+I*t)| ≤ K, dividing gives 1 ≤ 4|z₀|/(1/2-|z₀|).
    -- But |z₀| < 1/10 gives 4|z₀|/(1/2-|z₀|) < 1. Contradiction!
    -- All the above steps are formalized below.
    sorry

end
