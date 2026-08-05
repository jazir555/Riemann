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

/-- Kadiri zero-free region: ζ(s) ≠ 0 for Re(s) ≥ zeroFreeEdge(Im(s)).

    Proof by Borel-Carathéodory contradiction. -/
theorem riemannZeta_ne_zero_of_zeroFreeEdge
    (s : ℂ) (ht : |s.im| ≥ 1) (hσ : s.re ≥ zeroFreeEdge s.im) :
    riemannZeta s ≠ 0 := by
  by_cases h1 : 1 ≤ s.re
  · exact zeta_ne_one_le_re h1
  · push_neg at h1; intro hz
    have hs1 : s ≠ 1 := by intro heq; rw [heq] at hz; exact riemannZeta_one_ne_zero hz
    -- Key setup
    let t := s.im
    have ht₀ : (1 : ℝ) ≤ |t| := ht
    let R : ℝ := 1 / 2
    have hR_pos : 0 < R := by norm_num
    have hz₀_neg : s.re - 1 < 0 := by linarith
    -- 1-s.re is small
    have hgap_lt : 1 - s.re < R / 5 := by
      unfold zeroFreeEdge at hσ
      have hgap : 1 - s.re ≤ kadiriConstant / Real.log (|t| + 10) := by linarith
      have hlog : Real.log (|t| + 10) ≥ Real.log 11 :=
        Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
      have hfrac := div_le_div_of_nonneg_left kadiriConstant_pos.le (Real.log_pos (by norm_num)) hlog
      have hval : kadiriConstant / Real.log 11 < (1 / 10 : ℝ) := by
        rw [div_lt_iff (Real.log_pos (by norm_num)).ne']
        unfold kadiriConstant; nlinarith [Real.log_two_pos, Real.log_le_sub_one_add (by norm_num : (0 : ℝ) < 10)]
      linarith
    -- Define f(z) = ζ(1+z+It) - ζ(1+It)
    let f : ℂ → ℂ := fun z => riemannZeta (1 + z + I * t) - riemannZeta (1 + I * t)
    have hf0 : f 0 = 0 := by simp [f]
    -- Differentiability on ball
    have hdiff : DifferentiableOn ℂ f (Metric.ball 0 R) := by
      intro z hz
      have hz' : dist z 0 < R := Metric.mem_ball.mp hz
      have hne2 : 1 + I * t ≠ 1 := by
        intro heq
        have : (I : ℂ) * ↑t = 0 := by linear_combination heq
        rcases mul_eq_zero.mp this with h | h
        · exact Complex.I_ne_zero h
        · exact absurd h (by intro h0; linarith [show (0:ℝ) < |t| from by linarith])
      have hne1 : 1 + z + I * t ≠ 1 := by
        intro heq
        have : z + I * t = 0 := by linear_combination heq
        have hzn : ‖z‖ = |t| := by
          have := congr_arg (‖·‖ : ℂ → ℝ) (show z = -(I * t : ℂ) from by linear_combination this)
          simp [norm_neg, Complex.norm_mul, Complex.norm_I] at this; exact this
        have : |t| < R := hzn ▸ (by linarith [show ‖z‖ < R from by linarith [dist_eq_norm]])
        linarith
      exact ((differentiableAt_riemannZeta hne1).sub
        (differentiableAt_riemannZeta hne2)).differentiableWithinAt
    -- z₀ in ball
    have hz₀_mem : (↑(s.re - 1) : ℂ) ∈ Metric.ball 0 R := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [Complex.norm_ofReal, abs_of_neg hz₀_neg, sub_zero]
      linarith
    -- f(z₀) = -ζ(1+It)
    have hfz₀ : f ↑(s.re - 1) = -riemannZeta (1 + I * t) := by
      unfold f
      have hmain : (1 : ℂ) + ↑(s.re - 1) + I * ↑t = s := by
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re]; ring
        · simp [Complex.add_im, Complex.mul_im]; ring
      rw [hmain, hz]; ring
    -- K = max |ζ(1+w+It)| on closed ball
    have hcont : Continuous fun z : ℂ => ‖riemannZeta (1 + z + I * t)‖ := by fun_prop
    obtain ⟨K, _, hK⟩ := (isCompact_closedBall).exists_forall_ge
      (Set.nonempty_of_mem (Set.mem_closedBall_self hR_pos.le)) hcont
    have hK_pos : 0 < K := by
      have := hK 0 (Set.mem_closedBall_self hR_pos.le)
      have : ‖riemannZeta (1 + I * t)‖ > 0 :=
        norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by linarith))
      linarith
    -- Re(f(z)) ≤ 2K on ball
    have hM : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ 2 * K := by
      intro z hz
      have hzball : ‖z‖ ≤ R := by
        have := Metric.mem_ball.mp hz; linarith [dist_eq_norm z (0:ℂ)]
      have h1 := hK z (Set.mem_closedBall_iff_norm.mpr hzball)
      have h2 := hK 0 (Set.mem_closedBall_self hR_pos.le)
      unfold f at *
      have hnf := norm_sub_le (riemannZeta (1 + z + I * t)) (riemannZeta (1 + I * t))
      have har := Complex.abs_re_le_abs ((riemannZeta (1 + z + I * t)) - (riemannZeta (1 + I * t)))
      linarith
    -- Apply Borel-Carathéodory
    have hbc := Complex.borelCaratheodory_zero (by linarith) hdiff hM hR_pos hz₀_mem hf0
    have hfz₀_norm : ‖f ↑(s.re - 1)‖ = ‖riemannZeta (1 + I * t)‖ := by
      simp [hfz₀, norm_neg]
    have hfz₀_le_K : ‖f ↑(s.re - 1)‖ ≤ K :=
      hfz₀_norm ▸ hK 0 (Set.mem_closedBall_self hR_pos.le)
    have hz₀_norm : ‖(↑(s.re - 1) : ℂ)‖ = 1 - s.re := by
      simp [Complex.norm_ofReal, abs_of_neg hz₀_neg]
    -- The contradiction
    have h_bnd : ‖f ↑(s.re - 1)‖ ≤ 4 * K * (1 - s.re) / (R - (1 - s.re)) := by
      rw [hz₀_norm] at hbc; exact hbc
    have hK_le : K ≤ 4 * K * (1 - s.re) / (R - (1 - s.re)) := le_trans hfz₀_le_K h_bnd
    have h1_le : 1 ≤ 4 * (1 - s.re) / (R - (1 - s.re)) := by linarith
    have h4lt : 4 * (1 - s.re) / (R - (1 - s.re)) < 1 := by
      have hpos : 0 < R - (1 - s.re) := by linarith
      rw [div_lt_one hpos]; linarith
    linarith

end
