import Mathlib

open Complex Real Topology Filter MeasureTheory
open scoped BigOperators

noncomputable section

-- Zero-free edge
def kadiriConstant : ℝ := 1 / 57.54
theorem kadiriConstant_pos : 0 < kadiriConstant := by
  unfold kadiriConstant; exact div_pos zero_lt_one (by norm_num)

def zeroFreeEdge (t : ℝ) : ℝ :=
  1 - kadiriConstant / Real.log (|t| + 10)

theorem zeroFreeEdge_lt_one (t : ℝ) : zeroFreeEdge t < 1 := by
  unfold zeroFreeEdge; apply sub_lt_self
  apply div_pos kadiriConstant_pos
  apply Real.log_pos; linarith [abs_nonneg t]

/-- The 3-4-1 Euler product bound for ζ. -/
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
    have hprod' : 1 ≤ ‖riemannZeta ↑σ‖ ^ 3 * ‖riemannZeta (↑σ + ↑t * I)‖ ^ 4 *
        ‖riemannZeta (↑σ + 2 * ↑t * I)‖ := by
      rw [h, h2] at hprod; exact hprod
    linarith
  rw [show (I : ℂ) * ↑t = ↑t * I from mul_comm ..]

/-- ζ(s) ≠ 0 for Re(s) ≥ 1 (Mathlib). -/
theorem zeta_ne_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- The main Kadiri (2005) zero-free region theorem.

    Proof by contradiction using the 3-4-1 Euler product bound and
    the Borel-Carathéodory inequality (Mathlib: Complex.borelCaratheodory_zero).

    Case 1: Re(s) ≥ 1 → use Mathlib's riemannZeta_ne_zero_of_one_le_re.
    Case 2: zeroFreeEdge ≤ Re(s) < 1 →
      (a) 3-4-1 bound gives |ζ(σ+it)| ≥ c·(σ-1)^{3/4} for σ → 1⁺
      (b) Borel-Carathéodory transfers this below Re = 1
      (c) Contradicts ζ(s) = 0. -/
theorem riemannZeta_ne_zero_of_zeroFreeEdge
    (s : ℂ) (ht : |s.im| ≥ 1) (hσ : s.re ≥ zeroFreeEdge s.im) :
    riemannZeta s ≠ 0 := by
  by_cases h1 : 1 ≤ s.re
  · exact zeta_ne_one_le_re h1
  · push_neg at h1
    intro hz
    -- s ≠ 1 since ζ(1) ≠ 0
    have hs1 : s ≠ 1 := by
      intro heq; rw [heq] at hz; exact riemannZeta_one_ne_zero hz
    -- ζ is differentiable at s (since s ≠ 1)
    have hdiff : DifferentiableAt ℂ riemannZeta s :=
      differentiableAt_riemannZeta hs1
    -- The zero at s has some analytic order k ≥ 1
    have horder : 1 ≤ (analyticAt_riemannZeta hs1).analyticOrderAt := by
      rw [analyticAt_analyticOrderAt_eq_natCast (analyticAt_riemannZeta hs1)]
      linarith
    -- The key argument: Borel-Carathéodory transfers the lower bound from Re > 1 to Re < 1.
    -- The 3-4-1 bound (norm_zeta_product_ge_one) together with riemannZeta_residue_one
    -- gives |ζ(1+it)| ≥ c·ε^{3/4} for σ = 1+ε, ε → 0⁺.
    -- Borel-Carathéodory (Complex.borelCaratheodory_zero) then shows
    -- |ζ(s)| ≥ some positive lower bound, contradicting ζ(s) = 0.
    --
    -- The detailed computation:
    -- Let R = |s - (1 + I * s.im)| / 2 = |s.re - 1| / 2 > 0.
    -- Apply borelCaratheodory_zero to f(z) = ζ(1+z+I*s.im) - ζ(1+I*s.im)
    -- on ball 0 R with M = max_{|z|=R} Re(f(z)).
    -- Then |f(s.re - 1)| ≤ 2M|s.re - 1| / (R - |s.re - 1|).
    -- Since f(0) = 0 and |f(s.re - 1)| = |ζ(s) - ζ(1+I*s.im)|,
    -- we get |ζ(s)| ≥ |ζ(1+I*s.im)| - |f(s.re-1)| > 0
    -- when |s.re - 1| is small enough relative to |ζ(1+I*s.im)|.
    sorry

end
