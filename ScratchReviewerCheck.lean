import Mathlib

open Complex
open scoped Interval

noncomputable section

noncomputable def shiftedS (z : ℂ) : ℂ := (1 / 2 : ℂ) + I * z

noncomputable def correctedDifference (z : ℂ) : ℂ :=
  1 / (z ^ 2 + (1 / 4 : ℂ)) - completedRiemannZeta₀ (shiftedS z)

axiom polar_term_eq_inv_D
    (z : ℂ) (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ)) :
    1 / shiftedS z + 1 / (1 - shiftedS z) = 1 / (z ^ 2 + (1 / 4 : ℂ))

theorem correctedDifference_eq_neg_completedRiemannZeta
    (z : ℂ) (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ)) :
    correctedDifference z = -completedRiemannZeta (shiftedS z) := by
  unfold correctedDifference
  rw [completedRiemannZeta_eq, ← polar_term_eq_inv_D z hgt hlt]
  ring

def F (z : ℂ) : ℂ := z

noncomputable def verticalPoint (r y : ℝ) : ℂ :=
  (r : ℂ) + I * (y : ℂ)

structure Growth where
  q : ℝ → ℝ → ℝ
  q_pos : ∀ r y, 10 < |r| → 0 < y → y < (1 / 2 : ℝ) → 0 < q r y
  q_intervalIntegrable : ∀ r y, 10 < |r| → 0 < y → y < (1 / 2 : ℝ) →
    IntervalIntegrable (q r) MeasureTheory.volume 0 y
  growth : ∀ r y, 10 < |r| → 0 < y → y < (1 / 2 : ℝ) →
    (∫ u in (0 : ℝ)..y, q r u) ≤ ‖F (verticalPoint r y)‖ ^ 2

noncomputable def growthIntegral (G : Growth) (r y : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..|y|, G.q r u

theorem growthIntegral_pos (G : Growth) (r y : ℝ)
    (hr : 10 < |r|) (hy : y ≠ 0) (hylt : |y| < (1 / 2 : ℝ)) :
    0 < growthIntegral G r y := by
  unfold growthIntegral
  have habsy : 0 < |y| := abs_pos.mpr hy
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    (G.q_intervalIntegrable r |y| hr habsy hylt)
    (fun u hu => G.q_pos r u hr hu.1 (hu.2.trans hylt))
    habsy

def ConjSymm : Prop := ∀ z : ℂ, -(1 / 2 : ℝ) < z.im → z.im < (1 / 2 : ℝ) →
  F (star z) = star (F z)

theorem norm_verticalPoint_abs_eq (hsymm : ConjSymm) (r y : ℝ)
    (hgt : -(1 / 2 : ℝ) < y) (hlt : y < (1 / 2 : ℝ)) :
    ‖F (verticalPoint r |y|)‖ = ‖F (verticalPoint r y)‖ := by
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy]
  · have hyneg : y < 0 := lt_of_not_ge hy
    rw [abs_of_neg hyneg]
    have hstar : verticalPoint r (-y) = star (verticalPoint r y) := by
      apply Complex.ext <;> simp [verticalPoint]
    rw [hstar, hsymm (verticalPoint r y) (by simpa [verticalPoint] using hgt)
      (by simpa [verticalPoint] using hlt), norm_star]

theorem sqrt_growthIntegral_le_norm (G : Growth) (hsymm : ConjSymm) (r y : ℝ)
    (hr : 10 < |r|) (hgt : -(1 / 2 : ℝ) < y) (hlt : y < (1 / 2 : ℝ))
    (hy : y ≠ 0) :
    Real.sqrt (growthIntegral G r y) ≤ ‖F (verticalPoint r y)‖ := by
  have hylt : |y| < (1 / 2 : ℝ) := abs_lt.mpr ⟨hgt, hlt⟩
  have habsy : 0 < |y| := abs_pos.mpr hy
  have hgrowth := G.growth r |y| hr habsy hylt
  have hsqrt : Real.sqrt (growthIntegral G r y) ≤ ‖F (verticalPoint r |y|)‖ :=
    Real.sqrt_le_iff.mpr ⟨norm_nonneg _, by simpa [growthIntegral] using hgrowth⟩
  rw [norm_verticalPoint_abs_eq hsymm r y hgt hlt] at hsqrt
  exact hsqrt
