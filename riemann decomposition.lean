/-!
# RHMaster — block 1/5

Core tail-lower-bound machinery and corrected hard-difference tail route.

This block is intended to be appended after the original file.
-/

noncomputable section
open Complex

namespace RHMaster
namespace Core

/-!
## 1. Generic tail lower-bound shapes
-/

/-- A lower bound for a function in the right tail strip.

For `z = r + i y`, with

  r > 10,
  -1/2 < y < 1/2,
  y ≠ 0,

this asks for

  m r y ≤ ‖f z‖.
-/
structure TailLowerShape (f : ℂ → ℂ) where
  m : ℝ → ℝ → ℝ
  m_pos :
    ∀ r y : ℝ,
      10 ≤ r →
      -(1 / 2 : ℝ) < y →
      y < (1 / 2 : ℝ) →
      y ≠ 0 →
      0 < m r y
  bound :
    ∀ z : ℂ,
      10 < z.re →
      -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) →
      z.im ≠ 0 →
      m z.re z.im ≤ ‖f z‖

/-- An upper bound for a function in the right tail strip. -/
structure TailUpperShape (f : ℂ → ℂ) where
  u : ℝ → ℝ → ℝ
  u_nonneg :
    ∀ r y : ℝ,
      10 ≤ r →
      -(1 / 2 : ℝ) < y →
      y < (1 / 2 : ℝ) →
      y ≠ 0 →
      0 ≤ u r y
  bound :
    ∀ z : ℂ,
      10 < z.re →
      -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) →
      z.im ≠ 0 →
      ‖f z‖ ≤ u z.re z.im

/-- An explicit lower-bound shape:

  c * |y| / (r + 1)^M ≤ ‖f z‖.
-/
structure ExplicitTailLowerShape (f : ℂ → ℂ) where
  c : ℝ
  M : ℝ
  c_pos : 0 < c
  bound :
    ∀ z : ℂ,
      10 < z.re →
      -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) →
      z.im ≠ 0 →
      c * |z.im| / (z.re + 1) ^ M ≤ ‖f z‖

/-- Convert an explicit lower-bound shape into a general tail lower shape. -/
def tailLowerShape_from_explicit
    {f : ℂ → ℂ}
    (E : ExplicitTailLowerShape f) :
    TailLowerShape f where
  m r y := E.c * |y| / (r + 1) ^ E.M
  m_pos r y hr hgt hlt hne := by
    have hy : 0 < |y| := abs_pos.mpr hne
    positivity
  bound := E.bound

/-!
## 2. Product combination of lower bounds
-/

/-- If `f = g * h`, lower bounds for `g` and `h` multiply. -/
def tailLowerShape_mul
    {f g : ℂ → ℂ}
    (F : TailLowerShape f)
    (G : TailLowerShape g) :
    TailLowerShape (fun z => f z * g z) where
  m r y := F.m r y * G.m r y
  m_pos r y hr hgt hlt hne :=
    mul_pos
      (F.m_pos r y hr hgt hlt hne)
      (G.m_pos r y hr hgt hlt hne)
  bound z hre hgt hlt hne := by
    have hf := F.bound z hre hgt hlt hne
    have hg := G.bound z hre hgt hlt hne
    calc
      F.m z.re z.im * G.m z.re z.im ≤
          ‖f z‖ * ‖g z‖ := by
        exact
          mul_le_mul
            hf
            hg
            (le_of_lt (G.m_pos z.re z.im (le_of_lt hre) hgt hlt hne))
            (by positivity)
      _ = ‖f z * g z‖ := by
        rw [norm_mul]

/-!
## 3. Shifted zeta and prefactor functions
-/

def zetaFun (z : ℂ) : ℂ :=
  zeta (shiftedS z)

def prefactorFun (z : ℂ) : ℂ :=
  classicalXiPrefactor (shiftedS z)

theorem xiShifted_eq_prefactor_zeta (z : ℂ) :
    xiShifted z = prefactorFun z * zetaFun z := by
  simp [
    xiShifted,
    shiftedS,
    classicalXi,
    XiFromPrefactor,
    prefactorFun,
    zetaFun
  ]

/-- Lower bound for `xiShifted` from lower bounds for prefactor and ζ. -/
def xiTailLower_from_prefactor_zeta
    (P : TailLowerShape prefactorFun)
    (Z : TailLowerShape zetaFun) :
    TailLowerShape xiShifted := by
  have prod := tailLowerShape_mul P Z
  refine { m := prod.m, m_pos := prod.m_pos, bound := ?_ }
  intro z hre hgt hlt hne
  have := prod.bound z hre hgt hlt hne
  simpa [xiShifted_eq_prefactor_zeta z, prefactorFun, zetaFun] using this

/-!
## 4. Convert tail lower shape into existing RH tail certificate
-/

def distanceLower_from_tailLowerShape
    (S : TailLowerShape xiShifted) :
    XiRightTailDistanceLowerBoundForX 10 := by
  classical
  let lower (r y : ℝ) : ℝ :=
    if h : -(1 / 2 : ℝ) < y ∧ y < (1 / 2 : ℝ) then
      S.m r y
    else
      1
  refine { lower := lower, lower_pos := ?_, bound := ?_ }
  · intro r y hr hy
    by_cases h : -(1 / 2 : ℝ) < y ∧ y < (1 / 2 : ℝ)
    · simp [lower, h]
      exact S.m_pos r y hr h.1 h.2 hy
    · simp [lower, h]
      norm_num
  · intro z hre hgt hlt hne
    have h : -(1 / 2 : ℝ) < z.im ∧ z.im < (1 / 2 : ℝ) := ⟨hgt, hlt⟩
    simpa [lower, h] using S.bound z hre hgt hlt hne

/-!
## 5. Corrected hard-difference tail route
-/

noncomputable def invD (z : ℂ) : ℂ :=
  1 / (z ^ 2 + (1 / 4 : ℂ))

noncomputable def hardDifference (z : ℂ) : ℂ :=
  invD z - completedRiemannZeta₀ (shiftedS z)

theorem xiShifted_eq_half_D_mul_hardDifference
    (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im)
    (hlt : z.im < (1 / 2 : ℝ))
    (hne : z.im ≠ 0) :
    xiShifted z =
      (z ^ 2 + (1 / 4 : ℂ)) / 2 * hardDifference z := by
  have h :=
    inv_D_sub_completedZeta_eq_two_xiShifted_div_D z hgt hlt hne
  have hD : z ^ 2 + (1 / 4 : ℂ) ≠ 0 :=
    shifted_denominator_ne_zero_inside_strip z hgt hlt
  dsimp [hardDifference, invD] at h ⊢
  have hcalc :
      (z ^ 2 + (1 / 4 : ℂ)) / 2 *
        (1 / (z ^ 2 + (1 / 4 : ℂ)) -
          completedRiemannZeta₀ (shiftedS z)) =
        xiShifted z := by
    rw [h]
    field_simp [hD]
  exact hcalc.symm

theorem norm_xiShifted_eq_half_normD_mul_norm_hardDifference
    (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im)
    (hlt : z.im < (1 / 2 : ℝ))
    (hne : z.im ≠ 0) :
    ‖xiShifted z‖ =
      (‖z ^ 2 + (1 / 4 : ℂ)‖ / 2) * ‖hardDifference z‖ := by
  rw [xiShifted_eq_half_D_mul_hardDifference z hgt hlt hne]
  rw [norm_mul]
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    simp [Complex.norm_eq_abs, Complex.abs_ofReal]
    norm_num
  simp [norm_div, h2]

/-- Quantitative lower bound for the hard difference. -/
structure HardDifferenceTailLower where
  m : ℝ → ℝ → ℝ
  m_pos :
    ∀ r y : ℝ,
      10 ≤ r →
      -(1 / 2 : ℝ) < y →
      y < (1 / 2 : ℝ) →
      y ≠ 0 →
      0 < m r y
  bound :
    ∀ z : ℂ,
      10 < z.re →
      -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) →
      z.im ≠ 0 →
      m z.re z.im ≤ ‖hardDifference z‖

/-- Convert a hard-difference lower bound into an `xiShifted` lower bound. -/
def tailLowerShape_from_hardDifference
    (H : HardDifferenceTailLower) :
    TailLowerShape xiShifted where
  m r y := (‖tailD r y‖ / 2) * H.m r y
  m_pos r y hr hgt hlt hne := by
    have hD : 0 < ‖tailD r y‖ :=
      norm_pos_iff.mpr (tailD_ne_zero_of_strip r y hr hgt hlt)
    have hm := H.m_pos r y hr hgt hlt hne
    positivity
  bound z hre hgt hlt hne := by
    have hnorm :=
      norm_xiShifted_eq_half_normD_mul_norm_hardDifference z hgt hlt hne
    have hm := H.bound z hre hgt hlt hne
    have hDnorm :
        ‖tailD z.re z.im‖ = ‖z ^ 2 + (1 / 4 : ℂ)‖ := by
      simp [tailD, Complex.re_add_im, mul_comm I]
    calc
      (‖tailD z.re z.im‖ / 2) * H.m z.re z.im ≤
          (‖tailD z.re z.im‖ / 2) * ‖hardDifference z‖ := by
        exact mul_le_mul_of_nonneg_left hm (by positivity)
      _ =
          (‖z ^ 2 + (1 / 4 : ℂ)‖ / 2) * ‖hardDifference z‖ := by
        rw [hDnorm]
      _ = ‖xiShifted z‖ := by
        rw [← hnorm]

/-!
## 6. Bounded first-quadrant conversion
-/

/-- Convert the existing simple bounded first-quadrant evidence into
`RemainingQuadrantNonvanishing 10`.
-/
def remainingQuadrant_from_simple_bounded
    {ε η : ℝ}
    (P : SimpleFirstQuadrantRectangularBoundedProof 10 ε η) :
    RemainingQuadrantNonvanishing 10 where
  no_zero := by
    intro z hx0 hx1 hy0 hy1
    exact
      firstQuadrant_no_zero_of_bounded_proof
        (firstQuadrantBoundedZeroFreeProof_from_rectangular
          (firstQuadrantRectangularBoundedProof_of_evidenced
            (evidencedFirstQuadrantRectangularBoundedProof_from_simple P)))
        z
        hx0 hx1 hy0 hy1

/-!
## 7. Top-level RH assembly from bounded evidence + tail lower shape
-/

theorem rh_from_simple_bounded_and_tailLowerShape
    {ε η : ℝ}
    (P : SimpleFirstQuadrantRectangularBoundedProof 10 ε η)
    (T : TailLowerShape xiShifted) :
    RiemannHypothesisProp :=
  rh_from_remaining_rh_proof
    {
      quadrant := remainingQuadrant_from_simple_bounded P
      tail := distanceLower_from_tailLowerShape T
    }

theorem rh_from_simple_bounded_and_hardDifferenceTail
    {ε η : ℝ}
    (P : SimpleFirstQuadrantRectangularBoundedProof 10 ε η)
    (H : HardDifferenceTailLower) :
    RiemannHypothesisProp :=
  rh_from_simple_bounded_and_tailLowerShape
    P
    (tailLowerShape_from_hardDifference H)

/-!
## 8. Convenience aliases and capstone plan for this block
-/

abbrev XiTailLowerShape := TailLowerShape xiShifted
abbrev ZetaTailLowerShape := TailLowerShape zetaFun
abbrev PrefactorTailLowerShape := TailLowerShape prefactorFun

/-- Plan A: bounded evidence + corrected hard-difference tail. -/
structure RHPlanViaHardDifference10 (ε η : ℝ) where
  bounded : SimpleFirstQuadrantRectangularBoundedProof 10 ε η
  tail : HardDifferenceTailLower

theorem rh_from_plan_via_hard_difference
    {ε η : ℝ}
    (P : RHPlanViaHardDifference10 ε η) :
    RiemannHypothesisProp :=
  rh_from_simple_bounded_and_hardDifferenceTail
    P.bounded
    P.tail

end Core
end RHMaster

end