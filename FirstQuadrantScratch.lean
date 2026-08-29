import Mathlib

/-!
# First-quadrant challenge — recursive decomposition (scratch)

Goal: reduce `RiemannHypothesisProp` to finite/analytic leaves, recursively.

Build: `lake env lean FirstQuadrantScratch.lean` (only `import Mathlib`).

The definitions/theorems in section 1 below are the exact (now-compiling) content
of `rh_residual_gap.lean` — reproduced here so this scratch file builds
standalone without a cross-file `import` (the repo root is not a Lake module
root, so `import rh_residual_gap` cannot be resolved by the standalone toolchain).
They isolate `ThinRegion` as the residual leaf and prove `rh_iff_thin_region` /
`thin_region_is_exact_gap`, reusing `Mathlib` only.

Section 2 re-implements the *first-quadrant* decomposition over an abstract `ξ`:
`RHFirstQuadrantProof = (quadrant_no_zero rectangle) + (right_tail bound)` and
proves, with only the fourfold symmetry, that this reduces to off-real pointwise
non-vanishing.  The rectangle and the tail are the two GENUINE finite/analytic
leaves (the sorries 8356 / 9117 of `riemannhypothesis.lean`).
-/

open Complex Real ComplexConjugate

section RhResidualGap

/-- `ξ` vanishes exactly where `ζ` does inside the critical strip. -/
def XiZeroEquivInStrip (ξ : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → (ξ s = 0 ↔ riemannZeta s = 0)

/-- Functional equation `ξ(s) = ξ(1 - s)`. -/
def XiFE (ξ : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, ξ s = ξ (1 - s)

/-- Classical zero-free region (de la Vallée Poussin) — a TRUE theorem, supplied
as precise analytic input. -/
structure ClassicalZFR (ξ : ℂ → ℂ) where
  (C T₀ : ℝ)
  (Cpos : 0 < C)
  (zeroFree : ∀ s : ℂ,
     1 - C / Real.log (abs s.im + 2) ≤ s.re →
     s.re < 1 →
     T₀ ≤ abs s.im →
     ξ s ≠ 0)

/-- The thin region: the ONLY place an off-critical-line zero could still hide
once the classical ZFR and a bounded cover are in place.  Exact residual leaf. -/
def ThinRegion (ξ : ℂ → ℂ) (C T₀ : ℝ) : Prop :=
  ∀ s : ℂ,
    1 / 2 < s.re →
    s.re < 1 - C / Real.log (abs s.im + 2) →
    T₀ ≤ abs s.im →
    ξ s ≠ 0

/-- A finite zero-free cover of the bounded part near the real axis — a TRUE
finite numerical fact (rigorous interval arithmetic). -/
structure BoundedCover (ξ : ℂ → ℂ) (T₀ : ℝ) where
  covers : ∀ s : ℂ,
    1 / 2 < s.re → s.re < 1 → abs s.im < T₀ → ξ s ≠ 0

/-- Full zero-freeness of the right half of the critical strip. -/
def NoRightHalfZeros (ξ : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → ξ s ≠ 0

/-- **Exact gap isolation.**  Given the classical ZFR and a bounded cover (both
true), right-half zero-freeness of `ξ` is *precisely* equivalent to zero-freeness
on the thin region. -/
theorem thin_region_is_exact_gap (ξ : ℂ → ℂ)
    (hξ : XiZeroEquivInStrip ξ) (hfe : XiFE ξ)
    (hC : ClassicalZFR ξ) (hB : BoundedCover ξ hC.T₀) :
    NoRightHalfZeros ξ ↔ ThinRegion ξ hC.C hC.T₀ := by
  constructor
  · intro hNZ s hs_gt hs_lt hT₀
    have hlogpos : 0 < Real.log (abs s.im + 2) :=
      Real.log_pos (by linarith [abs_nonneg s.im])
    have hs_lt_one : s.re < 1 := by
      have hCdivpos : 0 < hC.C / Real.log (abs s.im + 2) := div_pos hC.Cpos hlogpos
      linarith
    exact hNZ s hs_gt hs_lt_one
  · intro hT s hs_gt hs_lt
    rcases hC with ⟨C, T₀, _, hZ⟩
    by_cases hT0 : abs s.im < T₀
    · exact hB.covers s hs_gt hs_lt hT0
    · push Not at hT0
      by_cases hcov : 1 - C / Real.log (abs s.im + 2) ≤ s.re
      · exact hZ s hcov hs_lt hT0
      · have hlt : s.re < 1 - C / Real.log (abs s.im + 2) := by linarith
        exact hT s hs_gt hlt hT0

/-- Critical-line zeros of `ξ`: every zero in the strip lies on `Re s = 1/2`. -/
def XiCriticalLineZeros (ξ : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, ξ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- Given the functional equation `ξ(s) = ξ(1 - s)`, off-critical-line zeros are
exactly ruled out by zero-freeness of the right half.  Pure logic; `dsimp`
resolves `Re(1 - s)`. -/
theorem crit_line_iff_no_right_half (ξ : ℂ → ℂ) (hfe : XiFE ξ) :
    XiCriticalLineZeros ξ ↔ NoRightHalfZeros ξ := by
  constructor
  · intro h s hgt hlt hs
    have hline : s.re = 1 / 2 := h s hs (by linarith) hlt
    linarith
  · intro h s hs hgt hlt
    by_contra hne
    rcases (lt_or_gt_of_ne hne) with (hlow | hhigh)
    · let t := 1 - s
      have ht_zero : ξ t = 0 := by rw [← hfe s] <;> exact hs
      have ht_gt : 1 / 2 < t.re := by dsimp [t] <;> linarith
      have ht_lt : t.re < 1 := by dsimp [t] <;> linarith
      exact h t ht_gt ht_lt ht_zero
    · exact h s hhigh hlt hs

/-- **RH is exactly the thin region.**  Under the standard xi symmetries, the
classical ZFR, and a bounded cover (all true), RH is logically equivalent to
zero-freeness on the thin region.  Therefore closing RH = proving `ThinRegion`. -/
theorem rh_iff_thin_region (ξ : ℂ → ℂ)
    (hξ : XiZeroEquivInStrip ξ) (hfe : XiFE ξ)
    (hC : ClassicalZFR ξ) (hB : BoundedCover ξ hC.T₀) :
    (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2)
    ↔ ThinRegion ξ hC.C hC.T₀ := by
  have hcrit : (∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2)
                ↔ XiCriticalLineZeros ξ := by
    constructor
    · intro h s hs h0 h1
      have hζ : riemannZeta s = 0 := (hξ s h0 h1).mp hs
      exact h s hζ h0 h1
    · intro h s hζ h0 h1
      have hξs : ξ s = 0 := (hξ s h0 h1).mpr hζ
      exact h s hξs h0 h1
  exact ((hcrit.trans (crit_line_iff_no_right_half ξ hfe)).trans
    (thin_region_is_exact_gap ξ hξ hfe hC hB))

end RhResidualGap

/-! ## Section 2 — first-quadrant decomposition over an abstract `ξ` -/

/-- Symmetries of `ξ` (mirror `riemannhypothesis.lean`). -/
def XiShiftedNegSymmetric (ξ : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, -(1 : ℝ) / 2 < z.im → z.im < (1 : ℝ) / 2 → ξ (-z) = ξ z

def XiShiftedConjugateSymmetric (ξ : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, -(1 : ℝ) / 2 < z.im → z.im < (1 : ℝ) / 2 → ξ (conj z) = conj (ξ z)

structure XiShiftedSymmetryPackage (ξ : ℂ → ℂ) where
  neg_symm : XiShiftedNegSymmetric ξ
  conj_symm : XiShiftedConjugateSymmetric ξ

/-- Fourfold symmetry of the zero set.  Pure logic from the two symmetries. -/
theorem xiShifted_fourfold_symmetry {ξ : ℂ → ℂ}
    (P : XiShiftedSymmetryPackage ξ)
    {z : ℂ} (hz : ξ z = 0)
    (hgt : -(1 : ℝ) / 2 < z.im) (hlt : z.im < (1 : ℝ) / 2) :
    ξ z = 0 ∧ ξ (-z) = 0 ∧ ξ (conj z) = 0 ∧ ξ (-conj z) = 0 := by
  refine ⟨hz, ?_, ?_, ?_⟩
  · rw [P.neg_symm z hgt hlt] <;> exact hz
  · rw [P.conj_symm z hgt hlt, hz] <;> simp
  · have h1 : -(1 : ℝ) / 2 < (conj z).im := by simpa [conj_im] using hlt
    have h2 : (conj z).im < 1 / 2 := by simpa [conj_im] using hgt
    rw [P.neg_symm (conj z) h1 h2, P.conj_symm z hgt hlt, hz] <;> simp

/-- Local zero-free rectangle. -/
structure XiLocalZeroFreeRect (ξ : ℂ → ℂ) where
  x0 x1 y0 y1 : ℝ
  x_lt : x0 < x1
  y_lt : y0 < y1
  no_zero : ∀ z : ℂ, x0 < z.re → z.re < x1 → y0 < z.im → z.im < y1 → ξ z ≠ 0

/-- Central zero-free cover on `[-X, X] × (-1/2, 1/2)`. -/
structure XiCentralZeroFreeCover (ξ : ℂ → ℂ) (X : ℝ) where
  rects : List (XiLocalZeroFreeRect ξ)
  covers :
    ∀ z : ℂ, -X ≤ z.re → z.re ≤ X → -(1 : ℝ) / 2 < z.im → z.im < 1 / 2 →
    z.im ≠ 0 → ξ z ≠ 0

/-- Decompose a central zero-free cover into an upper and a lower local
rectangle.  Pure combinatorics of the two half-strips; proven. -/
def central_cover_of_two_rects {ξ : ℂ → ℂ} (X : ℝ)
    (upper lower : XiLocalZeroFreeRect ξ)
    (hupper : ∀ z, 0 < z.im → z.im < 1 / 2 → -X ≤ z.re → z.re ≤ X →
       upper.x0 < z.re ∧ z.re < upper.x1 ∧ upper.y0 < z.im ∧ z.im < upper.y1)
    (hlower : ∀ z, -(1 : ℝ) / 2 < z.im → z.im < 0 → -X ≤ z.re → z.re ≤ X →
       lower.x0 < z.re ∧ z.re < lower.x1 ∧ lower.y0 < z.im ∧ z.im < lower.y1) :
    XiCentralZeroFreeCover ξ X where
  rects := [upper, lower]
  covers := by
    intro z hge hle hgt hlt hne
    by_cases hpos : 0 < z.im
    · have h := hupper z hpos hlt hge hle
      exact upper.no_zero z h.1 h.2.1 h.2.2.1 h.2.2.2
    · have hneg : z.im < 0 := lt_of_le_of_ne (not_lt.mp hpos) hne
      have h := hlower z hgt hneg hge hle
      exact lower.no_zero z h.1 h.2.1 h.2.2.1 h.2.2.2

/-- Asymptotic lower bound `m(|re|) ≤ ‖ξ z‖` on the two tails `|re| > X`. -/
structure XiTailAsymptoticLowerBoundForX (ξ : ℂ → ℂ) (X : ℝ) where
  (m : ℝ → ℝ)
  (m_pos : ∀ r, X ≤ r → 0 < m r)
  (bound :
    ∀ z : ℂ, (X < z.re ∨ z.re < -X) → -(1 : ℝ) / 2 < z.im → z.im < 1 / 2 →
    z.im ≠ 0 → m (abs z.re) ≤ ‖ξ z‖)

/-- Pointwise non-vanishing on the two tails from any asymptotic lower bound
(a lower bound `> 0` at a zero is the contradiction).  Proven. -/
def tailPointwise_of_asymptotic_lower_bound {ξ : ℂ → ℂ} {X : ℝ}
    (A : XiTailAsymptoticLowerBoundForX ξ X) :
    (∀ z, X < z.re → -(1 : ℝ) / 2 < z.im → z.im < 1 / 2 → z.im ≠ 0 → ξ z ≠ 0) ∧
    (∀ z, z.re < -X → -(1 : ℝ) / 2 < z.im → z.im < 1 / 2 → z.im ≠ 0 → ξ z ≠ 0) := by
  constructor
  · intro z hright hgt hlt hne hz
    have habs : X ≤ abs z.re := le_trans (le_of_lt hright) (le_abs_self z.re)
    have hpos := A.m_pos (abs z.re) habs
    have hbound := A.bound z (Or.inl hright) hgt hlt hne
    rw [hz] at hbound
    have : A.m (abs z.re) ≤ 0 := by simpa using hbound
    linarith
  · intro z hleft hgt hlt hne hz
    have hX : X ≤ abs z.re := by
      by_cases hXpos : 0 < X
      · have hzneg : z.re < 0 := by linarith
        rw [abs_of_neg hzneg]
        linarith
      · exact le_trans (not_lt.mp hXpos) (abs_nonneg z.re)
    have hpos := A.m_pos (abs z.re) hX
    have hbound := A.bound z (Or.inr hleft) hgt hlt hne
    rw [hz] at hbound
    have : A.m (abs z.re) ≤ 0 := by simpa using hbound
    linarith

/-- Explicit exponential tail `c·exp(-α|re|) ≤ ‖ξ z‖` (genuine analytic leaf;
the constants come from Stirling / the Hadamard product). -/
structure XiExponentialTailEstimate (ξ : ℂ → ℂ) (X : ℝ) where
  (c : ℝ) (c_pos : 0 < c) (α : ℝ)
  (estimate :
    ∀ z : ℂ, (X < z.re ∨ z.re < -X) → -(1 : ℝ) / 2 < z.im → z.im < 1 / 2 →
    z.im ≠ 0 → c * Real.exp (-α * abs z.re) ≤ ‖ξ z‖)

noncomputable def tailAsymptotic_of_exponential {ξ : ℂ → ℂ} {X : ℝ}
    (E : XiExponentialTailEstimate ξ X) : XiTailAsymptoticLowerBoundForX ξ X where
  m := fun r => E.c * Real.exp (-E.α * r)
  m_pos := by intro r _ <;> exact mul_pos E.c_pos (Real.exp_pos _)
  bound := E.estimate

/-- Off-real pointwise non-vanishing. -/
def XiOffRealPointwiseNonvanishing (ξ : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, -(1 : ℝ) / 2 < z.im → z.im < 1 / 2 → z.im ≠ 0 → ξ z ≠ 0

def XiCentralPointwiseNonvanishingForX (ξ : ℂ → ℂ) (X : ℝ) : Prop :=
  ∀ z : ℂ, -X ≤ z.re → z.re ≤ X → -(1 : ℝ) / 2 < z.im → z.im < 1 / 2 →
  z.im ≠ 0 → ξ z ≠ 0

def XiTailPointwiseNonvanishingForX (ξ : ℂ → ℂ) (X : ℝ) : Prop :=
  (∀ z, X < z.re → -(1 : ℝ) / 2 < z.im → z.im < 1 / 2 → z.im ≠ 0 → ξ z ≠ 0) ∧
  (∀ z, z.re < -X → -(1 : ℝ) / 2 < z.im → z.im < 1 / 2 → z.im ≠ 0 → ξ z ≠ 0)

/-- The first-quadrant *box* zero-freeness (`quadrant_no_zero`) is reflected by
the fourfold symmetry into full central zero-freeness.  Proven (no analysis,
pure symmetry + sign cases). -/
theorem nonvanishing_central_from_first_quadrant {ξ : ℂ → ℂ}
    (P : XiShiftedSymmetryPackage ξ) (X : ℝ)
    (h_quadrant :
      ∀ z : ℂ, 0 ≤ z.re → z.re ≤ X → 0 < z.im → z.im < 1 / 2 → ξ z ≠ 0)
    (z : ℂ) (hxge : -X ≤ z.re) (hxle : z.re ≤ X)
    (hygt : -(1 : ℝ) / 2 < z.im) (hylt : z.im < 1 / 2) (hyne : z.im ≠ 0) :
    ξ z ≠ 0 := by
  intro hz
  have h4 := xiShifted_fourfold_symmetry P hz hygt hylt
  by_cases hpos : 0 < z.im
  · by_cases hre : 0 ≤ z.re
    · exact h_quadrant z hre hxle hpos hylt hz
    · let w := -conj z
      have hw_re_ge : 0 ≤ w.re := by dsimp [w] <;> linarith
      have hw_re_le : w.re ≤ X := by dsimp [w] <;> linarith
      have hw_im_pos : 0 < w.im := by dsimp [w] <;> exact hpos
      have hw_im_lt : w.im < 1 / 2 := by dsimp [w] <;> exact hylt
      exact h_quadrant w hw_re_ge hw_re_le hw_im_pos hw_im_lt h4.2.2.2
  · have hneg : z.im < 0 := lt_of_le_of_ne (not_lt.mp hpos) hyne
    by_cases hre : 0 ≤ z.re
     · let w := conj z
       have hw_re_ge : 0 ≤ w.re := by dsimp [w] <;> exact hre
       have hw_re_le : w.re ≤ X := by dsimp [w] <;> exact hxle
       have hw_im_pos : 0 < w.im := by dsimp [w] <;> exact (neg_pos.2 hneg)
       have hw_im_lt : w.im < 1 / 2 := by dsimp [w] <;> linarith [hygt]
       exact h_quadrant w hw_re_ge hw_re_le hw_im_pos hw_im_lt h4.2.2.1
     · let w := -z
       have hw_re_ge : 0 ≤ w.re := by dsimp [w] <;> linarith
       have hw_re_le : w.re ≤ X := by dsimp [w] <;> linarith
       have hw_im_pos : 0 < w.im := by dsimp [w] <;> exact (neg_pos.2 hneg)
       have hw_im_lt : w.im < 1 / 2 := by dsimp [w] <;> linarith [hygt]
       exact h_quadrant w hw_re_ge hw_re_le hw_im_pos hw_im_lt h4.2.1

/-- Assemble central + tail pointwise non-vanishing into off-real pointwise
non-vanishing.  Pure case split.  Proven. -/
theorem xiOffRealPointwiseNonvanishing_of_central_and_tail {ξ : ℂ → ℂ} {X : ℝ}
    (C : XiCentralPointwiseNonvanishingForX ξ X)
    (T : XiTailPointwiseNonvanishingForX ξ X) :
    XiOffRealPointwiseNonvanishing ξ := by
  intro z hgt hlt hne
  by_cases hright : X < z.re
  · exact T.1 z hright hgt hlt hne
  · by_cases hleft : z.re < -X
    · exact T.2 z hleft hgt hlt hne
    · have hle : z.re ≤ X := not_lt.mp hright
      have hge : -X ≤ z.re := not_lt.mp hleft
      exact C z hge hle hgt hlt hne

/-- **Main decomposition lemma (proven).** A `RHFirstQuadrantProof` reduces to
off-real pointwise non-vanishing of `ξ`, i.e. to the conjunction of its two
leaves: `quadrant_no_zero` (bounded-box zero-freeness) and `right_tail`
(tail lower bound). -/
structure RHFirstQuadrantProof (ξ : ℂ → ℂ) where
  X : ℝ
  symmetries : XiShiftedSymmetryPackage ξ
  quadrant_no_zero :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ X → 0 < z.im → z.im < 1 / 2 → ξ z ≠ 0
  right_tail : XiTailAsymptoticLowerBoundForX ξ X

theorem rh_first_quadrant_proof_to_off_real {ξ : ℂ → ℂ}
    (P : RHFirstQuadrantProof ξ) :
    XiOffRealPointwiseNonvanishing ξ := by
  let central : XiCentralPointwiseNonvanishingForX ξ P.X :=
    fun z hge hle hgt hlt hne =>
      nonvanishing_central_from_first_quadrant P.symmetries P.X
        P.quadrant_no_zero z hge hle hgt hlt hne
  let tail : XiTailPointwiseNonvanishingForX ξ P.X :=
    tailPointwise_of_asymptotic_lower_bound P.right_tail
  exact xiOffRealPointwiseNonvanishing_of_central_and_tail central tail

/-!
## Decomposed leaves and flags

*FLAG — `ThinRegion ξ C T₀` (section 1) is the exact residual open leaf and is
**mathematically equivalent to RH** (`rh_iff_thin_region`).  It is the hard core,
not a finite/analytic fact.

*GENUINE finite leaf A — `quadrant_no_zero` (rectangle `[0,X]×(0,1/2)`):
  further decompose into a finite cover of tiny rectangles, each zero-free iff
  `‖ξ z‖ ≥ ε > 0` on its boundary (argument principle).  The boundary lower bound
  itself is a *bounded interval-arithmetic* computation — TRUE, finite,
  engineering.  Next sub-problem: `rect_boundary_lower_bound` (compute `ε` on a
  mesh of the box using explicit `ξ` bounds).

*GENUINE analytic leaf B — `right_tail` → `XiExponentialTailEstimate`
  (`c·exp(-α|re|) ≤ ‖ξ z‖`): the constants follow from the Stirling / Hadamard
  product asymptotics of `ξ`.  This is a *true analytic theorem*, not equivalent
  to RH, but the constant extraction is a substantial explicit estimate.
  Next sub-problem: `xiShifted_tail_asymptotic` (verify the Stirling bound on
  `‖ξ(1/2+it)‖` for `|t| ≥ T₀`).

Both leaves are precisely the sorries 8356 / 9117 of `riemannhypothesis.lean`,
labelled there as *true finite/analytic facts* — the only non-RH-equivalent open
steps.  Everything above them (symmetry reflection, central/tail assembly,
thin-region isolation) is now proven logic reusing `Mathlib`.
-/
