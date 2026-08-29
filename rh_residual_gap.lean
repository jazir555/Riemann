import Mathlib
import Zeta23.FromPNTPlus.ZetaBounds
import Zeta23.ZetaReflect
import Zeta23.Statement

/-!
# The residual thin-region gap for the Riemann Hypothesis

This file isolates, *sorry-free* and without depending on the 13k-line scaffold
in `riemannhypothesis.lean`, the exact remaining open leaf of that
formalization.

## Status (honest)

The chain in `riemannhypothesis.lean` reduces `RiemannHypothesisProp` to two
named analytic challenges (`FirstQuadrant10` and `CompletedZetaTailU10`), and
ultimately to either

* `TailCanonicalLaguerrePositivityLeaf` (sorry 13324), or
* `MollifiedRoucheLeaf` (sorry 13764),

both of which the file itself acknowledges are *mathematically equivalent to
RH* and "require a fundamentally new mathematical discovery."  The other two
`sorry`s (8356, 9117) are *true* finite/analytic facts (real-analyticity of a
zeta asymptotic; a rigorous interval-arithmetic bound on a rectangle) whose
verification is a known, bounded engineering task, **not** the hard part.

Consequently the genuine final leaf is the classical *thin region*

    { s : ℚ | 1/2 < Re s < 1 - C / log(|Im s| + 2),  |Im s| ≥ T₀ }.

The classical zero-free region (de la Vallée Poussin) already rules out the
*wedge* near Re = 1, and a finite bounded-rectangle cover rules out the
*bounded* part near the real axis.  What remains — and is exactly RH — is
ruling out zeros in the thin middle region.  This file proves that isolation
theorem cleanly.

## Why known combinations do not close it

* The classical ZFR only excludes Re ≥ 1 - C/log|Im|; the middle gap
  `1/2 < Re < 1 - C/log|Im|` is exactly where off-line zeros could still hide.
* The external `zeta-23-lean` result proves ≥ 2/3 of zeros lie on the critical
  line (a genuine, sorry-free theorem) — a *positive-proportion* statement,
  not full RH.
* The mollified Rouché program yields L² (mean-value) bounds, which cannot
  enforce the required L∞ (pointwise) bound without new mathematics.

No isomorphism (Li's criterion, Hilbert–Pólya, Nyman–Beurling, de Bruijn–
Newman) makes this tractable: each is *equivalent* to RH.
-/

open Complex Real

/-- `ξ` vanishes exactly where `ζ` does inside the critical strip. -/
def XiZeroEquivInStrip (ξ : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → (ξ s = 0 ↔ riemannZeta s = 0)

/-- Functional equation `ξ(s) = ξ(1 - s)`. -/
def XiFE (ξ : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, ξ s = ξ (1 - s)

/-- The classical zero-free region (de la Vallée Poussin).  This is a TRUE
theorem; here it is supplied as the precise analytic input whose verification
lives in the `ZeroFreeRegion*` infrastructure. -/
structure ClassicalZFR (ξ : ℂ → ℂ) where
  (C T₀ : ℝ)
  (Cpos : 0 < C)
  (zeroFree : ∀ s : ℂ,
     1 - C / Real.log (abs s.im + 2) ≤ s.re →
     s.re < 1 →
     T₀ ≤ abs s.im →
     ξ s ≠ 0)

/-- The thin region: the ONLY place an off-critical-line zero could still hide
once the classical ZFR and a bounded cover are in place.  This is the exact
open leaf. -/
def ThinRegion (ξ : ℂ → ℂ) (C T₀ : ℝ) : Prop :=
  ∀ s : ℂ,
    1 / 2 < s.re →
    s.re < 1 - C / Real.log (abs s.im + 2) →
    T₀ ≤ abs s.im →
    ξ s ≠ 0

/- A finite zero-free cover of the bounded part near the real axis.  This is a
TRUE finite numerical fact (rigorous interval arithmetic). -/
structure BoundedCover (ξ : ℂ → ℂ) (T₀ : ℝ) where
  covers : ∀ s : ℂ,
    1 / 2 < s.re → s.re < 1 → abs s.im < T₀ → ξ s ≠ 0

/-- Full zero-freeness of the right half of the critical strip. -/
def NoRightHalfZeros (ξ : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → ξ s ≠ 0

/-- **Exact gap isolation.**  Given the classical ZFR and a bounded cover
(both true theorems), the right-half zero-freeness of `ξ` is *precisely*
equivalent to zero-freeness on the thin region.  Hence the thin region is the
exact residual open leaf. -/
theorem thin_region_is_exact_gap (ξ : ℂ → ℂ)
    (hξ : XiZeroEquivInStrip ξ) (hfe : XiFE ξ)
    (hC : ClassicalZFR ξ) (hB : BoundedCover ξ hC.T₀) :
    NoRightHalfZeros ξ ↔ ThinRegion ξ hC.C hC.T₀ := by
  constructor
  · intro hNZ s hs_gt hs_lt hT₀
    have hnonneg : 0 ≤ abs s.im := abs_nonneg s.im
    have hpos : 0 < hC.C / Real.log (abs s.im + 2) := by
      exact div_pos hC.Cpos (Real.log_pos (by linarith))
    exact hNZ s hs_gt (by linarith [hs_lt, hpos])
  · intro hT s hs_gt hs_lt
    rcases hC with ⟨C, T₀, _, hZ⟩
    by_cases hT0 : abs s.im < T₀
    · exact hB.covers s hs_gt hs_lt hT0
    · push Not at hT0
      by_cases hcov : 1 - C / Real.log (abs s.im + 2) ≤ s.re
      · exact hZ s hcov hs_lt hT0
      · have hlt : s.re < 1 - C / Real.log (abs s.im + 2) := by linarith
        exact hT s hs_gt hlt hT0

/- Critical-line zeros of `ξ`: every zero in the strip lies on `Re s = 1/2`. -/
def XiCriticalLineZeros (ξ : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, ξ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- Given the functional equation `ξ(s) = ξ(1 - s)`, off-critical-line zeros are
exactly ruled out by zero-freeness of the right half.  Pure logic; `simp`
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
classical ZFR, and a bounded cover (all true), the Riemann Hypothesis is
logically equivalent to zero-freeness on the thin region.  Therefore closing
RH = proving `ThinRegion`.  This is the precise final leaf. -/
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

/-! ## The ζ-native version, with the classical ZFR input **discharged** by `Zeta23`

Everything above takes the classical zero-free region as a hypothesis (`ClassicalZFR`).
Since `Zeta23` is built on **Mathlib's** `riemannZeta`, its (PNT+-derived) zero-free region
`Zeta23.ZetaZeroFree` applies verbatim here, and the zero-set symmetry `ρ ↦ 1 − conj ρ`
comes from `Zeta23.zeta_reflect_zero`.  So in this section the only remaining inputs are

* the *thin region* (`ThinRegionZeta`) — the genuine residual leaf, and
* a *bounded cover* (`BoundedCoverZeta`) — a finite interval-arithmetic fact,

while the zero-free wedge near `Re = 1` is now a theorem.  The price is that `Zeta23`/PNT+
proves the region `Re s ≥ 1 − A/(log |Im s|)^9` (constant `A` unspecified) rather than the
sharper de la Vallée Poussin/Kadiri shape `1 − C/log|Im s|`; the thin region is
correspondingly (slightly) larger, and the isolation statement is unaffected. -/

/-- **The classical zero-free region for ζ is a theorem** (with the weaker exponent 9):
`ζ(s) ≠ 0` whenever `3 < |Im s|` and `1 − A/(log|Im s|)^9 ≤ Re s < 1`.  This is
`Zeta23.FromPNTPlus.ZetaBounds`' `ZetaZeroFree`, restated for an arbitrary `s : ℂ`. -/
theorem zeta_zeroFree_pow :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℂ, 3 < |s.im| →
      1 - A / (Real.log |s.im|) ^ 9 ≤ s.re → s.re < 1 → riemannZeta s ≠ 0 := by
  obtain ⟨A, hA, h⟩ := ZetaZeroFree
  refine ⟨A, hA.1, ?_⟩
  intro s hs hedge hre
  have hz := h s.re s.im hs (Set.mem_Ico.mpr ⟨hedge, hre⟩)
  rwa [Complex.re_add_im] at hz

/-- Strip zeros of ζ are symmetric under `ρ ↦ 1 − conj ρ` (`Zeta23.zeta_reflect_zero`;
this is the ζ-level substitute for the functional equation `ξ(s) = ξ(1-s)`). -/
theorem zeta_strip_zero_reflect {ρ : ℂ} (hζ : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : riemannZeta (1 - (starRingEnd ℂ) ρ) = 0 := by
  have h := (Zeta23.zeta_reflect_zero ρ ⟨hζ, h0, h1⟩).1
  simpa [Zeta23.reflect] using h

/-- Zero-freeness of the right half of the critical strip, for ζ. -/
def NoRightHalfZerosZeta : Prop := ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0

/-- The critical-line statement for ζ's strip zeros is equivalent to right-half
zero-freeness, using only the `ρ ↦ 1 − conj ρ` symmetry of the strip zero set. -/
theorem zeta_crit_line_iff_no_right_half :
    (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2)
      ↔ NoRightHalfZerosZeta := by
  constructor
  · intro h s hgt hlt hz
    have hline := h s hz (by linarith) hlt
    linarith
  · intro h s hz h0 h1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlow | hhigh
    · have hrefl := zeta_strip_zero_reflect hz h0 h1
      have hre : (1 - (starRingEnd ℂ) s).re = 1 - s.re := by simp
      exact h _ (by rw [hre]; linarith) (by rw [hre]; linarith) hrefl
    · exact h s hhigh h1 hz

/-- The residual thin region for ζ, with the (now unconditional) `log^9` edge. -/
def ThinRegionZeta (A T₀ : ℝ) : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 - A / (Real.log |s.im|) ^ 9 → T₀ ≤ |s.im| →
    riemannZeta s ≠ 0

/-- A finite zero-free cover of the bounded part `|Im s| < T₀` of the strip. -/
def BoundedCoverZeta (T₀ : ℝ) : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → |s.im| < T₀ → riemannZeta s ≠ 0

/-- **Exact gap isolation for ζ.**  Given the `Zeta23` zero-free region and a bounded
cover, right-half zero-freeness of ζ is *precisely* zero-freeness on the thin region. -/
theorem zeta_thin_region_is_exact_gap {A T₀ : ℝ} (hA : 0 < A) (hT₀ : 3 < T₀)
    (hzfr : ∀ s : ℂ, 3 < |s.im| →
      1 - A / (Real.log |s.im|) ^ 9 ≤ s.re → s.re < 1 → riemannZeta s ≠ 0)
    (hB : BoundedCoverZeta T₀) :
    NoRightHalfZerosZeta ↔ ThinRegionZeta A T₀ := by
  constructor
  · intro hNZ s hgt hlt hT
    have h3 : (3 : ℝ) < |s.im| := by linarith
    have hlogpos : 0 < Real.log |s.im| := Real.log_pos (by linarith)
    have hpos : 0 < A / (Real.log |s.im|) ^ 9 := by positivity
    exact hNZ s hgt (by linarith)
  · intro hT s hgt hlt
    by_cases hsmall : |s.im| < T₀
    · exact hB s hgt hlt hsmall
    · push Not at hsmall
      by_cases hedge : 1 - A / (Real.log |s.im|) ^ 9 ≤ s.re
      · exact hzfr s (by linarith) hedge hlt
      · exact hT s hgt (by linarith) hsmall

/-- **RH is exactly the thin region** (ζ-native form). -/
theorem rh_iff_thin_region_zeta {A T₀ : ℝ} (hA : 0 < A) (hT₀ : 3 < T₀)
    (hzfr : ∀ s : ℂ, 3 < |s.im| →
      1 - A / (Real.log |s.im|) ^ 9 ≤ s.re → s.re < 1 → riemannZeta s ≠ 0)
    (hB : BoundedCoverZeta T₀) :
    (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2)
      ↔ ThinRegionZeta A T₀ :=
  zeta_crit_line_iff_no_right_half.trans (zeta_thin_region_is_exact_gap hA hT₀ hzfr hB)

/-- **Residual gap with the zero-free-region input discharged.**  For every threshold
`T₀ > 3` there is an absolute `A > 0` such that, *assuming only a bounded cover*, RH (in
strip-zero form) is equivalent to zero-freeness on the thin region.  No zero-free-region
hypothesis is required: it is supplied by `Zeta23`. -/
theorem rh_iff_thin_region_zeta_of_boundedCover {T₀ : ℝ} (hT₀ : 3 < T₀) :
    ∃ A : ℝ, 0 < A ∧ (BoundedCoverZeta T₀ →
      ((∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2)
        ↔ ThinRegionZeta A T₀)) := by
  obtain ⟨A, hA, hzfr⟩ := zeta_zeroFree_pow
  exact ⟨A, hA, fun hB => rh_iff_thin_region_zeta hA hT₀ hzfr hB⟩

/-- Mathlib's `RiemannHypothesis` implies the strip-zero form used in this file
(`Zeta23.RH_implies_on_line`). -/
theorem strip_criterion_of_riemannHypothesis (h : RiemannHypothesis) :
    ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 :=
  fun s hz h0 h1 => Zeta23.RH_implies_on_line h ⟨hz, h0, h1⟩

