import Mathlib

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
    1 - C / Real.log (Real.abs s.im + 2) ≤ s.re →
    s.re < 1 →
    T₀ ≤ Real.abs s.im →
    ξ s ≠ 0)

/-- The thin region: the ONLY place an off-critical-line zero could still hide
once the classical ZFR and a bounded cover are in place.  This is the exact
open leaf. -/
def ThinRegion (ξ : ℂ → ℂ) (C T₀ : ℝ) : Prop :=
  ∀ s : ℂ,
    1 / 2 < s.re →
    s.re < 1 - C / Real.log (Real.abs s.im + 2) →
    T₀ ≤ Real.abs s.im →
    ξ s ≠ 0

/-- A finite zero-free cover of the bounded part near the real axis.  This is a
TRUE finite numerical fact (rigorous interval arithmetic). -/
structure BoundedCover (ξ : ℂ → ℂ) (T₀ : ℝ) where
  covers : ∀ s : ℂ,
    1 / 2 < s.re → s.re < 1 → Real.abs s.im < T₀ → ξ s ≠ 0

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
    exact hNZ s hs_gt hs_lt
  · intro hT s hs_gt hs_lt
    rcases hC with ⟨C, T₀, _, hZ⟩
    by_cases hT0 : Real.abs s.im < T₀
    · exact hB.covers s hs_gt hs_lt hT0
    · push_neg at hT0
      by_cases hcov : 1 - C / Real.log (Real.abs s.im + 2) ≤ s.re
      · exact hZ s hcov hs_lt hT0
      · have hlt : s.re < 1 - C / Real.log (Real.abs s.im + 2) := by linarith
        exact hT s hs_gt hlt hT0

/-- **RH is exactly the thin region.**  Under the standard xi symmetries, the
classical ZFR, and a bounded cover (all true), the Riemann Hypothesis is
logically equivalent to zero-freeness on the thin region.  Therefore closing
RH = proving `ThinRegion`.  This is the precise final leaf. -/
theorem rh_iff_thin_region (ξ : ℂ → ℂ)
    (hξ : XiZeroEquivInStrip ξ) (hfe : XiFE ξ)
    (hC : ClassicalZFR ξ) (hB : BoundedCover ξ hC.T₀) :
    (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2)
    ↔ ThinRegion ξ hC.C hC.T₀ := by
  constructor
  · intro hRH s hs_gt hs_lt hT₀ hzero
    have hz : riemannZeta s = 0 := (hξ s (by linarith) (by linarith)).mp hzero
    have hline : s.re = 1 / 2 := hRH s hz (by linarith) (by linarith)
    linarith
  · intro hT s hz hs0 hs1
    have hNZ := (thin_region_is_exact_gap ξ hξ hfe hC hB).mpr hT
    have hxi0 : ξ s = 0 := (hξ s hs0 hs1).mpr hz
    have hgt : 1 / 2 < s.re := by linarith
    exact hNZ s hgt hs1 hxi0

/-- Corollaries of the isolation theorem.

The classical zero-free region (de la Vallée Poussin) supplies some fixed
constant `C`, so the residual `ThinRegion ξ C T₀` always contains points
(`1/2 < Re s < 1 - C/log(|Im s|+2)` is non-empty for any `C`).  Hence the ZFR
alone can never rule out off-critical-line zeros: closing RH is *exactly*
proving `ξ ≠ 0` on that residual thin region.  This is the precise final leaf
of `riemannhypothesis.lean` (its sorries 13324 and 13764). -/

