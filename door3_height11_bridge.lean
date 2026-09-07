import riemann_hypothesis_newsection

open Complex Real Set

noncomputable section

/-!
# Exact-height Door-3 certificate interface

The shifted rectangle has `s.im = z.re`, hence its height is strictly below
`11`, not `14.13`.  The original `CriticalStripEvidence14` interface was
therefore stronger than necessary (and its `14.14` open rectangle reaches
above the target).  This file provides the precise height-11 certificate
interface used by the Door-3 rectangle.
-/

namespace Door3Height11

open RHProofScaffold.ClosedCertificate.Task1Completion.ZetaNumericCert

def yTop11 : ℝ := 11
def yBot11 : ℝ := -11

structure CriticalStripEvidence11 where
  upper : RectIntervalBound 0 1 0 yTop11
  upper_ex : IntervalExcludesZero upper
  lower : RectIntervalBound 0 1 yBot11 0
  lower_ex : IntervalExcludesZero lower

structure CriticalStripCover11 where
  rects : List ZeroFreeRect
  covers :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| < (11 : ℝ) → s.im ≠ 0 →
      ∃ R ∈ rects, inOpenRect R.x0 R.x1 R.y0 R.y1 s

def criticalStripCover11_of_evidence
    (E : CriticalStripEvidence11) : CriticalStripCover11 :=
  { rects := [zeroFreeRect_of_interval E.upper E.upper_ex,
      zeroFreeRect_of_interval E.lower E.lower_ex]
    covers := by
      intro s hs0 hs1 him him0
      by_cases hpos : 0 < s.im
      · have hle := (abs_lt.mp him).2
        have htop : s.im < yTop11 := by
          simpa [yTop11] using hle
        exact ⟨zeroFreeRect_of_interval E.upper E.upper_ex,
          List.mem_cons_self, hs0, hs1, hpos, htop⟩
      · have hneg : s.im < 0 := by
          have hle : s.im ≤ 0 := le_of_not_gt hpos
          exact lt_of_le_of_ne hle him0
        have hge := (abs_lt.mp him).1
        have hbot : yBot11 < s.im := by
          dsimp [yBot11]
          linarith
        exact ⟨zeroFreeRect_of_interval E.lower E.lower_ex,
          List.mem_cons_of_mem
            (y := zeroFreeRect_of_interval E.upper E.upper_ex)
            List.mem_cons_self, hs0, hs1, hbot, hneg⟩ }

theorem riemannZeta_ne_zero_of_evidence
    (E : CriticalStripEvidence11) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (him : |s.im| < (11 : ℝ)) (him0 : s.im ≠ 0) :
    riemannZeta s ≠ 0 := by
  intro hz
  rcases (criticalStripCover11_of_evidence E).covers s hs0 hs1 him him0 with
    ⟨R, hR, hs⟩
  exact (R.no_zero s hs) hz

theorem xiShifted_no_zero_in_rect_10_of_evidence
    (E : CriticalStripEvidence11) (z : ℂ)
    (hx0 : -1 < z.re) (hx1 : z.re < 11)
    (hy0 : 0 < z.im) (hy1 : z.im < (1 / 2 : ℝ)) :
    xiShifted z ≠ 0 := by
  set s := shiftedS z
  have hs_re : s.re = 1 / 2 - z.im := shiftedS_re z
  have hs_im : s.im = z.re :=
    RHProofScaffold.LeafDecomp.shiftedS_im_eq z
  have hs0 : 0 < s.re := by rw [hs_re]; linarith
  have hs1 : s.re < 1 := by rw [hs_re]; linarith
  have him : |s.im| ≤ (11 : ℝ) := by
    rw [hs_im]
    rw [abs_le]
    constructor <;> linarith
  have hzeta : riemannZeta s ≠ 0 := by
    by_cases hzre : z.re = 0
    · have hs_real : s = (s.re : ℂ) := by
        apply Complex.ext
        · simp
        · rw [hs_im, hzre]
          simp
      rw [hs_real]
      exact RHProofScaffold.ClosedCertificate.Task1Completion.riemannZeta_ne_zero_real_Ioo
        hs0 hs1
    · have him0 : s.im ≠ 0 := by rw [hs_im]; exact hzre
      have him' : |s.im| < (11 : ℝ) := by
        rw [hs_im, abs_lt]
        constructor <;> linarith
      exact riemannZeta_ne_zero_of_evidence E s hs0 hs1 him' him0
  have hxi : xiShifted z = 0 ↔ riemannZeta s = 0 :=
    classicalXi_zero_equivalence_from_gamma
      classical_gamma_nonzero_instrip s hs0 hs1
  intro hz
  exact hzeta (hxi.mp hz)

theorem rh_from_evidence11_and_tailU
    (E : CriticalStripEvidence11)
    (B : AnalyticChallenge.CompletedZetaTailU10) :
    RiemannHypothesisProp := by
  let A : AnalyticChallenge.FirstQuadrant10 :=
    { no_zero := by
        intro z hx0 hx1 hy0 hy1
        apply xiShifted_no_zero_in_rect_10_of_evidence E z
        · linarith
        · linarith
        · exact hy0
        · exact hy1 }
  exact RHProofScaffold.rh_from_first_quadrant_and_tailU A B

/-! A finite certificate is the natural interval-arithmetic shape: a single
axis-aligned enclosure over the whole strip is unnecessarily restrictive. -/

structure RectEvidence where
  x0 : ℝ
  x1 : ℝ
  y0 : ℝ
  y1 : ℝ
  bound : RectIntervalBound x0 x1 y0 y1
  excludes : IntervalExcludesZero bound

structure FiniteCriticalStripEvidence11 where
  rects : List RectEvidence
  covers :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| < (11 : ℝ) → s.im ≠ 0 →
      ∃ E ∈ rects, inOpenRect E.x0 E.x1 E.y0 E.y1 s

def finiteCover11 (E : FiniteCriticalStripEvidence11) : CriticalStripCover11 :=
  { rects := E.rects.map (fun R => zeroFreeRect_of_interval R.bound R.excludes)
    covers := by
      intro s hs0 hs1 him him0
      obtain ⟨R, hR, hs⟩ := E.covers s hs0 hs1 him him0
      refine ⟨zeroFreeRect_of_interval R.bound R.excludes, ?_, hs⟩
      exact List.mem_map.mpr ⟨R, hR, rfl⟩ }

theorem riemannZeta_ne_zero_of_finite_evidence
    (E : FiniteCriticalStripEvidence11) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (him : |s.im| < (11 : ℝ)) (him0 : s.im ≠ 0) :
    riemannZeta s ≠ 0 := by
  intro hz
  obtain ⟨R, hR, hs⟩ := E.covers s hs0 hs1 him him0
  exact (riemannZeta_ne_zero_of_interval_exclusion R.bound R.excludes s hs) hz

theorem xiShifted_no_zero_in_rect_10_of_finite_evidence
    (E : FiniteCriticalStripEvidence11) (z : ℂ)
    (hx0 : -1 < z.re) (hx1 : z.re < 11)
    (hy0 : 0 < z.im) (hy1 : z.im < (1 / 2 : ℝ)) :
    xiShifted z ≠ 0 := by
  set s := shiftedS z
  have hs_re : s.re = 1 / 2 - z.im := shiftedS_re z
  have hs_im : s.im = z.re := RHProofScaffold.LeafDecomp.shiftedS_im_eq z
  have hs0 : 0 < s.re := by rw [hs_re]; linarith
  have hs1 : s.re < 1 := by rw [hs_re]; linarith
  have hxi : xiShifted z = 0 ↔ riemannZeta s = 0 :=
    classicalXi_zero_equivalence_from_gamma
      classical_gamma_nonzero_instrip s hs0 hs1
  intro hz
  by_cases hzre : z.re = 0
  · have hs_real : s = (s.re : ℂ) := by
      apply Complex.ext
      · simp
      · rw [hs_im, hzre]
        simp
    apply RHProofScaffold.ClosedCertificate.Task1Completion.riemannZeta_ne_zero_real_Ioo
      hs0 hs1
    rw [← hs_real]
    exact hxi.mp hz
  · have him0 : s.im ≠ 0 := by rw [hs_im]; exact hzre
    have him : |s.im| < (11 : ℝ) := by
      rw [hs_im, abs_lt]
      constructor <;> linarith
    exact riemannZeta_ne_zero_of_finite_evidence E s hs0 hs1 him him0 (hxi.mp hz)

theorem rh_from_finite_evidence11_and_tailU
    (E : FiniteCriticalStripEvidence11)
    (B : AnalyticChallenge.CompletedZetaTailU10) :
    RiemannHypothesisProp := by
  let A : AnalyticChallenge.FirstQuadrant10 :=
    { no_zero := by
        intro z hx0 hx1 hy0 hy1
        apply xiShifted_no_zero_in_rect_10_of_finite_evidence E z
        · linarith
        · linarith
        · exact hy0
        · exact hy1 }
  exact RHProofScaffold.rh_from_first_quadrant_and_tailU A B

/-! ### ζ-native bounded-cover adapter

The finite certificate is stated in the full strip, so it can also be
consumed directly by the ζ-native residual formulation.  For the right half
of the strip we use the functional-equation reflection `s ↦ 1 - s`; the
reflected point remains in `(0,1)` and has the same height modulus, hence is
covered by the finite evidence.  This adapter contains no xi or RH axiom. -/

theorem boundedCoverZeta11_of_finite_evidence
    (E : FiniteCriticalStripEvidence11) :
    ∀ s : ℂ, (1 : ℝ) / 2 < s.re → s.re < 1 →
      |s.im| < (11 : ℝ) → riemannZeta s ≠ 0 := by
  intro s hs_half hs_one hs_height
  by_cases hsim : s.im = 0
  · have hs_real : s = (s.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa [hsim]
    rw [hs_real]
    exact RHProofScaffold.ClosedCertificate.Task1Completion.riemannZeta_ne_zero_real_Ioo
      (by linarith) (by linarith)
  let s' : ℂ := 1 - s
  have hs're : 0 < s'.re := by
    have h : s'.re = 1 - s.re := by simp [s', Complex.sub_re]
    rw [h]
    linarith
  have hs're_lt : s'.re < 1 := by
    have h : s'.re = 1 - s.re := by simp [s', Complex.sub_re]
    rw [h]
    linarith
  have hs'im_abs : |s'.im| = |s.im| := by
    have h : s'.im = -s.im := by simp [s', Complex.sub_im]
    rw [h, abs_neg]
  have hs'height : |s'.im| < (11 : ℝ) := by
    rw [hs'im_abs]
    exact hs_height
  have hs'im_ne : s'.im ≠ 0 := by
    intro h
    have : s.im = 0 := by
      dsimp [s'] at h
      simpa using h
    exact hsim this
  have hzero' : riemannZeta s' ≠ 0 :=
    riemannZeta_ne_zero_of_finite_evidence E s' hs're hs're_lt hs'height hs'im_ne
  intro hz
  have hz' : riemannZeta s' = 0 := by
    have hxi_s : classicalXi s = 0 :=
      (classicalXi_zero_equivalence_from_gamma
        classical_gamma_nonzero_instrip s (by linarith) (by linarith)).mpr hz
    have hxi_reflect : classicalXi (1 - s) = 0 := by
      rw [classicalXi_functional_equation s (by linarith) (by linarith)]
      exact hxi_s
    have hzero_reflect : riemannZeta (1 - s) = 0 :=
      (classicalXi_zero_equivalence_from_gamma
        classical_gamma_nonzero_instrip (1 - s) (by simp; linarith) (by simp; linarith)).mp
        hxi_reflect
    simpa [s'] using hzero_reflect
  exact hzero' hz'

#print axioms riemannZeta_ne_zero_of_evidence
#print axioms xiShifted_no_zero_in_rect_10_of_evidence
#print axioms riemannZeta_ne_zero_of_finite_evidence
#print axioms xiShifted_no_zero_in_rect_10_of_finite_evidence
#print axioms rh_from_finite_evidence11_and_tailU
#print axioms rh_from_evidence11_and_tailU
#print axioms boundedCoverZeta11_of_finite_evidence

end Door3Height11
