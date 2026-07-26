import Mathlib

set_option maxHeartbeats 1000000

open Complex

noncomputable section

/-!
# Basic objects: ζ, critical strip, RH proposition
-/

def zeta : ℂ → ℂ := riemannZeta

def CriticalStrip (s : ℂ) : Prop :=
  0 < s.re ∧ s.re < 1

def RiemannHypothesisProp : Prop :=
  ∀ s : ℂ,
    zeta s = 0 →
    0 < s.re →
    s.re < 1 →
    s.re = (1 : ℝ) / 2

/-!
# Generic xi-zero equivalence framework
-/

def XiZeroEquivalence (xi : ℂ → ℂ) : Prop :=
  ∀ s : ℂ,
    0 < s.re →
    s.re < 1 →
    (xi s = 0 ↔ zeta s = 0)

def XiCriticalLineZeros (xi : ℂ → ℂ) : Prop :=
  ∀ s : ℂ,
    xi s = 0 →
    0 < s.re →
    s.re < 1 →
    s.re = (1 : ℝ) / 2

theorem rh_of_xi (xi : ℂ → ℂ)
    (h_equiv : XiZeroEquivalence xi)
    (h_xi : XiCriticalLineZeros xi) :
    RiemannHypothesisProp := by
  intro s hz h0 h1
  have hx : xi s = 0 := by
    rw [h_equiv s h0 h1]
    exact hz
  exact h_xi s hx h0 h1

theorem xi_of_rh (xi : ℂ → ℂ)
    (h_equiv : XiZeroEquivalence xi)
    (h_rh : RiemannHypothesisProp) :
    XiCriticalLineZeros xi := by
  intro s hs h0 h1
  have hz : zeta s = 0 := by
    rw [← h_equiv s h0 h1]
    exact hs
  exact h_rh s hz h0 h1

theorem rh_iff_xi_critical_generic (xi : ℂ → ℂ)
    (h_equiv : XiZeroEquivalence xi) :
    RiemannHypothesisProp ↔ XiCriticalLineZeros xi := by
  constructor
  · exact xi_of_rh xi h_equiv
  · exact rh_of_xi xi h_equiv

/-!
# Prefactor framework
-/

def XiFromPrefactor (prefactor : ℂ → ℂ) : ℂ → ℂ :=
  fun s => prefactor s * zeta s

def PrefactorNonzeroInStrip (prefactor : ℂ → ℂ) : Prop :=
  ∀ s : ℂ,
    0 < s.re →
    s.re < 1 →
    prefactor s ≠ 0

theorem xi_zero_equiv_zeta_zero (prefactor : ℂ → ℂ)
    (h_nonzero : PrefactorNonzeroInStrip prefactor) :
    XiZeroEquivalence (XiFromPrefactor prefactor) := by
  intro s h0 h1
  constructor
  · intro h
    have hmul : prefactor s * zeta s = 0 := by
      simpa [XiFromPrefactor] using h
    exact (mul_eq_zero.mp hmul).resolve_left (h_nonzero s h0 h1)
  · intro hz
    simp [XiFromPrefactor, hz]

/-!
# Classical xi prefactor and classical xi function
-/

def classicalXiPrefactor (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
  s *
  (s - 1) *
  ((Real.pi : ℂ) ^ (-(s / 2))) *
  Complex.Gamma (s / 2)

def classicalXi : ℂ → ℂ :=
  XiFromPrefactor classicalXiPrefactor

def ClassicalGammaNonzeroInStrip : Prop :=
  ∀ s : ℂ,
    0 < s.re →
    s.re < 1 →
    Complex.Gamma (s / 2) ≠ 0

/-!
# Basic complex arithmetic helpers
-/

theorem pi_complex_ne_zero_for_powers : (Real.pi : ℂ) ≠ 0 := by
  intro h
  have hre : Real.pi = 0 := by
    simpa using congr_arg Complex.re h
  exact ne_of_gt Real.pi_pos hre

theorem pi_cpow_ne_zero (w : ℂ) :
    (Real.pi : ℂ) ^ w ≠ 0 := by
  first
  | rw [Complex.cpow_ne_zero_iff]
    exact Or.inl pi_complex_ne_zero_for_powers
  | rw [Complex.cpow_def_of_ne_zero pi_complex_ne_zero_for_powers]
    exact Complex.exp_ne_zero _
  | intro h
    rw [Complex.eq_zero_cpow_iff] at h
    exact pi_complex_ne_zero_for_powers h.1

def PiPowerNonzeroAll : Prop :=
  ∀ w : ℂ, (Real.pi : ℂ) ^ w ≠ 0

theorem piPowerNonzeroAll_mathlib : PiPowerNonzeroAll :=
  pi_cpow_ne_zero

theorem half_re_pos {s : ℂ} (h0 : 0 < s.re) :
    0 < (s / 2).re := by
  simp [div_eq_mul_inv, mul_re, inv_re, normSq_ofReal]
  norm_num
  linarith

/-!
# Instantiate Gamma-nonzero from mathlib
-/

theorem classical_gamma_nonzero_instrip :
    ClassicalGammaNonzeroInStrip := by
  intro s h0 _
  exact @Complex.Gamma_ne_zero_of_re_pos (s / 2) (half_re_pos h0)

/-!
# Nonzero classical prefactor in the critical strip
-/

theorem classical_prefactor_nonzero_instrip
    (hGamma : ClassicalGammaNonzeroInStrip) :
    PrefactorNonzeroInStrip classicalXiPrefactor := by
  intro s h0 h1 hzero
  have hs0 : s ≠ 0 := by
    intro h
    have : (1 : ℝ) < 0 := by
      simpa [h, zero_re] using h0
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have hseq : s = 1 := by
      simpa using sub_eq_zero.mp h
    have : (1 : ℝ) < 1 := by
      simpa [hseq, one_re] using h1
    linarith
  have hhalf : (1 / 2 : ℂ) ≠ 0 := by
    intro h
    have hre : (1 / 2 : ℝ) = 0 := by
      simpa using congr_arg Complex.re h
    exact (by norm_num : (1 / 2 : ℝ) ≠ 0) hre
  have hPiPow : ((Real.pi : ℂ) ^ (-(s / 2))) ≠ 0 :=
    pi_cpow_ne_zero (-(s / 2))
  have hGamma' : Complex.Gamma (s / 2) ≠ 0 :=
    hGamma s h0 h1
  have hPrefactor : classicalXiPrefactor s ≠ 0 := by
    unfold classicalXiPrefactor
    refine mul_ne_zero ?_ hGamma'
    refine mul_ne_zero ?_ hPiPow
    refine mul_ne_zero ?_ hs1
    refine mul_ne_zero hhalf hs0
  exact hPrefactor hzero

def classicalXi_zero_equivalence_from_gamma
    (hGamma : ClassicalGammaNonzeroInStrip) :
    XiZeroEquivalence classicalXi :=
  xi_zero_equiv_zeta_zero classicalXiPrefactor
    (classical_prefactor_nonzero_instrip hGamma)

theorem rh_iff_xi_critical_from_gamma
    (hGamma : ClassicalGammaNonzeroInStrip) :
    RiemannHypothesisProp ↔ XiCriticalLineZeros classicalXi :=
  rh_iff_xi_critical_generic classicalXi
    (classicalXi_zero_equivalence_from_gamma hGamma)

/-!
# Shifted xi function and real-zero formulation
-/

noncomputable def xiShifted (z : ℂ) : ℂ :=
  classicalXi ((1 / 2 : ℂ) + I * z)

noncomputable def shiftedZeroPreimage (s : ℂ) : ℂ :=
  (s.im : ℂ) + I * ((1 / 2 : ℝ) - s.re)

theorem shiftedZeroPreimage_identity (s : ℂ) :
    (1 / 2 : ℂ) + I * shiftedZeroPreimage s = s := by
  apply Complex.ext
  · simp [shiftedZeroPreimage, mul_re, I_re, I_im, ofReal_re, ofReal_im]
  · simp [shiftedZeroPreimage, mul_im, I_re, I_im, ofReal_re, ofReal_im]

def XiShiftedZerosReal : Prop :=
  ∀ z : ℂ,
    xiShifted z = 0 →
    - (1 : ℝ) / 2 < z.im →
    z.im < (1 : ℝ) / 2 →
    z.im = 0

theorem xi_critical_line_zeros_iff_shifted_zeros_real :
    XiCriticalLineZeros classicalXi ↔ XiShiftedZerosReal := by
  constructor
  · intro h z hz hgt hlt
    let s := (1 / 2 : ℂ) + I * z
    have hz' : classicalXi s = 0 := by
      simpa [xiShifted, s] using hz
    have hs0 : 0 < s.re := by
      simp [s]
      linarith
    have hs1 : s.re < 1 := by
      simp [s]
      linarith
    have hline := h s hz' hs0 hs1
    have : (1 / 2 : ℝ) - z.im = 1 / 2 := by
      simpa [s] using hline
    linarith
  · intro h s hs h0 h1
    let z := shiftedZeroPreimage s
    have hz : xiShifted z = 0 := by
      unfold xiShifted
      rw [shiftedZeroPreimage_identity]
      exact hs
    have hzim : z.im = (1 / 2 : ℝ) - s.re := by
      simp [z, shiftedZeroPreimage]
    have hgt : - (1 : ℝ) / 2 < z.im := by
      rw [hzim]
      linarith
    have hlt : z.im < (1 : ℝ) / 2 := by
      rw [hzim]
      linarith
    have him0 := h z hz hgt hlt
    rw [hzim] at him0
    linarith

theorem rh_iff_xi_shifted_zeros_real_from_gamma
    (hGamma : ClassicalGammaNonzeroInStrip) :
    RiemannHypothesisProp ↔ XiShiftedZerosReal := by
  rw [rh_iff_xi_critical_from_gamma hGamma,
      xi_critical_line_zeros_iff_shifted_zeros_real]

/-!
# Exact off-real pointwise nonvanishing target
-/

def XiOffRealPointwiseNonvanishing : Prop :=
  ∀ z : ℂ,
    - (1 : ℝ) / 2 < z.im →
    z.im < (1 : ℝ) / 2 →
    z.im ≠ 0 →
    xiShifted z ≠ 0

theorem xiShiftedZerosReal_iff_off_real_pointwise_nonvanishing :
    XiShiftedZerosReal ↔ XiOffRealPointwiseNonvanishing := by
  constructor
  · intro h z hgt hlt hne hz
    have him := h z hz hgt hlt
    contradiction
  · intro h z hz hgt hlt
    by_contra hne
    exact h z hgt hlt hne hz

theorem rh_iff_xi_off_real_pointwise_nonvanishing_mathlib :
    RiemannHypothesisProp ↔ XiOffRealPointwiseNonvanishing := by
  rw [rh_iff_xi_shifted_zeros_real_from_gamma classical_gamma_nonzero_instrip,
      xiShiftedZerosReal_iff_off_real_pointwise_nonvanishing]

theorem rh_from_off_real_pointwise_nonvanishing
    (H : XiOffRealPointwiseNonvanishing) :
    RiemannHypothesisProp := by
  rw [rh_iff_xi_off_real_pointwise_nonvanishing_mathlib]
  exact H

/-!
# Functional equation, right-half zeros, and Step4
-/

def XiFunctionalEquation (xi : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → xi s = xi (1 - s)

def XiNoRightHalfZeros (xi : ℂ → ℂ) : Prop :=
  ∀ s : ℂ,
    xi s = 0 →
    (1 : ℝ) / 2 < s.re →
    s.re < 1 →
    False

def Step4Obligation : Prop :=
  XiNoRightHalfZeros classicalXi

theorem xi_critical_line_of_no_right_half
    (xi : ℂ → ℂ)
    (hFE : XiFunctionalEquation xi)
    (hNo : XiNoRightHalfZeros xi) :
    XiCriticalLineZeros xi := by
  intro s hs h0 h1
  by_contra hne
  by_cases hgt : (1 : ℝ) / 2 < s.re
  · exact hNo s hs hgt h1
  · have hle : s.re ≤ (1 : ℝ) / 2 := not_lt.mp hgt
    have hlt : s.re < (1 : ℝ) / 2 :=
      lt_of_le_of_ne hle hne
    let t := 1 - s
    have ht_zero : xi t = 0 := by
      dsimp [t]
      rw [← hFE s h0 h1]
      exact hs
    have ht_gt : (1 : ℝ) / 2 < t.re := by
      dsimp [t]
      linarith
    have ht_lt : t.re < 1 := by
      dsimp [t]
      linarith
    exact hNo t ht_zero ht_gt ht_lt

theorem no_right_half_of_critical_line
    (xi : ℂ → ℂ)
    (hCrit : XiCriticalLineZeros xi) :
    XiNoRightHalfZeros xi := by
  intro s hs hgt hlt
  have h0 : 0 < s.re := by linarith
  have hline := hCrit s hs h0 hlt
  linarith

theorem step4_iff_xi_critical_line
    (hFE : XiFunctionalEquation classicalXi) :
    Step4Obligation ↔ XiCriticalLineZeros classicalXi := by
  constructor
  · exact xi_critical_line_of_no_right_half classicalXi hFE
  · exact no_right_half_of_critical_line classicalXi

/-!
# Local zero-free and lower-bound rectangles
-/

structure XiLocalZeroFreeRect where
  x0 : ℝ
  x1 : ℝ
  y0 : ℝ
  y1 : ℝ
  x_lt : x0 < x1
  y_lt : y0 < y1
  no_zero :
    ∀ z : ℂ,
      x0 < z.re →
      z.re < x1 →
      y0 < z.im →
      z.im < y1 →
      xiShifted z ≠ 0

structure XiLocalLowerBoundRect where
  x0 : ℝ
  x1 : ℝ
  y0 : ℝ
  y1 : ℝ
  x_lt : x0 < x1
  y_lt : y0 < y1
  ε : ℝ
  ε_pos : 0 < ε
  lower_bound :
    ∀ z : ℂ,
      x0 < z.re →
      z.re < x1 →
      y0 < z.im →
      z.im < y1 →
      ε ≤ ‖xiShifted z‖

def XiLocalZeroFreeRect_of_lower_bound
    (B : XiLocalLowerBoundRect) :
    XiLocalZeroFreeRect where
  x0 := B.x0
  x1 := B.x1
  y0 := B.y0
  y1 := B.y1
  x_lt := B.x_lt
  y_lt := B.y_lt
  no_zero := by
    intro z hx0 hx1 hy0 hy1 hz
    have hle : B.ε ≤ 0 := by
      simpa [hz] using B.lower_bound z hx0 hx1 hy0 hy1
    linarith [B.ε_pos]

/-!
# Rectangular zero-free covers
-/

structure XiRectangularZeroFreeCover where
  rects : Set XiLocalZeroFreeRect
  covers :
    ∀ z : ℂ,
      - (1 : ℝ) / 2 < z.im →
      z.im < (1 : ℝ) / 2 →
      z.im ≠ 0 →
      ∃ R ∈ rects,
        R.x0 < z.re ∧
        z.re < R.x1 ∧
        R.y0 < z.im ∧
        z.im < R.y1

theorem xiOffRealPointwiseNonvanishing_of_rectangular_cover
    (cover : XiRectangularZeroFreeCover) :
    XiOffRealPointwiseNonvanishing := by
  intro z hgt hlt hne hz
  rcases cover.covers z hgt hlt hne with
    ⟨R, _, hx0, hx1, hy0, hy1⟩
  exact R.no_zero z hx0 hx1 hy0 hy1 hz

theorem rh_from_rectangular_zero_free_cover
    (cover : XiRectangularZeroFreeCover) :
    RiemannHypothesisProp :=
  rh_from_off_real_pointwise_nonvanishing
    (xiOffRealPointwiseNonvanishing_of_rectangular_cover cover)

structure XiLocalLowerBoundCover where
  rects : Set XiLocalLowerBoundRect
  covers :
    ∀ z : ℂ,
      - (1 : ℝ) / 2 < z.im →
      z.im < (1 : ℝ) / 2 →
      z.im ≠ 0 →
      ∃ R ∈ rects,
        R.x0 < z.re ∧
        z.re < R.x1 ∧
        R.y0 < z.im ∧
        z.im < R.y1

def zeroFreeCover_of_lowerBoundCover
    (C : XiLocalLowerBoundCover) :
    XiRectangularZeroFreeCover where
  rects := XiLocalZeroFreeRect_of_lower_bound '' C.rects
  covers := by
    intro z hgt hlt hne
    rcases C.covers z hgt hlt hne with
      ⟨B, hB, hx0, hx1, hy0, hy1⟩
    refine ⟨XiLocalZeroFreeRect_of_lower_bound B, ?_, hx0, hx1, hy0, hy1⟩
    exact Set.mem_image_of_mem XiLocalZeroFreeRect_of_lower_bound hB

theorem xiOffRealPointwiseNonvanishing_of_lower_bound_cover
    (C : XiLocalLowerBoundCover) :
    XiOffRealPointwiseNonvanishing :=
  xiOffRealPointwiseNonvanishing_of_rectangular_cover
    (zeroFreeCover_of_lowerBoundCover C)

theorem rh_from_local_lower_bound_cover
    (C : XiLocalLowerBoundCover) :
    RiemannHypothesisProp :=
  rh_from_off_real_pointwise_nonvanishing
    (xiOffRealPointwiseNonvanishing_of_lower_bound_cover C)

/-!
# Direct sufficient certificates
-/

structure XiModulusLowerBoundCertificate where
  ε : ℝ
  ε_pos : 0 < ε
  lower_bound :
    ∀ z : ℂ,
      - (1 : ℝ) / 2 < z.im →
      z.im < (1 : ℝ) / 2 →
      z.im ≠ 0 →
      ε ≤ ‖xiShifted z‖

theorem xiOffRealPointwiseNonvanishing_of_modulus_lower_bound
    (C : XiModulusLowerBoundCertificate) :
    XiOffRealPointwiseNonvanishing := by
  intro z hgt hlt hne hz
  have hle : C.ε ≤ 0 := by
    simpa [hz] using C.lower_bound z hgt hlt hne
  linarith [C.ε_pos]

theorem rh_from_modulus_lower_bound
    (C : XiModulusLowerBoundCertificate) :
    RiemannHypothesisProp :=
  rh_from_off_real_pointwise_nonvanishing
    (xiOffRealPointwiseNonvanishing_of_modulus_lower_bound C)

structure XiHalfPlaneAvoidanceCertificate where
  c : ℂ
  positive_re :
    ∀ z : ℂ,
      - (1 : ℝ) / 2 < z.im →
      z.im < (1 : ℝ) / 2 →
      z.im ≠ 0 →
      0 < (c * xiShifted z).re

theorem xiOffRealPointwiseNonvanishing_of_half_plane_avoidance
    (C : XiHalfPlaneAvoidanceCertificate) :
    XiOffRealPointwiseNonvanishing := by
  intro z hgt hlt hne hz
  have hp := C.positive_re z hgt hlt hne
  have hcontra : (0 : ℝ) < 0 := by
    simpa [hz] using hp
  exact lt_irrefl _ hcontra

theorem rh_from_half_plane_avoidance
    (C : XiHalfPlaneAvoidanceCertificate) :
    RiemannHypothesisProp :=
  rh_from_off_real_pointwise_nonvanishing
    (xiOffRealPointwiseNonvanishing_of_half_plane_avoidance C)

structure XiNegativeImaginaryPartCertificate where
  neg_im :
    ∀ z : ℂ,
      - (1 : ℝ) / 2 < z.im →
      z.im < (1 : ℝ) / 2 →
      z.im ≠ 0 →
      (xiShifted z).im < 0

theorem xiOffRealPointwiseNonvanishing_of_negative_imaginary_part
    (C : XiNegativeImaginaryPartCertificate) :
    XiOffRealPointwiseNonvanishing := by
  intro z hgt hlt hne hz
  have hn := C.neg_im z hgt hlt hne
  have hcontra : (0 : ℝ) < 0 := by
    simpa [hz] using hn
  exact lt_irrefl _ hcontra

theorem rh_from_negative_imaginary_part
    (C : XiNegativeImaginaryPartCertificate) :
    RiemannHypothesisProp :=
  rh_from_off_real_pointwise_nonvanishing
    (xiOffRealPointwiseNonvanishing_of_negative_imaginary_part C)

/-!
# Symmetry package and first-quadrant reduction
-/

def XiShiftedNegSymmetric : Prop :=
  ∀ z : ℂ, -(1 : ℝ) / 2 < z.im → z.im < (1 : ℝ) / 2 → xiShifted (-z) = xiShifted z

def XiShiftedConjugateSymmetric : Prop :=
  ∀ z : ℂ, -(1 : ℝ) / 2 < z.im → z.im < (1 : ℝ) / 2 → xiShifted (star z) = star (xiShifted z)

structure XiShiftedSymmetryPackage where
  neg_symm : XiShiftedNegSymmetric
  conj_symm : XiShiftedConjugateSymmetric

theorem xiShifted_fourfold_symmetry
    (P : XiShiftedSymmetryPackage)
    {z : ℂ}
    (hz : xiShifted z = 0)
    (hgt : -(1 : ℝ) / 2 < z.im)
    (hlt : z.im < (1 : ℝ) / 2) :
    xiShifted z = 0 ∧
    xiShifted (-z) = 0 ∧
    xiShifted (star z) = 0 ∧
    xiShifted (-star z) = 0 := by
  refine ⟨hz, ?_, ?_, ?_⟩
  · rw [P.neg_symm z hgt hlt]
    exact hz
  · rw [P.conj_symm z hgt hlt, hz]
    simp
  · rw [P.neg_symm (star z) (by simp [star]; linarith) (by simp [star]; linarith), P.conj_symm z hgt hlt, hz]
    simp

theorem nonvanishing_central_from_first_quadrant
    (P : XiShiftedSymmetryPackage)
    (X : ℝ)
    (h_quadrant :
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ X →
        0 < z.im →
        z.im < (1 : ℝ) / 2 →
        xiShifted z ≠ 0) :
    ∀ z : ℂ,
      -X ≤ z.re →
      z.re ≤ X →
      - (1 : ℝ) / 2 < z.im →
      z.im < (1 : ℝ) / 2 →
      z.im ≠ 0 →
      xiShifted z ≠ 0 := by
  intro z hxge hxle hygt hylt hyne hz
  have h4 := xiShifted_fourfold_symmetry P hz hygt hylt
  by_cases hpos : 0 < z.im
  · by_cases hre : 0 ≤ z.re
    · exact h_quadrant z hre hxle hpos hylt hz
    · let w := -star z
      have hw_re_ge : 0 ≤ w.re := by
        dsimp [w]; linarith
      have hw_re_le : w.re ≤ X := by
        dsimp [w]; linarith
      have hw_im_pos : 0 < w.im := by
        dsimp [w]; linarith
      have hw_im_lt : w.im < (1 : ℝ) / 2 := by
        dsimp [w]; linarith
      exact h_quadrant w hw_re_ge hw_re_le hw_im_pos hw_im_lt h4.2.2.2
  · have hneg : z.im < 0 := by
      have hle' : z.im ≤ 0 := not_lt.mp hpos
      exact lt_of_le_of_ne hle' hyne
    by_cases hre : 0 ≤ z.re
    · let w := star z
      have hw_re_ge : 0 ≤ w.re := by
        dsimp [w]; linarith
      have hw_re_le : w.re ≤ X := by
        dsimp [w]; linarith
      have hw_im_pos : 0 < w.im := by
        dsimp [w]; linarith
      have hw_im_lt : w.im < (1 : ℝ) / 2 := by
        dsimp [w]; linarith
      exact h_quadrant w hw_re_ge hw_re_le hw_im_pos hw_im_lt h4.2.2.1
    · let w := -z
      have hw_re_ge : 0 ≤ w.re := by
        dsimp [w]; linarith
      have hw_re_le : w.re ≤ X := by
        dsimp [w]; linarith
      have hw_im_pos : 0 < w.im := by
        dsimp [w]; linarith
      have hw_im_lt : w.im < (1 : ℝ) / 2 := by
        dsimp [w]; linarith
      exact h_quadrant w hw_re_ge hw_re_le hw_im_pos hw_im_lt h4.2.1

structure XiCentralPointwiseNonvanishingForX (X : ℝ) where
  central_nonvanishing :
    ∀ z : ℂ,
      -X ≤ z.re →
      z.re ≤ X →
      - (1 : ℝ) / 2 < z.im →
      z.im < (1 : ℝ) / 2 →
      z.im ≠ 0 →
      xiShifted z ≠ 0

structure XiTailPointwiseNonvanishingForX (X : ℝ) where
  right_nonvanishing :
    ∀ z : ℂ,
      X < z.re →
      - (1 : ℝ) / 2 < z.im →
      z.im < (1 : ℝ) / 2 →
      z.im ≠ 0 →
      xiShifted z ≠ 0
  left_nonvanishing :
    ∀ z : ℂ,
      z.re < -X →
      - (1 : ℝ) / 2 < z.im →
      z.im < (1 : ℝ) / 2 →
      z.im ≠ 0 →
      xiShifted z ≠ 0

theorem xiOffRealPointwiseNonvanishing_of_central_pointwise_and_tail_pointwise
    {X : ℝ}
    (C : XiCentralPointwiseNonvanishingForX X)
    (T : XiTailPointwiseNonvanishingForX X) :
    XiOffRealPointwiseNonvanishing := by
  intro z hgt hlt hne
  by_cases hright : X < z.re
  · exact T.right_nonvanishing z hright hgt hlt hne
  · by_cases hleft : z.re < -X
    · exact T.left_nonvanishing z hleft hgt hlt hne
    · have hle : z.re ≤ X := not_lt.mp hright
      have hge : -X ≤ z.re := not_lt.mp hleft
      exact C.central_nonvanishing z hge hle hgt hlt hne

/-!
# Central zero-free covers and two-sided tail certificates
-/

structure XiCentralZeroFreeCover (X : ℝ) where
  rects : List XiLocalZeroFreeRect
  covers :
    ∀ z : ℂ,
      -X ≤ z.re →
      z.re ≤ X →
      - (1 : ℝ) / 2 < z.im →
      z.im < (1 : ℝ) / 2 →
      z.im ≠ 0 →
      ∃ R ∈ rects,
        R.x0 < z.re ∧
        z.re < R.x1 ∧
        R.y0 < z.im ∧
        z.im < R.y1

def centralPointwise_of_zero_free_cover
    {X : ℝ}
    (C : XiCentralZeroFreeCover X) :
    XiCentralPointwiseNonvanishingForX X where
  central_nonvanishing := by
    intro z hge hle hgt hlt hne hz
    rcases C.covers z hge hle hgt hlt hne with
      ⟨R, _, hx0, hx1, hy0, hy1⟩
    exact R.no_zero z hx0 hx1 hy0 hy1 hz

structure XiTailAsymptoticLowerBoundForX (X : ℝ) where
  m : ℝ → ℝ
  m_pos :
    ∀ r : ℝ,
      X ≤ r →
      0 < m r
  bound :
    ∀ z : ℂ,
      (X < z.re ∨ z.re < -X) →
      - (1 : ℝ) / 2 < z.im →
      z.im < (1 : ℝ) / 2 →
      z.im ≠ 0 →
      m (abs z.re) ≤ ‖xiShifted z‖

def tailPointwise_of_asymptotic_lower_bound
    {X : ℝ}
    (A : XiTailAsymptoticLowerBoundForX X) :
    XiTailPointwiseNonvanishingForX X where
  right_nonvanishing := by
    intro z hright hgt hlt hne hz
    have hpos := A.m_pos (abs z.re) (by
      calc
        X ≤ z.re := le_of_lt hright
        _ ≤ abs z.re := le_abs_self z.re)
    have hbound := A.bound z (Or.inl hright) hgt hlt hne
    rw [hz] at hbound
    have : A.m (abs z.re) ≤ 0 := by
      simpa using hbound
    linarith
  left_nonvanishing := by
    intro z hleft hgt hlt hne hz
    have hpos := A.m_pos (abs z.re) (by
      have : X ≤ -z.re := by linarith
      calc
        X ≤ -z.re := this
        _ ≤ abs z.re := by
          simpa using le_abs_self (-z.re))
    have hbound := A.bound z (Or.inr hleft) hgt hlt hne
    rw [hz] at hbound
    have : A.m (abs z.re) ≤ 0 := by
      simpa using hbound
    linarith

structure XiExponentialTailEstimate (X : ℝ) where
  c : ℝ
  c_pos : 0 < c
  α : ℝ
  estimate :
    ∀ z : ℂ,
      (X < z.re ∨ z.re < -X) →
      - (1 : ℝ) / 2 < z.im →
      z.im < (1 : ℝ) / 2 →
      z.im ≠ 0 →
      c * Real.exp (-α * abs z.re) ≤ ‖xiShifted z‖

def tailAsymptotic_of_exponential
    {X : ℝ}
    (E : XiExponentialTailEstimate X) :
    XiTailAsymptoticLowerBoundForX X where
  m := fun r => E.c * Real.exp (-E.α * r)
  m_pos := by
    intro r _
    exact mul_pos E.c_pos (Real.exp_pos _)
  bound := E.estimate

theorem rh_from_central_zero_free_cover_and_tail_pointwise
    {X : ℝ}
    (C : XiCentralZeroFreeCover X)
    (T : XiTailPointwiseNonvanishingForX X) :
    RiemannHypothesisProp :=
  rh_from_off_real_pointwise_nonvanishing
    (xiOffRealPointwiseNonvanishing_of_central_pointwise_and_tail_pointwise
      (centralPointwise_of_zero_free_cover C) T)

theorem rh_from_central_zero_free_cover_and_asymptotic_tail
    {X : ℝ}
    (C : XiCentralZeroFreeCover X)
    (A : XiTailAsymptoticLowerBoundForX X) :
    RiemannHypothesisProp :=
  rh_from_central_zero_free_cover_and_tail_pointwise C
    (tailPointwise_of_asymptotic_lower_bound A)

theorem rh_from_central_zero_free_cover_and_exponential_tail
    {X : ℝ}
    (C : XiCentralZeroFreeCover X)
    (E : XiExponentialTailEstimate X) :
    RiemannHypothesisProp :=
  rh_from_central_zero_free_cover_and_asymptotic_tail C
    (tailAsymptotic_of_exponential E)

def xiCentralZeroFreeCover_of_two_rects
    (X : ℝ)
    (upper lower : XiLocalZeroFreeRect)
    (hupper :
      ∀ z : ℂ,
        0 < z.im →
        z.im < (1 : ℝ) / 2 →
        -X ≤ z.re →
        z.re ≤ X →
        upper.x0 < z.re ∧
        z.re < upper.x1 ∧
        upper.y0 < z.im ∧
        z.im < upper.y1)
    (hlower :
      ∀ z : ℂ,
        - (1 : ℝ) / 2 < z.im →
        z.im < 0 →
        -X ≤ z.re →
        z.re ≤ X →
        lower.x0 < z.re ∧
        z.re < lower.x1 ∧
        lower.y0 < z.im ∧
        z.im < lower.y1) :
    XiCentralZeroFreeCover X where
  rects := [upper, lower]
  covers := by
    intro z hge hle hgt hlt hne
    by_cases hpos : 0 < z.im
    · have h := hupper z hpos hlt hge hle
      exact ⟨upper, by simp, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
    · have hneg : z.im < 0 := by
        have hle' : z.im ≤ 0 := not_lt.mp hpos
        exact lt_of_le_of_ne hle' hne
      have h := hlower z hgt hneg hge hle
      exact ⟨lower, by simp, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem rh_from_two_rect_central_and_exponential_tail
    (X : ℝ)
    (upper lower : XiLocalZeroFreeRect)
    (hupper :
      ∀ z : ℂ,
        0 < z.im →
        z.im < (1 : ℝ) / 2 →
        -X ≤ z.re →
        z.re ≤ X →
        upper.x0 < z.re ∧
        z.re < upper.x1 ∧
        upper.y0 < z.im ∧
        z.im < upper.y1)
    (hlower :
      ∀ z : ℂ,
        - (1 : ℝ) / 2 < z.im →
        z.im < 0 →
        -X ≤ z.re →
        z.re ≤ X →
        lower.x0 < z.re ∧
        z.re < lower.x1 ∧
        lower.y0 < z.im ∧
        z.im < lower.y1)
    (E : XiExponentialTailEstimate X) :
    RiemannHypothesisProp :=
  rh_from_central_zero_free_cover_and_exponential_tail
    (xiCentralZeroFreeCover_of_two_rects X upper lower hupper hlower)
    E

structure RHProofCertificate where
  X : ℝ
  upper : XiLocalZeroFreeRect
  lower : XiLocalZeroFreeRect
  upper_covers :
    ∀ z : ℂ,
      0 < z.im →
      z.im < (1 : ℝ) / 2 →
      -X ≤ z.re →
      z.re ≤ X →
      upper.x0 < z.re ∧
      z.re < upper.x1 ∧
      upper.y0 < z.im ∧
      z.im < upper.y1
  lower_covers :
    ∀ z : ℂ,
      - (1 : ℝ) / 2 < z.im →
      z.im < 0 →
      -X ≤ z.re →
      z.re ≤ X →
      lower.x0 < z.re ∧
      z.re < lower.x1 ∧
      lower.y0 < z.im ∧
      z.im < lower.y1
  tail : XiExponentialTailEstimate X

theorem rh_from_RHProofCertificate
    (C : RHProofCertificate) :
    RiemannHypothesisProp :=
  rh_from_two_rect_central_and_exponential_tail
    C.X C.upper C.lower C.upper_covers C.lower_covers C.tail

/-!
# Right-tail asymptotic lower bound and first-quadrant proof
-/

structure XiRightTailAsymptoticLowerBoundForX (X : ℝ) where
  m : ℝ → ℝ
  m_pos :
    ∀ r : ℝ,
      X ≤ r →
      0 < m r
  bound :
    ∀ z : ℂ,
      X < z.re →
      - (1 : ℝ) / 2 < z.im →
      z.im < (1 : ℝ) / 2 →
      z.im ≠ 0 →
      m z.re ≤ ‖xiShifted z‖

def tailPointwise_from_right_asymptotic_and_symmetry
    {X : ℝ}
    (hsymm : XiShiftedNegSymmetric)
    (A : XiRightTailAsymptoticLowerBoundForX X) :
    XiTailPointwiseNonvanishingForX X where
  right_nonvanishing := by
    intro z hright hgt hlt hne hz
    have hpos := A.m_pos z.re (le_of_lt hright)
    have hbound := A.bound z hright hgt hlt hne
    rw [hz] at hbound
    have : A.m z.re ≤ 0 := by
      simpa using hbound
    linarith
  left_nonvanishing := by
    intro z hleft hgt hlt hne hz
    let w := -z
    have hw_re : X < w.re := by
      dsimp [w]
      linarith
    have hw_gt : - (1 : ℝ) / 2 < w.im := by
      dsimp [w]
      linarith
    have hw_lt : w.im < (1 : ℝ) / 2 := by
      dsimp [w]
      linarith
    have hw_ne : w.im ≠ 0 := by
      dsimp [w]
      intro h
      apply hne
      linarith
    have hw_zero : xiShifted w = 0 := by
      dsimp [w]
      rw [hsymm z hgt hlt]
      exact hz
    have hpos := A.m_pos w.re (le_of_lt hw_re)
    have hbound := A.bound w hw_re hw_gt hw_lt hw_ne
    rw [hw_zero] at hbound
    have : A.m w.re ≤ 0 := by
      simpa using hbound
    linarith

/-- A tail lower bound which is allowed to degenerate when approaching the critical
    line.  This is the natural shape for a zero-free certificate: known zeros on the
    critical line rule out a lower bound that is uniform in `z.im ≠ 0`. -/
structure XiRightTailDistanceLowerBoundForX (X : ℝ) where
  lower : ℝ → ℝ → ℝ
  lower_pos :
    ∀ r y : ℝ,
      X ≤ r →
      y ≠ 0 →
      0 < lower r y
  bound :
    ∀ z : ℂ,
      X < z.re →
      - (1 : ℝ) / 2 < z.im →
      z.im < (1 : ℝ) / 2 →
      z.im ≠ 0 →
      lower z.re z.im ≤ ‖xiShifted z‖

/-- A uniform positive lower bound is, in particular, a distance-sensitive one.
    This adapter keeps the corrected API compatible with any future stronger result. -/
def XiRightTailAsymptoticLowerBoundForX.toDistanceLowerBound
    {X : ℝ}
    (A : XiRightTailAsymptoticLowerBoundForX X) :
    XiRightTailDistanceLowerBoundForX X where
  lower r _ := A.m r
  lower_pos r _ hr _ := A.m_pos r hr
  bound z hre hgt hlt hne := A.bound z hre hgt hlt hne

/-- A positive distance-sensitive lower bound on the right tail gives the exact
    off-axis nonvanishing fact needed by the symmetry argument. -/
def tailPointwise_from_right_distance_lower_bound_and_symmetry
    {X : ℝ}
    (hsymm : XiShiftedNegSymmetric)
    (A : XiRightTailDistanceLowerBoundForX X) :
    XiTailPointwiseNonvanishingForX X where
  right_nonvanishing := by
    intro z hright hgt hlt hne hz
    have hpos := A.lower_pos z.re z.im (le_of_lt hright) hne
    have hbound := A.bound z hright hgt hlt hne
    rw [hz] at hbound
    have : A.lower z.re z.im ≤ 0 := by simpa using hbound
    linarith
  left_nonvanishing := by
    intro z hleft hgt hlt hne hz
    let w := -z
    have hw_re : X < w.re := by
      dsimp [w]
      linarith
    have hw_gt : - (1 : ℝ) / 2 < w.im := by
      dsimp [w]
      linarith
    have hw_lt : w.im < (1 : ℝ) / 2 := by
      dsimp [w]
      linarith
    have hw_ne : w.im ≠ 0 := by
      dsimp [w]
      intro h
      apply hne
      linarith
    have hw_zero : xiShifted w = 0 := by
      dsimp [w]
      rw [hsymm z hgt hlt]
      exact hz
    have hpos := A.lower_pos w.re w.im (le_of_lt hw_re) hw_ne
    have hbound := A.bound w hw_re hw_gt hw_lt hw_ne
    rw [hw_zero] at hbound
    have : A.lower w.re w.im ≤ 0 := by simpa using hbound
    linarith

structure RHFirstQuadrantProof where
  X : ℝ
  symmetries : XiShiftedSymmetryPackage
  quadrant_no_zero :
    ∀ z : ℂ,
      0 ≤ z.re →
      z.re ≤ X →
      0 < z.im →
      z.im < (1 : ℝ) / 2 →
      xiShifted z ≠ 0
  right_tail : XiRightTailAsymptoticLowerBoundForX X

theorem xiOffRealPointwiseNonvanishing_from_first_quadrant_proof
    (P : RHFirstQuadrantProof) :
    XiOffRealPointwiseNonvanishing := by
  have hsymm : XiShiftedNegSymmetric := P.symmetries.neg_symm
  let central : XiCentralPointwiseNonvanishingForX P.X :=
    {
      central_nonvanishing := by
        intro z hge hle hgt hlt hne
        exact
          nonvanishing_central_from_first_quadrant
            P.symmetries
            P.X
            P.quadrant_no_zero
            z
            hge
            hle
            hgt
            hlt
            hne
    }
  let tail : XiTailPointwiseNonvanishingForX P.X :=
    tailPointwise_from_right_asymptotic_and_symmetry hsymm P.right_tail
  exact
    xiOffRealPointwiseNonvanishing_of_central_pointwise_and_tail_pointwise
      central tail

theorem rh_from_first_quadrant_proof
    (P : RHFirstQuadrantProof) :
    RiemannHypothesisProp :=
  rh_from_off_real_pointwise_nonvanishing
    (xiOffRealPointwiseNonvanishing_from_first_quadrant_proof P)

/-- First-quadrant proof data with a tail bound that may shrink as the point
    approaches the critical line. -/
structure RHFirstQuadrantDistanceProof where
  X : ℝ
  symmetries : XiShiftedSymmetryPackage
  quadrant_no_zero :
    ∀ z : ℂ,
      0 ≤ z.re →
      z.re ≤ X →
      0 < z.im →
      z.im < (1 : ℝ) / 2 →
      xiShifted z ≠ 0
  right_tail : XiRightTailDistanceLowerBoundForX X

theorem xiOffRealPointwiseNonvanishing_from_first_quadrant_distance_proof
    (P : RHFirstQuadrantDistanceProof) :
    XiOffRealPointwiseNonvanishing := by
  have hsymm : XiShiftedNegSymmetric := P.symmetries.neg_symm
  let central : XiCentralPointwiseNonvanishingForX P.X :=
    {
      central_nonvanishing := by
        intro z hge hle hgt hlt hne
        exact
          nonvanishing_central_from_first_quadrant
            P.symmetries
            P.X
            P.quadrant_no_zero
            z
            hge
            hle
            hgt
            hlt
            hne
    }
  let tail : XiTailPointwiseNonvanishingForX P.X :=
    tailPointwise_from_right_distance_lower_bound_and_symmetry hsymm P.right_tail
  exact
    xiOffRealPointwiseNonvanishing_of_central_pointwise_and_tail_pointwise
      central tail

theorem rh_from_first_quadrant_distance_proof
    (P : RHFirstQuadrantDistanceProof) :
    RiemannHypothesisProp :=
  rh_from_off_real_pointwise_nonvanishing
    (xiOffRealPointwiseNonvanishing_from_first_quadrant_distance_proof P)

/-!
# Safe derivations of shifted symmetries from classical xi facts
-/

def ClassicalXiFunctionalEq : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → classicalXi (1 - s) = classicalXi s

theorem xiShifted_neg_symmetric_from_functional_eq
    (hFE : ClassicalXiFunctionalEq) :
    XiShiftedNegSymmetric := by
  intro z hgt hlt
  simp only [xiShifted]
  have h : (1 / 2 : ℂ) + I * (-z) = 1 - ((1 / 2 : ℂ) + I * z) := by
    ring
  rw [h]
  apply hFE ((1 / 2 : ℂ) + I * z)
  · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]; ring; linarith
  · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]; ring; linarith

theorem xiShifted_conjugate_symmetric_from_identity
    (h :
      ∀ z : ℂ,
        -(1 : ℝ) / 2 < z.im →
        z.im < (1 : ℝ) / 2 →
        classicalXi ((1 / 2 : ℂ) + I * star z) =
        star (classicalXi ((1 / 2 : ℂ) + I * z))) :
    XiShiftedConjugateSymmetric := by
  intro z hgt hlt
  simpa [xiShifted] using h z hgt hlt

/-!
# Decomposed first-quadrant certificates
-/

structure FunctionalEquationCertificate where
  fe : ClassicalXiFunctionalEq

structure CompletedFunctionalEquationReduction (Λ₀ : ℂ → ℂ) where
  c : ℂ
  eq :
    ∀ s : ℂ,
      classicalXi s = c * Λ₀ s
  fe :
    ∀ s : ℂ,
      Λ₀ (1 - s) = Λ₀ s

theorem functionalEquationCertificate_from_completed_reduction
    {Λ₀ : ℂ → ℂ}
    (R : CompletedFunctionalEquationReduction Λ₀) :
    FunctionalEquationCertificate where
  fe := by
    intro s _ _
    calc
      classicalXi (1 - s)
          = R.c * Λ₀ (1 - s) := by
        rw [R.eq (1 - s)]
      _ = R.c * Λ₀ s := by
        rw [R.fe s]
      _ = classicalXi s := by
        rw [← R.eq s]

structure ConjugationIdentityCertificate where
  identity :
    ∀ z : ℂ,
      -(1 : ℝ) / 2 < z.im →
      z.im < (1 : ℝ) / 2 →
      classicalXi ((1 / 2 : ℂ) + I * star z) =
      star (classicalXi ((1 / 2 : ℂ) + I * z))

structure SymmetryCertificate where
  functional_eq : FunctionalEquationCertificate
  conjugation_identity : ConjugationIdentityCertificate

def xiShiftedSymmetryPackage_of_certificates
    (S : SymmetryCertificate) :
    XiShiftedSymmetryPackage where
  neg_symm :=
    xiShifted_neg_symmetric_from_functional_eq S.functional_eq.fe
  conj_symm :=
    xiShifted_conjugate_symmetric_from_identity S.conjugation_identity.identity

structure FirstQuadrantLowerBoundCover (X : ℝ) where
  rects : List XiLocalLowerBoundRect
  covers :
    ∀ z : ℂ,
      0 ≤ z.re →
      z.re ≤ X →
      0 < z.im →
      z.im < (1 : ℝ) / 2 →
      ∃ R ∈ rects,
        R.x0 < z.re ∧
        z.re < R.x1 ∧
        R.y0 < z.im ∧
        z.im < R.y1

theorem quadrant_no_zero_of_lower_bound_cover
    {X : ℝ}
    (C : FirstQuadrantLowerBoundCover X) :
    ∀ z : ℂ,
      0 ≤ z.re →
      z.re ≤ X →
      0 < z.im →
      z.im < (1 : ℝ) / 2 →
      xiShifted z ≠ 0 := by
  intro z hre0 hreX him0 him1 hz
  rcases C.covers z hre0 hreX him0 him1 with
    ⟨R, _, hx0, hx1, hy0, hy1⟩
  exact (XiLocalZeroFreeRect_of_lower_bound R).no_zero z hx0 hx1 hy0 hy1 hz

structure RightTailExponentialCertificate (X : ℝ) where
  c : ℝ
  c_pos : 0 < c
  α : ℝ
  estimate :
    ∀ z : ℂ,
      X < z.re →
      - (1 : ℝ) / 2 < z.im →
      z.im < (1 : ℝ) / 2 →
      z.im ≠ 0 →
      c * Real.exp (-α * z.re) ≤ ‖xiShifted z‖

def rightTailAsymptotic_of_exponential
    {X : ℝ}
    (E : RightTailExponentialCertificate X) :
    XiRightTailAsymptoticLowerBoundForX X where
  m := fun r => E.c * Real.exp (-E.α * r)
  m_pos := by
    intro r _
    exact mul_pos E.c_pos (Real.exp_pos _)
  bound := E.estimate

structure RHFirstQuadrantDecomposedCertificate (X : ℝ) where
  sym : SymmetryCertificate
  quadrant : FirstQuadrantLowerBoundCover X
  tail : RightTailExponentialCertificate X

def rhFirstQuadrantProof_of_decomposed
    {X : ℝ}
    (D : RHFirstQuadrantDecomposedCertificate X) :
    RHFirstQuadrantProof where
  X := X
  symmetries :=
    xiShiftedSymmetryPackage_of_certificates D.sym
  quadrant_no_zero :=
    quadrant_no_zero_of_lower_bound_cover D.quadrant
  right_tail :=
    rightTailAsymptotic_of_exponential D.tail

theorem rh_from_decomposed_first_quadrant_certificate
    {X : ℝ}
    (D : RHFirstQuadrantDecomposedCertificate X) :
    RiemannHypothesisProp :=
  rh_from_first_quadrant_proof
    (rhFirstQuadrantProof_of_decomposed D)

/-- Decomposed first-quadrant certificate with a tail lower bound that may
    vanish at the critical line, as it must in the presence of critical-line zeros. -/
structure RHFirstQuadrantDistanceDecomposedCertificate (X : ℝ) where
  sym : SymmetryCertificate
  quadrant : FirstQuadrantLowerBoundCover X
  tail : XiRightTailDistanceLowerBoundForX X

def rhFirstQuadrantDistanceProof_of_decomposed
    {X : ℝ}
    (D : RHFirstQuadrantDistanceDecomposedCertificate X) :
    RHFirstQuadrantDistanceProof where
  X := X
  symmetries :=
    xiShiftedSymmetryPackage_of_certificates D.sym
  quadrant_no_zero :=
    quadrant_no_zero_of_lower_bound_cover D.quadrant
  right_tail := D.tail

theorem rh_from_decomposed_first_quadrant_distance_certificate
    {X : ℝ}
    (D : RHFirstQuadrantDistanceDecomposedCertificate X) :
    RiemannHypothesisProp :=
  rh_from_first_quadrant_distance_proof
    (rhFirstQuadrantDistanceProof_of_decomposed D)

/-- Any certificate satisfying the older, stronger uniform-tail condition also
    satisfies the distance-sensitive formulation. -/
def RHFirstQuadrantDecomposedCertificate.toDistanceCertificate
    {X : ℝ}
    (D : RHFirstQuadrantDecomposedCertificate X) :
    RHFirstQuadrantDistanceDecomposedCertificate X where
  sym := D.sym
  quadrant := D.quadrant
  tail := (rightTailAsymptotic_of_exponential D.tail).toDistanceLowerBound

/-!
# Mathlib-native completed xi chain
-/

def xiMathlib (s : ℂ) : ℂ :=
  completedRiemannZeta₀ s

noncomputable def xiMathlibShifted (z : ℂ) : ℂ :=
  xiMathlib ((1 / 2 : ℂ) + I * z)

theorem xiMathlib_functional_equation :
    ∀ s : ℂ,
      xiMathlib (1 - s) = xiMathlib s :=
  completedRiemannZeta₀_one_sub

theorem xiMathlibShifted_neg_symmetric :
    ∀ z : ℂ,
      xiMathlibShifted (-z) = xiMathlibShifted z := by
  intro z
  simp only [xiMathlibShifted]
  have h :
      (1 / 2 : ℂ) + I * (-z) =
      1 - ((1 / 2 : ℂ) + I * z) := by
    ring
  rw [h, xiMathlib_functional_equation]

def XiMathlibZeroEquivalence : Prop :=
  XiZeroEquivalence xiMathlib

def XiMathlibShiftedZerosReal : Prop :=
  ∀ z : ℂ,
    xiMathlibShifted z = 0 →
    - (1 : ℝ) / 2 < z.im →
    z.im < (1 : ℝ) / 2 →
    z.im = 0

def XiMathlibOffRealPointwiseNonvanishing : Prop :=
  ∀ z : ℂ,
    - (1 : ℝ) / 2 < z.im →
    z.im < (1 : ℝ) / 2 →
    z.im ≠ 0 →
    xiMathlibShifted z ≠ 0

theorem xiMathlibShiftedZerosReal_iff_offRealNonvanishing :
    XiMathlibShiftedZerosReal ↔ XiMathlibOffRealPointwiseNonvanishing := by
  constructor
  · intro h z hgt hlt hne hz
    have him := h z hz hgt hlt
    contradiction
  · intro h z hz hgt hlt
    by_contra hne
    exact h z hgt hlt hne hz

theorem xiMathlib_critical_line_zeros_iff_shifted_real :
    XiCriticalLineZeros xiMathlib ↔ XiMathlibShiftedZerosReal := by
  constructor
  · intro h z hz hgt hlt
    let s := (1 / 2 : ℂ) + I * z
    have hz' : xiMathlib s = 0 := by
      simpa [xiMathlibShifted, s] using hz
    have hs0 : 0 < s.re := by
      simp [s]
      linarith
    have hs1 : s.re < 1 := by
      simp [s]
      linarith
    have hline := h s hz' hs0 hs1
    have : (1 / 2 : ℝ) - z.im = 1 / 2 := by
      simpa [s] using hline
    linarith
  · intro h s hs h0 h1
    let z := shiftedZeroPreimage s
    have hz : xiMathlibShifted z = 0 := by
      unfold xiMathlibShifted
      rw [shiftedZeroPreimage_identity]
      exact hs
    have hzim : z.im = (1 / 2 : ℝ) - s.re := by
      simp [z, shiftedZeroPreimage]
    have hgt : - (1 : ℝ) / 2 < z.im := by
      rw [hzim]
      linarith
    have hlt : z.im < (1 : ℝ) / 2 := by
      rw [hzim]
      linarith
    have him0 := h z hz hgt hlt
    rw [hzim] at him0
    linarith

theorem rh_iff_xiMathlib_shifted_real
    (hEquiv : XiMathlibZeroEquivalence) :
    RiemannHypothesisProp ↔ XiMathlibShiftedZerosReal := by
  have hCritical :
      RiemannHypothesisProp ↔ XiCriticalLineZeros xiMathlib := by
    constructor
    · exact xi_of_rh xiMathlib hEquiv
    · exact rh_of_xi xiMathlib hEquiv
  rw [hCritical, xiMathlib_critical_line_zeros_iff_shifted_real]

theorem rh_iff_xiMathlib_off_real_nonvanishing
    (hEquiv : XiMathlibZeroEquivalence) :
    RiemannHypothesisProp ↔ XiMathlibOffRealPointwiseNonvanishing := by
  rw [rh_iff_xiMathlib_shifted_real hEquiv,
      xiMathlibShiftedZerosReal_iff_offRealNonvanishing]

structure XiMathlibDirectCertificate where
  zero_equiv : XiMathlibZeroEquivalence
  nonvanishing : XiMathlibOffRealPointwiseNonvanishing

theorem rh_from_xiMathlib_direct_certificate
    (C : XiMathlibDirectCertificate) :
    RiemannHypothesisProp := by
  rw [rh_iff_xiMathlib_off_real_nonvanishing C.zero_equiv]
  exact C.nonvanishing

/-!
# Normalization between mathlib xi and classical xi
-/

structure XiMathlibClassicalNormalization where
  c : ℂ
  c_nonzero : c ≠ 0
  eq :
    ∀ s : ℂ,
      xiMathlib s = c * classicalXi s

theorem xiMathlibShifted_eq_c_xiShifted
    (N : XiMathlibClassicalNormalization)
    (z : ℂ) :
    xiMathlibShifted z = N.c * xiShifted z := by
  simp [xiMathlibShifted, xiShifted, N.eq]

theorem xiMathlibZeroEquivalence_from_classical_normalization
    (N : XiMathlibClassicalNormalization) :
    XiMathlibZeroEquivalence := by
  intro s h0 h1
  have h_equiv :=
    (classicalXi_zero_equivalence_from_gamma classical_gamma_nonzero_instrip) s h0 h1
  constructor
  · intro h
    rw [N.eq] at h
    have hxi : classicalXi s = 0 :=
      (mul_eq_zero.mp h).resolve_left N.c_nonzero
    exact h_equiv.mp hxi
  · intro hz
    have hxi := h_equiv.mpr hz
    rw [N.eq, hxi, mul_zero]

theorem xiMathlibOffReal_from_classicalOffReal
    (N : XiMathlibClassicalNormalization)
    (H : XiOffRealPointwiseNonvanishing) :
    XiMathlibOffRealPointwiseNonvanishing := by
  intro z hgt hlt hne hz
  have h_eq := xiMathlibShifted_eq_c_xiShifted N z
  rw [h_eq] at hz
  have hxi : xiShifted z = 0 :=
    (mul_eq_zero.mp hz).resolve_left N.c_nonzero
  exact H z hgt hlt hne hxi

theorem rh_from_normalization_and_classical_nonvanishing
    (N : XiMathlibClassicalNormalization)
    (H : XiOffRealPointwiseNonvanishing) :
    RiemannHypothesisProp :=
  rh_from_xiMathlib_direct_certificate
    {
      zero_equiv :=
        xiMathlibZeroEquivalence_from_classical_normalization N
      nonvanishing :=
        xiMathlibOffReal_from_classicalOffReal N H
    }

theorem rh_from_normalization_and_first_quadrant_proof
    (N : XiMathlibClassicalNormalization)
    (P : RHFirstQuadrantProof) :
    RiemannHypothesisProp :=
  rh_from_normalization_and_classical_nonvanishing
    N
    (xiOffRealPointwiseNonvanishing_from_first_quadrant_proof P)

/-!
# Hurwitz Λ₀ normalization bridge
-/

structure HurwitzLambda0Normalization where
  k : ℂ
  k_nonzero : k ≠ 0
  eq :
    ∀ s : ℂ,
      (HurwitzZeta.hurwitzEvenFEPair 0).Λ₀ (s / 2) =
      k * classicalXi s

def xiMathlibClassicalNormalization_from_lambda0
    (H : HurwitzLambda0Normalization) :
    XiMathlibClassicalNormalization where
  c := H.k / 2
  c_nonzero := by
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    exact div_ne_zero H.k_nonzero h2
  eq := by
    intro s
    simp only [xiMathlib, completedRiemannZeta₀, HurwitzZeta.completedHurwitzZetaEven₀]
    rw [H.eq]
    ring_nf

theorem rh_from_lambda0_normalization_and_xiMathlib_nonvanishing
    (H : HurwitzLambda0Normalization)
    (HV : XiMathlibOffRealPointwiseNonvanishing) :
    RiemannHypothesisProp :=
  rh_from_xiMathlib_direct_certificate
    {
      zero_equiv :=
        xiMathlibZeroEquivalence_from_classical_normalization
          (xiMathlibClassicalNormalization_from_lambda0 H)
      nonvanishing := HV
    }

theorem rh_from_lambda0_normalization_and_classical_nonvanishing
    (H : HurwitzLambda0Normalization)
    (HV : XiOffRealPointwiseNonvanishing) :
    RiemannHypothesisProp :=
  rh_from_normalization_and_classical_nonvanishing
    (xiMathlibClassicalNormalization_from_lambda0 H)
    HV

theorem rh_from_lambda0_normalization_and_first_quadrant_proof
    (H : HurwitzLambda0Normalization)
    (P : RHFirstQuadrantProof) :
    RiemannHypothesisProp :=
  rh_from_normalization_and_first_quadrant_proof
    (xiMathlibClassicalNormalization_from_lambda0 H)
    P

/-!
# Kernel simplification in the Riemann case a = 0
-/

theorem evenKernel_zero_eq_cosKernel_zero (x : ℝ) :
    (HurwitzZeta.evenKernel 0 x : ℂ) =
    (HurwitzZeta.cosKernel 0 x : ℂ) := by
  have h0 : ((0 : ℝ) : UnitAddCircle) = 0 := by simp
  have h_even := HurwitzZeta.evenKernel_def (0 : ℝ) x
  have h_cos := HurwitzZeta.cosKernel_def (0 : ℝ) x
  simp [h0] at h_even h_cos
  rw [h_even, h_cos]

theorem evenKernel_zero_eq_cosKernel_zero_real (x : ℝ) :
    HurwitzZeta.evenKernel 0 x =
    HurwitzZeta.cosKernel 0 x := by
  have h := evenKernel_zero_eq_cosKernel_zero x
  have := congr_arg Complex.re h
  simpa using this

/-!
# Final open certificate targets
-/

def RHOpenTarget : Prop :=
  XiOffRealPointwiseNonvanishing

def RHMathlibOpenTarget : Prop :=
  XiMathlibOffRealPointwiseNonvanishing

def RHFirstQuadrantOpenTarget : Type :=
  RHFirstQuadrantProof

def RHHurwitzNormalizationOpenTarget : Type :=
  HurwitzLambda0Normalization

def RHStep4OpenTarget : Prop :=
  Step4Obligation

end

/-! ## Decomposition of `XiNoRightHalfZeros` into a classical zero‑free region and a residual thin region -/

open Real

/-- Classical zero‑free region for ζ (and thus for ξ).
  There exist constants C > 0, T₀ ≥ 0 such that for all s with Re(s) ≥ 1 - C / log(|Im(s)|+2) and |Im(s)| ≥ T₀,
  ζ(s) ≠ 0.  Since ξ(s) = prefactor(s) * ζ(s) and the prefactor is non‑zero in the critical strip,
  this gives a zero‑free region for ξ as well. -/
structure ClassicalZeroFreeRegion where
  (C T₀ : ℝ)
  (C_pos : 0 < C)
  (zero_free : ∀ s : ℂ, 1 - C / Real.log (|s.im| + 2) ≤ s.re → s.re < 1 → T₀ ≤ |s.im| → classicalXi s ≠ 0)

/-- The “thin” region that is not covered by the classical zero‑free region:
    {s | 1/2 < s.re < 1 - C / log(|s.im|+2)} for large enough |s.im|.
    A potential off‑critical‑line zero must lie here. -/
def ThinRegionNonVanishing (C T₀ : ℝ) : Prop :=
  ∀ s : ℂ,
    1/2 < s.re →
    s.re < 1 - C / Real.log (|s.im| + 2) →
    T₀ ≤ |s.im| →
    classicalXi s ≠ 0

/-- The full zero‑free right half statement. -/
def XiNoRightHalfZerosFull : Prop :=
  ∀ s : ℂ, 1/2 < s.re → s.re < 1 → classicalXi s ≠ 0

/-- A finite cover of the bounded‑imaginary‑part region of the right half of the critical strip. -/
structure FiniteBoundedRectCover (T₀ : ℝ) : Prop where
  covers :
    ∀ s : ℂ,
      1 / 2 < s.re →
      s.re < 1 →
      |s.im| < T₀ →
      classicalXi s ≠ 0

/-- The full three-part decomposition: classical zero-free region + thin region + bounded rectangle cover. -/
theorem xiNoRightHalfZerosFull_from_all_three
    (h_classical : ClassicalZeroFreeRegion)
    (h_thin : ThinRegionNonVanishing h_classical.C h_classical.T₀)
    (h_bounded : FiniteBoundedRectCover h_classical.T₀) :
    XiNoRightHalfZerosFull := by
  intro s hs_gt hs_lt
  rcases h_classical with ⟨C, T₀, C_pos, hZ⟩
  by_cases hT : |s.im| < T₀
  · exact h_bounded.covers s hs_gt hs_lt hT
  · push_neg at hT
    by_cases h_covered : 1 - C / Real.log (|s.im| + 2) ≤ s.re
    · exact hZ s h_covered hs_lt hT
    · have h_re_gt : 1/2 < s.re := hs_gt
      have h_re_lt : s.re < 1 - C / Real.log (|s.im| + 2) := by linarith
      exact h_thin s h_re_gt h_re_lt hT

/-!
# Closing the functional equation for classicalXi
-/

/-- Helper: classicalXi s = (1/2)*s*(s-1)*(Λ₀(s) - 1/s - 1/(1-s)) on the critical strip.
    Proved by rewriting ζ via riemannZeta_eq_completedRiemannZeta₀ and cancelling π^{-s/2}Γ(s/2). -/
private theorem classicalXi_eq_completed (s : ℂ) (hs0 : s ≠ 0) (hGamma : Complex.Gamma (s / 2) ≠ 0) :
    classicalXi s = (1 / 2 : ℂ) * s * (s - 1) *
      (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) := by
  show classicalXiPrefactor s * zeta s = _
  unfold zeta
  rw [riemannZeta_eq_completedRiemannZeta₀ hs0]
  unfold classicalXiPrefactor
  field_simp [hGamma]

/-- `completedRiemannZeta₀` consists of the genuinely completed zeta term together
    with its two polar corrections.  In particular, on vertical lines the corrections
    have size of order `|Im s|⁻²`; one must subtract them before seeking cubic (or
    faster) decay. -/
theorem completedRiemannZeta₀_eq_polar_plus_xi (s : ℂ) (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) (hGamma : Complex.Gamma (s / 2) ≠ 0) :
    completedRiemannZeta₀ s = 1 / s + 1 / (1 - s) +
      2 * classicalXi s / (s * (s - 1)) := by
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  rw [classicalXi_eq_completed s hs0 hGamma]
  field_simp [hs0, hs1, h1s]
  ring

/-- On the critical line, the two polar corrections in `completedRiemannZeta₀`
    combine to the real term `1 / (t² + 1/4)`. -/
theorem critical_line_polar_correction (t : ℝ) :
    1 / ((1 / 2 : ℂ) + I * t) +
      1 / (1 - ((1 / 2 : ℂ) + I * t)) =
        (1 / (t ^ 2 + 1 / 4 : ℝ) : ℂ) := by
  have h1 : ((1 / 2 : ℂ) + I * t) ≠ 0 := by
    intro h; have := congrArg Complex.re h; norm_num at this
  have h2 : (1 / 2 : ℂ) - I * t ≠ 0 := by
    intro h; have := congrArg Complex.re h; norm_num at this
  rw [show (1 : ℂ) - ((1 / 2 : ℂ) + I * t) = (1 / 2 : ℂ) - I * t from by ring]
  rw [one_div_add_one_div h1 h2]
  have hprod : ((1 / 2 : ℂ) + I * t) * ((1 / 2 : ℂ) - I * t) = (t ^ 2 + 1 / 4 : ℂ) := by
    ring_nf; simp only [Complex.I_sq]; ring_nf
  have hsum : ((1 / 2 : ℂ) + I * t) + ((1 / 2 : ℂ) - I * t) = (1 : ℂ) := by ring
  rw [hsum, hprod, show (1 : ℂ) / (t ^ 2 + 1 / 4 : ℂ) = (1 / (t ^ 2 + 1 / 4 : ℝ) : ℂ) from by simp]

/-- Exact critical-line decomposition.  The final summand is the part controlled
    by the classical xi function; the first summand is the unavoidable polar term. -/
theorem completedRiemannZeta₀_critical_line_decomposition (t : ℝ) :
    completedRiemannZeta₀ ((1 / 2 : ℂ) + I * t) =
      (1 / (t ^ 2 + 1 / 4) : ℝ) +
        2 * classicalXi ((1 / 2 : ℂ) + I * t) /
          (((1 / 2 : ℂ) + I * t) * ((1 / 2 : ℂ) + I * t - 1)) := by
  have hs0 : (1 / 2 : ℂ) + I * t ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hs1 : (1 / 2 : ℂ) + I * t ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hGamma : Complex.Gamma (((1 / 2 : ℂ) + I * t) / 2) ≠ 0 :=
    classical_gamma_nonzero_instrip _ (by norm_num) (by norm_num)
  rw [completedRiemannZeta₀_eq_polar_plus_xi _ hs0 hs1 hGamma,
    critical_line_polar_correction]
  norm_cast

/-- After subtracting the polar term, the critical-line remainder is exactly a
    rational multiple of the classical xi function. -/
theorem completedRiemannZeta₀_critical_line_remainder (t : ℝ) :
    completedRiemannZeta₀ ((1 / 2 : ℂ) + I * t) -
      (1 / (t ^ 2 + 1 / 4) : ℝ) =
        2 * classicalXi ((1 / 2 : ℂ) + I * t) /
          (((1 / 2 : ℂ) + I * t) * ((1 / 2 : ℂ) + I * t - 1)) := by
  rw [completedRiemannZeta₀_critical_line_decomposition]
  ring

/-- The quadratic factor in the critical-line remainder is the negative real
    number `t² + 1/4`. -/
theorem critical_line_quadratic_factor (t : ℝ) :
    ((1 / 2 : ℂ) + I * t) * ((1 / 2 : ℂ) + I * t - 1) =
      -(t ^ 2 + 1 / 4 : ℝ) := by
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The polar-subtracted completion is a real scalar multiple of `classicalXi`
    on the critical line. -/
theorem completedRiemannZeta₀_critical_line_remainder_eq_xi (t : ℝ) :
    completedRiemannZeta₀ ((1 / 2 : ℂ) + I * t) -
      (1 / (t ^ 2 + 1 / 4) : ℝ) =
        -(2 / (t ^ 2 + 1 / 4) : ℝ) *
          classicalXi ((1 / 2 : ℂ) + I * t) := by
  rw [completedRiemannZeta₀_critical_line_remainder,
    critical_line_quadratic_factor]
  have ht : (t ^ 2 + 1 / 4 : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; norm_num at this; norm_cast at this
    linarith [sq_nonneg t]
  push_cast
  field_simp [ht]

/-- Norm form of the critical-line remainder identity. -/
theorem norm_completedRiemannZeta₀_critical_line_remainder (t : ℝ) :
    ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + I * t) -
      (1 / (t ^ 2 + 1 / 4) : ℝ)‖ =
        (2 / (t ^ 2 + 1 / 4) : ℝ) *
          ‖classicalXi ((1 / 2 : ℂ) + I * t)‖ := by
  rw [completedRiemannZeta₀_critical_line_remainder_eq_xi, norm_mul]
  have ht : 0 < t ^ 2 + 1 / 4 := by positivity
  rw [norm_neg, Complex.norm_of_nonneg (by positivity : 0 ≤ (2 / (t ^ 2 + 1 / 4) : ℝ))]

/-- The classical xi function satisfies ξ(s) = ξ(1-s) on the critical strip.
    Both sides reduce to (1/2)*s*(s-1)*(Λ₀(s) - 1/s - 1/(1-s)) via
    classicalXi_eq_completed and completedRiemannZeta₀_one_sub. -/
theorem classicalXi_functional_equation :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → classicalXi (1 - s) = classicalXi s := by
  intro s h0 h1
  have hs0 : s ≠ 0 := by intro h; subst h; norm_num at h0
  have hs1 : s ≠ 1 := by intro h; subst h; norm_num at h1
  have hs1s : (1 : ℂ) - s ≠ 0 := by
    intro h
    apply hs1
    rw [show s = (1 : ℂ) - ((1 : ℂ) - s) from by ring, h]
    ring
  have hGamma := classical_gamma_nonzero_instrip s h0 h1
  have hGamma1s : Complex.Gamma ((1 - s) / 2) ≠ 0 := by
    apply classical_gamma_nonzero_instrip
    · rw [sub_re, one_re]; linarith
    · rw [sub_re, one_re]; linarith
  rw [classicalXi_eq_completed s hs0 hGamma, classicalXi_eq_completed (1-s) hs1s hGamma1s]
  rw [completedRiemannZeta₀_one_sub]
  ring_nf

theorem real_pos_cpow_star (x : ℝ) (hx : 0 < x) (s : ℂ) :
    star ((x : ℂ) ^ s) = (x : ℂ) ^ (star s) := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast Ne.symm (ne_of_lt hx)
  have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) := (ofReal_log hx.le).symm
  show starRingEnd ℂ ((x : ℂ) ^ s) = (x : ℂ) ^ (starRingEnd ℂ s)
  rw [Complex.cpow_def_of_ne_zero hx', Complex.cpow_def_of_ne_zero hx', hlog,
    (exp_conj _).symm]
  congr 1
  rw [RingHom.map_mul, show starRingEnd ℂ ((Real.log x : ℂ)) = (Real.log x : ℂ) from by simp]

/-!
# Conjugation symmetry for riemannZeta

Key building block for the symmetry package: riemannZeta (star s) = star (riemannZeta s).
Proved for Re(s) > 1 via the Dirichlet series, extended to all s by analytic continuation.
-/

private theorem nat_cpow_star (n : ℕ) (s : ℂ) :
    star ((↑n + 1 : ℂ) ^ s) = (↑n + 1 : ℂ) ^ (star s) := by
  have hcpow := real_pos_cpow_star (n + 1) (by exact_mod_cast Nat.succ_pos n) s
  exact_mod_cast hcpow

theorem riemannZeta_star_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    riemannZeta (star s) = star (riemannZeta s) := by
  have hs' : 1 < (star s).re := by simp [star_def]; linarith
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs',
      zeta_eq_tsum_one_div_nat_add_one_cpow hs, tsum_star]
  congr 1; ext n
  have hcpow := nat_cpow_star n s
  simp only [div_eq_mul_inv, star_mul, star_one, one_mul, star_inv, ← hcpow]
  norm_num

/-- riemannZeta commutes with star for all s.
    Follows from riemannZeta_star_of_one_lt_re (Re(s) > 1) by analytic continuation:
    both sides are analytic on ℂ \ {1} and agree on {Re(s) > 1}, which accumulates to 2 ∈ ℂ \ {1}.
    Since ℂ \ {1} is connected, they agree everywhere. -/
theorem riemannZeta_star (s : ℂ) :
    riemannZeta (star s) = star (riemannZeta s) :=
  riemannZeta_conj s

/-!
# Conjugation identity for classicalXi

Combines riemannZeta_star with the functional equation to give the
full conjugation identity needed for the symmetry package.
-/

theorem classicalXi_conj (s : ℂ) :
    classicalXi (star s) = star (classicalXi s) := by
  have h : classicalXiPrefactor (star s) = star (classicalXiPrefactor s) := by
    unfold classicalXiPrefactor
    have h1 : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num [star_def]
    have h2 : star (s - 1) = star s - 1 := by simp [star_sub, star_one]
    have h3 : star ((Real.pi : ℂ) ^ (-(s / 2))) = (Real.pi : ℂ) ^ (-(star s / 2)) := by
      rw [real_pos_cpow_star Real.pi (by norm_num [Real.pi_pos])]
      congr 1; simp [star_neg, star_div]
    have h4 : star (Complex.Gamma (s / 2)) = Complex.Gamma (star s / 2) := by
      show (starRingEnd ℂ) (Complex.Gamma (s / 2)) = Complex.Gamma ((starRingEnd ℂ) s / 2)
      rw [(Complex.Gamma_conj (s / 2)).symm]
      congr 1
      change star (s / 2 : ℂ) = star s / 2
      simp [div_eq_mul_inv, star_mul', star_inv₀, show (star 2 : ℂ) = (2 : ℂ) from by norm_num [star_def]]
    rw [show star ((1 / 2 : ℂ) * s * (s - 1) * ((Real.pi : ℂ) ^ (-(s / 2))) * Complex.Gamma (s / 2)) =
      star (1 / 2 : ℂ) * star s * star (s - 1) * star ((Real.pi : ℂ) ^ (-(s / 2))) * star (Complex.Gamma (s / 2)) from
      by simp [star_mul']]
    rw [h1, h2, h3, h4]
  unfold classicalXi XiFromPrefactor
  rw [show zeta = riemannZeta from rfl, h, riemannZeta_star]
  exact (star_mul' (classicalXiPrefactor s) (riemannZeta s)).symm

theorem conjugationIdentity_classicalXi :
    ConjugationIdentityCertificate where
  identity z hgt hlt := by
    show classicalXi ((1 / 2 : ℂ) + I * star z) = star (classicalXi ((1 / 2 : ℂ) + I * z))
    have hfe := classicalXi_functional_equation ((1 / 2 : ℂ) + I * z)
      (by simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]; ring; linarith)
      (by simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]; ring; linarith)
    have hc := classicalXi_conj ((1 / 2 : ℂ) + I * star z)
    have hstar : star ((1 / 2 : ℂ) + I * star z) = (1 / 2 : ℂ) - I * z := by
      simp [star_def]; ring
    rw [hstar] at hc
    have hflip : classicalXi ((1 / 2 : ℂ) + I * star z) = star (star (classicalXi ((1 / 2 : ℂ) + I * star z))) := by
      rw [star_star]
    rw [hflip, ← hc, ← hfe]
    congr 1
    ring

/-- The full symmetry package for classical xi, derived from the functional equation
    and conjugation identity. -/
def classicalSymmetryPackage : SymmetryCertificate where
  functional_eq := { fe := classicalXi_functional_equation }
  conjugation_identity := conjugationIdentity_classicalXi

theorem classicalXi_symmetry : XiShiftedSymmetryPackage :=
  xiShiftedSymmetryPackage_of_certificates classicalSymmetryPackage

/-!
# Algebraic identity: classicalXi in terms of completedRiemannZeta₀ (simplified)

classicalXi s = (1/2)*s*(s-1)*completedRiemannZeta₀ s + 1/2

Follows from the existing classicalXi_eq_completed by expanding and cancelling.
-/

theorem classicalXi_eq_completed_add_half
    (s : ℂ) (hs : s ≠ 0) (hs1 : s ≠ 1)
    (hΓ : Complex.Gamma (s / 2) ≠ 0) :
    classicalXi s =
      (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + (1 / 2 : ℂ) := by
  have h := classicalXi_eq_completed s hs hΓ
  rw [h]
  have h1s : (1 : ℂ) - s ≠ 0 := fun h1 => hs1 (sub_eq_zero.mp h1 |>.symm)
  field_simp [h1s]
  ring

theorem xiShifted_eq_completed (z : ℂ) (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ)) :
    xiShifted z = (1 / 2 : ℂ) -
      (z ^ 2 + (1 / 4 : ℂ)) / 2 *
        completedRiemannZeta₀ ((1 / 2 : ℂ) + I * z) := by
  simp only [xiShifted]
  have hs : (1 / 2 : ℂ) + I * z ≠ 0 := by
    intro h
    have hre := congr_arg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im] at hre
    norm_num at hre
    linarith
  have hs1 : (1 / 2 : ℂ) + I * z ≠ 1 := by
    intro h
    have hre := congr_arg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im] at hre
    norm_num at hre
    linarith
  have hs_re : 0 < ((1 / 2 : ℂ) + I * z).re := by
    rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    norm_num
    linarith
  have hs_re1 : ((1 / 2 : ℂ) + I * z).re < 1 := by
    rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    norm_num
    linarith
  have hΓ := classical_gamma_nonzero_instrip _ hs_re hs_re1
  rw [classicalXi_eq_completed_add_half _ hs hs1 hΓ]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- xiShifted is continuous on the open strip {z | -1/2 < z.im < 1/2}.
    Follows from `xiShifted_eq_completed` expressing xiShifted as a polynomial
    in z times `completedRiemannZeta₀(1/2 + Iz)`, plus the fact that
    `completedRiemannZeta₀` is differentiable (hence continuous). -/
theorem xiShifted_continuousOn :
    ContinuousOn (fun z : ℂ => xiShifted z)
      {z : ℂ | -(1 / 2 : ℝ) < z.im ∧ z.im < (1 / 2 : ℝ)} :=
  have hagreement : Set.EqOn (fun z : ℂ => xiShifted z)
      (fun z : ℂ => (1 / 2 : ℂ) -
        (z ^ 2 + (1 / 4 : ℂ)) / 2 *
          completedRiemannZeta₀ ((1 / 2 : ℂ) + I * z))
      {z : ℂ | -(1 / 2 : ℝ) < z.im ∧ z.im < (1 / 2 : ℝ)} :=
    fun z hz => xiShifted_eq_completed z hz.1 hz.2
  ContinuousOn.congr
    (ContinuousOn.sub continuousOn_const
      (ContinuousOn.mul
        (ContinuousOn.div
          (ContinuousOn.add (continuousOn_pow 2) continuousOn_const)
          continuousOn_const
          (fun z _ => by norm_num))
        (differentiable_completedZeta₀.continuous.continuousOn.comp
          (ContinuousOn.add continuousOn_const
            (ContinuousOn.mul continuousOn_const continuousOn_id))
          (fun z _ => Set.mem_range_self _))))
    hagreement

/-- The completed Riemann zeta₀ function decays to 0 along horizontal lines
    in the critical strip: completedRiemannZeta₀(σ + it) → 0 as t → ∞ for any fixed σ.

    Proof: By definition, completedRiemannZeta₀(s) = mellin f_modif (s/2) / 2
    where f_modif = (hurwitzEvenFEPair 0).f_modif. By `mellin_eq_fourier`,
    this equals 𝓕(g)(Im(s)/(4π)) / 2 where
    g(u) = exp(-Re(s)·u/2) · f_modif(exp(-u)).
    By `Real.zero_at_infty_fourier` (Riemann-Lebesgue lemma), 𝓕(g)(ξ) → 0
    as |ξ| → ∞, since g is integrable (f_modif has exponential decay from
    `isBigO_atTop_evenKernel_sub`). Hence the Mellin transform → 0. -/
theorem completedRiemannZeta₀_vanishes_at_top_im :
    Filter.Tendsto (fun t : ℝ => completedRiemannZeta₀ ((1 / 2 : ℂ) + I * t))
      Filter.atTop (nhds (0 : ℂ)) := by
  let g : ℝ → ℂ := fun u =>
    Real.exp (-(1 / 4 : ℝ) * u) • (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (-u))
  have hform : ∀ t : ℝ, completedRiemannZeta₀ ((1 / 2 : ℂ) + I * t) =
      FourierTransform.fourier g (t / (4 * Real.pi)) / 2 := by
    intro t
    simp only [completedRiemannZeta₀, HurwitzZeta.completedHurwitzZetaEven₀, WeakFEPair.Λ₀, g]
    rw [mellin_eq_fourier]
    unfold Complex.smul
    push_cast
    ring
  have hfourier : Filter.Tendsto (FourierTransform.fourier g) Filter.atTop (nhds (0 : ℂ)) := by
    have hcocompact_atTop : Filter.atTop ≤ Filter.cocompact ℝ := by
      rw [cocompact_eq_atBot_atTop (α := ℝ)]
      exact Filter.le_sup_right
    exact Filter.Tendsto.mono_left (Real.zero_at_infty_fourier g) hcocompact_atTop
  have hfreq : Filter.Tendsto (fun t : ℝ => t / (4 * Real.pi)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const (by positivity : 0 < (4 : ℝ) * Real.pi) Filter.tendsto_id
  simp only [hform]
  exact (hfourier.comp hfreq).div tendsto_const_nhds two_ne_zero |>.cast (by simp)

/-!
# Open analytic targets for the first-quadrant certificate

To complete the Riemann Hypothesis via the decomposed first-quadrant
certificate (`rh_from_decomposed_first_quadrant_certificate`), two
analytic ingredients remain:

1. **Finite-rectangle nonvanishing** (`xiShifted_no_zero_in_rect`):
   `xiShifted z ≠ 0` for all z with z.re ∈ [-1, 11] and z.im ∈ (-0.1, 0.6).
   On the critical line (z.im = 0), this follows from the known zero-free
   region of ζ: the first non-trivial zero has Im(s) ≈ 14.13 > 11.
   Off the critical line, the Riemann Hypothesis would give nonvanishing
   for z.im ∈ (-1/2, 1/2) \ {0}, but this is precisely what we are
   trying to prove.  A proof must use the functional equation (symmetry
   in z.im) together with a separate argument for |z.im| ≥ 1/2.

2. **Exponential tail lower bound** (`xiShifted_tail_lower_bound`):
   For z.re > 10, some positive lower bound on ‖xiShifted z‖ that
   decays at most exponentially.  From `xiShifted_eq_completed`,
     xiShifted z = 1/2 − (z²+1/4)/2 · Λ₀(1/2+Iz),
   so it suffices to show Λ₀(1/2+Iz) → 0 fast enough as Re(z) → ∞.
   By `mellin_eq_fourier` + Riemann-Lebesgue (`completedRiemannZeta₀_vanishes_at_top_im`),
   Λ₀(1/2+Iz) = 𝓕(g)(Re(z)/(4π))/2 → 0, but the quantitative rate
   (needed to match the exponential form) requires bounding the Fourier
   transform of the kernel g(u) = exp(−u/4) · f_modif(exp(−u)).
-/

-- The certificate skeleton is ready; the remaining work is analytic.
-- See `rh_from_decomposed_first_quadrant_certificate` for how these
-- two ingredients yield RiemannHypothesisProp.


/-!
# Remaining proof skeleton

The symmetry package is already available:

    classicalXi_symmetry : XiShiftedSymmetryPackage

The assembly theorem is already available:

    rh_from_first_quadrant_distance_proof

So the remaining work is:

1. Prove first-quadrant nonvanishing:

    0 ≤ Re z ≤ X, 0 < Im z < 1/2 → xiShifted z ≠ 0.

2. Prove a right-tail lower bound that may degenerate as Im z → 0:

    X < Re z, -1/2 < Im z < 1/2, Im z ≠ 0 →
    lower(Re z, Im z) ≤ ‖xiShifted z‖,

    with lower(r, y) > 0 for y ≠ 0.

The skeleton below makes those obligations explicit.
-/

/-!
## 1. Safe conditional skeleton, no sorry
-/

/-- First-quadrant nonvanishing obligation. -/
structure RemainingQuadrantNonvanishing (X : ℝ) where
  no_zero :
    ∀ z : ℂ,
      0 ≤ z.re →
      z.re ≤ X →
      0 < z.im →
      z.im < (1 : ℝ) / 2 →
      xiShifted z ≠ 0

/-- A finite rectangular plan for proving first-quadrant nonvanishing. -/
structure QuadrantZeroFreePlan (X : ℝ) where
  rects : List XiLocalZeroFreeRect
  covers :
    ∀ z : ℂ,
      0 ≤ z.re →
      z.re ≤ X →
      0 < z.im →
      z.im < (1 : ℝ) / 2 →
      ∃ R ∈ rects,
        R.x0 < z.re ∧
        z.re < R.x1 ∧
        R.y0 < z.im ∧
        z.im < R.y1

/-- A finite zero-free rectangular plan gives first-quadrant nonvanishing. -/
def quadrant_nonvanishing_from_plan
    {X : ℝ}
    (P : QuadrantZeroFreePlan X) :
    RemainingQuadrantNonvanishing X where
  no_zero := by
    intro z hx0 hx1 hy0 hy1 hz
    rcases P.covers z hx0 hx1 hy0 hy1 with
      ⟨R, _, hx0', hx1', hy0', hy1'⟩
    exact R.no_zero z hx0' hx1' hy0' hy1' hz

/-- Algebraic lower bound for `xiShifted` from an upper bound on
    `completedRiemannZeta₀`.

From

    xiShifted z =
      1/2 - (z^2 + 1/4)/2 * completedRiemannZeta₀(1/2 + i z)

and

    ‖completedRiemannZeta₀(1/2 + i z)‖ ≤ U,

we get

    ‖xiShifted z‖ ≥
      1/2 - (‖z^2 + 1/4‖ / 2) * U.
-/
theorem xiShifted_lower_bound_of_completed_upper_bound
    (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im)
    (hlt : z.im < (1 / 2 : ℝ))
    (U : ℝ)
    (hU : 0 ≤ U)
    (hbound :
      ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + I * z)‖ ≤ U) :
    (1 / 2 : ℝ) -
      (‖z ^ 2 + (1 / 4 : ℂ)‖ / 2) * U ≤
    ‖xiShifted z‖ := by
  rw [xiShifted_eq_completed z hgt hlt]

  have hsub :=
    norm_sub_norm_le
      (1 / 2 : ℂ)
      ((z ^ 2 + (1 / 4 : ℂ)) / 2 *
        completedRiemannZeta₀ ((1 / 2 : ℂ) + I * z))

  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by simp
  rw [hhalf] at hsub

  have hprod :
      ‖(z ^ 2 + (1 / 4 : ℂ)) / 2 *
          completedRiemannZeta₀ ((1 / 2 : ℂ) + I * z)‖ ≤
        (‖z ^ 2 + (1 / 4 : ℂ)‖ / 2) * U := by
    calc
      _ = ‖(z ^ 2 + (1 / 4 : ℂ)) / 2‖ *
            ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + I * z)‖ := by
        rw [norm_mul]
      _ = (‖z ^ 2 + (1 / 4 : ℂ)‖ / ‖(2 : ℂ)‖) *
            ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + I * z)‖ := by
        rw [norm_div]
      _ = (‖z ^ 2 + (1 / 4 : ℂ)‖ / 2) *
            ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + I * z)‖ := by
        simp
      _ ≤ (‖z ^ 2 + (1 / 4 : ℂ)‖ / 2) * U := by
        exact mul_le_mul_of_nonneg_left hbound (by positivity)

  linarith

/-- A quantitative upper bound for `completedRiemannZeta₀` in the right tail,
    together with a positivity margin, yields a distance-sensitive lower bound
    for `xiShifted`. -/
structure CompletedZetaUpperBoundTail (X : ℝ) where
  U : ℝ → ℝ → ℝ
  U_nonneg :
    ∀ r y : ℝ,
      X ≤ r →
      y ≠ 0 →
      0 ≤ U r y
  bound :
    ∀ z : ℂ,
      X < z.re →
      -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) →
      z.im ≠ 0 →
      ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + I * z)‖ ≤ U z.re z.im
  margin_pos :
    ∀ r y : ℝ,
      X ≤ r →
      y ≠ 0 →
      0 <
        (1 / 2 : ℝ) -
          (‖((r : ℂ) + I * (y : ℂ)) ^ 2 + (1 / 4 : ℂ)‖ / 2) *
            U r y

/-- Convert a completed-zeta upper-bound tail estimate into a distance-sensitive
    lower-bound tail certificate for `xiShifted`. -/
def distanceLowerBound_from_completed_upper_bound
    {X : ℝ}
    (B : CompletedZetaUpperBoundTail X) :
    XiRightTailDistanceLowerBoundForX X where
  lower r y :=
    (1 / 2 : ℝ) -
      (‖((r : ℂ) + I * (y : ℂ)) ^ 2 + (1 / 4 : ℂ)‖ / 2) *
        B.U r y
  lower_pos r y hr hy :=
    B.margin_pos r y hr hy
  bound z hre hgt hlt hne := by
    have h :=
      xiShifted_lower_bound_of_completed_upper_bound
        z (by linarith) (by linarith)
        (B.U z.re z.im)
        (B.U_nonneg z.re z.im (le_of_lt hre) hne)
        (B.bound z hre (by linarith) (by linarith) hne)
    unfold lower at *
    simp only [Complex.re_add_im] at *
    exact h

/-- The remaining RH proof obligation at cutoff X. -/
structure RemainingRHProof (X : ℝ) where
  quadrant : RemainingQuadrantNonvanishing X
  tail : XiRightTailDistanceLowerBoundForX X

/-- Assemble the remaining work into RH. -/
theorem rh_from_remaining_rh_proof
    {X : ℝ}
    (W : RemainingRHProof X) :
    RiemannHypothesisProp :=
  rh_from_first_quadrant_distance_proof
    {
      X := X
      symmetries := classicalXi_symmetry
      quadrant_no_zero := W.quadrant.no_zero
      right_tail := W.tail
    }

/-- Assemble directly from quadrant nonvanishing and a completed-zeta upper-bound
    tail estimate. -/
theorem rh_from_quadrant_and_completed_upper_bound
    {X : ℝ}
    (Q : RemainingQuadrantNonvanishing X)
    (B : CompletedZetaUpperBoundTail X) :
    RiemannHypothesisProp :=
  rh_from_remaining_rh_proof
    {
      quadrant := Q
      tail := distanceLowerBound_from_completed_upper_bound B
    }

/-!
## 2. Development skeleton with explicit `sorry` placeholders

The following is a planning skeleton. The `sorry`s are the open analytic work.
Do not treat this as a proof of RH.

The main version is the `v2` development below, which uses
`CompletedZetaRectUpperBoundCertificate` and has margin positivity proved.
The remaining sorrys are:

1. `quadrantPlan_10_skeleton` rectangle nonvanishing (open analytics)
2. `completedZetaUpperBoundTail_10_v2.bound` (quantitative Fourier decay)
-/


    /-!
# Partial completion of the remaining proof skeleton

This section completes the purely algebraic and bookkeeping parts of the
remaining skeleton.

The two genuinely analytic `sorry`s that remain are:

1. `quadrantPlan_10_skeleton`:
   nonvanishing of `xiShifted` on a rectangle covering
   `[0,10] × (0,1/2)`.

2. `completedZetaUpperBoundTail_10_v2.bound`:
   a quantitative upper bound for
   `completedRiemannZeta₀ (1/2 + I*z)` in the right tail.
-/

/-!
## Tail helper functions

We choose a tail upper-bound shape `tailU` whose positivity margin can be
proved algebraically. The actual proof that `completedRiemannZeta₀` is bounded
by `tailU` remains open.
-/

/-- The quadratic factor appearing in the shifted xi identity. -/
noncomputable def tailD (r y : ℝ) : ℂ :=
  ((r : ℂ) + I * (y : ℂ)) ^ 2 + (1 / 4 : ℂ)

/-- A candidate tail upper-bound shape.

The definition is deliberately small enough that the positivity margin

    1/2 - (‖tailD r y‖ / 2) * tailU r y

is provably positive.
-/
noncomputable def tailU (r y : ℝ) : ℝ :=
  if ‖tailD r y‖ = 0 then 0
  else min (Real.exp (-r)) (1 / (4 * ‖tailD r y‖))

/-- `tailU` is nonnegative. -/
theorem tailU_nonneg (r y : ℝ) :
    0 ≤ tailU r y := by
  by_cases hD : ‖tailD r y‖ = 0
  · simp [tailU, hD]
  · simp [tailU, hD]
    positivity

/-- The positivity margin associated to `tailU` is strictly positive. -/
theorem tail_margin_pos (r y : ℝ) :
    0 <
      (1 / 2 : ℝ) -
        (‖tailD r y‖ / 2) * tailU r y := by
  by_cases hD : ‖tailD r y‖ = 0
  · simp [tailU, hD]
  · have hU : tailU r y ≤ 1 / (4 * ‖tailD r y‖) := by
      simp only [tailU, hD, ite_false]
      exact min_le_right _ _
    have hprod :
        (‖tailD r y‖ / 2) * tailU r y ≤ 1 / 8 := by
      calc
        _ ≤ (‖tailD r y‖ / 2) * (1 / (4 * ‖tailD r y‖)) := by
          exact mul_le_mul_of_nonneg_left hU (by positivity)
        _ = 1 / 8 := by
          field_simp [hD]
          ring
    linarith

/-- In the actual tail strip, `tailD r y` is nonzero. -/
theorem tailD_ne_zero_of_strip
    (r y : ℝ)
    (hr : 10 ≤ r)
    (hgt : -(1 / 2 : ℝ) < y)
    (hlt : y < (1 / 2 : ℝ)) :
    tailD r y ≠ 0 := by
  intro h
  have hre := congr_arg Complex.re h
  have him := congr_arg Complex.im h
  simp only [tailD, pow_two, Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at hre
  simp only [tailD, pow_two, Complex.add_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at him
  ring_nf at hre him
  have hy2 : y * y < 1 / 4 := by nlinarith
  have hr2 : (100 : ℝ) ≤ r * r := by nlinarith
  nlinarith

/-- In the tail strip, `tailU r y` is strictly positive. -/
theorem tailU_pos_of_strip
    (r y : ℝ)
    (hr : 10 ≤ r)
    (hgt : -(1 / 2 : ℝ) < y)
    (hlt : y < (1 / 2 : ℝ)) :
    0 < tailU r y := by
  have hD : tailD r y ≠ 0 := tailD_ne_zero_of_strip r y hr hgt hlt
  have hnorm : ‖tailD r y‖ ≠ 0 := by
    simpa [norm_eq_zero] using hD
  simp only [tailU, hnorm, ite_false]
  constructor
  · positivity
  · positivity

/-!
## Completed-zeta upper-bound tail skeleton, with margin completed
-/

/-- A completed-zeta upper-bound tail estimate at X = 10.

The margin positivity is proved. The actual upper bound for
`completedRiemannZeta₀` remains open.
-/
def completedZetaUpperBoundTail_10_v2 :
    CompletedZetaUpperBoundTail (10 : ℝ) where
  U := tailU
  U_nonneg := by
    intro r y _ _
    exact tailU_nonneg r y
  bound := by
    intro z hre hgt hlt hne
    -- OPEN ANALYTIC WORK:
    --
    -- Prove:
    --
    --   ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + I * z)‖
    --     ≤ tailU z.re z.im
    --
    -- for 10 < Re z, -1/2 < Im z < 1/2, Im z ≠ 0.
    --
    -- The qualitative decay `completedRiemannZeta₀_vanishes_at_top_im`
    -- is already available, but a quantitative uniform version is needed.
    sorry
  margin_pos := by
    intro r y _ _
    exact tail_margin_pos r y

/-!
## First-quadrant rectangular plan skeleton

The covering bookkeeping is completed. The rectangle nonvanishing proof is
still open.
-/

/-- A rectangular plan covering `[0,10] × (0,1/2)`.

The rectangle is chosen slightly larger than necessary:

    -1 < Re z < 11,
     0 < Im z < 1/2.

The covering proof is complete. The nonvanishing proof is open.
-/
def quadrantPlan_10_skeleton :
    QuadrantZeroFreePlan (10 : ℝ) where
  rects :=
    [
      {
        x0 := -1
        x1 := 11
        y0 := 0
        y1 := (1 : ℝ) / 2
        x_lt := by norm_num
        y_lt := by norm_num
        no_zero := by
          intro z hx0 hx1 hy0 hy1
          -- OPEN ANALYTIC WORK:
          --
          -- Prove:
          --
          --   xiShifted z ≠ 0
          --
          -- for
          --
          --   -1 < Re z < 11,
          --    0 < Im z < 1/2.
          --
          -- This is the finite-region nonvanishing obligation.
          sorry
      }
    ]
  covers := by
    intro z hx0 hx1 hy0 hy1
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    exact ⟨by linarith, by linarith, hy0, hy1⟩

/-- First-quadrant nonvanishing obtained from the rectangular plan.

This still depends on the open rectangle nonvanishing proof above.
-/
def remainingQuadrant_10_v2 :
    RemainingQuadrantNonvanishing (10 : ℝ) :=
  quadrant_nonvanishing_from_plan quadrantPlan_10_skeleton

/-!
## Final skeleton theorem

This theorem assembles the remaining work.

It currently depends on exactly two open analytic `sorry`s:

1. rectangle nonvanishing in `quadrantPlan_10_skeleton`;
2. quantitative tail bound in `completedZetaUpperBoundTail_10_v2`.
-/
theorem rh_proof_skeleton_v2 :
    RiemannHypothesisProp :=
  rh_from_quadrant_and_completed_upper_bound
    remainingQuadrant_10_v2
    completedZetaUpperBoundTail_10_v2

/-!
# Further completion: right-half zero-free route

The statement

    XiNoRightHalfZerosFull

says:

    classicalXi s ≠ 0 whenever 1/2 < Re(s) < 1.

This is equivalent to Step4Obligation, and therefore implies RH using the
functional equation and Gamma-nonzero equivalence.
-/

/-- `XiNoRightHalfZerosFull` is equivalent to the implication form of
    `XiNoRightHalfZeros classicalXi`. -/
theorem xiNoRightHalfZeros_iff_full :
    XiNoRightHalfZeros classicalXi ↔ XiNoRightHalfZerosFull := by
  constructor
  · intro H s hgt hlt hz
    exact H s hz hgt hlt
  · intro H s hz hgt hlt
    exact H s hgt hlt hz

/-- A full right-half zero-free statement implies RH. -/
theorem rh_from_xiNoRightHalfZerosFull
    (H : XiNoRightHalfZerosFull) :
    RiemannHypothesisProp := by
  have hStep : Step4Obligation :=
    xiNoRightHalfZeros_iff_full.mpr H
  have hCrit : XiCriticalLineZeros classicalXi :=
    (step4_iff_xi_critical_line classicalXi_functional_equation).mp hStep
  exact
    (rh_iff_xi_critical_from_gamma classical_gamma_nonzero_instrip).mpr hCrit

/-- A full right-half zero-free statement implies first-quadrant
    nonvanishing for `xiShifted`. -/
theorem quadrant_no_zero_from_xiNoRightHalfZerosFull
    (H : XiNoRightHalfZerosFull)
    (X : ℝ) :
    RemainingQuadrantNonvanishing X where
  no_zero := by
    intro z hx0 hx1 hy0 hy1 hz
    let s := (1 / 2 : ℂ) + I * z
    have hs_zero : classicalXi s = 0 := by
      simpa [xiShifted, s] using hz
    have hs_re_pos : 0 < s.re := by
      simp [s]
      linarith
    have hs_re_lt_one : s.re < 1 := by
      simp [s]
      linarith
    let t := 1 - s
    have ht_zero : classicalXi t = 0 := by
      have hfe := classicalXi_functional_equation s hs_re_pos hs_re_lt_one
      rw [hfe] at hs_zero
      exact hs_zero
    have ht_gt_half : (1 : ℝ) / 2 < t.re := by
      simp [t, s]
      linarith
    have ht_lt_one : t.re < 1 := by
      simp [t, s]
      linarith
    exact H t ht_gt_half ht_lt_one ht_zero

/-- A packaged right-half decomposition proof.

This uses the three-part decomposition:

1. classical zero-free region;
2. thin residual region;
3. bounded imaginary cover.
-/
structure RightHalfDecompositionProof where
  classical_region : ClassicalZeroFreeRegion
  thin : ThinRegionNonVanishing classical_region.C classical_region.T₀
  bounded : FiniteBoundedRectCover classical_region.T₀

/-- A right-half decomposition proof implies RH. -/
theorem rh_from_right_half_decomposition_proof
    (P : RightHalfDecompositionProof) :
    RiemannHypothesisProp :=
  rh_from_xiNoRightHalfZerosFull
    (xiNoRightHalfZerosFull_from_all_three
      P.classical_region
      P.thin
      P.bounded)

/-- A right-half decomposition proof also gives a first-quadrant
    nonvanishing certificate at any cutoff X. -/
def remainingQuadrant_from_right_half_decomposition_proof
    (P : RightHalfDecompositionProof)
    (X : ℝ) :
    RemainingQuadrantNonvanishing X :=
  quadrant_no_zero_from_xiNoRightHalfZerosFull
    (xiNoRightHalfZerosFull_from_all_three
      P.classical_region
      P.thin
      P.bounded)
    X

/-!
## Trivial bounded cover for T₀ = 0

If T₀ = 0, then the condition |Im(s)| < T₀ is impossible, so the bounded
cover obligation is vacuous.
-/

/-- The bounded-imaginary cover is vacuous when `T₀ = 0`. -/
def finiteBoundedRectCover_zero :
    FiniteBoundedRectCover 0 where
  covers := by
    intro s _ _ him
    have habs : 0 ≤ |s.im| := abs_nonneg s.im
    linarith

/-!
## Alternative right-half skeleton

This skeleton completes the bounded cover part by taking T₀ = 0. The remaining
open obligations are:

1. classical zero-free region;
2. thin-region nonvanishing.

Together these are still equivalent to the full right-half zero-free statement,
so they remain RH-hard.
-/

/-- A right-half decomposition skeleton with the bounded part completed
    vacuously. -/
def rightHalfDecompositionProof_skeleton :
    RightHalfDecompositionProof where
  classical_region :=
    {
      C := 1
      T₀ := 0
      C_pos := by norm_num
      zero_free := by
        intro s hbound hslt him
        -- OPEN ANALYTIC WORK:
        --
        -- Prove a classical zero-free region:
        --
        --   classicalXi s ≠ 0
        --
        -- when
        --
        --   1 - 1 / log(|Im(s)| + 2) ≤ Re(s) < 1.
        sorry
    }
  thin := by
    intro s hgt hlt him
    -- OPEN ANALYTIC WORK:
    --
    -- Prove thin-region nonvanishing:
    --
    --   classicalXi s ≠ 0
    --
    -- when
    --
    --   1/2 < Re(s) < 1 - 1 / log(|Im(s)| + 2),
    --   0 ≤ |Im(s)|.
    sorry
  bounded := finiteBoundedRectCover_zero

/-- RH from the right-half decomposition skeleton.

This theorem depends on the two open analytic `sorry`s inside
`rightHalfDecompositionProof_skeleton`.
-/
theorem rh_proof_skeleton_via_right_half :
    RiemannHypothesisProp :=
  rh_from_right_half_decomposition_proof
    rightHalfDecompositionProof_skeleton

/-!
# Completed-zeta rectangular upper-bound certificates

The identity

    xiShifted z =
      1/2 - (z^2 + 1/4)/2 * completedRiemannZeta₀(1/2 + i z)

shows that an upper bound

    ‖completedRiemannZeta₀(1/2 + i z)‖ ≤ U

gives a lower bound

    ‖xiShifted z‖ ≥ 1/2 - (‖z^2 + 1/4‖ / 2) * U.

If we also have a rectangle-bound

    ‖z^2 + 1/4‖ / 2 ≤ D_half

and a positivity margin

    0 < 1/2 - D_half * U,

then we obtain a positive lower bound for `xiShifted` on that rectangle.
-/

/-- A rectangular certificate giving an upper bound for
    `completedRiemannZeta₀` and a resulting positive lower bound for
    `xiShifted`. -/
structure CompletedZetaRectUpperBoundCertificate where
  x0 : ℝ
  x1 : ℝ
  y0 : ℝ
  y1 : ℝ
  x_lt : x0 < x1
  y_lt : y0 < y1
  y_lower : -(1 / 2 : ℝ) ≤ y0
  y_upper : y1 ≤ (1 / 2 : ℝ)
  U : ℝ
  U_nonneg : 0 ≤ U
  D_half : ℝ
  D_half_nonneg : 0 ≤ D_half
  D_half_spec :
    ∀ z : ℂ,
      x0 < z.re →
      z.re < x1 →
      y0 < z.im →
      z.im < y1 →
      ‖z ^ 2 + (1 / 4 : ℂ)‖ / 2 ≤ D_half
  bound :
    ∀ z : ℂ,
      x0 < z.re →
      z.re < x1 →
      y0 < z.im →
      z.im < y1 →
      ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + I * z)‖ ≤ U
  margin_pos :
    0 < (1 / 2 : ℝ) - D_half * U

/-- Convert a completed-zeta rectangular upper-bound certificate into a
    lower-bound rectangle for `xiShifted`. -/
def xiLocalLowerBoundRect_from_completedZetaRectUpperBound
    (C : CompletedZetaRectUpperBoundCertificate) :
    XiLocalLowerBoundRect where
  x0 := C.x0
  x1 := C.x1
  y0 := C.y0
  y1 := C.y1
  x_lt := C.x_lt
  y_lt := C.y_lt
  ε := (1 / 2 : ℝ) - C.D_half * C.U
  ε_pos := C.margin_pos
  lower_bound := by
    intro z hx0 hx1 hy0 hy1
    have hgt : -(1 / 2 : ℝ) < z.im := by
      linarith [C.y_lower]
    have hlt : z.im < (1 / 2 : ℝ) := by
      linarith [C.y_upper]

    have hbase :=
      xiShifted_lower_bound_of_completed_upper_bound
        z hgt hlt C.U C.U_nonneg
        (C.bound z hx0 hx1 hy0 hy1)

    have hD := C.D_half_spec z hx0 hx1 hy0 hy1

    have hprod :
        (‖z ^ 2 + (1 / 4 : ℂ)‖ / 2) * C.U ≤
        C.D_half * C.U :=
      mul_le_mul_of_nonneg_right hD C.U_nonneg

    have hmargin :
        (1 / 2 : ℝ) - C.D_half * C.U ≤
        (1 / 2 : ℝ) -
          (‖z ^ 2 + (1 / 4 : ℂ)‖ / 2) * C.U :=
      sub_le_sub_left hprod (1 / 2)

    linarith

/-- A finite list of completed-zeta rectangular upper-bound certificates
    covering the first quadrant. -/
structure CompletedZetaRectangularPlan (X : ℝ) where
  certs : List CompletedZetaRectUpperBoundCertificate
  covers :
    ∀ z : ℂ,
      0 ≤ z.re →
      z.re ≤ X →
      0 < z.im →
      z.im < (1 / 2 : ℝ) →
      ∃ C ∈ certs,
        C.x0 < z.re ∧
        z.re < C.x1 ∧
        C.y0 < z.im ∧
        z.im < C.y1

/-- Convert a completed-zeta rectangular plan into a zero-free rectangular
    plan for `xiShifted`. -/
def quadrantPlan_from_completedZetaPlan
    {X : ℝ}
    (P : CompletedZetaRectangularPlan X) :
    QuadrantZeroFreePlan X where
  rects :=
    P.certs.map xiLocalLowerBoundRect_from_completedZetaRectUpperBound
  covers := by
    intro z hx0 hx1 hy0 hy1
    rcases P.covers z hx0 hx1 hy0 hy1 with
      ⟨C, hC, hx0', hx1', hy0', hy1'⟩
    refine ⟨_, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
    exact ⟨hx0', hx1', hy0', hy1'⟩

/-- A completed-zeta rectangular plan gives first-quadrant
    nonvanishing. -/
def remainingQuadrant_from_completedZetaPlan
    {X : ℝ}
    (P : CompletedZetaRectangularPlan X) :
    RemainingQuadrantNonvanishing X :=
  quadrant_nonvanishing_from_plan
    (quadrantPlan_from_completedZetaPlan P)

/-!
# Master completed-zeta RH skeleton

This combines:

1. a finite completed-zeta rectangular plan for the first quadrant;
2. a completed-zeta upper-bound tail estimate.

Together they imply RH by the already proved assembly theorems.
-/

/-- A master RH proof skeleton expressed entirely in terms of
    completed-zeta upper-bound estimates. -/
structure CompletedZetaRHProof (X : ℝ) where
  quadrant_plan : CompletedZetaRectangularPlan X
  tail_bound : CompletedZetaUpperBoundTail X

/-- Assemble a completed-zeta RH proof skeleton into RH. -/
theorem rh_from_completedZeta_rh_proof
    {X : ℝ}
    (P : CompletedZetaRHProof X) :
    RiemannHypothesisProp :=
  rh_from_quadrant_and_completed_upper_bound
    (remainingQuadrant_from_completedZetaPlan P.quadrant_plan)
    P.tail_bound

/-!
# Global completed-zeta upper-bound framework

Instead of proving rectangle and tail bounds separately, we can first prove a
global pointwise upper bound of the form

    ‖completedRiemannZeta₀(1/2 + i z)‖ ≤ B(Re z, Im z)

and then derive rectangle and tail certificates from it.
-/

/-- A global pointwise upper bound for `completedRiemannZeta₀` in the shifted
    strip. -/
structure CompletedZetaGlobalUpperBound where
  B : ℝ → ℝ → ℝ
  B_nonneg :
    ∀ x y : ℝ,
      -(1 / 2 : ℝ) < y →
      y < (1 / 2 : ℝ) →
      y ≠ 0 →
      0 ≤ B x y
  bound :
    ∀ z : ℂ,
      -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) →
      z.im ≠ 0 →
      ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + I * z)‖ ≤ B z.re z.im

/-- The tautological global upper bound:

    B(x,y) = ‖completedRiemannZeta₀(1/2 + i(x+iy))‖

for y ≠ 0.

This is not analytically useful by itself, but it is a canonical starting
point. The real work is to compare this `B` with a simpler explicit function
`U`.
-/
def completedZetaGlobalUpperBound_self :
    CompletedZetaGlobalUpperBound where
  B := fun x y =>
    if y = 0 then 0
    else ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + I * ((x : ℂ) + I * (y : ℂ)))‖
  B_nonneg := by
    intro x y hgt hlt hne
    simp [hne]
    positivity
  bound := by
    intro z hgt hlt hne
    simp [hne, Complex.re_add_im]
    exact le_rfl

/-!
## Rectangular certificates from a global bound
-/

/-- A rectangular certificate derived from a global upper bound `B`. -/
structure CompletedZetaRectFromGlobalCertificate
    (B : ℝ → ℝ → ℝ) where
  x0 : ℝ
  x1 : ℝ
  y0 : ℝ
  y1 : ℝ
  x_lt : x0 < x1
  y_lt : y0 < y1
  y_nonneg : 0 ≤ y0
  y_upper : y1 ≤ (1 / 2 : ℝ)
  U : ℝ
  U_nonneg : 0 ≤ U
  D_half : ℝ
  D_half_nonneg : 0 ≤ D_half
  D_half_spec :
    ∀ z : ℂ,
      x0 < z.re →
      z.re < x1 →
      y0 < z.im →
      z.im < y1 →
      ‖z ^ 2 + (1 / 4 : ℂ)‖ / 2 ≤ D_half
  B_le_U :
    ∀ z : ℂ,
      x0 < z.re →
      z.re < x1 →
      y0 < z.im →
      z.im < y1 →
      B z.re z.im ≤ U
  margin_pos :
    0 < (1 / 2 : ℝ) - D_half * U

/-- Convert a rectangle certificate relative to a global bound into the
    standalone rectangle certificate. -/
def completedZetaRectUpperBoundCertificate_from_global
    (G : CompletedZetaGlobalUpperBound)
    (C : CompletedZetaRectFromGlobalCertificate G.B) :
    CompletedZetaRectUpperBoundCertificate where
  x0 := C.x0
  x1 := C.x1
  y0 := C.y0
  y1 := C.y1
  x_lt := C.x_lt
  y_lt := C.y_lt
  y_lower := by linarith [C.y_nonneg]
  y_upper := C.y_upper
  U := C.U
  U_nonneg := C.U_nonneg
  D_half := C.D_half
  D_half_nonneg := C.D_half_nonneg
  D_half_spec := C.D_half_spec
  bound := by
    intro z hx0 hx1 hy0 hy1
    have hy_pos : 0 < z.im := by linarith [C.y_nonneg]
    have hgt : -(1 / 2 : ℝ) < z.im := by linarith
    have hlt : z.im < (1 / 2 : ℝ) := by linarith [C.y_upper]
    have hne : z.im ≠ 0 := by linarith
    exact le_trans (G.bound z hgt hlt hne) (C.B_le_U z hx0 hx1 hy0 hy1)
  margin_pos := C.margin_pos

/-- A finite rectangular plan relative to a global bound. -/
structure CompletedZetaRectangularPlanFromGlobal
    (B : ℝ → ℝ → ℝ)
    (X : ℝ) where
  certs : List (CompletedZetaRectFromGlobalCertificate B)
  covers :
    ∀ z : ℂ,
      0 ≤ z.re →
      z.re ≤ X →
      0 < z.im →
      z.im < (1 / 2 : ℝ) →
      ∃ C ∈ certs,
        C.x0 < z.re ∧
        z.re < C.x1 ∧
        C.y0 < z.im ∧
        z.im < C.y1

/-- Convert a global-bound rectangular plan into the standalone rectangular
    plan. -/
def completedZetaRectangularPlan_from_global
    {X : ℝ}
    (G : CompletedZetaGlobalUpperBound)
    (P : CompletedZetaRectangularPlanFromGlobal G.B X) :
    CompletedZetaRectangularPlan X where
  certs :=
    P.certs.map (completedZetaRectUpperBoundCertificate_from_global G)
  covers := by
    intro z hx0 hx1 hy0 hy1
    rcases P.covers z hx0 hx1 hy0 hy1 with
      ⟨C, hC, hx0', hx1', hy0', hy1'⟩
    refine ⟨_, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
    exact ⟨hx0', hx1', hy0', hy1'⟩

/-!
## Tail certificates from a global bound
-/

/-- A tail certificate derived from a global upper bound `B`. -/
structure CompletedZetaTailFromGlobalCertificate
    (B : ℝ → ℝ → ℝ)
    (X : ℝ) where
  U : ℝ → ℝ → ℝ
  U_nonneg :
    ∀ r y : ℝ,
      X ≤ r →
      y ≠ 0 →
      0 ≤ U r y
  B_le_U :
    ∀ z : ℂ,
      X < z.re →
      -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) →
      z.im ≠ 0 →
      B z.re z.im ≤ U z.re z.im
  margin_pos :
    ∀ r y : ℝ,
      X ≤ r →
      y ≠ 0 →
      0 <
        (1 / 2 : ℝ) -
          (‖((r : ℂ) + I * (y : ℂ)) ^ 2 + (1 / 4 : ℂ)‖ / 2) *
            U r y

/-- Convert a global-bound tail certificate into the standalone tail
    certificate. -/
def completedZetaUpperBoundTail_from_global
    {X : ℝ}
    (G : CompletedZetaGlobalUpperBound)
    (T : CompletedZetaTailFromGlobalCertificate G.B X) :
    CompletedZetaUpperBoundTail X where
  U := T.U
  U_nonneg := T.U_nonneg
  bound := by
    intro z hre hgt hlt hne
    exact le_trans (G.bound z hgt hlt hne) (T.B_le_U z hre hgt hlt hne)
  margin_pos := T.margin_pos

/-!
# Master global-bound RH skeleton
-/

/-- A master RH proof skeleton based on one global upper bound `B`, a finite
    rectangular plan, and a tail estimate. -/
structure CompletedZetaGlobalRHProof (X : ℝ) where
  global : CompletedZetaGlobalUpperBound
  quadrant_plan : CompletedZetaRectangularPlanFromGlobal global.B X
  tail : CompletedZetaTailFromGlobalCertificate global.B X

/-- Assemble a global-bound RH proof skeleton into RH. -/
theorem rh_from_completedZeta_global_rh_proof
    {X : ℝ}
    (P : CompletedZetaGlobalRHProof X) :
    RiemannHypothesisProp :=
  rh_from_completedZeta_rh_proof
    {
      quadrant_plan :=
        completedZetaRectangularPlan_from_global
          P.global
          P.quadrant_plan
      tail_bound :=
        completedZetaUpperBoundTail_from_global
          P.global
          P.tail
    }
/-!
# Decomposition of completedRiemannZeta₀ into polar and xi parts

We use the identity

    completedRiemannZeta₀ s =
      1/s + 1/(1-s) + 2 * classicalXi s / (s * (s - 1))

in the critical strip.

In shifted coordinates s = 1/2 + i z, this becomes a decomposition of
completedRiemannZeta₀(1/2 + i z) into:

1. an explicit polar term;
2. a classical-xi term.

A global upper bound can then be obtained by bounding those two terms
separately.
-/

/-- The shifted critical-strip coordinate:

    s = 1/2 + i z.
-/
noncomputable def shiftedS (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) + I * z

theorem shiftedS_re (z : ℂ) :
    (shiftedS z).re = (1 / 2 : ℝ) - z.im := by
  simp [shiftedS]

theorem shiftedS_ne_zero
    (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im)
    (hlt : z.im < (1 / 2 : ℝ)) :
    shiftedS z ≠ 0 := by
  intro h
  have hre := congr_arg Complex.re h
  simp [shiftedS] at hre
  linarith

theorem shiftedS_ne_one
    (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im)
    (hlt : z.im < (1 / 2 : ℝ)) :
    shiftedS z ≠ 1 := by
  intro h
  have hre := congr_arg Complex.re h
  simp [shiftedS] at hre
  linarith

theorem shiftedS_in_critical_strip
    (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im)
    (hlt : z.im < (1 / 2 : ℝ)) :
    0 < (shiftedS z).re ∧ (shiftedS z).re < 1 := by
  constructor
  · simp [shiftedS]
    linarith
  · simp [shiftedS]
    linarith

theorem shiftedS_gamma_nonzero
    (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im)
    (hlt : z.im < (1 / 2 : ℝ)) :
    Complex.Gamma (shiftedS z / 2) ≠ 0 := by
  have hstrip := shiftedS_in_critical_strip z hgt hlt
  exact classical_gamma_nonzero_instrip (shiftedS z) hstrip.1 hstrip.2

/-- The polar/xi decomposition of `completedRiemannZeta₀` in shifted
    coordinates. -/
theorem completedZeta_decomp_polar_xi
    (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im)
    (hlt : z.im < (1 / 2 : ℝ))
    (hne : z.im ≠ 0) :
    completedRiemannZeta₀ (shiftedS z) =
      1 / shiftedS z +
      1 / (1 - shiftedS z) +
      2 * classicalXi (shiftedS z) /
        (shiftedS z * (shiftedS z - 1)) := by
  exact
    completedRiemannZeta₀_eq_polar_plus_xi
      (shiftedS z)
      (shiftedS_ne_zero z hgt hlt)
      (shiftedS_ne_one z hgt hlt)
      (shiftedS_gamma_nonzero z hgt hlt)

/-!
# Global upper bounds from sums
-/

/-- A global upper bound obtained by decomposing
    `completedRiemannZeta₀(1/2 + i z)` as `f z + g z`. -/
structure CompletedZetaSumBound where
  f : ℂ → ℂ
  g : ℂ → ℂ
  B1 : ℝ → ℝ → ℝ
  B2 : ℝ → ℝ → ℝ
  B1_nonneg :
    ∀ x y : ℝ,
      -(1 / 2 : ℝ) < y →
      y < (1 / 2 : ℝ) →
      y ≠ 0 →
      0 ≤ B1 x y
  B2_nonneg :
    ∀ x y : ℝ,
      -(1 / 2 : ℝ) < y →
      y < (1 / 2 : ℝ) →
      y ≠ 0 →
      0 ≤ B2 x y
  decomp :
    ∀ z : ℂ,
      -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) →
      z.im ≠ 0 →
      completedRiemannZeta₀ ((1 / 2 : ℂ) + I * z) = f z + g z
  bound1 :
    ∀ z : ℂ,
      -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) →
      z.im ≠ 0 →
      ‖f z‖ ≤ B1 z.re z.im
  bound2 :
    ∀ z : ℂ,
      -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) →
      z.im ≠ 0 →
      ‖g z‖ ≤ B2 z.re z.im

/-- Convert a sum decomposition with separate bounds into a global upper
    bound. -/
def completedZetaGlobalUpperBound_from_sum
    (S : CompletedZetaSumBound) :
    CompletedZetaGlobalUpperBound where
  B := fun x y => S.B1 x y + S.B2 x y
  B_nonneg := by
    intro x y hgt hlt hne
    positivity
  bound := by
    intro z hgt hlt hne
    rw [S.decomp z hgt hlt hne]
    exact
      le_trans
        (norm_add_le _ _)
        (add_le_add
          (S.bound1 z hgt hlt hne)
          (S.bound2 z hgt hlt hne))

/-!
# Polar/xi bound skeleton
-/

/-- Separate bounds for the polar part and the classical-xi part of
    `completedRiemannZeta₀`. -/
structure CompletedZetaPolarXiBound where
  Bpolar : ℝ → ℝ → ℝ
  Bxi : ℝ → ℝ → ℝ
  Bpolar_nonneg :
    ∀ x y : ℝ,
      -(1 / 2 : ℝ) < y →
      y < (1 / 2 : ℝ) →
      y ≠ 0 →
      0 ≤ Bpolar x y
  Bxi_nonneg :
    ∀ x y : ℝ,
      -(1 / 2 : ℝ) < y →
      y < (1 / 2 : ℝ) →
      y ≠ 0 →
      0 ≤ Bxi x y
  polar_bound :
    ∀ z : ℂ,
      -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) →
      z.im ≠ 0 →
      ‖1 / shiftedS z + 1 / (1 - shiftedS z)‖ ≤
        Bpolar z.re z.im
  xi_bound :
    ∀ z : ℂ,
      -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) →
      z.im ≠ 0 →
      ‖2 * classicalXi (shiftedS z) /
          (shiftedS z * (shiftedS z - 1))‖ ≤
        Bxi z.re z.im

/-- Build a sum-bound from separate polar and xi bounds. -/
def completedZetaSumBound_from_polar_xi
    (E : CompletedZetaPolarXiBound) :
    CompletedZetaSumBound where
  f := fun z =>
    1 / shiftedS z + 1 / (1 - shiftedS z)
  g := fun z =>
    2 * classicalXi (shiftedS z) /
      (shiftedS z * (shiftedS z - 1))
  B1 := E.Bpolar
  B2 := E.Bxi
  B1_nonneg := E.Bpolar_nonneg
  B2_nonneg := E.Bxi_nonneg
  decomp := by
    intro z hgt hlt hne
    exact completedZeta_decomp_polar_xi z hgt hlt hne
  bound1 := E.polar_bound
  bound2 := E.xi_bound

/-- Build a global upper bound from separate polar and xi bounds. -/
def completedZetaGlobalUpperBound_from_polar_xi
    (E : CompletedZetaPolarXiBound) :
    CompletedZetaGlobalUpperBound :=
  completedZetaGlobalUpperBound_from_sum
    (completedZetaSumBound_from_polar_xi E)

/-!
# Convenience: RH skeleton from polar/xi bounds

Given separate polar/xi bounds, plus a rectangular plan and tail estimate for
the resulting global bound, we obtain RH.
-/

/-- A master RH skeleton based on separate polar and xi bounds. -/
structure CompletedZetaPolarXiRHProof (X : ℝ) where
  estimate : CompletedZetaPolarXiBound
  quadrant_plan :
    CompletedZetaRectangularPlanFromGlobal
      (completedZetaGlobalUpperBound_from_polar_xi estimate).B
      X
  tail :
    CompletedZetaTailFromGlobalCertificate
      (completedZetaGlobalUpperBound_from_polar_xi estimate).B
      X

/-- Assemble a polar/xi RH skeleton into RH. -/
theorem rh_from_completedZeta_polar_xi_rh_proof
    {X : ℝ}
    (P : CompletedZetaPolarXiRHProof X) :
    RiemannHypothesisProp :=
  rh_from_completedZeta_global_rh_proof
    {
      global :=
        completedZetaGlobalUpperBound_from_polar_xi P.estimate
      quadrant_plan := P.quadrant_plan
      tail := P.tail
    }
/-!
# Explicit bound for the polar term

The polar term is

    1 / s + 1 / (1 - s)

where s = shiftedS z = 1/2 + i z.

Writing z = x + i y, we have:

    s = 1/2 - y + i x,
    1 - s = 1/2 + y - i x.

Since -1/2 < y < 1/2, both real parts are positive:

    Re(s) = 1/2 - y > 0,
    Re(1 - s) = 1/2 + y > 0.

Therefore:

    |s| ≥ 1/2 - y,
    |1 - s| ≥ 1/2 + y,

and hence:

    ‖1/s + 1/(1-s)‖ ≤ 1/(1/2 - y) + 1/(1/2 + y).
-/

/-- Explicit polar upper bound. -/
noncomputable def polarBound (x y : ℝ) : ℝ :=
  1 / (1 / 2 - y) + 1 / (1 / 2 + y)

theorem polarBound_nonneg
    (x y : ℝ)
    (hgt : -(1 / 2 : ℝ) < y)
    (hlt : y < (1 / 2 : ℝ)) :
    0 ≤ polarBound x y := by
  have h1 : 0 < (1 / 2 : ℝ) - y := by linarith
  have h2 : 0 < (1 / 2 : ℝ) + y := by linarith
  positivity

/-- Helper: the absolute value of the real part is bounded by the norm. -/
private theorem abs_re_le_norm (w : ℂ) :
    |w.re| ≤ ‖w‖ := by
  simpa [Complex.norm_eq_abs] using Complex.abs_re_le_abs w

/-- Explicit bound for the polar term. -/
theorem polar_bound_explicit
    (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im)
    (hlt : z.im < (1 / 2 : ℝ))
    (hne : z.im ≠ 0) :
    ‖1 / shiftedS z + 1 / (1 - shiftedS z)‖ ≤
      polarBound z.re z.im := by
  let hs := shiftedS z
  change ‖1 / hs + 1 / (1 - hs)‖ ≤ polarBound z.re z.im
  have hs0 : hs ≠ 0 := shiftedS_ne_zero z hgt hlt
  have h1s : 1 - hs ≠ 0 := by
    intro h; exact shiftedS_ne_one z hgt hlt (sub_eq_zero.mp h).symm
  have hd1 : 0 < (1 / 2 : ℝ) - z.im := by linarith
  have hd2 : 0 < (1 / 2 : ℝ) + z.im := by linarith
  have hre_hs : hs.re = (1 / 2 : ℝ) - z.im := by simp [hs, shiftedS]
  have hre_1hs : (1 - hs).re = (1 / 2 : ℝ) + z.im := by simp [hs, shiftedS]
  have hd1le : (1 / 2 : ℝ) - z.im ≤ ‖hs‖ := by
    have h := Complex.abs_re_le_abs hs
    simp only [Complex.norm_eq_abs, hre_hs, Real.abs_of_nonneg (le_of_lt hd1)] at h
    exact_mod_cast h
  have hd2le : (1 / 2 : ℝ) + z.im ≤ ‖1 - hs‖ := by
    have h := Complex.abs_re_le_abs (1 - hs)
    simp only [Complex.norm_eq_abs, hre_1hs, Real.abs_of_nonneg (le_of_lt hd2)] at h
    exact_mod_cast h
  have h1 : ‖1 / hs‖ ≤ 1 / ((1 / 2 : ℝ) - z.im) := by
    rw [norm_div, Complex.norm_one, one_div_le_one_div_iff (by positivity) (by positivity)]
    exact hd1le
  have h2 : ‖1 / (1 - hs)‖ ≤ 1 / ((1 / 2 : ℝ) + z.im) := by
    rw [norm_div, Complex.norm_one, one_div_le_one_div_iff (by positivity) (by positivity)]
    exact hd2le
  have hsum : ‖1 / hs + 1 / (1 - hs)‖ ≤ 1 / ((1 / 2 : ℝ) - z.im) + 1 / ((1 / 2 : ℝ) + z.im) :=
    le_trans (norm_add_le _ _) (add_le_add h1 h2)
  exact hsum

/-!
# Isolate the remaining xi-term bound
-/

/-- A bound for the classical-xi term appearing in the polar/xi
    decomposition. -/
structure XiTermBound where
  Bxi : ℝ → ℝ → ℝ
  Bxi_nonneg :
    ∀ x y : ℝ,
      -(1 / 2 : ℝ) < y →
      y < (1 / 2 : ℝ) →
      y ≠ 0 →
      0 ≤ Bxi x y
  xi_bound :
    ∀ z : ℂ,
      -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) →
      z.im ≠ 0 →
      ‖2 * classicalXi (shiftedS z) /
          (shiftedS z * (shiftedS z - 1))‖ ≤
        Bxi z.re z.im

/-- Build a full polar/xi bound from an explicit polar bound and a supplied
    xi-term bound. -/
def completedZetaPolarXiBound_from_xi_bound
    (T : XiTermBound) :
    CompletedZetaPolarXiBound where
  Bpolar := polarBound
  Bxi := T.Bxi
  Bpolar_nonneg := by
    intro x y hgt hlt _
    exact polarBound_nonneg x y hgt hlt
  Bxi_nonneg := T.Bxi_nonneg
  polar_bound := by
    intro z hgt hlt hne
    exact polar_bound_explicit z hgt hlt hne
  xi_bound := T.xi_bound

/-- The tautological xi-term bound.

This is not analytically useful by itself, but it is a canonical placeholder.
The real work is to replace `Bxi` with an explicit decaying or otherwise
controllable function.
-/
def xiTermBound_self : XiTermBound where
  Bxi := fun x y =>
    if y = 0 then 0
    else
      ‖2 * classicalXi (shiftedS ((x : ℂ) + I * (y : ℂ))) /
          (shiftedS ((x : ℂ) + I * (y : ℂ)) *
            (shiftedS ((x : ℂ) + I * (y : ℂ)) - 1))‖
  Bxi_nonneg := by
    intro x y hgt hlt hne
    simp [hne]
    positivity
  xi_bound := by
    intro z hgt hlt hne
    simp [hne, Complex.re_add_im]
    exact le_rfl

/-- A canonical polar/xi bound using the explicit polar bound and the
    tautological xi bound. -/
def completedZetaPolarXiBound_self :
    CompletedZetaPolarXiBound :=
  completedZetaPolarXiBound_from_xi_bound xiTermBound_self

/-!
# A fully proved geometric subproblem: bounding ‖z^2 + 1/4‖ on rectangles

For a rectangle

    x0 < Re z < x1,
    y0 < Im z < y1,

we prove a crude explicit bound

    ‖z^2 + 1/4‖ / 2 ≤ rectangleDHalf x0 x1 y0 y1.

This is not RH-hard; it is elementary complex geometry.
-/

/-- A crude explicit bound for `‖z^2 + 1/4‖ / 2` on a rectangle. -/
noncomputable def rectangleDHalf
    (x0 x1 y0 y1 : ℝ) : ℝ :=
  (((|x0| + |x1| + 1) + (|y0| + |y1| + 1)) ^ 2 + 1 / 4) / 2

/-- Elementary norm estimate:

    ‖z^2 + 1/4‖ / 2 ≤ ((R + S)^2 + 1/4) / 2

whenever `|Re z| ≤ R` and `|Im z| ≤ S`.
-/
theorem norm_z_sq_add_quarter_le
    (z : ℂ)
    (R S : ℝ)
    (hR : 0 ≤ R)
    (hS : 0 ≤ S)
    (hre : |z.re| ≤ R)
    (him : |z.im| ≤ S) :
    ‖z ^ 2 + (1 / 4 : ℂ)‖ / 2 ≤
      ((R + S) ^ 2 + 1 / 4) / 2 := by
  have hnorm : ‖z‖ ≤ R + S := by
    calc
      ‖z‖ = ‖(z.re : ℂ) + I * (z.im : ℂ)‖ := by
        rw [Complex.re_add_im]
      _ ≤ ‖(z.re : ℂ)‖ + ‖I * (z.im : ℂ)‖ :=
        norm_add_le _ _
      _ = |z.re| + |z.im| := by
        simp [norm_mul, Complex.norm_I]
      _ ≤ R + S :=
        add_le_add hre him

  have hsq : ‖z‖ ^ 2 ≤ (R + S) ^ 2 := by
    exact pow_le_pow_left (by positivity) hnorm 2

  calc
    ‖z ^ 2 + (1 / 4 : ℂ)‖ / 2 ≤
        (‖z ^ 2‖ + ‖(1 / 4 : ℂ)‖) / 2 := by
      exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ = (‖z‖ ^ 2 + 1 / 4) / 2 := by
      simp [norm_pow, Complex.norm_ofReal,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    _ ≤ ((R + S) ^ 2 + 1 / 4) / 2 := by
      exact div_le_div_of_nonneg_right
        (add_le_add_right hsq (1 / 4))
        (by norm_num)

/-- The rectangle bound for `‖z^2 + 1/4‖ / 2`. -/
theorem rectangle_D_half_spec
    (x0 x1 y0 y1 : ℝ)
    (x_lt : x0 < x1)
    (y_lt : y0 < y1)
    (z : ℂ)
    (hx0 : x0 < z.re)
    (hx1 : z.re < x1)
    (hy0 : y0 < z.im)
    (hy1 : z.im < y1) :
    ‖z ^ 2 + (1 / 4 : ℂ)‖ / 2 ≤
      rectangleDHalf x0 x1 y0 y1 := by
  have hre : |z.re| ≤ |x0| + |x1| + 1 := by
    apply abs_le.mpr
    constructor
    · have : -|x0| ≤ x0 := neg_abs_le_self x0
      linarith [abs_nonneg x1]
    · have : x1 ≤ |x1| := le_abs_self x1
      linarith [abs_nonneg x0]

  have him : |z.im| ≤ |y0| + |y1| + 1 := by
    apply abs_le.mpr
    constructor
    · have : -|y0| ≤ y0 := neg_abs_le_self y0
      linarith [abs_nonneg y1]
    · have : y1 ≤ |y1| := le_abs_self y1
      linarith [abs_nonneg y0]

  exact
    norm_z_sq_add_quarter_le
      z
      (|x0| + |x1| + 1)
      (|y0| + |y1| + 1)
      (by positivity)
      (by positivity)
      hre
      him

/-- A simplified rectangle certificate template.

The geometric `D_half` bound is supplied automatically by
`rectangle_D_half_spec`. The remaining analytic obligations are:

1. `bound`: an upper bound for `completedRiemannZeta₀`;
2. `margin_pos`: positivity of the resulting lower-bound margin.
-/
structure SimpleRectCertificateTemplate where
  x0 : ℝ
  x1 : ℝ
  y0 : ℝ
  y1 : ℝ
  x_lt : x0 < x1
  y_lt : y0 < y1
  y_nonneg : 0 ≤ y0
  y_upper : y1 ≤ (1 / 2 : ℝ)
  U : ℝ
  U_nonneg : 0 ≤ U
  bound :
    ∀ z : ℂ,
      x0 < z.re →
      z.re < x1 →
      y0 < z.im →
      z.im < y1 →
      ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + I * z)‖ ≤ U
  margin_pos :
    0 < (1 / 2 : ℝ) - rectangleDHalf x0 x1 y0 y1 * U

/-- Convert a simple rectangle template into a full completed-zeta rectangle
    upper-bound certificate. -/
def completedZetaRectUpperBoundCertificate_from_simple_template
    (T : SimpleRectCertificateTemplate) :
    CompletedZetaRectUpperBoundCertificate where
  x0 := T.x0
  x1 := T.x1
  y0 := T.y0
  y1 := T.y1
  x_lt := T.x_lt
  y_lt := T.y_lt
  y_lower := by linarith [T.y_nonneg]
  y_upper := T.y_upper
  U := T.U
  U_nonneg := T.U_nonneg
  D_half := rectangleDHalf T.x0 T.x1 T.y0 T.y1
  D_half_nonneg := by
    dsimp [rectangleDHalf]
    positivity
  D_half_spec := by
    intro z hx0 hx1 hy0 hy1
    exact
      rectangle_D_half_spec
        T.x0 T.x1 T.y0 T.y1
        T.x_lt T.y_lt
        z hx0 hx1 hy0 hy1
  bound := T.bound
  margin_pos := T.margin_pos

/-!
# Canonical margin constructors

These constructors remove the algebraic margin obligations.

For rectangles, if one can prove

    ‖completedRiemannZeta₀(1/2 + i z)‖ ≤ 1 / (8 * rectangleDHalf ...)

then the margin

    0 < 1/2 - rectangleDHalf * U

is automatic.

For tails, if one can prove

    ‖completedRiemannZeta₀(1/2 + i z)‖ ≤ tailCanonicalU z.re z.im

then the tail margin is automatic.
-/

/-- Positivity of the crude rectangle geometric bound. -/
theorem rectangleDHalf_pos
    (x0 x1 y0 y1 : ℝ) :
    0 < rectangleDHalf x0 x1 y0 y1 := by
  dsimp [rectangleDHalf]
  positivity

/-- A rectangle template with canonical margin.

The only remaining obligation is the explicit upper bound.
-/
def simpleRectTemplate_canonical_margin
    (x0 x1 y0 y1 : ℝ)
    (x_lt : x0 < x1)
    (y_lt : y0 < y1)
    (y_nonneg : 0 ≤ y0)
    (y_upper : y1 ≤ (1 / 2 : ℝ))
    (bound :
      ∀ z : ℂ,
        x0 < z.re →
        z.re < x1 →
        y0 < z.im →
        z.im < y1 →
        ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + I * z)‖ ≤
          1 / (8 * rectangleDHalf x0 x1 y0 y1)) :
    SimpleRectCertificateTemplate where
  x0 := x0
  x1 := x1
  y0 := y0
  y1 := y1
  x_lt := x_lt
  y_lt := y_lt
  y_nonneg := y_nonneg
  y_upper := y_upper
  U := 1 / (8 * rectangleDHalf x0 x1 y0 y1)
  U_nonneg := by
    have hD := rectangleDHalf_pos x0 x1 y0 y1
    positivity
  bound := bound
  margin_pos := by
    have hD := rectangleDHalf_pos x0 x1 y0 y1
    have hprod :
        rectangleDHalf x0 x1 y0 y1 *
          (1 / (8 * rectangleDHalf x0 x1 y0 y1)) =
        1 / 8 := by
      field_simp
    linarith

/-!
# Canonical tail margin
-/

/-- Canonical tail upper-bound shape.

This is deliberately small enough that the margin is automatic.
-/
noncomputable def tailCanonicalU (r y : ℝ) : ℝ :=
  if h : ‖tailD r y‖ = 0 then 0
  else 1 / (8 * ‖tailD r y‖)

/-- The canonical tail margin is automatically positive. -/
theorem tailCanonicalU_margin
    (r y : ℝ) :
    0 <
      (1 / 2 : ℝ) -
        (‖tailD r y‖ / 2) * tailCanonicalU r y := by
  by_cases h : ‖tailD r y‖ = 0
  · simp [tailCanonicalU, h]
    norm_num
  · simp [tailCanonicalU, h]
    field_simp
    norm_num

/-- The canonical tail U is nonnegative. -/
theorem tailCanonicalU_nonneg
    (r y : ℝ) :
    0 ≤ tailCanonicalU r y := by
  by_cases h : ‖tailD r y‖ = 0
  · simp [tailCanonicalU, h]
  · simp [tailCanonicalU, h]
    positivity

/-- A tail certificate with canonical margin.

The only remaining obligation is the explicit upper bound.
-/
def completedZetaUpperBoundTail_canonical
    (X : ℝ)
    (bound :
      ∀ z : ℂ,
        X < z.re →
        -(1 / 2 : ℝ) < z.im →
        z.im < (1 / 2 : ℝ) →
        z.im ≠ 0 →
        ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + I * z)‖ ≤
          tailCanonicalU z.re z.im) :
    CompletedZetaUpperBoundTail X where
  U := tailCanonicalU
  U_nonneg := by
    intro r y _ _
    exact tailCanonicalU_nonneg r y
  bound := bound
  margin_pos := by
    intro r y _ _
    exact tailCanonicalU_margin r y

/-!
# Explicit sufficient tail estimate

We prove:

1. For r ≥ 10 and |y| < 1/2,

       r^2 ≤ ‖tailD r y‖.

2. Also,

       ‖tailD r y‖ ≤ (r + 1)^2.

Therefore:

       1 / (8 * (r + 1)^2) ≤ tailCanonicalU r y.

So it is enough to prove:

       ‖completedRiemannZeta₀(1/2 + i z)‖ ≤ 1 / (8 * (Re z + 1)^2)

in the tail.
-/

/-- Public helper: real part bounded by norm. -/
theorem abs_re_le_norm_pub (w : ℂ) :
    |w.re| ≤ ‖w‖ := by
  simpa [Complex.norm_eq_abs] using Complex.abs_re_le_abs w

/-- Lower bound for the tail quadratic factor. -/
theorem tailD_norm_ge_r_sq
    (r y : ℝ)
    (hr : 10 ≤ r)
    (hgt : -(1 / 2 : ℝ) < y)
    (hlt : y < (1 / 2 : ℝ)) :
    (r : ℝ) ^ 2 ≤ ‖tailD r y‖ := by
  have hre : (tailD r y).re = r ^ 2 - y ^ 2 + 1 / 4 := by
    simp [
      tailD,
      pow_two,
      Complex.add_re,
      Complex.mul_re,
      Complex.ofReal_re,
      Complex.ofReal_im,
      Complex.I_re,
      Complex.I_im
    ]
    ring

  have hy2 : y ^ 2 < 1 / 4 := by
    nlinarith

  have hreal : (r : ℝ) ^ 2 ≤ (tailD r y).re := by
    rw [hre]
    linarith

  have hre_nonneg : 0 ≤ (tailD r y).re := by
    rw [hre]
    nlinarith [pow_nonneg (by linarith : 0 ≤ (r : ℝ)) 2]

  have habs : |(tailD r y).re| ≤ ‖tailD r y‖ :=
    abs_re_le_norm_pub (tailD r y)

  rw [abs_of_nonneg hre_nonneg] at habs
  linarith

/-- Upper bound for the tail quadratic factor. -/
theorem tailD_norm_le_r_plus_one_sq
    (r y : ℝ)
    (hr : 10 ≤ r)
    (hgt : -(1 / 2 : ℝ) < y)
    (hlt : y < (1 / 2 : ℝ)) :
    ‖tailD r y‖ ≤ (r + 1) ^ 2 := by
  let z : ℂ := (r : ℂ) + I * (y : ℂ)

  have hznorm : ‖z‖ ≤ r + 1 / 2 := by
    calc
      ‖z‖ = ‖(r : ℂ) + I * (y : ℂ)‖ := rfl
      _ ≤ ‖(r : ℂ)‖ + ‖I * (y : ℂ)‖ := norm_add_le _ _
      _ = |r| + |y| := by
        simp [norm_mul, Complex.norm_I]
      _ ≤ r + 1 / 2 := by
        have hrabs : |r| = r := abs_of_nonneg (by linarith)
        have hyabs : |y| ≤ 1 / 2 := by
          rw [abs_le]
          constructor <;> linarith
        linarith

  calc
    ‖tailD r y‖ = ‖z ^ 2 + (1 / 4 : ℂ)‖ := by
      simp [tailD, z]
    _ ≤ ‖z ^ 2‖ + ‖(1 / 4 : ℂ)‖ := norm_add_le _ _
    _ = ‖z‖ ^ 2 + 1 / 4 := by
      simp [
        norm_pow,
        Complex.norm_ofReal,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)
      ]
    _ ≤ (r + 1 / 2) ^ 2 + 1 / 4 := by
      have hsqr : ‖z‖ ^ 2 ≤ (r + 1 / 2) ^ 2 := by
        gcongr
      linarith
    _ ≤ (r + 1) ^ 2 := by
      ring_nf
      nlinarith

/-- The canonical tail U is at least `1 / (8 * (r + 1)^2)` in the tail strip. -/
theorem tailCanonicalU_ge_inv_r_plus_one_sq
    (r y : ℝ)
    (hr : 10 ≤ r)
    (hgt : -(1 / 2 : ℝ) < y)
    (hlt : y < (1 / 2 : ℝ)) :
    1 / (8 * (r + 1) ^ 2) ≤ tailCanonicalU r y := by
  have hDne : ‖tailD r y‖ ≠ 0 := by
    have hge := tailD_norm_ge_r_sq r y hr hgt hlt
    intro h
    rw [h] at hge
    have : (r : ℝ) ^ 2 ≤ 0 := hge
    have : r = 0 := by
      nlinarith
    linarith

  simp [tailCanonicalU, hDne]

  have hle := tailD_norm_le_r_plus_one_sq r y hr hgt hlt

  rw [div_le_div_iff (by positivity) (by positivity)]
  nlinarith

/-- A concrete polynomial decay bound sufficient for the tail certificate.

If one proves

    ‖completedRiemannZeta₀(1/2 + i z)‖ ≤ 1 / (8 * (Re z + 1)^2)

for Re z > X ≥ 10 and |Im z| < 1/2, then the full tail certificate follows.
-/
theorem completedZetaUpperBoundTail_of_simple_polynomial_bound
    (X : ℝ)
    (hX : 10 ≤ X)
    (bound :
      ∀ z : ℂ,
        X < z.re →
        -(1 / 2 : ℝ) < z.im →
        z.im < (1 / 2 : ℝ) →
        z.im ≠ 0 →
        ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + I * z)‖ ≤
          1 / (8 * (z.re + 1) ^ 2)) :
    CompletedZetaUpperBoundTail X :=
  completedZetaUpperBoundTail_canonical X (by
    intro z hre hgt hlt hne
    have hrez : 10 ≤ z.re := by linarith
    have hsimple := bound z hre hgt hlt hne
    exact le_trans hsimple
      (tailCanonicalU_ge_inv_r_plus_one_sq z.re z.im hrez hgt hlt))

/-!
# Exact shifted identities

Let

    s = shiftedS z = 1/2 + i z,
    D = z^2 + 1/4.

Then:

    s(1 - s) = D,
    s(s - 1) = -D.

Also:

    1/s + 1/(1-s) = 1/D.

Using the polar/xi decomposition, we get:

    completedRiemannZeta₀(s) = 1/D - 2 * xiShifted(z) / D.

Equivalently:

    1/D - completedRiemannZeta₀(s) = 2 * xiShifted(z) / D.

Thus xiShifted(z) ≠ 0 is exactly the statement that
completedRiemannZeta₀(s) differs from 1/D.
-/

theorem shiftedS_mul_one_sub
    (z : ℂ) :
    shiftedS z * (1 - shiftedS z) =
      z ^ 2 + (1 / 4 : ℂ) := by
  simp [shiftedS]
  ring

theorem shiftedS_mul_sub_one_neg
    (z : ℂ) :
    shiftedS z * (shiftedS z - 1) =
      -(z ^ 2 + (1 / 4 : ℂ)) := by
  simp [shiftedS]
  ring

theorem polar_term_eq_inv_D
    (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im)
    (hlt : z.im < (1 / 2 : ℝ)) :
    1 / shiftedS z + 1 / (1 - shiftedS z) =
      1 / (z ^ 2 + (1 / 4 : ℂ)) := by
  have hs0 : shiftedS z ≠ 0 := shiftedS_ne_zero z hgt hlt
  have h1s : 1 - shiftedS z ≠ 0 := by
    intro h
    exact shiftedS_ne_one z hgt hlt (sub_eq_zero.mp h).symm

  have hprod : shiftedS z * (1 - shiftedS z) = z ^ 2 + (1 / 4 : ℂ) :=
    shiftedS_mul_one_sub z

  calc
    1 / shiftedS z + 1 / (1 - shiftedS z) =
        (1 - shiftedS z + shiftedS z) /
          (shiftedS z * (1 - shiftedS z)) := by
      field_simp [hs0, h1s]
    _ = 1 / (shiftedS z * (1 - shiftedS z)) := by
      ring
    _ = 1 / (z ^ 2 + (1 / 4 : ℂ)) := by
      rw [hprod]

theorem completedZeta_shifted_eq_inv_D_sub_two_classicalXi_div_D
    (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im)
    (hlt : z.im < (1 / 2 : ℝ))
    (hne : z.im ≠ 0) :
    completedRiemannZeta₀ (shiftedS z) =
      1 / (z ^ 2 + (1 / 4 : ℂ)) -
      2 * classicalXi (shiftedS z) /
        (z ^ 2 + (1 / 4 : ℂ)) := by
  have hdecomp := completedZeta_decomp_polar_xi z hgt hlt hne
  rw [hdecomp, polar_term_eq_inv_D z hgt hlt]

  have hD : z ^ 2 + (1 / 4 : ℂ) ≠ 0 :=
    shifted_denominator_ne_zero_inside_strip z hgt hlt

  have hss : shiftedS z * (shiftedS z - 1) =
      -(z ^ 2 + (1 / 4 : ℂ)) :=
    shiftedS_mul_sub_one_neg z

  rw [hss]
  field_simp [hD]
  ring

theorem completedZeta_shifted_eq_inv_D_sub_two_xiShifted_div_D
    (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im)
    (hlt : z.im < (1 / 2 : ℝ))
    (hne : z.im ≠ 0) :
    completedRiemannZeta₀ (shiftedS z) =
      1 / (z ^ 2 + (1 / 4 : ℂ)) -
      2 * xiShifted z /
        (z ^ 2 + (1 / 4 : ℂ)) := by
  simpa [xiShifted] using
    completedZeta_shifted_eq_inv_D_sub_two_classicalXi_div_D z hgt hlt hne

theorem inv_D_sub_completedZeta_eq_two_xiShifted_div_D
    (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im)
    (hlt : z.im < (1 / 2 : ℝ))
    (hne : z.im ≠ 0) :
    1 / (z ^ 2 + (1 / 4 : ℂ)) -
      completedRiemannZeta₀ (shiftedS z) =
    2 * xiShifted z /
      (z ^ 2 + (1 / 4 : ℂ)) := by
  rw [completedZeta_shifted_eq_inv_D_sub_two_xiShifted_div_D z hgt hlt hne]
  ring

/-- The nonvanishing target is equivalent to saying that
`completedRiemannZeta₀(shiftedS z)` is not equal to `1 / (z^2 + 1/4)`.
-/
theorem xiShifted_ne_zero_iff_completed_ne_inv_D
    (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im)
    (hlt : z.im < (1 / 2 : ℝ))
    (hne : z.im ≠ 0) :
    xiShifted z ≠ 0 ↔
    completedRiemannZeta₀ (shiftedS z) ≠
      1 / (z ^ 2 + (1 / 4 : ℂ)) := by
  have hD : z ^ 2 + (1 / 4 : ℂ) ≠ 0 :=
    shifted_denominator_ne_zero_inside_strip z hgt hlt

  constructor
  · intro hz hbad
    have h := inv_D_sub_completedZeta_eq_two_xiShifted_div_D z hgt hlt hne
    rw [hbad, sub_self] at h
    have hzero : 2 * xiShifted z / (z ^ 2 + (1 / 4 : ℂ)) = 0 := by
      simpa using h
    have hxi : xiShifted z = 0 := by
      field_simp [hD] at hzero
      simpa using hzero
    exact hz hxi
  · intro hne_completed hz
    have h := inv_D_sub_completedZeta_eq_two_xiShifted_div_D z hgt hlt hne
    rw [hz] at h
    have hzero :
        1 / (z ^ 2 + (1 / 4 : ℂ)) -
          completedRiemannZeta₀ (shiftedS z) = 0 := by
      field_simp [hD] at h
      simpa using h
    have hbad :
        completedRiemannZeta₀ (shiftedS z) =
          1 / (z ^ 2 + (1 / 4 : ℂ)) := by
      rw [sub_eq_zero] at hzero
      exact hzero.symm
    exact hne_completed hbad

/-!
# The remaining hard analytic problem, stated explicitly

Define the statement:

    For all off-real z in the shifted strip,

      1 / (z^2 + 1/4) - completedRiemannZeta₀(shiftedS z) ≠ 0.

This is equivalent to:

    xiShifted z ≠ 0

for all off-real z in the shifted strip, and therefore equivalent to RH.
-/

/-- The hard difference-nonzero statement. -/
def HardDifferenceNonzero : Prop :=
  ∀ z : ℂ,
    -(1 / 2 : ℝ) < z.im →
    z.im < (1 / 2 : ℝ) →
    z.im ≠ 0 →
    1 / (z ^ 2 + (1 / 4 : ℂ)) -
      completedRiemannZeta₀ (shiftedS z) ≠ 0

/-- The hard difference-nonzero statement implies RH. -/
theorem hardDifferenceNonzero_implies_RH :
    HardDifferenceNonzero → RiemannHypothesisProp := by
  intro H
  rw [rh_iff_xi_off_real_pointwise_nonvanishing_mathlib]
  intro z hgt hlt hne
  have hD : z ^ 2 + (1 / 4 : ℂ) ≠ 0 :=
    shifted_denominator_ne_zero_inside_strip z hgt hlt
  intro hz
  have hdiff := H z hgt hlt hne
  rw [inv_D_sub_completedZeta_eq_two_xiShifted_div_D z hgt hlt hne, hz] at hdiff
  field_simp [hD] at hdiff
  exact hdiff rfl

/-- RH implies the hard difference-nonzero statement. -/
theorem RH_implies_hardDifferenceNonzero :
    RiemannHypothesisProp → HardDifferenceNonzero := by
  intro H
  rw [rh_iff_xi_off_real_pointwise_nonvanishing_mathlib] at H
  intro z hgt hlt hne
  have hnz := H z hgt hlt hne
  have hD : z ^ 2 + (1 / 4 : ℂ) ≠ 0 :=
    shifted_denominator_ne_zero_inside_strip z hgt hlt
  intro h
  rw [inv_D_sub_completedZeta_eq_two_xiShifted_div_D z hgt hlt hne] at h
  have hzero :
      2 * xiShifted z / (z ^ 2 + (1 / 4 : ℂ)) = 0 := h
  rw [div_eq_zero_iff] at hzero
  cases hzero with
  | inl hmul =>
    have hxi : xiShifted z = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (by norm_num)
    exact hnz hxi
  | inr hD0 =>
    exact hD hD0

/-- The hard difference-nonzero statement is equivalent to RH. -/
theorem hardDifferenceNonzero_iff_RH :
    HardDifferenceNonzero ↔ RiemannHypothesisProp := by
  constructor
  · exact hardDifferenceNonzero_implies_RH
  · exact RH_implies_hardDifferenceNonzero

/-!
# The remaining hard analytic problem, stated explicitly

Define the statement:

    For all off-real z in the shifted strip,

      1 / (z^2 + 1/4) - completedRiemannZeta₀(shiftedS z) ≠ 0.

This is equivalent to:

    xiShifted z ≠ 0

for all off-real z in the shifted strip, and therefore equivalent to RH.
-/

/-- The hard difference-nonzero statement. -/
def HardDifferenceNonzero : Prop :=
  ∀ z : ℂ,
    -(1 / 2 : ℝ) < z.im →
    z.im < (1 / 2 : ℝ) →
    z.im ≠ 0 →
    1 / (z ^ 2 + (1 / 4 : ℂ)) -
      completedRiemannZeta₀ (shiftedS z) ≠ 0

/-- The hard difference-nonzero statement implies RH. -/
theorem hardDifferenceNonzero_implies_RH :
    HardDifferenceNonzero → RiemannHypothesisProp := by
  intro H
  rw [rh_iff_xi_off_real_pointwise_nonvanishing_mathlib]
  intro z hgt hlt hne
  have hD : z ^ 2 + (1 / 4 : ℂ) ≠ 0 :=
    shifted_denominator_ne_zero_inside_strip z hgt hlt
  intro hz
  have hdiff := H z hgt hlt hne
  rw [inv_D_sub_completedZeta_eq_two_xiShifted_div_D z hgt hlt hne, hz] at hdiff
  field_simp [hD] at hdiff
  exact hdiff rfl

/-- RH implies the hard difference-nonzero statement. -/
theorem RH_implies_hardDifferenceNonzero :
    RiemannHypothesisProp → HardDifferenceNonzero := by
  intro H
  rw [rh_iff_xi_off_real_pointwise_nonvanishing_mathlib] at H
  intro z hgt hlt hne
  have hnz := H z hgt hlt hne
  have hD : z ^ 2 + (1 / 4 : ℂ) ≠ 0 :=
    shifted_denominator_ne_zero_inside_strip z hgt hlt
  intro h
  rw [inv_D_sub_completedZeta_eq_two_xiShifted_div_D z hgt hlt hne] at h
  have hzero :
      2 * xiShifted z / (z ^ 2 + (1 / 4 : ℂ)) = 0 := h
  rw [div_eq_zero_iff] at hzero
  cases hzero with
  | inl hmul =>
    have hxi : xiShifted z = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (by norm_num)
    exact hnz hxi
  | inr hD0 =>
    exact hD hD0

/-- The hard difference-nonzero statement is equivalent to RH. -/
theorem hardDifferenceNonzero_iff_RH :
    HardDifferenceNonzero ↔ RiemannHypothesisProp := by
  constructor
  · exact hardDifferenceNonzero_implies_RH
  · exact RH_implies_hardDifferenceNonzero

/-!
# Partial attack: prove the difference nonzero on the imaginary axis

For z = i y with -1/2 < y < 1/2 and y ≠ 0, we have

    shiftedS z = 1/2 - y ∈ (0,1).

Thus classicalXi(shiftedS z) is a nonzero prefactor times ζ(1/2 - y).
So it suffices to know that ζ(t) ≠ 0 for real t ∈ (0,1).
-/

/-- Standard real nonvanishing of ζ in the open critical interval. -/
def ZetaRealNonzeroInCritical : Prop :=
  ∀ t : ℝ,
    0 < t →
    t < 1 →
    zeta (t : ℂ) ≠ 0

/-- `xiShifted` is nonzero on the imaginary axis, assuming real ζ-nonvanishing
    in (0,1). -/
theorem xiShifted_ne_zero_on_imaginary_axis
    (hReal : ZetaRealNonzeroInCritical)
    (y : ℝ)
    (hyne : y ≠ 0)
    (hgt : -(1 / 2 : ℝ) < y)
    (hlt : y < (1 / 2 : ℝ)) :
    xiShifted (I * (y : ℂ)) ≠ 0 := by
  let z : ℂ := I * (y : ℂ)

  have hs : shiftedS z = ((1 / 2 - y : ℝ) : ℂ) := by
    simp [shiftedS, z]
    ring

  have ht0 : 0 < (1 / 2 - y : ℝ) := by linarith
  have ht1 : (1 / 2 - y : ℝ) < 1 := by linarith

  have hpref :
      classicalXiPrefactor ((1 / 2 - y : ℝ) : ℂ) ≠ 0 :=
    classical_prefactor_nonzero_instrip
      classical_gamma_nonzero_instrip
      _
      (by simpa using ht0)
      (by simpa using ht1)

  intro hzero

  have hmul :
      classicalXiPrefactor ((1 / 2 - y : ℝ) : ℂ) *
        zeta ((1 / 2 - y : ℝ) : ℂ) = 0 := by
    simpa [xiShifted, classicalXi, XiFromPrefactor, hs] using hzero

  have hzeta : zeta ((1 / 2 - y : ℝ) : ℂ) = 0 :=
    (mul_eq_zero.mp hmul).resolve_left hpref

  exact hReal (1 / 2 - y) ht0 ht1 hzeta

/-- Therefore the hard difference is nonzero on the imaginary axis. -/
theorem hardDifferenceNonzero_on_imaginary_axis
    (hReal : ZetaRealNonzeroInCritical)
    (y : ℝ)
    (hyne : y ≠ 0)
    (hgt : -(1 / 2 : ℝ) < y)
    (hlt : y < (1 / 2 : ℝ)) :
    1 / ((I * (y : ℂ)) ^ 2 + (1 / 4 : ℂ)) -
      completedRiemannZeta₀ (shiftedS (I * (y : ℂ))) ≠ 0 := by
  have hne : (I * (y : ℂ)).im ≠ 0 := by
    simpa using hyne
  have h := xiShifted_ne_zero_on_imaginary_axis hReal y hyne hgt hlt
  exact
    (xiShifted_ne_zero_iff_completed_ne_inv_D
      (I * (y : ℂ)) hgt hlt hne).mp h
