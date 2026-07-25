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
