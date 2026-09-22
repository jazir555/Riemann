import Mathlib
import central_cover_assembly
import door3_premise_poly
import door3_premise_pi
import door3_premise_gamma
import door3_tail_eta_upper

/-!
# Door-3 local factor-derivative uppers for the subdivision plan (WRITE-ONLY).

No build / lean / lake command run. No commit / push. One new file only.

## Import leaf check (read-only, verified before writing)

* `door3_premise_poly.lean:1-2` imports `Mathlib` + `central_cover_assembly` only.
* `door3_premise_pi.lean:1-2` imports `Mathlib` + `central_cover_assembly` only.
* `door3_premise_gamma.lean:1-3` imports `Mathlib` + `central_cover_assembly`
  + `door3_stirling_gamma`, and `door3_stirling_gamma.lean:1` imports `Mathlib`
  only. Hence the import graph stays a DAG; this file creates no cycle.
* This file reuses premise uppers by exact theorem name
  (`premPoly_R00_ge`, `Door3PremisePi.piOf_le_one_of_re_nonneg`,
  `Door3PremisePi.premPi_R00_le`, `Door3PremiseGamma.premGamma_wide_of_mem`,
  `Door3PremiseGamma.premGamma_BA00_le`). Nothing is re-proved locally.

## Subdivision targets (from `door3_subdiv_plan.lean`)

* outer M prime = 0.11, feasibility `0.002 + 0.11 * 0.5 <= 0.0678 - 0.01`.
* leaf M prime = 0.15, feasibility `0.002 + 0.15 * 0.5 <= 0.091 - 0.01`.
* mid M prime = 0.15, feasibility `0.05 + 0.15 * 0.5 <= 0.14 - 0.01`.
* inner M prime = 0.09, feasibility `0.15 + 0.09 * 0.9 <= 0.25 - 0.01`.
* Cauchy shape reused: `plan_cauchy_template` (shared sup C over a sphere of
  radius rhoC gives `‖deriv‖ <= C / rhoC`).

## Representative centers (one per row group)

* outer: dOuter = 0.395 - 8.75 I (batch A R00 class).
* leaf: dLeaf = 0.2 - 6.75 I (batch D R22 class).
* mid: dMid = 0.395 - 4.75 I (batch A R03 class).
* inner: dInner = 0.395 - 0.75 I (batch E R05 class).

## Results banked here

* poly prime EXACT via `poly_hasDerivAt`: outer <= 8.86, leaf <= 7.06,
  mid <= 4.86, inner <= 0.86. All closed.
* pi prime closed form via `HasDerivAt.const_cpow` plus banked pi uppers:
  `‖deriv piOf‖ <= ‖piOf‖ * ‖log pi‖ / 2` with `‖log pi‖ <= 2.15` proved from
  `Real.log_le_sub_one_of_pos` + `Real.pi_lt_d2` (no banked `Real.log_pi`
  upper was found in Mathlib; local proof used instead).
  With `‖piOf‖ <= 1`: outer / leaf / mid / inner <= 1.075. All closed.
* gamma prime: option (i) shifted representation needs a real-Gamma prime
  bound that is not banked; option (ii) Cauchy with rhoC = 0.01 and the
  tightest closed local numeral C <= 600 gives C / rhoC = 60000, far above
  any per-group budget share. Recorded as DERIV-GAP with numbers below.
  The wide premise-gamma numerals 67-498 mentioned in the brief would give
  6700-49800, equally useless; we use the uniform 600 majorant so every
  center is covered by one closed lemma.
* zeta prime / zeta values: Euler / FE pieces live in the ballsup tail
  (`door3_cutR10_ballsup.lean`, `door3_cutL10_remainders.lean`,
  `door3_premise_zeta.lean`, read-only reference only, not imported).
  Reproving them needs more than three lemmas, so they are taken as
  explicit premises (`zetaValCap_*`, `zetaSupOnSphere_*`,
  `zetaDiffCont_*`). Conditional Cauchy then gives `‖zeta prime‖ <= 1000`.
* Leibniz assembly `leibniz4_norm` is closed conditionally. With the closed
  poly / pi primes plus tight TRUE-scale value premises for gamma / zeta,
  the gamma-prime and zeta-prime terms dominate: total upper exceeds M
  prime in every group. Recorded as DERIV-GAP with explicit ratios.
  Nothing is forced.

## Remainder (cell-by-cell extension)

Generic lemmas cover all 40 centers once tight local gamma / zeta sups land:
`poly_derivUp_of_abs`, `pi_derivUp_of_upper`, `gammaDerivUp_of_sup`,
`zetaDerivUp_of_sup`, `leibniz4_norm`. Per-cell work owed: tight local
`‖gammaOf‖` (TRUE scale 0.001-5 by row) and `‖zeta‖` (TRUE scale 1-3) on
each 0.01-sphere, plus `DiffContOnCl` on each disc away from Gamma poles.
-/

noncomputable section

namespace Door3DerivUp

open Metric

/-! ## 0. Premise reuse check (exact names; proves the imports resolve). -/

theorem reuse_poly_R00 : (34 : ℝ) ≤ ‖DerivCauchyBridge.polyOf sR00‖ :=
  premPoly_R00_ge

theorem reuse_pi_R00_le : ‖DerivCauchyBridge.piOf Door3PremisePi.sPiR00‖ ≤ 1 :=
  Door3PremisePi.premPi_R00_le

theorem reuse_gamma_BA00_le :
    ‖DerivCauchyBridge.gammaOf (Complex.mk 0.395 (-8.75))‖ ≤
      600 * Real.exp (-(1 / 2) * |((Complex.mk 0.395 (-8.75) : ℂ) / 2).im|) :=
  Door3PremiseGamma.premGamma_BA00_le

/-! ## 1. Cauchy helpers (local reproof of the plan template shape). -/

theorem cauchy_derivUp_of_sphere (f : ℂ → ℂ) (w : ℂ) (r C : ℝ)
    (hr : 0 < r)
    (hd : DiffContOnCl ℂ f (Metric.ball w r))
    (hC : ∀ z : ℂ, z ∈ Metric.sphere w r → ‖f z‖ ≤ C) :
    ‖deriv f w‖ ≤ C / r :=
  Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd hC

theorem cauchy_derivUp_of_closedBall (f : ℂ → ℂ) (c w : ℂ) (R r C : ℝ)
    (hr : 0 < r)
    (hd : DiffContOnCl ℂ f (Metric.ball c R))
    (hB : ∀ z : ℂ, z ∈ Metric.closedBall c R → ‖f z‖ ≤ C)
    (hw : ‖w - c‖ + r ≤ R) :
    ‖deriv f w‖ ≤ C / r := by
  have hball : Metric.ball w r ⊆ Metric.ball c R := by
    intro z hz
    have hzw : ‖z - w‖ < r := by
      rw [← dist_eq_norm]
      exact hz
    show dist z c < R
    calc dist z c ≤ dist z w + dist w c := dist_triangle z w c
      _ = ‖z - w‖ + ‖w - c‖ := by
        rw [dist_eq_norm z w, dist_eq_norm w c]
      _ < r + ‖w - c‖ := add_lt_add_of_lt_of_le hzw le_rfl
      _ = ‖w - c‖ + r := add_comm r ‖w - c‖
      _ ≤ R := hw
  have hsph : Metric.sphere w r ⊆ Metric.closedBall c R := by
    intro z hz
    have h1 : ‖z - w‖ = r := by
      have hdist : dist z w = r := Metric.mem_sphere.mp hz
      rwa [dist_eq_norm] at hdist
    show dist z c ≤ R
    calc dist z c = ‖(z - w) + (w - c)‖ := by
        rw [dist_eq_norm]
        congr 1
        abel
      _ ≤ ‖z - w‖ + ‖w - c‖ := norm_add_le (z - w) (w - c)
      _ = r + ‖w - c‖ := by rw [h1]
      _ = ‖w - c‖ + r := add_comm r ‖w - c‖
      _ ≤ R := hw
  have hC : ∀ z : ℂ, z ∈ Metric.sphere w r → ‖f z‖ ≤ C := by
    intro z hz
    exact hB z (hsph hz)
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr (hd.mono hball) hC

/-! ## 2. Centers. -/

noncomputable def dOuter : ℂ := Complex.mk 0.395 (-8.75)

noncomputable def dLeaf : ℂ := Complex.mk 0.2 (-6.75)

noncomputable def dMid : ℂ := Complex.mk 0.395 (-4.75)

noncomputable def dInner : ℂ := Complex.mk 0.395 (-0.75)

theorem dOuter_re : dOuter.re = (0.395 : ℝ) := rfl

theorem dOuter_im : dOuter.im = (-8.75 : ℝ) := rfl

theorem dLeaf_re : dLeaf.re = (0.2 : ℝ) := rfl

theorem dLeaf_im : dLeaf.im = (-6.75 : ℝ) := rfl

theorem dMid_re : dMid.re = (0.395 : ℝ) := rfl

theorem dMid_im : dMid.im = (-4.75 : ℝ) := rfl

theorem dInner_re : dInner.re = (0.395 : ℝ) := rfl

theorem dInner_im : dInner.im = (-0.75 : ℝ) := rfl

/-! ## 3. Poly prime: exact derivative plus generic and per-center uppers. -/

theorem poly_hasDerivAt (s : ℂ) :
    HasDerivAt DerivCauchyBridge.polyOf (s - 1 / 2) s := by
  have hid : HasDerivAt (fun t : ℂ => t) 1 s :=
    hasDerivAt_id' (x := s)
  have hconst : HasDerivAt (fun t : ℂ => (1 : ℂ)) 0 s :=
    hasDerivAt_const (x := s) (c := (1 : ℂ))
  have hsub : HasDerivAt (fun t : ℂ => t - (1 : ℂ)) (1 - 0) s :=
    hid.sub hconst
  have hmul : HasDerivAt (fun t : ℂ => t * (t - (1 : ℂ)))
      (1 * (s - 1) + s * (1 - 0)) s :=
    hid.mul hsub
  have hdiv : HasDerivAt (fun t : ℂ => t * (t - (1 : ℂ)) / 2)
      ((1 * (s - 1) + s * (1 - 0)) / 2) s :=
    hmul.div_const (2 : ℂ)
  have heqF : (fun t : ℂ => t * (t - (1 : ℂ)) / 2) = DerivCauchyBridge.polyOf := by
    unfold DerivCauchyBridge.polyOf
    rfl
  have heqD : (1 * (s - 1) + s * (1 - 0)) / 2 = s - 1 / 2 := by
    ring
  rw [heqF] at hdiv
  rw [heqD] at hdiv
  exact hdiv

theorem poly_deriv_eq (s : ℂ) :
    deriv DerivCauchyBridge.polyOf s = s - 1 / 2 :=
  (poly_hasDerivAt s).deriv

theorem poly_derivUp_of_abs (s : ℂ) (A B : ℝ)
    (hre : |s.re| ≤ A) (him : |s.im| ≤ B) :
    ‖deriv DerivCauchyBridge.polyOf s‖ ≤ A + B + 0.5 := by
  rw [poly_deriv_eq s]
  have h1 : ‖s - 1 / 2‖ ≤ ‖s‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le s (1 / 2)
  have h2 : ‖s‖ ≤ |s.re| + |s.im| :=
    Complex.norm_le_abs_re_add_abs_im s
  have h3 : ‖(1 / 2 : ℂ)‖ = (0.5 : ℝ) := by
    have e1 : ((1 / 2 : ℂ)) = (1 : ℂ) / 2 := by norm_num
    rw [e1, norm_div, Complex.norm_one, Complex.norm_two]
    norm_num
  have h4 : ‖s - 1 / 2‖ ≤ (|s.re| + |s.im|) + 0.5 := by
    calc ‖s - 1 / 2‖ ≤ ‖s‖ + ‖(1 / 2 : ℂ)‖ := h1
      _ ≤ (|s.re| + |s.im|) + 0.5 := by
        rw [h3] at h1 ⊢
        linarith [h2]
  calc ‖s - 1 / 2‖ ≤ (|s.re| + |s.im|) + 0.5 := h4
    _ ≤ (A + B) + 0.5 := by linarith [hre, him]
    _ = A + B + 0.5 := by ring

theorem polyUp_outer : ‖deriv DerivCauchyBridge.polyOf dOuter‖ ≤ 8.86 := by
  have hre : |dOuter.re| ≤ (0.4 : ℝ) := by
    rw [dOuter_re]
    rw [abs_of_nonneg (by norm_num)]
    norm_num
  have him : |dOuter.im| ≤ (8.75 : ℝ) := by
    rw [dOuter_im]
    rw [abs_of_neg (by norm_num)]
    norm_num
  have h := poly_derivUp_of_abs dOuter 0.4 8.75 hre him
  norm_num at h ⊢
  linarith

theorem polyUp_leaf : ‖deriv DerivCauchyBridge.polyOf dLeaf‖ ≤ 7.06 := by
  have hre : |dLeaf.re| ≤ (0.2 : ℝ) := by
    rw [dLeaf_re]
    rw [abs_of_nonneg (by norm_num)]
  have him : |dLeaf.im| ≤ (6.75 : ℝ) := by
    rw [dLeaf_im]
    rw [abs_of_neg (by norm_num)]
    norm_num
  have h := poly_derivUp_of_abs dLeaf 0.2 6.75 hre him
  norm_num at h ⊢
  linarith

theorem polyUp_mid : ‖deriv DerivCauchyBridge.polyOf dMid‖ ≤ 4.86 := by
  have hre : |dMid.re| ≤ (0.4 : ℝ) := by
    rw [dMid_re]
    rw [abs_of_nonneg (by norm_num)]
    norm_num
  have him : |dMid.im| ≤ (4.75 : ℝ) := by
    rw [dMid_im]
    rw [abs_of_neg (by norm_num)]
    norm_num
  have h := poly_derivUp_of_abs dMid 0.4 4.75 hre him
  norm_num at h ⊢
  linarith

theorem polyUp_inner : ‖deriv DerivCauchyBridge.polyOf dInner‖ ≤ 0.86 := by
  have hre : |dInner.re| ≤ (0.4 : ℝ) := by
    rw [dInner_re]
    rw [abs_of_nonneg (by norm_num)]
    norm_num
  have him : |dInner.im| ≤ (0.75 : ℝ) := by
    rw [dInner_im]
    rw [abs_of_neg (by norm_num)]
    norm_num
  have h := poly_derivUp_of_abs dInner 0.4 0.75 hre him
  norm_num at h ⊢
  linarith

/-! Poly value majorants (triangle; feed Leibniz). -/

theorem polyValUp_of_norm (s : ℂ) (A B : ℝ)
    (hs : ‖s‖ ≤ A) (hs1 : ‖s - 1‖ ≤ B) :
    ‖DerivCauchyBridge.polyOf s‖ ≤ A * B / 2 := by
  have e1 : ‖DerivCauchyBridge.polyOf s‖ = ‖s * (s - 1)‖ / 2 := by
    unfold DerivCauchyBridge.polyOf
    rw [norm_div, Complex.norm_two]
  have em : ‖s * (s - 1)‖ ≤ A * B := by
    rw [norm_mul]
    exact mul_le_mul hs hs1 (norm_nonneg _) (by linarith [hs])
  rw [e1]
  linarith [em]

theorem polyVal_outer : ‖DerivCauchyBridge.polyOf dOuter‖ ≤ 42.83 := by
  have hs : ‖dOuter‖ ≤ (9.15 : ℝ) := by
    have h := Complex.norm_le_abs_re_add_abs_im dOuter
    rw [dOuter_re, dOuter_im] at h
    rw [abs_of_nonneg (by norm_num), abs_of_neg (by norm_num)] at h
    norm_num at h ⊢
    linarith
  have hs1 : ‖dOuter - 1‖ ≤ (9.36 : ℝ) := by
    have hre1 : (dOuter - 1).re = (-0.605 : ℝ) := by
      have e : (dOuter - 1).re = dOuter.re - 1 := Complex.sub_re dOuter 1
      rw [e, dOuter_re]
      norm_num
    have him1 : (dOuter - 1).im = (-8.75 : ℝ) := by
      have e : (dOuter - 1).im = dOuter.im := Complex.sub_im dOuter 1
      rw [e, dOuter_im]
    have h := Complex.norm_le_abs_re_add_abs_im (dOuter - 1)
    rw [hre1, him1] at h
    rw [abs_of_neg (by norm_num), abs_of_neg (by norm_num)] at h
    norm_num at h ⊢
    linarith
  have h := polyValUp_of_norm dOuter 9.15 9.36 hs hs1
  norm_num at h ⊢
  linarith

theorem polyVal_leaf : ‖DerivCauchyBridge.polyOf dLeaf‖ ≤ 26.24 := by
  have hs : ‖dLeaf‖ ≤ (6.95 : ℝ) := by
    have h := Complex.norm_le_abs_re_add_abs_im dLeaf
    rw [dLeaf_re, dLeaf_im] at h
    rw [abs_of_nonneg (by norm_num), abs_of_neg (by norm_num)] at h
    norm_num at h ⊢
    linarith
  have hs1 : ‖dLeaf - 1‖ ≤ (7.55 : ℝ) := by
    have hre1 : (dLeaf - 1).re = (-0.8 : ℝ) := by
      have e : (dLeaf - 1).re = dLeaf.re - 1 := Complex.sub_re dLeaf 1
      rw [e, dLeaf_re]
      norm_num
    have him1 : (dLeaf - 1).im = (-6.75 : ℝ) := by
      have e : (dLeaf - 1).im = dLeaf.im := Complex.sub_im dLeaf 1
      rw [e, dLeaf_im]
    have h := Complex.norm_le_abs_re_add_abs_im (dLeaf - 1)
    rw [hre1, him1] at h
    rw [abs_of_neg (by norm_num), abs_of_neg (by norm_num)] at h
    norm_num at h ⊢
    linarith
  have h := polyValUp_of_norm dLeaf 6.95 7.55 hs hs1
  norm_num at h ⊢
  linarith

theorem polyVal_mid : ‖DerivCauchyBridge.polyOf dMid‖ ≤ 13.81 := by
  have hs : ‖dMid‖ ≤ (5.15 : ℝ) := by
    have h := Complex.norm_le_abs_re_add_abs_im dMid
    rw [dMid_re, dMid_im] at h
    rw [abs_of_nonneg (by norm_num), abs_of_neg (by norm_num)] at h
    norm_num at h ⊢
    linarith
  have hs1 : ‖dMid - 1‖ ≤ (5.36 : ℝ) := by
    have hre1 : (dMid - 1).re = (-0.605 : ℝ) := by
      have e : (dMid - 1).re = dMid.re - 1 := Complex.sub_re dMid 1
      rw [e, dMid_re]
      norm_num
    have him1 : (dMid - 1).im = (-4.75 : ℝ) := by
      have e : (dMid - 1).im = dMid.im := Complex.sub_im dMid 1
      rw [e, dMid_im]
    have h := Complex.norm_le_abs_re_add_abs_im (dMid - 1)
    rw [hre1, him1] at h
    rw [abs_of_neg (by norm_num), abs_of_neg (by norm_num)] at h
    norm_num at h ⊢
    linarith
  have h := polyValUp_of_norm dMid 5.15 5.36 hs hs1
  norm_num at h ⊢
  linarith

theorem polyVal_inner : ‖DerivCauchyBridge.polyOf dInner‖ ≤ 0.79 := by
  have hs : ‖dInner‖ ≤ (1.15 : ℝ) := by
    have h := Complex.norm_le_abs_re_add_abs_im dInner
    rw [dInner_re, dInner_im] at h
    rw [abs_of_nonneg (by norm_num), abs_of_neg (by norm_num)] at h
    norm_num at h ⊢
    linarith
  have hs1 : ‖dInner - 1‖ ≤ (1.36 : ℝ) := by
    have hre1 : (dInner - 1).re = (-0.605 : ℝ) := by
      have e : (dInner - 1).re = dInner.re - 1 := Complex.sub_re dInner 1
      rw [e, dInner_re]
      norm_num
    have him1 : (dInner - 1).im = (-0.75 : ℝ) := by
      have e : (dInner - 1).im = dInner.im := Complex.sub_im dInner 1
      rw [e, dInner_im]
    have h := Complex.norm_le_abs_re_add_abs_im (dInner - 1)
    rw [hre1, him1] at h
    rw [abs_of_neg (by norm_num), abs_of_neg (by norm_num)] at h
    norm_num at h ⊢
    linarith
  have h := polyValUp_of_norm dInner 1.15 1.36 hs hs1
  norm_num at h ⊢
  linarith

/-! ## 4. Pi prime: log-derivative closed form plus banked pi uppers. -/

theorem logPi_norm_le : ‖Complex.log (Real.pi : ℂ)‖ ≤ (2.15 : ℝ) := by
  have hlogEq : Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) :=
    (Complex.ofReal_log (le_of_lt Real.pi_pos)).symm
  rw [hlogEq, Complex.norm_real, Real.norm_eq_abs]
  have hnn : 0 ≤ Real.log Real.pi := by
    apply Real.log_nonneg
    linarith [Real.pi_gt_three]
  rw [abs_of_nonneg hnn]
  have h1 : Real.log Real.pi ≤ Real.pi - 1 :=
    Real.log_le_sub_one_of_pos Real.pi_pos
  have h2 : Real.pi < 3.1416 := Real.pi_lt_d2
  norm_num at h1 h2 ⊢
  linarith

theorem piExp_hasDerivAt (s : ℂ) :
    HasDerivAt (fun t : ℂ => -((t : ℂ) / 2)) (-(1 / 2 : ℂ)) s := by
  have hid : HasDerivAt (fun t : ℂ => t) 1 s :=
    hasDerivAt_id' (x := s)
  have hdiv : HasDerivAt (fun t : ℂ => t / 2) (1 / 2) s :=
    hid.div_const (2 : ℂ)
  have hneg : HasDerivAt (-(fun t : ℂ => t / 2)) (-(1 / 2)) s :=
    hdiv.neg
  have heq : (-(fun t : ℂ => t / 2)) = (fun t : ℂ => -(t / 2)) := rfl
  rw [heq] at hneg
  exact hneg

theorem pi_hasDerivAt (s : ℂ) :
    HasDerivAt DerivCauchyBridge.piOf
      (DerivCauchyBridge.piOf s * Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))) s := by
  have hc0 : ((Real.pi : ℂ) ≠ 0) := by
    exact_mod_cast Real.pi_pos.ne'
  have hf : HasDerivAt (fun t : ℂ => -((t : ℂ) / 2)) (-(1 / 2 : ℂ)) s :=
    piExp_hasDerivAt s
  have h := hf.const_cpow (c := (Real.pi : ℂ)) (Or.inl hc0)
  have heqF : (fun t : ℂ => ((Real.pi : ℂ) ^ (-(t / 2)))) =
      DerivCauchyBridge.piOf := by
    unfold DerivCauchyBridge.piOf
    rfl
  rw [heqF] at h
  exact h

theorem pi_derivUp_of_upper (s : ℂ) (U : ℝ)
    (hU : ‖DerivCauchyBridge.piOf s‖ ≤ U) :
    ‖deriv DerivCauchyBridge.piOf s‖ ≤ U * 2.15 / 2 := by
  have hder : deriv DerivCauchyBridge.piOf s =
      DerivCauchyBridge.piOf s * Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) :=
    (pi_hasDerivAt s).deriv
  rw [hder]
  have e1 : ‖DerivCauchyBridge.piOf s * Complex.log (Real.pi : ℂ) *
      (-(1 / 2 : ℂ))‖ =
      ‖DerivCauchyBridge.piOf s‖ * ‖Complex.log (Real.pi : ℂ)‖ *
        ‖(-(1 / 2 : ℂ))‖ := by
    rw [norm_mul, norm_mul]
  rw [e1]
  have hn : ‖(-(1 / 2 : ℂ))‖ = (0.5 : ℝ) := by
    rw [norm_neg]
    have e2 : ((1 / 2 : ℂ)) = (1 : ℂ) / 2 := by norm_num
    rw [e2, norm_div, Complex.norm_one, Complex.norm_two]
    norm_num
  rw [hn]
  have hlog := logPi_norm_le
  have hnn1 : 0 ≤ ‖DerivCauchyBridge.piOf s‖ := norm_nonneg _
  have hnn2 : 0 ≤ ‖Complex.log (Real.pi : ℂ)‖ := norm_nonneg _
  have step1 : ‖DerivCauchyBridge.piOf s‖ * ‖Complex.log (Real.pi : ℂ)‖ ≤
      U * 2.15 :=
    mul_le_mul hU hlog hnn1 (by norm_num)
  have step2 : ‖DerivCauchyBridge.piOf s‖ * ‖Complex.log (Real.pi : ℂ)‖ * 0.5 ≤
      U * 2.15 * 0.5 :=
    mul_le_mul_of_nonneg_right step1 (by norm_num)
  have fin : U * 2.15 * 0.5 = U * 2.15 / 2 := by ring
  rw [fin] at step2
  exact step2

theorem piVal_outer : ‖DerivCauchyBridge.piOf dOuter‖ ≤ 1 :=
  Door3PremisePi.piOf_le_one_of_re_nonneg dOuter (by rw [dOuter_re]; norm_num)

theorem piVal_leaf : ‖DerivCauchyBridge.piOf dLeaf‖ ≤ 1 :=
  Door3PremisePi.piOf_le_one_of_re_nonneg dLeaf (by rw [dLeaf_re]; norm_num)

theorem piVal_mid : ‖DerivCauchyBridge.piOf dMid‖ ≤ 1 :=
  Door3PremisePi.piOf_le_one_of_re_nonneg dMid (by rw [dMid_re]; norm_num)

theorem piVal_inner : ‖DerivCauchyBridge.piOf dInner‖ ≤ 1 :=
  Door3PremisePi.piOf_le_one_of_re_nonneg dInner (by rw [dInner_re]; norm_num)

theorem piUp_outer : ‖deriv DerivCauchyBridge.piOf dOuter‖ ≤ 1.075 := by
  have h := pi_derivUp_of_upper dOuter 1 piVal_outer
  norm_num at h ⊢
  linarith

theorem piUp_leaf : ‖deriv DerivCauchyBridge.piOf dLeaf‖ ≤ 1.075 := by
  have h := pi_derivUp_of_upper dLeaf 1 piVal_leaf
  norm_num at h ⊢
  linarith

theorem piUp_mid : ‖deriv DerivCauchyBridge.piOf dMid‖ ≤ 1.075 := by
  have h := pi_derivUp_of_upper dMid 1 piVal_mid
  norm_num at h ⊢
  linarith

theorem piUp_inner : ‖deriv DerivCauchyBridge.piOf dInner‖ ≤ 1.075 := by
  have h := pi_derivUp_of_upper dInner 1 piVal_inner
  norm_num at h ⊢
  linarith

/-! ## 5. Gamma prime: Cauchy with uniform closed majorant; DERIV-GAP.

Option (i) from the brief (differentiate the shifted polynomial part exactly
and use a real-Gamma prime bound) is not available: no real-Gamma prime upper
is banked in the premise leaves. Option (ii) below uses rhoC = 0.01 with the
uniform closed majorant C = 600 from `premGamma_wide_of_mem` (since
`Real.exp` of a nonpositive number is at most one). C / rhoC = 60000 at every
center, far above every budget share. Option (iii): record DERIV-GAP.
-/

theorem gamma_wide_num (s : ℂ) (hlo : (0.01 : ℝ) ≤ s.re)
    (hhi : s.re ≤ (1.9 : ℝ)) :
    ‖DerivCauchyBridge.gammaOf s‖ ≤ 600 := by
  have h := Door3PremiseGamma.premGamma_wide_of_mem s hlo hhi
  have hexp : Real.exp (-(1 / 2) * |(s / 2).im|) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hnn : 0 ≤ |(s / 2).im| := abs_nonneg _
    have hle : -(1 / 2) * |(s / 2).im| ≤ 0 := by
      have h2 : (1 / 2 : ℝ) * |(s / 2).im| ≥ 0 := by
        apply mul_nonneg (by norm_num) hnn
      linarith
    exact hle
  have h600 : 600 * Real.exp (-(1 / 2) * |(s / 2).im|) ≤ 600 * 1 :=
    mul_le_mul_of_nonneg_left hexp (by norm_num)
  norm_num at h600 ⊢
  linarith [h, h600]

theorem gammaVal_outer_num : ‖DerivCauchyBridge.gammaOf dOuter‖ ≤ 600 :=
  gamma_wide_num dOuter (by rw [dOuter_re]; norm_num) (by rw [dOuter_re]; norm_num)

theorem gammaVal_leaf_num : ‖DerivCauchyBridge.gammaOf dLeaf‖ ≤ 600 :=
  gamma_wide_num dLeaf (by rw [dLeaf_re]; norm_num) (by rw [dLeaf_re]; norm_num)

theorem gammaVal_mid_num : ‖DerivCauchyBridge.gammaOf dMid‖ ≤ 600 :=
  gamma_wide_num dMid (by rw [dMid_re]; norm_num) (by rw [dMid_re]; norm_num)

theorem gammaVal_inner_num : ‖DerivCauchyBridge.gammaOf dInner‖ ≤ 600 :=
  gamma_wide_num dInner (by rw [dInner_re]; norm_num) (by rw [dInner_re]; norm_num)

theorem gammaDerivUp_of_sup (w : ℂ) (rho C : ℝ)
    (hr : 0 < rho)
    (hd : DiffContOnCl ℂ DerivCauchyBridge.gammaOf (Metric.ball w rho))
    (hC : ∀ z : ℂ, z ∈ Metric.sphere w rho → ‖DerivCauchyBridge.gammaOf z‖ ≤ C) :
    ‖deriv DerivCauchyBridge.gammaOf w‖ ≤ C / rho :=
  cauchy_derivUp_of_sphere DerivCauchyBridge.gammaOf w rho C hr hd hC

/-! Closed Cauchy instance shape with C = 600, rho = 0.01 (conditional only
on the `DiffContOnCl` side condition and the sphere majorant, both stated
explicitly; the sphere majorant follows from `gamma_wide_num` on the disc
once the disc stays in `Re in [0.01, 1.9]`, which holds for rho = 0.01 at
all four centers since their `Re` are 0.2-0.395). -/

theorem gammaGap_outer_shape (hd : DiffContOnCl ℂ DerivCauchyBridge.gammaOf
      (Metric.ball dOuter 0.01))
    (hC : ∀ z : ℂ, z ∈ Metric.sphere dOuter 0.01 →
      ‖DerivCauchyBridge.gammaOf z‖ ≤ 600) :
    ‖deriv DerivCauchyBridge.gammaOf dOuter‖ ≤ 600 / 0.01 :=
  gammaDerivUp_of_sup dOuter 0.01 600 (by norm_num) hd hC

theorem gammaGap_leaf_shape (hd : DiffContOnCl ℂ DerivCauchyBridge.gammaOf
      (Metric.ball dLeaf 0.01))
    (hC : ∀ z : ℂ, z ∈ Metric.sphere dLeaf 0.01 →
      ‖DerivCauchyBridge.gammaOf z‖ ≤ 600) :
    ‖deriv DerivCauchyBridge.gammaOf dLeaf‖ ≤ 600 / 0.01 :=
  gammaDerivUp_of_sup dLeaf 0.01 600 (by norm_num) hd hC

theorem gammaGap_mid_shape (hd : DiffContOnCl ℂ DerivCauchyBridge.gammaOf
      (Metric.ball dMid 0.01))
    (hC : ∀ z : ℂ, z ∈ Metric.sphere dMid 0.01 →
      ‖DerivCauchyBridge.gammaOf z‖ ≤ 600) :
    ‖deriv DerivCauchyBridge.gammaOf dMid‖ ≤ 600 / 0.01 :=
  gammaDerivUp_of_sup dMid 0.01 600 (by norm_num) hd hC

theorem gammaGap_inner_shape (hd : DiffContOnCl ℂ DerivCauchyBridge.gammaOf
      (Metric.ball dInner 0.01))
    (hC : ∀ z : ℂ, z ∈ Metric.sphere dInner 0.01 →
      ‖DerivCauchyBridge.gammaOf z‖ ≤ 600) :
    ‖deriv DerivCauchyBridge.gammaOf dInner‖ ≤ 600 / 0.01 :=
  gammaDerivUp_of_sup dInner 0.01 600 (by norm_num) hd hC

/-! Pure gap arithmetic: 600 / 0.01 exceeds every factor budget share. -/

theorem gamma_gap_number : (600 : ℝ) / 0.01 = 60000 := by norm_num

theorem gamma_gap_vs_outer : (0.02 : ℝ) < (600 : ℝ) / 0.01 := by norm_num

theorem gamma_gap_vs_leaf : (0.03 : ℝ) < (600 : ℝ) / 0.01 := by norm_num

theorem gamma_gap_vs_mid : (0.03 : ℝ) < (600 : ℝ) / 0.01 := by norm_num

theorem gamma_gap_vs_inner : (0.02 : ℝ) < (600 : ℝ) / 0.01 := by norm_num

/-! ## 6. Zeta prime: explicit premises (more than three lemmas would be
needed for Euler / FE pieces) plus conditional Cauchy. -/

def zetaValCap_outer : ℝ := 3

def zetaValCap_leaf : ℝ := 3

def zetaValCap_mid : ℝ := 3

def zetaValCap_inner : ℝ := 3

def zetaNeed_outer : Prop :=
  ∀ s : ℂ, s = dOuter → ‖riemannZeta s‖ ≤ zetaValCap_outer

def zetaNeed_leaf : Prop :=
  ∀ s : ℂ, s = dLeaf → ‖riemannZeta s‖ ≤ zetaValCap_leaf

def zetaNeed_mid : Prop :=
  ∀ s : ℂ, s = dMid → ‖riemannZeta s‖ ≤ zetaValCap_mid

def zetaNeed_inner : Prop :=
  ∀ s : ℂ, s = dInner → ‖riemannZeta s‖ ≤ zetaValCap_inner

def zetaSupOnSphere_outer : Prop :=
  ∀ z : ℂ, z ∈ Metric.sphere dOuter 0.01 → ‖riemannZeta z‖ ≤ 10

def zetaSupOnSphere_leaf : Prop :=
  ∀ z : ℂ, z ∈ Metric.sphere dLeaf 0.01 → ‖riemannZeta z‖ ≤ 10

def zetaSupOnSphere_mid : Prop :=
  ∀ z : ℂ, z ∈ Metric.sphere dMid 0.01 → ‖riemannZeta z‖ ≤ 10

def zetaSupOnSphere_inner : Prop :=
  ∀ z : ℂ, z ∈ Metric.sphere dInner 0.01 → ‖riemannZeta z‖ ≤ 10

def zetaDiffCont_outer : Prop :=
  DiffContOnCl ℂ riemannZeta (Metric.ball dOuter 0.01)

def zetaDiffCont_leaf : Prop :=
  DiffContOnCl ℂ riemannZeta (Metric.ball dLeaf 0.01)

def zetaDiffCont_mid : Prop :=
  DiffContOnCl ℂ riemannZeta (Metric.ball dMid 0.01)

def zetaDiffCont_inner : Prop :=
  DiffContOnCl ℂ riemannZeta (Metric.ball dInner 0.01)

theorem zetaDerivUp_of_sup (w : ℂ) (rho C : ℝ)
    (hr : 0 < rho)
    (hd : DiffContOnCl ℂ riemannZeta (Metric.ball w rho))
    (hC : ∀ z : ℂ, z ∈ Metric.sphere w rho → ‖riemannZeta z‖ ≤ C) :
    ‖deriv riemannZeta w‖ ≤ C / rho :=
  cauchy_derivUp_of_sphere riemannZeta w rho C hr hd hC

theorem zetaDeriv_outer_of_premise
    (hd : zetaDiffCont_outer) (hC : zetaSupOnSphere_outer) :
    ‖deriv riemannZeta dOuter‖ ≤ 10 / 0.01 := by
  unfold zetaDiffCont_outer at hd
  unfold zetaSupOnSphere_outer at hC
  exact zetaDerivUp_of_sup dOuter 0.01 10 (by norm_num) hd hC

theorem zetaDeriv_leaf_of_premise
    (hd : zetaDiffCont_leaf) (hC : zetaSupOnSphere_leaf) :
    ‖deriv riemannZeta dLeaf‖ ≤ 10 / 0.01 := by
  unfold zetaDiffCont_leaf at hd
  unfold zetaSupOnSphere_leaf at hC
  exact zetaDerivUp_of_sup dLeaf 0.01 10 (by norm_num) hd hC

theorem zetaDeriv_mid_of_premise
    (hd : zetaDiffCont_mid) (hC : zetaSupOnSphere_mid) :
    ‖deriv riemannZeta dMid‖ ≤ 10 / 0.01 := by
  unfold zetaDiffCont_mid at hd
  unfold zetaSupOnSphere_mid at hC
  exact zetaDerivUp_of_sup dMid 0.01 10 (by norm_num) hd hC

theorem zetaDeriv_inner_of_premise
    (hd : zetaDiffCont_inner) (hC : zetaSupOnSphere_inner) :
    ‖deriv riemannZeta dInner‖ ≤ 10 / 0.01 := by
  unfold zetaDiffCont_inner at hd
  unfold zetaSupOnSphere_inner at hC
  exact zetaDerivUp_of_sup dInner 0.01 10 (by norm_num) hd hC

theorem zeta_gap_number : (10 : ℝ) / 0.01 = 1000 := by norm_num

/-! ## 7. Tight TRUE-scale value premises for gamma (needed for Leibniz).
Wide 600 is closed above but useless for the product; the tight caps below
are explicit premises with TRUE-scale numerals (outer TRUE about 0.0016,
leaf about 0.0077, mid about 0.03, inner about 4.4). -/

def tightGamma_outer : ℝ := 0.002

def tightGamma_leaf : ℝ := 0.008

def tightGamma_mid : ℝ := 0.04

def tightGamma_inner : ℝ := 4.5

def tightGammaNeed_outer : Prop :=
  ‖DerivCauchyBridge.gammaOf dOuter‖ ≤ tightGamma_outer

def tightGammaNeed_leaf : Prop :=
  ‖DerivCauchyBridge.gammaOf dLeaf‖ ≤ tightGamma_leaf

def tightGammaNeed_mid : Prop :=
  ‖DerivCauchyBridge.gammaOf dMid‖ ≤ tightGamma_mid

def tightGammaNeed_inner : Prop :=
  ‖DerivCauchyBridge.gammaOf dInner‖ ≤ tightGamma_inner

/-! ## 8. Four-factor Leibniz norm bound (closed, conditional). -/

theorem leibniz4_norm (P Pi G Z : ℂ → ℂ) (s : ℂ)
    (dP dPi dG dZ : ℂ)
    (vP vPi vG vZ nP nPi nG nZ : ℝ)
    (hP : HasDerivAt P dP s)
    (hPi : HasDerivAt Pi dPi s)
    (hG : HasDerivAt G dG s)
    (hZ : HasDerivAt Z dZ s)
    (hvP : ‖P s‖ ≤ vP) (hvPi : ‖Pi s‖ ≤ vPi)
    (hvG : ‖G s‖ ≤ vG) (hvZ : ‖Z s‖ ≤ vZ)
    (hdP : ‖dP‖ ≤ nP) (hdPi : ‖dPi‖ ≤ nPi)
    (hdG : ‖dG‖ ≤ nG) (hdZ : ‖dZ‖ ≤ nZ)
    (hpP : 0 ≤ vP) (hpPi : 0 ≤ vPi) (hpG : 0 ≤ vG) (hpZ : 0 ≤ vZ)
    (hqP : 0 ≤ nP) (hqPi : 0 ≤ nPi) (hqG : 0 ≤ nG) (hqZ : 0 ≤ nZ) :
    ‖deriv (fun t : ℂ => P t * Pi t * G t * Z t) s‖ ≤
      nP * vPi * vG * vZ + vP * nPi * vG * vZ +
        vP * vPi * nG * vZ + vP * vPi * vG * nZ := by
  have hPPi : HasDerivAt (fun t : ℂ => P t * Pi t) (dP * Pi s + P s * dPi) s :=
    hP.mul hPi
  have hPPiG : HasDerivAt (fun t : ℂ => (P t * Pi t) * G t)
      ((dP * Pi s + P s * dPi) * G s + (P s * Pi s) * dG) s :=
    hPPi.mul hG
  have hAll : HasDerivAt (fun t : ℂ => ((P t * Pi t) * G t) * Z t)
      (((dP * Pi s + P s * dPi) * G s + (P s * Pi s) * dG) * Z s +
        ((P s * Pi s) * G s) * dZ) s :=
    hPPiG.mul hZ
  have heqF : (fun t : ℂ => ((P t * Pi t) * G t) * Z t) =
      (fun t : ℂ => P t * Pi t * G t * Z t) := by
    rfl
  rw [heqF] at hAll
  have hder : deriv (fun t : ℂ => P t * Pi t * G t * Z t) s =
      (((dP * Pi s + P s * dPi) * G s + (P s * Pi s) * dG) * Z s +
        ((P s * Pi s) * G s) * dZ) :=
    hAll.deriv
  rw [hder]
  have t1 : ‖(dP * Pi s + P s * dPi) * G s‖ ≤
      (nP * vPi + vP * nPi) * vG := by
    have a1 : ‖dP * Pi s‖ ≤ nP * vPi := by
      rw [norm_mul]
      exact mul_le_mul hdP hvPi (norm_nonneg _) hqP
    have a2 : ‖P s * dPi‖ ≤ vP * nPi := by
      rw [norm_mul]
      exact mul_le_mul hvP hdPi (norm_nonneg _) hpP
    have a3 : ‖dP * Pi s + P s * dPi‖ ≤ nP * vPi + vP * nPi := by
      calc ‖dP * Pi s + P s * dPi‖ ≤ ‖dP * Pi s‖ + ‖P s * dPi‖ :=
            norm_add_le _ _
        _ ≤ nP * vPi + vP * nPi := add_le_add a1 a2
    rw [norm_mul]
    exact mul_le_mul a3 hvG (norm_nonneg _) (by linarith [hqP, hqPi, hpP, hpPi])
  have t2 : ‖(P s * Pi s) * dG‖ ≤ vP * vPi * nG := by
    have b1 : ‖P s * Pi s‖ ≤ vP * vPi := by
      rw [norm_mul]
      exact mul_le_mul hvP hvPi (norm_nonneg _) hpP
    rw [norm_mul]
    exact mul_le_mul b1 hdG (norm_nonneg _) (by linarith [hpP, hpPi])
  have t12 : ‖(dP * Pi s + P s * dPi) * G s + (P s * Pi s) * dG‖ ≤
      (nP * vPi + vP * nPi) * vG + vP * vPi * nG :=
    add_le_add t1 t2
  have u1 : ‖((dP * Pi s + P s * dPi) * G s + (P s * Pi s) * dG) * Z s‖ ≤
      ((nP * vPi + vP * nPi) * vG + vP * vPi * nG) * vZ := by
    rw [norm_mul]
    exact mul_le_mul t12 hvZ (norm_nonneg _)
      (by linarith [hqP, hqPi, hqG, hpP, hpPi, hpG])
  have u2 : ‖((P s * Pi s) * G s) * dZ‖ ≤ vP * vPi * vG * nZ := by
    have c1 : ‖P s * Pi s‖ ≤ vP * vPi := by
      rw [norm_mul]
      exact mul_le_mul hvP hvPi (norm_nonneg _) hpP
    have c2 : ‖(P s * Pi s) * G s‖ ≤ vP * vPi * vG := by
      rw [norm_mul]
      exact mul_le_mul c1 hvG (norm_nonneg _) (by linarith [hpP, hpPi])
    rw [norm_mul]
    exact mul_le_mul c2 hdZ (norm_nonneg _) (by linarith [hpP, hpPi, hpG])
  have fin : ‖((dP * Pi s + P s * dPi) * G s + (P s * Pi s) * dG) * Z s +
        ((P s * Pi s) * G s) * dZ‖ ≤
      ((nP * vPi + vP * nPi) * vG + vP * vPi * nG) * vZ +
        vP * vPi * vG * nZ :=
    add_le_add u1 u2
  have alg : ((nP * vPi + vP * nPi) * vG + vP * vPi * nG) * vZ +
      vP * vPi * vG * nZ =
      nP * vPi * vG * vZ + vP * nPi * vG * vZ +
        vP * vPi * nG * vZ + vP * vPi * vG * nZ := by
    ring
  rw [alg] at fin
  exact fin

/-! ## 9. Per-group assembly: conditional total plus GAP arithmetic.

Each `derivUp_GROUP_cond` is closed conditionally on tight gamma values,
zeta values, and gamma / zeta derivative caps. The following `gap`
theorems plug the closed Cauchy numbers (60000 for gamma prime,
1000 for zeta prime) and show the total exceeds M prime.
-/

theorem derivUp_outer_cond
    (dG dZ : ℂ) (vG vZ nG nZ : ℝ)
    (hG : HasDerivAt DerivCauchyBridge.gammaOf dG dOuter)
    (hZ : HasDerivAt riemannZeta dZ dOuter)
    (hvG : ‖DerivCauchyBridge.gammaOf dOuter‖ ≤ vG)
    (hvZ : ‖riemannZeta dOuter‖ ≤ vZ)
    (hdG : ‖dG‖ ≤ nG) (hdZ : ‖dZ‖ ≤ nZ)
    (hpG : 0 ≤ vG) (hpZ : 0 ≤ vZ) (hqG : 0 ≤ nG) (hqZ : 0 ≤ nZ) :
    ‖deriv (fun t : ℂ => DerivCauchyBridge.polyOf t *
      DerivCauchyBridge.piOf t * DerivCauchyBridge.gammaOf t *
      riemannZeta t) dOuter‖ ≤
      8.86 * 1 * vG * vZ + 42.83 * 1.075 * vG * vZ +
        42.83 * 1 * nG * vZ + 42.83 * 1 * vG * nZ := by
  have hP := poly_hasDerivAt dOuter
  have hPi := pi_hasDerivAt dOuter
  have hPv : ‖DerivCauchyBridge.polyOf dOuter‖ ≤ 42.83 := polyVal_outer
  have hPiv : ‖DerivCauchyBridge.piOf dOuter‖ ≤ 1 := piVal_outer
  have hPd : ‖dOuter - 1 / 2‖ ≤ 8.86 := polyUp_outer
  have hPid : ‖DerivCauchyBridge.piOf dOuter *
      Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))‖ ≤ 1.075 := piUp_outer
  have hderP : deriv DerivCauchyBridge.polyOf dOuter = dOuter - 1 / 2 :=
    poly_deriv_eq dOuter
  have hderPi : deriv DerivCauchyBridge.piOf dOuter =
      DerivCauchyBridge.piOf dOuter * Complex.log (Real.pi : ℂ) *
        (-(1 / 2 : ℂ)) :=
    (pi_hasDerivAt dOuter).deriv
  have hP' : HasDerivAt DerivCauchyBridge.polyOf (dOuter - 1 / 2) dOuter :=
    poly_hasDerivAt dOuter
  have hPi' : HasDerivAt DerivCauchyBridge.piOf
      (DerivCauchyBridge.piOf dOuter * Complex.log (Real.pi : ℂ) *
        (-(1 / 2 : ℂ))) dOuter :=
    pi_hasDerivAt dOuter
  have h := leibniz4_norm DerivCauchyBridge.polyOf DerivCauchyBridge.piOf
    DerivCauchyBridge.gammaOf riemannZeta dOuter
    (dOuter - 1 / 2)
    (DerivCauchyBridge.piOf dOuter * Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)))
    dG dZ 42.83 1 vG vZ 8.86 1.075 nG nZ
    hP' hPi' hG hZ hPv hPiv hvG hvZ hPd hPid hdG hdZ
    (by norm_num) (by norm_num) hpG hpZ
    (by norm_num) (by norm_num) hqG hqZ
  exact h

theorem derivUp_leaf_cond
    (dG dZ : ℂ) (vG vZ nG nZ : ℝ)
    (hG : HasDerivAt DerivCauchyBridge.gammaOf dG dLeaf)
    (hZ : HasDerivAt riemannZeta dZ dLeaf)
    (hvG : ‖DerivCauchyBridge.gammaOf dLeaf‖ ≤ vG)
    (hvZ : ‖riemannZeta dLeaf‖ ≤ vZ)
    (hdG : ‖dG‖ ≤ nG) (hdZ : ‖dZ‖ ≤ nZ)
    (hpG : 0 ≤ vG) (hpZ : 0 ≤ vZ) (hqG : 0 ≤ nG) (hqZ : 0 ≤ nZ) :
    ‖deriv (fun t : ℂ => DerivCauchyBridge.polyOf t *
      DerivCauchyBridge.piOf t * DerivCauchyBridge.gammaOf t *
      riemannZeta t) dLeaf‖ ≤
      7.06 * 1 * vG * vZ + 26.24 * 1.075 * vG * vZ +
        26.24 * 1 * nG * vZ + 26.24 * 1 * vG * nZ := by
  have hP' : HasDerivAt DerivCauchyBridge.polyOf (dLeaf - 1 / 2) dLeaf :=
    poly_hasDerivAt dLeaf
  have hPi' : HasDerivAt DerivCauchyBridge.piOf
      (DerivCauchyBridge.piOf dLeaf * Complex.log (Real.pi : ℂ) *
        (-(1 / 2 : ℂ))) dLeaf :=
    pi_hasDerivAt dLeaf
  have h := leibniz4_norm DerivCauchyBridge.polyOf DerivCauchyBridge.piOf
    DerivCauchyBridge.gammaOf riemannZeta dLeaf
    (dLeaf - 1 / 2)
    (DerivCauchyBridge.piOf dLeaf * Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)))
    dG dZ 26.24 1 vG vZ 7.06 1.075 nG nZ
    hP' hPi' hG hZ polyVal_leaf piVal_leaf hvG hvZ
    polyUp_leaf piUp_leaf hdG hdZ
    (by norm_num) (by norm_num) hpG hpZ
    (by norm_num) (by norm_num) hqG hqZ
  exact h

theorem derivUp_mid_cond
    (dG dZ : ℂ) (vG vZ nG nZ : ℝ)
    (hG : HasDerivAt DerivCauchyBridge.gammaOf dG dMid)
    (hZ : HasDerivAt riemannZeta dZ dMid)
    (hvG : ‖DerivCauchyBridge.gammaOf dMid‖ ≤ vG)
    (hvZ : ‖riemannZeta dMid‖ ≤ vZ)
    (hdG : ‖dG‖ ≤ nG) (hdZ : ‖dZ‖ ≤ nZ)
    (hpG : 0 ≤ vG) (hpZ : 0 ≤ vZ) (hqG : 0 ≤ nG) (hqZ : 0 ≤ nZ) :
    ‖deriv (fun t : ℂ => DerivCauchyBridge.polyOf t *
      DerivCauchyBridge.piOf t * DerivCauchyBridge.gammaOf t *
      riemannZeta t) dMid‖ ≤
      4.86 * 1 * vG * vZ + 13.81 * 1.075 * vG * vZ +
        13.81 * 1 * nG * vZ + 13.81 * 1 * vG * nZ := by
  have hP' : HasDerivAt DerivCauchyBridge.polyOf (dMid - 1 / 2) dMid :=
    poly_hasDerivAt dMid
  have hPi' : HasDerivAt DerivCauchyBridge.piOf
      (DerivCauchyBridge.piOf dMid * Complex.log (Real.pi : ℂ) *
        (-(1 / 2 : ℂ))) dMid :=
    pi_hasDerivAt dMid
  have h := leibniz4_norm DerivCauchyBridge.polyOf DerivCauchyBridge.piOf
    DerivCauchyBridge.gammaOf riemannZeta dMid
    (dMid - 1 / 2)
    (DerivCauchyBridge.piOf dMid * Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)))
    dG dZ 13.81 1 vG vZ 4.86 1.075 nG nZ
    hP' hPi' hG hZ polyVal_mid piVal_mid hvG hvZ
    polyUp_mid piUp_mid hdG hdZ
    (by norm_num) (by norm_num) hpG hpZ
    (by norm_num) (by norm_num) hqG hqZ
  exact h

theorem derivUp_inner_cond
    (dG dZ : ℂ) (vG vZ nG nZ : ℝ)
    (hG : HasDerivAt DerivCauchyBridge.gammaOf dG dInner)
    (hZ : HasDerivAt riemannZeta dZ dInner)
    (hvG : ‖DerivCauchyBridge.gammaOf dInner‖ ≤ vG)
    (hvZ : ‖riemannZeta dInner‖ ≤ vZ)
    (hdG : ‖dG‖ ≤ nG) (hdZ : ‖dZ‖ ≤ nZ)
    (hpG : 0 ≤ vG) (hpZ : 0 ≤ vZ) (hqG : 0 ≤ nG) (hqZ : 0 ≤ nZ) :
    ‖deriv (fun t : ℂ => DerivCauchyBridge.polyOf t *
      DerivCauchyBridge.piOf t * DerivCauchyBridge.gammaOf t *
      riemannZeta t) dInner‖ ≤
      0.86 * 1 * vG * vZ + 0.79 * 1.075 * vG * vZ +
        0.79 * 1 * nG * vZ + 0.79 * 1 * vG * nZ := by
  have hP' : HasDerivAt DerivCauchyBridge.polyOf (dInner - 1 / 2) dInner :=
    poly_hasDerivAt dInner
  have hPi' : HasDerivAt DerivCauchyBridge.piOf
      (DerivCauchyBridge.piOf dInner * Complex.log (Real.pi : ℂ) *
        (-(1 / 2 : ℂ))) dInner :=
    pi_hasDerivAt dInner
  have h := leibniz4_norm DerivCauchyBridge.polyOf DerivCauchyBridge.piOf
    DerivCauchyBridge.gammaOf riemannZeta dInner
    (dInner - 1 / 2)
    (DerivCauchyBridge.piOf dInner * Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)))
    dG dZ 0.79 1 vG vZ 0.86 1.075 nG nZ
    hP' hPi' hG hZ polyVal_inner piVal_inner hvG hvZ
    polyUp_inner piUp_inner hdG hdZ
    (by norm_num) (by norm_num) hpG hpZ
    (by norm_num) (by norm_num) hqG hqZ
  exact h

/-! GAP totals with closed Cauchy numbers and tight TRUE-scale values.
Even the poly + pi partial sums are shown alongside; the gamma-prime term
alone exceeds M prime by orders of magnitude, and the zeta-prime term adds
a second independent excess. -/

theorem gap_outer_total :
    (0.11 : ℝ) <
      8.86 * 1 * 0.002 * 3 + 42.83 * 1.075 * 0.002 * 3 +
        42.83 * 1 * (600 / 0.01) * 3 + 42.83 * 1 * 0.002 * (10 / 0.01) := by
  norm_num

theorem gap_leaf_total :
    (0.15 : ℝ) <
      7.06 * 1 * 0.008 * 3 + 26.24 * 1.075 * 0.008 * 3 +
        26.24 * 1 * (600 / 0.01) * 3 + 26.24 * 1 * 0.008 * (10 / 0.01) := by
  norm_num

theorem gap_mid_total :
    (0.15 : ℝ) <
      4.86 * 1 * 0.04 * 3 + 13.81 * 1.075 * 0.04 * 3 +
        13.81 * 1 * (600 / 0.01) * 3 + 13.81 * 1 * 0.04 * (10 / 0.01) := by
  norm_num

theorem gap_inner_total :
    (0.09 : ℝ) <
      0.86 * 1 * 4.5 * 3 + 0.79 * 1.075 * 4.5 * 3 +
        0.79 * 1 * (600 / 0.01) * 3 + 0.79 * 1 * 4.5 * (10 / 0.01) := by
  norm_num

theorem gap_outer_gamma_alone :
    (0.11 : ℝ) < 42.83 * 1 * (600 / 0.01) * 3 := by
  norm_num

theorem gap_leaf_gamma_alone :
    (0.15 : ℝ) < 26.24 * 1 * (600 / 0.01) * 3 := by
  norm_num

theorem gap_mid_gamma_alone :
    (0.15 : ℝ) < 13.81 * 1 * (600 / 0.01) * 3 := by
  norm_num

theorem gap_inner_gamma_alone :
    (0.09 : ℝ) < 0.79 * 1 * (600 / 0.01) * 3 := by
  norm_num

/-! Poly + pi partial sums with tight values (for the record; outer partial
already exceeds 0.11 at zeta cap 3, leaf / mid / inner partials shown with
the same caps). -/

theorem partial_outer_poly_pi :
    8.86 * 1 * 0.002 * 3 + 42.83 * 1.075 * 0.002 * 3 < (0.33 : ℝ) := by
  norm_num

theorem partial_leaf_poly_pi :
    7.06 * 1 * 0.008 * 3 + 26.24 * 1.075 * 0.008 * 3 < (0.85 : ℝ) := by
  norm_num

theorem partial_mid_poly_pi :
    4.86 * 1 * 0.04 * 3 + 13.81 * 1.075 * 0.04 * 3 < (2.37 : ℝ) := by
  norm_num

theorem partial_inner_poly_pi :
    0.86 * 1 * 4.5 * 3 + 0.79 * 1.075 * 4.5 * 3 < (23.06 : ℝ) := by
  norm_num

/-! ## 10. MID sphere at honest tail-quarter 125 (dMid = 0.395 - 4.75 I).

Geometry check (margins honest, no force):
* `dMid.re = 0.395`, radius `0.01` gives `z.re ∈ [0.385, 0.405]` on the
  sphere, inside tail-quarter `[1/4, 1/2]` with margins `0.135` below
  (`0.385 - 0.25`) and `0.095` above (`0.5 - 0.405`).
* `dMid.im = -4.75`, radius `0.01` gives `z.im ∈ [-4.76, -4.74]`, so
  `|z.im| ≤ 4.76 ≤ 11` with margin `6.24`.
* Tail-quarter domain (`door3_tail_eta_upper.lean:167-170`):
  `1/4 ≤ s.re`, `s.re ≤ 1/2`, `|s.im| ≤ 11` gives `‖riemannZeta s‖ ≤ 125`.
  Hence the whole `0.01`-sphere over `dMid` is covered at `125`, NOT `10`.
  The pre-existing `zetaSupOnSphere_mid` (`≤ 10`) is left untouched and
  NOT claimed here; the filled instance below is restated at `125` only.
  `dMid` is above the R02-disc `Im ∈ [-8.25, -5.25]` strip, so no R02-disc
  numeral is used. -/

def zetaSupOnSphere_mid_125 : Prop :=
  ∀ z : ℂ, z ∈ Metric.sphere dMid 0.01 → ‖riemannZeta z‖ ≤ 125

theorem dMid_sphere_re_bounds {z : ℂ}
    (hz : z ∈ Metric.sphere dMid 0.01) :
    (1 / 4 : ℝ) ≤ z.re ∧ z.re ≤ (1 / 2 : ℝ) := by
  have hdist : dist z dMid = (0.01 : ℝ) := Metric.mem_sphere.mp hz
  have hnorm : ‖z - dMid‖ = (0.01 : ℝ) := by rwa [dist_eq_norm] at hdist
  have hre : |(z - dMid).re| ≤ (0.01 : ℝ) := by
    calc |(z - dMid).re| ≤ ‖z - dMid‖ := Complex.abs_re_le_norm _
      _ = 0.01 := hnorm
  have here : (z - dMid).re = z.re - 0.395 := by
    have e : (z - dMid).re = z.re - dMid.re := Complex.sub_re z dMid
    rw [e, dMid_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

theorem dMid_sphere_im_bound {z : ℂ}
    (hz : z ∈ Metric.sphere dMid 0.01) :
    |z.im| ≤ (11 : ℝ) := by
  have hdist : dist z dMid = (0.01 : ℝ) := Metric.mem_sphere.mp hz
  have hnorm : ‖z - dMid‖ = (0.01 : ℝ) := by rwa [dist_eq_norm] at hdist
  have him : |(z - dMid).im| ≤ (0.01 : ℝ) := by
    calc |(z - dMid).im| ≤ ‖z - dMid‖ := Complex.abs_im_le_norm _
      _ = 0.01 := hnorm
  have heim : (z - dMid).im = z.im - (-4.75) := by
    have e : (z - dMid).im = z.im - dMid.im := Complex.sub_im z dMid
    rw [e, dMid_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  have himlo : (-4.76 : ℝ) ≤ z.im := by linarith
  have himhi : z.im ≤ (-4.74 : ℝ) := by linarith
  rw [abs_le]
  constructor <;> linarith

theorem zetaSupOnSphere_mid_125_filled :
    ∀ z : ℂ, z ∈ Metric.sphere dMid 0.01 → ‖riemannZeta z‖ ≤ 125 := by
  intro z hz
  obtain ⟨hre_lo, hre_hi⟩ := dMid_sphere_re_bounds hz
  have him := dMid_sphere_im_bound hz
  exact Door3TailEtaUpper.zeta_upper_tail_quarter hre_lo hre_hi him

theorem zetaSup_mid_125_banked : zetaSupOnSphere_mid_125 :=
  zetaSupOnSphere_mid_125_filled

theorem zetaDeriv_mid_125_of_diffCont
    (hd : zetaDiffCont_mid) :
    ‖deriv riemannZeta dMid‖ ≤ 125 / 0.01 := by
  unfold zetaDiffCont_mid at hd
  exact zetaDerivUp_of_sup dMid 0.01 125 (by norm_num) hd
    zetaSupOnSphere_mid_125_filled

theorem zeta_mid_125_number : (125 : ℝ) / 0.01 = 12500 := by norm_num

/-! ## 10b. MID DiffContOnCl on the 0.01-ball (pole avoided).

Path: `differentiableAt_riemannZeta` (off pole) at each point of the
closed ball, assembled to `DifferentiableOn` via
`DifferentiableAt.differentiableWithinAt`, then
`DifferentiableOn.diffContOnCl` after `Metric.closure_ball`.
Pole avoidance: `dMid.re = 0.395`, radius `0.01`, so every
`z ∈ closedBall dMid 0.01` has `z.re ≤ 0.405 < 1`, hence `z ≠ 1`.
`1 ∉ ball` since `‖(1 : ℂ) - dMid‖ ≥ 1 - 0.405 > 0.01` on the real part. -/

theorem dMid_closedBall_re_upper {z : ℂ}
    (hz : z ∈ Metric.closedBall dMid 0.01) :
    z.re ≤ (0.405 : ℝ) := by
  have hdist : dist z dMid ≤ (0.01 : ℝ) := Metric.mem_closedBall.mp hz
  have hnorm : ‖z - dMid‖ ≤ (0.01 : ℝ) := by rwa [dist_eq_norm] at hdist
  have hre : |(z - dMid).re| ≤ (0.01 : ℝ) := by
    calc |(z - dMid).re| ≤ ‖z - dMid‖ := Complex.abs_re_le_norm _
      _ ≤ 0.01 := hnorm
  have here : (z - dMid).re = z.re - 0.395 := by
    have e : (z - dMid).re = z.re - dMid.re := Complex.sub_re z dMid
    rw [e, dMid_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  linarith

theorem zetaDiffCont_mid_filled :
    DiffContOnCl ℂ riemannZeta (Metric.ball dMid 0.01) := by
  apply DifferentiableOn.diffContOnCl
  rw [Metric.closure_ball dMid (by norm_num : (0.01 : ℝ) ≠ 0)]
  intro z hz
  apply (differentiableAt_riemannZeta ?_).differentiableWithinAt
  intro hcon
  have hle := dMid_closedBall_re_upper hz
  have e : z.re = 1 := by
    rw [hcon]
    exact Complex.one_re
  linarith

theorem zetaDiffCont_mid_banked : zetaDiffCont_mid :=
  zetaDiffCont_mid_filled

theorem zetaDeriv_mid_125_closed :
    ‖deriv riemannZeta dMid‖ ≤ 12500 := by
  have h := zetaDeriv_mid_125_of_diffCont zetaDiffCont_mid_banked
  rw [zeta_mid_125_number] at h
  exact h

/-! ## 11. INNER sphere at honest tail-quarter 125 (dInner = 0.395 - 0.75 I).

Geometry check (margins honest, no force):
* `dInner.re = 0.395`, radius `0.01` gives `z.re ∈ [0.385, 0.405]` on the
  sphere, inside tail-quarter `[1/4, 1/2]` with margins `0.135` below
  (`0.385 - 0.25`) and `0.095` above (`0.5 - 0.405`).
* `dInner.im = -0.75`, radius `0.01` gives `z.im ∈ [-0.76, -0.74]`, so
  `|z.im| ≤ 0.76 ≤ 11` with margin `10.24`.
* Tail-quarter domain (`door3_tail_eta_upper.lean:167-170`):
  `1/4 ≤ s.re`, `s.re ≤ 1/2`, `|s.im| ≤ 11` gives `‖riemannZeta s‖ ≤ 125`.
  Hence the whole `0.01`-sphere over `dInner` is covered at `125`, NOT `10`.
  The pre-existing `zetaSupOnSphere_inner` (`≤ 10`) is left untouched and
  NOT claimed here; the filled instance below is restated at `125` only.
* R02-disc numeral 934 (`zeta_rigorous.lean:32566-32568`):
  `Re ∈ [0.05, 0.74]`, `Im ∈ [-8.25, -5.25]` gives `‖riemannZeta s‖ ≤ 934`.
  `dInner.im = -0.75` lies outside `[-8.25, -5.25]` (above by `4.5`), so the
  R02-disc numeral is inapplicable here; only tail-quarter 125 is used. -/

def zetaSupOnSphere_inner_125 : Prop :=
  ∀ z : ℂ, z ∈ Metric.sphere dInner 0.01 → ‖riemannZeta z‖ ≤ 125

theorem dInner_sphere_re_bounds {z : ℂ}
    (hz : z ∈ Metric.sphere dInner 0.01) :
    (1 / 4 : ℝ) ≤ z.re ∧ z.re ≤ (1 / 2 : ℝ) := by
  have hdist : dist z dInner = (0.01 : ℝ) := Metric.mem_sphere.mp hz
  have hnorm : ‖z - dInner‖ = (0.01 : ℝ) := by rwa [dist_eq_norm] at hdist
  have hre : |(z - dInner).re| ≤ (0.01 : ℝ) := by
    calc |(z - dInner).re| ≤ ‖z - dInner‖ := Complex.abs_re_le_norm _
      _ = 0.01 := hnorm
  have here : (z - dInner).re = z.re - 0.395 := by
    have e : (z - dInner).re = z.re - dInner.re := Complex.sub_re z dInner
    rw [e, dInner_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

theorem dInner_sphere_im_bound {z : ℂ}
    (hz : z ∈ Metric.sphere dInner 0.01) :
    |z.im| ≤ (11 : ℝ) := by
  have hdist : dist z dInner = (0.01 : ℝ) := Metric.mem_sphere.mp hz
  have hnorm : ‖z - dInner‖ = (0.01 : ℝ) := by rwa [dist_eq_norm] at hdist
  have him : |(z - dInner).im| ≤ (0.01 : ℝ) := by
    calc |(z - dInner).im| ≤ ‖z - dInner‖ := Complex.abs_im_le_norm _
      _ = 0.01 := hnorm
  have heim : (z - dInner).im = z.im - (-0.75) := by
    have e : (z - dInner).im = z.im - dInner.im := Complex.sub_im z dInner
    rw [e, dInner_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  have himlo : (-0.76 : ℝ) ≤ z.im := by linarith
  have himhi : z.im ≤ (-0.74 : ℝ) := by linarith
  rw [abs_le]
  constructor <;> linarith

theorem zetaSupOnSphere_inner_125_filled :
    ∀ z : ℂ, z ∈ Metric.sphere dInner 0.01 → ‖riemannZeta z‖ ≤ 125 := by
  intro z hz
  obtain ⟨hre_lo, hre_hi⟩ := dInner_sphere_re_bounds hz
  have him := dInner_sphere_im_bound hz
  exact Door3TailEtaUpper.zeta_upper_tail_quarter hre_lo hre_hi him

theorem zetaSup_inner_125_banked : zetaSupOnSphere_inner_125 :=
  zetaSupOnSphere_inner_125_filled

theorem zetaDeriv_inner_125_of_diffCont
    (hd : zetaDiffCont_inner) :
    ‖deriv riemannZeta dInner‖ ≤ 125 / 0.01 := by
  unfold zetaDiffCont_inner at hd
  exact zetaDerivUp_of_sup dInner 0.01 125 (by norm_num) hd
    zetaSupOnSphere_inner_125_filled

theorem zeta_inner_125_number : (125 : ℝ) / 0.01 = 12500 := by norm_num

/-! ## 11b. INNER DiffContOnCl on the 0.01-ball (pole avoided).

Mirror of MID (`dMid_closedBall_re_upper :1059` + `zetaDiffCont_mid_filled :1074` +
`zetaDiffCont_mid_banked :1087`): `dInner.re = 0.395`, radius `0.01`, so every
`z ∈ closedBall dInner 0.01` has `z.re ≤ 0.405 < 1`, hence `z ≠ 1`. -/

theorem dInner_closedBall_re_upper {z : ℂ}
    (hz : z ∈ Metric.closedBall dInner 0.01) :
    z.re ≤ (0.405 : ℝ) := by
  have hdist : dist z dInner ≤ (0.01 : ℝ) := Metric.mem_closedBall.mp hz
  have hnorm : ‖z - dInner‖ ≤ (0.01 : ℝ) := by rwa [dist_eq_norm] at hdist
  have hre : |(z - dInner).re| ≤ (0.01 : ℝ) := by
    calc |(z - dInner).re| ≤ ‖z - dInner‖ := Complex.abs_re_le_norm _
      _ ≤ 0.01 := hnorm
  have here : (z - dInner).re = z.re - 0.395 := by
    have e : (z - dInner).re = z.re - dInner.re := Complex.sub_re z dInner
    rw [e, dInner_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  linarith

theorem zetaDiffCont_inner_filled :
    DiffContOnCl ℂ riemannZeta (Metric.ball dInner 0.01) := by
  apply DifferentiableOn.diffContOnCl
  rw [Metric.closure_ball dInner (by norm_num : (0.01 : ℝ) ≠ 0)]
  intro z hz
  apply (differentiableAt_riemannZeta ?_).differentiableWithinAt
  intro hcon
  have hle := dInner_closedBall_re_upper hz
  have e : z.re = 1 := by
    rw [hcon]
    exact Complex.one_re
  linarith

theorem zetaDiffCont_inner_banked : zetaDiffCont_inner :=
  zetaDiffCont_inner_filled

theorem zetaDeriv_inner_125_closed :
    ‖deriv riemannZeta dInner‖ ≤ 12500 := by
  have h := zetaDeriv_inner_125_of_diffCont zetaDiffCont_inner_banked
  rw [zeta_inner_125_number] at h
  exact h

/-! ## 12. LEAF sphere at honest R02-disc 934 (dLeaf = 0.2 - 6.75 I).

Geometry check (margins honest, no force):
* `dLeaf.re = 0.2`, radius `0.01` gives `z.re ∈ [0.19, 0.21]` on the
  sphere, inside R02-disc `Re ∈ [0.05, 0.74]` with margins `0.14` below
  (`0.19 - 0.05`) and `0.53` above (`0.74 - 0.21`).
* `dLeaf.im = -6.75`, radius `0.01` gives `z.im ∈ [-6.76, -6.74]`, inside
  R02-disc `Im ∈ [-8.25, -5.25]` with margins `1.49` below
  (`-6.76 + 8.25`) and `1.49` above (`-5.25 + 6.74`).
* R02-disc numeral (`zeta_rigorous.lean:32566-32568`, via
  `door3_tail_eta_upper.lean:1` transitively):
  `0.05 ≤ s.re`, `s.re ≤ 0.74`, `-8.25 ≤ s.im`, `s.im ≤ -5.25` gives
  `‖riemannZeta s‖ ≤ 934`.
  Hence the whole `0.01`-sphere over `dLeaf` is covered at `934`, NOT `10`.
  The pre-existing `zetaSupOnSphere_leaf` (`≤ 10`) is left untouched and
  NOT claimed here; the filled instance below is restated at `934` only. -/

def zetaSupOnSphere_leaf_934 : Prop :=
  ∀ z : ℂ, z ∈ Metric.sphere dLeaf 0.01 → ‖riemannZeta z‖ ≤ 934

theorem dLeaf_sphere_re_bounds {z : ℂ}
    (hz : z ∈ Metric.sphere dLeaf 0.01) :
    (0.05 : ℝ) ≤ z.re ∧ z.re ≤ (0.74 : ℝ) := by
  have hdist : dist z dLeaf = (0.01 : ℝ) := Metric.mem_sphere.mp hz
  have hnorm : ‖z - dLeaf‖ = (0.01 : ℝ) := by rwa [dist_eq_norm] at hdist
  have hre : |(z - dLeaf).re| ≤ (0.01 : ℝ) := by
    calc |(z - dLeaf).re| ≤ ‖z - dLeaf‖ := Complex.abs_re_le_norm _
      _ = 0.01 := hnorm
  have here : (z - dLeaf).re = z.re - 0.2 := by
    have e : (z - dLeaf).re = z.re - dLeaf.re := Complex.sub_re z dLeaf
    rw [e, dLeaf_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

theorem dLeaf_sphere_im_bounds {z : ℂ}
    (hz : z ∈ Metric.sphere dLeaf 0.01) :
    (-8.25 : ℝ) ≤ z.im ∧ z.im ≤ (-5.25 : ℝ) := by
  have hdist : dist z dLeaf = (0.01 : ℝ) := Metric.mem_sphere.mp hz
  have hnorm : ‖z - dLeaf‖ = (0.01 : ℝ) := by rwa [dist_eq_norm] at hdist
  have him : |(z - dLeaf).im| ≤ (0.01 : ℝ) := by
    calc |(z - dLeaf).im| ≤ ‖z - dLeaf‖ := Complex.abs_im_le_norm _
      _ = 0.01 := hnorm
  have heim : (z - dLeaf).im = z.im - (-6.75) := by
    have e : (z - dLeaf).im = z.im - dLeaf.im := Complex.sub_im z dLeaf
    rw [e, dLeaf_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  have himlo : (-6.76 : ℝ) ≤ z.im := by linarith
  have himhi : z.im ≤ (-6.74 : ℝ) := by linarith
  constructor <;> linarith

theorem zetaSupOnSphere_leaf_934_filled :
    ∀ z : ℂ, z ∈ Metric.sphere dLeaf 0.01 → ‖riemannZeta z‖ ≤ 934 := by
  intro z hz
  obtain ⟨hre_lo, hre_hi⟩ := dLeaf_sphere_re_bounds hz
  obtain ⟨him_lo, him_hi⟩ := dLeaf_sphere_im_bounds hz
  exact R02_D3_zeta_upper_934 z hre_lo hre_hi him_lo him_hi

theorem zetaSup_leaf_934_banked : zetaSupOnSphere_leaf_934 :=
  zetaSupOnSphere_leaf_934_filled

theorem zetaDeriv_leaf_934_of_diffCont
    (hd : zetaDiffCont_leaf) :
    ‖deriv riemannZeta dLeaf‖ ≤ 934 / 0.01 := by
  unfold zetaDiffCont_leaf at hd
  exact zetaDerivUp_of_sup dLeaf 0.01 934 (by norm_num) hd
    zetaSupOnSphere_leaf_934_filled

theorem zeta_leaf_934_number : (934 : ℝ) / 0.01 = 93400 := by norm_num

/-! ## 12b. LEAF DiffContOnCl on the 0.01-ball (pole avoided).

Mirror of MID (`dMid_closedBall_re_upper :1059` + `zetaDiffCont_mid_filled :1074` +
`zetaDiffCont_mid_banked :1087`) and INNER (`dInner_closedBall_re_upper :1175` +
`zetaDiffCont_inner_filled :1190` + `zetaDiffCont_inner_banked :1203`):
`dLeaf.re = 0.2`, radius `0.01`, so every `z ∈ closedBall dLeaf 0.01` has
`z.re ≤ 0.21 < 1`, hence `z ≠ 1`. -/

theorem dLeaf_closedBall_re_upper {z : ℂ}
    (hz : z ∈ Metric.closedBall dLeaf 0.01) :
    z.re ≤ (0.21 : ℝ) := by
  have hdist : dist z dLeaf ≤ (0.01 : ℝ) := Metric.mem_closedBall.mp hz
  have hnorm : ‖z - dLeaf‖ ≤ (0.01 : ℝ) := by rwa [dist_eq_norm] at hdist
  have hre : |(z - dLeaf).re| ≤ (0.01 : ℝ) := by
    calc |(z - dLeaf).re| ≤ ‖z - dLeaf‖ := Complex.abs_re_le_norm _
      _ ≤ 0.01 := hnorm
  have here : (z - dLeaf).re = z.re - 0.2 := by
    have e : (z - dLeaf).re = z.re - dLeaf.re := Complex.sub_re z dLeaf
    rw [e, dLeaf_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  linarith

theorem zetaDiffCont_leaf_filled :
    DiffContOnCl ℂ riemannZeta (Metric.ball dLeaf 0.01) := by
  apply DifferentiableOn.diffContOnCl
  rw [Metric.closure_ball dLeaf (by norm_num : (0.01 : ℝ) ≠ 0)]
  intro z hz
  apply (differentiableAt_riemannZeta ?_).differentiableWithinAt
  intro hcon
  have hle := dLeaf_closedBall_re_upper hz
  have e : z.re = 1 := by
    rw [hcon]
    exact Complex.one_re
  linarith

theorem zetaDiffCont_leaf_banked : zetaDiffCont_leaf :=
  zetaDiffCont_leaf_filled

theorem zetaDeriv_leaf_934_closed :
    ‖deriv riemannZeta dLeaf‖ ≤ 93400 := by
  have h := zetaDeriv_leaf_934_of_diffCont zetaDiffCont_leaf_banked
  rw [zeta_leaf_934_number] at h
  exact h

end Door3DerivUp
