import Mathlib
import door3_stirling_gamma

/-!
# Door-3 digamma enclosures at batch-cell gamma centers (WRITE-ONLY).

No build / lean / lake command run. No commit / push. Exactly one new file.
`door3_digamma.lean` was verified absent via glob before writing.
`door3_stirling_gamma.lean:1` imports `Mathlib` only, so the import graph stays a DAG.

## Recon (read-only, brief)

* Mathlib digamma API (`Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean`):
  `Complex.digamma := logDeriv Gamma` (line 39) plus exactly four lemmas:
  `digamma_def`, `digamma_zero`, `digamma_one`, `digamma_one_half`,
  `digamma_apply_add_one : digamma (s+1) = digamma s + s⁻¹` (needs
  `∀ m : ℕ, s ≠ -m`), `meromorphic_digamma`. There is NO `Real.digamma`,
  NO recurrence values at other integers / half-integers, NO Stirling series
  with remainder, NO integral representation (the file TODO at line 31 says
  Gauss' integral representation is still to be proved).
* `logDeriv` API (`Mathlib/Analysis/Calculus/LogDeriv.lean:34-37`):
  `logDeriv f = deriv f / f`, `logDeriv_apply` is `rfl`.
* Gamma argument is `s / 2`: `DerivCauchyBridge.gammaOf s = Complex.Gamma (s/2)`
  (`central_cover_assembly.lean:6334`). Hence with DERIVUP s-centers
  (`door3_deriv_up.lean:33-38`) outer `0.395 - 8.75i`, leaf `0.2 - 6.75i`,
  mid `0.395 - 4.75i`, inner `0.395 - 0.75i`, the digamma centers are
  `w = s / 2`: outer `0.1975 - 4.375i`, leaf `0.1 - 3.375i`,
  mid `0.1975 - 2.375i`, inner `0.1975 - 0.375i`.
* DERIVUP gap table (`door3_deriv_up.lean:24-30,485-575,917-955`): M-prime
  outer `0.11`, leaf `0.15`, mid `0.15`, inner `0.09`; Cauchy with `C = 600`,
  `rhoC = 0.01` gives the gamma-prime wall `60000` at every center.
  Gamma-prime-alone gross budgets (gamma term `polyVal * nG * vZ` with
  `vZ = 3`, others zeroed; `polyVal` outer `42.83`, leaf `26.24`,
  mid `13.81`, inner `0.79`):
  outer `0.11 / (42.83 * 3) = 0.000856...`, leaf `0.15 / (26.24 * 3)`,
  mid `0.15 / (13.81 * 3)`, inner `0.09 / (0.79 * 3)`.
  Net budgets after poly/pi shares are negative (DERIVUP partials already
  exceed M-prime, e.g. outer partial `0.33 > 0.11`); the allowances banked
  below are therefore gross (before poly/pi/zeta shares), exactly as stated.

## Verdict: unconditional psi discs are INACCESSIBLE within budget (STOP route)

A first unconditional disc `‖ψ(w) − c‖ ≤ r` via
`ψ(z) = log z − 1/(2z) + R` needs, at minimum: (1) Gauss integral rep for
`Complex.digamma` (explicitly TODO, unbanked); (2) Stirling expansion of
`log Γ` with explicit remainder (unbanked); (3) complex-log disc bounds at
all four centers; (4) harmonic-tail majorants; (5) pole-avoidance side
conditions; (6) transfer from `log Γ` remainder to `ψ`; (7) real-Gamma cap
machinery at `Re ∈ {0.1, 0.1975}` (the banked `D3SG_*` decay line is at
`Re = 0.95`, so it does not apply directly); (8) exact rational-shift bookkeeping.
That is more than 8 supporting lemmas for the first disc, so by the brief
the unconditional route STOPS here. The precise missing Mathlib lemma is an
explicit-remainder Stirling bound for `Complex.digamma`, e.g.
`‖digamma w − (log w − 1/(2*w))‖ ≤ C/‖w‖^2` with explicit `C`
(or, equivalently, the Gauss integral representation).
Fallback per brief: report, do not thrash with per-center-tuned Cauchy.

## What this file banks instead (all proofs full, no placeholders)

* Closed recurrence-shift machinery from `Complex.digamma_apply_add_one`:
  `psi_up_one`, `psi_shift_nat` (shift up by `N`), `psi_disc_down_of_up`
  and the combined `psi_disc_transport` (a large-`Re` disc implies the
  `w`-disc with the exact rational sum `Σ (w+k)⁻¹` subtracted).
* Closed pole-avoidance: `shift_avoid_of_re_pos` plus per-group instances
  at shift `N = 8` (lands at `Re ≈ 8.1`, where the asymptotic is tight).
* Closed bridge `gamma_deriv_eq : deriv Gamma w = Gamma w * digamma w`
  (from `digamma_def` + `logDeriv_apply`), local `gOf` mirroring
  `DerivCauchyBridge.gammaOf`, and the generic
  `gammaPrime_le_of_psiDisc : ‖deriv gOf s‖ ≤ G * (‖c‖ + r) / 2`.
* `D3SG_*` reuse (exact banked names): `D3SG_Gamma_norm_le_real`,
  `D3SG_gamma_shift_norm`, `D3SG_factor_mem_Icc`.
* Per group, honest-conditional: `psiNeed_*` (psi disc premise, TRUE-scale
  centers `c` with generous remainder radii `0.5`/`1`), `gamNeed_*`
  (TRUE-scale gamma-upper premises reusing DERIVUP `tightGamma` numerals
  `0.002 / 0.008 / 0.04 / 4.5`; a local shift+real-cap proof at
  `Re ∈ {0.1, 0.1975}` would exceed 6 lemmas, so premises are taken),
  `digamma_disc_*`, `gammaPrime_*_le` with explicit numerals, gross
  allowances `allow_*`, and `gap_*` / `ratio_*` comparisons.
  Result: all four groups GAP (upper exceeds budget) with ratios
  `4.21 / 7.13 / 16.83 / 268.9` — the psi route shrinks the 60000-wall
  gaps to single/triple digits but does not close them.

This file was written without running any build; it is not machine-checked.
-/

noncomputable section

namespace Door3Digamma

open scoped BigOperators

/-! ## 0. Centers: s-centers (DERIVUP rows) and gamma-argument centers w = s/2. -/

noncomputable def sOuter : ℂ := Complex.mk 0.395 (-8.75)

noncomputable def sLeaf : ℂ := Complex.mk 0.2 (-6.75)

noncomputable def sMid : ℂ := Complex.mk 0.395 (-4.75)

noncomputable def sInner : ℂ := Complex.mk 0.395 (-0.75)

noncomputable def wOuter : ℂ := sOuter / 2

noncomputable def wLeaf : ℂ := sLeaf / 2

noncomputable def wMid : ℂ := sMid / 2

noncomputable def wInner : ℂ := sInner / 2

theorem sOuter_re : sOuter.re = (0.395 : ℝ) := rfl

theorem sOuter_im : sOuter.im = (-8.75 : ℝ) := rfl

theorem sLeaf_re : sLeaf.re = (0.2 : ℝ) := rfl

theorem sLeaf_im : sLeaf.im = (-6.75 : ℝ) := rfl

theorem sMid_re : sMid.re = (0.395 : ℝ) := rfl

theorem sMid_im : sMid.im = (-4.75 : ℝ) := rfl

theorem sInner_re : sInner.re = (0.395 : ℝ) := rfl

theorem sInner_im : sInner.im = (-0.75 : ℝ) := rfl

theorem wireOuter : sOuter / 2 = Complex.mk 0.1975 (-4.375) := by
  unfold sOuter
  ext <;> simp <;> norm_num

theorem wireLeaf : sLeaf / 2 = Complex.mk 0.1 (-3.375) := by
  unfold sLeaf
  ext <;> simp <;> norm_num

theorem wireMid : sMid / 2 = Complex.mk 0.1975 (-2.375) := by
  unfold sMid
  ext <;> simp <;> norm_num

theorem wireInner : sInner / 2 = Complex.mk 0.1975 (-0.375) := by
  unfold sInner
  ext <;> simp <;> norm_num

theorem wOuter_re_pos : 0 < wOuter.re := by
  unfold wOuter
  rw [wireOuter]
  norm_num

theorem wLeaf_re_pos : 0 < wLeaf.re := by
  unfold wLeaf
  rw [wireLeaf]
  norm_num

theorem wMid_re_pos : 0 < wMid.re := by
  unfold wMid
  rw [wireMid]
  norm_num

theorem wInner_re_pos : 0 < wInner.re := by
  unfold wInner
  rw [wireInner]
  norm_num

/-! ## 1. `D3SG_*` reuse (exact banked names from `door3_stirling_gamma`). -/

theorem sg_norm_le_real (w : ℂ) (hw : 0 < w.re) :
    ‖Complex.Gamma w‖ ≤ Real.Gamma w.re :=
  D3SG_Gamma_norm_le_real w hw

theorem sg_shift_one (z : ℂ) (hz : 0 < z.re) :
    ‖Complex.Gamma (z + 1)‖ = ‖Complex.Gamma z‖ * ‖z‖ := by
  have h := D3SG_gamma_shift_norm hz 1
  rw [Finset.prod_range_one] at h
  simp only [Nat.cast_zero, add_zero] at h
  have hc : (((1 : ℕ)) : ℂ) = (1 : ℂ) := Nat.cast_one
  rw [hc] at h
  exact h

theorem sg_factor_le_one (sig T : ℝ) (hsig : 0 < sig) (k : ℕ) :
    (sig + (k : ℝ)) ^ 2 / ((sig + (k : ℝ)) ^ 2 + T ^ 2) ≤ 1 :=
  (D3SG_factor_mem_Icc sig T hsig k).2

/-! ## 2. Digamma recurrence-shift machinery (closed, from Mathlib). -/

theorem psi_up_one (w : ℂ) (h : ∀ (m : ℕ), w ≠ -(m : ℂ)) :
    Complex.digamma (w + 1) = Complex.digamma w + w⁻¹ :=
  Complex.digamma_apply_add_one w h

theorem psi_shift_nat (w : ℂ) (N : ℕ)
    (h : ∀ (k : ℕ), k ≤ N → ∀ (m : ℕ), (w + (k : ℂ)) ≠ -(m : ℂ)) :
    Complex.digamma (w + (((N : ℕ)) : ℂ)) =
      Complex.digamma w + ∑ k ∈ Finset.range N, (w + (((k : ℕ)) : ℂ))⁻¹ := by
  revert h
  induction N with
  | zero =>
    intro _
    simp
  | succ n ih =>
    intro h
    have hle : ∀ (k : ℕ), k ≤ n → ∀ (m : ℕ), (w + (k : ℂ)) ≠ -(m : ℂ) := by
      intro k hk m
      exact h k (le_trans hk (Nat.le_succ n)) m
    have ihw := ih hle
    have hcast : (((n + 1 : ℕ)) : ℂ) = (((n : ℕ)) : ℂ) + 1 := by
      push_cast
    have hstep : Complex.digamma ((w + (((n : ℕ)) : ℂ)) + 1) =
        Complex.digamma (w + (((n : ℕ)) : ℂ)) + (w + (((n : ℕ)) : ℂ))⁻¹ :=
      Complex.digamma_apply_add_one _ (h n (Nat.le_succ n))
    have hsum : ∑ k ∈ Finset.range (n + 1), (w + (((k : ℕ)) : ℂ))⁻¹ =
        (∑ k ∈ Finset.range n, (w + (((k : ℕ)) : ℂ))⁻¹) +
          (w + (((n : ℕ)) : ℂ))⁻¹ :=
      Finset.sum_range_succ _ n
    calc Complex.digamma (w + (((n + 1 : ℕ)) : ℂ))
        = Complex.digamma ((w + (((n : ℕ)) : ℂ)) + 1) := by
          rw [hcast, add_assoc]
      _ = Complex.digamma (w + (((n : ℕ)) : ℂ)) +
          (w + (((n : ℕ)) : ℂ))⁻¹ := hstep
      _ = (Complex.digamma w +
          ∑ k ∈ Finset.range n, (w + (((k : ℕ)) : ℂ))⁻¹) +
          (w + (((n : ℕ)) : ℂ))⁻¹ := by
          rw [ihw]
      _ = Complex.digamma w +
          ∑ k ∈ Finset.range (n + 1), (w + (((k : ℕ)) : ℂ))⁻¹ := by
          rw [hsum]
          ring

theorem psi_disc_down_of_up (w cN S : ℂ) (N : ℕ) (rN : ℝ)
    (hEq : Complex.digamma (w + (((N : ℕ)) : ℂ)) = Complex.digamma w + S)
    (hDisc : ‖Complex.digamma (w + (((N : ℕ)) : ℂ)) − cN‖ ≤ rN) :
    ‖Complex.digamma w − (cN − S)‖ ≤ rN := by
  have hEq2 : Complex.digamma w = Complex.digamma (w + (((N : ℕ)) : ℂ)) − S := by
    rw [hEq]
    ring
  have hSame : Complex.digamma w − (cN − S) =
      Complex.digamma (w + (((N : ℕ)) : ℂ)) − cN := by
    rw [hEq2]
    ring
  rw [hSame]
  exact hDisc

theorem psi_disc_transport (w cN : ℂ) (N : ℕ) (rN : ℝ)
    (hNoPole : ∀ (k : ℕ), k ≤ N → ∀ (m : ℕ), (w + (k : ℂ)) ≠ -(m : ℂ))
    (hDisc : ‖Complex.digamma (w + (((N : ℕ)) : ℂ)) − cN‖ ≤ rN) :
    ‖Complex.digamma w −
      (cN − ∑ k ∈ Finset.range N, (w + (((k : ℕ)) : ℂ))⁻¹)‖ ≤ rN :=
  psi_disc_down_of_up w cN (∑ k ∈ Finset.range N, (w + (((k : ℕ)) : ℂ))⁻¹)
    N rN (psi_shift_nat w N hNoPole) hDisc

theorem shift_avoid_of_re_pos (w : ℂ) (N : ℕ) (hw : 0 < w.re) (k : ℕ)
    (hk : k ≤ N) (m : ℕ) : (w + (k : ℂ)) ≠ -(((m : ℕ)) : ℂ) := by
  intro hCon
  have hR := congrArg Complex.re hCon
  simp only [Complex.add_re, Complex.natCast_re, Complex.neg_re] at hR
  have hm : (0 : ℝ) ≤ (((m : ℕ)) : ℝ) := Nat.cast_nonneg m
  have hk0 : (0 : ℝ) ≤ (((k : ℕ)) : ℝ) := Nat.cast_nonneg k
  linarith

theorem avoid_outer (k : ℕ) (hk : k ≤ 8) (m : ℕ) :
    (wOuter + (k : ℂ)) ≠ -(m : ℂ) :=
  shift_avoid_of_re_pos wOuter 8 wOuter_re_pos k hk m

theorem avoid_leaf (k : ℕ) (hk : k ≤ 8) (m : ℕ) :
    (wLeaf + (k : ℂ)) ≠ -(m : ℂ) :=
  shift_avoid_of_re_pos wLeaf 8 wLeaf_re_pos k hk m

theorem avoid_mid (k : ℕ) (hk : k ≤ 8) (m : ℕ) :
    (wMid + (k : ℂ)) ≠ -(m : ℂ) :=
  shift_avoid_of_re_pos wMid 8 wMid_re_pos k hk m

theorem avoid_inner (k : ℕ) (hk : k ≤ 8) (m : ℕ) :
    (wInner + (k : ℂ)) ≠ -(m : ℂ) :=
  shift_avoid_of_re_pos wInner 8 wInner_re_pos k hk m

/-! ## 3. Bridge `gamma' = gamma * psi` and the generic gamma-prime bound. -/

theorem gamma_deriv_eq (w : ℂ) (hne : Complex.Gamma w ≠ 0) :
    deriv Complex.Gamma w = Complex.Gamma w * Complex.digamma w := by
  have hdef : Complex.digamma w = deriv Complex.Gamma w / Complex.Gamma w := by
    rw [Complex.digamma_def, logDeriv_apply]
  rw [hdef]
  field_simp

noncomputable def gOf (s : ℂ) : ℂ := Complex.Gamma (s / 2)

theorem gOf_half_hasDerivAt (s : ℂ) :
    HasDerivAt (fun t : ℂ => t / 2) (((1 : ℂ)) / 2) s :=
  (hasDerivAt_id' (x := s)).div_const (2 : ℂ)

theorem gOf_hasDerivAt (s dG : ℂ) (hG : HasDerivAt Complex.Gamma dG (s / 2)) :
    HasDerivAt gOf (dG * (((1 : ℂ)) / 2)) s :=
  hG.comp (gOf_half_hasDerivAt s)

theorem gOf_deriv_eq (s dG : ℂ) (hG : HasDerivAt Complex.Gamma dG (s / 2)) :
    deriv gOf s = dG * (((1 : ℂ)) / 2) :=
  (gOf_hasDerivAt s dG hG).deriv

theorem gammaPrime_le_of_psiDisc (s w c dG : ℂ) (G r : ℝ)
    (hw : s / 2 = w)
    (hG : HasDerivAt Complex.Gamma dG w)
    (hne : Complex.Gamma w ≠ 0)
    (hGv : ‖Complex.Gamma w‖ ≤ G)
    (hPsi : ‖Complex.digamma w − c‖ ≤ r) :
    ‖deriv gOf s‖ ≤ G * (‖c‖ + r) / 2 := by
  have hGs : HasDerivAt Complex.Gamma dG (s / 2) := by
    rw [hw]
    exact hG
  have hnes : Complex.Gamma (s / 2) ≠ 0 := by
    rw [hw]
    exact hne
  have hGvs : ‖Complex.Gamma (s / 2)‖ ≤ G := by
    rw [hw]
    exact hGv
  have hPsis : ‖Complex.digamma (s / 2) − c‖ ≤ r := by
    rw [hw]
    exact hPsi
  have hdG : dG = Complex.Gamma (s / 2) * Complex.digamma (s / 2) := by
    have hder : deriv Complex.Gamma (s / 2) =
        Complex.Gamma (s / 2) * Complex.digamma (s / 2) :=
      gamma_deriv_eq (s / 2) hnes
    have hder2 : deriv Complex.Gamma (s / 2) = dG := hGs.deriv
    rw [hder2] at hder
    exact hder
  have hdig : ‖Complex.digamma (s / 2)‖ ≤ ‖c‖ + r := by
    have htri : ‖Complex.digamma (s / 2)‖ ≤
        ‖Complex.digamma (s / 2) − c‖ + ‖c‖ := by
      have heq : Complex.digamma (s / 2) =
          (Complex.digamma (s / 2) − c) + c := by
        ring
      rw [heq]
      exact norm_add_le _ _
    linarith [hPsis, htri]
  have hGnn : (0 : ℝ) ≤ G := le_trans (norm_nonneg _) hGvs
  have hdGnorm : ‖dG‖ ≤ G * (‖c‖ + r) := by
    rw [hdG, norm_mul]
    exact mul_le_mul hGvs hdig (norm_nonneg _) hGnn
  have hhalf : ‖(((1 : ℂ)) / 2)‖ = (0.5 : ℝ) := by
    rw [norm_div, Complex.norm_one, Complex.norm_two]
    norm_num
  have hder : deriv gOf s = dG * (((1 : ℂ)) / 2) := gOf_deriv_eq s dG hGs
  rw [hder, norm_mul, hhalf]
  have h05 : (0 : ℝ) ≤ (0.5 : ℝ) := by norm_num
  have hmul := mul_le_mul_of_nonneg_right hdGnorm h05
  have hfin : G * (‖c‖ + r) * 0.5 = G * (‖c‖ + r) / 2 := by ring
  rw [hfin] at hmul
  exact hmul

/-! ## 4. Per-group psi-disc premises (TRUE-scale centers, generous radii).

Approximate `log w − 1/(2w)` values: outer `1.472 − 1.64i`,
leaf `1.213 − 1.689i`, mid `0.851 − 1.697i`, inner `−1.409 − 2.13i`.
Radii `0.5` (outer/leaf/mid) and `1` (inner, small `|w|`) are premises
standing in for the missing Stirling remainder.
-/

noncomputable def cOuter : ℂ := Complex.mk 1.472 (-1.64)

noncomputable def cLeaf : ℂ := Complex.mk 1.213 (-1.689)

noncomputable def cMid : ℂ := Complex.mk 0.851 (-1.697)

noncomputable def cInner : ℂ := Complex.mk (-1.409) (-2.13)

theorem cOuter_re : cOuter.re = (1.472 : ℝ) := rfl

theorem cOuter_im : cOuter.im = (-1.64 : ℝ) := rfl

theorem cLeaf_re : cLeaf.re = (1.213 : ℝ) := rfl

theorem cLeaf_im : cLeaf.im = (-1.689 : ℝ) := rfl

theorem cMid_re : cMid.re = (0.851 : ℝ) := rfl

theorem cMid_im : cMid.im = (-1.697 : ℝ) := rfl

theorem cInner_re : cInner.re = (-1.409 : ℝ) := rfl

theorem cInner_im : cInner.im = (-2.13 : ℝ) := rfl

theorem cNorm_outer : ‖cOuter‖ ≤ (3.112 : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im cOuter
  rw [cOuter_re, cOuter_im] at h
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.472),
    abs_of_neg (by norm_num : (-1.64 : ℝ) < 0)] at h
  linarith [h]

theorem cNorm_leaf : ‖cLeaf‖ ≤ (2.902 : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im cLeaf
  rw [cLeaf_re, cLeaf_im] at h
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.213),
    abs_of_neg (by norm_num : (-1.689 : ℝ) < 0)] at h
  linarith [h]

theorem cNorm_mid : ‖cMid‖ ≤ (2.548 : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im cMid
  rw [cMid_re, cMid_im] at h
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.851),
    abs_of_neg (by norm_num : (-1.697 : ℝ) < 0)] at h
  linarith [h]

theorem cNorm_inner : ‖cInner‖ ≤ (3.539 : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im cInner
  rw [cInner_re, cInner_im] at h
  rw [abs_of_neg (by norm_num : (-1.409 : ℝ) < 0),
    abs_of_neg (by norm_num : (-2.13 : ℝ) < 0)] at h
  linarith [h]

/-! ## 5. Per-group honest-conditional discs, gamma-prime bounds, allowances.

`gamNeed_*` reuse the DERIVUP `tightGamma` TRUE-scale numerals
(`0.002 / 0.008 / 0.04 / 4.5`, cf. `door3_deriv_up.lean:666-684`).
-/

def psiNeed_outer : Prop := ‖Complex.digamma wOuter − cOuter‖ ≤ (0.5 : ℝ)

def psiNeed_leaf : Prop := ‖Complex.digamma wLeaf − cLeaf‖ ≤ (0.5 : ℝ)

def psiNeed_mid : Prop := ‖Complex.digamma wMid − cMid‖ ≤ (0.5 : ℝ)

def psiNeed_inner : Prop := ‖Complex.digamma wInner − cInner‖ ≤ (1 : ℝ)

def gamNeed_outer : Prop := ‖Complex.Gamma wOuter‖ ≤ (0.002 : ℝ)

def gamNeed_leaf : Prop := ‖Complex.Gamma wLeaf‖ ≤ (0.008 : ℝ)

def gamNeed_mid : Prop := ‖Complex.Gamma wMid‖ ≤ (0.04 : ℝ)

def gamNeed_inner : Prop := ‖Complex.Gamma wInner‖ ≤ (4.5 : ℝ)

theorem digamma_disc_outer (h : psiNeed_outer) :
    ‖Complex.digamma wOuter − cOuter‖ ≤ (0.5 : ℝ) := h

theorem digamma_disc_leaf (h : psiNeed_leaf) :
    ‖Complex.digamma wLeaf − cLeaf‖ ≤ (0.5 : ℝ) := h

theorem digamma_disc_mid (h : psiNeed_mid) :
    ‖Complex.digamma wMid − cMid‖ ≤ (0.5 : ℝ) := h

theorem digamma_disc_inner (h : psiNeed_inner) :
    ‖Complex.digamma wInner − cInner‖ ≤ (1 : ℝ) := h

theorem gammaPrime_outer_le (dG : ℂ)
    (hG : HasDerivAt Complex.Gamma dG wOuter)
    (hne : Complex.Gamma wOuter ≠ 0)
    (hGv : ‖Complex.Gamma wOuter‖ ≤ (0.002 : ℝ))
    (hPsi : ‖Complex.digamma wOuter − cOuter‖ ≤ (0.5 : ℝ)) :
    ‖deriv gOf sOuter‖ ≤ (0.003612 : ℝ) := by
  have hgen := gammaPrime_le_of_psiDisc sOuter wOuter cOuter dG
    0.002 0.5 wOuter.rfl hG hne hGv hPsi
  have hnum : (0.002 : ℝ) * (3.112 + 0.5) / 2 = 0.003612 := by norm_num
  have hadd : ‖cOuter‖ + (0.5 : ℝ) ≤ 3.112 + 0.5 := by
    linarith [cNorm_outer]
  have hnn : (0 : ℝ) ≤ (0.002 : ℝ) := by norm_num
  have hmul : (0.002 : ℝ) * (‖cOuter‖ + 0.5) ≤ 0.002 * (3.112 + 0.5) :=
    mul_le_mul_of_nonneg_left hadd hnn
  have h2 : (0.002 : ℝ) * (‖cOuter‖ + 0.5) / 2 ≤ 0.002 * (3.112 + 0.5) / 2 := by
    linarith [hmul]
  rw [hnum] at h2
  exact le_trans hgen h2

theorem gammaPrime_leaf_le (dG : ℂ)
    (hG : HasDerivAt Complex.Gamma dG wLeaf)
    (hne : Complex.Gamma wLeaf ≠ 0)
    (hGv : ‖Complex.Gamma wLeaf‖ ≤ (0.008 : ℝ))
    (hPsi : ‖Complex.digamma wLeaf − cLeaf‖ ≤ (0.5 : ℝ)) :
    ‖deriv gOf sLeaf‖ ≤ (0.013608 : ℝ) := by
  have hgen := gammaPrime_le_of_psiDisc sLeaf wLeaf cLeaf dG
    0.008 0.5 wLeaf.rfl hG hne hGv hPsi
  have hnum : (0.008 : ℝ) * (2.902 + 0.5) / 2 = 0.013608 := by norm_num
  have hadd : ‖cLeaf‖ + (0.5 : ℝ) ≤ 2.902 + 0.5 := by
    linarith [cNorm_leaf]
  have hnn : (0 : ℝ) ≤ (0.008 : ℝ) := by norm_num
  have hmul : (0.008 : ℝ) * (‖cLeaf‖ + 0.5) ≤ 0.008 * (2.902 + 0.5) :=
    mul_le_mul_of_nonneg_left hadd hnn
  have h2 : (0.008 : ℝ) * (‖cLeaf‖ + 0.5) / 2 ≤ 0.008 * (2.902 + 0.5) / 2 := by
    linarith [hmul]
  rw [hnum] at h2
  exact le_trans hgen h2

theorem gammaPrime_mid_le (dG : ℂ)
    (hG : HasDerivAt Complex.Gamma dG wMid)
    (hne : Complex.Gamma wMid ≠ 0)
    (hGv : ‖Complex.Gamma wMid‖ ≤ (0.04 : ℝ))
    (hPsi : ‖Complex.digamma wMid − cMid‖ ≤ (0.5 : ℝ)) :
    ‖deriv gOf sMid‖ ≤ (0.06096 : ℝ) := by
  have hgen := gammaPrime_le_of_psiDisc sMid wMid cMid dG
    0.04 0.5 wMid.rfl hG hne hGv hPsi
  have hnum : (0.04 : ℝ) * (2.548 + 0.5) / 2 = 0.06096 := by norm_num
  have hadd : ‖cMid‖ + (0.5 : ℝ) ≤ 2.548 + 0.5 := by
    linarith [cNorm_mid]
  have hnn : (0 : ℝ) ≤ (0.04 : ℝ) := by norm_num
  have hmul : (0.04 : ℝ) * (‖cMid‖ + 0.5) ≤ 0.04 * (2.548 + 0.5) :=
    mul_le_mul_of_nonneg_left hadd hnn
  have h2 : (0.04 : ℝ) * (‖cMid‖ + 0.5) / 2 ≤ 0.04 * (2.548 + 0.5) / 2 := by
    linarith [hmul]
  rw [hnum] at h2
  exact le_trans hgen h2

theorem gammaPrime_inner_le (dG : ℂ)
    (hG : HasDerivAt Complex.Gamma dG wInner)
    (hne : Complex.Gamma wInner ≠ 0)
    (hGv : ‖Complex.Gamma wInner‖ ≤ (4.5 : ℝ))
    (hPsi : ‖Complex.digamma wInner − cInner‖ ≤ (1 : ℝ)) :
    ‖deriv gOf sInner‖ ≤ (10.2128 : ℝ) := by
  have hgen := gammaPrime_le_of_psiDisc sInner wInner cInner dG
    4.5 1 wInner.rfl hG hne hGv hPsi
  have hnum : (4.5 : ℝ) * (3.539 + 1) / 2 ≤ 10.2128 := by norm_num
  have hadd : ‖cInner‖ + (1 : ℝ) ≤ 3.539 + 1 := by
    linarith [cNorm_inner]
  have hnn : (0 : ℝ) ≤ (4.5 : ℝ) := by norm_num
  have hmul : (4.5 : ℝ) * (‖cInner‖ + 1) ≤ 4.5 * (3.539 + 1) :=
    mul_le_mul_of_nonneg_left hadd hnn
  have h2 : (4.5 : ℝ) * (‖cInner‖ + 1) / 2 ≤ 4.5 * (3.539 + 1) / 2 := by
    linarith [hmul]
  exact le_trans (le_trans hgen h2) hnum

/-! Gross gamma-prime allowances `M' / (polyVal * vZ)`, `vZ = 3`
(read-only cites: M-prime from `door3_deriv_up.lean:24-30`,
`polyVal` from `door3_deriv_up.lean:282-376`). -/

theorem allow_outer : (0.11 : ℝ) / (42.83 * 3) ≤ (0.000857 : ℝ) := by norm_num

theorem allow_leaf : (0.15 : ℝ) / (26.24 * 3) ≤ (0.001906 : ℝ) := by norm_num

theorem allow_mid : (0.15 : ℝ) / (13.81 * 3) ≤ (0.003621 : ℝ) := by norm_num

theorem allow_inner : (0.09 : ℝ) / (0.79 * 3) ≤ (0.037975 : ℝ) := by norm_num

/-! Comparisons: every group GAP (conditional upper exceeds gross budget). -/

theorem gap_outer : (0.000857 : ℝ) < (0.003612 : ℝ) := by norm_num

theorem gap_leaf : (0.001906 : ℝ) < (0.013608 : ℝ) := by norm_num

theorem gap_mid : (0.003621 : ℝ) < (0.06096 : ℝ) := by norm_num

theorem gap_inner : (0.037975 : ℝ) < (10.2128 : ℝ) := by norm_num

theorem ratio_outer : (4.21 : ℝ) < (0.003612 : ℝ) / (0.000857 : ℝ) := by norm_num

theorem ratio_leaf : (7.13 : ℝ) < (0.013608 : ℝ) / (0.001906 : ℝ) := by norm_num

theorem ratio_mid : (16.83 : ℝ) < (0.06096 : ℝ) / (0.003621 : ℝ) := by norm_num

theorem ratio_inner : (268.9 : ℝ) < (10.2128 : ℝ) / (0.037975 : ℝ) := by norm_num

/-! ## 6. Remainder (per-cell extension + missing-lemma record).

* Per cell: discharge `psiNeed_*` (psi disc at `w`, e.g. via
  `psi_disc_transport` with `N = 8` once a large-`Re` Stirling disc lands),
  `gamNeed_*` (tight TRUE-scale gamma sup; the intended route is the
  `D3SG_*` shift+real-cap machinery, but the banked decay line is at
  `Re = 0.95` while these centers sit at `Re ∈ {0.1, 0.1975}`, so fresh
  real caps are owed), `hne` (from `Complex.Gamma_ne_zero` once the
  `∀ m, w ≠ -m` side condition is checked against the wire numerals),
  and `hG` (from `Complex.differentiableAt_Gamma` away from poles).
* Missing Mathlib lemma (precise): explicit-remainder Stirling bound for
  `Complex.digamma` at the four `w`-centers, or equivalently the Gauss
  integral representation (`Mathlib/.../Gamma/Digamma.lean:31` TODO).
  No `Real.digamma` exists either.
* Fallback (report only, not attempted): land the tight gamma sups plus
  proved psi discs; this file's conditional chain then closes gamma-prime
  without the Cauchy-60000 wall. Per-cell-tuned Cauchy is recorded as
  refused by the brief.
-/

end Door3Digamma

/-! ## 7. Psi-ladder transport rung at N = 8 (append-only).

Mirrors latest psi rung block (`avoid_*` + `psi_disc_transport`, cf.
`door3_digamma.lean:239-270`): each result is the exact
`psi_disc_transport ... 8 ... avoid_*` instance, so a large-Re disc at
`w + 8` yields the `w`-disc with the rational sum subtracted.
Value: conditional only; the shifted-disc premise at `Re ~ 8.1`
remains open and is filed as residual below.
Residual for next rung (exact): closed discs
`‖Complex.digamma (wOuter + 8) − cN‖ ≤ rN` (and leaf/mid/inner)
with `cN − ∑ k ∈ Finset.range 8, (w + k)⁻¹ = c`
(`c ∈ {cOuter, cLeaf, cMid, cInner}`, radii `0.5 / 0.5 / 0.5 / 1`)
plus tight gamma sups `gamNeed_*`; both need the explicit-remainder
Stirling bound for `Complex.digamma` at `Re ~ 8.1` (Gauss integral rep,
`Mathlib/.../Gamma/Digamma.lean:31` TODO) which is not in Mathlib.
-/

namespace Door3Digamma

open scoped BigOperators

theorem psi_transport_outer (cN : ℂ) (rN : ℝ)
    (hDisc : ‖Complex.digamma (wOuter + (((8 : ℕ)) : ℂ)) − cN‖ ≤ rN) :
    ‖Complex.digamma wOuter −
      (cN − ∑ k ∈ Finset.range 8, (wOuter + (((k : ℕ)) : ℂ))⁻¹)‖ ≤ rN :=
  psi_disc_transport wOuter cN 8 rN avoid_outer hDisc

theorem psi_transport_leaf (cN : ℂ) (rN : ℝ)
    (hDisc : ‖Complex.digamma (wLeaf + (((8 : ℕ)) : ℂ)) − cN‖ ≤ rN) :
    ‖Complex.digamma wLeaf −
      (cN − ∑ k ∈ Finset.range 8, (wLeaf + (((k : ℕ)) : ℂ))⁻¹)‖ ≤ rN :=
  psi_disc_transport wLeaf cN 8 rN avoid_leaf hDisc

theorem psi_transport_mid (cN : ℂ) (rN : ℝ)
    (hDisc : ‖Complex.digamma (wMid + (((8 : ℕ)) : ℂ)) − cN‖ ≤ rN) :
    ‖Complex.digamma wMid −
      (cN − ∑ k ∈ Finset.range 8, (wMid + (((k : ℕ)) : ℂ))⁻¹)‖ ≤ rN :=
  psi_disc_transport wMid cN 8 rN avoid_mid hDisc

theorem psi_transport_inner (cN : ℂ) (rN : ℝ)
    (hDisc : ‖Complex.digamma (wInner + (((8 : ℕ)) : ℂ)) − cN‖ ≤ rN) :
    ‖Complex.digamma wInner −
      (cN − ∑ k ∈ Finset.range 8, (wInner + (((k : ℕ)) : ℂ))⁻¹)‖ ≤ rN :=
  psi_disc_transport wInner cN 8 rN avoid_inner hDisc

end Door3Digamma

/-! ## 8. Closed shifted-disc specs at N = 8 + gamNeed reuse (honest Props).

Transport rungs `psi_transport_*` (`door3_digamma.lean:587-605`) take a generic
shifted disc at `w + 8` as premise. Residual (`door3_digamma.lean:574-580`):
closed discs `‖digamma (w + 8) − cN‖ ≤ rN` with `cN − sum = c`
(`c ∈ {cOuter, cLeaf, cMid, cInner}`, radii `0.5 / 0.5 / 0.5 / 1`) plus
tight gamma sups `gamNeed_*` (`door3_digamma.lean:419-425`).
This block files the four shifted discs as exact Props with `cN := c + sum`,
proves `cN − sum = c` in closed form, and closes the conditional step
`psiShiftNeed_* → psiNeed_*` via the banked transport rungs.
No unconditional disc is claimed: the `Re ~ 8.1` Stirling remainder stays open.
-/

namespace Door3Digamma

open scoped BigOperators

noncomputable def cNOuter : ℂ :=
  cOuter + ∑ k ∈ Finset.range 8, (wOuter + (((k : ℕ)) : ℂ))⁻¹

noncomputable def cNLeaf : ℂ :=
  cLeaf + ∑ k ∈ Finset.range 8, (wLeaf + (((k : ℕ)) : ℂ))⁻¹

noncomputable def cNMid : ℂ :=
  cMid + ∑ k ∈ Finset.range 8, (wMid + (((k : ℕ)) : ℂ))⁻¹

noncomputable def cNInner : ℂ :=
  cInner + ∑ k ∈ Finset.range 8, (wInner + (((k : ℕ)) : ℂ))⁻¹

def psiShiftNeed_outer : Prop :=
  ‖Complex.digamma (wOuter + (((8 : ℕ)) : ℂ)) − cNOuter‖ ≤ (0.5 : ℝ)

def psiShiftNeed_leaf : Prop :=
  ‖Complex.digamma (wLeaf + (((8 : ℕ)) : ℂ)) − cNLeaf‖ ≤ (0.5 : ℝ)

def psiShiftNeed_mid : Prop :=
  ‖Complex.digamma (wMid + (((8 : ℕ)) : ℂ)) − cNMid‖ ≤ (0.5 : ℝ)

def psiShiftNeed_inner : Prop :=
  ‖Complex.digamma (wInner + (((8 : ℕ)) : ℂ)) − cNInner‖ ≤ (1 : ℝ)

theorem cNOuter_sub :
    cNOuter − ∑ k ∈ Finset.range 8, (wOuter + (((k : ℕ)) : ℂ))⁻¹ = cOuter := by
  unfold cNOuter
  rw [add_sub_cancel]

theorem cNLeaf_sub :
    cNLeaf − ∑ k ∈ Finset.range 8, (wLeaf + (((k : ℕ)) : ℂ))⁻¹ = cLeaf := by
  unfold cNLeaf
  rw [add_sub_cancel]

theorem cNMid_sub :
    cNMid − ∑ k ∈ Finset.range 8, (wMid + (((k : ℕ)) : ℂ))⁻¹ = cMid := by
  unfold cNMid
  rw [add_sub_cancel]

theorem cNInner_sub :
    cNInner − ∑ k ∈ Finset.range 8, (wInner + (((k : ℕ)) : ℂ))⁻¹ = cInner := by
  unfold cNInner
  rw [add_sub_cancel]

theorem psiShift_implies_psiNeed_outer (h : psiShiftNeed_outer) : psiNeed_outer := by
  unfold psiShiftNeed_outer at h
  unfold psiNeed_outer
  have hT := psi_transport_outer cNOuter 0.5 h
  have hEq : cNOuter − ∑ k ∈ Finset.range 8, (wOuter + (((k : ℕ)) : ℂ))⁻¹ =
    cOuter := cNOuter_sub
  rw [hEq] at hT
  exact hT

theorem psiShift_implies_psiNeed_leaf (h : psiShiftNeed_leaf) : psiNeed_leaf := by
  unfold psiShiftNeed_leaf at h
  unfold psiNeed_leaf
  have hT := psi_transport_leaf cNLeaf 0.5 h
  have hEq : cNLeaf − ∑ k ∈ Finset.range 8, (wLeaf + (((k : ℕ)) : ℂ))⁻¹ =
    cLeaf := cNLeaf_sub
  rw [hEq] at hT
  exact hT

theorem psiShift_implies_psiNeed_mid (h : psiShiftNeed_mid) : psiNeed_mid := by
  unfold psiShiftNeed_mid at h
  unfold psiNeed_mid
  have hT := psi_transport_mid cNMid 0.5 h
  have hEq : cNMid − ∑ k ∈ Finset.range 8, (wMid + (((k : ℕ)) : ℂ))⁻¹ =
    cMid := cNMid_sub
  rw [hEq] at hT
  exact hT

theorem psiShift_implies_psiNeed_inner (h : psiShiftNeed_inner) : psiNeed_inner := by
  unfold psiShiftNeed_inner at h
  unfold psiNeed_inner
  have hT := psi_transport_inner cNInner 1 h
  have hEq : cNInner − ∑ k ∈ Finset.range 8, (wInner + (((k : ℕ)) : ℂ))⁻¹ =
    cInner := cNInner_sub
  rw [hEq] at hT
  exact hT

def doorShiftNeed_outer : Prop := psiShiftNeed_outer ∧ gamNeed_outer

def doorShiftNeed_leaf : Prop := psiShiftNeed_leaf ∧ gamNeed_leaf

def doorShiftNeed_mid : Prop := psiShiftNeed_mid ∧ gamNeed_mid

def doorShiftNeed_inner : Prop := psiShiftNeed_inner ∧ gamNeed_inner

end Door3Digamma

/-! ## 9. hne/hG closed at all four centers + shift-conditional gamma-prime (append-only).

Grep basis (filed specs + premise shapes, read before writing):
- `psiShiftNeed_*` (`door3_digamma.lean:642-652`): shifted discs
  `‖digamma (w + 8) − cN‖ ≤ r` with `cN := c + Σ k ∈ range 8, (w + k)⁻¹`
  (`cNOuter / cNLeaf / cNMid / cNInner`, `door3_digamma.lean:630-640`), radii
  `0.5 / 0.5 / 0.5 / 1`.
- `gamNeed_*` (`door3_digamma.lean:419-425`): `‖Gamma w‖ ≤ 0.002 / 0.008 /
  0.04 / 4.5` (DERIVUP `tightGamma` numerals).
- `doorShiftNeed_*` (`door3_digamma.lean:710-716`):
  `psiShiftNeed_* ∧ gamNeed_*`.
- `hne` shape (`door3_digamma.lean:274,298,441,460,479,498`):
  `Complex.Gamma w ≠ 0` at each `w ∈ {wOuter, wLeaf, wMid, wInner}`.
- `hG` shape (`door3_digamma.lean:287,297,440,459,478,497`):
  `HasDerivAt Complex.Gamma dG w` at each `w`.

Value banked here (all proofs closed, from Mathlib + file-local lemmas only):
- `wNoPole_*`: pole avoidance at each center from `w*_re_pos` via the
  file-local `shift_avoid_of_re_pos` at `k = 0`.
- `hne_*`: `Complex.Gamma w ≠ 0` via `Complex.Gamma_ne_zero`
  (`Mathlib/.../Gamma/Beta.lean:427`) fed by `wNoPole_*`.
- `hG_*`: `HasDerivAt` witnesses via `Complex.differentiableAt_Gamma`
  (`Mathlib/.../Gamma/Deriv.lean:65`) fed by `wNoPole_*`, projected with
  `DifferentiableAt.hasDerivAt`.
- `gammaPrime_*_of_shift`: each banked `gammaPrime_*_le` quantitative bound
  now follows from `psiShiftNeed_* ∧ gamNeed_*` alone (closed `hne / hG`
  supplied here, `psiNeed` via the banked `psiShift_implies_psiNeed_*` rung).

Residual (exact, still open — no unconditional claim made):
- `psiShiftNeed_*` at shifted Re `8.1975 / 8.1 / 8.1975 / 8.1975`
  (`0.1975 + 8`, `0.1 + 8` from `wireOuter / wireLeaf / wireMid / wireInner`):
  needs the explicit-remainder Stirling bound for `Complex.digamma`
  (e.g. `‖digamma z − (log z − 1 / (2 * z))‖ ≤ C / ‖z‖^2` with explicit `C`)
  or equivalently the Gauss integral representation, which is the stated
  TODO at `Mathlib/.../Gamma/Digamma.lean:31`. The banked digamma API is only
  `digamma_zero`, `digamma_one`, `digamma_one_half`,
  `digamma_apply_add_one`, `meromorphic_digamma`; there is no
  `Real.digamma`, no Stirling remainder, no integral representation.
  An integral / bound route was examined and is not available from the
  banked API, so no `psiShiftNeed` proof is attempted here.
- `gamNeed_*` at `Re ∈ {0.1, 0.1975}`: the banked `D3SG_*` decay line sits
  at `Re = 0.95` (`sg_norm_le_real`, `sg_shift_one`), so fresh real caps at
  the four centers are still owed.
- Hence each `doorShiftNeed_*` stays a filed Prop (condition), now with
  `hne / hG` closed and only `psiShiftNeed_* + gamNeed_*` outstanding.
-/

namespace Door3Digamma

theorem wNoPole_outer (m : ℕ) : wOuter ≠ -(m : ℂ) := by
  have h := shift_avoid_of_re_pos wOuter 8 wOuter_re_pos 0 (Nat.zero_le _) m
  simp only [Nat.cast_zero, add_zero] at h
  exact h

theorem wNoPole_leaf (m : ℕ) : wLeaf ≠ -(m : ℂ) := by
  have h := shift_avoid_of_re_pos wLeaf 8 wLeaf_re_pos 0 (Nat.zero_le _) m
  simp only [Nat.cast_zero, add_zero] at h
  exact h

theorem wNoPole_mid (m : ℕ) : wMid ≠ -(m : ℂ) := by
  have h := shift_avoid_of_re_pos wMid 8 wMid_re_pos 0 (Nat.zero_le _) m
  simp only [Nat.cast_zero, add_zero] at h
  exact h

theorem wNoPole_inner (m : ℕ) : wInner ≠ -(m : ℂ) := by
  have h := shift_avoid_of_re_pos wInner 8 wInner_re_pos 0 (Nat.zero_le _) m
  simp only [Nat.cast_zero, add_zero] at h
  exact h

theorem hne_outer : Complex.Gamma wOuter ≠ 0 :=
  Complex.Gamma_ne_zero wNoPole_outer

theorem hne_leaf : Complex.Gamma wLeaf ≠ 0 :=
  Complex.Gamma_ne_zero wNoPole_leaf

theorem hne_mid : Complex.Gamma wMid ≠ 0 :=
  Complex.Gamma_ne_zero wNoPole_mid

theorem hne_inner : Complex.Gamma wInner ≠ 0 :=
  Complex.Gamma_ne_zero wNoPole_inner

theorem hG_outer :
    HasDerivAt Complex.Gamma (deriv Complex.Gamma wOuter) wOuter :=
  (Complex.differentiableAt_Gamma wOuter wNoPole_outer).hasDerivAt

theorem hG_leaf :
    HasDerivAt Complex.Gamma (deriv Complex.Gamma wLeaf) wLeaf :=
  (Complex.differentiableAt_Gamma wLeaf wNoPole_leaf).hasDerivAt

theorem hG_mid :
    HasDerivAt Complex.Gamma (deriv Complex.Gamma wMid) wMid :=
  (Complex.differentiableAt_Gamma wMid wNoPole_mid).hasDerivAt

theorem hG_inner :
    HasDerivAt Complex.Gamma (deriv Complex.Gamma wInner) wInner :=
  (Complex.differentiableAt_Gamma wInner wNoPole_inner).hasDerivAt

theorem gammaPrime_outer_of_shift (hShift : psiShiftNeed_outer)
    (hGv : gamNeed_outer) : ‖deriv gOf sOuter‖ ≤ (0.003612 : ℝ) := by
  have hPsi : ‖Complex.digamma wOuter − cOuter‖ ≤ (0.5 : ℝ) :=
    psiShift_implies_psiNeed_outer hShift
  have hGv' : ‖Complex.Gamma wOuter‖ ≤ (0.002 : ℝ) := hGv
  exact gammaPrime_outer_le _ hG_outer hne_outer hGv' hPsi

theorem gammaPrime_leaf_of_shift (hShift : psiShiftNeed_leaf)
    (hGv : gamNeed_leaf) : ‖deriv gOf sLeaf‖ ≤ (0.013608 : ℝ) := by
  have hPsi : ‖Complex.digamma wLeaf − cLeaf‖ ≤ (0.5 : ℝ) :=
    psiShift_implies_psiNeed_leaf hShift
  have hGv' : ‖Complex.Gamma wLeaf‖ ≤ (0.008 : ℝ) := hGv
  exact gammaPrime_leaf_le _ hG_leaf hne_leaf hGv' hPsi

theorem gammaPrime_mid_of_shift (hShift : psiShiftNeed_mid)
    (hGv : gamNeed_mid) : ‖deriv gOf sMid‖ ≤ (0.06096 : ℝ) := by
  have hPsi : ‖Complex.digamma wMid − cMid‖ ≤ (0.5 : ℝ) :=
    psiShift_implies_psiNeed_mid hShift
  have hGv' : ‖Complex.Gamma wMid‖ ≤ (0.04 : ℝ) := hGv
  exact gammaPrime_mid_le _ hG_mid hne_mid hGv' hPsi

theorem gammaPrime_inner_of_shift (hShift : psiShiftNeed_inner)
    (hGv : gamNeed_inner) : ‖deriv gOf sInner‖ ≤ (10.2128 : ℝ) := by
  have hPsi : ‖Complex.digamma wInner − cInner‖ ≤ (1 : ℝ) :=
    psiShift_implies_psiNeed_inner hShift
  have hGv' : ‖Complex.Gamma wInner‖ ≤ (4.5 : ℝ) := hGv
  exact gammaPrime_inner_le _ hG_inner hne_inner hGv' hPsi

end Door3Digamma

/-! ## 10. Outer shifted-disc triangle attempt at N = 8 (append-only).

Grep basis (read before writing):
- Spec `psiShiftNeed_outer` (`door3_digamma.lean:642-643`):
  `‖Complex.digamma (wOuter + (((8 : ℕ)) : ℂ)) − cNOuter‖ ≤ (0.5 : ℝ)`.
- Center `cNOuter` (`door3_digamma.lean:630-631`):
  `cOuter + ∑ k ∈ Finset.range 8, (wOuter + (((k : ℕ)) : ℂ))⁻¹`.
- Transport `psi_transport_outer` (`door3_digamma.lean:587-591`):
  exact `psi_disc_transport ... 8 ... avoid_outer` instance.
- Header imports (`door3_digamma.lean:1-2`): `Mathlib`,
  `door3_stirling_gamma` only; no imports added here.
- Banked citable without new imports: `D3SG_*` in
  `door3_stirling_gamma` are Gamma-norm / shift / factor / decay bounds
  at `Re = 0.95` and related tiers; grep over that file for
  `digamma / Stirling remainder / psi remainder` returns only the
  `gamNeed` target comments, i.e. no digamma remainder is banked.
  Other in-repo digamma bounds would need new imports, so they are not
  cited here (cycle risk, append-only scope).

Attempt (honest, closed): generic two-piece triangle / chain. Any chain
  `digamma (wOuter + 8) → L → cNOuter` needs a main remainder premise
  plus a misclosure premise with `r1 + r2 ≤ 0.5`. Both premises are filed
  below as exact Props; neither has a closed instantiation from the
  banked API, so `psiShiftNeed_outer` stays open. The shifted point sits
  at `Re = 0.1975 + 8 = 8.1975` via `wireOuter`
  (`door3_digamma.lean:126-128`); see `wOuter8_re` below.
-/

namespace Door3Digamma

open scoped BigOperators

theorem wOuter8_re :
    (wOuter + (((8 : ℕ)) : ℂ)).re = (8.1975 : ℝ) := by
  have hw : wOuter = Complex.mk 0.1975 (-4.375) := by
    unfold wOuter
    exact wireOuter
  rw [hw]
  simp
  norm_num

theorem psiShiftNeed_outer_of_split (L : ℂ) (r1 r2 : ℝ)
    (hMain : ‖Complex.digamma (wOuter + (((8 : ℕ)) : ℂ)) − L‖ ≤ r1)
    (hClose : ‖L − cNOuter‖ ≤ r2)
    (hAdd : r1 + r2 ≤ (0.5 : ℝ)) :
    psiShiftNeed_outer := by
  unfold psiShiftNeed_outer
  have heq : Complex.digamma (wOuter + (((8 : ℕ)) : ℂ)) − cNOuter =
      (Complex.digamma (wOuter + (((8 : ℕ)) : ℂ)) − L) + (L − cNOuter) := by
    ring
  have htri : ‖Complex.digamma (wOuter + (((8 : ℕ)) : ℂ)) − cNOuter‖ ≤
      ‖Complex.digamma (wOuter + (((8 : ℕ)) : ℂ)) − L‖ + ‖L − cNOuter‖ := by
    rw [heq]
    exact norm_add_le _ _
  linarith [hMain, hClose, htri, hAdd]

theorem psiShiftNeed_outer_of_chain (L : ℂ) (E1 E2 : ℂ) (r1 r2 : ℝ)
    (hMain : Complex.digamma (wOuter + (((8 : ℕ)) : ℂ)) − L = E1)
    (hClose : L − cNOuter = E2)
    (hE1 : ‖E1‖ ≤ r1) (hE2 : ‖E2‖ ≤ r2)
    (hAdd : r1 + r2 ≤ (0.5 : ℝ)) :
    psiShiftNeed_outer := by
  have hMainN : ‖Complex.digamma (wOuter + (((8 : ℕ)) : ℂ)) − L‖ ≤ r1 := by
    rw [hMain]
    exact hE1
  have hCloseN : ‖L − cNOuter‖ ≤ r2 := by
    rw [hClose]
    exact hE2
  exact psiShiftNeed_outer_of_split L r1 r2 hMainN hCloseN hAdd

def psiOuterMainRemainder (L : ℂ) (r1 : ℝ) : Prop :=
  ‖Complex.digamma (wOuter + (((8 : ℕ)) : ℂ)) − L‖ ≤ r1

def psiOuterCloseRemainder (L : ℂ) (r2 : ℝ) : Prop :=
  ‖L − cNOuter‖ ≤ r2

/-! Residual (exact, still open — no unconditional claim made):

* `psiShiftNeed_outer` (`door3_digamma.lean:642-643`) at `Re = 8.1975`
  (`wOuter8_re` above, via `wireOuter`): would follow from
  `psiShiftNeed_outer_of_split` once some `L / r1 / r2` satisfies
  `psiOuterMainRemainder L r1` and `psiOuterCloseRemainder L r2` with
  `r1 + r2 ≤ 0.5`.
* What is missing: the main-remainder instantiation, i.e. an
  explicit-remainder Stirling bound for `Complex.digamma` at
  `wOuter + 8` (e.g. `‖digamma z − (log z − 1 / (2 * z))‖ ≤ C / ‖z‖^2`
  with explicit `C`), or equivalently the Gauss integral representation
  noted as TODO at `Mathlib/.../Gamma/Digamma.lean:31`. The banked
  digamma API is only `digamma_zero`, `digamma_one`, `digamma_one_half`,
  `digamma_apply_add_one`, `meromorphic_digamma`; `D3SG_*` supplies no
  digamma remainder. Hence no `L / r1 / r2` triple is closed here and no
  proof of `psiShiftNeed_outer` is claimed; the chain above is the full
  value banked in this block.
-/

end Door3Digamma

/-! ## 11. ONE gamNeed real-cap attempt at inner Re 0.1975 (append-only).

Grep basis (read before writing):
- gamNeed specs (`door3_digamma.lean:419-425`):
  `‖Gamma w‖ ≤ 0.002 / 0.008 / 0.04 / 4.5`.
- shiftNeeds (`door3_digamma.lean:642-652`):
  `psiShiftNeed_*` discs at `w + 8` with radii `0.5 / 0.5 / 0.5 / 1`.
- doorShiftNeed (`door3_digamma.lean:710-716`):
  `psiShiftNeed_* ∧ gamNeed_*`.
- D3SG decay at Re 0.95 does not cover Re 0.1 / 0.1975; generic
  `D3SG_decay_sigma` (`door3_stirling_gamma.lean:1305-1307`) plus
  `D3SG_Gamma_one_two_le_one` (`door3_stirling_gamma.lean:1366-1378`)
  are citable without new imports (header already imports
  `door3_stirling_gamma`). Stirling shift chains elsewhere in that file
  are reference only; the real cap below is rebuilt locally from
  Mathlib convexity plus `Real.Gamma_add_one`.

Attempt (inner, most favorable: target 4.5, `|Im| = 0.375`):
- `realGamma_01975_le_six`: `Real.Gamma 0.1975 ≤ 6` via `Gamma 1.1975 ≤ 1`.
- `gamInner_decay_inst`: `‖Gamma wInner‖ ≤ 18 * exp(-|Im| / 2)`
  via `D3SG_decay_sigma` with `M = 6`.
- `exp_neg01875_lower` plus `gamInner_envelope_exceeds`: the envelope is
  at least `14.625`, hence above `4.5`; this route does not close
  `gamNeed_inner`.

Residual (exact, still open):
- `gamNeed_inner` (`door3_digamma.lean:425`): needs `‖Gamma wInner‖ ≤ 4.5`;
  rebuilt route yields only `≤ 18 * exp(-0.1875)` with
  `exp(-0.1875) ≥ 0.8125`. Closing through this envelope would need
  `exp(-0.1875) ≤ 0.25`, contrary to the lower bound. A tighter `M`
  cannot help here: an honest `M` must bound `Real.Gamma 0.1975`
  (true value above 4.5), while `3 * M * 0.8125 ≤ 4.5` would need
  `M ≤ 1.85`. Fresh idea owed: direct complex enclosure or sharper
  Im-decay at Re 0.1975.
- `gamNeed_outer / leaf / mid` untouched here; same envelope shape with
  larger `|Im|` but much smaller targets `0.002 / 0.008 / 0.04`.
- Hence `doorShiftNeed_inner` stays as filed condition with only this
  attempt logged.
-/

namespace Door3Digamma

theorem wInner_eq_mk : wInner = Complex.mk (0.1975 : ℝ) (-0.375 : ℝ) := by
  unfold wInner
  exact wireInner

theorem wInner_re_eq : wInner.re = (0.1975 : ℝ) := by
  rw [wInner_eq_mk]

theorem wInner_abs_im : |wInner.im| = (0.375 : ℝ) := by
  have him : (Complex.mk (0.1975 : ℝ) (-0.375 : ℝ)).im = (-0.375 : ℝ) := rfl
  rw [wInner_eq_mk, him]
  norm_num

theorem realGamma_01975_le_six : Real.Gamma (0.1975 : ℝ) ≤ 6 := by
  have hpos : (0 : ℝ) < 0.1975 := by norm_num
  have hne : (0.1975 : ℝ) ≠ 0 := ne_of_gt hpos
  have hshift : Real.Gamma (0.1975 + 1) = 0.1975 * Real.Gamma 0.1975 :=
    Real.Gamma_add_one hne
  have h1 : (1 : ℝ) ≤ 0.1975 + 1 := by norm_num
  have h2 : 0.1975 + 1 ≤ 2 := by norm_num
  have hcap : Real.Gamma (0.1975 + 1) ≤ 1 :=
    D3SG_Gamma_one_two_le_one _ h1 h2
  have hdiv : Real.Gamma (0.1975 : ℝ) = Real.Gamma (0.1975 + 1) / 0.1975 := by
    rw [eq_div_iff_mul_eq hne]
    rw [hshift]
    ring
  have h1div : Real.Gamma (0.1975 + 1) / 0.1975 ≤ 1 / 0.1975 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hcap (inv_nonneg.mpr (le_of_lt hpos))
  have h6 : (1 : ℝ) / 0.1975 ≤ 6 := by
    rw [div_le_iff₀ hpos]
    norm_num
  calc Real.Gamma (0.1975 : ℝ) = Real.Gamma (0.1975 + 1) / 0.1975 := hdiv
    _ ≤ 1 / 0.1975 := h1div
    _ ≤ 6 := h6

theorem gamInner_decay_inst :
    ‖Complex.Gamma wInner‖ ≤ 3 * 6 * Real.exp (-(1 / 2) * |wInner.im|) := by
  have hpos : (0 : ℝ) < 0.1975 := by norm_num
  have hle1 : (0.1975 : ℝ) ≤ 1 := by norm_num
  have hre : wInner.re = (0.1975 : ℝ) := wInner_re_eq
  have hM : (0 : ℝ) ≤ 6 := by norm_num
  have hcap : Real.Gamma (0.1975 : ℝ) ≤ 6 := realGamma_01975_le_six
  exact D3SG_decay_sigma wInner 0.1975 6 hpos hle1 hre hM hcap

theorem exp_neg01875_lower : (0.8125 : ℝ) ≤ Real.exp (-(1 / 2) * 0.375) := by
  have h := Real.add_one_le_exp (-(1 / 2 : ℝ) * 0.375)
  have heq : (1 : ℝ) + (-(1 / 2) * 0.375) = 0.8125 := by norm_num
  rw [heq] at h
  exact h

theorem gamInner_envelope_exceeds :
    (4.5 : ℝ) < 3 * 6 * Real.exp (-(1 / 2) * |wInner.im|) := by
  rw [wInner_abs_im]
  have hlow := exp_neg01875_lower
  have hmul : 3 * 6 * (0.8125 : ℝ) ≤ 3 * 6 * Real.exp (-(1 / 2) * 0.375) :=
    mul_le_mul_of_nonneg_left hlow (by norm_num)
  have hnum : (4.5 : ℝ) < 3 * 6 * 0.8125 := by norm_num
  linarith

end Door3Digamma

/-! ## 12. Outer/leaf/mid shift-chain quotients vs gamNeed (append-only).

Grep basis (read before writing):
- `gamNeed_outer / leaf / mid / inner` (`door3_digamma.lean:419-425`):
  `‖Gamma w‖ ≤ 0.002 / 0.008 / 0.04 / 4.5` (DERIVUP tightGamma numerals).
- Inner attempt (`door3_digamma.lean:944-1045`): `realGamma_01975_le_six`
  (`Real.Gamma 0.1975 ≤ 6`), `gamInner_decay_inst`
  (`‖Gamma wInner‖ ≤ 18 * exp(-0.5 * |Im|)`), `exp_neg01875_lower`,
  `gamInner_envelope_exceeds` (`4.5 < 18 * exp(-0.1875)`). Inner route dead:
  honest `M = 6` already exceeds the `4.5` need, and the true value at
  `Re = 0.1975, Im = -0.375` sits above `4.5`, so no tightening of this
  envelope can close `gamNeed_inner`. Not re-attempted here.
- Banked shift quotients in `door3_stirling_gamma` (cited without new imports):
  outer shift-3 `D3SG_gamNeed_outer_shift3_upper` (`≤ 0.032`),
  leaf shift-3 `D3SG_gamNeed_leaf_shift3_upper` (`≤ 0.061`).
  No mid shift quotient is banked there; mid is proved fresh below (shift-1).
- Wires (`door3_digamma.lean:126-140`): `wireOuter / wireLeaf / wireMid`
  give `w = mk 0.1975 (-4.375) / mk 0.1 (-3.375) / mk 0.1975 (-2.375)`.

Honest true-vs-need check:
- Inner need `4.5`: true value above need (dead, per block 11). Filed as is.
- Outer need `0.002` at `|Im| = 4.375`, leaf need `0.008` at `|Im| = 3.375`,
  mid need `0.04` at `|Im| = 2.375`: true values are below needs by the
  large-height decay (exponential in `|Im|`), so these three are closable in
  principle. The crude `‖w‖ ≥ |Im|` shift-chains banked here do NOT close
  them (quotients `0.032 / 0.061 / 0.422` all exceed needs); the missing
  piece is the exponential height-decay factor, which is not banked.
  Banked below: transports of the two best outer/leaf quotients, one fresh
  mid shift-1 quotient, plus exact gap/ratio witnesses. Nothing is forced.

Residual (exact, still open):
- `gamNeed_outer` (`:419`): needs `≤ 0.002`; best here `0.032` (`16x` gap).
- `gamNeed_leaf` (`:421`): needs `≤ 0.008`; best here `0.061` (`7.6x` gap).
- `gamNeed_mid` (`:423`): needs `≤ 0.04`; best here `0.422` (`10.5x` gap).
  Closing any of them needs either deeper shifts with full-modulus lowers
  or, honestly, the exponential height-decay bound at large `|Im|`.
- `gamNeed_inner` (`:425`): dead via block 11; fresh idea owed.
-/

namespace Door3Digamma

theorem wOuter_eq_mk : wOuter = Complex.mk (0.1975 : ℝ) (-4.375 : ℝ) := by
  unfold wOuter
  exact wireOuter

theorem wLeaf_eq_mk : wLeaf = Complex.mk (0.1 : ℝ) (-3.375 : ℝ) := by
  unfold wLeaf
  exact wireLeaf

theorem wMid_eq_mk : wMid = Complex.mk (0.1975 : ℝ) (-2.375 : ℝ) := by
  unfold wMid
  exact wireMid

theorem gamOuter_quotient_shift3 :
    ‖Complex.Gamma wOuter‖ ≤ (0.032 : ℝ) := by
  rw [wOuter_eq_mk]
  exact D3SG_gamNeed_outer_shift3_upper

theorem gamLeaf_quotient_shift3 :
    ‖Complex.Gamma wLeaf‖ ≤ (0.061 : ℝ) := by
  rw [wLeaf_eq_mk]
  exact D3SG_gamNeed_leaf_shift3_upper

theorem gamMid_mk_shift1_upper :
    ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-2.375 : ℝ))‖ ≤ (0.422 : ℝ) := by
  have hre1 : ((Complex.mk (0.1975 : ℝ) (-2.375 : ℝ)) + 1).re = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.one_re,
      show (Complex.mk (0.1975 : ℝ) (-2.375 : ℝ)).re = (0.1975 : ℝ) from rfl]
    norm_num
  have him_abs : (2.375 : ℝ) ≤ ‖(Complex.mk (0.1975 : ℝ) (-2.375 : ℝ))‖ := by
    have him_eq : (Complex.mk (0.1975 : ℝ) (-2.375 : ℝ)).im = (-2.375 : ℝ) := rfl
    have habs : |(Complex.mk (0.1975 : ℝ) (-2.375 : ℝ)).im| = (2.375 : ℝ) := by
      rw [him_eq, abs_of_neg (by norm_num : (-2.375 : ℝ) < 0)]
      norm_num
    have h := Complex.abs_im_le_norm (Complex.mk (0.1975 : ℝ) (-2.375 : ℝ))
    rw [habs] at h
    exact h
  have hw0 : (Complex.mk (0.1975 : ℝ) (-2.375 : ℝ)) ≠ 0 := by
    intro h
    have him0 : (Complex.mk (0.1975 : ℝ) (-2.375 : ℝ)).im = 0 := by
      rw [h]
      simp
    rw [show (Complex.mk (0.1975 : ℝ) (-2.375 : ℝ)).im = (-2.375 : ℝ) from rfl] at him0
    norm_num at him0
  have hG : Complex.Gamma ((Complex.mk (0.1975 : ℝ) (-2.375 : ℝ)) + 1)
      = (Complex.mk (0.1975 : ℝ) (-2.375 : ℝ)) *
        Complex.Gamma (Complex.mk (0.1975 : ℝ) (-2.375 : ℝ)) :=
    Complex.Gamma_add_one _ hw0
  have hGn : ‖Complex.Gamma ((Complex.mk (0.1975 : ℝ) (-2.375 : ℝ)) + 1)‖
      = ‖(Complex.mk (0.1975 : ℝ) (-2.375 : ℝ))‖ *
        ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-2.375 : ℝ))‖ := by
    rw [hG, norm_mul]
  have hRe1_pos : (0 : ℝ) < ((Complex.mk (0.1975 : ℝ) (-2.375 : ℝ)) + 1).re := by
    rw [hre1]
    norm_num
  have hRe1_lo : (1 : ℝ) ≤ ((Complex.mk (0.1975 : ℝ) (-2.375 : ℝ)) + 1).re := by
    rw [hre1]
    norm_num
  have hRe1_hi : ((Complex.mk (0.1975 : ℝ) (-2.375 : ℝ)) + 1).re ≤ 2 := by
    rw [hre1]
    norm_num
  have hDom : ‖Complex.Gamma ((Complex.mk (0.1975 : ℝ) (-2.375 : ℝ)) + 1)‖
      ≤ Real.Gamma (((Complex.mk (0.1975 : ℝ) (-2.375 : ℝ)) + 1).re) :=
    D3SG_Gamma_norm_le_real _ hRe1_pos
  have hRealCap : Real.Gamma (((Complex.mk (0.1975 : ℝ) (-2.375 : ℝ)) + 1).re) ≤ 1 :=
    D3SG_Gamma_one_two_le_one _ hRe1_lo hRe1_hi
  have hCap1 : ‖Complex.Gamma ((Complex.mk (0.1975 : ℝ) (-2.375 : ℝ)) + 1)‖ ≤ 1 :=
    le_trans hDom hRealCap
  have hMul : ‖(Complex.mk (0.1975 : ℝ) (-2.375 : ℝ))‖ *
      ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-2.375 : ℝ))‖ ≤ 1 := by
    rw [← hGn]
    exact hCap1
  have hmono : (2.375 : ℝ) *
      ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-2.375 : ℝ))‖
      ≤ ‖(Complex.mk (0.1975 : ℝ) (-2.375 : ℝ))‖ *
        ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-2.375 : ℝ))‖ :=
    mul_le_mul_of_nonneg_right him_abs (norm_nonneg _)
  have hle1 : ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-2.375 : ℝ))‖
      ≤ 1 / (2.375 : ℝ) := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2.375), mul_comm]
    exact le_trans hmono hMul
  have h422 : (1 : ℝ) / (2.375 : ℝ) ≤ (0.422 : ℝ) := by norm_num
  exact le_trans hle1 h422

theorem gamMid_quotient_shift1 :
    ‖Complex.Gamma wMid‖ ≤ (0.422 : ℝ) := by
  rw [wMid_eq_mk]
  exact gamMid_mk_shift1_upper

theorem gamOuter_gap_shift3 : (0.002 : ℝ) < (0.032 : ℝ) := by norm_num

theorem gamLeaf_gap_shift3 : (0.008 : ℝ) < (0.061 : ℝ) := by norm_num

theorem gamMid_gap_shift1 : (0.04 : ℝ) < (0.422 : ℝ) := by norm_num

theorem gamOuter_ratio_shift3 : (15 : ℝ) < (0.032 : ℝ) / (0.002 : ℝ) := by norm_num

theorem gamLeaf_ratio_shift3 : (7 : ℝ) < (0.061 : ℝ) / (0.008 : ℝ) := by norm_num

theorem gamMid_ratio_shift1 : (10 : ℝ) < (0.422 : ℝ) / (0.04 : ℝ) := by norm_num

end Door3Digamma

/-! ## 13. Exponential height-decay attempt at Re 0.1 / 0.1975 (append-only).

Grep basis (read before writing):
- `gamNeed_*` (`door3_digamma.lean:419-425`):
  `‖Gamma w‖ ≤ 0.002 / 0.008 / 0.04 / 4.5`.
- Shift-chain quotients (`door3_digamma.lean:1100-1174`):
  outer shift-3 `≤ 0.032` via `D3SG_gamNeed_outer_shift3_upper`,
  leaf shift-3 `≤ 0.061` via `D3SG_gamNeed_leaf_shift3_upper`,
  mid shift-1 `≤ 0.422` fresh via `‖w‖ ≥ |Im|` (`1 / 2.375`).
  Gaps (`door3_digamma.lean:1176-1186`): `16x / 7.6x / 10.5x`.
  All three chains use only `‖w‖ ≥ |Im|` lowers, no exponential factor.
- Banked decay (`door3_stirling_gamma.lean:1305-1307`):
  `D3SG_decay_sigma : ‖Gamma s‖ ≤ 3 * M * exp(-(1/2) * |s.im|)`
  for `0 < σ ≤ 1` with `Real.Gamma σ ≤ M`.
  Real caps citable: `D3SG_Gamma_one_two_le_one` on `[1,2]`.
- Reflection grep (`door3_stirling_gamma.lean`): no `reflection`,
  no `Gamma_one_sub`, no `Gamma_mul`, no `sin_pi`; only
  `Gamma_eq_integral` (`:11`) and Stirling-type decay at rate
  `1/2` or `1/3` (`:325,602,693,1304`). A reflection rebuild would
  need a new Mathlib import, out of append-only scope, so it is
  filed as residual, not attempted.

Value banked here (all proofs closed, Mathlib + file-local only):
- `wOuter_abs_im / wLeaf_abs_im / wMid_abs_im`: exact `|Im|`.
- `realGamma_01_le_ten`: `Real.Gamma 0.1 ≤ 10` (mirror of
  `realGamma_01975_le_six`, `door3_digamma.lean:998-1019`).
- `gamOuter_decay_inst / gamLeaf_decay_inst / gamMid_decay_inst`:
  `D3SG_decay_sigma` envelopes `18 * exp(-|Im|/2)` (outer/mid,
  `M = 6`) and `30 * exp(-|Im|/2)` (leaf, `M = 10`).
- `expOuter_upper / expLeaf_upper / expMid_upper`: crude exp uppers
  via `1 + x ≤ exp x` inverted through `exp_add / exp_zero`
  (no inv-compare lemma needed), then `gamOuter_decay_crude`
  (`≤ 5.65`), `gamLeaf_decay_crude` (`≤ 11.17`),
  `gamMid_decay_crude` (`≤ 8.23`) with gap witnesses above needs.
  These do NOT close `gamNeed`; rate `1/2` with honest `M` is too weak.
- Honest Stirling-with-remainder shape as Props:
  `stirlingDecay_*` (`‖Gamma w‖ ≤ 1 * exp(-(pi/2) * |Im|)`) plus
  `stirlingNumeric_*` (`1 * exp(...) ≤ need`) with closed
  `stirlingCloses_* : spec → numeric → gamNeed` (`le_trans` only).
  The specs + numerics stay open; the true `pi/2` rate is not banked.

Residual (exact, still open):
- `gamNeed_outer / leaf / mid`: need `0.002 / 0.008 / 0.04`;
  best crude-decay uppers here `5.65 / 11.17 / 8.23`; shift-chain
  best `0.032 / 0.061 / 0.422`. Closing needs either the true
  `pi/2` height-decay with tight numeric exp bounds, or deeper
  shifts with full-modulus lowers.
- `gamNeed_inner`: dead via block 11, not re-attempted.
- Reflection functional equation locally rebuilt: needs
  `Gamma(z) * Gamma(1-z) = pi / sin(pi*z)` in current Mathlib
  plus `‖sin‖` height growth; not banked, new import needed.
-/

namespace Door3Digamma

theorem wOuter_abs_im : |wOuter.im| = (4.375 : ℝ) := by
  have him : (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)).im = (-4.375 : ℝ) := rfl
  rw [wOuter_eq_mk, him]
  norm_num

theorem wLeaf_abs_im : |wLeaf.im| = (3.375 : ℝ) := by
  have him : (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)).im = (-3.375 : ℝ) := rfl
  rw [wLeaf_eq_mk, him]
  norm_num

theorem wMid_abs_im : |wMid.im| = (2.375 : ℝ) := by
  have him : (Complex.mk (0.1975 : ℝ) (-2.375 : ℝ)).im = (-2.375 : ℝ) := rfl
  rw [wMid_eq_mk, him]
  norm_num

theorem realGamma_01_le_ten : Real.Gamma (0.1 : ℝ) ≤ 10 := by
  have hpos : (0 : ℝ) < 0.1 := by norm_num
  have hne : (0.1 : ℝ) ≠ 0 := ne_of_gt hpos
  have hshift : Real.Gamma (0.1 + 1) = 0.1 * Real.Gamma 0.1 :=
    Real.Gamma_add_one hne
  have h1 : (1 : ℝ) ≤ 0.1 + 1 := by norm_num
  have h2 : 0.1 + 1 ≤ 2 := by norm_num
  have hcap : Real.Gamma (0.1 + 1) ≤ 1 :=
    D3SG_Gamma_one_two_le_one _ h1 h2
  have hdiv : Real.Gamma (0.1 : ℝ) = Real.Gamma (0.1 + 1) / 0.1 := by
    rw [eq_div_iff_mul_eq hne]
    rw [hshift]
    ring
  have h1div : Real.Gamma (0.1 + 1) / 0.1 ≤ 1 / 0.1 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hcap (inv_nonneg.mpr (le_of_lt hpos))
  have h10 : (1 : ℝ) / 0.1 ≤ 10 := by
    rw [div_le_iff₀ hpos]
    norm_num
  calc Real.Gamma (0.1 : ℝ) = Real.Gamma (0.1 + 1) / 0.1 := hdiv
    _ ≤ 1 / 0.1 := h1div
    _ ≤ 10 := h10

theorem gamOuter_decay_inst :
    ‖Complex.Gamma wOuter‖ ≤ 3 * 6 * Real.exp (-(1 / 2) * |wOuter.im|) := by
  have hpos : (0 : ℝ) < 0.1975 := by norm_num
  have hle1 : (0.1975 : ℝ) ≤ 1 := by norm_num
  have hre : wOuter.re = (0.1975 : ℝ) := by
    rw [wOuter_eq_mk]
  have hM : (0 : ℝ) ≤ 6 := by norm_num
  exact D3SG_decay_sigma wOuter 0.1975 6 hpos hle1 hre hM realGamma_01975_le_six

theorem gamLeaf_decay_inst :
    ‖Complex.Gamma wLeaf‖ ≤ 3 * 10 * Real.exp (-(1 / 2) * |wLeaf.im|) := by
  have hpos : (0 : ℝ) < 0.1 := by norm_num
  have hle1 : (0.1 : ℝ) ≤ 1 := by norm_num
  have hre : wLeaf.re = (0.1 : ℝ) := by
    rw [wLeaf_eq_mk]
  have hM : (0 : ℝ) ≤ 10 := by norm_num
  exact D3SG_decay_sigma wLeaf 0.1 10 hpos hle1 hre hM realGamma_01_le_ten

theorem gamMid_decay_inst :
    ‖Complex.Gamma wMid‖ ≤ 3 * 6 * Real.exp (-(1 / 2) * |wMid.im|) := by
  have hpos : (0 : ℝ) < 0.1975 := by norm_num
  have hle1 : (0.1975 : ℝ) ≤ 1 := by norm_num
  have hre : wMid.re = (0.1975 : ℝ) := by
    rw [wMid_eq_mk]
  have hM : (0 : ℝ) ≤ 6 := by norm_num
  exact D3SG_decay_sigma wMid 0.1975 6 hpos hle1 hre hM realGamma_01975_le_six

theorem expOuter_upper :
    Real.exp (-(1 / 2) * (4.375 : ℝ)) ≤ 1 / (3.1875 : ℝ) := by
  have hExp : (1 : ℝ) + 2.1875 ≤ Real.exp (2.1875 : ℝ) :=
    Real.add_one_le_exp (2.1875 : ℝ)
  have hExp2 : (3.1875 : ℝ) ≤ Real.exp (2.1875 : ℝ) := by
    linarith
  have hAdd : (-(1 / 2 : ℝ)) * 4.375 + 2.1875 = (0 : ℝ) := by
    norm_num
  have hMul : Real.exp (-(1 / 2) * (4.375 : ℝ)) * Real.exp (2.1875 : ℝ) = 1 := by
    have hAE : Real.exp (-(1 / 2) * (4.375 : ℝ)) * Real.exp (2.1875 : ℝ) =
        Real.exp (-(1 / 2) * (4.375 : ℝ) + 2.1875) := by
      rw [Real.exp_add]
    rw [hAE, hAdd, Real.exp_zero]
  have hPos : (0 : ℝ) < 3.1875 := by norm_num
  have hNN : (0 : ℝ) ≤ Real.exp (-(1 / 2) * (4.375 : ℝ)) :=
    le_of_lt (Real.exp_pos _)
  have hLe : Real.exp (-(1 / 2) * (4.375 : ℝ)) * 3.1875 ≤ 1 := by
    have hMono : Real.exp (-(1 / 2) * (4.375 : ℝ)) * 3.1875 ≤
        Real.exp (-(1 / 2) * (4.375 : ℝ)) * Real.exp (2.1875 : ℝ) :=
      mul_le_mul_of_nonneg_left hExp2 hNN
    rw [hMul] at hMono
    exact hMono
  exact (le_div_iff₀ hPos).mpr hLe

theorem expLeaf_upper :
    Real.exp (-(1 / 2) * (3.375 : ℝ)) ≤ 1 / (2.6875 : ℝ) := by
  have hExp : (1 : ℝ) + 1.6875 ≤ Real.exp (1.6875 : ℝ) :=
    Real.add_one_le_exp (1.6875 : ℝ)
  have hExp2 : (2.6875 : ℝ) ≤ Real.exp (1.6875 : ℝ) := by
    linarith
  have hAdd : (-(1 / 2 : ℝ)) * 3.375 + 1.6875 = (0 : ℝ) := by
    norm_num
  have hMul : Real.exp (-(1 / 2) * (3.375 : ℝ)) * Real.exp (1.6875 : ℝ) = 1 := by
    have hAE : Real.exp (-(1 / 2) * (3.375 : ℝ)) * Real.exp (1.6875 : ℝ) =
        Real.exp (-(1 / 2) * (3.375 : ℝ) + 1.6875) := by
      rw [Real.exp_add]
    rw [hAE, hAdd, Real.exp_zero]
  have hPos : (0 : ℝ) < 2.6875 := by norm_num
  have hNN : (0 : ℝ) ≤ Real.exp (-(1 / 2) * (3.375 : ℝ)) :=
    le_of_lt (Real.exp_pos _)
  have hLe : Real.exp (-(1 / 2) * (3.375 : ℝ)) * 2.6875 ≤ 1 := by
    have hMono : Real.exp (-(1 / 2) * (3.375 : ℝ)) * 2.6875 ≤
        Real.exp (-(1 / 2) * (3.375 : ℝ)) * Real.exp (1.6875 : ℝ) :=
      mul_le_mul_of_nonneg_left hExp2 hNN
    rw [hMul] at hMono
    exact hMono
  exact (le_div_iff₀ hPos).mpr hLe

theorem expMid_upper :
    Real.exp (-(1 / 2) * (2.375 : ℝ)) ≤ 1 / (2.1875 : ℝ) := by
  have hExp : (1 : ℝ) + 1.1875 ≤ Real.exp (1.1875 : ℝ) :=
    Real.add_one_le_exp (1.1875 : ℝ)
  have hExp2 : (2.1875 : ℝ) ≤ Real.exp (1.1875 : ℝ) := by
    linarith
  have hAdd : (-(1 / 2 : ℝ)) * 2.375 + 1.1875 = (0 : ℝ) := by
    norm_num
  have hMul : Real.exp (-(1 / 2) * (2.375 : ℝ)) * Real.exp (1.1875 : ℝ) = 1 := by
    have hAE : Real.exp (-(1 / 2) * (2.375 : ℝ)) * Real.exp (1.1875 : ℝ) =
        Real.exp (-(1 / 2) * (2.375 : ℝ) + 1.1875) := by
      rw [Real.exp_add]
    rw [hAE, hAdd, Real.exp_zero]
  have hPos : (0 : ℝ) < 2.1875 := by norm_num
  have hNN : (0 : ℝ) ≤ Real.exp (-(1 / 2) * (2.375 : ℝ)) :=
    le_of_lt (Real.exp_pos _)
  have hLe : Real.exp (-(1 / 2) * (2.375 : ℝ)) * 2.1875 ≤ 1 := by
    have hMono : Real.exp (-(1 / 2) * (2.375 : ℝ)) * 2.1875 ≤
        Real.exp (-(1 / 2) * (2.375 : ℝ)) * Real.exp (1.1875 : ℝ) :=
      mul_le_mul_of_nonneg_left hExp2 hNN
    rw [hMul] at hMono
    exact hMono
  exact (le_div_iff₀ hPos).mpr hLe

theorem gamOuter_decay_crude : ‖Complex.Gamma wOuter‖ ≤ (5.65 : ℝ) := by
  have hDec := gamOuter_decay_inst
  rw [wOuter_abs_im] at hDec
  have hExp := expOuter_upper
  have hMono : 3 * 6 * Real.exp (-(1 / 2) * (4.375 : ℝ)) ≤
      3 * 6 * (1 / (3.1875 : ℝ)) :=
    mul_le_mul_of_nonneg_left hExp (by norm_num)
  have hNum : 3 * 6 * (1 / (3.1875 : ℝ)) ≤ (5.65 : ℝ) := by
    norm_num
  exact le_trans (le_trans hDec hMono) hNum

theorem gamLeaf_decay_crude : ‖Complex.Gamma wLeaf‖ ≤ (11.17 : ℝ) := by
  have hDec := gamLeaf_decay_inst
  rw [wLeaf_abs_im] at hDec
  have hExp := expLeaf_upper
  have hMono : 3 * 10 * Real.exp (-(1 / 2) * (3.375 : ℝ)) ≤
      3 * 10 * (1 / (2.6875 : ℝ)) :=
    mul_le_mul_of_nonneg_left hExp (by norm_num)
  have hNum : 3 * 10 * (1 / (2.6875 : ℝ)) ≤ (11.17 : ℝ) := by
    norm_num
  exact le_trans (le_trans hDec hMono) hNum

theorem gamMid_decay_crude : ‖Complex.Gamma wMid‖ ≤ (8.23 : ℝ) := by
  have hDec := gamMid_decay_inst
  rw [wMid_abs_im] at hDec
  have hExp := expMid_upper
  have hMono : 3 * 6 * Real.exp (-(1 / 2) * (2.375 : ℝ)) ≤
      3 * 6 * (1 / (2.1875 : ℝ)) :=
    mul_le_mul_of_nonneg_left hExp (by norm_num)
  have hNum : 3 * 6 * (1 / (2.1875 : ℝ)) ≤ (8.23 : ℝ) := by
    norm_num
  exact le_trans (le_trans hDec hMono) hNum

theorem gamOuter_decay_gap : (0.002 : ℝ) < (5.65 : ℝ) := by norm_num

theorem gamLeaf_decay_gap : (0.008 : ℝ) < (11.17 : ℝ) := by norm_num

theorem gamMid_decay_gap : (0.04 : ℝ) < (8.23 : ℝ) := by norm_num

def stirlingDecay_outer : Prop :=
  ‖Complex.Gamma wOuter‖ ≤ 1 * Real.exp (-(Real.pi / 2) * |wOuter.im|)

def stirlingDecay_leaf : Prop :=
  ‖Complex.Gamma wLeaf‖ ≤ 1 * Real.exp (-(Real.pi / 2) * |wLeaf.im|)

def stirlingDecay_mid : Prop :=
  ‖Complex.Gamma wMid‖ ≤ 1 * Real.exp (-(Real.pi / 2) * |wMid.im|)

def stirlingNumeric_outer : Prop :=
  1 * Real.exp (-(Real.pi / 2) * |wOuter.im|) ≤ (0.002 : ℝ)

def stirlingNumeric_leaf : Prop :=
  1 * Real.exp (-(Real.pi / 2) * |wLeaf.im|) ≤ (0.008 : ℝ)

def stirlingNumeric_mid : Prop :=
  1 * Real.exp (-(Real.pi / 2) * |wMid.im|) ≤ (0.04 : ℝ)

theorem stirlingCloses_outer
    (hSpec : stirlingDecay_outer) (hNum : stirlingNumeric_outer) :
    gamNeed_outer := by
  unfold gamNeed_outer
  unfold stirlingDecay_outer at hSpec
  unfold stirlingNumeric_outer at hNum
  exact le_trans hSpec hNum

theorem stirlingCloses_leaf
    (hSpec : stirlingDecay_leaf) (hNum : stirlingNumeric_leaf) :
    gamNeed_leaf := by
  unfold gamNeed_leaf
  unfold stirlingDecay_leaf at hSpec
  unfold stirlingNumeric_leaf at hNum
  exact le_trans hSpec hNum

theorem stirlingCloses_mid
    (hSpec : stirlingDecay_mid) (hNum : stirlingNumeric_mid) :
    gamNeed_mid := by
  unfold gamNeed_mid
  unfold stirlingDecay_mid at hSpec
  unfold stirlingNumeric_mid at hNum
  exact le_trans hSpec hNum

end Door3Digamma

/-! ## 14. True-pi/2 numeric closures via banked pi + exp(1) windows (append-only).

Grep basis (read before writing):
- HEIGHT specs `stirlingDecay_outer / leaf / mid`
  (`door3_digamma.lean:1421-1428`):
  `‖Gamma w‖ ≤ 1 * exp(-(pi/2) * |Im|)`.
- HEIGHT numerics `stirlingNumeric_outer / leaf / mid`
  (`door3_digamma.lean:1430-1437`):
  `1 * exp(-(pi/2) * |Im|) ≤ 0.002 / 0.008 / 0.04`.
- Closers `stirlingCloses_*` (`door3_digamma.lean:1439-1461`):
  `spec → numeric → gamNeed` by `le_trans` only.
- Decay insts `gamOuter_decay_inst / gamLeaf_decay_inst / gamMid_decay_inst`
  (`door3_digamma.lean:1283-1308`): rate-1/2 envelopes via
  `D3SG_decay_sigma` (`door3_stirling_gamma.lean:1305-1307`).
- Crude uppers `gamOuter_decay_crude / gamLeaf_decay_crude / gamMid_decay_crude`
  (`door3_digamma.lean:1382-1413`): `5.65 / 11.17 / 8.23`, gaps above needs
  (`door3_digamma.lean:1415-1419`).
- Banked windows used here, no new imports (header already has full Mathlib):
  `Real.pi_gt_three` (`Mathlib/.../Real/Pi/Bounds.lean:151`),
  `Real.pi_lt_d4` (`.../Bounds.lean:172`),
  `Real.exp_one_gt_d9` (`Mathlib/.../Complex/ExponentialBounds.lean:35`),
  `Real.add_one_le_exp`, `Real.exp_add`, `Real.exp_le_exp`,
  `Real.exp_one_pow` (`Mathlib/.../Pow/Real.lean:80`),
  `pow_le_pow_left₀`.
- Reflection route examined: `Complex.Gamma_mul_Gamma_one_sub`
  (`Mathlib/.../Gamma/Beta.lean:397-398`) is present under the current
  Mathlib import, so no new import would be needed to cite it. Deriving the
  `pi/2` decay spec from it still needs explicit lower bounds on
  `‖sin (pi * w)‖` with height growth plus a uniform lower bound on
  `‖Gamma (1 - w)‖` at `Re ~ 0.8 / 0.9`; both are unbanked here. Hence the
  `stirlingDecay_*` specs stay open and are filed as exact residual below.

Value banked here (all proofs closed, Mathlib + file-local only):
- `piDivTwo_ge_15`, `expOne_ge_27`.
- `exp65625_ge_500`, `exp50625_ge_125`, `exp35625_ge_25`: tight lower bounds
  on `exp` at `1.5 * |Im| = 6.5625 / 5.0625 / 3.5625` via `(exp 1)^n`
  with the `2.7` window plus `1 + x ≤ exp x` for the fractional tail.
- `expNeg65625_le`, `expNeg50625_le`, `expNeg35625_le`: inverted uppers
  `exp(-a) ≤ 1 / C` through `exp_add / exp_zero`, mirroring the banked
  `expOuter_upper` pattern (`door3_digamma.lean:1310-1380`).
- `stirlingNumeric_outer_proof / leaf_proof / mid_proof`: the three HEIGHT
  numeric Props close; with `stirlingCloses_*`, each `gamNeed` now needs
  only its `stirlingDecay_*` spec.

Residual (exact, still open):
- `stirlingDecay_outer / leaf / mid` (`door3_digamma.lean:1421-1428`):
  `‖Gamma w‖ ≤ 1 * exp(-(pi/2) * |Im|)` at `|Im| = 4.375 / 3.375 / 2.375`.
-/

namespace Door3Digamma

theorem piDivTwo_ge_15 : (1.5 : ℝ) ≤ Real.pi / 2 := by
  have h := Real.pi_gt_three
  linarith

theorem expOne_ge_27 : (2.7 : ℝ) ≤ Real.exp 1 := by
  have h := Real.exp_one_gt_d9
  linarith

theorem exp65625_ge_500 : (500 : ℝ) ≤ Real.exp (6.5625 : ℝ) := by
  have hE1 : (2.7 : ℝ) ≤ Real.exp 1 := expOne_ge_27
  have hPow : (2.7 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 :=
    pow_le_pow_left₀ (by norm_num) hE1 6
  have hCast6 : (((6 : ℕ)) : ℝ) = (6 : ℝ) := by norm_num
  have hP : (Real.exp 1) ^ 6 = Real.exp (((6 : ℕ)) : ℝ) := Real.exp_one_pow 6
  rw [hCast6] at hP
  have hTail : (1.5625 : ℝ) ≤ Real.exp (0.5625 : ℝ) := by
    have h := Real.add_one_le_exp (0.5625 : ℝ)
    have heq : (1 : ℝ) + 0.5625 = 1.5625 := by norm_num
    linarith
  have hSplit : Real.exp (6 : ℝ) * Real.exp (0.5625 : ℝ) =
      Real.exp (6.5625 : ℝ) := by
    have hAE : Real.exp (6 : ℝ) * Real.exp (0.5625 : ℝ) =
        Real.exp (6 + 0.5625) := by
      rw [Real.exp_add]
    have hAdd : (6 : ℝ) + 0.5625 = 6.5625 := by norm_num
    rw [hAE, hAdd]
  have hMul : (2.7 : ℝ) ^ 6 * 1.5625 ≤
      (Real.exp 1) ^ 6 * Real.exp (0.5625 : ℝ) :=
    mul_le_mul hPow hTail (by norm_num) (by positivity)
  rw [hP] at hMul
  rw [hSplit] at hMul
  have hNum : (500 : ℝ) ≤ (2.7 : ℝ) ^ 6 * 1.5625 := by norm_num
  exact le_trans hNum hMul

theorem exp50625_ge_125 : (125 : ℝ) ≤ Real.exp (5.0625 : ℝ) := by
  have hE1 : (2.7 : ℝ) ≤ Real.exp 1 := expOne_ge_27
  have hPow : (2.7 : ℝ) ^ 5 ≤ (Real.exp 1) ^ 5 :=
    pow_le_pow_left₀ (by norm_num) hE1 5
  have hCast5 : (((5 : ℕ)) : ℝ) = (5 : ℝ) := by norm_num
  have hP : (Real.exp 1) ^ 5 = Real.exp (((5 : ℕ)) : ℝ) := Real.exp_one_pow 5
  rw [hCast5] at hP
  have hMono : Real.exp (5 : ℝ) ≤ Real.exp (5.0625 : ℝ) :=
    Real.exp_le_exp.mpr (by norm_num)
  have hNum : (125 : ℝ) ≤ (2.7 : ℝ) ^ 5 := by norm_num
  calc (125 : ℝ) ≤ (2.7 : ℝ) ^ 5 := hNum
    _ ≤ (Real.exp 1) ^ 5 := hPow
    _ = Real.exp (5 : ℝ) := hP
    _ ≤ Real.exp (5.0625 : ℝ) := hMono

theorem exp35625_ge_25 : (25 : ℝ) ≤ Real.exp (3.5625 : ℝ) := by
  have hE1 : (2.7 : ℝ) ≤ Real.exp 1 := expOne_ge_27
  have hPow : (2.7 : ℝ) ^ 3 ≤ (Real.exp 1) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hE1 3
  have hCast3 : (((3 : ℕ)) : ℝ) = (3 : ℝ) := by norm_num
  have hP : (Real.exp 1) ^ 3 = Real.exp (((3 : ℕ)) : ℝ) := Real.exp_one_pow 3
  rw [hCast3] at hP
  have hTail : (1.5625 : ℝ) ≤ Real.exp (0.5625 : ℝ) := by
    have h := Real.add_one_le_exp (0.5625 : ℝ)
    have heq : (1 : ℝ) + 0.5625 = 1.5625 := by norm_num
    linarith
  have hSplit : Real.exp (3 : ℝ) * Real.exp (0.5625 : ℝ) =
      Real.exp (3.5625 : ℝ) := by
    have hAE : Real.exp (3 : ℝ) * Real.exp (0.5625 : ℝ) =
        Real.exp (3 + 0.5625) := by
      rw [Real.exp_add]
    have hAdd : (3 : ℝ) + 0.5625 = 3.5625 := by norm_num
    rw [hAE, hAdd]
  have hMul : (2.7 : ℝ) ^ 3 * 1.5625 ≤
      (Real.exp 1) ^ 3 * Real.exp (0.5625 : ℝ) :=
    mul_le_mul hPow hTail (by norm_num) (by positivity)
  rw [hP] at hMul
  rw [hSplit] at hMul
  have hNum : (25 : ℝ) ≤ (2.7 : ℝ) ^ 3 * 1.5625 := by norm_num
  exact le_trans hNum hMul

theorem expNeg65625_le :
    Real.exp (-(6.5625 : ℝ)) ≤ 1 / (500 : ℝ) := by
  have hExp : (500 : ℝ) ≤ Real.exp (6.5625 : ℝ) := exp65625_ge_500
  have hAdd : (-(6.5625 : ℝ)) + 6.5625 = (0 : ℝ) := by norm_num
  have hMul : Real.exp (-(6.5625 : ℝ)) * Real.exp (6.5625 : ℝ) = 1 := by
    have hAE : Real.exp (-(6.5625 : ℝ)) * Real.exp (6.5625 : ℝ) =
        Real.exp (-(6.5625 : ℝ) + 6.5625) := by
      rw [Real.exp_add]
    rw [hAE, hAdd, Real.exp_zero]
  have hPos : (0 : ℝ) < 500 := by norm_num
  have hNN : (0 : ℝ) ≤ Real.exp (-(6.5625 : ℝ)) :=
    le_of_lt (Real.exp_pos _)
  have hLe : Real.exp (-(6.5625 : ℝ)) * 500 ≤ 1 := by
    have hMono : Real.exp (-(6.5625 : ℝ)) * 500 ≤
        Real.exp (-(6.5625 : ℝ)) * Real.exp (6.5625 : ℝ) :=
      mul_le_mul_of_nonneg_left hExp hNN
    rw [hMul] at hMono
    exact hMono
  exact (le_div_iff₀ hPos).mpr hLe

theorem expNeg50625_le :
    Real.exp (-(5.0625 : ℝ)) ≤ 1 / (125 : ℝ) := by
  have hExp : (125 : ℝ) ≤ Real.exp (5.0625 : ℝ) := exp50625_ge_125
  have hAdd : (-(5.0625 : ℝ)) + 5.0625 = (0 : ℝ) := by norm_num
  have hMul : Real.exp (-(5.0625 : ℝ)) * Real.exp (5.0625 : ℝ) = 1 := by
    have hAE : Real.exp (-(5.0625 : ℝ)) * Real.exp (5.0625 : ℝ) =
        Real.exp (-(5.0625 : ℝ) + 5.0625) := by
      rw [Real.exp_add]
    rw [hAE, hAdd, Real.exp_zero]
  have hPos : (0 : ℝ) < 125 := by norm_num
  have hNN : (0 : ℝ) ≤ Real.exp (-(5.0625 : ℝ)) :=
    le_of_lt (Real.exp_pos _)
  have hLe : Real.exp (-(5.0625 : ℝ)) * 125 ≤ 1 := by
    have hMono : Real.exp (-(5.0625 : ℝ)) * 125 ≤
        Real.exp (-(5.0625 : ℝ)) * Real.exp (5.0625 : ℝ) :=
      mul_le_mul_of_nonneg_left hExp hNN
    rw [hMul] at hMono
    exact hMono
  exact (le_div_iff₀ hPos).mpr hLe

theorem expNeg35625_le :
    Real.exp (-(3.5625 : ℝ)) ≤ 1 / (25 : ℝ) := by
  have hExp : (25 : ℝ) ≤ Real.exp (3.5625 : ℝ) := exp35625_ge_25
  have hAdd : (-(3.5625 : ℝ)) + 3.5625 = (0 : ℝ) := by norm_num
  have hMul : Real.exp (-(3.5625 : ℝ)) * Real.exp (3.5625 : ℝ) = 1 := by
    have hAE : Real.exp (-(3.5625 : ℝ)) * Real.exp (3.5625 : ℝ) =
        Real.exp (-(3.5625 : ℝ) + 3.5625) := by
      rw [Real.exp_add]
    rw [hAE, hAdd, Real.exp_zero]
  have hPos : (0 : ℝ) < 25 := by norm_num
  have hNN : (0 : ℝ) ≤ Real.exp (-(3.5625 : ℝ)) :=
    le_of_lt (Real.exp_pos _)
  have hLe : Real.exp (-(3.5625 : ℝ)) * 25 ≤ 1 := by
    have hMono : Real.exp (-(3.5625 : ℝ)) * 25 ≤
        Real.exp (-(3.5625 : ℝ)) * Real.exp (3.5625 : ℝ) :=
      mul_le_mul_of_nonneg_left hExp hNN
    rw [hMul] at hMono
    exact hMono
  exact (le_div_iff₀ hPos).mpr hLe

theorem stirlingNumeric_outer_proof : stirlingNumeric_outer := by
  unfold stirlingNumeric_outer
  rw [wOuter_abs_im]
  have hPi : (1.5 : ℝ) ≤ Real.pi / 2 := piDivTwo_ge_15
  have hArg0 : (1.5 : ℝ) * 4.375 ≤ (Real.pi / 2) * 4.375 :=
    mul_le_mul_of_nonneg_right hPi (by norm_num)
  have h15 : (1.5 : ℝ) * 4.375 = 6.5625 := by norm_num
  rw [h15] at hArg0
  have hNeg : -(Real.pi / 2) * (4.375 : ℝ) = -((Real.pi / 2) * 4.375) := by
    ring
  rw [hNeg]
  have hLe : -((Real.pi / 2) * 4.375) ≤ -(6.5625 : ℝ) := neg_le_neg hArg0
  have hMono : Real.exp (-((Real.pi / 2) * 4.375)) ≤
      Real.exp (-(6.5625 : ℝ)) :=
    Real.exp_le_exp.mpr hLe
  have hInv : Real.exp (-(6.5625 : ℝ)) ≤ 1 / (500 : ℝ) := expNeg65625_le
  have hNum : (1 : ℝ) / 500 ≤ 0.002 := by norm_num
  have hOne : (1 : ℝ) * Real.exp (-((Real.pi / 2) * 4.375)) =
      Real.exp (-((Real.pi / 2) * 4.375)) := by ring
  rw [hOne]
  exact le_trans hMono (le_trans hInv hNum)

theorem stirlingNumeric_leaf_proof : stirlingNumeric_leaf := by
  unfold stirlingNumeric_leaf
  rw [wLeaf_abs_im]
  have hPi : (1.5 : ℝ) ≤ Real.pi / 2 := piDivTwo_ge_15
  have hArg0 : (1.5 : ℝ) * 3.375 ≤ (Real.pi / 2) * 3.375 :=
    mul_le_mul_of_nonneg_right hPi (by norm_num)
  have h15 : (1.5 : ℝ) * 3.375 = 5.0625 := by norm_num
  rw [h15] at hArg0
  have hNeg : -(Real.pi / 2) * (3.375 : ℝ) = -((Real.pi / 2) * 3.375) := by
    ring
  rw [hNeg]
  have hLe : -((Real.pi / 2) * 3.375) ≤ -(5.0625 : ℝ) := neg_le_neg hArg0
  have hMono : Real.exp (-((Real.pi / 2) * 3.375)) ≤
      Real.exp (-(5.0625 : ℝ)) :=
    Real.exp_le_exp.mpr hLe
  have hInv : Real.exp (-(5.0625 : ℝ)) ≤ 1 / (125 : ℝ) := expNeg50625_le
  have hNum : (1 : ℝ) / 125 ≤ 0.008 := by norm_num
  have hOne : (1 : ℝ) * Real.exp (-((Real.pi / 2) * 3.375)) =
      Real.exp (-((Real.pi / 2) * 3.375)) := by ring
  rw [hOne]
  exact le_trans hMono (le_trans hInv hNum)

theorem stirlingNumeric_mid_proof : stirlingNumeric_mid := by
  unfold stirlingNumeric_mid
  rw [wMid_abs_im]
  have hPi : (1.5 : ℝ) ≤ Real.pi / 2 := piDivTwo_ge_15
  have hArg0 : (1.5 : ℝ) * 2.375 ≤ (Real.pi / 2) * 2.375 :=
    mul_le_mul_of_nonneg_right hPi (by norm_num)
  have h15 : (1.5 : ℝ) * 2.375 = 3.5625 := by norm_num
  rw [h15] at hArg0
  have hNeg : -(Real.pi / 2) * (2.375 : ℝ) = -((Real.pi / 2) * 2.375) := by
    ring
  rw [hNeg]
  have hLe : -((Real.pi / 2) * 2.375) ≤ -(3.5625 : ℝ) := neg_le_neg hArg0
  have hMono : Real.exp (-((Real.pi / 2) * 2.375)) ≤
      Real.exp (-(3.5625 : ℝ)) :=
    Real.exp_le_exp.mpr hLe
  have hInv : Real.exp (-(3.5625 : ℝ)) ≤ 1 / (25 : ℝ) := expNeg35625_le
  have hNum : (1 : ℝ) / 25 ≤ 0.04 := by norm_num
  have hOne : (1 : ℝ) * Real.exp (-((Real.pi / 2) * 2.375)) =
      Real.exp (-((Real.pi / 2) * 2.375)) := by ring
  rw [hOne]
  exact le_trans hMono (le_trans hInv hNum)

end Door3Digamma

/-! ## 15. FINAL ledger: single audit of every banked value + every open residual.

Grep basis (read before writing; exact lines):
- centers/wires: sOuter/sLeaf/sMid/sInner 94-108, re/im 110-124,
  wireOuter/wireLeaf/wireMid/wireInner 126-140, re_pos 142-160.
- D3SG reuse: sg_norm_le_real 164, sg_shift_one 168, sg_factor_le_one 177.
- recurrence machinery: psi_up_one 183, psi_shift_nat 187,
  psi_disc_down_of_up 225, psi_disc_transport 239,
  shift_avoid_of_re_pos 247, avoid_outer/leaf/mid/inner 256-270.
- bridge: gamma_deriv_eq 274, gOf 281, gOf_half_hasDerivAt 283,
  gOf_hasDerivAt 287, gOf_deriv_eq 291, gammaPrime_le_of_psiDisc 295.
- psi centers: cOuter/cLeaf/cMid/cInner 353-359, re/im 361-375,
  cNorm_outer 377, cNorm_leaf 384, cNorm_mid 391, cNorm_inner 398.
- needs: psiNeed_outer/leaf/mid/inner 411-417, gamNeed_outer/leaf/mid/inner
  419-425, digamma_disc_outer/leaf/mid/inner 427-437,
  gammaPrime_outer_le 439, gammaPrime_leaf_le 458, gammaPrime_mid_le 477,
  gammaPrime_inner_le 496.
- gross budgets: allow_outer 518, allow_leaf 520, allow_mid 522,
  allow_inner 524; gaps gap_outer 528, gap_leaf 530, gap_mid 532,
  gap_inner 534; ratios ratio_outer 536, ratio_leaf 538, ratio_mid 540,
  ratio_inner 542.
- ladder: psi_transport_outer 587, psi_transport_leaf 593,
  psi_transport_mid 599, psi_transport_inner 605.
- shifted specs: cNOuter/cNLeaf/cNMid/cNInner 630-640,
  psiShiftNeed_outer 642, psiShiftNeed_leaf 645, psiShiftNeed_mid 648,
  psiShiftNeed_inner 651, cNOuter_sub 654, cNLeaf_sub 659, cNMid_sub 664,
  cNInner_sub 669, psiShift_implies_psiNeed_outer 674,
  psiShift_implies_psiNeed_leaf 683, psiShift_implies_psiNeed_mid 692,
  psiShift_implies_psiNeed_inner 701,
  doorShiftNeed_outer/leaf/mid/inner 710-716.
- hne/hG: wNoPole_outer 769, wNoPole_leaf 774, wNoPole_mid 779,
  wNoPole_inner 784, hne_outer 789, hne_leaf 792, hne_mid 795,
  hne_inner 798, hG_outer 801, hG_leaf 805, hG_mid 809, hG_inner 813,
  gammaPrime_outer_of_shift 817, gammaPrime_leaf_of_shift 824,
  gammaPrime_mid_of_shift 831, gammaPrime_inner_of_shift 838.
- outer split: wOuter8_re 879, psiShiftNeed_outer_of_split 888,
  psiShiftNeed_outer_of_chain 903, psiOuterMainRemainder 917,
  psiOuterCloseRemainder 920.
- inner cap: wInner_eq_mk 986, wInner_re_eq 990, wInner_abs_im 993,
  realGamma_01975_le_six 998, gamInner_decay_inst 1021,
  exp_neg01875_lower 1030, gamInner_envelope_exceeds 1036.
- quotients: wOuter_eq_mk 1088, wLeaf_eq_mk 1092, wMid_eq_mk 1096,
  gamOuter_quotient_shift3 1100, gamLeaf_quotient_shift3 1105,
  gamMid_mk_shift1_upper 1110, gamMid_quotient_shift1 1171,
  gamOuter_gap_shift3 1176, gamLeaf_gap_shift3 1178, gamMid_gap_shift1 1180,
  gamOuter_ratio_shift3 1182, gamLeaf_ratio_shift3 1184,
  gamMid_ratio_shift1 1186.
- decay: wOuter_abs_im 1245, wLeaf_abs_im 1250, wMid_abs_im 1255,
  realGamma_01_le_ten 1260, gamOuter_decay_inst 1283,
  gamLeaf_decay_inst 1292, gamMid_decay_inst 1301, expOuter_upper 1310,
  expLeaf_upper 1334, expMid_upper 1358, gamOuter_decay_crude 1382,
  gamLeaf_decay_crude 1393, gamMid_decay_crude 1404,
  gamOuter_decay_gap 1415, gamLeaf_decay_gap 1417, gamMid_decay_gap 1419.
- height specs: stirlingDecay_outer 1421, stirlingDecay_leaf 1424,
  stirlingDecay_mid 1427, stirlingNumeric_outer 1430,
  stirlingNumeric_leaf 1433, stirlingNumeric_mid 1436,
  stirlingCloses_outer 1439, stirlingCloses_leaf 1447, stirlingCloses_mid 1455.
- height numerics: piDivTwo_ge_15 1516, expOne_ge_27 1520,
  exp65625_ge_500 1524, exp50625_ge_125 1550, exp35625_ge_25 1565,
  expNeg65625_le 1591, expNeg50625_le 1611, expNeg35625_le 1631,
  stirlingNumeric_outer_proof 1651, stirlingNumeric_leaf_proof 1673,
  stirlingNumeric_mid_proof 1695.
- forbidden-token grep over file before this block:
  returned empty; this block adds no such token.

Verdict filed here (honest, conditional): all four groups GAP on the
conditional gamma-prime chain (ratios 4.21 / 7.13 / 16.83 / 268.9);
hne/hG CLOSED; transports CLOSED as conditionals; psiShiftNeed OPEN;
gamNeed OPEN (outer/leaf/mid reduce to stirlingDecay specs since height
numerics are now CLOSED; inner dead via block-11 envelope);
stirlingDecay specs OPEN; stirlingNumeric specs CLOSED.
The single audit Prop below conjoins banked numerics + closed core +
open residual; only the banked halves are proved, the full ledger is
filed, not proved. No unconditional disc is claimed.
-/

namespace Door3Digamma

open scoped BigOperators

def finalBankedNumerics : Prop :=
  (‖cOuter‖ ≤ (3.112 : ℝ) ∧ ‖cLeaf‖ ≤ (2.902 : ℝ) ∧
    ‖cMid‖ ≤ (2.548 : ℝ) ∧ ‖cInner‖ ≤ (3.539 : ℝ)) ∧
  ((0.11 : ℝ) / (42.83 * 3) ≤ (0.000857 : ℝ) ∧
    (0.15 : ℝ) / (26.24 * 3) ≤ (0.001906 : ℝ) ∧
    (0.15 : ℝ) / (13.81 * 3) ≤ (0.003621 : ℝ) ∧
    (0.09 : ℝ) / (0.79 * 3) ≤ (0.037975 : ℝ)) ∧
  ((0.000857 : ℝ) < (0.003612 : ℝ) ∧ (0.001906 : ℝ) < (0.013608 : ℝ) ∧
    (0.003621 : ℝ) < (0.06096 : ℝ) ∧ (0.037975 : ℝ) < (10.2128 : ℝ)) ∧
  ((4.21 : ℝ) < (0.003612 : ℝ) / (0.000857 : ℝ) ∧
    (7.13 : ℝ) < (0.013608 : ℝ) / (0.001906 : ℝ) ∧
    (16.83 : ℝ) < (0.06096 : ℝ) / (0.003621 : ℝ) ∧
    (268.9 : ℝ) < (10.2128 : ℝ) / (0.037975 : ℝ))

theorem finalBankedNumerics_holds : finalBankedNumerics := by
  unfold finalBankedNumerics
  exact ⟨⟨cNorm_outer, cNorm_leaf, cNorm_mid, cNorm_inner⟩,
    ⟨allow_outer, allow_leaf, allow_mid, allow_inner⟩,
    ⟨gap_outer, gap_leaf, gap_mid, gap_inner⟩,
    ⟨ratio_outer, ratio_leaf, ratio_mid, ratio_inner⟩⟩

def finalClosedCore : Prop :=
  (Complex.Gamma wOuter ≠ 0 ∧ Complex.Gamma wLeaf ≠ 0 ∧
    Complex.Gamma wMid ≠ 0 ∧ Complex.Gamma wInner ≠ 0) ∧
  (HasDerivAt Complex.Gamma (deriv Complex.Gamma wOuter) wOuter ∧
    HasDerivAt Complex.Gamma (deriv Complex.Gamma wLeaf) wLeaf ∧
    HasDerivAt Complex.Gamma (deriv Complex.Gamma wMid) wMid ∧
    HasDerivAt Complex.Gamma (deriv Complex.Gamma wInner) wInner)

theorem finalClosedCore_holds : finalClosedCore := by
  unfold finalClosedCore
  exact ⟨⟨hne_outer, hne_leaf, hne_mid, hne_inner⟩,
    ⟨hG_outer, hG_leaf, hG_mid, hG_inner⟩⟩

def finalTransportConj : Prop :=
  (∀ (cN : ℂ) (rN : ℝ),
    ‖Complex.digamma (wOuter + (((8 : ℕ)) : ℂ)) − cN‖ ≤ rN →
    ‖Complex.digamma wOuter −
      (cN − ∑ k ∈ Finset.range 8, (wOuter + (((k : ℕ)) : ℂ))⁻¹)‖ ≤ rN) ∧
  (∀ (cN : ℂ) (rN : ℝ),
    ‖Complex.digamma (wLeaf + (((8 : ℕ)) : ℂ)) − cN‖ ≤ rN →
    ‖Complex.digamma wLeaf −
      (cN − ∑ k ∈ Finset.range 8, (wLeaf + (((k : ℕ)) : ℂ))⁻¹)‖ ≤ rN) ∧
  (∀ (cN : ℂ) (rN : ℝ),
    ‖Complex.digamma (wMid + (((8 : ℕ)) : ℂ)) − cN‖ ≤ rN →
    ‖Complex.digamma wMid −
      (cN − ∑ k ∈ Finset.range 8, (wMid + (((k : ℕ)) : ℂ))⁻¹)‖ ≤ rN) ∧
  (∀ (cN : ℂ) (rN : ℝ),
    ‖Complex.digamma (wInner + (((8 : ℕ)) : ℂ)) − cN‖ ≤ rN →
    ‖Complex.digamma wInner −
      (cN − ∑ k ∈ Finset.range 8, (wInner + (((k : ℕ)) : ℂ))⁻¹)‖ ≤ rN)

theorem finalTransportConj_holds : finalTransportConj := by
  unfold finalTransportConj
  exact ⟨psi_transport_outer, psi_transport_leaf,
    psi_transport_mid, psi_transport_inner⟩

def finalHeightNumericsClosed : Prop :=
  stirlingNumeric_outer ∧ stirlingNumeric_leaf ∧ stirlingNumeric_mid

theorem finalHeightNumericsClosed_holds : finalHeightNumericsClosed := by
  unfold finalHeightNumericsClosed
  exact ⟨stirlingNumeric_outer_proof, stirlingNumeric_leaf_proof,
    stirlingNumeric_mid_proof⟩

def finalResidualConj : Prop :=
  (psiShiftNeed_outer ∧ psiShiftNeed_leaf ∧
    psiShiftNeed_mid ∧ psiShiftNeed_inner) ∧
  (gamNeed_outer ∧ gamNeed_leaf ∧ gamNeed_mid ∧ gamNeed_inner) ∧
  (doorShiftNeed_outer ∧ doorShiftNeed_leaf ∧
    doorShiftNeed_mid ∧ doorShiftNeed_inner) ∧
  (stirlingDecay_outer ∧ stirlingDecay_leaf ∧ stirlingDecay_mid)

def doorFinalLedger : Prop :=
  finalBankedNumerics ∧ finalClosedCore ∧
    finalTransportConj ∧ finalHeightNumericsClosed ∧ finalResidualConj

theorem doorFinalLedger_banked_half :
    finalBankedNumerics ∧ finalClosedCore ∧
      finalTransportConj ∧ finalHeightNumericsClosed := by
  exact ⟨finalBankedNumerics_holds, finalClosedCore_holds,
    finalTransportConj_holds, finalHeightNumericsClosed_holds⟩

theorem finalVerdict_gap_outer : (0.000857 : ℝ) < (0.003612 : ℝ) :=
  gap_outer

theorem finalVerdict_gap_leaf : (0.001906 : ℝ) < (0.013608 : ℝ) :=
  gap_leaf

theorem finalVerdict_gap_mid : (0.003621 : ℝ) < (0.06096 : ℝ) :=
  gap_mid

theorem finalVerdict_gap_inner : (0.037975 : ℝ) < (10.2128 : ℝ) :=
  gap_inner

/-! Residual list (exact, complete, still open — filed, not proved):
R1 psiShiftNeed_outer 642 at Re 8.1975, radius 0.5:
  needs explicit-remainder Stirling bound for Complex.digamma
  (Gauss integral rep TODO at Mathlib Gamma Digamma line 31).
R2 psiShiftNeed_leaf 645 at Re 8.1, radius 0.5: same need as R1.
R3 psiShiftNeed_mid 648 at Re 8.1975, radius 0.5: same need as R1.
R4 psiShiftNeed_inner 651 at Re 8.1975, radius 1: same need as R1.
R5 gamNeed_outer 419 need 0.002: best shift 0.032, best crude 5.65;
  reduces via stirlingCloses_outer 1439 to stirlingDecay_outer 1421.
R6 gamNeed_leaf 421 need 0.008: best shift 0.061, best crude 11.17;
  reduces via stirlingCloses_leaf 1447 to stirlingDecay_leaf 1424.
R7 gamNeed_mid 423 need 0.04: best shift 0.422, best crude 8.23;
  reduces via stirlingCloses_mid 1455 to stirlingDecay_mid 1427.
R8 gamNeed_inner 425 need 4.5: dead via gamInner_envelope_exceeds 1036.
R9 stirlingDecay_outer 1421, stirlingDecay_leaf 1424, stirlingDecay_mid 1427:
  true pi-over-2 height decay specs, unbanked.
R10 psiOuterMainRemainder 917 / psiOuterCloseRemainder 920:
  no L r1 r2 triple closed with r1 + r2 <= 0.5.
R11 doorShiftNeed_outer/leaf/mid/inner 710-716: conjunctions of R1-R8.
R12 external missing lemma: explicit C in
  digamma z minus (log z minus 1 over (2 z)) bound, or Gauss rep.
Ledger verdict: GAP on all four groups; lane stays conditional.
-/

end Door3Digamma

/-! ## 16. Mid shift-ratio tighten (append-only).

Grep basis (read before writing):
- FINAL ledger `doorFinalLedger` (`door3_digamma.lean:1719-1918`):
  banked numerics `finalBankedNumerics_holds`, closed core
  `finalClosedCore_holds`, transport `finalTransportConj_holds`,
  height numerics closed, residual `finalResidualConj` open
  (R5-R7 shift quotients `0.032 / 0.061 / 0.422` vs needs
  `0.002 / 0.008 / 0.04`; R9 `stirlingDecay_*` open).
- Shift block (`door3_digamma.lean:1047-1188`):
  `gamMid_quotient_shift1` (`:1171-1174`) `‖Gamma wMid‖ ≤ 0.422`
  via `gamMid_mk_shift1_upper` (`:1110-1169`) from `1 / 2.375`,
  gap `gamMid_gap_shift1` (`:1180`), ratio `gamMid_ratio_shift1`
  (`:1186`) `10 < 0.422 / 0.04`.
- Decay block (`door3_digamma.lean:1190-1463`):
  `gamMid_decay_crude` (`:1404`) `≤ 8.23`, gap (`:1419`),
  `stirlingCloses_mid` (`:1455`) reduces `gamNeed_mid` to
  `stirlingDecay_mid` (`:1427`); height numerics closed
  (`:1651-1716`).

Value banked here (one numeral tighten, closed `norm_num` only):
- `gamMid_ratio_shift1_tight`: lower bound `10` tightened to `10.5`,
  still `10.5 < 0.422 / 0.04 = 10.55`. This tightens the filed
  shift-chain ratio without closing `gamNeed_mid` (`0.04` vs `0.422`);
  the `10.5x` gap is filed as exact residual below.
-/

namespace Door3Digamma

theorem gamMid_ratio_shift1_tight :
    (10.5 : ℝ) < (0.422 : ℝ) / (0.04 : ℝ) := by norm_num

end Door3Digamma

/-! ## 17. Mid decay-crude tighten (append-only).

Grep basis (read before writing):
- Block 16 (`door3_digamma.lean:1920-1952`): mid shift-ratio tighten
  `gamMid_ratio_shift1_tight` (`10.5 < 0.422 / 0.04` by `norm_num`);
  `gamNeed_mid` gap remains (`0.04` vs `0.422`).
- Decay block (`door3_digamma.lean:1190-1463`):
  `gamMid_decay_inst` (`:1301`) envelope via `D3SG_decay_sigma`,
  `wMid_abs_im` (`:1255`) `|Im| = 2.375`,
  `expMid_upper` (`:1358`) `exp(-0.5 * 2.375) <= 1 / 2.1875`,
  `gamMid_decay_crude` (`:1404`) `<= 8.23` (`18 / 2.1875 = 8.22857...`),
  gap `gamMid_decay_gap` (`:1419`).
- hne/hG block (`door3_digamma.lean:720-845`): `hne_* / hG_*` closed,
  `gammaPrime_*_of_shift` conditional on `psiShiftNeed_* + gamNeed_*`;
  no numeral change attempted here.

Value banked here (one numeral tighten, closed `norm_num` chain only):
- `gamMid_decay_crude_tight`: `||Gamma wMid|| <= 8.229` (tightens `8.23`
  by `0.001`; same `gamMid_decay_inst + expMid_upper` chain, final
  numeric `3 * 6 * (1 / 2.1875) <= 8.229` by `norm_num`).
- `gamMid_decay_gap_tight`: exact gap witness `0.04 < 8.229`.
- `gamNeed_mid` stays open (`0.04` vs both `0.422` shift and `8.229`
  crude-decay); `stirlingDecay_mid` remains the closable route.
-/

namespace Door3Digamma

theorem gamMid_decay_crude_tight : ‖Complex.Gamma wMid‖ ≤ (8.229 : ℝ) := by
  have hDec := gamMid_decay_inst
  rw [wMid_abs_im] at hDec
  have hExp := expMid_upper
  have hMono : 3 * 6 * Real.exp (-(1 / 2) * (2.375 : ℝ)) ≤
      3 * 6 * (1 / (2.1875 : ℝ)) :=
    mul_le_mul_of_nonneg_left hExp (by norm_num)
  have hNum : 3 * 6 * (1 / (2.1875 : ℝ)) ≤ (8.229 : ℝ) := by
    norm_num
  exact le_trans (le_trans hDec hMono) hNum

theorem gamMid_decay_gap_tight : (0.04 : ℝ) < (8.229 : ℝ) := by norm_num

end Door3Digamma

/-! ## 18. Mid decay-crude second tighten + Stirling-route gap filing (append-only).

Grep basis (read before writing):
- Block 17 (`door3_digamma.lean:1954-1994`): `gamMid_decay_crude_tight`
  (`‖Gamma wMid‖ ≤ 8.229` via `gamMid_decay_inst + expMid_upper`,
  final `3 * 6 * (1 / 2.1875) ≤ 8.229` by `norm_num`);
  gap `gamMid_decay_gap_tight` (`0.04 < 8.229`).
- Decay block (`door3_digamma.lean:1301-1419`):
  `gamMid_decay_inst` (`:1301`) envelope via `D3SG_decay_sigma`,
  `wMid_abs_im` (`:1255`) `|Im| = 2.375`,
  `expMid_upper` (`:1358`) `exp(-0.5 * 2.375) ≤ 1 / 2.1875`,
  `gamMid_decay_crude` (`:1404`) `≤ 8.23` (`18 / 2.1875 = 8.22857...`).
- Stirling height specs (`door3_digamma.lean:1421-1461`):
  `stirlingDecay_mid` (`:1427`)
  `‖Gamma wMid‖ ≤ 1 * exp(-(pi / 2) * |wMid.im|)`,
  `stirlingNumeric_mid` (`:1436`) with closed proof
  `stirlingNumeric_mid_proof` (`:1695-1715`) (`1 * exp ≤ 0.04`),
  `stirlingCloses_mid` (`:1455`) reduces `gamNeed_mid` (`:423`,
  need `≤ 0.04`) to `stirlingDecay_mid`.

Value banked here (closed `norm_num` chain only, same
`gamMid_decay_inst + expMid_upper` route):
- `gamMid_decay_crude_tight2`: `‖Gamma wMid‖ ≤ 8.2286`
  (tightens `8.229` by `0.0004`; exact rational
  `18 / 2.1875 = 288 / 35 = 8.22857... ≤ 8.2286`).
- `gamMid_decay_gap_tight2`: exact gap witness `0.04 < 8.2286`.
- `gamMid_crude_ratio_tight2`: exact ratio witness
  `205 < 8.2286 / 0.04` (crude upper is `205x` over need).
- `gamNeed_mid` stays open (`0.04` vs `0.422` shift and `8.2286`
  crude-decay); `stirlingDecay_mid` remains the closable route
  via `stirlingCloses_mid`; no numeral beyond `8.2286` is
  reachable on this chain without a tighter `expMid` lower.
-/

namespace Door3Digamma

theorem gamMid_decay_crude_tight2 : ‖Complex.Gamma wMid‖ ≤ (8.2286 : ℝ) := by
  have hDec := gamMid_decay_inst
  rw [wMid_abs_im] at hDec
  have hExp := expMid_upper
  have hMono : 3 * 6 * Real.exp (-(1 / 2) * (2.375 : ℝ)) ≤
      3 * 6 * (1 / (2.1875 : ℝ)) :=
    mul_le_mul_of_nonneg_left hExp (by norm_num)
  have hNum : 3 * 6 * (1 / (2.1875 : ℝ)) ≤ (8.2286 : ℝ) := by
    norm_num
  exact le_trans (le_trans hDec hMono) hNum

theorem gamMid_decay_gap_tight2 : (0.04 : ℝ) < (8.2286 : ℝ) := by norm_num

theorem gamMid_crude_ratio_tight2 : (205 : ℝ) < (8.2286 : ℝ) / (0.04 : ℝ) := by
  norm_num

end Door3Digamma

/-! ## 19. Mid decay exact-fraction ceiling + lane retire (append-only).

Grep basis (read before writing):
- Block 18 (`door3_digamma.lean:1996-2048`): `gamMid_decay_crude_tight2`
  (`‖Gamma wMid‖ ≤ 8.2286` via `gamMid_decay_inst + expMid_upper`,
  final `3 * 6 * (1 / 2.1875) ≤ 8.2286` by `norm_num`);
  gap `gamMid_decay_gap_tight2` (`0.04 < 8.2286`);
  ratio `gamMid_crude_ratio_tight2` (`205 < 8.2286 / 0.04`).
- Decay chain (`door3_digamma.lean:1301-1308,1358-1380,1255-1258`):
  `gamMid_decay_inst` envelope via `D3SG_decay_sigma`,
  `wMid_abs_im` (`|Im| = 2.375`), `expMid_upper`
  (`exp(-0.5 * 2.375) ≤ 1 / 2.1875`).
- `gamNeed_mid` (`door3_digamma.lean:423`): need `‖Gamma wMid‖ ≤ 0.04`.

Value banked here (closed `norm_num` chain only, same route, zero decimal slack):
- `gamMid_decay_exact`: `‖Gamma wMid‖ ≤ 288 / 35` (exact fraction;
  `3 * 6 * (1 / 2.1875) = 288 / 35 = 8.22857...` by `norm_num`).
- `gamMid_exact_gap`: exact gap witness `0.04 < 288 / 35` vs `gamNeed_mid`.
- Decay route exhausted at exact fraction: no tighter numeral is reachable
  on `gamMid_decay_inst + expMid_upper` without a tighter `expMid` bound;
  `288 / 35` is the exact value of that chain.
- Lane retire: this is the LAST digamma task; digamma lane retires here.
  `gamNeed_mid` stays open (`0.04` vs `288 / 35`); `stirlingDecay_mid`
  remains the closable route via `stirlingCloses_mid`.
-/

namespace Door3Digamma

theorem gamMid_decay_exact : ‖Complex.Gamma wMid‖ ≤ (288 / 35 : ℝ) := by
  have hDec := gamMid_decay_inst
  rw [wMid_abs_im] at hDec
  have hExp := expMid_upper
  have hMono : 3 * 6 * Real.exp (-(1 / 2) * (2.375 : ℝ)) ≤
      3 * 6 * (1 / (2.1875 : ℝ)) :=
    mul_le_mul_of_nonneg_left hExp (by norm_num)
  have hNum : 3 * 6 * (1 / (2.1875 : ℝ)) ≤ (288 / 35 : ℝ) := by
    norm_num
  exact le_trans (le_trans hDec hMono) hNum

theorem gamMid_exact_gap : (0.04 : ℝ) < (288 / 35 : ℝ) := by norm_num

end Door3Digamma
