import Mathlib
import door3_stirling_gamma

/-!
# Door-3 Stirling remainder: Wendel real two-sided bound + reflection lower bridge.

WRITE-ONLY appendage (report-and-stop). No build command run. No commit / push.
`door3_stirling_rem.lean` was verified absent via glob before writing.
`door3_stirling_gamma.lean:1` imports `Mathlib` only, so the import graph stays a DAG.
This file imports `Mathlib` + `door3_stirling_gamma` only.

## Recon (read-only, brief — route-determining)

* Euler-Maclaurin: NO match in Mathlib (`EulerMaclaurin` / `euler_maclaurin`
  absent). Route (i) (EM summation of log Gamma from scratch) is out.
* `Complex.logGamma` / `Real.logGamma`: absent as API. Only internal
  `BohrMollerup.logGammaSeq` exists. No Stirling series with remainder for Gamma.
* Existing Stirling: only `Mathlib/.../Stirling.lean` for `Nat.factorial`
  (`stirlingSeq`, limit `sqrt pi`). No complex-Gamma asymptotics.
* Wendel / Gautschi: absent. But BOTH ingredients are banked:
  `Real.Gamma_add_one` (Basic.lean) and `Real.convexOn_log_Gamma`
  (BohrMollerup.lean), plus real monotonicity
  (`Real.Gamma_strictAntiOn_Ioc`, `Real.Gamma_strictMonoOn_Ici`) and the
  reflection formula `Complex.Gamma_mul_Gamma_one_sub` (Beta.lean).
* Taylor: `taylor_mean_remainder_lagrange` / `cauchy` / integral forms exist
  but only for real functions; not directly usable for complex log Gamma.
* Sibling digamma residual (`door3_digamma.lean` header): unconditional psi
  discs need (1) Gauss integral rep for `Complex.digamma` (Mathlib TODO,
  unbanked), (2) Stirling expansion of log Gamma with explicit remainder
  (unbanked). Verdict there: unconditional discs STOP; file banks conditional
  transport machinery instead.
* `D3SG_*` decay line scope: uniform UPPER lane only —
  `D3SG_TierC_gamma_wide`: `‖Gamma s‖ ≤ 600 * exp (-(1/2) * |s.im|)` for
  `Re ∈ [0.005, 0.95]`; sharper `≤ 3 * exp (-|Im|/2)` and
  `≤ 5 * exp (-log 2 * |Im|)` on `Re = 0.95`; real caps
  (`Gamma 0.95 ≤ 1.1`, `Gamma ≤ 20` on `[0.05, 0.95]`, `≤ 1` on `[1,2]`).
  No LOWER anywhere. Rate `1/2` (resp. `log 2 ≈ 0.69`), NOT `pi/2`.

## Verdict: route (iv) — Wendel from recurrence + log-convexity, both banked.

Full `c * |y|^{x-1/2} * exp (-pi * |y| / 2)` lower needs reflection (BANKED)
plus a complex sine upper (NOT catalogued) plus the polynomial factor from a
Stirling remainder (unbanked). That exceeds the fragment budget, so this file
lands the biggest provable fragment:

* (A) Wendel two-sided real bound with explicit polynomial factors
  (upper + lower + combined + log form + finite-difference slope form).
* (B) Unconditional real Gamma lowers from banked monotonicity
  (`1 ≤ Gamma` on `(0,1]` and `[2,∞)`, `1/2 ≤ Gamma` on `[1,2]` and `(0,2]`).
* (C) ONE complex consequence: reflection lower bridge
  (`‖Gamma z‖ ≥ pi / (‖sin‖ * ‖Gamma (1-z)‖)`) instantiated on the Tier-C
  strip with the banked `D3SG_TierC_gamma_wide` upper, leaving the sine norm
  as an explicit premise `S` (composes with the chi-file sine uppers).

All proofs full, explicit binders, small numerals only.
-/

namespace Door3StirlingRem

/-! ## 1. Log-form Wendel (core convexity computation). -/

/-- Log-form Wendel upper: `log Gamma (x+s) ≤ log Gamma x + s * log x`. -/
theorem D3SR_logGamma_wendel (x s : ℝ) (hx : 0 < x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.log (Real.Gamma (x + s)) ≤ Real.log (Real.Gamma x) + s * Real.log x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hGx : (0 : ℝ) < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hGxne : Real.Gamma x ≠ 0 := ne_of_gt hGx
  have hmem1 : x ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr hx
  have hmem2 : (x + 1) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr hx1
  have ha : (0 : ℝ) ≤ 1 - s := by linarith
  have hab : (1 - s) + s = 1 := by ring
  have hJ := Real.convexOn_log_Gamma.2 hmem1 hmem2 ha hs0 hab
  simp only [smul_eq_mul, Function.comp_apply] at hJ
  have hpt : (1 - s) * x + s * (x + 1) = x + s := by ring
  rw [hpt] at hJ
  have hG1 : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one hxne
  have hlog1 : Real.log (Real.Gamma (x + 1))
      = Real.log x + Real.log (Real.Gamma x) := by
    rw [hG1, Real.log_mul hxne hGxne]
  rw [hlog1] at hJ
  calc Real.log (Real.Gamma (x + s))
      ≤ (1 - s) * Real.log (Real.Gamma x)
        + s * (Real.log x + Real.log (Real.Gamma x)) := hJ
    _ = Real.log (Real.Gamma x) + s * Real.log x := by ring

/-! ## 2. Wendel upper, lower, and two-sided real bound. -/

/-- Wendel upper: `Gamma (x+s) ≤ x^s * Gamma x` for `x > 0`, `s ∈ [0,1]`. -/
theorem D3SR_wendel_upper (x s : ℝ) (hx : 0 < x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.Gamma (x + s) ≤ (x ^ s) * Real.Gamma x := by
  have hxs : (0 : ℝ) < x + s := by linarith
  have hGx : (0 : ℝ) < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hGxs : (0 : ℝ) < Real.Gamma (x + s) := Real.Gamma_pos_of_pos hxs
  have hlog := D3SR_logGamma_wendel x s hx hs0 hs1
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_add, Real.exp_log hGx, Real.exp_log hGxs] at hexp
  have erpow : Real.exp (s * Real.log x) = x ^ s := by
    rw [mul_comm s (Real.log x), Real.rpow_def_of_pos hx s]
  rw [erpow] at hexp
  calc Real.Gamma (x + s) ≤ Real.Gamma x * x ^ s := hexp
    _ = (x ^ s) * Real.Gamma x := by ring

/-- Wendel lower (multiplicative form): `x * Gamma x ≤ (x+s)^(1-s) * Gamma (x+s)`.
Proved by applying the upper bound at `x+s` with increment `1-s`. -/
theorem D3SR_wendel_lower (x s : ℝ) (hx : 0 < x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    x * Real.Gamma x ≤ ((x + s) ^ (1 - s)) * Real.Gamma (x + s) := by
  have hxs : (0 : ℝ) < x + s := by linarith
  have h1s0 : (0 : ℝ) ≤ 1 - s := by linarith
  have h1s1 : 1 - s ≤ 1 := by linarith
  have hup := D3SR_wendel_upper (x + s) (1 - s) hxs h1s0 h1s1
  have hcomb : (x + s) + (1 - s) = x + 1 := by ring
  rw [hcomb] at hup
  have hG1 : Real.Gamma (x + 1) = x * Real.Gamma x :=
    Real.Gamma_add_one (ne_of_gt hx)
  rw [hG1] at hup
  exact hup

/-- Wendel two-sided real bound (combined statement). -/
theorem D3SR_wendel_two_sided (x s : ℝ) (hx : 0 < x) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    x * Real.Gamma x ≤ ((x + s) ^ (1 - s)) * Real.Gamma (x + s) ∧
      Real.Gamma (x + s) ≤ (x ^ s) * Real.Gamma x :=
  And.intro (D3SR_wendel_lower x s hx hs0 hs1) (D3SR_wendel_upper x s hx hs0 hs1)

/-- Finite-difference slope control (psi-feeding fragment without limits):
`(log Gamma (x+s) - log Gamma x) / s ≤ log x`. -/
theorem D3SR_logGamma_slope_le (x s : ℝ) (hx : 0 < x) (hs0 : 0 < s)
    (hs1 : s ≤ 1) :
    (Real.log (Real.Gamma (x + s)) - Real.log (Real.Gamma x)) / s
      ≤ Real.log x := by
  have h := D3SR_logGamma_wendel x s hx (le_of_lt hs0) hs1
  have he : s * Real.log x = Real.log x * s := mul_comm _ _
  rw [div_le_iff₀ hs0]
  linarith

/-! ## 3. Unconditional real Gamma lowers from banked monotonicity. -/

/-- `1 ≤ Gamma x` on `(0,1]` (banked strict-antitone lane). -/
theorem D3SR_gamma_ge_one_Ioc (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    1 ≤ Real.Gamma x := by
  have hmem : x ∈ Set.Ioc (0 : ℝ) 1 := Set.mem_Ioc.mpr ⟨hx0, hx1⟩
  have h1mem : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 :=
    Set.mem_Ioc.mpr ⟨by norm_num, le_rfl⟩
  have h := Real.Gamma_strictAntiOn_Ioc.antitoneOn hmem h1mem hx1
  rw [Real.Gamma_one] at h
  exact h

/-- `1 ≤ Gamma x` on `[2,∞)` (banked strict-monotone lane). -/
theorem D3SR_gamma_ge_one_Ici (x : ℝ) (hx : 2 ≤ x) :
    1 ≤ Real.Gamma x := by
  have hmem : x ∈ Set.Ici (2 : ℝ) := Set.mem_Ici.mpr hx
  have h2mem : (2 : ℝ) ∈ Set.Ici (2 : ℝ) := Set.mem_Ici.mpr le_rfl
  have h := Real.Gamma_strictMonoOn_Ici.monotoneOn h2mem hmem hx
  rw [Real.Gamma_two] at h
  exact h

/-- `1/2 ≤ Gamma x` on `[1,2]` (one shift down from the `[2,∞)` lower). -/
theorem D3SR_gamma_ge_half_Icc12 (x : ℝ) (h1 : 1 ≤ x) (h2 : x ≤ 2) :
    1 / 2 ≤ Real.Gamma x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hshift : Real.Gamma (x + 1) = x * Real.Gamma x :=
    Real.Gamma_add_one hxne
  have hcap : (1 : ℝ) ≤ Real.Gamma (x + 1) :=
    D3SR_gamma_ge_one_Ici (x + 1) (by linarith)
  have hdiv : Real.Gamma x = Real.Gamma (x + 1) / x := by
    rw [eq_div_iff_mul_eq hxne, hshift]
    ring
  have hle : (1 : ℝ) / x ≤ Real.Gamma (x + 1) / x := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hcap (inv_nonneg.mpr (le_of_lt hx0))
  have h2inv : (1 : ℝ) / 2 ≤ 1 / x := one_div_le_one_div_of_le hx0 h2
  calc (1 : ℝ) / 2 ≤ 1 / x := h2inv
    _ ≤ Real.Gamma (x + 1) / x := hle
    _ = Real.Gamma x := hdiv.symm

/-- Uniform `1/2 ≤ Gamma x` on `(0,2]`. -/
theorem D3SR_gamma_ge_half_pos_le_two (x : ℝ) (hx0 : 0 < x) (hx2 : x ≤ 2) :
    1 / 2 ≤ Real.Gamma x := by
  by_cases h1 : x ≤ 1
  · have h := D3SR_gamma_ge_one_Ioc x hx0 h1
    linarith
  · have h1' : 1 ≤ x := le_of_not_ge h1
    exact D3SR_gamma_ge_half_Icc12 x h1' hx2

/-! ## 4. Complex lower via reflection (one complex consequence). -/

/-- Reflection lower bridge: with a sine-upper premise `S` and a
`Gamma (1-z)`-upper premise `G`,
`‖Gamma z‖ ≥ pi / (S * G)`. Pure norm algebra over the banked
`Complex.Gamma_mul_Gamma_one_sub`. -/
theorem D3SR_gamma_lower_of_refl (z : ℂ)
    (hsin : Complex.sin (Real.pi * z) ≠ 0)
    (hG : Complex.Gamma (1 - z) ≠ 0) :
    Real.pi / (‖Complex.sin (Real.pi * z)‖ * ‖Complex.Gamma (1 - z)‖) ≤
      ‖Complex.Gamma z‖ := by
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  have hsinNorm : (0 : ℝ) < ‖Complex.sin (Real.pi * z)‖ :=
    lt_of_le_of_ne' (norm_nonneg _) (Ne.symm (norm_ne_zero_iff.mpr hsin))
  have hGNorm : (0 : ℝ) < ‖Complex.Gamma (1 - z)‖ :=
    lt_of_le_of_ne' (norm_nonneg _) (Ne.symm (norm_ne_zero_iff.mpr hG))
  have hpi : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi :=
    Complex.norm_of_nonneg (le_of_lt Real.pi_pos)
  have hnorm : ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ =
      Real.pi / ‖Complex.sin (Real.pi * z)‖ := by
    have h := congrArg Norm.norm hrefl
    rw [norm_mul, norm_div, hpi] at h
    exact h
  have heq : ‖Complex.Gamma z‖ =
      Real.pi / (‖Complex.sin (Real.pi * z)‖ * ‖Complex.Gamma (1 - z)‖) := by
    rw [eq_div_iff_mul_eq (ne_of_gt (mul_pos hsinNorm hGNorm))]
    have h2 : ‖Complex.Gamma z‖
          * (‖Complex.sin (Real.pi * z)‖ * ‖Complex.Gamma (1 - z)‖)
        = (‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖)
          * ‖Complex.sin (Real.pi * z)‖ := by
      ring
    rw [h2, hnorm, div_mul_cancel₀ _ (ne_of_gt hsinNorm)]
  exact le_of_eq heq.symm

/-- Tier-C instantiation: on `Re ∈ [0.05, 0.95]` the reflected upper is the
banked `D3SG_TierC_gamma_wide` (`≤ 600 * exp (-|Im|/2)`); the sine norm stays
an explicit premise `S`. Closed lower with constants `pi / 600`:
`‖Gamma s‖ ≥ pi / (S * (600 * exp (-|Im|/2)))`. -/
theorem D3SR_gamma_lower_TierC_of_sin (s : ℂ)
    (hlo : 0.05 ≤ s.re) (hhi : s.re ≤ 0.95)
    (S : ℝ) (hS : ‖Complex.sin (Real.pi * s)‖ ≤ S)
    (hSpos : 0 < S)
    (hsin : Complex.sin (Real.pi * s) ≠ 0)
    (hG : Complex.Gamma (1 - s) ≠ 0) :
    Real.pi / (S * (600 * Real.exp (-(1 / 2) * |s.im|))) ≤
      ‖Complex.Gamma s‖ := by
  have hre1 : (1 - s).re = 1 - s.re := by simp
  have him0 : (1 - s).im = -(s.im) := by simp
  have him1 : |(1 - s).im| = |s.im| := by rw [him0, abs_neg]
  have hlo1 : (0.05 : ℝ) ≤ (1 - s).re := by rw [hre1]; linarith
  have hhi1 : (1 - s).re ≤ (0.95 : ℝ) := by rw [hre1]; linarith
  have hGup := D3SG_TierC_gamma_wide (1 - s) hlo1 hhi1
  rw [him1] at hGup
  have hbase := D3SR_gamma_lower_of_refl s hsin hG
  have hSnn : (0 : ℝ) ≤ S := le_of_lt hSpos
  have hden : ‖Complex.sin (Real.pi * s)‖ * ‖Complex.Gamma (1 - s)‖ ≤
      S * (600 * Real.exp (-(1 / 2) * |s.im|)) :=
    mul_le_mul hS hGup (norm_nonneg _) hSnn
  have hsinNorm : (0 : ℝ) < ‖Complex.sin (Real.pi * s)‖ :=
    lt_of_le_of_ne' (norm_nonneg _) (Ne.symm (norm_ne_zero_iff.mpr hsin))
  have hGNorm : (0 : ℝ) < ‖Complex.Gamma (1 - s)‖ :=
    lt_of_le_of_ne' (norm_nonneg _) (Ne.symm (norm_ne_zero_iff.mpr hG))
  have hBIG : (0 : ℝ) < S * (600 * Real.exp (-(1 / 2) * |s.im|)) :=
    mul_pos hSpos (by positivity)
  have hle : Real.pi / (S * (600 * Real.exp (-(1 / 2) * |s.im|))) ≤
      Real.pi / (‖Complex.sin (Real.pi * s)‖ * ‖Complex.Gamma (1 - s)‖) := by
    rw [div_le_div_left Real.pi_pos hBIG (mul_pos hsinNorm hGNorm)]
    exact hden
  exact le_trans hle hbase

/-! ## 5. Residual (precise missing pieces, per-cell extension notes).

* Real Wendel (A) is closed above with explicit polynomial factors
  `x^s` (upper) and `(x+s)^(1-s)` (lower). It feeds real-side gamma
  arguments (recurrence chains, base caps) but carries no `Im` dependence,
  so it does not by itself lower-bound `|Gamma (x + iy)|`.
* Complex bridge (C) is closed with constants `pi / 600` on the Tier-C
  strip `Re ∈ [0.05, 0.95]`, modulo the sine premise `S`.
  Missing lemma M1 (name): an explicit catalogued upper
  `‖Complex.sin (Real.pi * s)‖ ≤ Real.exp (Real.pi * |s.im|)`
  (or the `cosh` refinement) in Mathlib complex trigonometry. Once M1 lands,
  (C) closes unconditionally with net exponential rate `-(pi - 1/2) ≈ -2.64`,
  weaker than the `-pi/2 ≈ -1.57` target; the gap is the decay lost by
  bounding `‖Gamma (1-s)‖` with the `1/2`-rate banked upper instead of a
  `pi/2`-rate tail.
* Missing lemma M2 (name): the polynomial factor `|y|^{x-1/2}` in the lower
  bound. Needs a Stirling remainder for complex log Gamma (unbanked) or the
  Binet integral representation with explicit bounds (unbanked).
* Psi-disc feed (priority 2): this file banks the log form
  `D3SR_logGamma_wendel` and the slope form `D3SR_logGamma_slope_le`
  (finite-difference psi control). Missing lemma M3 (name): the limit passage
  from slope bounds to a `Complex.digamma` disc
  `‖digamma w - (log w - 1 / (2 * w))‖ ≤ C / ‖w‖^2`, equivalently the Gauss
  integral representation of digamma (Mathlib TODO in
  `Gamma/Digamma.lean`), plus differentiation of the log-Gamma expansion.
* Uniform upper at `pi/2` rate (priority 3): NOT attempted here; banked rate
  is `1/2` (`D3SG_TierC_gamma_wide`). Missing lemma M4 (name): the full-tail
  `pi/2` Gamma integral estimate (open `door3_gamma_pi2.lean` route).
-/

end Door3StirlingRem
