import Mathlib
import central_cover_assembly
import door3_stirling_gamma

/-!
# Door 3 complex-Gamma LOWERS (PREM-GAMMA remainder: uppers done, lowers open).

Cycle safety (verified read-only before writing):
* `door3_stirling_gamma.lean:1` imports `Mathlib` only.
* `central_cover_assembly.lean:1-3` imports `Mathlib`, `riemann_hypothesis`,
  `rh_certificate_infra` (no door3 import).
* Hence `Mathlib + central_cover_assembly + door3_stirling_gamma` is a DAG.
  This file reuses `D3SG_*` caps instead of reproving them and does NOT import
  `door3_premise_gamma` (keeps the lane one-directional).

Recon (brief, read-only):
* `gammaOf s = Complex.Gamma (s / 2)` (`central_cover_assembly.lean:6334`).
* 30 lower obligations `premGamma_*_ge` in `door3_premise_gamma.lean:81-169`
  with floors + s-centers; banked shift infrastructure
  `premGamma_shift_norm_one / premGamma_shift_lower` (`:60-77`).
* Tight-flagged R28 / R35 / R38 / R29 gate re-tier decisions
  (`premGamma_R28_threshold_ok`, TRUE-scale notes `:209-212`, `:693-696`).
* `D3SG_TierC_gamma_wide` (`door3_stirling_gamma.lean:1468`) and
  `D3SG_decay_sigma` (`:1305`) are UPPERS (`‖Γ‖ ≤ …`).
* `D3SG_Real_Gamma_*` numerals in the stirling file are ALL uppers:
  `≤ 4` (`:125`), `≤ 1.1` (`:378`), `≤ 20` (`:1381`), `≤ 200` (`:1425`),
  `≤ 1` on `[1,2]` (`:1366`), `≤ 2` (`:1641`, `:1669`).
  There is NO banked real-Gamma LOWER numeral.  Using a real upper as a
  numerator lower would reverse `D3SG_Gamma_norm_le_real`
  (`‖Γ(w)‖ ≤ Real.Gamma (Re w)`) and be unsound.  Nothing is forced here.

Technique banked per center (sound direction):
shift UP by integers via `Γ(w+1) = w·Γ(w)` (`Complex.Gamma_add_one`),
`‖Γ(w)‖ = ‖Γ(w+n)‖ / ∏ ‖w+k‖`, so a numerator LOWER plus explicit
polynomial denominator UPPERS `‖w‖·‖w+1‖⋯` gives a lower.  This file banks
the implication once and for all plus every denominator factor upper by
direct `norm_num`-scale arithmetic at the explicit center (concrete
complex-number bounds, no analysis).  Numerator complex lowers at shifted
points are NOT banked anywhere (integral domination only gives uppers;
reflection `Γ(w)Γ(1-w) = π/sin` with banked uppers gives only
`O(10⁻⁵)-O(10⁻²)` — far below floors; see remainder).  Hence 0 of 30 floors
are closed here; all 30 stay open as `Prop` obligations with per-center
status.  False floors would be reported as true value + deficit, never forced.

Line budget: well under 1400.  No `sorry` / `admit` / `axiom`, explicit
binders, no `simpa`, numerals ≤ 6 digits.
-/

noncomputable section

namespace Door3GammaLow

/-! ## Shift infrastructure (mirrors `premGamma_shift_*`, local names). -/

/-- Norm shift identity for one step up (reproved from `Gamma_add_one`
at `w ≠ 0`; the in-file `D3SG_gamma_shift_norm` needs `0 < Re`, so the
single step here covers the low-sigma centers directly). -/
theorem shift_norm_one (w : ℂ) (hw : w ≠ 0) :
    ‖Complex.Gamma (w + 1)‖ = ‖w‖ * ‖Complex.Gamma w‖ := by
  have hG : Complex.Gamma (w + 1) = w * Complex.Gamma w :=
    Complex.Gamma_add_one w hw
  rw [hG, norm_mul]

/-- Lower via shift: upper on `‖w‖` plus lower on `‖Gamma (w+1)‖` gives a
lower on `‖Gamma w‖`. -/
theorem shift_lower (w : ℂ) (hw : w ≠ 0) (c : ℝ) (M : ℝ)
    (hc : c ≤ ‖Complex.Gamma (w + 1)‖) (hM : ‖w‖ ≤ M) (hMpos : 0 < M) :
    c / M ≤ ‖Complex.Gamma w‖ := by
  have hEq : ‖Complex.Gamma (w + 1)‖ = ‖w‖ * ‖Complex.Gamma w‖ :=
    shift_norm_one w hw
  have hnn : 0 ≤ ‖Complex.Gamma w‖ := norm_nonneg _
  have h1 : c ≤ M * ‖Complex.Gamma w‖ :=
    le_trans hc (mul_le_mul_of_nonneg_right hM hnn)
  exact (le_div_iff₀ hMpos).mpr h1

/-- Two-step lower: pay `‖w‖·‖w+1‖` explicitly. -/
theorem shift_lower_two (w : ℂ) (hw0 : w ≠ 0) (hw1 : w + 1 ≠ 0)
    (c : ℝ) (M0 : ℝ) (M1 : ℝ)
    (hc : c ≤ ‖Complex.Gamma (w + 2)‖)
    (hM0 : ‖w‖ ≤ M0) (hM1 : ‖w + 1‖ ≤ M1)
    (hM0pos : 0 < M0) (hM1pos : 0 < M1) :
    c / (M0 * M1) ≤ ‖Complex.Gamma w‖ := by
  have heq : (w + 2 : ℂ) = w + 1 + 1 := by ring
  rw [heq] at hc
  have h1 : c / M1 ≤ ‖Complex.Gamma (w + 1)‖ :=
    shift_lower (w + 1) hw1 c M1 hc hM1 hM1pos
  have h2 : (c / M1) / M0 ≤ ‖Complex.Gamma w‖ :=
    shift_lower w hw0 (c / M1) M0 h1 hM0 hM0pos
  have e : (c / M1) / M0 = c / (M0 * M1) := by
    rw [div_div, mul_comm]
  rw [e] at h2
  exact h2

/-- Nonvanishing side goals at the explicit centers (`Re ≠ 0` suffices). -/
theorem w_ne_zero_of_re (w : ℂ) (hre : w.re ≠ 0) : w ≠ 0 := by
  intro h
  rw [h] at hre
  simp at hre

/-! ## Helper: from `‖w‖² ≤ M²` to `‖w‖ ≤ M` (mirrors stirling `sqrt` close). -/

theorem norm_le_of_sq_le (w : ℂ) (M : ℝ) (hMnn : 0 ≤ M)
    (hsq : ‖w‖ ^ 2 ≤ M ^ 2) : ‖w‖ ≤ M := by
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-! ## TIGHT-FLAGGED FIRST (gate re-tier): R28 / R35 / R38 / R29.

Status: OPEN (0 discharged).  TRUE (Stirling, per premise header):
R28 ~0.0274 vs floor 0.026 (1.05x); R35 ~2.16 vs 2 (1.08x);
R38 ~0.0262 vs 0.024 (1.09x); R29 ~0.00504 vs 0.0045 (1.12x).
Banked reflection lower with `D3SG_*` uppers is O(10⁻⁵)-O(10⁻²), far below
floors (see remainder); explicit Stirling-disc enclosures needed next wave.
Denominator uppers below are CLOSED (concrete arithmetic).
-/

/-- R28 lower obligation (mirrors `premGamma_R28_ge`; OPEN). -/
def gammaLow_R28_ge : Prop :=
  (0.026 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.2 5.25 : ℂ)) / 2)‖

/-- R35 lower obligation (mirrors `premGamma_R35_ge`; OPEN). -/
def gammaLow_R35_ge : Prop :=
  (2 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.105 (-0.75) : ℂ)) / 2)‖

/-- R38 lower obligation (mirrors `premGamma_R38_ge`; OPEN). -/
def gammaLow_R38_ge : Prop :=
  (0.024 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.105 5.25 : ℂ)) / 2)‖

/-- R29 lower obligation (mirrors `premGamma_R29_ge`; OPEN). -/
def gammaLow_R29_ge : Prop :=
  (0.0045 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.2 7.25 : ℂ)) / 2)‖

/-- R28 denominator `‖w‖ ≤ 2.83` at `w = s/2` (CLOSED arithmetic). -/
theorem R28_w_norm_le :
    ‖(((Complex.mk 0.2 5.25 : ℂ)) / 2)‖ ≤ 2.83 := by
  have hsq : ‖(((Complex.mk 0.2 5.25 : ℂ)) / 2)‖ ^ 2 ≤ (2.83 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 2.83 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R28 second factor `‖w+1‖ ≤ 3.83` (CLOSED arithmetic). -/
theorem R28_w1_norm_le :
    ‖(((Complex.mk 0.2 5.25 : ℂ)) / 2 + 1)‖ ≤ 3.83 := by
  have hsq : ‖(((Complex.mk 0.2 5.25 : ℂ)) / 2 + 1)‖ ^ 2 ≤ (3.83 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 3.83 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R35 denominator `‖w‖ ≤ 0.58` (CLOSED arithmetic). -/
theorem R35_w_norm_le :
    ‖(((Complex.mk 0.105 (-0.75) : ℂ)) / 2)‖ ≤ 0.58 := by
  have hsq : ‖(((Complex.mk 0.105 (-0.75) : ℂ)) / 2)‖ ^ 2 ≤ (0.58 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 0.58 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R35 second factor `‖w+1‖ ≤ 1.58` (CLOSED arithmetic). -/
theorem R35_w1_norm_le :
    ‖(((Complex.mk 0.105 (-0.75) : ℂ)) / 2 + 1)‖ ≤ 1.58 := by
  have hsq : ‖(((Complex.mk 0.105 (-0.75) : ℂ)) / 2 + 1)‖ ^ 2 ≤ (1.58 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 1.58 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R38 denominator `‖w‖ ≤ 2.83` (CLOSED arithmetic). -/
theorem R38_w_norm_le :
    ‖(((Complex.mk 0.105 5.25 : ℂ)) / 2)‖ ≤ 2.83 := by
  have hsq : ‖(((Complex.mk 0.105 5.25 : ℂ)) / 2)‖ ^ 2 ≤ (2.83 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 2.83 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R38 second factor `‖w+1‖ ≤ 3.83` (CLOSED arithmetic). -/
theorem R38_w1_norm_le :
    ‖(((Complex.mk 0.105 5.25 : ℂ)) / 2 + 1)‖ ≤ 3.83 := by
  have hsq : ‖(((Complex.mk 0.105 5.25 : ℂ)) / 2 + 1)‖ ^ 2 ≤ (3.83 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 3.83 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R29 denominator `‖w‖ ≤ 3.83` (CLOSED arithmetic). -/
theorem R29_w_norm_le :
    ‖(((Complex.mk 0.2 7.25 : ℂ)) / 2)‖ ≤ 3.83 := by
  have hsq : ‖(((Complex.mk 0.2 7.25 : ℂ)) / 2)‖ ^ 2 ≤ (3.83 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 3.83 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R29 second factor `‖w+1‖ ≤ 4.83` (CLOSED arithmetic). -/
theorem R29_w1_norm_le :
    ‖(((Complex.mk 0.2 7.25 : ℂ)) / 2 + 1)‖ ≤ 4.83 := by
  have hsq : ‖(((Complex.mk 0.2 7.25 : ℂ)) / 2 + 1)‖ ^ 2 ≤ (4.83 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 4.83 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-! ## Remaining 26 obligations (OPEN) + denominator uppers (CLOSED).

TRUE estimates per `door3_premise_gamma.lean:26-35` headers are quoted in
comments; none is forced.  Ascending-difficulty order is approximated by
ascending `|Im|` within each row (small-`|Im|` first).
-/

/-- R36 lower (OPEN; TRUE ~1.16 vs floor 1). -/
def gammaLow_R36_ge : Prop :=
  (1 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.105 1.25 : ℂ)) / 2)‖

/-- R36 denominator (CLOSED). -/
theorem R36_w_norm_le :
    ‖(((Complex.mk 0.105 1.25 : ℂ)) / 2)‖ ≤ 0.83 := by
  have hsq : ‖(((Complex.mk 0.105 1.25 : ℂ)) / 2)‖ ^ 2 ≤ (0.83 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 0.83 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R34 lower (OPEN; TRUE ~0.25 vs floor 0.2). -/
def gammaLow_R34_ge : Prop :=
  (0.2 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.105 (-2.75) : ℂ)) / 2)‖

/-- R34 denominator (CLOSED). -/
theorem R34_w_norm_le :
    ‖(((Complex.mk 0.105 (-2.75) : ℂ)) / 2)‖ ≤ 1.58 := by
  have hsq : ‖(((Complex.mk 0.105 (-2.75) : ℂ)) / 2)‖ ^ 2 ≤ (1.58 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 1.58 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R37 lower (OPEN; TRUE ~0.157 vs floor 0.12). -/
def gammaLow_R37_ge : Prop :=
  (0.12 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.105 3.25 : ℂ)) / 2)‖

/-- R37 denominator (CLOSED). -/
theorem R37_w_norm_le :
    ‖(((Complex.mk 0.105 3.25 : ℂ)) / 2)‖ ≤ 1.83 := by
  have hsq : ‖(((Complex.mk 0.105 3.25 : ℂ)) / 2)‖ ^ 2 ≤ (1.83 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 1.83 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R33 lower (OPEN; TRUE ~0.0408 vs floor 0.032). -/
def gammaLow_R33_ge : Prop :=
  (0.032 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.105 (-4.75) : ℂ)) / 2)‖

/-- R33 denominator (CLOSED). -/
theorem R33_w_norm_le :
    ‖(((Complex.mk 0.105 (-4.75) : ℂ)) / 2)‖ ≤ 2.58 := by
  have hsq : ‖(((Complex.mk 0.105 (-4.75) : ℂ)) / 2)‖ ^ 2 ≤ (2.58 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 2.58 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R32 lower (OPEN; TRUE ~0.00725 vs floor 0.006; feasibility-negative lane). -/
def gammaLow_R32_ge : Prop :=
  (0.006 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.105 (-6.75) : ℂ)) / 2)‖

/-- R32 denominator (CLOSED). -/
theorem R32_w_norm_le :
    ‖(((Complex.mk 0.105 (-6.75) : ℂ)) / 2)‖ ≤ 3.58 := by
  have hsq : ‖(((Complex.mk 0.105 (-6.75) : ℂ)) / 2)‖ ^ 2 ≤ (3.58 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 3.58 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R39 lower (OPEN; TRUE ~0.00472 vs floor 0.004; feasibility-negative lane). -/
def gammaLow_R39_ge : Prop :=
  (0.004 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.105 7.25 : ℂ)) / 2)‖

/-- R39 denominator (CLOSED). -/
theorem R39_w_norm_le :
    ‖(((Complex.mk 0.105 7.25 : ℂ)) / 2)‖ ≤ 3.83 := by
  have hsq : ‖(((Complex.mk 0.105 7.25 : ℂ)) / 2)‖ ^ 2 ≤ (3.83 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 3.83 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R31 lower (OPEN; TRUE ~0.00134 vs floor 0.001; feasibility-negative lane). -/
def gammaLow_R31_ge : Prop :=
  (0.001 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.105 (-8.75) : ℂ)) / 2)‖

/-- R31 denominator (CLOSED). -/
theorem R31_w_norm_le :
    ‖(((Complex.mk 0.105 (-8.75) : ℂ)) / 2)‖ ≤ 4.58 := by
  have hsq : ‖(((Complex.mk 0.105 (-8.75) : ℂ)) / 2)‖ ^ 2 ≤ (4.58 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 4.58 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R40 lower (OPEN; TRUE ~0.00134 vs floor 0.001; feasibility-negative lane). -/
def gammaLow_R40_ge : Prop :=
  (0.001 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.105 8.75 : ℂ)) / 2)‖

/-- R40 denominator (CLOSED). -/
theorem R40_w_norm_le :
    ‖(((Complex.mk 0.105 8.75 : ℂ)) / 2)‖ ≤ 4.58 := by
  have hsq : ‖(((Complex.mk 0.105 8.75 : ℂ)) / 2)‖ ^ 2 ≤ (4.58 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 4.58 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R25 lower (OPEN; TRUE ~5.0 vs floor 2). -/
def gammaLow_R25_ge : Prop :=
  (2 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.2 (-0.75) : ℂ)) / 2)‖

/-- R25 denominator (CLOSED). -/
theorem R25_w_norm_le :
    ‖(((Complex.mk 0.2 (-0.75) : ℂ)) / 2)‖ ≤ 0.58 := by
  have hsq : ‖(((Complex.mk 0.2 (-0.75) : ℂ)) / 2)‖ ^ 2 ≤ (0.58 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 0.58 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R26 lower (OPEN; TRUE ~1.5 vs floor 1). -/
def gammaLow_R26_ge : Prop :=
  (1 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.2 1.25 : ℂ)) / 2)‖

/-- R26 denominator (CLOSED). -/
theorem R26_w_norm_le :
    ‖(((Complex.mk 0.2 1.25 : ℂ)) / 2)‖ ≤ 0.83 := by
  have hsq : ‖(((Complex.mk 0.2 1.25 : ℂ)) / 2)‖ ^ 2 ≤ (0.83 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 0.83 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R24 lower (OPEN; TRUE ~0.254 vs floor 0.2). -/
def gammaLow_R24_ge : Prop :=
  (0.2 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.2 (-2.75) : ℂ)) / 2)‖

/-- R24 denominator (CLOSED). -/
theorem R24_w_norm_le :
    ‖(((Complex.mk 0.2 (-2.75) : ℂ)) / 2)‖ ≤ 1.58 := by
  have hsq : ‖(((Complex.mk 0.2 (-2.75) : ℂ)) / 2)‖ ^ 2 ≤ (1.58 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 1.58 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R27 lower (OPEN; TRUE ~0.161 vs floor 0.12). -/
def gammaLow_R27_ge : Prop :=
  (0.12 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.2 3.25 : ℂ)) / 2)‖

/-- R27 denominator (CLOSED). -/
theorem R27_w_norm_le :
    ‖(((Complex.mk 0.2 3.25 : ℂ)) / 2)‖ ≤ 1.83 := by
  have hsq : ‖(((Complex.mk 0.2 3.25 : ℂ)) / 2)‖ ^ 2 ≤ (1.83 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 1.83 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R23 lower (OPEN; TRUE ~0.0426 vs floor 0.032). -/
def gammaLow_R23_ge : Prop :=
  (0.032 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.2 (-4.75) : ℂ)) / 2)‖

/-- R23 denominator (CLOSED). -/
theorem R23_w_norm_le :
    ‖(((Complex.mk 0.2 (-4.75) : ℂ)) / 2)‖ ≤ 2.58 := by
  have hsq : ‖(((Complex.mk 0.2 (-4.75) : ℂ)) / 2)‖ ^ 2 ≤ (2.58 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 2.58 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R22 lower (OPEN; TRUE ~0.00769 vs floor 0.006; conditional-feasible lane). -/
def gammaLow_R22_ge : Prop :=
  (0.006 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.2 (-6.75) : ℂ)) / 2)‖

/-- R22 denominator (CLOSED). -/
theorem R22_w_norm_le :
    ‖(((Complex.mk 0.2 (-6.75) : ℂ)) / 2)‖ ≤ 3.58 := by
  have hsq : ‖(((Complex.mk 0.2 (-6.75) : ℂ)) / 2)‖ ^ 2 ≤ (3.58 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 3.58 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R21 lower (OPEN; TRUE ~0.00143 vs floor 0.001; feasibility-negative lane). -/
def gammaLow_R21_ge : Prop :=
  (0.001 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.2 (-8.75) : ℂ)) / 2)‖

/-- R21 denominator (CLOSED). -/
theorem R21_w_norm_le :
    ‖(((Complex.mk 0.2 (-8.75) : ℂ)) / 2)‖ ≤ 4.58 := by
  have hsq : ‖(((Complex.mk 0.2 (-8.75) : ℂ)) / 2)‖ ^ 2 ≤ (4.58 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 4.58 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- R30 lower (OPEN; TRUE ~0.00143 vs floor 0.001; feasibility-negative lane). -/
def gammaLow_R30_ge : Prop :=
  (0.001 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.2 8.75 : ℂ)) / 2)‖

/-- R30 denominator (CLOSED). -/
theorem R30_w_norm_le :
    ‖(((Complex.mk 0.2 8.75 : ℂ)) / 2)‖ ≤ 4.58 := by
  have hsq : ‖(((Complex.mk 0.2 8.75 : ℂ)) / 2)‖ ^ 2 ≤ (4.58 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 4.58 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- E05 lower (OPEN; TRUE ~4.4 vs floor 1.5). -/
def gammaLow_E05_ge : Prop :=
  (1.5 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.395 (-0.75) : ℂ)) / 2)‖

/-- E05 denominator (CLOSED). -/
theorem E05_w_norm_le :
    ‖(((Complex.mk 0.395 (-0.75) : ℂ)) / 2)‖ ≤ 0.58 := by
  have hsq : ‖(((Complex.mk 0.395 (-0.75) : ℂ)) / 2)‖ ^ 2 ≤ (0.58 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 0.58 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- E06 lower (OPEN; TRUE ~2.5 vs floor 1). -/
def gammaLow_E06_ge : Prop :=
  (1 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.395 1.25 : ℂ)) / 2)‖

/-- E06 denominator (CLOSED). -/
theorem E06_w_norm_le :
    ‖(((Complex.mk 0.395 1.25 : ℂ)) / 2)‖ ≤ 0.83 := by
  have hsq : ‖(((Complex.mk 0.395 1.25 : ℂ)) / 2)‖ ^ 2 ≤ (0.83 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 0.83 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- E07 lower (OPEN; TRUE ~0.169 vs floor 0.1). -/
def gammaLow_E07_ge : Prop :=
  (0.1 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.395 3.25 : ℂ)) / 2)‖

/-- E07 denominator (CLOSED). -/
theorem E07_w_norm_le :
    ‖(((Complex.mk 0.395 3.25 : ℂ)) / 2)‖ ≤ 1.83 := by
  have hsq : ‖(((Complex.mk 0.395 3.25 : ℂ)) / 2)‖ ^ 2 ≤ (1.83 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 1.83 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- E08 lower (OPEN; TRUE ~0.03 vs floor 0.02). -/
def gammaLow_E08_ge : Prop :=
  (0.02 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.395 5.25 : ℂ)) / 2)‖

/-- E08 denominator (CLOSED). -/
theorem E08_w_norm_le :
    ‖(((Complex.mk 0.395 5.25 : ℂ)) / 2)‖ ≤ 2.83 := by
  have hsq : ‖(((Complex.mk 0.395 5.25 : ℂ)) / 2)‖ ^ 2 ≤ (2.83 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 2.83 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- E09 lower (OPEN; TRUE ~0.0057 vs floor 0.0045). -/
def gammaLow_E09_ge : Prop :=
  (0.0045 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.395 7.25 : ℂ)) / 2)‖

/-- E09 denominator (CLOSED). -/
theorem E09_w_norm_le :
    ‖(((Complex.mk 0.395 7.25 : ℂ)) / 2)‖ ≤ 3.83 := by
  have hsq : ‖(((Complex.mk 0.395 7.25 : ℂ)) / 2)‖ ^ 2 ≤ (3.83 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 3.83 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- E01 lower (OPEN; TRUE ~0.013 vs floor 0.01). -/
def gammaLow_E01_ge : Prop :=
  (0.01 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.395 (-6.25) : ℂ)) / 2)‖

/-- E01 denominator (CLOSED). -/
theorem E01_w_norm_le :
    ‖(((Complex.mk 0.395 (-6.25) : ℂ)) / 2)‖ ≤ 3.33 := by
  have hsq : ‖(((Complex.mk 0.395 (-6.25) : ℂ)) / 2)‖ ^ 2 ≤ (3.33 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 3.33 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- E10 lower (OPEN; TRUE ~0.00166 vs floor 0.0015). -/
def gammaLow_E10_ge : Prop :=
  (0.0015 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.395 8.75 : ℂ)) / 2)‖

/-- E10 denominator (CLOSED). -/
theorem E10_w_norm_le :
    ‖(((Complex.mk 0.395 8.75 : ℂ)) / 2)‖ ≤ 4.58 := by
  have hsq : ‖(((Complex.mk 0.395 8.75 : ℂ)) / 2)‖ ^ 2 ≤ (4.58 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 4.58 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- BA00 lower (OPEN; batch-A header floor 0.0015). -/
def gammaLow_BA00_ge : Prop :=
  (0.0015 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.395 (-8.75) : ℂ)) / 2)‖

/-- BA00 denominator (CLOSED). -/
theorem BA00_w_norm_le :
    ‖(((Complex.mk 0.395 (-8.75) : ℂ)) / 2)‖ ≤ 4.58 := by
  have hsq : ‖(((Complex.mk 0.395 (-8.75) : ℂ)) / 2)‖ ^ 2 ≤ (4.58 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 4.58 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- BA03 lower (OPEN; batch-A header floor 0.015). -/
def gammaLow_BA03_ge : Prop :=
  (0.015 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.395 (-4.75) : ℂ)) / 2)‖

/-- BA03 denominator (CLOSED). -/
theorem BA03_w_norm_le :
    ‖(((Complex.mk 0.395 (-4.75) : ℂ)) / 2)‖ ≤ 2.58 := by
  have hsq : ‖(((Complex.mk 0.395 (-4.75) : ℂ)) / 2)‖ ^ 2 ≤ (2.58 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 2.58 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-- BA04 lower (OPEN; batch-A header floor 0.08). -/
def gammaLow_BA04_ge : Prop :=
  (0.08 : ℝ) ≤ ‖Complex.Gamma (((Complex.mk 0.395 (-2.75) : ℂ)) / 2)‖

/-- BA04 denominator (CLOSED). -/
theorem BA04_w_norm_le :
    ‖(((Complex.mk 0.395 (-2.75) : ℂ)) / 2)‖ ≤ 1.58 := by
  have hsq : ‖(((Complex.mk 0.395 (-2.75) : ℂ)) / 2)‖ ^ 2 ≤ (1.58 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hMnn : (0 : ℝ) ≤ 1.58 := by norm_num
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hMnn] at hsqrt
  exact hsqrt

/-! ## Discharge record + remainder (honest split).

LOWERS CLOSED: 0 of 30.  No `premGamma_*_ge` discharged here.
`gammaLow_*_ge` unfolds to `premGamma_*_ge` via
`DerivCauchyBridge.gammaOf s = Complex.Gamma (s / 2)` (`:6334`); the rewrite
is banked for the wave that supplies numerator lowers:
`unfold DerivCauchyBridge.gammaOf` turns each `premGamma_*_ge` into the
matching `gammaLow_*_ge` verbatim (same `Complex.mk` numerals).
DENOMINATORS CLOSED: 34 factor uppers above
(R28/R35/R38/R29 ×2 plus 26 ×1), all by `Complex.sq_norm +
Complex.normSq_apply + simp + norm_num` and the stirling `sqrt` close.
SHIFT INFRA CLOSED: `shift_norm_one`, `shift_lower`, `shift_lower_two`,
`w_ne_zero_of_re`, `norm_le_of_sq_le` (reuse `Complex.Gamma_add_one`).
FALSE FLOORS: none declared false.  All 30 floors sit below the TRUE
Stirling estimates quoted from `door3_premise_gamma.lean:26-35`, so each
deficit is negative (margin positive); tightest is R28 (TRUE ~0.0274 vs
0.026, margin ~0.0014, 1.05x).  Nothing was forced.
REMAINDER (next wave): all 30 `gammaLow_*_ge` Props above.  What blocks them:
(a) no banked complex-Gamma numerator lower exists — `D3SG_*` gives only
uppers, and `D3SG_Real_Gamma_*` numerals are real uppers, so the naive
`Real.Gamma`-as-lower step is unsound (reverses `D3SG_Gamma_norm_le_real`);
(b) reflection `‖Γ(w)‖ = π/(‖sin πw‖·‖Γ(1-w)‖)` with banked
`D3SG_CHI_sin_le_exp_abs_im` (`exp(π|Im|)`) and `D3SG_TierC_gamma_rect`
(`60·exp(−|Im|/2)`) yields only ~0.019 at `|Im|=0.375` (R35 needs 2) and
~5e-05 at `|Im|=2.625` (R28 needs 0.026) — 2-3 orders of magnitude short;
the banked `c = 1/2` rate cannot cancel `exp(π|Im|)` growth, so the `π/2`
rate lane (`door3_gamma_pi2.lean`, open full-tail route) plus explicit
Stirling-disc enclosures at shifted `Re ∈ [1,2]` are required;
(c) feasibility-negative cells R31/R32/R39/R40/R21/R30 (per
`premGamma_*_threshold_negative`) plus R22/R28 conditional cells stay in
re-tier/subdivision lane, consistent with the premise audit.
-/

end Door3GammaLow
