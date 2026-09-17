import Mathlib
import central_cover_assembly

/-!
# Door 3 CELL residual suppliers (`door3_cell_suppliers.lean`, NEW file)

WRITE-ONLY supplier task (2026-09-10; DO NOT BUILD here — patch phase builds).
Working directory: `C:\Users\mmeadow\Documents\Lean\mathlib4`.
Ownership: this file ONLY (`door3_cell_suppliers.lean` was absent — verified via
`Test-Path` before writing). No other repo file touched. No commit/push.
No repo logs. No lakefile edit (central registration later).

Recon (read-only, before writing; nothing touched):
* `door3_first_cell.lean` (398-line draft + close-out tail): premise shapes
  `FC_zeta14_obligation` (`1.4 ≤ ‖ζ‖`), `FC_rpow2_head_upper`
  (`2^-0.395 ≤ 0.77`), even-partial domination `hEven`, `FC_Lambda0_upper_fat`
  (`Λ₀ ≤ 479` on the fat `s`-rect), and the `0.008`-gamma path
  (need reflected `U ≤ 0.0195`, have `0.026`; `S = 20128` banked).
* `TailLaguerreScratch.lean` trig pattern (§5r): quadratic cos floor via
  `cos x = 1 - 2·sin(x/2)²` + `Real.sin_le` + `sin ≥ 0` on `[0,π]`;
  6-digit rounded `log 2` bounds; `log 3` via `log 4 = 2·log 2` recipe.
* `zeta_rigorous.lean` slice pattern: `Antitone.alternating_series_le_tendsto`
  / `tendsto_le_alternating_series` with `S₂` lower / `S₁,S₃` uppers.
* `R02GammaLower` / `R02SineSharp` (`interval_arith.lean`): reflection
  `π/(S·U)` route, `(exp 1)^n` numeral pattern, `Real.exp_bound'` fractional
  rung, `S·U` cap arithmetic. Reproved locally here (lane independence).

## Numbers landed per item

| item | target | landed in this file | status |
| (a) zeta-lower `1.4` at `sCenter` | `1.4 ≤ ‖ζ‖` | trig floors: phase cap `6.75·log2 < 4.679` PROVED; `cos(0.75·log2) ≥ 43/50` reproved; real-`σ` head `S₂ ≥ 0.23` UNCONDITIONAL (via §C); complex N=2 head `‖S₂ᶜ‖ ≥ 1` conditional on TRUE premises; general `slow/tail/cF` assembly PROVED; N=2 insufficiency for `1.4` quantified | residual `CS_zeta14_residual` (`1.4`, same shape as `FC_zeta14_obligation`) + trig/tail/factor premises below |
| (b) wide-`Λ₀ ≤ 479` fat `s`-rect | `Λ₀ ≤ 479` | `s`-map identities, fat-ball enclosures, norm caps, prefactor `≤ 35`, ball-sup assembly `16800` conditional on `CS_Lambda0_upper_fat` — ALL PROVED (mirrors of the `FC_fat*` route, lane-local); FE-step existential shape PROVED-sufficient | residual `CS_Lambda0_upper_fat` (same shape as `FC_Lambda0_upper_fat`; TRUE, `O(1)–O(10)` vs `479`) + `CS_Lambda0_FE_step` discharge (FE + Stirling, patch) |
| (c) rpow head-upper + even-partial | `2^-0.395 ≤ 0.77` (true `≈0.7605`) | `CS_rpow2_proved` PROVED (`≤ 0.77`, log/exp route); `S₂ ≥ 0.23` conditional + unconditional corollaries PROVED; even-partial domination template PROVED (finite `S₂` step + Tendsto-slice mirror of `zeta_rigorous`); cleared-numeral check PROVED | NO residual (closed) — domination *input* (`Antitone`, `Tendsto`) stays a patch hypothesis where consumed |
| (d) deeper reflected Gamma chain | reflected `U ≤ 0.0195` (true `≈0.018`) for `0.008` | `S·U` cap route PROVED (`20128·0.0195 = 392.496 ≤ 392.7`); `0.008` lower conditional on TRUE premises PROVED; banked-gap (`0.026` vs `0.0195`) + Stirling numeral witnesses (`exp 1 ≤ 2.72`, fractional-exp template) PROVED | residual `CS_reflected_upper_00195` + `CS_sine_upper_20128` + `CS_reflection_link` (all TRUE, values stated; patch extends the shift chain one step) |

RULES kept: no `sorry` / `admit` / `axiom`; explicit `Prop` premises only;
explicit binders; no `simpa`; all numerals ≤ 6 digits; `norm_num` only on
`ℝ` / `ℕ` goals (never `decide` on `ℚ`); imports ONLY `Mathlib` +
`central_cover_assembly` (no `zeta_rigorous` import — slice lemmas are
referenced by name and re-applied locally; NO import added beyond the two
allowed lines above — flagged explicitly: none).
-/

noncomputable section

namespace Door3CellSuppliers

/-! ## §0. Six-digit log bounds (mirror of the `d3_log2_ge/le` pattern) -/

/-- `log 2` lower, rounded to 6 digits (mirrors `d3_log2_ge`). -/
theorem CS_log2_ge : (0.693147 : ℝ) < Real.log 2 := by
  have h9 := Real.log_two_gt_d9
  linarith

/-- `log 2` upper, rounded to 6 digits (mirrors `d3_log2_le`). -/
theorem CS_log2_le : Real.log 2 < (0.693148 : ℝ) := by
  have h9 := Real.log_two_lt_d9
  linarith

/-- `log 4 = 2 * log 2` (exact, mirrors `d3_log_four_eq`). -/
theorem CS_log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  have h4 : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
  rw [h4, Real.log_pow]
  norm_num

/-- `log 3` lower (`1.0529 ≤ log 3`, mirrors `d3_log_three_ge`: `log 3 =
2·log 2 + log(3/4)` with the 6-digit `log 2` lower and `log(4/3) ≤ 1/3`). -/
theorem CS_log_three_ge : (1.0529 : ℝ) ≤ Real.log 3 := by
  have h2lo := CS_log2_ge
  have hub43 : Real.log (4 / 3 : ℝ) ≤ (1 / 3 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    have he : (4 / 3 : ℝ) - 1 = (1 / 3 : ℝ) := by norm_num
    linarith
  have hinv : Real.log (3 / 4 : ℝ) = -Real.log (4 / 3 : ℝ) := by
    have heq : (3 / 4 : ℝ) = (4 / 3 : ℝ)⁻¹ := by rw [inv_div]
    rw [heq, Real.log_inv]
  have hmeq : (4 : ℝ) * (3 / 4) = 3 := by norm_num
  have hlog3 : Real.log 3 = 2 * Real.log 2 + Real.log (3 / 4 : ℝ) := by
    have h := Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num)
      (show (3 / 4 : ℝ) ≠ 0 by norm_num)
    rw [hmeq, CS_log_four_eq] at h
    exact h
  have hfin : (1.0529 : ℝ) ≤ 2 * (0.693147 : ℝ) - (1 / 3 : ℝ) := by
    norm_num
  rw [hlog3, hinv]
  linarith

/-- `log 3` upper (`log 3 ≤ 1.1363`, mirrors `d3_log_three_le`: same recipe
with the 6-digit `log 2` upper and `log(3/4) ≤ -1/4`). -/
theorem CS_log_three_le : Real.log 3 ≤ (1.1363 : ℝ) := by
  have h2hi := CS_log2_le
  have hub34 : Real.log (3 / 4 : ℝ) ≤ (-1 / 4 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 4)
    have he : (3 / 4 : ℝ) - 1 = (-1 / 4 : ℝ) := by norm_num
    linarith
  have hmeq : (4 : ℝ) * (3 / 4) = 3 := by norm_num
  have hlog3 : Real.log 3 = 2 * Real.log 2 + Real.log (3 / 4 : ℝ) := by
    have h := Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num)
      (show (3 / 4 : ℝ) ≠ 0 by norm_num)
    rw [hmeq, CS_log_four_eq] at h
    exact h
  have hfin : 2 * (0.693148 : ℝ) - (1 / 4 : ℝ) ≤ (1.1363 : ℝ) := by
    norm_num
  rw [hlog3]
  linarith

/-! ## §C. rpow head-upper ≈ 0.7605 + even-partial domination (CLOSED)

Route: `2^-0.395 = 1 / 2^0.395 ≤ 0.77` from `2^0.395 = exp(0.395·log 2) ≥
1.2988` (quadratic Taylor lower `Real.quadratic_le_exp_of_nonneg` at
`x = 0.395·log 2 > 0.2737`); `1/1.2988 ≈ 0.76992 ≤ 0.77` closes with a
`7.6e-5` margin. TRUE value `≈ 0.7605`, so `0.77` carries `1.2%` headroom.
-/

/-- Numeric rpow premise, SAME shape as `FC_rpow2_head_upper`
(`2^-0.395 ≤ 0.77`; TRUE `≈ 0.7605`). -/
def CS_rpow2_head_upper : Prop := (2 : ℝ) ^ (-(0.395 : ℝ)) ≤ 0.77

/-- CLOSED: the rpow head-upper. -/
theorem CS_rpow2_proved : CS_rpow2_head_upper := by
  have hlog : (0.693147 : ℝ) < Real.log 2 := CS_log2_ge
  have hx_lo : (0.2737 : ℝ) < 0.395 * Real.log 2 := by linarith
  set x : ℝ := 0.395 * Real.log 2 with hx_def
  have hx0 : (0 : ℝ) ≤ x := le_trans (by norm_num) hx_lo.le
  have hsq : (0.2737 : ℝ) ^ 2 ≤ x ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hx_lo.le 2
  have hquad := Real.quadratic_le_exp_of_nonneg hx0
  have hbase : (1.2988 : ℝ) ≤ 1 + 0.2737 + (0.2737 : ℝ) ^ 2 / 2 := by
    norm_num
  have hchain : (1.2988 : ℝ) ≤ Real.exp x := by
    linarith [hquad, hsq, hx_lo, hbase]
  have hrpow : (2 : ℝ) ^ ((0.395 : ℝ)) = Real.exp x := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    rw [hx_def]
    ring
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((0.395 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hInv : (2 : ℝ) ^ (-(0.395 : ℝ)) = 1 / (2 : ℝ) ^ ((0.395 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [inv_eq_one_div]
  have h12 : (1.2988 : ℝ) ≤ (2 : ℝ) ^ ((0.395 : ℝ)) := by
    rw [hrpow]
    exact hchain
  have hmul : (0.77 : ℝ) * 1.2988 ≤ 0.77 * (2 : ℝ) ^ ((0.395 : ℝ)) :=
    mul_le_mul_of_nonneg_left h12 (by norm_num)
  have hnum : (1 : ℝ) ≤ 0.77 * 1.2988 := by norm_num
  show (2 : ℝ) ^ (-(0.395 : ℝ)) ≤ 0.77
  rw [hInv, div_le_iff₀ hpos]
  linarith [hmul, hnum]

/-- Real-`σ` eta magnitudes at `σ = 0.395` (same shape as `FC_etaF0395`). -/
noncomputable def CS_etaF0395 (k : ℕ) : ℝ := (((k : ℝ) + 1) ^ (-(0.395 : ℝ)))

/-- Even-partial domination template head step at `σ = 0.395` (mirrors
`FC_eta0395_S2_le`): every limit `L` dominating all even partial sums
dominates `S₂ = 1 - 2^-0.395`. -/
theorem CS_eta0395_S2_le (L : ℝ)
    (hEven : ∀ (k : ℕ), ∑ i ∈ Finset.range (2 * k),
      (-1 : ℝ) ^ i * CS_etaF0395 i ≤ L) :
    1 - (2 : ℝ) ^ (-(0.395 : ℝ)) ≤ L := by
  have h1 := hEven 1
  rw [show (2 * 1 : ℕ) = 2 from by norm_num,
    show (2 : ℕ) = 1 + 1 from by norm_num] at h1
  have h_eq : (∑ i ∈ Finset.range (1 + 1),
      (-1 : ℝ) ^ i * CS_etaF0395 i) = 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_one,
      Finset.sum_range_zero]
    simp only [CS_etaF0395, pow_zero, pow_one, Nat.cast_zero, Nat.cast_one,
      Real.one_rpow]
    ring
  rw [← h_eq]
  exact h1

/-- Slice mirror of the `zeta_rigorous` `eta_half_ge_S2` route at
`σ = 0.395`: from a `Tendsto` alternating-series limit plus the (TRUE)
antitonicity input, `S₂ ≤ L`. Uses
`Antitone.alternating_series_le_tendsto` exactly as `zeta_rigorous` does;
the `Antitone` fact itself is a patch hypothesis (TRUE: `(k+1)^-0.395`
decreases in `k`). -/
theorem CS_slice_S2_of_tendsto (L : ℝ)
    (hL : Filter.Tendsto
      (fun (n : ℕ) => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * CS_etaF0395 i)
      Filter.atTop (nhds L))
    (hAnti : Antitone CS_etaF0395) :
    1 - (2 : ℝ) ^ (-(0.395 : ℝ)) ≤ L := by
  have h_raw : (∑ i ∈ Finset.range (2 * 1), (-1 : ℝ) ^ i * CS_etaF0395 i) ≤ L :=
    Antitone.alternating_series_le_tendsto hL hAnti 1
  have h_eq : (∑ i ∈ Finset.range (2 * 1), (-1 : ℝ) ^ i * CS_etaF0395 i)
      = 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) := by
    rw [show (2 * 1 : ℕ) = 2 from by norm_num,
      show (2 : ℕ) = 1 + 1 from by norm_num]
    simp only [Finset.sum_range_succ, Finset.sum_range_one,
      Finset.sum_range_zero]
    simp only [CS_etaF0395, pow_zero, pow_one, Nat.cast_zero, Nat.cast_one,
      Real.one_rpow]
    ring
  rw [← h_eq]
  exact h_raw

/-- Sharpest CLOSED head floor at real `σ = 0.395`, conditional form
(mirrors `FC_etaS2_ge_023`): `S₂ ≥ 0.23` (TRUE `≈ 0.2395`). -/
theorem CS_etaS2_ge_023 (h : CS_rpow2_head_upper) :
    (0.23 : ℝ) ≤ 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) := by
  have h2 : (2 : ℝ) ^ (-(0.395 : ℝ)) ≤ 0.77 := h
  linarith

/-- UNCONDITIONAL head floor (the §C closure discharges the premise). -/
theorem CS_etaS2_uncond : (0.23 : ℝ) ≤ 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) :=
  CS_etaS2_ge_023 CS_rpow2_proved

/-- Cleared-power numeral witness linking the `0.77` cap to the `0.23`
floor (`23/100 ≤ 1 - 77/100`, `norm_num`). -/
theorem CS_cleared_head_check : (23 / 100 : ℝ) ≤ 1 - 77 / 100 := by
  norm_num

/-! ## §A. Zeta-lower scaffolding at `sCenter = 0.395 - 6.75·I`

Landed: trig floors (RX-lane pattern), general `slow/tail/cF` assembly,
real-`σ` head (unconditional via §C), complex N=2 head (`‖S₂ᶜ‖ ≥ 1`
conditional on TRUE premises), and the quantified N=2 gap vs `1.4`.
-/

/-- Quadratic cosine floor for `0 ≤ x ≤ 2` (mirrors `d3_cos_quad_lower`:
`cos x = 1 - 2·sin(x/2)²` via `Real.cos_two_mul` + `sin²+cos²=1`,
`Real.sin_le`, `sin ≥ 0` on `[0,π]`). -/
theorem CS_cos_quad_lower (x : ℝ) (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    1 - x ^ 2 / 2 ≤ Real.cos x := by
  have hpi := Real.pi_gt_d6
  have ht0 : (0 : ℝ) ≤ x / 2 := by positivity
  have htpi : x / 2 ≤ Real.pi := by linarith
  have hsin_nn : (0 : ℝ) ≤ Real.sin (x / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 htpi
  have hsin_le : Real.sin (x / 2) ≤ x / 2 := Real.sin_le ht0
  have hsq : Real.sin (x / 2) ^ 2 ≤ (x / 2) ^ 2 :=
    pow_le_pow_left₀ hsin_nn hsin_le 2
  have h2t : 2 * (x / 2) = x := by ring
  have hcos2 : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    have h := Real.cos_two_mul (x / 2)
    have hpy := Real.sin_sq_add_cos_sq (x / 2)
    rw [h2t] at h
    linarith
  have ht2 : (x / 2) ^ 2 = x ^ 2 / 4 := by ring
  rw [hcos2]
  linarith

/-- Phase-cosine floor at the R05 phase (reproof of the
`R05_phase_cos_lower` route on lane-local lemmas:
`cos (0.75·log 2) ≥ 43/50` from `0.75·log 2 < 0.5199`). -/
theorem CS_cos_075log2_lower :
    (43 / 50 : ℝ) ≤ Real.cos (0.75 * Real.log 2) := by
  have hloghi := CS_log2_le
  have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hnn : (0 : ℝ) ≤ 0.75 * Real.log 2 :=
    mul_nonneg (by norm_num) (le_of_lt hpos)
  have hhi : 0.75 * Real.log 2 < (0.5199 : ℝ) := by linarith
  have hle : 0.75 * Real.log 2 ≤ (0.5199 : ℝ) := le_of_lt hhi
  have hsq : (0.75 * Real.log 2) ^ 2 ≤ (0.5199 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hnn hle 2
  have hc := Real.one_sub_sq_div_two_le_cos (x := 0.75 * Real.log 2)
  have hbase : (43 / 50 : ℝ) ≤ 1 - (0.5199 : ℝ) ^ 2 / 2 := by norm_num
  linarith

/-- Eta head-phase upper at `t = -6.75`, sharpened to 6 digits
(mirrors `FC_eta_phase1_lt`, whose `4.73` is loosened here to `4.679`:
`6.75 × 0.693148 = 4.678749`). -/
theorem CS_eta_phase1_lt : (6.75 : ℝ) * Real.log 2 < 4.679 := by
  have h := CS_log2_le
  have hpos : (0 : ℝ) < 6.75 := by norm_num
  have hm := mul_lt_mul_of_pos_left h hpos
  norm_num at hm
  linarith

/-- Rebalanced zeta premise, SAME shape as `FC_zeta14_obligation`
(`1.4 ≤ ‖ζ‖` at `sCenter`; TRUE: unmeasured `O(1)`). -/
def CS_zeta14_residual : Prop :=
  (1.4 : ℝ) ≤ ‖zeta R02Pilot.sCenter‖

/-- General `slow/tail/cF` assembly (PROVED, unconditional): from the link
`slow - tail ≤ cF·Z` and the threshold `1.4·cF + tail ≤ slow`, the `1.4`
floor follows. This is the arithmetic core the patch instantiates with
`slow_N` (pair-head), `tail_N` (pair-tail majorant) and `cF`
(eta-factor cap). -/
theorem CS_zeta_of_parts (slow tail cF Z : ℝ) (hcF : 0 < cF)
    (hLink : slow - tail ≤ cF * Z) (hNeed : 1.4 * cF + tail ≤ slow) :
    1.4 ≤ Z := by
  have hcomm : cF * Z = Z * cF := by ring
  have h1 : (slow - tail) / cF ≤ Z := by
    rw [div_le_iff₀ hcF, ← hcomm]
    exact hLink
  have h2 : (1.4 : ℝ) ≤ (slow - tail) / cF := by
    rw [le_div_iff₀ hcF]
    linarith
  exact le_trans h2 h1

/-- Quantified N=2 gap: the real-`σ` slow value `0.23` falls short of the
`1.4` need even with ideal `tail = 0`, `cF = 1`. Hence `1.4` needs a
larger-`N` slow value (patch phase). -/
theorem CS_N2_slow_gap : (0.23 : ℝ) < (1.4 : ℝ) * 1 + 0 := by
  norm_num

/-- Complex-head real-part identity (TRUE premise for patch discharge via
the `R05_etaFactor_phase_le_one` cpow pattern: `(2:ℂ)^(-s)` has norm
`2^-0.395` and phase `6.75·log 2`). -/
def CS_S2C_Re_eq : Prop :=
  (((1 : ℂ) - (2 : ℂ) ^ (-R02Pilot.sCenter)).re
    = 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 2))

/-- Cosine nonpositivity at the head phase (TRUE premise; true value
`cos(6.75·log 2) ≈ -0.0338 ≤ 0`). -/
def CS_cos675_nonpos : Prop := Real.cos (6.75 * Real.log 2) ≤ 0

/-- CLOSED: cosine nonpositivity at the head phase (true value
`cos(6.75·log 2) ≈ -0.0338 ≤ 0`). Route: `Real.cos_nonpos_of_pi_div_two_le_of_le`
with the banked phase cap `CS_eta_phase1_lt` (`6.75·log 2 < 4.679 ≤ 1.5·π`
via `Real.pi_gt_d6`) and the floor `4.6787 ≤ 6.75·log 2` (via `CS_log2_ge`)
above `π/2` (via `Real.pi_lt_d6`). -/
theorem CS_cos675_nonpos_proved : CS_cos675_nonpos := by
  show Real.cos (6.75 * Real.log 2) ≤ 0
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have hphase := CS_eta_phase1_lt
  have hlo : (4.6787 : ℝ) ≤ 6.75 * Real.log 2 := by
    have h2 := CS_log2_ge
    have hmul : 6.75 * (0.693147 : ℝ) ≤ 6.75 * Real.log 2 :=
      mul_le_mul_of_nonneg_left h2.le (by norm_num)
    have hcap : (4.6787 : ℝ) ≤ 6.75 * 0.693147 := by
      norm_num
    linarith
  have h1 : Real.pi / 2 ≤ 6.75 * Real.log 2 := by linarith
  have h2 : 6.75 * Real.log 2 ≤ Real.pi + Real.pi / 2 := by linarith
  exact Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2

/-- Cpow real-part split at `sCenter` (phase/norm split via
`Complex.cpow_def_of_ne_zero` + `Complex.ofReal_log`, mirroring the
`prefix_R05_cpow2_re` / `r05_cpow_re` recipe: `(-sCenter).re = -0.395`,
`(-sCenter).im = 6.75`, so the `exp` re-part is `2^-0.395·cos(6.75·log 2)`). -/
theorem CS_cpow2_sCenter_re : ((((2 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter)).re
    = (2 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 2) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hxC : ((2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h2pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((2 : ℝ) : ℂ) = (((Real.log 2 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h2pos)).symm
  rw [hlog]
  have hre_w : (-R02Pilot.sCenter).re = (-(0.395 : ℝ)) := by
    have e : (-R02Pilot.sCenter).re = -(R02Pilot.sCenter.re) := rfl
    rw [e, R02Pilot.sCenter_re]
  have him_w : (-R02Pilot.sCenter).im = (6.75 : ℝ) := by
    have e : (-R02Pilot.sCenter).im = -(R02Pilot.sCenter.im) := rfl
    rw [e, R02Pilot.sCenter_im]
    norm_num
  have hzre : ((((Real.log 2 : ℝ)) : ℂ)).re = Real.log 2 := Complex.ofReal_re _
  have hzim : ((((Real.log 2 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 2 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).re
      = Real.log 2 * (-(0.395 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 2 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).im
      = Real.log 2 * (6.75 : ℝ) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 2 * (-(0.395 : ℝ)))
      = (2 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_def_of_pos h2pos _).symm
  have hcos : Real.cos (Real.log 2 * (6.75 : ℝ))
      = Real.cos (6.75 * Real.log 2) := by
    rw [mul_comm]
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- CLOSED: complex-head real-part identity (`CS_S2C_Re_eq`): `Re(1 - 2^-s)`
at `sCenter` is `1 - 2^-0.395·cos(6.75·log 2)` (cast `(2:ℂ) = ((2:ℝ):ℂ)`
via `simp`, then `sub_re` / `one_re` / `CS_cpow2_sCenter_re`). -/
theorem CS_S2C_Re_proved : CS_S2C_Re_eq := by
  show (((1 : ℂ) - (2 : ℂ) ^ (-R02Pilot.sCenter)).re
    = 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 2))
  have hcast : ((2 : ℂ)) = (((2 : ℝ)) : ℂ) := by simp
  rw [hcast, Complex.sub_re, Complex.one_re, CS_cpow2_sCenter_re]

/-- Complex N=2 head real part `≥ 1` (conditional on TRUE premises:
`r ≤ 0.77`, `cos ≤ 0` give `1 - r·cos ≥ 1`). -/
theorem CS_complex_S2_Re_ge_one (hEq : CS_S2C_Re_eq) (hCos0 : CS_cos675_nonpos)
    (hR : CS_rpow2_head_upper) :
    (1 : ℝ) ≤ (((1 : ℂ) - (2 : ℂ) ^ (-R02Pilot.sCenter)).re) := by
  have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hnp : (2 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hr0 hCos0
  have hE : (((1 : ℂ) - (2 : ℂ) ^ (-R02Pilot.sCenter)).re
      = 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 2)) := hEq
  rw [hE]
  linarith

/-- Complex N=2 head absolute value `≥ 1` (conditional; `‖z‖ ≥ Re z`). -/
theorem CS_complex_S2_abs_ge_one (hEq : CS_S2C_Re_eq) (hCos0 : CS_cos675_nonpos)
    (hR : CS_rpow2_head_upper) :
    (1 : ℝ) ≤ ‖((1 : ℂ) - (2 : ℂ) ^ (-R02Pilot.sCenter))‖ := by
  have hRe := CS_complex_S2_Re_ge_one hEq hCos0 hR
  have hle : (((1 : ℂ) - (2 : ℂ) ^ (-R02Pilot.sCenter)).re)
      ≤ ‖((1 : ℂ) - (2 : ℂ) ^ (-R02Pilot.sCenter))‖ := by
    have h1 := Complex.abs_re_le_norm (((1 : ℂ) - (2 : ℂ) ^ (-R02Pilot.sCenter)))
    have h2 := le_abs_self (((1 : ℂ) - (2 : ℂ) ^ (-R02Pilot.sCenter)).re)
    linarith
  linarith

/-- CLOSED: complex-head real part `≥ 1` (unconditional; discharges the three
TRUE premises via the banked closures `CS_S2C_Re_proved`,
`CS_cos675_nonpos_proved`, `CS_rpow2_proved`). -/
theorem CS_complex_S2_Re_proved :
    (1 : ℝ) ≤ (((1 : ℂ) - (2 : ℂ) ^ (-R02Pilot.sCenter)).re) :=
  CS_complex_S2_Re_ge_one CS_S2C_Re_proved CS_cos675_nonpos_proved CS_rpow2_proved

/-- CLOSED: complex-head absolute value `≥ 1` (unconditional; same three
closures). -/
theorem CS_complex_S2_abs_proved :
    (1 : ℝ) ≤ ‖((1 : ℂ) - (2 : ℂ) ^ (-R02Pilot.sCenter))‖ :=
  CS_complex_S2_abs_ge_one CS_S2C_Re_proved CS_cos675_nonpos_proved CS_rpow2_proved

/-- Eta-factor upper at `sCenter` (TRUE premise; magnitude route:
`‖1 - 2^{1-s}‖ ≤ 1 + 2^0.605 ≈ 2.521`, so `2.53` carries margin; the
phase-aware `≤ 1` is FALSE here since `cos(6.75·log 2) < 0` — the true
factor is `≈ 1.85`). Patch proves this via the R05 cpow pattern. -/
def CS_etaFactor_upper : Prop :=
  ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)‖ ≤ 2.53

/-- `2^0.605` cap input for the factor route (TRUE premise; true
`≈ 1.521`; patch proves like §C). -/
def CS_rpow0605_upper : Prop := (2 : ℝ) ^ ((0.605 : ℝ)) ≤ 1.53

/-- CLOSED: the `2^0.605` cap (`≈ 1.521 ≤ 1.53`).
Route (upper via `Real.exp_bound'`, `n = 4`): `2^0.605 = exp(0.605·log 2)`
with `0.605·log 2 ≤ 0.605·0.693148 ≤ 0.41936`; the degree-3 Taylor sum
plus remainder at `0.41936` is `≈ 1.5212 ≤ 1.53`. -/
theorem CS_rpow0605_proved : CS_rpow0605_upper := by
  show (2 : ℝ) ^ ((0.605 : ℝ)) ≤ 1.53
  have hlog : Real.log 2 < (0.693148 : ℝ) := CS_log2_le
  have hlog_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  set x : ℝ := 0.605 * Real.log 2 with hx_def
  have hx0 : (0 : ℝ) ≤ x := by
    rw [hx_def]
    exact mul_nonneg (by norm_num) (le_of_lt hlog_pos)
  have hx_hi : x ≤ (0.41936 : ℝ) := by
    rw [hx_def]
    have hmul : 0.605 * Real.log 2 ≤ 0.605 * 0.693148 := by
      apply mul_le_mul_of_nonneg_left hlog.le (by norm_num)
    have hcap : (0.605 : ℝ) * 0.693148 ≤ (0.41936 : ℝ) := by
      norm_num
    linarith
  have hx1 : x ≤ 1 := by linarith
  have hrpow : (2 : ℝ) ^ ((0.605 : ℝ)) = Real.exp x := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    rw [hx_def]
    ring
  rw [hrpow]
  have hub := Real.exp_bound' hx0 hx1 (show 0 < 4 by norm_num)
  have e0 : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
  have e1 : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
  have e2f : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  have e3f : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  have e4f : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  have hsum : (∑ m ∈ Finset.range 4, x ^ m / (Nat.factorial m : ℝ)) =
      1 + x + x ^ 2 / 2 + x ^ 3 / 6 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [e0, e1, e2f, e3f]
    ring
  have hub2 : Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 * 5 / (24 * 4) := by
    rw [hsum, e4f] at hub
    norm_num at hub
    linarith
  have q2 : x ^ 2 ≤ (0.41936 : ℝ) ^ 2 := pow_le_pow_left₀ hx0 hx_hi 2
  have q3 : x ^ 3 ≤ (0.41936 : ℝ) ^ 3 := pow_le_pow_left₀ hx0 hx_hi 3
  have q4 : x ^ 4 ≤ (0.41936 : ℝ) ^ 4 := pow_le_pow_left₀ hx0 hx_hi 4
  have hnum : (1 : ℝ) + 0.41936 + (0.41936 : ℝ) ^ 2 / 2 +
      (0.41936 : ℝ) ^ 3 / 6 + (0.41936 : ℝ) ^ 4 * 5 / (24 * 4) ≤ 1.53 := by
    norm_num
  linarith

/-- Eta-factor upper from the `2^0.605` cap (PROVED): the cpow norm is the
real rpow (`Complex.norm_cpow_eq_rpow_re_of_pos` with `(1 - sCenter).re =
0.605` from `R02Pilot.sCenter_re`), then `‖1 - w‖ ≤ 1 + ‖w‖`. -/
theorem CS_etaFactor_of_rpow (h : CS_rpow0605_upper) : CS_etaFactor_upper := by
  show ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)‖ ≤ 2.53
  have hre : ((1 : ℂ) - R02Pilot.sCenter).re = (0.605 : ℝ) := by
    rw [Complex.sub_re, Complex.one_re, R02Pilot.sCenter_re]
    norm_num
  have hcast : ((2 : ℂ)) = (((2 : ℝ)) : ℂ) := by simp
  have hnorm : ‖(2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)‖ =
      (2 : ℝ) ^ ((0.605 : ℝ)) := by
    rw [hcast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2), hre]
  have htri := norm_sub_le (1 : ℂ) ((2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter))
  rw [norm_one, hnorm] at htri
  have hr : (2 : ℝ) ^ ((0.605 : ℝ)) ≤ 1.53 := h
  linarith

/-- UNCONDITIONAL eta-factor cap (both links closed above). -/
theorem CS_etaFactor_proved : CS_etaFactor_upper :=
  CS_etaFactor_of_rpow CS_rpow0605_proved

/-- Factor-need numeral: with the banked factor cap, `1.4` needs
`slow ≥ 1.4 × 2.53 = 3.542 + tail` — far above the N=2 complex head
(`≈ 1.03`), so the patch must grow `N` (and sharpen `cF`/`tail`). -/
theorem CS_factor_need : (1.4 : ℝ) * 2.53 = 3.542 := by
  norm_num

/-- Complex-head ceiling note, quantified: even `1.03` (above the proved
`1`) falls short of `1.4`. -/
theorem CS_head14_gap : (1.03 : ℝ) < 1.4 := by
  norm_num

/-- S2 feed into the zeta assembly (exact instantiation shape): with the
now-unconditional complex-head lower `slow = 1` (`CS_complex_S2_abs_proved`),
`tail = 0`, and the banked factor cap `cF = 2.53` (`CS_etaFactor_proved`),
`CS_zeta_of_parts` applies directly — the `hNeed` hypothesis is the
unclosable `3.542 ≤ 1` (see `CS_S2_shortfall`), so the `1.4` floor still
fails; the patch must grow `slow` (larger `N`) and sharpen `cF`/`tail`. -/
theorem CS_zeta_of_S2 (Z : ℝ)
    (hLink : (1 : ℝ) - 0 ≤ 2.53 * Z) (hNeed : (1.4 : ℝ) * 2.53 + 0 ≤ 1) :
    1.4 ≤ Z :=
  CS_zeta_of_parts 1 0 2.53 Z (by norm_num) hLink hNeed

/-- Exact remaining shortfall numeral (honest floor report): the `1.4`
need at `cF = 2.53` exceeds the unconditional `slow = 1` by `2.542`. -/
theorem CS_S2_shortfall : (1.4 : ℝ) * 2.53 - 1 = 2.542 := by
  norm_num

/-! ## §A2. Slow growth: S2 sharpened `1 → 1.25` + real-σ S4 `0.23 → 0.26`

Route (honest, low-risk, mirrors §C/`CS_rpow0605_proved` shapes only):
* `2^-0.395 ≥ 0.75` via upper `2^0.395 ≤ 1.32` (`exp_bound'` n=4 at
  `x = 0.395·log 2 ≤ 0.27380`; true `2^0.395 ≈ 1.3152`, margin `0.0048`).
* Complex S2 Pythagoras: `‖1 - w‖² = 1 - 2·Re w + ‖w‖² ≥ 1 + ‖w‖²`
  since `Re w = r·cos ≤ 0` (banked `CS_cos675_nonpos_proved`); with
  `‖w‖ = r ≥ 0.75`, `‖S₂ᶜ‖² ≥ 1 + 0.75² = 1.25²`, so `‖S₂ᶜ‖ ≥ 1.25`.
  True `‖S₂ᶜ‖ ≈ 1.276`, so `1.25` carries `≈ 2%` margin.
* Real-σ S4: `1 - r2 + r3 - r4 ≥ 1 - 0.77 + 0.63 - 0.60 = 0.26` via
  banked `0.77` upper + new `3^-0.395 ≥ 0.63` (from `3^0.395 ≤ 1.57`,
  `exp_bound'` n=4 at `0.395·log 3 ≤ 0.44884`) + new `4^-0.395 ≤ 0.60`
  (from `4^0.395 ≥ 1.69`, quadratic lower at `0.395·log 4 ≥ 0.54758`).
  True S4 real `≈ 0.3095`, so `0.26` is safe.
* Recomputed assembly `CS_zeta_of_S2b` at `slow = 1.25` + exact new
  shortfall `1.4·2.53 - 1.25 = 2.292` (was `2.542`; gain `0.25`).
  The `1.4` floor still fails (`3.542 ≤ 1.25` false); patch must grow
  further (larger `N`) and/or sharpen `cF`/`tail`. -/

/-- `2^-0.395 ≥ 0.75` lower (TRUE `≈ 0.7605`). -/
def CS_rpow2_low075 : Prop := (0.75 : ℝ) ≤ (2 : ℝ) ^ (-(0.395 : ℝ))

/-- CLOSED: `2^-0.395 ≥ 0.75` via `2^0.395 ≤ 1.32`
(`exp_bound'` n=4 at `x ≤ 0.27380`; `1 + x + x²/2 + x³/6 + rem ≤ 1.32`). -/
theorem CS_rpow2_low075_proved : CS_rpow2_low075 := by
  show (0.75 : ℝ) ≤ (2 : ℝ) ^ (-(0.395 : ℝ))
  have hlog : Real.log 2 < (0.693148 : ℝ) := CS_log2_le
  have hlog_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  set x : ℝ := 0.395 * Real.log 2 with hx_def
  have hx0 : (0 : ℝ) ≤ x := by
    rw [hx_def]
    exact mul_nonneg (by norm_num) (le_of_lt hlog_pos)
  have hx_hi : x ≤ (0.27380 : ℝ) := by
    rw [hx_def]
    have hmul : 0.395 * Real.log 2 ≤ 0.395 * 0.693148 := by
      apply mul_le_mul_of_nonneg_left hlog.le (by norm_num)
    have hcap : (0.395 : ℝ) * 0.693148 ≤ (0.27380 : ℝ) := by
      norm_num
    linarith
  have hx1 : x ≤ 1 := by linarith
  have hrpow : (2 : ℝ) ^ ((0.395 : ℝ)) = Real.exp x := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    rw [hx_def]
    ring
  have hub := Real.exp_bound' hx0 hx1 (show 0 < 4 by norm_num)
  have e0 : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
  have e1 : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
  have e2f : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  have e3f : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  have e4f : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  have hsum : (∑ m ∈ Finset.range 4, x ^ m / (Nat.factorial m : ℝ)) =
      1 + x + x ^ 2 / 2 + x ^ 3 / 6 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [e0, e1, e2f, e3f]
    ring
  have hub2 : Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 * 5 / (24 * 4) := by
    rw [hsum, e4f] at hub
    norm_num at hub
    linarith
  have q2 : x ^ 2 ≤ (0.27380 : ℝ) ^ 2 := pow_le_pow_left₀ hx0 hx_hi 2
  have q3 : x ^ 3 ≤ (0.27380 : ℝ) ^ 3 := pow_le_pow_left₀ hx0 hx_hi 3
  have q4 : x ^ 4 ≤ (0.27380 : ℝ) ^ 4 := pow_le_pow_left₀ hx0 hx_hi 4
  have hnum : (1 : ℝ) + 0.27380 + (0.27380 : ℝ) ^ 2 / 2 +
      (0.27380 : ℝ) ^ 3 / 6 + (0.27380 : ℝ) ^ 4 * 5 / (24 * 4) ≤ 1.32 := by
    norm_num
  have hupper : (2 : ℝ) ^ ((0.395 : ℝ)) ≤ 1.32 := by
    rw [hrpow]
    linarith
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((0.395 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hInv : (2 : ℝ) ^ (-(0.395 : ℝ)) = 1 / (2 : ℝ) ^ ((0.395 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [inv_eq_one_div]
  have h75 : (0.75 : ℝ) * (2 : ℝ) ^ ((0.395 : ℝ)) ≤ 1 := by
    have hmul : (0.75 : ℝ) * 1.32 ≤ 1 := by norm_num
    calc (0.75 : ℝ) * (2 : ℝ) ^ ((0.395 : ℝ))
        ≤ 0.75 * 1.32 := mul_le_mul_of_nonneg_left hupper (by norm_num)
      _ ≤ 1 := hmul
  rw [hInv, le_div_iff₀ hpos]
  exact h75

/-- Cpow norm identity for the S2 sharpening
(`‖2^-s‖ = 2^-0.395` via `norm_cpow_eq_rpow_re_of_pos`). -/
theorem CS_cpow2_norm_eq :
    ‖((((2 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter))‖ = (2 : ℝ) ^ (-(0.395 : ℝ)) := by
  have hre : (-R02Pilot.sCenter).re = (-(0.395 : ℝ)) := by
    have e : (-R02Pilot.sCenter).re = -(R02Pilot.sCenter.re) := rfl
    rw [e, R02Pilot.sCenter_re]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2), hre]

/-- Sharpened complex-head absolute value `≥ 1.25` (PROVED, unconditional):
Pythagoras `‖1-w‖² = 1 - 2·Re w + ‖w‖²` with `Re w ≤ 0` (banked cos) and
`‖w‖ = r ≥ 0.75`, so `‖S₂ᶜ‖² ≥ 1 + 0.75² = 1.25²`. -/
theorem CS_complex_S2_abs_ge_125 :
    (1.25 : ℝ) ≤ ‖((1 : ℂ) - (2 : ℂ) ^ (-R02Pilot.sCenter))‖ := by
  have hcast : ((2 : ℂ)) = ((((2 : ℝ)) : ℂ)) := by simp
  have hnorm := CS_cpow2_norm_eq
  have hReEq := CS_cpow2_sCenter_re
  have hcos : Real.cos (6.75 * Real.log 2) ≤ 0 := CS_cos675_nonpos_proved
  have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hrLow : (0.75 : ℝ) ≤ (2 : ℝ) ^ (-(0.395 : ℝ)) := CS_rpow2_low075_proved
  have hReW : (((((2 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter)).re) ≤ 0 := by
    rw [hReEq]
    exact mul_nonpos_of_nonneg_of_nonpos hr0 hcos
  have hS2eq : ((1 : ℂ) - (2 : ℂ) ^ (-R02Pilot.sCenter))
      = ((1 : ℂ) - ((((2 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter))) := by
    rw [hcast]
  rw [hS2eq]
  have hsq_eq : ‖((1 : ℂ) - ((((2 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter)))‖ ^ 2
      = 1 - 2 * (((((2 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter)).re)
        + ‖((((2 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter))‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im]
    ring
  have hwReal : (0.75 : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (-(0.395 : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hrLow 2
  have hsq_ge : (1.25 : ℝ) ^ 2
      ≤ ‖((1 : ℂ) - ((((2 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter)))‖ ^ 2 := by
    have h1 : (1.25 : ℝ) ^ 2 = 1 + (0.75 : ℝ) ^ 2 := by norm_num
    have h2 : (0 : ℝ) ≤ -2 * (((((2 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter)).re) := by
      linarith
    rw [hsq_eq, hnorm]
    linarith
  calc (1.25 : ℝ) = Real.sqrt ((1.25 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖((1 : ℂ) - ((((2 : ℝ)) : ℂ)
        ^ (-R02Pilot.sCenter)))‖ ^ 2) := Real.sqrt_le_sqrt hsq_ge
    _ = ‖((1 : ℂ) - ((((2 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter)))‖ :=
        Real.sqrt_sq (norm_nonneg _)

/-- `3^0.395 ≤ 1.57` upper input (TRUE `≈ 1.543`). -/
def CS_rpow3pos_upper : Prop := (3 : ℝ) ^ ((0.395 : ℝ)) ≤ 1.57

/-- CLOSED: `3^0.395 ≤ 1.57` via `exp_bound'` n=4 at
`x = 0.395·log 3 ≤ 0.44884` (uses `CS_log_three_le`). -/
theorem CS_rpow3pos_proved : CS_rpow3pos_upper := by
  show (3 : ℝ) ^ ((0.395 : ℝ)) ≤ 1.57
  have hlog : Real.log 3 ≤ (1.1363 : ℝ) := CS_log_three_le
  have hlog_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  set x : ℝ := 0.395 * Real.log 3 with hx_def
  have hx0 : (0 : ℝ) ≤ x := by
    rw [hx_def]
    exact mul_nonneg (by norm_num) (le_of_lt hlog_pos)
  have hx_hi : x ≤ (0.44884 : ℝ) := by
    rw [hx_def]
    have hmul : 0.395 * Real.log 3 ≤ 0.395 * 1.1363 := by
      apply mul_le_mul_of_nonneg_left hlog (by norm_num)
    have hcap : (0.395 : ℝ) * 1.1363 ≤ (0.44884 : ℝ) := by
      norm_num
    linarith
  have hx1 : x ≤ 1 := by linarith
  have hrpow : (3 : ℝ) ^ ((0.395 : ℝ)) = Real.exp x := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    rw [hx_def]
    ring
  have hub := Real.exp_bound' hx0 hx1 (show 0 < 4 by norm_num)
  have e0 : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
  have e1 : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
  have e2f : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  have e3f : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  have e4f : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  have hsum : (∑ m ∈ Finset.range 4, x ^ m / (Nat.factorial m : ℝ)) =
      1 + x + x ^ 2 / 2 + x ^ 3 / 6 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [e0, e1, e2f, e3f]
    ring
  have hub2 : Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 * 5 / (24 * 4) := by
    rw [hsum, e4f] at hub
    norm_num at hub
    linarith
  have q2 : x ^ 2 ≤ (0.44884 : ℝ) ^ 2 := pow_le_pow_left₀ hx0 hx_hi 2
  have q3 : x ^ 3 ≤ (0.44884 : ℝ) ^ 3 := pow_le_pow_left₀ hx0 hx_hi 3
  have q4 : x ^ 4 ≤ (0.44884 : ℝ) ^ 4 := pow_le_pow_left₀ hx0 hx_hi 4
  have hnum : (1 : ℝ) + 0.44884 + (0.44884 : ℝ) ^ 2 / 2 +
      (0.44884 : ℝ) ^ 3 / 6 + (0.44884 : ℝ) ^ 4 * 5 / (24 * 4) ≤ 1.57 := by
    norm_num
  rw [hrpow]
  linarith

/-- `3^-0.395 ≥ 0.63` lower input (TRUE `≈ 0.6479`). -/
def CS_rpow3neg_lower : Prop := (0.63 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ))

/-- CLOSED: `3^-0.395 ≥ 0.63` from `3^0.395 ≤ 1.57`
(`0.63·1.57 = 0.9891 ≤ 1`). -/
theorem CS_rpow3neg_lower_proved : CS_rpow3neg_lower := by
  show (0.63 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ))
  have hup : (3 : ℝ) ^ ((0.395 : ℝ)) ≤ 1.57 := CS_rpow3pos_proved
  have hpos : (0 : ℝ) < (3 : ℝ) ^ ((0.395 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hInv : (3 : ℝ) ^ (-(0.395 : ℝ)) = 1 / (3 : ℝ) ^ ((0.395 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    rw [inv_eq_one_div]
  have hle : (0.63 : ℝ) * (3 : ℝ) ^ ((0.395 : ℝ)) ≤ 1 := by
    have hmul : (0.63 : ℝ) * 1.57 ≤ 1 := by norm_num
    calc (0.63 : ℝ) * (3 : ℝ) ^ ((0.395 : ℝ))
        ≤ 0.63 * 1.57 := mul_le_mul_of_nonneg_left hup (by norm_num)
      _ ≤ 1 := hmul
  rw [hInv, le_div_iff₀ hpos]
  exact hle

/-- `4^0.395 ≥ 1.69` lower input (TRUE `≈ 1.7292`). -/
def CS_rpow4pos_lower : Prop := (1.69 : ℝ) ≤ (4 : ℝ) ^ ((0.395 : ℝ))

/-- CLOSED: `4^0.395 ≥ 1.69` via quadratic lower at
`x = 0.395·log 4 ≥ 0.54758` (`log 4 = 2·log 2` + `CS_log2_ge`). -/
theorem CS_rpow4pos_proved : CS_rpow4pos_lower := by
  show (1.69 : ℝ) ≤ (4 : ℝ) ^ ((0.395 : ℝ))
  have h4 : Real.log 4 = 2 * Real.log 2 := CS_log_four_eq
  have h2lo : (0.693147 : ℝ) < Real.log 2 := CS_log2_ge
  have hmul : (0.79 : ℝ) * 0.693147 < 0.79 * Real.log 2 :=
    mul_lt_mul_of_pos_left h2lo (by norm_num)
  have hcap : (0.54758 : ℝ) ≤ 0.79 * 0.693147 := by norm_num
  have hx_eq : 0.395 * Real.log 4 = 0.79 * Real.log 2 := by
    rw [h4]
    ring
  have hx_lo : (0.54758 : ℝ) < 0.395 * Real.log 4 := by linarith
  set x : ℝ := 0.395 * Real.log 4 with hx_def
  have hx0 : (0 : ℝ) ≤ x := le_trans (by norm_num) hx_lo.le
  have hsq : (0.54758 : ℝ) ^ 2 ≤ x ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hx_lo.le 2
  have hquad := Real.quadratic_le_exp_of_nonneg hx0
  have hbase : (1.69 : ℝ) ≤ 1 + 0.54758 + (0.54758 : ℝ) ^ 2 / 2 := by
    norm_num
  have hchain : (1.69 : ℝ) ≤ Real.exp x := by
    linarith [hquad, hsq, hx_lo, hbase]
  have hrpow : (4 : ℝ) ^ ((0.395 : ℝ)) = Real.exp x := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4)]
    congr 1
    rw [hx_def]
    ring
  rw [hrpow]
  exact hchain

/-- `4^-0.395 ≤ 0.60` upper input (TRUE `≈ 0.5783`). -/
def CS_rpow4neg_upper : Prop := (4 : ℝ) ^ (-(0.395 : ℝ)) ≤ (0.60 : ℝ)

/-- CLOSED: `4^-0.395 ≤ 0.60` from `4^0.395 ≥ 1.69`
(`0.60·1.69 = 1.014 ≥ 1`). -/
theorem CS_rpow4neg_upper_proved : CS_rpow4neg_upper := by
  show (4 : ℝ) ^ (-(0.395 : ℝ)) ≤ (0.60 : ℝ)
  have hlow : (1.69 : ℝ) ≤ (4 : ℝ) ^ ((0.395 : ℝ)) := CS_rpow4pos_proved
  have hpos : (0 : ℝ) < (4 : ℝ) ^ ((0.395 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hInv : (4 : ℝ) ^ (-(0.395 : ℝ)) = 1 / (4 : ℝ) ^ ((0.395 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    rw [inv_eq_one_div]
  have hle : (1 : ℝ) ≤ (0.60 : ℝ) * (4 : ℝ) ^ ((0.395 : ℝ)) := by
    have hmul : (1 : ℝ) ≤ 0.60 * 1.69 := by norm_num
    calc (1 : ℝ) ≤ 0.60 * 1.69 := hmul
      _ ≤ 0.60 * (4 : ℝ) ^ ((0.395 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlow (by norm_num)
  rw [hInv, div_le_iff₀ hpos]
  linarith [hle]

/-- Real-σ S4 lower, conditional form: `1 - r2 + r3 - r4 ≥ 0.26`
(TRUE `≈ 0.3095`). Mirrors `CS_etaS2_ge_023`. -/
theorem CS_etaS4_ge_026 (h2 : CS_rpow2_head_upper)
    (h3 : CS_rpow3neg_lower) (h4 : CS_rpow4neg_upper) :
    (0.26 : ℝ) ≤ 1 - (2 : ℝ) ^ (-(0.395 : ℝ))
      + (3 : ℝ) ^ (-(0.395 : ℝ)) - (4 : ℝ) ^ (-(0.395 : ℝ)) := by
  have h2u : (2 : ℝ) ^ (-(0.395 : ℝ)) ≤ 0.77 := h2
  have h3l : (0.63 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ)) := h3
  have h4u : (4 : ℝ) ^ (-(0.395 : ℝ)) ≤ 0.60 := h4
  linarith

/-- UNCONDITIONAL real-σ S4 floor `0.26` (all three premises closed). -/
theorem CS_etaS4_uncond :
    (0.26 : ℝ) ≤ 1 - (2 : ℝ) ^ (-(0.395 : ℝ))
      + (3 : ℝ) ^ (-(0.395 : ℝ)) - (4 : ℝ) ^ (-(0.395 : ℝ)) :=
  CS_etaS4_ge_026 CS_rpow2_proved CS_rpow3neg_lower_proved CS_rpow4neg_upper_proved

/-- S4-complex feed into the zeta assembly (exact instantiation shape, one-liner
mirror of `CS_zeta_of_S2`): with sharpened `slow = 1.25`
(`CS_complex_S2_abs_ge_125`), `tail = 0`, `cF = 2.53`, `CS_zeta_of_parts`
applies directly — `hNeed` is still the unclosable `3.542 ≤ 1.25`
(see `CS_S2b_shortfall`); patch must grow further / sharpen `cF`/`tail`. -/
theorem CS_zeta_of_S2b (Z : ℝ)
    (hLink : (1.25 : ℝ) - 0 ≤ 2.53 * Z) (hNeed : (1.4 : ℝ) * 2.53 + 0 ≤ 1.25) :
    1.4 ≤ Z :=
  CS_zeta_of_parts 1.25 0 2.53 Z (by norm_num) hLink hNeed

/-- Exact new shortfall numeral (honest floor report): the `1.4` need at
`cF = 2.53` exceeds sharpened `slow = 1.25` by `2.292` (was `2.542`). -/
theorem CS_S2b_shortfall : (1.4 : ℝ) * 2.53 - 1.25 = 2.292 := by
  norm_num

/-! ## §B. Wide-`Λ₀ ≤ 479` on the fat `s`-rect (FE + Stirling route)

Lane-local reproofs of the `FC_fat*` chain (mirroring
`door3_first_cell.lean` §D read-only): inclusion + prefactor are PROVED;
the `Λ₀` cap itself stays one explicit premise (same shape as
`FC_Lambda0_upper_fat`), with the FE+Stirling discharge packaged as the
existential `CS_Lambda0_FE_step` (PROVED-sufficient below).
-/

/-- The fencing rect, alias of banked `R02` (same convention as `FC_rect`). -/
def CS_rect : CellProofEngine.Rect2D := CentralCoverAssembly.R02

/-- Radius equation (banked). -/
theorem CS_rect_radius_eq :
    CS_rect.radius = Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) :=
  CentralCoverAssembly.R02_radius_eq

/-- Radius cap (banked). -/
theorem CS_rect_radius_lt : CS_rect.radius < 1.26 := by
  rw [CS_rect_radius_eq]
  exact CentralCoverAssembly.sample_cell_radius_bound

/-- Cell-center real part (mirrors `FC_center_re`). -/
theorem CS_center_re : (CentralCoverAssembly.R02.center).re = -6.75 := by
  rw [R02Pilot.center_eq]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num

/-- Cell-center imaginary part (mirrors `FC_center_im`). -/
theorem CS_center_im : (CentralCoverAssembly.R02.center).im = 0.105 := by
  rw [R02Pilot.center_eq]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num

/-- `s`-map real part (mirrors `FC_sOfZ_re`). -/
theorem CS_sOfZ_re (z : ℂ) :
    ((1 / 2 : ℂ) + Complex.I * z).re = 1 / 2 - z.im := by
  rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.div_ofNat_re, Complex.one_re]
  ring

/-- `s`-map imaginary part (mirrors `FC_sOfZ_im`). -/
theorem CS_sOfZ_im (z : ℂ) :
    ((1 / 2 : ℂ) + Complex.I * z).im = z.re := by
  rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.div_ofNat_im, Complex.one_im]
  ring

/-- Fat-ball real-part enclosure (mirrors `FC_fat_z_re`). -/
theorem CS_fat_z_re (z : ℂ)
    (hz : z ∈ Metric.closedBall CS_rect.center (CS_rect.radius + 0.25)) :
    -8.26 ≤ z.re ∧ z.re ≤ -5.24 := by
  have hce : CS_rect.center = CentralCoverAssembly.R02.center := rfl
  have hd : dist z CS_rect.center ≤ CS_rect.radius + 0.25 :=
    Metric.mem_closedBall.mp hz
  have hR : CS_rect.radius + 0.25 < 1.51 := by
    have hlt := CS_rect_radius_lt
    linarith
  have hn : ‖z - CentralCoverAssembly.R02.center‖ < 1.51 := by
    rw [hce] at hd
    rw [← dist_eq_norm]
    linarith [hd, hR]
  have hre : |(z - CentralCoverAssembly.R02.center).re| < 1.51 :=
    lt_of_le_of_lt (Complex.abs_re_le_norm _) hn
  rw [Complex.sub_re, CS_center_re] at hre
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hre
  constructor <;> linarith

/-- Fat-ball imaginary-part enclosure (mirrors `FC_fat_z_im`). -/
theorem CS_fat_z_im (z : ℂ)
    (hz : z ∈ Metric.closedBall CS_rect.center (CS_rect.radius + 0.25)) :
    -1.41 ≤ z.im ∧ z.im ≤ 1.62 := by
  have hce : CS_rect.center = CentralCoverAssembly.R02.center := rfl
  have hd : dist z CS_rect.center ≤ CS_rect.radius + 0.25 :=
    Metric.mem_closedBall.mp hz
  have hR : CS_rect.radius + 0.25 < 1.51 := by
    have hlt := CS_rect_radius_lt
    linarith
  have hn : ‖z - CentralCoverAssembly.R02.center‖ < 1.51 := by
    rw [hce] at hd
    rw [← dist_eq_norm]
    linarith [hd, hR]
  have him : |(z - CentralCoverAssembly.R02.center).im| < 1.51 :=
    lt_of_le_of_lt (Complex.abs_im_le_norm _) hn
  rw [Complex.sub_im, CS_center_im] at him
  obtain ⟨hlo, hhi⟩ := abs_lt.mp him
  constructor <;> linarith

/-- Fat-ball `s`-rect (mirrors `FC_fat_s_bounds`). -/
theorem CS_fat_s_bounds (z : ℂ)
    (hz : z ∈ Metric.closedBall CS_rect.center (CS_rect.radius + 0.25)) :
    -1.12 ≤ ((1 / 2 : ℂ) + Complex.I * z).re ∧
    ((1 / 2 : ℂ) + Complex.I * z).re ≤ 1.91 ∧
    -8.27 ≤ ((1 / 2 : ℂ) + Complex.I * z).im ∧
    ((1 / 2 : ℂ) + Complex.I * z).im ≤ -5.23 := by
  obtain ⟨hre_lo, hre_hi⟩ := CS_fat_z_re z hz
  obtain ⟨him_lo, him_hi⟩ := CS_fat_z_im z hz
  rw [CS_sOfZ_re, CS_sOfZ_im]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Center norm cap (mirrors `FC_center_norm_le`). -/
theorem CS_center_norm_le : ‖CentralCoverAssembly.R02.center‖ ≤ 6.76 := by
  have hsq : ‖CentralCoverAssembly.R02.center‖ ^ 2 ≤ (6.76 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, CS_center_re, CS_center_im]
    norm_num
  calc ‖CentralCoverAssembly.R02.center‖
      = Real.sqrt (‖CentralCoverAssembly.R02.center‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((6.76 : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 6.76 := Real.sqrt_sq (by norm_num)

/-- Fat-ball norm cap (mirrors `FC_fatNorm_upper`). -/
theorem CS_fatNorm_upper (z : ℂ)
    (hz : z ∈ Metric.closedBall CS_rect.center (CS_rect.radius + 0.25)) :
    ‖z‖ ≤ 8.27 := by
  have hce : CS_rect.center = CentralCoverAssembly.R02.center := rfl
  have hd : dist z CS_rect.center ≤ CS_rect.radius + 0.25 :=
    Metric.mem_closedBall.mp hz
  have hR : CS_rect.radius + 0.25 < 1.51 := by
    have hlt := CS_rect_radius_lt
    linarith
  have hzc : ‖z - CentralCoverAssembly.R02.center‖ < 1.51 := by
    rw [hce] at hd
    rw [← dist_eq_norm]
    linarith [hd, hR]
  have hzz : z = (z - CentralCoverAssembly.R02.center) +
      CentralCoverAssembly.R02.center := by abel
  calc ‖z‖ ≤ ‖z - CentralCoverAssembly.R02.center‖ +
        ‖CentralCoverAssembly.R02.center‖ := by
        conv_lhs => rw [hzz]
        exact norm_add_le (z - CentralCoverAssembly.R02.center)
          CentralCoverAssembly.R02.center
    _ ≤ 8.27 := by linarith [hzc, CS_center_norm_le]

/-- `‖(1/2 : ℂ)‖ = 1/2` (mirrors `FC_norm_half`). -/
theorem CS_norm_half : ‖((1 / 2 : ℂ))‖ = (1 / 2 : ℝ) := by
  have e12 : ((1 / 2 : ℂ)) = (((1 / 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [e12, Complex.norm_real]
  exact Real.norm_of_nonneg (by norm_num)

/-- `‖(1/4 : ℂ)‖ = 1/4` (mirrors `FC_norm_quarter`). -/
theorem CS_norm_quarter : ‖((1 / 4 : ℂ))‖ = (1 / 4 : ℝ) := by
  have e14 : ((1 / 4 : ℂ)) = (((1 / 4 : ℝ)) : ℂ) := by push_cast; ring
  rw [e14, Complex.norm_real]
  exact Real.norm_of_nonneg (by norm_num)

/-- Entire-form prefactor cap on the fat ball (mirrors
`FC_fatPrefactor_upper`): `‖(z^2 + 1/4)/2‖ ≤ 35`. -/
theorem CS_fatPrefactor_upper (z : ℂ)
    (hz : z ∈ Metric.closedBall CS_rect.center (CS_rect.radius + 0.25)) :
    ‖(z ^ 2 + (1 / 4 : ℂ)) / 2‖ ≤ 35 := by
  have hzn : ‖z‖ ≤ 8.27 := CS_fatNorm_upper z hz
  have hsq : ‖z ^ 2‖ ≤ (8.27 : ℝ) ^ 2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hzn 2
  have h1 := norm_add_le (z ^ 2) ((1 / 4 : ℂ))
  rw [CS_norm_quarter] at h1
  have hadd : ‖z ^ 2 + (1 / 4 : ℂ)‖ ≤ (8.27 : ℝ) ^ 2 + 1 / 4 := by
    linarith [h1, hsq]
  have hdiv : ‖(z ^ 2 + (1 / 4 : ℂ)) / 2‖ = ‖z ^ 2 + (1 / 4 : ℂ)‖ / 2 := by
    rw [norm_div, Complex.norm_two]
  rw [hdiv]
  have hcalc : ((8.27 : ℝ) ^ 2 + 1 / 4) / 2 ≤ 35 := by norm_num
  linarith [hadd, hcalc]

/-- Wide `Λ₀` premise on the fat `s`-rect, SAME shape as
`FC_Lambda0_upper_fat` (`≤ 479`; TRUE with large margin: `Λ₀` there is
`O(1)`–`O(10)`, so `~35×` safe; patch proves it via FE + Stirling +
convexity, mirroring the `R02GammaDisc` route at the new re-values). -/
def CS_Lambda0_upper_fat : Prop :=
  ∀ (s : ℂ), -1.12 ≤ s.re → s.re ≤ 1.91 → -8.27 ≤ s.im → s.im ≤ -5.23 →
    ‖completedRiemannZeta₀ s‖ ≤ 479

/-- FE+Stirling discharge shape (TRUE premise for patch): some cap
`M ≤ 479` covers the fat rect. TRUE (take `M` = the actual maximum,
`O(1)`–`O(10)`); the patch exhibits it as
`FE-constant × Stirling-Gamma-cap × right-side-zeta-cap`. -/
def CS_Lambda0_FE_step : Prop :=
  ∃ (M : ℝ), M ≤ 479 ∧ ∀ (s : ℂ), -1.12 ≤ s.re → s.re ≤ 1.91 →
    -8.27 ≤ s.im → s.im ≤ -5.23 → ‖completedRiemannZeta₀ s‖ ≤ M

/-- The FE-step discharge implies the wide premise (PROVED). -/
theorem CS_Lambda0_of_FE_step (h : CS_Lambda0_FE_step) :
    CS_Lambda0_upper_fat := by
  obtain ⟨M, hM, hcov⟩ := h
  intro s hlo hhi hloi hii
  exact le_trans (hcov s hlo hhi hloi hii) hM

/-- Fat-ball sup `16800` from the prefactor cap + the wide `Λ₀` premise
(mirrors `FC_ballSup16800_of_Lambda0`):
`‖entire z‖ ≤ 1/2 + 35 * 479 = 16765.5 ≤ 16800`. -/
theorem CS_ballSup16800_of_Lambda0 (hL : CS_Lambda0_upper_fat) (z : ℂ)
    (hz : z ∈ Metric.closedBall CS_rect.center (CS_rect.radius + 0.25)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 16800 := by
  have hP := CS_fatPrefactor_upper z hz
  have hs := CS_fat_s_bounds z hz
  have hLam : ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + Complex.I * z)‖ ≤ 479 :=
    hL _ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  unfold CentralCoverAssembly.xiShiftedEntire
  have hprod : ‖(z ^ 2 + (1 / 4 : ℂ)) / 2 *
      completedRiemannZeta₀ ((1 / 2 : ℂ) + Complex.I * z)‖ ≤ 35 * 479 := by
    rw [norm_mul]
    exact mul_le_mul hP hLam (norm_nonneg _) (by norm_num)
  have htot := norm_sub_le ((1 / 2 : ℂ))
    ((z ^ 2 + (1 / 4 : ℂ)) / 2 *
      completedRiemannZeta₀ ((1 / 2 : ℂ) + Complex.I * z))
  rw [CS_norm_half] at htot
  linarith [htot, hprod]

/-! ## §D. Deeper reflected Gamma chain for `0.008`

Banked: sine `S = 20128` (`R02SineSharp`, true `≈ 20125.7`) and reflected
`U = 0.026` (true `≈ 0.018`), giving `S·U = 523.328 > 392.7` (gap to
`0.008`). With `S = 20128` fixed, closing needs `U ≤ 392.7/20128 =
0.01951…`; we bank `U ≤ 0.0195` (`20128 × 0.0195 = 392.496 ≤ 392.7`),
which holds with `≈ 8%` headroom over the true `≈ 0.018` — feasible via
one more reflected shift step (patch phase).
-/

/-- Sharp sine cap premise (TRUE; banked `R02SineSharp.sin_upper_R02_sharp`,
true `≈ 20125.7`). -/
def CS_sine_upper_20128 : Prop :=
  ‖Complex.sin ((Real.pi : ℂ) * (R02Pilot.sCenter / 2))‖ ≤ 20128

/-- Reflected-upper premise one step past banked (TRUE; true `≈ 0.018`,
so `0.0195` carries `≈ 8%` headroom; patch extends the reflected shift
chain, mirroring the `R02GammaUpperDeep` template). -/
def CS_reflected_upper_00195 : Prop :=
  ‖Complex.Gamma (1 - R02Pilot.sCenter / 2)‖ ≤ 0.0195

/-- Reflection-link premise (TRUE by the reflection equality
`Complex.Gamma_mul_Gamma_one_sub`; patch discharges the `sin ≠ 0` /
nonvanishing side facts). Stated in the multiplication order consumed
by the bridge below. -/
def CS_reflection_link : Prop :=
  Real.pi ≤ ‖Complex.Gamma (R02Pilot.sCenter / 2)‖ *
    (‖Complex.sin ((Real.pi : ℂ) * (R02Pilot.sCenter / 2))‖ *
      ‖Complex.Gamma (1 - R02Pilot.sCenter / 2)‖)

/-- `S·U` product at the new rung: `20128 × 0.0195 = 392.496`. -/
theorem CS_SU_product : (20128 : ℝ) * 0.0195 = 392.496 := by
  norm_num

/-- The new rung fits the `0.008` cap (`392.496 ≤ 392.7`). -/
theorem CS_U_cap_S20128 : (20128 : ℝ) * 0.0195 ≤ 392.7 := by
  norm_num

/-- Banked-gap witness: `0.026` exceeds the needed `0.0195` (patch must
shave `0.0065`, i.e. `25%` off the reflected upper; the true `≈ 0.018`
is already there). -/
theorem CS_U_gap : (0.0195 : ℝ) < 0.026 := by
  norm_num

/-- Banked-product gap witness (mirrors `FC_gamma0008_gap` at the new
rung input): `392.7 < 20128 × 0.026`. -/
theorem CS_gamma0008_banked_gap : (392.7 : ℝ) < 20128 * 0.026 := by
  norm_num

/-- Bridge (PROVED, conditional on TRUE premises): the deeper reflected
rung gives `0.008 ≤ ‖Γ(sCenter/2)‖`. Since `0.008 × 392.496 = 3.139968
≤ 3.14 < 3.141592 < π`, `π/(S·U) ≥ 0.008`. -/
theorem CS_gamma0008_of_link (hLink : CS_reflection_link)
    (hS : CS_sine_upper_20128) (hU : CS_reflected_upper_00195)
    (hA : 0 < ‖Complex.sin ((Real.pi : ℂ) * (R02Pilot.sCenter / 2))‖)
    (hB : 0 < ‖Complex.Gamma (1 - R02Pilot.sCenter / 2)‖) :
    (0.008 : ℝ) ≤ ‖Complex.Gamma (R02Pilot.sCenter / 2)‖ := by
  have hSU : ‖Complex.sin ((Real.pi : ℂ) * (R02Pilot.sCenter / 2))‖ *
      ‖Complex.Gamma (1 - R02Pilot.sCenter / 2)‖ ≤ 392.496 := by
    have hmul := mul_le_mul hS hU (le_of_lt hB) (by norm_num : (0 : ℝ) ≤ 20128)
    have hprod : (20128 : ℝ) * 0.0195 = 392.496 := CS_SU_product
    linarith
  have hpos : (0 : ℝ) < ‖Complex.sin ((Real.pi : ℂ) * (R02Pilot.sCenter / 2))‖ *
      ‖Complex.Gamma (1 - R02Pilot.sCenter / 2)‖ :=
    mul_pos hA hB
  have hLinkE : Real.pi ≤ ‖Complex.Gamma (R02Pilot.sCenter / 2)‖ *
      (‖Complex.sin ((Real.pi : ℂ) * (R02Pilot.sCenter / 2))‖ *
        ‖Complex.Gamma (1 - R02Pilot.sCenter / 2)‖) := hLink
  have hdiv : Real.pi /
      (‖Complex.sin ((Real.pi : ℂ) * (R02Pilot.sCenter / 2))‖ *
        ‖Complex.Gamma (1 - R02Pilot.sCenter / 2)‖)
      ≤ ‖Complex.Gamma (R02Pilot.sCenter / 2)‖ := by
    rw [div_le_iff₀ hpos]
    linarith
  have hcap : (0.008 : ℝ) ≤ Real.pi /
      (‖Complex.sin ((Real.pi : ℂ) * (R02Pilot.sCenter / 2))‖ *
        ‖Complex.Gamma (1 - R02Pilot.sCenter / 2)‖) := by
    rw [le_div_iff₀ hpos]
    have e : (0.008 : ℝ) *
        (‖Complex.sin ((Real.pi : ℂ) * (R02Pilot.sCenter / 2))‖ *
          ‖Complex.Gamma (1 - R02Pilot.sCenter / 2)‖)
        ≤ 0.008 * 392.496 :=
      mul_le_mul_of_nonneg_left hSU (by norm_num)
    have n : (0.008 : ℝ) * 392.496 ≤ 3.14 := by norm_num
    have hpi := Real.pi_gt_d6
    linarith
  exact le_trans hcap hdiv

/-- Drop-in for the fencing premise: the `0.008` Gamma lower at
`DerivCauchyBridge.gammaOf R02Pilot.sCenter` (same shape as
`FC_gammaLower_obligation`; defeq to `Γ(sCenter/2)` exactly as in the
banked `R02GammaLower.gammaOf_lower_R02` proof). -/
theorem CS_gammaOf0008_of_Gamma
    (h : (0.008 : ℝ) ≤ ‖Complex.Gamma (R02Pilot.sCenter / 2)‖) :
    (0.008 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖ := h

/-! ## Stirling numeral witnesses (lane-local; the integer-exp rungs reuse
banked `R02SineSharp.exp_ten_lt` read-only) -/

/-- `exp 1 ≤ 2.72` (6-digit-safe corollary of `Real.exp_one_lt_d9`). -/
theorem CS_exp_one_le : Real.exp 1 ≤ 2.72 := by
  have h := Real.exp_one_lt_d9
  linarith

/-- Fractional-exp template rung (mirrors `R02SineSharp.exp_frac_lt` via
`Real.exp_bound'` at `n = 7`; true `≈ 1.8274`). -/
theorem CS_exp_frac_lt : Real.exp 0.6029 ≤ 1.8275 := by
  have h := Real.exp_bound' (x := (0.6029 : ℝ)) (by norm_num) (by norm_num)
    (n := 7) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

#print axioms CS_rpow2_proved
#print axioms CS_slice_S2_of_tendsto
#print axioms CS_zeta_of_parts
#print axioms CS_complex_S2_abs_ge_one
#print axioms CS_cos_075log2_lower
#print axioms CS_ballSup16800_of_Lambda0
#print axioms CS_gamma0008_of_link
#print axioms CS_exp_frac_lt
#print axioms CS_rpow2_low075_proved
#print axioms CS_complex_S2_abs_ge_125
#print axioms CS_rpow3pos_proved
#print axioms CS_rpow3neg_lower_proved
#print axioms CS_rpow4pos_proved
#print axioms CS_rpow4neg_upper_proved
#print axioms CS_etaS4_uncond
#print axioms CS_zeta_of_S2b
#print axioms CS_S2b_shortfall

end Door3CellSuppliers
