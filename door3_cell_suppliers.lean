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

/-! ## §A3. Phase-aware eta-factor sharpening `2.53 → 1.87`

Route (honest, cheapest-first per ETA-NEXT2): keep `slow = 1.25`
(`CS_complex_S2_abs_ge_125`) and sharpen `cF` via the Pythagoras UPPER
`‖1-w‖² = 1 - 2·Re w + ‖w‖²` with a LOWER bound on `Re w`.
Here `w = 2^{1-s}`, `‖w‖ = 2^0.605 ≤ 1.53` (banked), `Re w = r·cos φ`
with the same head phase `φ = 6.75·log 2` (so `(1-s).im = 6.75` reuses
the banked phase interval `[4.6787, 4.679)`).
Since `φ` sits `≈ 0.0336` below `3π/2`, `cos φ = sin d ≥ -|d| ≥ -0.05`
with `d = φ - 3π/2`, `|d| ≤ 0.05` (coarse `π` + phase bounds only).
Hence `Re w ≥ -0.05·r ≥ -0.0765`, so
`‖1-w‖² ≤ 1 + 0.153 + 1.53² = 3.4939 ≤ 1.87² = 3.4969`.
True `cF ≈ 1.85`, so `1.87` carries `≈ 1%` margin.
New need `1.4·1.87 = 2.618`; shortfall vs `slow = 1.25` is `1.368`
(was `2.292`; gain `0.924`). The `1.4` floor still fails
(`2.618 ≤ 1.25` false); patch must still grow `slow` / sharpen `tail`. -/

/-- Cosine lower at the head phase (`≥ -0.05`; true `≈ -0.0338`). -/
theorem CS_cos675_lower_neg005 :
    (-0.05 : ℝ) ≤ Real.cos (6.75 * Real.log 2) := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have hphase_hi := CS_eta_phase1_lt
  have hlo : (4.6787 : ℝ) ≤ 6.75 * Real.log 2 := by
    have h2 := CS_log2_ge
    have hmul : 6.75 * (0.693147 : ℝ) ≤ 6.75 * Real.log 2 :=
      mul_le_mul_of_nonneg_left h2.le (by norm_num)
    have hcap : (4.6787 : ℝ) ≤ 6.75 * 0.693147 := by
      norm_num
    linarith
  set x : ℝ := 6.75 * Real.log 2 with hx_def
  set d : ℝ := x - 3 * Real.pi / 2 with hd_def
  have hd_lo : (-0.05 : ℝ) ≤ d := by
    rw [hd_def]
    linarith
  have hd_hi : d ≤ (0.05 : ℝ) := by
    rw [hd_def]
    linarith
  have h32eq : (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 := by
    ring
  have hcos32 : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [h32eq, Real.cos_add, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hsin32 : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [h32eq, Real.sin_add, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hx_eq : x = 3 * Real.pi / 2 + d := by
    rw [hd_def]
    ring
  have hcos_eq : Real.cos x = Real.sin d := by
    rw [hx_eq, Real.cos_add, hcos32, hsin32]
    ring
  have hsin_lb : (-0.05 : ℝ) ≤ Real.sin d := by
    by_cases hd0 : (0 : ℝ) ≤ d
    · have hd_pi : d ≤ Real.pi := by linarith
      have hnn : (0 : ℝ) ≤ Real.sin d :=
        Real.sin_nonneg_of_nonneg_of_le_pi hd0 hd_pi
      linarith
    · push_neg at hd0
      have he_pos : (0 : ℝ) < -d := by linarith
      have hle : Real.sin (-d) ≤ -d := Real.sin_le he_pos.le
      have hneg : Real.sin d = -Real.sin (-d) := by
        have h := Real.sin_neg (x := -d)
        rw [neg_neg] at h
        exact h
      linarith
  rw [hcos_eq]
  exact hsin_lb

/-- Cpow real-part split for the eta factor (`1 - sCenter` phase/norm
split, mirror of `CS_cpow2_sCenter_re`: `(1-s).re = 0.605`,
`(1-s).im = 6.75`). -/
theorem CS_cpow_factor_re : ((((2 : ℝ)) : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)).re
    = (2 : ℝ) ^ ((0.605 : ℝ)) * Real.cos (6.75 * Real.log 2) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hxC : ((2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h2pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((2 : ℝ) : ℂ) = (((Real.log 2 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h2pos)).symm
  rw [hlog]
  have hre_w : (((Real.log 2 : ℝ)) : ℂ).re = Real.log 2 := Complex.ofReal_re _
  have hzim : (((Real.log 2 : ℝ)) : ℂ).im = 0 := Complex.ofReal_im _
  have hre_z : ((1 : ℂ) - R02Pilot.sCenter).re = (0.605 : ℝ) := by
    rw [Complex.sub_re, Complex.one_re, R02Pilot.sCenter_re]
    norm_num
  have him_z : ((1 : ℂ) - R02Pilot.sCenter).im = (6.75 : ℝ) := by
    rw [Complex.sub_im, Complex.one_im, R02Pilot.sCenter_im]
    norm_num
  have harg_re : ((((Real.log 2 : ℝ)) : ℂ) * ((1 : ℂ) - R02Pilot.sCenter)).re
      = Real.log 2 * (0.605 : ℝ) := by
    rw [Complex.mul_re, hre_w, hzim, hre_z]
    ring
  have harg_im : ((((Real.log 2 : ℝ)) : ℂ) * ((1 : ℂ) - R02Pilot.sCenter)).im
      = Real.log 2 * (6.75 : ℝ) := by
    rw [Complex.mul_im, hre_w, hzim, him_z]
    ring
  have hexp : Real.exp (Real.log 2 * (0.605 : ℝ))
      = (2 : ℝ) ^ ((0.605 : ℝ)) :=
    (Real.rpow_def_of_pos h2pos _).symm
  have hcos : Real.cos (Real.log 2 * (6.75 : ℝ))
      = Real.cos (6.75 * Real.log 2) := by
    rw [mul_comm]
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- Cpow norm identity for the factor (`‖2^{1-s}‖ = 2^0.605`). -/
theorem CS_cpow_factor_norm_eq :
    ‖((((2 : ℝ)) : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter))‖
      = (2 : ℝ) ^ ((0.605 : ℝ)) := by
  have hre : ((1 : ℂ) - R02Pilot.sCenter).re = (0.605 : ℝ) := by
    rw [Complex.sub_re, Complex.one_re, R02Pilot.sCenter_re]
    norm_num
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2), hre]

/-- Sharpened eta-factor cap `≤ 1.87` (TRUE `≈ 1.85`). -/
def CS_etaFactor_upper_187 : Prop :=
  ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)‖ ≤ 1.87

/-- Phase-aware factor upper from the `2^0.605` cap + the `-0.05` cosine
floor (PROVED): Pythagoras upper `‖1-w‖² = 1 - 2·Re w + ‖w‖²` with
`Re w ≥ -0.0765`, `‖w‖ ≤ 1.53`, so `‖1-w‖² ≤ 3.4939 ≤ 1.87²`. -/
theorem CS_etaFactor_187_of_bounds (hCap : CS_rpow0605_upper)
    (hCos : (-0.05 : ℝ) ≤ Real.cos (6.75 * Real.log 2)) :
    CS_etaFactor_upper_187 := by
  show ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)‖ ≤ 1.87
  have hReEq := CS_cpow_factor_re
  have hnormR := CS_cpow_factor_norm_eq
  have hcast : ((2 : ℂ)) = ((((2 : ℝ)) : ℂ)) := by simp
  have hrHi : (2 : ℝ) ^ ((0.605 : ℝ)) ≤ 1.53 := hCap
  have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((0.605 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hRe_lo : (-0.0765 : ℝ)
      ≤ (((((2 : ℝ)) : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)).re) := by
    rw [hReEq]
    have h1 : (-0.05 : ℝ) * (2 : ℝ) ^ ((0.605 : ℝ))
        ≤ (2 : ℝ) ^ ((0.605 : ℝ)) * Real.cos (6.75 * Real.log 2) := by
      have h := mul_le_mul_of_nonneg_left hCos hr0
      linarith [h]
    have hmul : (-0.05 : ℝ) * 1.53 = -0.0765 := by norm_num
    have h2 : (-0.0765 : ℝ) ≤ (-0.05 : ℝ) * (2 : ℝ) ^ ((0.605 : ℝ)) := by
      linarith
    linarith
  have hS_eq : ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter))
      = ((1 : ℂ) - ((((2 : ℝ)) : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter))) := by
    rw [hcast]
  rw [hS_eq]
  have hsq_eq : ‖((1 : ℂ) - ((((2 : ℝ)) : ℂ)
      ^ ((1 : ℂ) - R02Pilot.sCenter)))‖ ^ 2
      = 1 - 2 * (((((2 : ℝ)) : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)).re)
        + ‖((((2 : ℝ)) : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter))‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im]
    ring
  have hr2 : ((2 : ℝ) ^ ((0.605 : ℝ))) ^ 2 ≤ (1.53 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hr0 hrHi 2
  have hsq_le : ‖((1 : ℂ) - ((((2 : ℝ)) : ℂ)
      ^ ((1 : ℂ) - R02Pilot.sCenter)))‖ ^ 2 ≤ (1.87 : ℝ) ^ 2 := by
    have hnum : (1 : ℝ) - 2 * (-0.0765) + (1.53 : ℝ) ^ 2 ≤ (1.87 : ℝ) ^ 2 := by
      norm_num
    rw [hsq_eq, hnormR]
    linarith
  calc ‖((1 : ℂ) - ((((2 : ℝ)) : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)))‖
      = Real.sqrt (‖((1 : ℂ) - ((((2 : ℝ)) : ℂ)
        ^ ((1 : ℂ) - R02Pilot.sCenter)))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((1.87 : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq_le
    _ = 1.87 := Real.sqrt_sq (by norm_num)

/-- UNCONDITIONAL sharpened factor cap (both links closed above). -/
theorem CS_etaFactor_187_proved : CS_etaFactor_upper_187 :=
  CS_etaFactor_187_of_bounds CS_rpow0605_proved CS_cos675_lower_neg005

/-- Factor-need numeral at the sharpened cap: `1.4·1.87 = 2.618`. -/
theorem CS_factor_need_187 : (1.4 : ℝ) * 1.87 = 2.618 := by
  norm_num

/-- S2c feed into the zeta assembly (exact instantiation shape, mirror of
`CS_zeta_of_S2b`): with sharpened `slow = 1.25`, `tail = 0`,
`cF = 1.87`, `CS_zeta_of_parts` applies directly — `hNeed` is still the
unclosable `2.618 ≤ 1.25` (see `CS_S2c_shortfall_187`). -/
theorem CS_zeta_of_S2c (Z : ℝ)
    (hLink : (1.25 : ℝ) - 0 ≤ 1.87 * Z) (hNeed : (1.4 : ℝ) * 1.87 + 0 ≤ 1.25) :
    1.4 ≤ Z :=
  CS_zeta_of_parts 1.25 0 1.87 Z (by norm_num) hLink hNeed

/-- Exact new shortfall numeral (honest floor report): the `1.4` need at
`cF = 1.87` exceeds sharpened `slow = 1.25` by `1.368` (was `2.292`;
gain `0.924`). -/
theorem CS_S2c_shortfall_187 : (1.4 : ℝ) * 1.87 - 1.25 = 1.368 := by
  norm_num

#print axioms CS_cos675_lower_neg005
#print axioms CS_cpow_factor_re
#print axioms CS_cpow_factor_norm_eq
#print axioms CS_etaFactor_187_proved
#print axioms CS_S2c_shortfall_187

/-! ## §A4. Slow growth S6 (real-σ `0.26 → 0.25`, honest weak step)

Route (mirrors §A2 `CS_rpow3pos_proved` / `CS_rpow4pos_proved` only):
* `log 5` via `Real.log_five_gt_d9` / `lt_d9` (same recipe as
  `door3_dp_headA`: `1.6094 ≤ log 5 ≤ 1.6095`).
* `log 6 = log 2 + log 3` composite bridge (`Real.log_mul`), so
  `1.74604 ≤ log 6 ≤ 1.8295` from the banked `CS_log2` / `CS_log_three`.
* `5^0.395 ≤ 1.90` via `Real.exp_bound'` n=4 at
  `x = 0.395·log 5 ≤ 0.63576` (true `≈ 1.8884`, margin `0.0116`).
* `5^-0.395 ≥ 0.52` from `0.52·1.90 = 0.988 ≤ 1` (true `≈ 0.5295`).
* `6^0.395 ≥ 1.92` via quadratic lower at
  `x = 0.395·log 6 ≥ 0.68968` (true `≈ 2.0294`; quad at the floor
  is `≈ 1.9275`, margin `0.0075`).
* `6^-0.395 ≤ 0.53` from `0.53·1.92 = 1.0176 ≥ 1` (true `≈ 0.4927`).
* Alternating-sum lower `S6 = S4 + r5 - r6 ≥ 0.26 + 0.52 - 0.53 = 0.25`.
  True S6 real `≈ 0.3459`, so `0.25` is safe but WEAKER than S4 `0.26`
  (the `r5 - r6` window `≈ 0.0368` is eaten by the loose `0.53` cap).
  Honest report: no slow gain; the `1.4` floor still fails — see
  `CS_S6_shortfall_187` (`2.368` vs `1.368`). The cF shave below
  (`§A5`) is the fallback per ETA-NEXT3. -/

/-- `log 5` lower (`1.6094 ≤ log 5`, mirrors `dp_headA_log5_lo`). -/
theorem CS_log_five_ge : (16094 / 10000 : ℝ) ≤ Real.log 5 := by
  have h := Real.log_five_gt_d9
  norm_num at h ⊢
  linarith

/-- `log 5` upper (`log 5 ≤ 1.6095`, mirrors `dp_headA_log5_hi`). -/
theorem CS_log_five_le : Real.log 5 ≤ (16095 / 10000 : ℝ) := by
  have h := Real.log_five_lt_d9
  norm_num at h ⊢
  linarith

/-- `log 6 = log 2 + log 3` composite bridge (`Real.log_mul`). -/
theorem CS_log_six_eq : Real.log 6 = Real.log 2 + Real.log 3 := by
  have h6 : (6 : ℝ) = 2 * 3 := by norm_num
  rw [h6, Real.log_mul (by norm_num) (by norm_num)]

/-- `log 6` lower (`1.74604 ≤ log 6` from banked `log2` / `log3` lowers). -/
theorem CS_log_six_ge : (1.74604 : ℝ) ≤ Real.log 6 := by
  rw [CS_log_six_eq]
  have h2 := CS_log2_ge
  have h3 := CS_log_three_ge
  linarith

/-- `log 6` upper (`log 6 ≤ 1.8295` from banked uppers). -/
theorem CS_log_six_le : Real.log 6 ≤ (1.8295 : ℝ) := by
  rw [CS_log_six_eq]
  have h2 := CS_log2_le
  have h3 := CS_log_three_le
  linarith

/-- `5^0.395 ≤ 1.90` upper input (TRUE `≈ 1.8884`). -/
def CS_rpow5pos_upper : Prop := (5 : ℝ) ^ ((0.395 : ℝ)) ≤ 1.90

/-- CLOSED: `5^0.395 ≤ 1.90` via `exp_bound'` n=4 at
`x = 0.395·log 5 ≤ 0.63576` (uses `CS_log_five_le`). -/
theorem CS_rpow5pos_proved : CS_rpow5pos_upper := by
  show (5 : ℝ) ^ ((0.395 : ℝ)) ≤ 1.90
  have hlog : Real.log 5 ≤ (16095 / 10000 : ℝ) := CS_log_five_le
  have hlog_pos : (0 : ℝ) < Real.log 5 := Real.log_pos (by norm_num : (1 : ℝ) < 5)
  set x : ℝ := 0.395 * Real.log 5 with hx_def
  have hx0 : (0 : ℝ) ≤ x := by
    rw [hx_def]
    exact mul_nonneg (by norm_num) (le_of_lt hlog_pos)
  have hx_hi : x ≤ (0.63576 : ℝ) := by
    rw [hx_def]
    have hmul : 0.395 * Real.log 5 ≤ 0.395 * (16095 / 10000) := by
      apply mul_le_mul_of_nonneg_left hlog (by norm_num)
    have hcap : (0.395 : ℝ) * (16095 / 10000) ≤ (0.63576 : ℝ) := by
      norm_num
    linarith
  have hx1 : x ≤ 1 := by linarith
  have hrpow : (5 : ℝ) ^ ((0.395 : ℝ)) = Real.exp x := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5)]
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
  have q2 : x ^ 2 ≤ (0.63576 : ℝ) ^ 2 := pow_le_pow_left₀ hx0 hx_hi 2
  have q3 : x ^ 3 ≤ (0.63576 : ℝ) ^ 3 := pow_le_pow_left₀ hx0 hx_hi 3
  have q4 : x ^ 4 ≤ (0.63576 : ℝ) ^ 4 := pow_le_pow_left₀ hx0 hx_hi 4
  have hnum : (1 : ℝ) + 0.63576 + (0.63576 : ℝ) ^ 2 / 2 +
      (0.63576 : ℝ) ^ 3 / 6 + (0.63576 : ℝ) ^ 4 * 5 / (24 * 4) ≤ 1.90 := by
    norm_num
  rw [hrpow]
  linarith

/-- `5^-0.395 ≥ 0.52` lower input (TRUE `≈ 0.5295`). -/
def CS_rpow5neg_lower : Prop := (0.52 : ℝ) ≤ (5 : ℝ) ^ (-(0.395 : ℝ))

/-- CLOSED: `5^-0.395 ≥ 0.52` from `5^0.395 ≤ 1.90`
(`0.52·1.90 = 0.988 ≤ 1`). -/
theorem CS_rpow5neg_lower_proved : CS_rpow5neg_lower := by
  show (0.52 : ℝ) ≤ (5 : ℝ) ^ (-(0.395 : ℝ))
  have hup : (5 : ℝ) ^ ((0.395 : ℝ)) ≤ 1.90 := CS_rpow5pos_proved
  have hpos : (0 : ℝ) < (5 : ℝ) ^ ((0.395 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hInv : (5 : ℝ) ^ (-(0.395 : ℝ)) = 1 / (5 : ℝ) ^ ((0.395 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 5)]
    rw [inv_eq_one_div]
  have hle : (0.52 : ℝ) * (5 : ℝ) ^ ((0.395 : ℝ)) ≤ 1 := by
    have hmul : (0.52 : ℝ) * 1.90 ≤ 1 := by norm_num
    calc (0.52 : ℝ) * (5 : ℝ) ^ ((0.395 : ℝ))
        ≤ 0.52 * 1.90 := mul_le_mul_of_nonneg_left hup (by norm_num)
      _ ≤ 1 := hmul
  rw [hInv, le_div_iff₀ hpos]
  exact hle

/-- `6^0.395 ≥ 1.92` lower input (TRUE `≈ 2.0294`). -/
def CS_rpow6pos_lower : Prop := (1.92 : ℝ) ≤ (6 : ℝ) ^ ((0.395 : ℝ))

/-- CLOSED: `6^0.395 ≥ 1.92` via quadratic lower at
`x = 0.395·log 6 ≥ 0.68968` (`log 6 = log 2 + log 3` + `CS_log_six_ge`). -/
theorem CS_rpow6pos_proved : CS_rpow6pos_lower := by
  show (1.92 : ℝ) ≤ (6 : ℝ) ^ ((0.395 : ℝ))
  have h6 : (1.74604 : ℝ) ≤ Real.log 6 := CS_log_six_ge
  have hx_lo : (0.68968 : ℝ) < 0.395 * Real.log 6 := by
    have hmul : (0.395 : ℝ) * 1.74604 ≤ 0.395 * Real.log 6 :=
      mul_le_mul_of_nonneg_left h6 (by norm_num)
    have hcap : (0.68968 : ℝ) < 0.395 * 1.74604 := by norm_num
    linarith
  set x : ℝ := 0.395 * Real.log 6 with hx_def
  have hx0 : (0 : ℝ) ≤ x := le_trans (by norm_num) hx_lo.le
  have hsq : (0.68968 : ℝ) ^ 2 ≤ x ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hx_lo.le 2
  have hquad := Real.quadratic_le_exp_of_nonneg hx0
  have hbase : (1.92 : ℝ) ≤ 1 + 0.68968 + (0.68968 : ℝ) ^ 2 / 2 := by
    norm_num
  have hchain : (1.92 : ℝ) ≤ Real.exp x := by
    linarith [hquad, hsq, hx_lo, hbase]
  have hrpow : (6 : ℝ) ^ ((0.395 : ℝ)) = Real.exp x := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 6)]
    congr 1
    rw [hx_def]
    ring
  rw [hrpow]
  exact hchain

/-- `6^-0.395 ≤ 0.53` upper input (TRUE `≈ 0.4927`). -/
def CS_rpow6neg_upper : Prop := (6 : ℝ) ^ (-(0.395 : ℝ)) ≤ (0.53 : ℝ)

/-- CLOSED: `6^-0.395 ≤ 0.53` from `6^0.395 ≥ 1.92`
(`0.53·1.92 = 1.0176 ≥ 1`). -/
theorem CS_rpow6neg_upper_proved : CS_rpow6neg_upper := by
  show (6 : ℝ) ^ (-(0.395 : ℝ)) ≤ (0.53 : ℝ)
  have hlow : (1.92 : ℝ) ≤ (6 : ℝ) ^ ((0.395 : ℝ)) := CS_rpow6pos_proved
  have hpos : (0 : ℝ) < (6 : ℝ) ^ ((0.395 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hInv : (6 : ℝ) ^ (-(0.395 : ℝ)) = 1 / (6 : ℝ) ^ ((0.395 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 6)]
    rw [inv_eq_one_div]
  have hle : (1 : ℝ) ≤ (0.53 : ℝ) * (6 : ℝ) ^ ((0.395 : ℝ)) := by
    have hmul : (1 : ℝ) ≤ 0.53 * 1.92 := by norm_num
    calc (1 : ℝ) ≤ 0.53 * 1.92 := hmul
      _ ≤ 0.53 * (6 : ℝ) ^ ((0.395 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlow (by norm_num)
  rw [hInv, div_le_iff₀ hpos]
  linarith [hle]

/-- Real-σ S6 lower, conditional form: `1 - r2 + r3 - r4 + r5 - r6 ≥ 0.25`
(TRUE `≈ 0.3459`). Mirrors `CS_etaS4_ge_026`. -/
theorem CS_etaS6_ge_025 (h2 : CS_rpow2_head_upper)
    (h3 : CS_rpow3neg_lower) (h4 : CS_rpow4neg_upper)
    (h5 : CS_rpow5neg_lower) (h6 : CS_rpow6neg_upper) :
    (0.25 : ℝ) ≤ 1 - (2 : ℝ) ^ (-(0.395 : ℝ))
      + (3 : ℝ) ^ (-(0.395 : ℝ)) - (4 : ℝ) ^ (-(0.395 : ℝ))
      + (5 : ℝ) ^ (-(0.395 : ℝ)) - (6 : ℝ) ^ (-(0.395 : ℝ)) := by
  have h2u : (2 : ℝ) ^ (-(0.395 : ℝ)) ≤ 0.77 := h2
  have h3l : (0.63 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ)) := h3
  have h4u : (4 : ℝ) ^ (-(0.395 : ℝ)) ≤ 0.60 := h4
  have h5l : (0.52 : ℝ) ≤ (5 : ℝ) ^ (-(0.395 : ℝ)) := h5
  have h6u : (6 : ℝ) ^ (-(0.395 : ℝ)) ≤ 0.53 := h6
  linarith

/-- UNCONDITIONAL real-σ S6 floor `0.25` (all five premises closed;
WEAKER than S4 `0.26` — honest weak step, see header). -/
theorem CS_etaS6_uncond :
    (0.25 : ℝ) ≤ 1 - (2 : ℝ) ^ (-(0.395 : ℝ))
      + (3 : ℝ) ^ (-(0.395 : ℝ)) - (4 : ℝ) ^ (-(0.395 : ℝ))
      + (5 : ℝ) ^ (-(0.395 : ℝ)) - (6 : ℝ) ^ (-(0.395 : ℝ)) :=
  CS_etaS6_ge_025 CS_rpow2_proved CS_rpow3neg_lower_proved CS_rpow4neg_upper_proved
    CS_rpow5neg_lower_proved CS_rpow6neg_upper_proved

/-- S6-real feed into the zeta assembly (exact instantiation shape, mirror of
`CS_zeta_of_S2c`): with real `slow = 0.25`, `tail = 0`, `cF = 1.87`,
`CS_zeta_of_parts` applies directly — `hNeed` is the unclosable
`2.618 ≤ 0.25` (see `CS_S6_shortfall_187`); documents that real-S6 does
NOT replace the complex `slow = 1.25`. -/
theorem CS_zeta_of_S6 (Z : ℝ)
    (hLink : (0.25 : ℝ) - 0 ≤ 1.87 * Z) (hNeed : (1.4 : ℝ) * 1.87 + 0 ≤ 0.25) :
    1.4 ≤ Z :=
  CS_zeta_of_parts 0.25 0 1.87 Z (by norm_num) hLink hNeed

/-- Exact new shortfall numeral (honest floor report): the `1.4` need at
`cF = 1.87` exceeds real `slow = 0.25` by `2.368` (vs S2c `1.368`;
regression `1.0` — real S6 is NOT a complex-slow substitute). -/
theorem CS_S6_shortfall_187 : (1.4 : ℝ) * 1.87 - 0.25 = 2.368 := by
  norm_num

/-! ## §A5. Cosine tightening `-0.05 → -0.04` + `2^0.605 ≤ 1.525` = cF shave

Fallback per ETA-NEXT3 (S6 went weak above): the head phase sits
`≈ 0.0336` below `3π/2` (true `cos ≈ -0.0338`), so `-0.04` carries
`≈ 18%` margin and is provable with the SAME coarse `π` + phase bounds
(`|d| ≤ 0.04` needs only `±0.04`, true `|d| ≈ 0.0336`).
With `r = 2^0.605 ≤ 1.525` (tightened from `1.53`; `exp_bound'` at
`0.41936` gives `≈ 1.5212`, margin `0.0038`) and `Re w ≥ -0.04·r ≥ -0.061`,
`‖1-w‖² ≤ 1 + 0.122 + 1.525² = 3.447625 ≤ 1.86² = 3.4596`.
True `cF ≈ 1.85`, so `1.86` carries `≈ 0.5%` margin.
New need `1.4·1.86 = 2.604`; shortfall vs `slow = 1.25` is `1.354`
(was `1.368`; shave `0.014`). The `1.4` floor still fails
(`2.604 ≤ 1.25` false); patch must still grow complex `slow`. -/

/-- Cosine lower at the head phase (`≥ -0.04`; true `≈ -0.0338`). -/
theorem CS_cos675_lower_neg004 :
    (-0.04 : ℝ) ≤ Real.cos (6.75 * Real.log 2) := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have hphase_hi := CS_eta_phase1_lt
  have hlo : (4.6787 : ℝ) ≤ 6.75 * Real.log 2 := by
    have h2 := CS_log2_ge
    have hmul : 6.75 * (0.693147 : ℝ) ≤ 6.75 * Real.log 2 :=
      mul_le_mul_of_nonneg_left h2.le (by norm_num)
    have hcap : (4.6787 : ℝ) ≤ 6.75 * 0.693147 := by
      norm_num
    linarith
  set x : ℝ := 6.75 * Real.log 2 with hx_def
  set d : ℝ := x - 3 * Real.pi / 2 with hd_def
  have hd_lo : (-0.04 : ℝ) ≤ d := by
    rw [hd_def]
    linarith
  have hd_hi : d ≤ (0.04 : ℝ) := by
    rw [hd_def]
    linarith
  have h32eq : (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 := by
    ring
  have hcos32 : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [h32eq, Real.cos_add, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hsin32 : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [h32eq, Real.sin_add, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hx_eq : x = 3 * Real.pi / 2 + d := by
    rw [hd_def]
    ring
  have hcos_eq : Real.cos x = Real.sin d := by
    rw [hx_eq, Real.cos_add, hcos32, hsin32]
    ring
  have hsin_lb : (-0.04 : ℝ) ≤ Real.sin d := by
    by_cases hd0 : (0 : ℝ) ≤ d
    · have hd_pi : d ≤ Real.pi := by linarith
      have hnn : (0 : ℝ) ≤ Real.sin d :=
        Real.sin_nonneg_of_nonneg_of_le_pi hd0 hd_pi
      linarith
    · push_neg at hd0
      have he_pos : (0 : ℝ) < -d := by linarith
      have hle : Real.sin (-d) ≤ -d := Real.sin_le he_pos.le
      have hneg : Real.sin d = -Real.sin (-d) := by
        have h := Real.sin_neg (x := -d)
        rw [neg_neg] at h
        exact h
      linarith
  rw [hcos_eq]
  exact hsin_lb

/-- Tightened `2^0.605 ≤ 1.525` cap input (TRUE `≈ 1.5212`). -/
def CS_rpow0605_tight : Prop := (2 : ℝ) ^ ((0.605 : ℝ)) ≤ 1.525

/-- CLOSED: the tightened `2^0.605` cap (same `exp_bound'` n=4 route at
`0.41936`; numeral `≈ 1.5212 ≤ 1.525`). -/
theorem CS_rpow0605_tight_proved : CS_rpow0605_tight := by
  show (2 : ℝ) ^ ((0.605 : ℝ)) ≤ 1.525
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
      (0.41936 : ℝ) ^ 3 / 6 + (0.41936 : ℝ) ^ 4 * 5 / (24 * 4) ≤ 1.525 := by
    norm_num
  linarith

/-- Sharpened eta-factor cap `≤ 1.86` (TRUE `≈ 1.85`). -/
def CS_etaFactor_upper_186 : Prop :=
  ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)‖ ≤ 1.86

/-- Phase-aware factor upper from the tightened `2^0.605` cap + the `-0.04`
cosine floor (PROVED): `Re w ≥ -0.061`, `‖w‖ ≤ 1.525`, so
`‖1-w‖² ≤ 3.447625 ≤ 1.86²`. -/
theorem CS_etaFactor_186_of_bounds (hCap : CS_rpow0605_tight)
    (hCos : (-0.04 : ℝ) ≤ Real.cos (6.75 * Real.log 2)) :
    CS_etaFactor_upper_186 := by
  show ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)‖ ≤ 1.86
  have hReEq := CS_cpow_factor_re
  have hnormR := CS_cpow_factor_norm_eq
  have hcast : ((2 : ℂ)) = ((((2 : ℝ)) : ℂ)) := by simp
  have hrHi : (2 : ℝ) ^ ((0.605 : ℝ)) ≤ 1.525 := hCap
  have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((0.605 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hRe_lo : (-0.061 : ℝ)
      ≤ (((((2 : ℝ)) : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)).re) := by
    rw [hReEq]
    have h1 : (-0.04 : ℝ) * (2 : ℝ) ^ ((0.605 : ℝ))
        ≤ (2 : ℝ) ^ ((0.605 : ℝ)) * Real.cos (6.75 * Real.log 2) := by
      have h := mul_le_mul_of_nonneg_left hCos hr0
      linarith [h]
    have hmul : (-0.04 : ℝ) * 1.525 = -0.061 := by norm_num
    have h2 : (-0.061 : ℝ) ≤ (-0.04 : ℝ) * (2 : ℝ) ^ ((0.605 : ℝ)) := by
      linarith
    linarith
  have hS_eq : ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter))
      = ((1 : ℂ) - ((((2 : ℝ)) : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter))) := by
    rw [hcast]
  rw [hS_eq]
  have hsq_eq : ‖((1 : ℂ) - ((((2 : ℝ)) : ℂ)
      ^ ((1 : ℂ) - R02Pilot.sCenter)))‖ ^ 2
      = 1 - 2 * (((((2 : ℝ)) : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)).re)
        + ‖((((2 : ℝ)) : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter))‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im]
    ring
  have hr2 : ((2 : ℝ) ^ ((0.605 : ℝ))) ^ 2 ≤ (1.525 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hr0 hrHi 2
  have hsq_le : ‖((1 : ℂ) - ((((2 : ℝ)) : ℂ)
      ^ ((1 : ℂ) - R02Pilot.sCenter)))‖ ^ 2 ≤ (1.86 : ℝ) ^ 2 := by
    have hnum : (1 : ℝ) - 2 * (-0.061) + (1.525 : ℝ) ^ 2 ≤ (1.86 : ℝ) ^ 2 := by
      norm_num
    rw [hsq_eq, hnormR]
    linarith
  calc ‖((1 : ℂ) - ((((2 : ℝ)) : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)))‖
      = Real.sqrt (‖((1 : ℂ) - ((((2 : ℝ)) : ℂ)
        ^ ((1 : ℂ) - R02Pilot.sCenter)))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((1.86 : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq_le
    _ = 1.86 := Real.sqrt_sq (by norm_num)

/-- UNCONDITIONAL `1.86` factor cap (both links closed above). -/
theorem CS_etaFactor_186_proved : CS_etaFactor_upper_186 :=
  CS_etaFactor_186_of_bounds CS_rpow0605_tight_proved CS_cos675_lower_neg004

/-- Factor-need numeral at the shaved cap: `1.4·1.86 = 2.604`. -/
theorem CS_factor_need_186 : (1.4 : ℝ) * 1.86 = 2.604 := by
  norm_num

/-- S2d feed into the zeta assembly (exact instantiation shape, mirror of
`CS_zeta_of_S2c`): with `slow = 1.25`, `tail = 0`, `cF = 1.86`,
`CS_zeta_of_parts` applies directly — `hNeed` is still the unclosable
`2.604 ≤ 1.25` (see `CS_S2d_shortfall_186`). -/
theorem CS_zeta_of_S2d (Z : ℝ)
    (hLink : (1.25 : ℝ) - 0 ≤ 1.86 * Z) (hNeed : (1.4 : ℝ) * 1.86 + 0 ≤ 1.25) :
    1.4 ≤ Z :=
  CS_zeta_of_parts 1.25 0 1.86 Z (by norm_num) hLink hNeed

/-- Exact new shortfall numeral (honest floor report): the `1.4` need at
`cF = 1.86` exceeds `slow = 1.25` by `1.354` (was `1.368`; shave `0.014`). -/
theorem CS_S2d_shortfall_186 : (1.4 : ℝ) * 1.86 - 1.25 = 1.354 := by
  norm_num

/-! ## §A6. Cosine tightening `-0.04 → -0.035` = cF shave `1.86 → 1.853`

Picked (b) per ETA-NEXT4 (proved numerals only): the `-0.04` route replays
with `|d| ≤ 0.04` but only the LOWER `d ≥ -0.035` is needed (`sin d ≥ d`
for `d < 0`, `sin d ≥ 0` for `d ≥ 0`). True `d ≈ -0.03364`, so `-0.035`
carries `≈ 4%` margin and is provable with the SAME coarse `π` + phase
bounds (`4.6787 ≤ x`, `π` via `pi_gt/lt_d6` only). Reuses banked
`r = 2^0.605 ≤ 1.525` (no new rpow numeral), so
`Re w ≥ -0.035·r ≥ -0.053375` and
`‖1-w‖² ≤ 1 + 0.10675 + 1.525² = 3.432375 ≤ 1.853² = 3.433609`.
True `cF ≈ 1.8482`, so `1.853` carries `≈ 0.26%` margin.
New need `1.4·1.853 = 2.5942`; shortfall vs `slow = 1.25` is `1.3442`
(was `1.354`; shave `0.0098`). The `1.4` floor still fails
(`2.5942 ≤ 1.25` false); patch must still grow complex `slow`.
Option (a) (complex S4) NOT taken: `φ₃ = 6.75·log 3` interval from banked
`log3` bounds is `≈ 0.56` wide, so no proved positive `cos φ₃` lower is
available without a new `log3` sharpening (out of scope for this lane). -/

/-- Cosine lower at the head phase (`≥ -0.035`; true `≈ -0.0336`). -/
theorem CS_cos675_lower_neg0035 :
    (-0.035 : ℝ) ≤ Real.cos (6.75 * Real.log 2) := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have hphase_hi := CS_eta_phase1_lt
  have hlo : (4.6787 : ℝ) ≤ 6.75 * Real.log 2 := by
    have h2 := CS_log2_ge
    have hmul : 6.75 * (0.693147 : ℝ) ≤ 6.75 * Real.log 2 :=
      mul_le_mul_of_nonneg_left h2.le (by norm_num)
    have hcap : (4.6787 : ℝ) ≤ 6.75 * 0.693147 := by
      norm_num
    linarith
  set x : ℝ := 6.75 * Real.log 2 with hx_def
  set d : ℝ := x - 3 * Real.pi / 2 with hd_def
  have hd_lo : (-0.035 : ℝ) ≤ d := by
    rw [hd_def]
    linarith
  have hd_hi : d ≤ (0.04 : ℝ) := by
    rw [hd_def]
    linarith
  have h32eq : (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 := by
    ring
  have hcos32 : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [h32eq, Real.cos_add, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hsin32 : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [h32eq, Real.sin_add, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hx_eq : x = 3 * Real.pi / 2 + d := by
    rw [hd_def]
    ring
  have hcos_eq : Real.cos x = Real.sin d := by
    rw [hx_eq, Real.cos_add, hcos32, hsin32]
    ring
  have hsin_lb : (-0.035 : ℝ) ≤ Real.sin d := by
    by_cases hd0 : (0 : ℝ) ≤ d
    · have hd_pi : d ≤ Real.pi := by linarith
      have hnn : (0 : ℝ) ≤ Real.sin d :=
        Real.sin_nonneg_of_nonneg_of_le_pi hd0 hd_pi
      linarith
    · push_neg at hd0
      have he_pos : (0 : ℝ) < -d := by linarith
      have hle : Real.sin (-d) ≤ -d := Real.sin_le he_pos.le
      have hneg : Real.sin d = -Real.sin (-d) := by
        have h := Real.sin_neg (x := -d)
        rw [neg_neg] at h
        exact h
      linarith
  rw [hcos_eq]
  exact hsin_lb

/-- Sharpened eta-factor cap `≤ 1.853` (TRUE `≈ 1.8482`). -/
def CS_etaFactor_upper_1853 : Prop :=
  ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)‖ ≤ 1.853

/-- Phase-aware factor upper from banked `2^0.605 ≤ 1.525` + the `-0.035`
cosine floor (PROVED): `Re w ≥ -0.053375`, `‖w‖ ≤ 1.525`, so
`‖1-w‖² ≤ 3.432375 ≤ 1.853²`. -/
theorem CS_etaFactor_1853_of_bounds (hCap : CS_rpow0605_tight)
    (hCos : (-0.035 : ℝ) ≤ Real.cos (6.75 * Real.log 2)) :
    CS_etaFactor_upper_1853 := by
  show ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)‖ ≤ 1.853
  have hReEq := CS_cpow_factor_re
  have hnormR := CS_cpow_factor_norm_eq
  have hcast : ((2 : ℂ)) = ((((2 : ℝ)) : ℂ)) := by simp
  have hrHi : (2 : ℝ) ^ ((0.605 : ℝ)) ≤ 1.525 := hCap
  have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((0.605 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hRe_lo : (-0.053375 : ℝ)
      ≤ (((((2 : ℝ)) : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)).re) := by
    rw [hReEq]
    have h1 : (-0.035 : ℝ) * (2 : ℝ) ^ ((0.605 : ℝ))
        ≤ (2 : ℝ) ^ ((0.605 : ℝ)) * Real.cos (6.75 * Real.log 2) := by
      have h := mul_le_mul_of_nonneg_left hCos hr0
      linarith [h]
    have hmul : (-0.035 : ℝ) * 1.525 = -0.053375 := by norm_num
    have h2 : (-0.053375 : ℝ) ≤ (-0.035 : ℝ) * (2 : ℝ) ^ ((0.605 : ℝ)) := by
      linarith
    linarith
  have hS_eq : ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter))
      = ((1 : ℂ) - ((((2 : ℝ)) : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter))) := by
    rw [hcast]
  rw [hS_eq]
  have hsq_eq : ‖((1 : ℂ) - ((((2 : ℝ)) : ℂ)
      ^ ((1 : ℂ) - R02Pilot.sCenter)))‖ ^ 2
      = 1 - 2 * (((((2 : ℝ)) : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)).re)
        + ‖((((2 : ℝ)) : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter))‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im]
    ring
  have hr2 : ((2 : ℝ) ^ ((0.605 : ℝ))) ^ 2 ≤ (1.525 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hr0 hrHi 2
  have hsq_le : ‖((1 : ℂ) - ((((2 : ℝ)) : ℂ)
      ^ ((1 : ℂ) - R02Pilot.sCenter)))‖ ^ 2 ≤ (1.853 : ℝ) ^ 2 := by
    have hnum : (1 : ℝ) - 2 * (-0.053375) + (1.525 : ℝ) ^ 2 ≤ (1.853 : ℝ) ^ 2 := by
      norm_num
    rw [hsq_eq, hnormR]
    linarith
  calc ‖((1 : ℂ) - ((((2 : ℝ)) : ℂ) ^ ((1 : ℂ) - R02Pilot.sCenter)))‖
      = Real.sqrt (‖((1 : ℂ) - ((((2 : ℝ)) : ℂ)
        ^ ((1 : ℂ) - R02Pilot.sCenter)))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((1.853 : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq_le
    _ = 1.853 := Real.sqrt_sq (by norm_num)

/-- UNCONDITIONAL `1.853` factor cap (both links closed above). -/
theorem CS_etaFactor_1853_proved : CS_etaFactor_upper_1853 :=
  CS_etaFactor_1853_of_bounds CS_rpow0605_tight_proved CS_cos675_lower_neg0035

/-- Factor-need numeral at the shaved cap: `1.4·1.853 = 2.5942`. -/
theorem CS_factor_need_1853 : (1.4 : ℝ) * 1.853 = 2.5942 := by
  norm_num

/-- S2e feed into the zeta assembly (exact instantiation shape, mirror of
`CS_zeta_of_S2d`): with `slow = 1.25`, `tail = 0`, `cF = 1.853`,
`CS_zeta_of_parts` applies directly — `hNeed` is still the unclosable
`2.5942 ≤ 1.25` (see `CS_S2e_shortfall_1853`). -/
theorem CS_zeta_of_S2e (Z : ℝ)
    (hLink : (1.25 : ℝ) - 0 ≤ 1.853 * Z) (hNeed : (1.4 : ℝ) * 1.853 + 0 ≤ 1.25) :
    1.4 ≤ Z :=
  CS_zeta_of_parts 1.25 0 1.853 Z (by norm_num) hLink hNeed

/-- Exact new shortfall numeral (honest floor report): the `1.4` need at
`cF = 1.853` exceeds `slow = 1.25` by `1.3442` (was `1.354`; shave `0.0098`). -/
theorem CS_S2e_shortfall_1853 : (1.4 : ℝ) * 1.853 - 1.25 = 1.3442 := by
  norm_num

#print axioms CS_cos675_lower_neg0035
#print axioms CS_etaFactor_1853_proved
#print axioms CS_S2e_shortfall_1853

/-! ## §A7. Complex S4 slow growth `1.25 → 1.56` (ETA-NEXT5)

Judgment on `CS_log_three_le` (coarse `≤ 1.1363`, `≥ 1.0529`, width
`≈ 0.56` rad at `6.75×`): a proved POSITIVE `cos φ₃` lower is out of
scope, but a NONNEG lower `cos φ₃ ≥ 0` IS available from the coarse
interval alone (`φ₃ ∈ [7.10707, 7.67003]`, so `e = φ₃ - 2π ∈
[0.82, 1.39] ⊂ [-π/2, π/2]`), giving `Re(w₃) ≥ 0` with no log3
sharpening. `φ₄ = 6.75·log 4 = 13.5·log 2` is EXACT via
`CS_log_four_eq` + 6-digit `log2` bounds (`φ₄ ∈ [9.35748, 9.35750]`),
so `δ = 3π - φ₄ ∈ [0, 0.068]` gives `cos φ₄ = -cos δ ≤ -0.99`
(`cos δ ≥ 1 - δ²/2 ≥ 0.99`). True `cos φ₄ ≈ -0.9977`, so `-0.99`
carries margin. New `4^0.395 ≤ 1.74` (`exp_bound'` n=4 at
`x ≤ 0.54759`; true `≈ 1.7292`, margin `≈ 0.01`) gives
`r₄ = 4^-0.395 ≥ 0.57` (`0.57·1.74 = 0.9918 ≤ 1`; true `≈ 0.5783`).
Then `Re(S₄) = 1 - Re₂ + Re₃ - Re₄ ≥ 1 - 0 + 0 + 0.5643 = 1.5643 ≥
1.56` (`Re₂ ≤ 0` via banked `CS_cos675_nonpos_proved`, `Re₃ ≥ 0`,
`Re₄ ≤ 0.57·(-0.99) = -0.5643`). True `Re(S₄) ≈ 1.878`,
`|S₄| ≈ 2.288`, so `1.56` is safe. `|S₄| ≥ Re(S₄)` mirrors the
`CS_complex_S2_abs_ge_one` triangle step (Pythagoras not needed since
`Re` already exceeds `1.25`). New need `1.4·1.853 = 2.5942`;
shortfall vs `slow = 1.56` is `1.0342` (was `1.3442`; gain `0.31`).
The `1.4` floor still fails (`2.5942 ≤ 1.56` false); patch must grow
further / sharpen `cF`/`tail`. Fallback (real-S4 tightening) NOT
needed — complex S4 banked. -/

/-- Cpow real-part split for `3^{-s}` at `sCenter` (mirror of
`CS_cpow2_sCenter_re`: `(-s).re = -0.395`, `(-s).im = 6.75`). -/
theorem CS_cpow3_sCenter_re : ((((3 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter)).re
    = (3 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 3) := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hxC : ((3 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h3pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((3 : ℝ) : ℂ) = (((Real.log 3 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h3pos)).symm
  rw [hlog]
  have hre_w : (-R02Pilot.sCenter).re = (-(0.395 : ℝ)) := by
    have e : (-R02Pilot.sCenter).re = -(R02Pilot.sCenter.re) := rfl
    rw [e, R02Pilot.sCenter_re]
  have him_w : (-R02Pilot.sCenter).im = (6.75 : ℝ) := by
    have e : (-R02Pilot.sCenter).im = -(R02Pilot.sCenter.im) := rfl
    rw [e, R02Pilot.sCenter_im]
    norm_num
  have hzre : ((((Real.log 3 : ℝ)) : ℂ)).re = Real.log 3 := Complex.ofReal_re _
  have hzim : ((((Real.log 3 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 3 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).re
      = Real.log 3 * (-(0.395 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 3 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).im
      = Real.log 3 * (6.75 : ℝ) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 3 * (-(0.395 : ℝ)))
      = (3 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_def_of_pos h3pos _).symm
  have hcos : Real.cos (Real.log 3 * (6.75 : ℝ))
      = Real.cos (6.75 * Real.log 3) := by
    rw [mul_comm]
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- Cpow real-part split for `4^{-s}` at `sCenter` (mirror of
`CS_cpow2_sCenter_re`). -/
theorem CS_cpow4_sCenter_re : ((((4 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter)).re
    = (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4) := by
  have h4pos : (0 : ℝ) < 4 := by norm_num
  have hxC : ((4 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h4pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((4 : ℝ) : ℂ) = (((Real.log 4 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h4pos)).symm
  rw [hlog]
  have hre_w : (-R02Pilot.sCenter).re = (-(0.395 : ℝ)) := by
    have e : (-R02Pilot.sCenter).re = -(R02Pilot.sCenter.re) := rfl
    rw [e, R02Pilot.sCenter_re]
  have him_w : (-R02Pilot.sCenter).im = (6.75 : ℝ) := by
    have e : (-R02Pilot.sCenter).im = -(R02Pilot.sCenter.im) := rfl
    rw [e, R02Pilot.sCenter_im]
    norm_num
  have hzre : ((((Real.log 4 : ℝ)) : ℂ)).re = Real.log 4 := Complex.ofReal_re _
  have hzim : ((((Real.log 4 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 4 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).re
      = Real.log 4 * (-(0.395 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 4 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).im
      = Real.log 4 * (6.75 : ℝ) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 4 * (-(0.395 : ℝ)))
      = (4 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_def_of_pos h4pos _).symm
  have hcos : Real.cos (Real.log 4 * (6.75 : ℝ))
      = Real.cos (6.75 * Real.log 4) := by
    rw [mul_comm]
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- `4^0.395 ≤ 1.74` upper input (TRUE `≈ 1.7292`). -/
def CS_rpow4pos_upper174 : Prop := (4 : ℝ) ^ ((0.395 : ℝ)) ≤ 1.74

/-- CLOSED: `4^0.395 ≤ 1.74` via `exp_bound'` n=4 at
`x = 0.395·log 4 = 0.79·log 2 ≤ 0.54759`. -/
theorem CS_rpow4pos_upper174_proved : CS_rpow4pos_upper174 := by
  show (4 : ℝ) ^ ((0.395 : ℝ)) ≤ 1.74
  have hlog : Real.log 2 < (0.693148 : ℝ) := CS_log2_le
  have hlog_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h4 : Real.log 4 = 2 * Real.log 2 := CS_log_four_eq
  have hlog4_pos : (0 : ℝ) < Real.log 4 := by
    rw [h4]
    linarith
  set x : ℝ := 0.395 * Real.log 4 with hx_def
  have hx0 : (0 : ℝ) ≤ x := by
    rw [hx_def]
    exact mul_nonneg (by norm_num) (le_of_lt hlog4_pos)
  have hx_hi : x ≤ (0.54759 : ℝ) := by
    rw [hx_def, h4]
    have hmul : 0.79 * Real.log 2 ≤ 0.79 * 0.693148 := by
      apply mul_le_mul_of_nonneg_left hlog.le (by norm_num)
    have hcap : (0.79 : ℝ) * 0.693148 ≤ (0.54759 : ℝ) := by
      norm_num
    have heq : 0.395 * (2 * Real.log 2) = 0.79 * Real.log 2 := by
      ring
    linarith
  have hx1 : x ≤ 1 := by linarith
  have hrpow : (4 : ℝ) ^ ((0.395 : ℝ)) = Real.exp x := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4)]
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
  have q2 : x ^ 2 ≤ (0.54759 : ℝ) ^ 2 := pow_le_pow_left₀ hx0 hx_hi 2
  have q3 : x ^ 3 ≤ (0.54759 : ℝ) ^ 3 := pow_le_pow_left₀ hx0 hx_hi 3
  have q4 : x ^ 4 ≤ (0.54759 : ℝ) ^ 4 := pow_le_pow_left₀ hx0 hx_hi 4
  have hnum : (1 : ℝ) + 0.54759 + (0.54759 : ℝ) ^ 2 / 2 +
      (0.54759 : ℝ) ^ 3 / 6 + (0.54759 : ℝ) ^ 4 * 5 / (24 * 4) ≤ 1.74 := by
    norm_num
  rw [hrpow]
  linarith

/-- `4^-0.395 ≥ 0.57` lower input (TRUE `≈ 0.5783`). -/
def CS_rpow4neg_lower057 : Prop := (0.57 : ℝ) ≤ (4 : ℝ) ^ (-(0.395 : ℝ))

/-- CLOSED: `4^-0.395 ≥ 0.57` from `4^0.395 ≤ 1.74`
(`0.57·1.74 = 0.9918 ≤ 1`). -/
theorem CS_rpow4neg_lower057_proved : CS_rpow4neg_lower057 := by
  show (0.57 : ℝ) ≤ (4 : ℝ) ^ (-(0.395 : ℝ))
  have hup : (4 : ℝ) ^ ((0.395 : ℝ)) ≤ 1.74 := CS_rpow4pos_upper174_proved
  have hpos : (0 : ℝ) < (4 : ℝ) ^ ((0.395 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hInv : (4 : ℝ) ^ (-(0.395 : ℝ)) = 1 / (4 : ℝ) ^ ((0.395 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    rw [inv_eq_one_div]
  have hle : (0.57 : ℝ) * (4 : ℝ) ^ ((0.395 : ℝ)) ≤ 1 := by
    have hmul : (0.57 : ℝ) * 1.74 ≤ 1 := by norm_num
    calc (0.57 : ℝ) * (4 : ℝ) ^ ((0.395 : ℝ))
        ≤ 0.57 * 1.74 := mul_le_mul_of_nonneg_left hup (by norm_num)
      _ ≤ 1 := hmul
  rw [hInv, le_div_iff₀ hpos]
  exact hle

/-- Cosine nonnegativity at `φ₃ = 6.75·log 3` (TRUE `≈ 0.4244 ≥ 0`).
Route: `φ₃ ∈ [7.10707, 7.67003]` from banked coarse `log3` bounds, so
`e = φ₃ - 2π ∈ [-π/2, π/2]` and `cos φ₃ = cos e ≥ 0` via
`Real.cos_add_two_pi` + `Real.cos_nonneg_of_neg_pi_div_two_le_of_le`. -/
theorem CS_cos3_nonneg :
    (0 : ℝ) ≤ Real.cos (6.75 * Real.log 3) := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have h3lo := CS_log_three_ge
  have h3hi := CS_log_three_le
  have hlo : (7.10707 : ℝ) ≤ 6.75 * Real.log 3 := by
    have hmul : 6.75 * (1.0529 : ℝ) ≤ 6.75 * Real.log 3 :=
      mul_le_mul_of_nonneg_left h3lo (by norm_num)
    have hcap : (7.10707 : ℝ) ≤ 6.75 * 1.0529 := by
      norm_num
    linarith
  have hhi : 6.75 * Real.log 3 ≤ (7.67003 : ℝ) := by
    have hmul : 6.75 * Real.log 3 ≤ 6.75 * 1.1363 :=
      mul_le_mul_of_nonneg_left h3hi (by norm_num)
    have hcap : (6.75 : ℝ) * 1.1363 ≤ 7.67003 := by
      norm_num
    linarith
  set x : ℝ := 6.75 * Real.log 3 with hx_def
  set e : ℝ := x - 2 * Real.pi with he_def
  have he_lo : -(Real.pi / 2) ≤ e := by
    rw [he_def]
    linarith
  have he_hi : e ≤ Real.pi / 2 := by
    rw [he_def]
    linarith
  have hx_eq : x = e + 2 * Real.pi := by
    rw [he_def]
    ring
  have hcos_eq : Real.cos x = Real.cos e := by
    rw [hx_eq, Real.cos_add_two_pi]
  rw [hcos_eq]
  exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le he_lo he_hi

/-- Cosine upper at `φ₄ = 6.75·log 4` (`≤ -0.99`; TRUE `≈ -0.9977`).
Route: `φ₄ ∈ [9.35748, 9.35750]` via `CS_log_four_eq` + 6-digit `log2`
bounds, so `δ = 3π - φ₄ ∈ [0, 0.068]`; `cos φ₄ = -cos δ` via
`(π - δ) + 2π` + `Real.cos_add_two_pi` / `Real.cos_pi_sub`, and
`cos δ ≥ 1 - δ²/2 ≥ 0.99` via
`Real.one_sub_sq_div_two_le_cos`. -/
theorem CS_cos4_upper_neg099 :
    Real.cos (6.75 * Real.log 4) ≤ (-0.99 : ℝ) := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have h4 : Real.log 4 = 2 * Real.log 2 := CS_log_four_eq
  have h2lo := CS_log2_ge
  have h2hi := CS_log2_le
  have hphi_lo : (9.35748 : ℝ) ≤ 6.75 * Real.log 4 := by
    rw [h4]
    have hmul : 13.5 * (0.693147 : ℝ) ≤ 13.5 * Real.log 2 :=
      mul_le_mul_of_nonneg_left h2lo.le (by norm_num)
    have hcap : (9.35748 : ℝ) ≤ 13.5 * 0.693147 := by
      norm_num
    have heq : 6.75 * (2 * Real.log 2) = 13.5 * Real.log 2 := by
      ring
    linarith
  have hphi_hi : 6.75 * Real.log 4 ≤ (9.35750 : ℝ) := by
    rw [h4]
    have hmul : 13.5 * Real.log 2 ≤ 13.5 * 0.693148 :=
      mul_le_mul_of_nonneg_left h2hi.le (by norm_num)
    have hcap : (13.5 : ℝ) * 0.693148 ≤ 9.35750 := by
      norm_num
    have heq : 6.75 * (2 * Real.log 2) = 13.5 * Real.log 2 := by
      ring
    linarith
  set x : ℝ := 6.75 * Real.log 4 with hx_def
  set d : ℝ := 3 * Real.pi - x with hd_def
  have hd_lo : (0 : ℝ) ≤ d := by
    rw [hd_def]
    linarith
  have hd_hi : d ≤ (0.068 : ℝ) := by
    rw [hd_def]
    linarith
  have hx_eq : x = (Real.pi - d) + 2 * Real.pi := by
    rw [hd_def]
    ring
  have hcos_eq : Real.cos x = -Real.cos d := by
    rw [hx_eq, Real.cos_add_two_pi, Real.cos_pi_sub]
  have hcosd_lo : (0.99 : ℝ) ≤ Real.cos d := by
    have hquad := Real.one_sub_sq_div_two_le_cos (x := d)
    have hsq : d ^ 2 ≤ (0.068 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hd_lo hd_hi 2
    have hnum : (0.99 : ℝ) ≤ 1 - (0.068 : ℝ) ^ 2 / 2 := by
      norm_num
    linarith
  rw [hcos_eq]
  linarith

/-- Complex S4 partial sum at `sCenter`
(`1 - 2^{-s} + 3^{-s} - 4^{-s}`). -/
noncomputable def CS_S4C : ℂ :=
  (1 : ℂ) - (2 : ℂ) ^ (-R02Pilot.sCenter)
    + (3 : ℂ) ^ (-R02Pilot.sCenter) - (4 : ℂ) ^ (-R02Pilot.sCenter)

/-- Real-part identity for the complex S4 (cast + `sub_re` / `add_re` /
`one_re` + the three per-term cpow splits). -/
theorem CS_S4C_Re_eq :
    (CS_S4C).re = 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 2)
      + (3 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 3)
      - (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4) := by
  unfold CS_S4C
  have h2 : ((2 : ℂ)) = ((((2 : ℝ)) : ℂ)) := by simp
  have h3 : ((3 : ℂ)) = ((((3 : ℝ)) : ℂ)) := by simp
  have h4c : ((4 : ℂ)) = ((((4 : ℝ)) : ℂ)) := by simp
  rw [h2, h3, h4c]
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re,
    CS_cpow2_sCenter_re, CS_cpow3_sCenter_re, CS_cpow4_sCenter_re]

/-- Complex-S4 real part `≥ 1.56` (PROVED, unconditional):
`Re₂ ≤ 0` (banked cos nonpos), `Re₃ ≥ 0` (new cos nonneg),
`Re₄ ≤ -0.5643` (`r₄ ≥ 0.57`, `cos φ₄ ≤ -0.99`), so
`Re(S₄) ≥ 1 + 0.5643 = 1.5643 ≥ 1.56`. -/
theorem CS_complex_S4_Re_ge_156 :
    (1.56 : ℝ) ≤ (CS_S4C).re := by
  have hEq := CS_S4C_Re_eq
  have hr2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr4lo : (0.57 : ℝ) ≤ (4 : ℝ) ^ (-(0.395 : ℝ)) :=
    CS_rpow4neg_lower057_proved
  have hc2 : Real.cos (6.75 * Real.log 2) ≤ 0 := CS_cos675_nonpos_proved
  have hc3 : (0 : ℝ) ≤ Real.cos (6.75 * Real.log 3) := CS_cos3_nonneg
  have hc4 : Real.cos (6.75 * Real.log 4) ≤ (-0.99 : ℝ) := CS_cos4_upper_neg099
  have hT2 : (2 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hr2 hc2
  have hT3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 3) :=
    mul_nonneg hr3 hc3
  have hRe4 : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4)
      ≤ (-0.5643 : ℝ) := by
    have hc4nn : Real.cos (6.75 * Real.log 4) ≤ 0 := by linarith
    have hdiff : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4)
        - 0.57 * Real.cos (6.75 * Real.log 4)
        = ((4 : ℝ) ^ (-(0.395 : ℝ)) - 0.57) * Real.cos (6.75 * Real.log 4) := by
      ring
    have hnn : (0 : ℝ) ≤ (4 : ℝ) ^ (-(0.395 : ℝ)) - 0.57 := by linarith
    have hle1 : ((4 : ℝ) ^ (-(0.395 : ℝ)) - 0.57) * Real.cos (6.75 * Real.log 4)
        ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hnn hc4nn
    have h1 : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4)
        ≤ 0.57 * Real.cos (6.75 * Real.log 4) := by linarith
    have h2b : (0.57 : ℝ) * Real.cos (6.75 * Real.log 4) ≤ 0.57 * (-0.99) :=
      mul_le_mul_of_nonneg_left hc4 (by norm_num)
    have hmul : (0.57 : ℝ) * (-0.99) = -0.5643 := by norm_num
    linarith
  rw [hEq]
  linarith

/-- Complex-S4 absolute value `≥ 1.56` (triangle `‖z‖ ≥ Re z`,
mirroring `CS_complex_S2_abs_ge_one`). -/
theorem CS_complex_S4_abs_ge_156 :
    (1.56 : ℝ) ≤ ‖CS_S4C‖ := by
  have hRe := CS_complex_S4_Re_ge_156
  have hle : (CS_S4C).re ≤ ‖CS_S4C‖ := by
    have h1 := Complex.abs_re_le_norm (CS_S4C)
    have h2 := le_abs_self ((CS_S4C).re)
    linarith
  linarith

/-- S4 feed into the zeta assembly (exact instantiation shape, mirror of
`CS_zeta_of_S2e`): with complex-S4 `slow = 1.56`, `tail = 0`,
`cF = 1.853`, `CS_zeta_of_parts` applies directly — `hNeed` is still
the unclosable `2.5942 ≤ 1.56` (see `CS_S4_shortfall_1853`). -/
theorem CS_zeta_of_S4 (Z : ℝ)
    (hLink : (1.56 : ℝ) - 0 ≤ 1.853 * Z) (hNeed : (1.4 : ℝ) * 1.853 + 0 ≤ 1.56) :
    1.4 ≤ Z :=
  CS_zeta_of_parts 1.56 0 1.853 Z (by norm_num) hLink hNeed

/-- Exact new shortfall numeral (honest floor report): the `1.4` need at
`cF = 1.853` exceeds complex-S4 `slow = 1.56` by `1.0342` (was `1.3442`;
gain `0.31`). -/
theorem CS_S4_shortfall_1853 : (1.4 : ℝ) * 1.853 - 1.56 = 1.0342 := by
  norm_num

#print axioms CS_cpow3_sCenter_re
#print axioms CS_cpow4_sCenter_re
#print axioms CS_rpow4pos_upper174_proved
#print axioms CS_rpow4neg_lower057_proved
#print axioms CS_cos3_nonneg
#print axioms CS_cos4_upper_neg099
#print axioms CS_complex_S4_Re_ge_156
#print axioms CS_complex_S4_abs_ge_156
#print axioms CS_S4_shortfall_1853

/-! ## §A8. Complex S6 slow `0.95` (ETA-NEXT6)

Honest extension of the §A7 S4 recipe to `S₆ = S₄ + 5^{-s} - 6^{-s}`.
True values: `Re(S₆) ≈ 1.366 < Re(S₄) ≈ 1.874` (the `+5` term is
`≈ -0.070` since `cos φ₅ ≈ -0.1315`, the `-6` term is `≈ -0.439`
since `cos φ₆ ≈ +0.891`), so no `Re`-only S6 lower can beat the S4
`1.56` — this S6 floor `0.95` REGRESSES vs S4 by design (honest
signed/trivial fallbacks below, NOT a growth claim on the numeral).
`|S₆| ≈ 1.70` still exceeds `1.56` via the `Im` channel, but the `Im`
lower is out of scope for this lane (would need `sin` floors); the
`abs` floor here is just `‖S₆‖ ≥ Re(S₆)` mirroring `CS_complex_S4_abs`.
New need `1.4·1.853 = 2.5942`; shortfall vs `slow = 0.95` is `1.6442`
(was `1.0342`; regression `0.61` — slow still binding, patch must grow
further / sharpen `cF` / `tail` / `Im` route).

Per-term routes (mirrors of §A7):
* `φ₅ = 6.75·log 5 ∈ [10.8634, 10.8642]` (TIGHT, from banked
  `CS_log_five_ge/le`): `y = φ₅ - 2π ∈ [π/2, 3π/2]` gives
  `cos φ₅ ≤ 0` (`CS_cos5_nonpos`); `d = φ₅ - 7π/2 ∈ [-0.14, 0]`
  gives `cos φ₅ = sin d ≥ d ≥ -0.14` (`CS_cos5_lower_neg014`).
  `r₅ = 5^-0.395 ≤ 0.55` from new `5^0.395 ≥ 1.83` (quadratic lower
  at `x ≥ 0.635`; true `≈ 1.888`; `0.55·1.83 = 1.0065 ≥ 1`).
  Hence `Re₅ = r₅·cos φ₅ ≥ 0.55·(-0.14) = -0.077` (signed lower;
  needs both `cos φ₅ ≤ 0` and `cos φ₅ ≥ -0.14`).
* `φ₆ = 6.75·log 6 ∈ [11.7857, 12.3492]` (WIDE `≈ 0.56`, from banked
  composite `CS_log_six_ge/le`): `e = φ₆ - 4π ∈ [-π/2, π/2]` gives
  `cos φ₆ ≥ 0` (`CS_cos6_nonneg`, mirror of `CS_cos3_nonneg` with two
  `cos_add_two_pi` steps). Upper is the TRIVIALLY-signed fallback
  `cos φ₆ ≤ 1` (`Real.cos_le_one`, documented here) since the wide
  window makes a proved `< 1` upper out of scope. With banked
  `r₆ = 6^-0.395 ≤ 0.53`, `Re₆ = r₆·cos φ₆ ≤ 0.53`, so
  `-Re₆ ≥ -0.53`.
Then `Re(S₆) = Re(S₄) + Re₅ - Re₆ ≥ 1.56 - 0.077 - 0.53 = 0.953 ≥
0.95`. -/

/-- Cpow real-part split for `5^{-s}` at `sCenter` (mirror of
`CS_cpow3_sCenter_re`: `(-s).re = -0.395`, `(-s).im = 6.75`). -/
theorem CS_cpow5_sCenter_re : ((((5 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter)).re
    = (5 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 5) := by
  have h5pos : (0 : ℝ) < 5 := by norm_num
  have hxC : ((5 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h5pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((5 : ℝ) : ℂ) = (((Real.log 5 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h5pos)).symm
  rw [hlog]
  have hre_w : (-R02Pilot.sCenter).re = (-(0.395 : ℝ)) := by
    have e : (-R02Pilot.sCenter).re = -(R02Pilot.sCenter.re) := rfl
    rw [e, R02Pilot.sCenter_re]
  have him_w : (-R02Pilot.sCenter).im = (6.75 : ℝ) := by
    have e : (-R02Pilot.sCenter).im = -(R02Pilot.sCenter.im) := rfl
    rw [e, R02Pilot.sCenter_im]
    norm_num
  have hzre : ((((Real.log 5 : ℝ)) : ℂ)).re = Real.log 5 := Complex.ofReal_re _
  have hzim : ((((Real.log 5 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 5 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).re
      = Real.log 5 * (-(0.395 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 5 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).im
      = Real.log 5 * (6.75 : ℝ) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 5 * (-(0.395 : ℝ)))
      = (5 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_def_of_pos h5pos _).symm
  have hcos : Real.cos (Real.log 5 * (6.75 : ℝ))
      = Real.cos (6.75 * Real.log 5) := by
    rw [mul_comm]
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- Cpow real-part split for `6^{-s}` at `sCenter` (mirror of
`CS_cpow4_sCenter_re`). -/
theorem CS_cpow6_sCenter_re : ((((6 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter)).re
    = (6 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 6) := by
  have h6pos : (0 : ℝ) < 6 := by norm_num
  have hxC : ((6 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h6pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((6 : ℝ) : ℂ) = (((Real.log 6 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h6pos)).symm
  rw [hlog]
  have hre_w : (-R02Pilot.sCenter).re = (-(0.395 : ℝ)) := by
    have e : (-R02Pilot.sCenter).re = -(R02Pilot.sCenter.re) := rfl
    rw [e, R02Pilot.sCenter_re]
  have him_w : (-R02Pilot.sCenter).im = (6.75 : ℝ) := by
    have e : (-R02Pilot.sCenter).im = -(R02Pilot.sCenter.im) := rfl
    rw [e, R02Pilot.sCenter_im]
    norm_num
  have hzre : ((((Real.log 6 : ℝ)) : ℂ)).re = Real.log 6 := Complex.ofReal_re _
  have hzim : ((((Real.log 6 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 6 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).re
      = Real.log 6 * (-(0.395 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 6 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).im
      = Real.log 6 * (6.75 : ℝ) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 6 * (-(0.395 : ℝ)))
      = (6 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_def_of_pos h6pos _).symm
  have hcos : Real.cos (Real.log 6 * (6.75 : ℝ))
      = Real.cos (6.75 * Real.log 6) := by
    rw [mul_comm]
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- `5^0.395 ≥ 1.83` lower input (TRUE `≈ 1.8884`). -/
def CS_rpow5pos_lower183 : Prop := (1.83 : ℝ) ≤ (5 : ℝ) ^ ((0.395 : ℝ))

/-- CLOSED: `5^0.395 ≥ 1.83` via quadratic lower at
`x = 0.395·log 5 ≥ 0.635` (uses `CS_log_five_ge`). -/
theorem CS_rpow5pos_lower183_proved : CS_rpow5pos_lower183 := by
  show (1.83 : ℝ) ≤ (5 : ℝ) ^ ((0.395 : ℝ))
  have h5 : (16094 / 10000 : ℝ) ≤ Real.log 5 := CS_log_five_ge
  have hx_lo : (0.635 : ℝ) < 0.395 * Real.log 5 := by
    have hmul : (0.395 : ℝ) * (16094 / 10000) ≤ 0.395 * Real.log 5 :=
      mul_le_mul_of_nonneg_left h5 (by norm_num)
    have hcap : (0.635 : ℝ) < 0.395 * (16094 / 10000) := by
      norm_num
    linarith
  set x : ℝ := 0.395 * Real.log 5 with hx_def
  have hx0 : (0 : ℝ) ≤ x := le_trans (by norm_num) hx_lo.le
  have hsq : (0.635 : ℝ) ^ 2 ≤ x ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hx_lo.le 2
  have hquad := Real.quadratic_le_exp_of_nonneg hx0
  have hbase : (1.83 : ℝ) ≤ 1 + 0.635 + (0.635 : ℝ) ^ 2 / 2 := by
    norm_num
  have hchain : (1.83 : ℝ) ≤ Real.exp x := by
    linarith [hquad, hsq, hx_lo, hbase]
  have hrpow : (5 : ℝ) ^ ((0.395 : ℝ)) = Real.exp x := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5)]
    congr 1
    rw [hx_def]
    ring
  rw [hrpow]
  exact hchain

/-- `5^-0.395 ≤ 0.55` upper input (TRUE `≈ 0.5295`). -/
def CS_rpow5neg_upper055 : Prop := (5 : ℝ) ^ (-(0.395 : ℝ)) ≤ (0.55 : ℝ)

/-- CLOSED: `5^-0.395 ≤ 0.55` from `5^0.395 ≥ 1.83`
(`0.55·1.83 = 1.0065 ≥ 1`). -/
theorem CS_rpow5neg_upper055_proved : CS_rpow5neg_upper055 := by
  show (5 : ℝ) ^ (-(0.395 : ℝ)) ≤ (0.55 : ℝ)
  have hlow : (1.83 : ℝ) ≤ (5 : ℝ) ^ ((0.395 : ℝ)) := CS_rpow5pos_lower183_proved
  have hpos : (0 : ℝ) < (5 : ℝ) ^ ((0.395 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hInv : (5 : ℝ) ^ (-(0.395 : ℝ)) = 1 / (5 : ℝ) ^ ((0.395 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 5)]
    rw [inv_eq_one_div]
  have hle : (1 : ℝ) ≤ (0.55 : ℝ) * (5 : ℝ) ^ ((0.395 : ℝ)) := by
    have hmul : (1 : ℝ) ≤ 0.55 * 1.83 := by norm_num
    calc (1 : ℝ) ≤ 0.55 * 1.83 := hmul
      _ ≤ 0.55 * (5 : ℝ) ^ ((0.395 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlow (by norm_num)
  rw [hInv, div_le_iff₀ hpos]
  linarith [hle]

/-- Cosine nonpositivity at `φ₅ = 6.75·log 5` (TRUE `≈ -0.1315 ≤ 0`).
Route: `φ₅ ∈ [10.8634, 10.8642]` from banked `log5` bounds, so
`y = φ₅ - 2π ∈ [π/2, π + π/2]` and `cos φ₅ = cos y ≤ 0`. -/
theorem CS_cos5_nonpos :
    Real.cos (6.75 * Real.log 5) ≤ 0 := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have h5lo := CS_log_five_ge
  have h5hi := CS_log_five_le
  have hlo : (10.8634 : ℝ) ≤ 6.75 * Real.log 5 := by
    have hmul : 6.75 * (16094 / 10000 : ℝ) ≤ 6.75 * Real.log 5 :=
      mul_le_mul_of_nonneg_left h5lo (by norm_num)
    have hcap : (10.8634 : ℝ) ≤ 6.75 * (16094 / 10000) := by
      norm_num
    linarith
  have hhi : 6.75 * Real.log 5 ≤ (10.8642 : ℝ) := by
    have hmul : 6.75 * Real.log 5 ≤ 6.75 * (16095 / 10000 : ℝ) :=
      mul_le_mul_of_nonneg_left h5hi (by norm_num)
    have hcap : (6.75 : ℝ) * (16095 / 10000) ≤ 10.8642 := by
      norm_num
    linarith
  set x : ℝ := 6.75 * Real.log 5 with hx_def
  set y : ℝ := x - 2 * Real.pi with hy_def
  have h1 : Real.pi / 2 ≤ y := by
    rw [hy_def]
    linarith
  have h2 : y ≤ Real.pi + Real.pi / 2 := by
    rw [hy_def]
    linarith
  have hx_eq : x = y + 2 * Real.pi := by
    rw [hy_def]
    ring
  have hcos_eq : Real.cos x = Real.cos y := by
    rw [hx_eq, Real.cos_add_two_pi]
  rw [hcos_eq]
  exact Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2

/-- Cosine lower at `φ₅ = 6.75·log 5` (`≥ -0.14`; TRUE `≈ -0.1315`).
Route: `d = φ₅ - 7π/2 ∈ [-0.14, 0]`, `cos φ₅ = sin d ≥ d ≥ -0.14`
(`sin d ≥ 0` for `d ≥ 0`, `sin d = -sin(-d) ≥ d` for `d < 0`). -/
theorem CS_cos5_lower_neg014 :
    (-0.14 : ℝ) ≤ Real.cos (6.75 * Real.log 5) := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have h5lo := CS_log_five_ge
  have h5hi := CS_log_five_le
  have hlo : (10.8634 : ℝ) ≤ 6.75 * Real.log 5 := by
    have hmul : 6.75 * (16094 / 10000 : ℝ) ≤ 6.75 * Real.log 5 :=
      mul_le_mul_of_nonneg_left h5lo (by norm_num)
    have hcap : (10.8634 : ℝ) ≤ 6.75 * (16094 / 10000) := by
      norm_num
    linarith
  have hhi : 6.75 * Real.log 5 ≤ (10.8642 : ℝ) := by
    have hmul : 6.75 * Real.log 5 ≤ 6.75 * (16095 / 10000 : ℝ) :=
      mul_le_mul_of_nonneg_left h5hi (by norm_num)
    have hcap : (6.75 : ℝ) * (16095 / 10000) ≤ 10.8642 := by
      norm_num
    linarith
  set x : ℝ := 6.75 * Real.log 5 with hx_def
  set d : ℝ := x - 7 * Real.pi / 2 with hd_def
  have hd_lo : (-0.14 : ℝ) ≤ d := by
    rw [hd_def]
    linarith
  have hd_hi : d ≤ (0 : ℝ) := by
    rw [hd_def]
    linarith
  have h32eq : (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 := by
    ring
  have hcos32 : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [h32eq, Real.cos_add, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hsin32 : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [h32eq, Real.sin_add, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hx_eq : x = (3 * Real.pi / 2 + d) + 2 * Real.pi := by
    rw [hd_def]
    ring
  have hcos_mid : Real.cos x = Real.cos (3 * Real.pi / 2 + d) := by
    rw [hx_eq, Real.cos_add_two_pi]
  have hcos_eq : Real.cos (3 * Real.pi / 2 + d) = Real.sin d := by
    rw [Real.cos_add, hcos32, hsin32]
    ring
  have hsin_lb : (-0.14 : ℝ) ≤ Real.sin d := by
    by_cases hd0 : (0 : ℝ) ≤ d
    · have hd_pi : d ≤ Real.pi := by linarith
      have hnn : (0 : ℝ) ≤ Real.sin d :=
        Real.sin_nonneg_of_nonneg_of_le_pi hd0 hd_pi
      linarith
    · push_neg at hd0
      have he_pos : (0 : ℝ) < -d := by linarith
      have hle : Real.sin (-d) ≤ -d := Real.sin_le he_pos.le
      have hneg : Real.sin d = -Real.sin (-d) := by
        have h := Real.sin_neg (x := -d)
        rw [neg_neg] at h
        exact h
      linarith
  rw [hcos_mid, hcos_eq]
  exact hsin_lb

/-- Cosine nonnegativity at `φ₆ = 6.75·log 6` (TRUE `≈ 0.8907 ≥ 0`).
Route: `φ₆ ∈ [11.7857, 12.3492]` from banked composite `log6` bounds,
so `e = φ₆ - 4π ∈ [-π/2, π/2]` and `cos φ₆ = cos e ≥ 0` (two
`Real.cos_add_two_pi` steps). The matching upper is the
TRIVIALLY-signed fallback `cos φ₆ ≤ 1` used at the S6 assembly. -/
theorem CS_cos6_nonneg :
    (0 : ℝ) ≤ Real.cos (6.75 * Real.log 6) := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have h6lo := CS_log_six_ge
  have h6hi := CS_log_six_le
  have hlo : (11.7857 : ℝ) ≤ 6.75 * Real.log 6 := by
    have hmul : 6.75 * (1.74604 : ℝ) ≤ 6.75 * Real.log 6 :=
      mul_le_mul_of_nonneg_left h6lo (by norm_num)
    have hcap : (11.7857 : ℝ) ≤ 6.75 * 1.74604 := by
      norm_num
    linarith
  have hhi : 6.75 * Real.log 6 ≤ (12.3492 : ℝ) := by
    have hmul : 6.75 * Real.log 6 ≤ 6.75 * 1.8295 :=
      mul_le_mul_of_nonneg_left h6hi (by norm_num)
    have hcap : (6.75 : ℝ) * 1.8295 ≤ 12.3492 := by
      norm_num
    linarith
  set x : ℝ := 6.75 * Real.log 6 with hx_def
  set e : ℝ := x - 2 * Real.pi - 2 * Real.pi with he_def
  have he_lo : -(Real.pi / 2) ≤ e := by
    rw [he_def]
    linarith
  have he_hi : e ≤ Real.pi / 2 := by
    rw [he_def]
    linarith
  have hx_eq : x = e + 2 * Real.pi + 2 * Real.pi := by
    rw [he_def]
    ring
  have hcos_eq : Real.cos x = Real.cos e := by
    have h1 : Real.cos (e + 2 * Real.pi + 2 * Real.pi)
        = Real.cos (e + 2 * Real.pi) := Real.cos_add_two_pi _
    have h2 : Real.cos (e + 2 * Real.pi) = Real.cos e :=
      Real.cos_add_two_pi _
    rw [hx_eq]
    exact h1.trans h2
  rw [hcos_eq]
  exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le he_lo he_hi

/-- Complex S6 partial sum at `sCenter`
(`1 - 2^{-s} + 3^{-s} - 4^{-s} + 5^{-s} - 6^{-s}`). -/
noncomputable def CS_S6C : ℂ :=
  (1 : ℂ) - (2 : ℂ) ^ (-R02Pilot.sCenter)
    + (3 : ℂ) ^ (-R02Pilot.sCenter) - (4 : ℂ) ^ (-R02Pilot.sCenter)
    + (5 : ℂ) ^ (-R02Pilot.sCenter) - (6 : ℂ) ^ (-R02Pilot.sCenter)

/-- Real-part identity for the complex S6 (cast + `sub_re` / `add_re` /
`one_re` + the five per-term cpow splits). -/
theorem CS_S6C_Re_eq :
    (CS_S6C).re = 1 - (2 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 2)
      + (3 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 3)
      - (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 4)
      + (5 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 5)
      - (6 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 6) := by
  unfold CS_S6C
  have h2 : ((2 : ℂ)) = ((((2 : ℝ)) : ℂ)) := by simp
  have h3 : ((3 : ℂ)) = ((((3 : ℝ)) : ℂ)) := by simp
  have h4c : ((4 : ℂ)) = ((((4 : ℝ)) : ℂ)) := by simp
  have h5 : ((5 : ℂ)) = ((((5 : ℝ)) : ℂ)) := by simp
  have h6 : ((6 : ℂ)) = ((((6 : ℝ)) : ℂ)) := by simp
  rw [h2, h3, h4c, h5, h6]
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re,
    CS_cpow2_sCenter_re, CS_cpow3_sCenter_re, CS_cpow4_sCenter_re,
    CS_cpow5_sCenter_re, CS_cpow6_sCenter_re]

/-- Complex-S6 real part `≥ 0.95` (PROVED, unconditional):
`Re(S₆) = Re(S₄) + Re₅ - Re₆` with `Re(S₄) ≥ 1.56` (banked),
`Re₅ ≥ 0.55·(-0.14) = -0.077` (new `r₅ ≤ 0.55`, signed
`cos φ₅ ∈ [-0.14, 0]`), `-Re₆ ≥ -0.53` (banked `r₆ ≤ 0.53`,
nonneg `cos φ₆ ≥ 0` + trivial fallback `cos φ₆ ≤ 1`).
Honest REGRESSION vs S4 `1.56` (true `Re(S₆) ≈ 1.366`). -/
theorem CS_complex_S6_Re_ge_095 :
    (0.95 : ℝ) ≤ (CS_S6C).re := by
  have hEq := CS_S6C_Re_eq
  have hEq4 := CS_S4C_Re_eq
  have hS4 := CS_complex_S4_Re_ge_156
  have hr5u : (5 : ℝ) ^ (-(0.395 : ℝ)) ≤ (0.55 : ℝ) :=
    CS_rpow5neg_upper055_proved
  have hr50 : (0 : ℝ) ≤ (5 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr6u : (6 : ℝ) ^ (-(0.395 : ℝ)) ≤ (0.53 : ℝ) :=
    CS_rpow6neg_upper_proved
  have hr60 : (0 : ℝ) ≤ (6 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hc5lo : (-0.14 : ℝ) ≤ Real.cos (6.75 * Real.log 5) :=
    CS_cos5_lower_neg014
  have hc5hi : Real.cos (6.75 * Real.log 5) ≤ 0 := CS_cos5_nonpos
  have hc6lo : (0 : ℝ) ≤ Real.cos (6.75 * Real.log 6) := CS_cos6_nonneg
  have hc6hi : Real.cos (6.75 * Real.log 6) ≤ 1 := Real.cos_le_one _
  have hLink : (CS_S6C).re = (CS_S4C).re
      + (5 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 5)
      - (6 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 6) := by
    rw [hEq, hEq4]
  have hT5 : (-0.077 : ℝ)
      ≤ (5 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 5) := by
    have hdiff : (5 : ℝ) ^ (-(0.395 : ℝ)) - 0.55 ≤ 0 := by linarith
    have hprod : (0 : ℝ) ≤ ((5 : ℝ) ^ (-(0.395 : ℝ)) - 0.55)
        * Real.cos (6.75 * Real.log 5) :=
      mul_nonneg_of_nonpos_of_nonpos hdiff hc5hi
    have hring : (5 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 5)
        - 0.55 * Real.cos (6.75 * Real.log 5)
        = ((5 : ℝ) ^ (-(0.395 : ℝ)) - 0.55)
          * Real.cos (6.75 * Real.log 5) := by
      ring
    have h1 : (0.55 : ℝ) * Real.cos (6.75 * Real.log 5)
        ≤ (5 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 5) := by
      linarith
    have hmul : (0.55 : ℝ) * (-0.14) = -0.077 := by norm_num
    have h2 : (-0.077 : ℝ) ≤ (0.55 : ℝ) * Real.cos (6.75 * Real.log 5) := by
      have hle : (0.55 : ℝ) * (-0.14)
          ≤ 0.55 * Real.cos (6.75 * Real.log 5) :=
        mul_le_mul_of_nonneg_left hc5lo (by norm_num)
      linarith
    linarith
  have hT6 : (6 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 6)
      ≤ (0.53 : ℝ) := by
    have ha : (6 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (6.75 * Real.log 6)
        ≤ 0.53 * Real.cos (6.75 * Real.log 6) :=
      mul_le_mul_of_nonneg_right hr6u hc6lo
    have hb : (0.53 : ℝ) * Real.cos (6.75 * Real.log 6) ≤ 0.53 * 1 :=
      mul_le_mul_of_nonneg_left hc6hi (by norm_num)
    have hmul : (0.53 : ℝ) * 1 = 0.53 := by norm_num
    linarith
  rw [hLink]
  linarith

/-- Complex-S6 absolute value `≥ 0.95` (triangle `‖z‖ ≥ Re z`,
mirroring `CS_complex_S4_abs_ge_156`). -/
theorem CS_complex_S6_abs_ge_095 :
    (0.95 : ℝ) ≤ ‖CS_S6C‖ := by
  have hRe := CS_complex_S6_Re_ge_095
  have hle : (CS_S6C).re ≤ ‖CS_S6C‖ := by
    have h1 := Complex.abs_re_le_norm (CS_S6C)
    have h2 := le_abs_self ((CS_S6C).re)
    linarith
  linarith

/-- S6 feed into the zeta assembly (exact instantiation shape, mirror of
`CS_zeta_of_S4`): with complex-S6 `slow = 0.95`, `tail = 0`,
`cF = 1.853`, `CS_zeta_of_parts` applies directly — `hNeed` is still
the unclosable `2.5942 ≤ 0.95` (see `CS_S6C_shortfall_1853`). -/
theorem CS_zeta_of_S6C (Z : ℝ)
    (hLink : (0.95 : ℝ) - 0 ≤ 1.853 * Z) (hNeed : (1.4 : ℝ) * 1.853 + 0 ≤ 0.95) :
    1.4 ≤ Z :=
  CS_zeta_of_parts 0.95 0 1.853 Z (by norm_num) hLink hNeed

/-- Exact new shortfall numeral (honest floor report): the `1.4` need at
`cF = 1.853` exceeds complex-S6 `slow = 0.95` by `1.6442` (was `1.0342`;
regression `0.61` — `Re`-only S6 cannot beat S4; `Im` route needed). -/
theorem CS_S6C_shortfall_1853 : (1.4 : ℝ) * 1.853 - 0.95 = 1.6442 := by
  norm_num

#print axioms CS_cpow5_sCenter_re
#print axioms CS_cpow6_sCenter_re
#print axioms CS_rpow5pos_lower183_proved
#print axioms CS_rpow5neg_upper055_proved
#print axioms CS_cos5_nonpos
#print axioms CS_cos5_lower_neg014
#print axioms CS_cos6_nonneg
#print axioms CS_complex_S6_Re_ge_095
#print axioms CS_complex_S6_abs_ge_095
#print axioms CS_S6C_shortfall_1853

/-! ## §A9. Complex S6 Im splits for n=5,6 ONLY (ETA-NEXT8 retry; ETA-NEXT7 EMPTY)

TIGHTER BRIEF compliance: read banked S6 assembly (`CS_S6C_Re_eq:2598` +
`CS_cpow5/6` Re splits `:2322/:2358`); prove Im splits for n=5,6 ONLY via
`Complex.cpow_def_of_ne_zero` + `Complex.exp_im`, mirroring the Re splits
token-for-token with banked `log5`/`log6` bounds; then Im(S6) lower via the
alternating sum (`CS_S4C` + 5,6 tail, no 2,3,4 Im reproofs); then
`‖S6‖ ≥ Im(S6)`; STOP honestly (no zeta feed / shortfall recompute forced).

Honest outcome (STALL, do not force):
* 5-term Im is STRICTLY NEGATIVE: `r₅·sin φ₅ ≤ -0.5148` (`r₅ ≥ 0.52`
  banked `CS_rpow5neg_lower_proved`, `sin φ₅ ≤ -0.99` proved below via
  `φ₅ = 7π/2 + d`, `d ∈ [-0.14, 0]`, `sin φ₅ = -cos d ≤ -0.99`).
* 6-term Im is NON-POSITIVE: `r₆·sin φ₆ ≤ 0` (`r₆ ≥ 0`,
  `sin φ₆ ≤ 0` proved below via `e = φ₆ - 4π ∈ [-π, 0]` negation route).
* Tail lower: `r₅·sin φ₅ ≥ -0.55` (`r₅ ≤ 0.55`, `sin ≥ -1`), so
  `Im(S₆) = Im(S₄) + tail ≥ Im(S₄) - 0.55` (conditional on explicit `S₄`
  premise `Y ≤ Im(S₄)`; unconditional positivity is OUT OF SCOPE per
  ONLY-5,6 and is NOT claimed).
* Hence no unconditional `Im(S₆) > 0` slow is closed here; live best
  STANDS: complex-S4 `slow = 1.56`, `cF = 1.853`,
  shortfall `1.4·1.853 - 1.56 = 1.0342` (`CS_S4_shortfall_1853`).
  True values (`Re(S₆) ≈ 1.366`, `Im(S₆) ≈ 1.00`, `|S₆| ≈ 1.70`) are
  consistent with this stall (Im-only `≈ 1.00 < 1.56` cannot beat S4
  alone; Pythagoras route needs a proved `Re+Im` pair, out of scope). -/

/-- Cpow imaginary-part split for `5^{-s}` at `sCenter` (token-for-token
mirror of `CS_cpow5_sCenter_re`: `(-s).re = -0.395`, `(-s).im = 6.75`,
`Complex.exp_im` + `sin` in place of `Complex.exp_re` + `cos`). -/
theorem CS_cpow5_sCenter_im : ((((5 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter)).im
    = (5 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 5) := by
  have h5pos : (0 : ℝ) < 5 := by norm_num
  have hxC : ((5 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h5pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((5 : ℝ) : ℂ) = (((Real.log 5 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h5pos)).symm
  rw [hlog]
  have hre_w : (-R02Pilot.sCenter).re = (-(0.395 : ℝ)) := by
    have e : (-R02Pilot.sCenter).re = -(R02Pilot.sCenter.re) := rfl
    rw [e, R02Pilot.sCenter_re]
  have him_w : (-R02Pilot.sCenter).im = (6.75 : ℝ) := by
    have e : (-R02Pilot.sCenter).im = -(R02Pilot.sCenter.im) := rfl
    rw [e, R02Pilot.sCenter_im]
    norm_num
  have hzre : ((((Real.log 5 : ℝ)) : ℂ)).re = Real.log 5 := Complex.ofReal_re _
  have hzim : ((((Real.log 5 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 5 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).re
      = Real.log 5 * (-(0.395 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 5 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).im
      = Real.log 5 * (6.75 : ℝ) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 5 * (-(0.395 : ℝ)))
      = (5 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_def_of_pos h5pos _).symm
  have hsin : Real.sin (Real.log 5 * (6.75 : ℝ))
      = Real.sin (6.75 * Real.log 5) := by
    rw [mul_comm]
  rw [Complex.exp_im, harg_re, harg_im, hexp, hsin]

/-- Cpow imaginary-part split for `6^{-s}` at `sCenter` (token-for-token
mirror of `CS_cpow6_sCenter_re`). -/
theorem CS_cpow6_sCenter_im : ((((6 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter)).im
    = (6 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 6) := by
  have h6pos : (0 : ℝ) < 6 := by norm_num
  have hxC : ((6 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h6pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((6 : ℝ) : ℂ) = (((Real.log 6 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h6pos)).symm
  rw [hlog]
  have hre_w : (-R02Pilot.sCenter).re = (-(0.395 : ℝ)) := by
    have e : (-R02Pilot.sCenter).re = -(R02Pilot.sCenter.re) := rfl
    rw [e, R02Pilot.sCenter_re]
  have him_w : (-R02Pilot.sCenter).im = (6.75 : ℝ) := by
    have e : (-R02Pilot.sCenter).im = -(R02Pilot.sCenter.im) := rfl
    rw [e, R02Pilot.sCenter_im]
    norm_num
  have hzre : ((((Real.log 6 : ℝ)) : ℂ)).re = Real.log 6 := Complex.ofReal_re _
  have hzim : ((((Real.log 6 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 6 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).re
      = Real.log 6 * (-(0.395 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 6 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).im
      = Real.log 6 * (6.75 : ℝ) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 6 * (-(0.395 : ℝ)))
      = (6 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_def_of_pos h6pos _).symm
  have hsin : Real.sin (Real.log 6 * (6.75 : ℝ))
      = Real.sin (6.75 * Real.log 6) := by
    rw [mul_comm]
  rw [Complex.exp_im, harg_re, harg_im, hexp, hsin]

/-- Sine upper at `φ₅ = 6.75·log 5` (`≤ -0.99`; TRUE `≈ -0.991`).
Route (mirror of `CS_cos5_lower_neg014`): `d = φ₅ - 7π/2 ∈ [-0.14, 0]`,
`φ₅ = (3π/2 + d) + 2π`, `sin φ₅ = -cos d ≤ -0.99`
(`cos d ≥ 1 - d²/2 ≥ 0.99`). -/
theorem CS_sin5_upper_neg099 :
    Real.sin (6.75 * Real.log 5) ≤ (-0.99 : ℝ) := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have h5lo := CS_log_five_ge
  have h5hi := CS_log_five_le
  have hlo : (10.8634 : ℝ) ≤ 6.75 * Real.log 5 := by
    have hmul : 6.75 * (16094 / 10000 : ℝ) ≤ 6.75 * Real.log 5 :=
      mul_le_mul_of_nonneg_left h5lo (by norm_num)
    have hcap : (10.8634 : ℝ) ≤ 6.75 * (16094 / 10000) := by
      norm_num
    linarith
  have hhi : 6.75 * Real.log 5 ≤ (10.8642 : ℝ) := by
    have hmul : 6.75 * Real.log 5 ≤ 6.75 * (16095 / 10000 : ℝ) :=
      mul_le_mul_of_nonneg_left h5hi (by norm_num)
    have hcap : (6.75 : ℝ) * (16095 / 10000) ≤ 10.8642 := by
      norm_num
    linarith
  set x : ℝ := 6.75 * Real.log 5 with hx_def
  set d : ℝ := x - 7 * Real.pi / 2 with hd_def
  have hd_lo : (-0.14 : ℝ) ≤ d := by
    rw [hd_def]
    linarith
  have hd_hi : d ≤ (0 : ℝ) := by
    rw [hd_def]
    linarith
  have h32eq : (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 := by
    ring
  have hcos32 : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [h32eq, Real.cos_add, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hsin32 : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [h32eq, Real.sin_add, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hx_eq : x = (3 * Real.pi / 2 + d) + 2 * Real.pi := by
    rw [hd_def]
    ring
  have hsin_mid : Real.sin x = Real.sin (3 * Real.pi / 2 + d) := by
    rw [hx_eq, Real.sin_add_two_pi]
  have hsin_eq : Real.sin (3 * Real.pi / 2 + d) = -Real.cos d := by
    rw [Real.sin_add, hsin32, hcos32]
    ring
  have hsq : d ^ 2 ≤ (0.14 : ℝ) ^ 2 := by
    have h1 : (0 : ℝ) ≤ d + 0.14 := by linarith
    have h2 : (0 : ℝ) ≤ -d := by linarith
    nlinarith [mul_nonneg h1 h2]
  have hcosd_lo : (0.99 : ℝ) ≤ Real.cos d := by
    have hquad := Real.one_sub_sq_div_two_le_cos (x := d)
    have hnum : (0.99 : ℝ) ≤ 1 - (0.14 : ℝ) ^ 2 / 2 := by
      norm_num
    linarith
  rw [hsin_mid, hsin_eq]
  linarith

/-- Sine nonpositivity at `φ₆ = 6.75·log 6` (TRUE `≈ -0.454 ≤ 0`).
Route: `φ₆ ∈ [11.7857, 12.3492]` from banked composite `log6` bounds, so
`e = φ₆ - 4π ∈ [-π, 0]`; `sin φ₆ = sin e = -sin(-e) ≤ 0` via
`Real.sin_add_two_pi` (twice) + `Real.sin_nonneg_of_nonneg_of_le_pi`
on `-e ∈ [0, π]` (negation route, no new sin machinery). -/
theorem CS_sin6_nonpos :
    Real.sin (6.75 * Real.log 6) ≤ (0 : ℝ) := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have h6lo := CS_log_six_ge
  have h6hi := CS_log_six_le
  have hlo : (11.7857 : ℝ) ≤ 6.75 * Real.log 6 := by
    have hmul : 6.75 * (1.74604 : ℝ) ≤ 6.75 * Real.log 6 :=
      mul_le_mul_of_nonneg_left h6lo (by norm_num)
    have hcap : (11.7857 : ℝ) ≤ 6.75 * 1.74604 := by
      norm_num
    linarith
  have hhi : 6.75 * Real.log 6 ≤ (12.3492 : ℝ) := by
    have hmul : 6.75 * Real.log 6 ≤ 6.75 * 1.8295 :=
      mul_le_mul_of_nonneg_left h6hi (by norm_num)
    have hcap : (6.75 : ℝ) * 1.8295 ≤ 12.3492 := by
      norm_num
    linarith
  set x : ℝ := 6.75 * Real.log 6 with hx_def
  set e : ℝ := x - 2 * Real.pi - 2 * Real.pi with he_def
  have hne0 : (0 : ℝ) ≤ -e := by
    rw [he_def]
    linarith
  have hne_pi : -e ≤ Real.pi := by
    rw [he_def]
    linarith
  have hnn : (0 : ℝ) ≤ Real.sin (-e) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hne0 hne_pi
  have hneg : Real.sin e = -Real.sin (-e) := by
    have h := Real.sin_neg (x := -e)
    rw [neg_neg] at h
    exact h
  have hx_eq : x = e + 2 * Real.pi + 2 * Real.pi := by
    rw [he_def]
    ring
  have hsin_eq : Real.sin x = Real.sin e := by
    have h1 : Real.sin (e + 2 * Real.pi + 2 * Real.pi)
        = Real.sin (e + 2 * Real.pi) := Real.sin_add_two_pi _
    have h2 : Real.sin (e + 2 * Real.pi) = Real.sin e :=
      Real.sin_add_two_pi _
    rw [hx_eq]
    exact h1.trans h2
  rw [hsin_eq, hneg]
  linarith

/-- 5-term Im lower (`≥ -0.55`; TRUE `≈ -0.5247`): `r₅ ≤ 0.55`
(banked) and `sin φ₅ ≥ -1`. -/
theorem CS_Im5_ge_neg055 :
    (-0.55 : ℝ) ≤ (5 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 5) := by
  have hr0 : (0 : ℝ) ≤ (5 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hru : (5 : ℝ) ^ (-(0.395 : ℝ)) ≤ (0.55 : ℝ) :=
    CS_rpow5neg_upper055_proved
  have hslo : (-1 : ℝ) ≤ Real.sin (6.75 * Real.log 5) :=
    Real.neg_one_le_sin _
  have h1 : (5 : ℝ) ^ (-(0.395 : ℝ)) * (-1)
      ≤ (5 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 5) :=
    mul_le_mul_of_nonneg_left hslo hr0
  have hring : (5 : ℝ) ^ (-(0.395 : ℝ)) * (-1)
      = -((5 : ℝ) ^ (-(0.395 : ℝ))) := by
    ring
  have h2 : (-0.55 : ℝ) ≤ (5 : ℝ) ^ (-(0.395 : ℝ)) * (-1) := by
    rw [hring]
    linarith
  linarith

/-- 5-term Im HONEST UPPER (STALL numeral): `r₅·sin φ₅ ≤ -0.5148 < 0`
(`r₅ ≥ 0.52` banked `CS_rpow5neg_lower_proved`, `sin φ₅ ≤ -0.99` above).
The 5-term is strictly negative — no force. -/
theorem CS_Im5_le_neg05148 :
    (5 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 5) ≤ (-0.5148 : ℝ) := by
  have hr0 : (0 : ℝ) ≤ (5 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hrl : (0.52 : ℝ) ≤ (5 : ℝ) ^ (-(0.395 : ℝ)) :=
    CS_rpow5neg_lower_proved
  have hsup : Real.sin (6.75 * Real.log 5) ≤ (-0.99 : ℝ) :=
    CS_sin5_upper_neg099
  have h1 : (5 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 5)
      ≤ (5 : ℝ) ^ (-(0.395 : ℝ)) * (-0.99) :=
    mul_le_mul_of_nonneg_left hsup hr0
  have h2 : (5 : ℝ) ^ (-(0.395 : ℝ)) * (-0.99) ≤ (0.52 : ℝ) * (-0.99) :=
    mul_le_mul_of_nonpos_right hrl (by norm_num)
  have hmul : (0.52 : ℝ) * (-0.99) = -0.5148 := by norm_num
  linarith

/-- 6-term Im non-positive (`r₆·sin φ₆ ≤ 0`; TRUE `≈ -0.223`). -/
theorem CS_Im6_nonpos :
    (6 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 6) ≤ (0 : ℝ) := by
  have hr0 : (0 : ℝ) ≤ (6 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hs : Real.sin (6.75 * Real.log 6) ≤ 0 := CS_sin6_nonpos
  exact mul_nonpos_of_nonneg_of_nonpos hr0 hs

/-- S6 Im link via the alternating sum (`CS_S6C = CS_S4C + 5^{-s} - 6^{-s}`
as `ℂ`, then `.im` + the two new Im splits; NO 2,3,4 Im reproofs needed). -/
theorem CS_S6C_Im_link :
    (CS_S6C).im = (CS_S4C).im
      + (5 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 5)
      - (6 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 6) := by
  have hEq : CS_S6C = CS_S4C + ((((5 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter))
      - ((((6 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter)) := by
    unfold CS_S6C CS_S4C
    have h5 : ((5 : ℂ)) = ((((5 : ℝ)) : ℂ)) := by simp
    have h6 : ((6 : ℂ)) = ((((6 : ℝ)) : ℂ)) := by simp
    rw [h5, h6]
    abel
  rw [hEq, Complex.add_im, Complex.sub_im,
    CS_cpow5_sCenter_im, CS_cpow6_sCenter_im]

/-- Conditional S6 Im lower via the alternating sum (explicit `S₄`
premise only): from `Y ≤ Im(S₄)`, `Im(S₆) ≥ Y - 0.55`
(tail `≥ -0.55`, 6-term `≥ 0` contribution via `CS_Im6_nonpos`). -/
theorem CS_complex_S6_Im_ge_of_S4 (Y : ℝ) (hS4 : Y ≤ (CS_S4C).im) :
    Y - 0.55 ≤ (CS_S6C).im := by
  have hLink := CS_S6C_Im_link
  have hT5 := CS_Im5_ge_neg055
  have hT6 := CS_Im6_nonpos
  linarith

/-- `‖S₆‖ ≥ Im(S₆)` triangle step (mirror of `CS_complex_S6_abs_ge_095`
with `abs_im_le_norm`). -/
theorem CS_complex_S6_abs_ge_Im :
    (CS_S6C).im ≤ ‖CS_S6C‖ := by
  have h1 := Complex.abs_im_le_norm (CS_S6C)
  have h2 := le_abs_self ((CS_S6C).im)
  linarith

#print axioms CS_cpow5_sCenter_im
#print axioms CS_cpow6_sCenter_im
#print axioms CS_sin5_upper_neg099
#print axioms CS_sin6_nonpos
#print axioms CS_Im5_ge_neg055
#print axioms CS_Im5_le_neg05148
#print axioms CS_Im6_nonpos
#print axioms CS_S6C_Im_link
#print axioms CS_complex_S6_Im_ge_of_S4
#print axioms CS_complex_S6_abs_ge_Im

/-! ## §A10. Complex S4 Im splits for n=1..4 + Im(S4) LOWER (ETA-NEXT9)

Token-for-token mirrors of the n=5,6 Im splits (`cpow_def_of_ne_zero` +
`exp_im`) with banked log bounds (`log1 = 0` exact via `Real.log_one`,
`log2` 6-digit, `log3` coarse, `log4 = 2·log2` exact); sin-phase windows
per n; then `Im(S4)` LOWER with exact numerals.

Honest outcome (STALL, do not force):
* `Im₂ = r₂·sin φ₂ ≤ -0.7425` (`r₂ ≥ 0.75` banked, `sin φ₂ ≤ -0.99`
  via `φ₂ - 3π/2 ∈ [-0.14, 0]`, `sin = -cos`, quadratic floor).
* `Im₃ = r₃·sin φ₃ ≥ 0` (`r₃ ≥ 0`, `sin φ₃ ≥ 0` via `φ₃ - 2π ∈ [0, π]`).
* `Im₄ = r₄·sin φ₄ ≤ 0.0408` (`r₄ ≤ 0.60` banked, `sin φ₄ ≤ 0.068`
  via `δ = 3π - φ₄ ∈ [0, 0.068]`, `sin φ₄ = sin δ ≤ δ`).
* Hence `Im(S₄) = -Im₂ + Im₃ - Im₄ ≥ 0.7425 - 0.0408 = 0.7017`
  (TRUE `≈ 1.307`; weak but unconditional and committable).
* Tail: `Im(S₆) ≥ Im(S₄) - 0.55 ≥ 0.1517` (via banked
  `CS_complex_S6_Im_ge_of_S4` + `CS_Im5_ge_neg055` + `CS_Im6_nonpos`).
* `0.1517 < 0.95`: the Im-only route does NOT beat the banked Re-route
  (`CS_complex_S6_Re_ge_095`); live best STANDS (complex-S4 `slow = 1.56`,
  `cF = 1.853`, shortfall `1.0342`). True `|S₆| ≈ 1.70` needs the
  proved `Re+Im` Pythagoras pair (out of scope this turn). -/

/-- Cpow imaginary-part split for `1^{-s}` at `sCenter` (token-for-token
mirror of `CS_cpow5_sCenter_im`; `log 1 = 0` exact). -/
theorem CS_cpow1_sCenter_im : ((((1 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter)).im
    = (1 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 1) := by
  have h1pos : (0 : ℝ) < 1 := by norm_num
  have hxC : ((1 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h1pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((1 : ℝ) : ℂ) = (((Real.log 1 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h1pos)).symm
  rw [hlog]
  have hre_w : (-R02Pilot.sCenter).re = (-(0.395 : ℝ)) := by
    have e : (-R02Pilot.sCenter).re = -(R02Pilot.sCenter.re) := rfl
    rw [e, R02Pilot.sCenter_re]
  have him_w : (-R02Pilot.sCenter).im = (6.75 : ℝ) := by
    have e : (-R02Pilot.sCenter).im = -(R02Pilot.sCenter.im) := rfl
    rw [e, R02Pilot.sCenter_im]
    norm_num
  have hzre : ((((Real.log 1 : ℝ)) : ℂ)).re = Real.log 1 := Complex.ofReal_re _
  have hzim : ((((Real.log 1 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 1 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).re
      = Real.log 1 * (-(0.395 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 1 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).im
      = Real.log 1 * (6.75 : ℝ) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 1 * (-(0.395 : ℝ)))
      = (1 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_def_of_pos h1pos _).symm
  have hsin : Real.sin (Real.log 1 * (6.75 : ℝ))
      = Real.sin (6.75 * Real.log 1) := by
    rw [mul_comm]
  rw [Complex.exp_im, harg_re, harg_im, hexp, hsin]

/-- Cpow imaginary-part split for `2^{-s}` at `sCenter` (token-for-token
mirror of `CS_cpow2_sCenter_re`: `Complex.exp_im` + `sin` in place of
`Complex.exp_re` + `cos`). -/
theorem CS_cpow2_sCenter_im : ((((2 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter)).im
    = (2 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 2) := by
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
  have hsin : Real.sin (Real.log 2 * (6.75 : ℝ))
      = Real.sin (6.75 * Real.log 2) := by
    rw [mul_comm]
  rw [Complex.exp_im, harg_re, harg_im, hexp, hsin]

/-- Cpow imaginary-part split for `3^{-s}` at `sCenter` (token-for-token
mirror of `CS_cpow3_sCenter_re`). -/
theorem CS_cpow3_sCenter_im : ((((3 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter)).im
    = (3 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 3) := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hxC : ((3 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h3pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((3 : ℝ) : ℂ) = (((Real.log 3 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h3pos)).symm
  rw [hlog]
  have hre_w : (-R02Pilot.sCenter).re = (-(0.395 : ℝ)) := by
    have e : (-R02Pilot.sCenter).re = -(R02Pilot.sCenter.re) := rfl
    rw [e, R02Pilot.sCenter_re]
  have him_w : (-R02Pilot.sCenter).im = (6.75 : ℝ) := by
    have e : (-R02Pilot.sCenter).im = -(R02Pilot.sCenter.im) := rfl
    rw [e, R02Pilot.sCenter_im]
    norm_num
  have hzre : ((((Real.log 3 : ℝ)) : ℂ)).re = Real.log 3 := Complex.ofReal_re _
  have hzim : ((((Real.log 3 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 3 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).re
      = Real.log 3 * (-(0.395 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 3 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).im
      = Real.log 3 * (6.75 : ℝ) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 3 * (-(0.395 : ℝ)))
      = (3 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_def_of_pos h3pos _).symm
  have hsin : Real.sin (Real.log 3 * (6.75 : ℝ))
      = Real.sin (6.75 * Real.log 3) := by
    rw [mul_comm]
  rw [Complex.exp_im, harg_re, harg_im, hexp, hsin]

/-- Cpow imaginary-part split for `4^{-s}` at `sCenter` (token-for-token
mirror of `CS_cpow4_sCenter_re`). -/
theorem CS_cpow4_sCenter_im : ((((4 : ℝ)) : ℂ) ^ (-R02Pilot.sCenter)).im
    = (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 4) := by
  have h4pos : (0 : ℝ) < 4 := by norm_num
  have hxC : ((4 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h4pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((4 : ℝ) : ℂ) = (((Real.log 4 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h4pos)).symm
  rw [hlog]
  have hre_w : (-R02Pilot.sCenter).re = (-(0.395 : ℝ)) := by
    have e : (-R02Pilot.sCenter).re = -(R02Pilot.sCenter.re) := rfl
    rw [e, R02Pilot.sCenter_re]
  have him_w : (-R02Pilot.sCenter).im = (6.75 : ℝ) := by
    have e : (-R02Pilot.sCenter).im = -(R02Pilot.sCenter.im) := rfl
    rw [e, R02Pilot.sCenter_im]
    norm_num
  have hzre : ((((Real.log 4 : ℝ)) : ℂ)).re = Real.log 4 := Complex.ofReal_re _
  have hzim : ((((Real.log 4 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 4 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).re
      = Real.log 4 * (-(0.395 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 4 : ℝ)) : ℂ) * (-R02Pilot.sCenter)).im
      = Real.log 4 * (6.75 : ℝ) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 4 * (-(0.395 : ℝ)))
      = (4 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_def_of_pos h4pos _).symm
  have hsin : Real.sin (Real.log 4 * (6.75 : ℝ))
      = Real.sin (6.75 * Real.log 4) := by
    rw [mul_comm]
  rw [Complex.exp_im, harg_re, harg_im, hexp, hsin]

/-- Sine upper at `φ₂ = 6.75·log 2` (`≤ -0.99`; TRUE `≈ -0.9994`).
Route (mirror of `CS_sin5_upper_neg099` without the `2π` shift):
`d = φ₂ - 3π/2 ∈ [-0.14, 0]`, `sin φ₂ = -cos d ≤ -0.99`
(`cos d ≥ 1 - d²/2 ≥ 0.99`). -/
theorem CS_sin2_upper_neg099 :
    Real.sin (6.75 * Real.log 2) ≤ (-0.99 : ℝ) := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have h2lo := CS_log2_ge
  have h2hi := CS_log2_le
  have hlo : (4.67874 : ℝ) ≤ 6.75 * Real.log 2 := by
    have hmul : 6.75 * (0.693147 : ℝ) ≤ 6.75 * Real.log 2 :=
      mul_le_mul_of_nonneg_left h2lo.le (by norm_num)
    have hcap : (4.67874 : ℝ) ≤ 6.75 * 0.693147 := by
      norm_num
    linarith
  have hhi : 6.75 * Real.log 2 ≤ (4.67875 : ℝ) := by
    have hmul : 6.75 * Real.log 2 ≤ 6.75 * (0.693148 : ℝ) :=
      mul_le_mul_of_nonneg_left h2hi.le (by norm_num)
    have hcap : (6.75 : ℝ) * 0.693148 ≤ 4.67875 := by
      norm_num
    linarith
  set x : ℝ := 6.75 * Real.log 2 with hx_def
  set d : ℝ := x - 3 * Real.pi / 2 with hd_def
  have hd_lo : (-0.14 : ℝ) ≤ d := by
    rw [hd_def]
    linarith
  have hd_hi : d ≤ (0 : ℝ) := by
    rw [hd_def]
    linarith
  have h32eq : (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 := by
    ring
  have hcos32 : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [h32eq, Real.cos_add, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hsin32 : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [h32eq, Real.sin_add, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hx_eq : x = 3 * Real.pi / 2 + d := by
    rw [hd_def]
    ring
  have hsin_eq : Real.sin (3 * Real.pi / 2 + d) = -Real.cos d := by
    rw [Real.sin_add, hsin32, hcos32]
    ring
  have hsq : d ^ 2 ≤ (0.14 : ℝ) ^ 2 := by
    have h1 : (0 : ℝ) ≤ d + 0.14 := by linarith
    have h2 : (0 : ℝ) ≤ -d := by linarith
    nlinarith [mul_nonneg h1 h2]
  have hcosd_lo : (0.99 : ℝ) ≤ Real.cos d := by
    have hquad := Real.one_sub_sq_div_two_le_cos (x := d)
    have hnum : (0.99 : ℝ) ≤ 1 - (0.14 : ℝ) ^ 2 / 2 := by
      norm_num
    linarith
  rw [hx_eq, hsin_eq]
  linarith

/-- Sine nonnegativity at `φ₃ = 6.75·log 3` (TRUE `≈ 0.905 ≥ 0`).
Route (mirror of `CS_cos3_nonneg`): `φ₃ ∈ [7.10707, 7.67003]` from
banked coarse `log3` bounds, so `e = φ₃ - 2π ∈ [0, π]` and
`sin φ₃ = sin e ≥ 0` via `Real.sin_add_two_pi` +
`Real.sin_nonneg_of_nonneg_of_le_pi`. -/
theorem CS_sin3_nonneg :
    (0 : ℝ) ≤ Real.sin (6.75 * Real.log 3) := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have h3lo := CS_log_three_ge
  have h3hi := CS_log_three_le
  have hlo : (7.10707 : ℝ) ≤ 6.75 * Real.log 3 := by
    have hmul : 6.75 * (1.0529 : ℝ) ≤ 6.75 * Real.log 3 :=
      mul_le_mul_of_nonneg_left h3lo (by norm_num)
    have hcap : (7.10707 : ℝ) ≤ 6.75 * 1.0529 := by
      norm_num
    linarith
  have hhi : 6.75 * Real.log 3 ≤ (7.67003 : ℝ) := by
    have hmul : 6.75 * Real.log 3 ≤ 6.75 * 1.1363 :=
      mul_le_mul_of_nonneg_left h3hi (by norm_num)
    have hcap : (6.75 : ℝ) * 1.1363 ≤ 7.67003 := by
      norm_num
    linarith
  set x : ℝ := 6.75 * Real.log 3 with hx_def
  set e : ℝ := x - 2 * Real.pi with he_def
  have he_lo : (0 : ℝ) ≤ e := by
    rw [he_def]
    linarith
  have he_hi : e ≤ Real.pi := by
    rw [he_def]
    linarith
  have hx_eq : x = e + 2 * Real.pi := by
    rw [he_def]
    ring
  have hsin_eq : Real.sin x = Real.sin e := by
    rw [hx_eq, Real.sin_add_two_pi]
  rw [hsin_eq]
  exact Real.sin_nonneg_of_nonneg_of_le_pi he_lo he_hi

/-- Sine upper at `φ₄ = 6.75·log 4` (`≤ 0.068`; TRUE `≈ 0.0673`).
Route: `φ₄ ∈ [9.35748, 9.35750]` via `CS_log_four_eq` + 6-digit `log2`
bounds, so `δ = 3π - φ₄ ∈ [0, 0.068]`; `φ₄ = (π - δ) + 2π`,
`sin φ₄ = sin(π - δ) = sin δ ≤ δ ≤ 0.068` via `Real.sin_add_two_pi`
+ a `Real.sin_add` expansion (banked `sin_pi`/`cos_pi`/`sin_neg` only)
+ `Real.sin_le`. -/
theorem CS_sin4_upper_0068 :
    Real.sin (6.75 * Real.log 4) ≤ (0.068 : ℝ) := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have h4 : Real.log 4 = 2 * Real.log 2 := CS_log_four_eq
  have h2lo := CS_log2_ge
  have h2hi := CS_log2_le
  have hphi_lo : (9.35748 : ℝ) ≤ 6.75 * Real.log 4 := by
    rw [h4]
    have hmul : 13.5 * (0.693147 : ℝ) ≤ 13.5 * Real.log 2 :=
      mul_le_mul_of_nonneg_left h2lo.le (by norm_num)
    have hcap : (9.35748 : ℝ) ≤ 13.5 * 0.693147 := by
      norm_num
    have heq : 6.75 * (2 * Real.log 2) = 13.5 * Real.log 2 := by
      ring
    linarith
  have hphi_hi : 6.75 * Real.log 4 ≤ (9.35750 : ℝ) := by
    rw [h4]
    have hmul : 13.5 * Real.log 2 ≤ 13.5 * 0.693148 :=
      mul_le_mul_of_nonneg_left h2hi.le (by norm_num)
    have hcap : (13.5 : ℝ) * 0.693148 ≤ 9.35750 := by
      norm_num
    have heq : 6.75 * (2 * Real.log 2) = 13.5 * Real.log 2 := by
      ring
    linarith
  set x : ℝ := 6.75 * Real.log 4 with hx_def
  set d : ℝ := 3 * Real.pi - x with hd_def
  have hd_lo : (0 : ℝ) ≤ d := by
    rw [hd_def]
    linarith
  have hd_hi : d ≤ (0.068 : ℝ) := by
    rw [hd_def]
    linarith
  have hx_eq : x = (Real.pi - d) + 2 * Real.pi := by
    rw [hd_def]
    ring
  have hsin2pi : Real.sin x = Real.sin (Real.pi - d) := by
    rw [hx_eq, Real.sin_add_two_pi]
  have hpi_sub : Real.sin (Real.pi - d) = Real.sin d := by
    have h1 : Real.pi - d = Real.pi + (-d) := by ring
    rw [h1, Real.sin_add, Real.sin_pi, Real.cos_pi]
    have h2 : Real.sin (-d) = -Real.sin d := Real.sin_neg (x := d)
    rw [h2]
    ring
  have hle : Real.sin d ≤ d := Real.sin_le hd_lo
  rw [hsin2pi, hpi_sub]
  linarith

/-- 2-term Im HONEST UPPER (`≤ -0.7425`; TRUE `≈ -0.7600`):
`r₂ ≥ 0.75` banked, `sin φ₂ ≤ -0.99` above. -/
theorem CS_Im2_le_neg07425 :
    (2 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 2) ≤ (-0.7425 : ℝ) := by
  have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hrl : (0.75 : ℝ) ≤ (2 : ℝ) ^ (-(0.395 : ℝ)) :=
    CS_rpow2_low075_proved
  have hsup : Real.sin (6.75 * Real.log 2) ≤ (-0.99 : ℝ) :=
    CS_sin2_upper_neg099
  have h1 : (2 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 2)
      ≤ (2 : ℝ) ^ (-(0.395 : ℝ)) * (-0.99) :=
    mul_le_mul_of_nonneg_left hsup hr0
  have h2 : (2 : ℝ) ^ (-(0.395 : ℝ)) * (-0.99) ≤ (0.75 : ℝ) * (-0.99) :=
    mul_le_mul_of_nonpos_right hrl (by norm_num)
  have hmul : (0.75 : ℝ) * (-0.99) = -0.7425 := by norm_num
  linarith

/-- 3-term Im nonnegativity (`≥ 0`; TRUE `≈ 0.586`): `r₃ ≥ 0`,
`sin φ₃ ≥ 0` above. -/
theorem CS_Im3_nonneg :
    (0 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 3) := by
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hs : (0 : ℝ) ≤ Real.sin (6.75 * Real.log 3) := CS_sin3_nonneg
  exact mul_nonneg hr0 hs

/-- 4-term Im upper (`≤ 0.0408`; TRUE `≈ 0.0389`): `r₄ ≤ 0.60`
banked, `sin φ₄ ≤ 0.068` above (`0.60·0.068 = 0.0408`). -/
theorem CS_Im4_le_00408 :
    (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 4) ≤ (0.0408 : ℝ) := by
  have hr0 : (0 : ℝ) ≤ (4 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hru : (4 : ℝ) ^ (-(0.395 : ℝ)) ≤ (0.60 : ℝ) :=
    CS_rpow4neg_upper_proved
  have hsup : Real.sin (6.75 * Real.log 4) ≤ (0.068 : ℝ) :=
    CS_sin4_upper_0068
  have h1 : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 4)
      ≤ (4 : ℝ) ^ (-(0.395 : ℝ)) * (0.068 : ℝ) :=
    mul_le_mul_of_nonneg_left hsup hr0
  have h2 : (4 : ℝ) ^ (-(0.395 : ℝ)) * (0.068 : ℝ) ≤ (0.60 : ℝ) * (0.068 : ℝ) :=
    mul_le_mul_of_nonneg_right hru (by norm_num)
  have hmul : (0.60 : ℝ) * (0.068 : ℝ) = 0.0408 := by norm_num
  linarith

/-- Imaginary-part identity for the complex S4 (cast + `sub_im` /
`add_im` / `one_im` + the three per-term cpow Im splits; the `1` term
contributes `0`). -/
theorem CS_S4C_Im_eq :
    (CS_S4C).im = 0 - (2 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 2)
      + (3 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 3)
      - (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.sin (6.75 * Real.log 4) := by
  unfold CS_S4C
  have h2 : ((2 : ℂ)) = ((((2 : ℝ)) : ℂ)) := by simp
  have h3 : ((3 : ℂ)) = ((((3 : ℝ)) : ℂ)) := by simp
  have h4c : ((4 : ℂ)) = ((((4 : ℝ)) : ℂ)) := by simp
  rw [h2, h3, h4c]
  simp only [Complex.add_im, Complex.sub_im, Complex.one_im,
    CS_cpow2_sCenter_im, CS_cpow3_sCenter_im, CS_cpow4_sCenter_im]

/-- Complex-S4 imaginary part `≥ 0.7017` (PROVED, unconditional):
`-Im₂ ≥ 0.7425`, `Im₃ ≥ 0`, `-Im₄ ≥ -0.0408`, so
`Im(S₄) ≥ 0.7425 - 0.0408 = 0.7017` (TRUE `≈ 1.307`). -/
theorem CS_complex_S4_Im_ge_07017 :
    (0.7017 : ℝ) ≤ (CS_S4C).im := by
  have hEq := CS_S4C_Im_eq
  have hT2 := CS_Im2_le_neg07425
  have hT3 := CS_Im3_nonneg
  have hT4 := CS_Im4_le_00408
  rw [hEq]
  linarith

/-- Unconditional S6 Im lower `≥ 0.1517` via the banked conditional link:
`Im(S₆) ≥ Im(S₄) - 0.55 ≥ 0.7017 - 0.55 = 0.1517`. -/
theorem CS_complex_S6_Im_ge_01517 :
    (0.1517 : ℝ) ≤ (CS_S6C).im := by
  have hS4 : (0.7017 : ℝ) ≤ (CS_S4C).im := CS_complex_S4_Im_ge_07017
  have h := CS_complex_S6_Im_ge_of_S4 0.7017 hS4
  have hnum : (0.7017 : ℝ) - 0.55 = 0.1517 := by norm_num
  linarith

/-- `‖S₆‖ ≥ 0.1517` triangle step (`‖z‖ ≥ Im z`). -/
theorem CS_complex_S6_abs_ge_01517 :
    (0.1517 : ℝ) ≤ ‖CS_S6C‖ := by
  have hIm := CS_complex_S6_Im_ge_01517
  have hle : (CS_S6C).im ≤ ‖CS_S6C‖ := CS_complex_S6_abs_ge_Im
  linarith

/-- Honest stall numeral: the new Im-only `0.1517` does NOT beat the
banked Re-route `0.95` (Pythagoras `Re+Im` pair out of scope). -/
theorem CS_ImS6_below_Re : (0.1517 : ℝ) < (0.95 : ℝ) := by
  norm_num

/-! ## §A11. Complex S4 Pythagoras `‖S₄‖ ≥ 1.71` (ETA-NEXT10)

KEY UNLOCK: `|S₄| ≥ sqrt(1.56^2 + 0.7017^2) ≈ 1.71` beats `1.56`.
Numerals (Python-verified): `1.56^2 = 2.4336`, `0.7017^2 = 0.49238289`,
sum `= 2.92598289 ≥ 2.9241 = 1.71^2`; `1.72^2 = 2.9584` fails, so `1.71`
is the largest 2-decimal that proves. Shortfall at `cF = 1.853`:
`1.4 * 1.853 - 1.71 = 0.8842`. -/

/-- Complex-S4 Pythagoras absolute value `≥ 1.71` (PROVED, unconditional):
`‖S₄‖^2 = Re^2 + Im^2 ≥ 1.56^2 + 0.7017^2 = 2.92598289 ≥ 2.9241 = 1.71^2`
via `Complex.sq_norm` (mirror of `CS_complex_S2_abs_ge_125`), then
`Real.sqrt` monotone. -/
theorem CS_complex_S4_abs_ge_pyth :
    (1.71 : ℝ) ≤ ‖CS_S4C‖ := by
  have hRe := CS_complex_S4_Re_ge_156
  have hIm := CS_complex_S4_Im_ge_07017
  have hsq_eq : ‖CS_S4C‖ ^ 2 = (CS_S4C).re ^ 2 + (CS_S4C).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have hRe2 : (1.56 : ℝ) ^ 2 ≤ (CS_S4C).re ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hRe 2
  have hIm2 : (0.7017 : ℝ) ^ 2 ≤ (CS_S4C).im ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hIm 2
  have hsq_ge : (1.71 : ℝ) ^ 2 ≤ ‖CS_S4C‖ ^ 2 := by
    have h171 : (1.71 : ℝ) ^ 2 = 2.9241 := by norm_num
    have hsum : (1.56 : ℝ) ^ 2 + (0.7017 : ℝ) ^ 2 = 2.92598289 := by norm_num
    have hle_num : (2.9241 : ℝ) ≤ 2.92598289 := by norm_num
    rw [hsq_eq]
    linarith
  calc (1.71 : ℝ) = Real.sqrt ((1.71 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖CS_S4C‖ ^ 2) := Real.sqrt_le_sqrt hsq_ge
    _ = ‖CS_S4C‖ := Real.sqrt_sq (norm_nonneg _)

/-- S4b feed into the zeta assembly (exact instantiation shape, mirror of
`CS_zeta_of_S4`): with complex-S4-Pythagoras `slow = 1.71`, `tail = 0`,
`cF = 1.853`, `CS_zeta_of_parts` applies directly — `hNeed` is still
the unclosable `2.5942 ≤ 1.71` (see `CS_S4b_shortfall_1853`). -/
theorem CS_zeta_of_S4b (Z : ℝ)
    (hLink : (1.71 : ℝ) - 0 ≤ 1.853 * Z) (hNeed : (1.4 : ℝ) * 1.853 + 0 ≤ 1.71) :
    1.4 ≤ Z :=
  CS_zeta_of_parts 1.71 0 1.853 Z (by norm_num) hLink hNeed

/-- Exact new shortfall numeral (honest floor report): the `1.4` need at
`cF = 1.853` exceeds complex-S4-Pythagoras `slow = 1.71` by `0.8842`
(was `1.0342`; gain `0.15`). -/
theorem CS_S4b_shortfall_1853 : (1.4 : ℝ) * 1.853 - 1.71 = 0.8842 := by
  norm_num

#print axioms CS_cpow1_sCenter_im
#print axioms CS_cpow2_sCenter_im
#print axioms CS_cpow3_sCenter_im
#print axioms CS_cpow4_sCenter_im
#print axioms CS_sin2_upper_neg099
#print axioms CS_sin3_nonneg
#print axioms CS_sin4_upper_0068
#print axioms CS_Im2_le_neg07425
#print axioms CS_Im3_nonneg
#print axioms CS_Im4_le_00408
#print axioms CS_S4C_Im_eq
#print axioms CS_complex_S4_Im_ge_07017
#print axioms CS_complex_S6_Im_ge_01517
#print axioms CS_complex_S6_abs_ge_01517
#print axioms CS_ImS6_below_Re

end Door3CellSuppliers
