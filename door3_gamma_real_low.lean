import Mathlib

/-!
# Real `Gamma` lower on `Icc 1 2.1` (REALGAM-LOW input for `door3_gamma_disc.lean`).

Blocker fed: `door3_gamma_disc.lean:602-617` — the 30 per-center CONDITIONAL lowers
(`R28_cond`, `R35_cond`, `R38_cond`, `R29_cond`, `E10/R31/R40/R21/R30/R39/E09/
R32/R22/E01/R33/E08/R23/BA03/R37/R27/R34/R24/E07/BA04/R36/R26/E06/R25/E05/
BA00_cond`) discharge floors `F` from a numerator lower `c` via `c / M`
(single-step) or `c / (M0 * M1)` (two-step) with banked denominator uppers.
Target shape was `∀ x ∈ Icc 1 2.1, (0.88 : ℝ) ≤ Real.Gamma x`
(true minimum ≈ 0.8856 at x ≈ 1.4616).

## Recon (read-only, Mathlib banked real-Gamma API)
* Values: `Real.Gamma_one`, `Real.Gamma_two`, `Real.Gamma_add_one`,
  `Real.Gamma_one_half_eq` (`Γ(1/2) = √π`), `Real.Gamma_pos_of_pos`.
* Convexity: `Real.convexOn_Gamma`, `Real.convexOn_log_Gamma`
  (`Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean`).
* Monotonicity: `Real.Gamma_strictMonoOn_Ici` (on `Ici 2`),
  `Real.Gamma_strictAntiOn_Ioc`, `Real.Gamma_three_div_two_lt_one`.
* Bounds on π: `Real.pi_gt_d2` (`3.14 < π`), `Real.pi_gt_d4`.
* Digamma numerals: only `hasDerivAt_Gamma_one`-type values at `1`, `1/2`
  (`Mathlib/NumberTheory/Harmonic/GammaDeriv.lean`); NO value near the
  minimizer ≈ 1.4616. No Gautschi/Wendel/Kershaw inequality banked.

## Routes tried (instructed order (c) → (a) → (e) → (d))
* (c) Recurrence + split at 1.5: `Γ(1) = Γ(2) = 1`, `Γ(1.5) = √π/2 ≥ 0.886`
  (closed below as `gamma_three_half_lower`). Interior monotonicity on
  `[1,1.5]`/`[1.5,2]` needs digamma sign — unbanked. Recurrence-backward
  sub-lane noted: `Γ(x) = Γ(x+1)/x ≥ 1/x` on `[1, 1.14]` reaches `≥ 0.88`
  pointwise, but does not lift the uniform constant. Route (c) alone cannot
  close uniform `0.88`.
* (a) Tangent-lower from `convexOn_Gamma`: needs `Γ'` at an interior point —
  unbanked digamma numeral. Abandoned (would need ≥ 2 new supporting
  developments: digamma evaluation + tangent inequality).
* (e) Sharp named inequality: none banked. Abandoned.
* (d) Integral-definition lower: mass near `t ≈ 1` forces full interval
  arithmetic; crude boxes give `≤ 0.26`. Abandoned (needs > 6 lemmas).
* (c′) Exterior-secant lower from convexity (CLOSED, used here): for
  `x ∈ [1, 3/2]`, `3/2` is a convex combination of `x` and `2`, so
  convexity with `Γ(3/2) ≥ 0.886`, `Γ(2) = 1` forces
  `Γ(x) ≥ 2·0.886 − 1 = 0.772` (mirror on `[3/2, 2]`); `[2, 2.1]` uses
  banked `Gamma_strictMonoOn_Ici` (`Γ ≥ Γ(2) = 1`). Uniform constant
  **0.77** with 5 supporting lemmas (within the 6-lemma cap).
  Log-convex variant would give `0.886^2 = 0.78499…` (constant `0.78`);
  not pursued: still below the `0.80` bar for +complexity. Bohr–Mollerup
  finite-`n` (`ge_logGammaSeq`, `n = 1`) gives only `1/6`.

## Closed constant
`gamma_low_77`: `∀ x ∈ Icc 1 2.1, (0.77 : ℝ) ≤ Real.Gamma x`.
Target `0.88` is NOT closed (true min 0.8856 leaves 0.0056 margin; banked
API + 6-lemma cap tops out at the secant `2m − 1 ≈ 0.772` / log-secant
`m^2 ≈ 0.785` with `m = Γ(1.5)`).

## Survival table at achieved `c = 0.77`
Required numerator threshold `t = F` (floor) `× M` (denominator product)
per `door3_gamma_disc.lean` conditionals and `door3_gamma_low.lean` floors.
Centers with `t ≤ 0.77` are feedable (modulo a future sound real→complex
bridge at the shifted point plus shifted-`TRUE` headroom); `t > 0.77` stay
open. All shifted `Re` lie in `[1, 2.1]` (single-step `[1.05, 1.2]`;
two-step `2.0525`/`2.1`), hence inside the proved interval.
* Two-step: R28 `0.026×10.8389 = 0.28182` FEEDABLE; R38 `0.024×10.8389
  = 0.26014` FEEDABLE; R29 `0.0045×18.4989 = 0.08325` FEEDABLE;
  R35 `2×0.9164 = 1.8328` OPEN.
* Single-step: E10/BA00 `0.00687`, R31/R40/R21/R30 `0.00458`, R39
  `0.01532`, E09 `0.017235`, R32/R22 `0.02148`, E01 `0.0333`, R33/R23
  `0.08256`, E08 `0.0566`, BA03 `0.0387`, R37/R27 `0.2196`, R34/R24
  `0.316`, E07 `0.183`, BA04 `0.1264` — all 20 FEEDABLE;
  R36/R26/E06 `0.83` OPEN; E05 `0.87` OPEN; R25 `1.16` OPEN.
* Totals at `0.77`: 24 feedable, 6 open (R35, R25, E05, R36, R26, E06).
  At the full `0.88` target, E05 (`0.87`) and R36/R26/E06 (`0.83`) would
  additionally become feedable; R35 (`1.8328`) and R25 (`1.16`) stay open
  regardless (re-tier lane).

## Remainder / precise residual
Missing Mathlib lemma blocking `0.88`: an interior digamma numeral
(`Γ'(a)` or sign of `ψ` on `[1, 2]`, e.g. at the minimizer) or a banked
Gautschi-type two-sided bound; alternatively a verified quadrature of the
`Γ`-integral to `±0.005`. Next upgrade path inside this file's technique:
log-convex exterior secant (`m^2`, constant `0.78`) — all inputs banked.
-/

noncomputable section

namespace Door3GammaRealLow

/-- Lower bound `1.772 ≤ √π` from `1.772 ^ 2 = 3.139984 ≤ 3.14 < π`. -/
theorem sqrt_pi_lower : (1.772 : ℝ) ≤ Real.sqrt Real.pi := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hsq : (1.772 : ℝ) ^ 2 ≤ Real.pi := by
    have h1 : (1.772 : ℝ) ^ 2 ≤ 3.14 := by norm_num
    linarith
  exact (Real.le_sqrt' (by norm_num : (0 : ℝ) < 1.772)).mpr hsq

/-- Anchor: `0.886 ≤ Γ(3/2)` via `Γ(1/2 + 1) = (1/2) * Γ(1/2) = √π / 2`. -/
theorem gamma_three_half_lower : (0.886 : ℝ) ≤ Real.Gamma (3 / 2) := by
  have h32 : (3 / 2 : ℝ) = 1 / 2 + 1 := by norm_num
  rw [h32, Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0),
    Real.Gamma_one_half_eq]
  have hs := sqrt_pi_lower
  linarith

/-- Left secant lane: `x ∈ [1, 3/2]` gives `0.77 ≤ Γ(x)`.
`3/2` is the convex combination `a * x + b * 2` with
`a = (1/2)/(2-x)`, `b = ((3/2)-x)/(2-x)`; convexity at `(x, 2)` with
`Γ(3/2) ≥ 0.886`, `Γ(2) = 1` forces `Γ(x) ≥ 2 * 0.886 - 1 ≥ 0.77`. -/
theorem gamma_lower_left (x : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 3 / 2) :
    (0.77 : ℝ) ≤ Real.Gamma x := by
  have h2x : (0 : ℝ) < 2 - x := by linarith
  have h2xne : (2 : ℝ) - x ≠ 0 := ne_of_gt h2x
  set a : ℝ := (1 / 2) / (2 - x) with ha_def
  set b : ℝ := ((3 / 2) - x) / (2 - x) with hb_def
  have ha0 : 0 ≤ a := by
    rw [ha_def]
    exact div_nonneg (by norm_num) h2x.le
  have hb0 : 0 ≤ b := by
    rw [hb_def]
    exact div_nonneg (by linarith) h2x.le
  have hab : a + b = 1 := by
    rw [ha_def, hb_def]
    field_simp
    ring
  have hcombo : a * x + b * 2 = 3 / 2 := by
    rw [ha_def, hb_def]
    field_simp
    ring
  have hmem_x : x ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have hmem_2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have hconv := Real.convexOn_Gamma.2 hmem_x hmem_2 ha0 hb0 hab
  simp only [smul_eq_mul] at hconv
  rw [hcombo, Real.Gamma_two] at hconv
  have hm := gamma_three_half_lower
  have ha2 : a * (2 - x) = 1 / 2 := by
    rw [ha_def]
    exact div_mul_cancel₀ _ h2xne
  have hb2 : b * (2 - x) = (3 / 2) - x := by
    rw [hb_def]
    exact div_mul_cancel₀ _ h2xne
  have hkey : (0.77 : ℝ) / 2 + ((3 / 2) - x) ≤ 0.886 * (2 - x) := by
    linarith
  have hmul : ((0.77 : ℝ) * a + b) * (2 - x) ≤ 0.886 * (2 - x) := by
    have e : ((0.77 : ℝ) * a + b) * (2 - x) = 0.77 / 2 + ((3 / 2) - x) := by
      linear_combination 0.77 * ha2 + hb2
    rw [e]
    exact hkey
  have hleo : (0.77 : ℝ) * a + b ≤ 0.886 := (mul_le_mul_right h2x).mp hmul
  have hage : (0.77 : ℝ) * a ≤ a * Real.Gamma x := by linarith [hconv, hm]
  have hapos : (0 : ℝ) < a := by
    rw [ha_def]
    exact div_pos (by norm_num) h2x
  have h3 : a * 0.77 ≤ a * Real.Gamma x := by
    rw [mul_comm a (0.77 : ℝ)]
    exact hage
  exact (mul_le_mul_left hapos).mp h3

/-- Right secant lane: `x ∈ [3/2, 2]` gives `0.77 ≤ Γ(x)`.
Mirror image: `3/2 = t * 1 + u * x` with `t = (x-(3/2))/(x-1)`,
`u = (1/2)/(x-1)`; convexity at `(1, x)` with `Γ(1) = 1`,
`Γ(3/2) ≥ 0.886` forces the symmetric bound. -/
theorem gamma_lower_right (x : ℝ) (hx1 : 3 / 2 ≤ x) (hx2 : x ≤ 2) :
    (0.77 : ℝ) ≤ Real.Gamma x := by
  have h1x : (0 : ℝ) < x - 1 := by linarith
  have h1xne : (x : ℝ) - 1 ≠ 0 := ne_of_gt h1x
  set t : ℝ := (x - (3 / 2)) / (x - 1) with ht_def
  set u : ℝ := (1 / 2) / (x - 1) with hu_def
  have ht0 : 0 ≤ t := by
    rw [ht_def]
    exact div_nonneg (by linarith) h1x.le
  have hu0 : 0 ≤ u := by
    rw [hu_def]
    exact div_nonneg (by norm_num) h1x.le
  have htu : t + u = 1 := by
    rw [ht_def, hu_def]
    field_simp
    ring
  have hcombo : t * 1 + u * x = 3 / 2 := by
    rw [ht_def, hu_def]
    field_simp
    ring
  have hmem_1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have hmem_x : x ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have hconv := Real.convexOn_Gamma.2 hmem_1 hmem_x ht0 hu0 htu
  simp only [smul_eq_mul] at hconv
  rw [hcombo, Real.Gamma_one] at hconv
  have hm := gamma_three_half_lower
  have ht2 : t * (x - 1) = x - (3 / 2) := by
    rw [ht_def]
    exact div_mul_cancel₀ _ h1xne
  have hu2 : u * (x - 1) = 1 / 2 := by
    rw [hu_def]
    exact div_mul_cancel₀ _ h1xne
  have hkey : (0.77 : ℝ) / 2 + (x - (3 / 2)) ≤ 0.886 * (x - 1) := by
    linarith
  have hmul : ((0.77 : ℝ) * u + t) * (x - 1) ≤ 0.886 * (x - 1) := by
    have e : ((0.77 : ℝ) * u + t) * (x - 1) = 0.77 / 2 + (x - (3 / 2)) := by
      linear_combination 0.77 * hu2 + ht2
    rw [e]
    exact hkey
  have hleo : (0.77 : ℝ) * u + t ≤ 0.886 := (mul_le_mul_right h1x).mp hmul
  have huge : (0.77 : ℝ) * u ≤ u * Real.Gamma x := by linarith [hconv, hm]
  have hupos : (0 : ℝ) < u := by
    rw [hu_def]
    exact div_pos (by norm_num) h1x
  have h3 : u * 0.77 ≤ u * Real.Gamma x := by
    rw [mul_comm u (0.77 : ℝ)]
    exact huge
  exact (mul_le_mul_left hupos).mp h3

/-- Top lane: `x ≥ 2` gives `0.77 ≤ Γ(x)` from banked eventual monotonicity
(`Γ ≥ Γ(2) = 1` on `Ici 2`). -/
theorem gamma_lower_top (x : ℝ) (hx1 : 2 ≤ x) :
    (0.77 : ℝ) ≤ Real.Gamma x := by
  have hmono := Real.Gamma_strictMonoOn_Ici.monotoneOn
  have h2 : Real.Gamma 2 ≤ Real.Gamma x :=
    hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx1) hx1
  rw [Real.Gamma_two] at h2
  linarith

/-- Main input: uniform `0.77` lower for real `Gamma` on `[1, 2.1]`. -/
theorem gamma_low_77 (x : ℝ) (hx : x ∈ Set.Icc (1 : ℝ) 2.1) :
    (0.77 : ℝ) ≤ Real.Gamma x := by
  rw [Set.mem_Icc] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rcases le_total x (3 / 2) with hleft | hright
  · exact gamma_lower_left x hx1 hleft
  · rcases le_total x 2 with hmid | htop
    · exact gamma_lower_right x hright hmid
    · exact gamma_lower_top x htop

end Door3GammaRealLow
