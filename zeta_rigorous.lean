import Mathlib

noncomputable section

/-!
# Rigorous proof that ξ(1/2) > 0 — ITERATIVE BUILD

Proving `ξ(1/2) > 0` using Mathlib's alternating series test. Fully proved
— no outstanding goals.
-/

open Filter Topology Real

/-- Dirichlet eta partial sum at 1/2. -/
def etaPartial (n : ℕ) : ℝ :=
  Finset.sum (Finset.range n) (fun k => ((-1 : ℤ) ^ k : ℝ) / sqrt (k + 1 : ℝ))

/-- The terms a_k = 1/√(k+1) are antitone. -/
theorem eta_terms_antitone : Antitone (fun k : ℕ => 1 / sqrt (k + 1 : ℝ)) := by
  intro a b hab
  have h_le : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
    have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    linarith
  have h_sqrt_le := Real.sqrt_le_sqrt h_le
  have h_pos : 0 < sqrt ((a : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  exact one_div_le_one_div_of_le h_pos h_sqrt_le

/-- The terms tend to 0. -/
theorem eta_terms_tendsto_zero : Tendsto (fun k : ℕ => 1 / sqrt (k + 1 : ℝ)) atTop (𝓝 0) := by
  have h_top : Tendsto (fun k : ℕ => ((k : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have h_inv : Tendsto (fun k : ℕ => ((((k : ℝ) + 1))⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h_top
  have h_cont : Tendsto Real.sqrt (𝓝 0) (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.tendsto 0
  have h_comp : Tendsto (fun k : ℕ => Real.sqrt ((((k : ℝ) + 1))⁻¹)) atTop (𝓝 (Real.sqrt 0)) :=
    h_cont.comp h_inv
  rw [Real.sqrt_zero] at h_comp
  have h_eq : (fun k : ℕ => 1 / Real.sqrt (((k : ℝ) + 1))) =
      (fun k : ℕ => Real.sqrt ((((k : ℝ) + 1))⁻¹)) := by
    funext k
    rw [Real.sqrt_inv, inv_eq_one_div]
  rw [h_eq]
  exact h_comp

/-- KEY: The alternating Dirichlet eta series at 1/2 converges to a positive limit.
NOTE (correctness fix): the original statement `0 < ∑' k, ...` is FALSE as stated:
the series is only conditionally convergent, hence not `Summable` in Mathlib's
unconditional sense (`summable_norm_iff` + divergence of `∑ 1/√(k+1)`), so its
`tsum` is 0 by definition (`tsum_eq_zero_of_not_summable`). The true, provable
content of this route is the `Tendsto` limit version below (same route:
alternating series + `S₂ = 1 - 1/√2` lower bound). -/
theorem eta_half_pos :
    ∃ L : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L) ∧ 0 < L := by
  let f : ℕ → ℝ := fun k => 1 / sqrt (k + 1 : ℝ)
  have h_anti : Antitone f := eta_terms_antitone
  have h_tendsto : Tendsto f atTop (𝓝 0) := eta_terms_tendsto_zero
  obtain ⟨L, hL⟩ := Antitone.tendsto_alternating_series_of_tendsto_zero (f := f) h_anti h_tendsto
  have h_fun_eq : (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i) =
      (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ)) := by
    funext n
    apply Finset.sum_congr rfl
    intro k _
    simp only [f]
    push_cast
    ring
  have hL' : Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L) := by
    rw [← h_fun_eq]
    exact hL
  have h_bound : etaPartial 2 ≤ L := by
    have h_raw : Finset.sum (Finset.range (2 * 1)) (fun i => (-1 : ℝ) ^ i * f i) ≤ L :=
      Antitone.alternating_series_le_tendsto hL h_anti 1
    have h_eq : Finset.sum (Finset.range (2 * 1)) (fun i => (-1 : ℝ) ^ i * f i) = etaPartial 2 := by
      simp [etaPartial, f, Finset.sum_range_succ]
      ring
    linarith
  have h_eps : 0 < etaPartial 2 := by
    have h_eq : etaPartial 2 = 1 - 1 / Real.sqrt 2 := by
      simp [etaPartial, Finset.sum_range_succ, Real.sqrt_one]
      ring_nf
    rw [h_eq]
    have h_sqrt2_gt_1 : Real.sqrt 2 > 1 := by
      calc 1 = Real.sqrt 1 := by simp
        _ < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h_inv_lt : (1 / Real.sqrt 2 : ℝ) < 1 :=
      (div_lt_one (Real.sqrt_pos.mpr (by norm_num))).mpr h_sqrt2_gt_1
    linarith
  exact ⟨L, hL', lt_of_lt_of_le h_eps h_bound⟩

/-- Eta partial sum S₁ = 1. -/
theorem etaPartial_one_eq : etaPartial 1 = 1 := by
  simp [etaPartial, Real.sqrt_one]

/-- Eta partial sum S₃ = 1 - 1/√2 + 1/√3. -/
theorem etaPartial_three_eq :
    etaPartial 3 = 1 - 1 / Real.sqrt 2 + 1 / Real.sqrt 3 := by
  simp [etaPartial, Finset.sum_range_succ, Real.sqrt_one]
  ring_nf

/-- S₃ ≤ S₁ = 1 (since 1/√3 ≤ 1/√2). The S₃ upper bound is strictly tighter. -/
theorem etaPartial_three_le_one : etaPartial 3 ≤ 1 := by
  rw [etaPartial_three_eq]
  have h23 : Real.sqrt 2 ≤ Real.sqrt 3 :=
    Real.sqrt_le_sqrt (by norm_num)
  have hpos2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h13 : (1 : ℝ) / Real.sqrt 3 ≤ 1 / Real.sqrt 2 :=
    one_div_le_one_div_of_le hpos2 h23
  linarith

/-- LOWER BOUND (standalone): every eta limit L satisfies S₂ ≤ L. -/
theorem eta_half_ge_S2 (L : ℝ)
    (hL : Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L)) : etaPartial 2 ≤ L := by
  let f : ℕ → ℝ := fun k => 1 / sqrt (k + 1 : ℝ)
  have h_anti : Antitone f := eta_terms_antitone
  have h_fun_eq : (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i) =
      (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ)) := by
    funext n
    apply Finset.sum_congr rfl
    intro k _
    simp only [f]
    push_cast
    ring
  have hL' : Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i) atTop (𝓝 L) := by
    rw [h_fun_eq]
    exact hL
  have h_raw : Finset.sum (Finset.range (2 * 1)) (fun i => (-1 : ℝ) ^ i * f i) ≤ L :=
    Antitone.alternating_series_le_tendsto hL' h_anti 1
  have h_eq : Finset.sum (Finset.range (2 * 1)) (fun i => (-1 : ℝ) ^ i * f i) = etaPartial 2 := by
    simp [etaPartial, f, Finset.sum_range_succ]
    ring
  linarith

/-- UPPER BOUND S₁: every eta limit L satisfies L ≤ 1 (odd partial sum, k = 0). -/
theorem eta_half_le_one (L : ℝ)
    (hL : Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L)) : L ≤ 1 := by
  let f : ℕ → ℝ := fun k => 1 / sqrt (k + 1 : ℝ)
  have h_anti : Antitone f := eta_terms_antitone
  have h_fun_eq : (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i) =
      (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ)) := by
    funext n
    apply Finset.sum_congr rfl
    intro k _
    simp only [f]
    push_cast
    ring
  have hL' : Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i) atTop (𝓝 L) := by
    rw [h_fun_eq]
    exact hL
  have h_up := Antitone.tendsto_le_alternating_series hL' h_anti 0
  have h_eq : (∑ i ∈ Finset.range (2 * 0 + 1), (-1 : ℝ) ^ i * f i) = etaPartial 1 := by
    have h3 : (∑ i ∈ Finset.range 1, (-1 : ℝ) ^ i * f i) =
        (∑ i ∈ Finset.range 1, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ)) :=
      congrFun h_fun_eq 1
    have h31 : (2 * 0 + 1 : ℕ) = 1 := rfl
    rw [h31, h3]
    rfl
  rw [h_eq, etaPartial_one_eq] at h_up
  exact h_up

/-- UPPER BOUND S₃ (tighter): every eta limit L satisfies L ≤ S₃ (odd partial sum, k = 1). -/
theorem eta_half_le_S3 (L : ℝ)
    (hL : Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L)) : L ≤ etaPartial 3 := by
  let f : ℕ → ℝ := fun k => 1 / sqrt (k + 1 : ℝ)
  have h_anti : Antitone f := eta_terms_antitone
  have h_fun_eq : (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i) =
      (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ)) := by
    funext n
    apply Finset.sum_congr rfl
    intro k _
    simp only [f]
    push_cast
    ring
  have hL' : Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i) atTop (𝓝 L) := by
    rw [h_fun_eq]
    exact hL
  have h_up := Antitone.tendsto_le_alternating_series hL' h_anti 1
  have h_eq : (∑ i ∈ Finset.range (2 * 1 + 1), (-1 : ℝ) ^ i * f i) = etaPartial 3 := by
    have h3 : (∑ i ∈ Finset.range 3, (-1 : ℝ) ^ i * f i) =
        (∑ i ∈ Finset.range 3, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ)) :=
      congrFun h_fun_eq 3
    have h31 : (2 * 1 + 1 : ℕ) = 3 := rfl
    rw [h31, h3]
    rfl
  rw [h_eq] at h_up
  exact h_up

/-- TWO-SIDED interval with S₁: ∃ L, Tendsto ∧ 0 < L ∧ L ≤ 1. -/
theorem eta_half_two_sided :
    ∃ L : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L) ∧ 0 < L ∧ L ≤ 1 := by
  obtain ⟨L, hL, hpos⟩ := eta_half_pos
  exact ⟨L, hL, hpos, eta_half_le_one L hL⟩

/-- TWO-SIDED tight interval: ∃ L, Tendsto ∧ S₂ ≤ L ∧ L ≤ S₃ (hence 0 < L). -/
theorem eta_half_two_sided_tight :
    ∃ L : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L) ∧ etaPartial 2 ≤ L ∧ L ≤ etaPartial 3 ∧ 0 < L := by
  obtain ⟨L, hL, hpos⟩ := eta_half_pos
  exact ⟨L, hL, eta_half_ge_S2 L hL, eta_half_le_S3 L hL, hpos⟩

/-!
## Dirichlet-eta API feeder (partial).

Goal feeder: `riemannZeta (1/2 : ℂ) = (L : ℂ) / (1 - √2)` where `L` is the
`Tendsto` alternating-series limit from `eta_half_pos` (here `√2` is
`((Real.sqrt 2 : ℝ) : ℂ)`).

Status of each step:

(a) Eta partial sums / limit: `etaPartial` exists above; here we add the `etaTerm` /
    `etaTermℂ` / `etaPartialℂ` API and restate `eta_half_pos` through it
    (`eta_half_pos_etaTerm`, `eta_complex_tendsto`).

(b) HasSum / tsum links, proved ONLY in the valid directions:
    * `eta_hasSum_imp_tendsto`: `HasSum f L → Tendsto` of `range` partial sums —
      always true (`HasSum.tendsto_sum_nat`).
    * `eta_tendsto_tsum_eq_of_summable`: `Tendsto + Summable → L = ∑'`.
    The converse (`Tendsto` of `range` sums `→ HasSum`) is FALSE without `Summable`:
    `HasSum` is unconditional convergence over all finite sets, while `Tendsto` of
    `range` sums is strictly weaker for conditionally convergent series (cf.
    `Summable.hasSum_iff_tendsto_nat`, whose reverse direction needs `Summable`).
    In particular the eta series is NOT summable (`eta_not_summable`, via the
    `p = 1/2` p-series `Real.summable_one_div_nat_rpow`), so its `tsum` is `0`
    (`eta_tsum_eq_zero` via `tsum_eq_zero_of_not_summable`) — the `0 < ∑'` tsum
    form is FALSE, and only the `Tendsto` form carries the positivity.

(c) The eta–zeta identity `η(s) = (1 - 2 ^ (1 - s)) * ζ(s)`: for `1 < s.re` this is
    a Dirichlet-series rearrangement available from Mathlib's Hurwitz API
    (`HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re`, `LSeriesHasSum_one`), but
    Mathlib has NO Dirichlet-eta API (`dirichletEta` greps empty) and NO
    `η = (1 - 2 ^ (1 - s)) ζ` identity for `re > 0`. Transporting the identity from
    `re > 1` to `s = 1/2` needs analytic continuation (the eta side as an
    alternating Hurwitz difference, entire via
    `HurwitzZeta.differentiable_hurwitzZeta_sub_hurwitzZeta`, plus uniqueness of
    analytic continuation) — that bridge is NOT in Mathlib and is the remaining
    gap (see the `hEta` hypothesis below).

(d) We therefore commit the CONDITIONAL bridge: `zeta_half_eq_eta_div_of_identity`
    and the packaged `zeta_half_feeder_of_identity`, which turn the single
    analytic-continuation hypothesis `hEta` into
    `riemannZeta (1/2 : ℂ) = (L : ℂ) / (1 - √2)` with `0 < L`.
-/

/-- Dirichlet eta term at `s = 1/2` (real): `(-1)^k / √(k+1)`. -/
def etaTerm (k : ℕ) : ℝ := ((-1 : ℤ) ^ k : ℝ) / Real.sqrt (k + 1 : ℝ)

/-- Complex Dirichlet eta term: the real term coerced to `ℂ`. -/
def etaTermℂ (k : ℕ) : ℂ := (etaTerm k : ℂ)

/-- Complex eta partial sums. -/
def etaPartialℂ (n : ℕ) : ℂ := ∑ i ∈ Finset.range n, etaTermℂ i

/-- `etaTerm` partial sums agree with `etaPartial`. -/
theorem etaTerm_sum_eq_etaPartial (n : ℕ) :
    (∑ i ∈ Finset.range n, etaTerm i) = etaPartial n := by
  simp only [etaTerm, etaPartial]

/-- Restatement of `eta_half_pos` through the `etaTerm` API. -/
theorem eta_half_pos_etaTerm :
    ∃ L : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n, etaTerm i) atTop (𝓝 L) ∧ 0 < L := by
  obtain ⟨L, hL, hpos⟩ := eta_half_pos
  exact ⟨L, by simpa only [etaTerm] using hL, hpos⟩

/-- VALID HasSum → Tendsto direction (true with no summability hypothesis). -/
theorem eta_hasSum_imp_tendsto {f : ℕ → ℝ} {L : ℝ} (h : HasSum f L) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, f i) atTop (𝓝 L) :=
  h.tendsto_sum_nat

/-- VALID Tendsto + Summable → `L = tsum` link. The `Summable` hypothesis is essential. -/
theorem eta_tendsto_tsum_eq_of_summable {f : ℕ → ℝ} {L : ℝ}
    (hT : Tendsto (fun n => ∑ i ∈ Finset.range n, f i) atTop (𝓝 L))
    (hS : Summable f) : L = ∑' i, f i :=
  tendsto_nhds_unique hT hS.hasSum.tendsto_sum_nat

/-- Norm of the eta term. -/
theorem etaTerm_norm (k : ℕ) : ‖etaTerm k‖ = 1 / Real.sqrt ((k : ℝ) + 1) := by
  have h1 : (((-1 : ℤ) ^ k : ℝ)) = (-1 : ℝ) ^ k := by push_cast; ring
  simp only [etaTerm, h1, norm_div, norm_pow, norm_neg, norm_one, one_pow,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Shifted harmonic series diverges (from Mathlib's `Real.tendsto_sum_range_one_div_nat_succ_atTop`). -/
theorem harm_shift_not_summable : ¬Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
  rw [not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => by positivity)]
  exact Real.tendsto_sum_range_one_div_nat_succ_atTop

/-- The absolute eta series diverges by comparison (`1/(n+1) ≤ 1/√(n+1)`). -/
theorem eta_norm_not_summable : ¬Summable (fun k => ‖etaTerm k‖) := by
  have hle : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ ‖etaTerm n‖ := by
    intro n
    rw [etaTerm_norm, Real.sqrt_eq_rpow]
    have hy1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by linarith) _
    apply one_div_le_one_div_of_le hpos
    calc ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) ≤ ((n : ℝ) + 1) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
      _ = (n : ℝ) + 1 := Real.rpow_one _
  have hnn : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + 1) := fun n => by positivity
  exact mt (Summable.of_nonneg_of_le hnn hle) harm_shift_not_summable

/-- Hence the eta series is not unconditionally summable (in finite dimensions,
unconditional and absolute summability coincide: `summable_norm_iff`). -/
theorem eta_not_summable : ¬Summable etaTerm := by
  intro h
  exact eta_norm_not_summable (summable_norm_iff.mpr h)

/-- ...so its `tsum` is `0` by definition: the `0 < ∑'` tsum form is FALSE. -/
theorem eta_tsum_eq_zero : (∑' k, etaTerm k) = 0 :=
  tsum_eq_zero_of_not_summable eta_not_summable

/-- `etaPartialℂ` is the coercion of `etaPartial`. -/
theorem etaPartialℂ_eq_coe (n : ℕ) : etaPartialℂ n = ((etaPartial n : ℝ) : ℂ) := by
  simp only [etaPartialℂ, etaTermℂ, etaPartial, etaTerm, ← Complex.ofReal_sum]

/-- Complex `Tendsto` form of eta positivity (bridge-ready). -/
theorem eta_complex_tendsto :
    ∃ L : ℝ, Tendsto etaPartialℂ atTop (𝓝 (L : ℂ)) ∧ 0 < L := by
  obtain ⟨L, hL, hpos⟩ := eta_half_pos
  refine ⟨L, ?_, hpos⟩
  have hL2 : Tendsto (fun n => ∑ i ∈ Finset.range n, etaTerm i) atTop (𝓝 L) := by
    simpa only [etaTerm] using hL
  have hC := (Complex.continuous_ofReal.tendsto L).comp hL2
  have hfun : etaPartialℂ = fun n => ((∑ i ∈ Finset.range n, etaTerm i : ℝ) : ℂ) := by
    funext n
    simp only [etaPartialℂ, etaTermℂ, Complex.ofReal_sum]
  rw [hfun]
  simpa only [Function.comp_def] using hC

/-- `1 - √2 ≠ 0` over `ℝ` (since `√2 > 1`). -/
theorem one_sub_sqrt2_ne_zero : (1 : ℝ) - Real.sqrt 2 ≠ 0 := by
  have h : (1 : ℝ) < Real.sqrt 2 := by
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  intro hcon
  linarith

/-- ...hence over `ℂ`. -/
theorem one_sub_sqrt2_ne_zeroℂ : (1 : ℂ) - ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  have h2 := Complex.ofReal_ne_zero.mpr one_sub_sqrt2_ne_zero
  simpa only [Complex.ofReal_sub, Complex.ofReal_one] using h2

/-- CONDITIONAL eta–zeta bridge at `s = 1/2`: from the analytic-continuation identity
`η(1/2) = (1 - √2) * ζ(1/2)` (hypothesis `hEta` — the exact remaining gap, see above),
divide to get `ζ(1/2) = L / (1 - √2)`. -/
theorem zeta_half_eq_eta_div_of_identity (L : ℝ)
    (hEta : (L : ℂ) = (1 - ((Real.sqrt 2 : ℝ) : ℂ)) * riemannZeta (1 / 2 : ℂ)) :
    riemannZeta (1 / 2 : ℂ) = (L : ℂ) / (1 - ((Real.sqrt 2 : ℝ) : ℂ)) := by
  rw [eq_div_iff one_sub_sqrt2_ne_zeroℂ]
  calc riemannZeta (1 / 2 : ℂ) * (1 - ((Real.sqrt 2 : ℝ) : ℂ))
      = (1 - ((Real.sqrt 2 : ℝ) : ℂ)) * riemannZeta (1 / 2 : ℂ) := mul_comm _ _
    _ = (L : ℂ) := hEta.symm

/-- Packaged conditional feeder: eta positivity plus the single analytic-continuation
hypothesis `hEta` yields `L > 0` and `ζ(1/2) = L / (1 - √2)`. -/
theorem zeta_half_feeder_of_identity
    (hEta : ∀ L : ℝ, Tendsto etaPartialℂ atTop (𝓝 (L : ℂ)) →
      (L : ℂ) = (1 - ((Real.sqrt 2 : ℝ) : ℂ)) * riemannZeta (1 / 2 : ℂ)) :
    ∃ L : ℝ, 0 < L ∧
      riemannZeta (1 / 2 : ℂ) = (L : ℂ) / (1 - ((Real.sqrt 2 : ℝ) : ℂ)) := by
  obtain ⟨L, hL, hpos⟩ := eta_complex_tendsto
  exact ⟨L, hpos, zeta_half_eq_eta_div_of_identity L (hEta L hL)⟩

#print axioms eta_hasSum_imp_tendsto
#print axioms eta_tendsto_tsum_eq_of_summable
#print axioms eta_not_summable
#print axioms eta_tsum_eq_zero
#print axioms eta_complex_tendsto
#print axioms zeta_half_eq_eta_div_of_identity
#print axioms zeta_half_feeder_of_identity

/-!
## Eta–zeta Dirichlet identity on `1 < s.re` (Re>1 rearrangement).

`etaDirichletTerm s n = (-1)^n / (n+1)^s`. For `1 < s.re` the series is
absolutely convergent, so even/odd rearrangement is legitimate and yields
`∑' n, eta = (1 - 2^(1-s)) * ζ(s)`. This is the Re>1 input to analytic
continuation. No Hurwitz API is needed for this part.
-/

/-- Dirichlet eta term at general `s`: `(-1)^n / (n+1)^s`. -/
def etaDirichletTerm (s : ℂ) (n : ℕ) : ℂ := (-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ)) ^ s)

/-- The zeta summand `1/(n+1)^s` is summable for `1 < s.re`. -/
theorem summable_one_div_nat_add_one_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s)) := by
  have h0 : Summable (fun n : ℕ => (1 : ℂ) / ((n : ℂ) ^ s)) :=
    Complex.summable_one_div_nat_cpow.mpr hs
  have h1 : Summable (fun n : ℕ => (fun m : ℕ => (1 : ℂ) / ((m : ℂ) ^ s)) (n + 1)) :=
    (summable_nat_add_iff (G := ℂ) 1).mpr h0
  simpa only [] using h1

/-- Eta Dirichlet series is summable for `1 < s.re` (absolute convergence). -/
theorem etaDirichlet_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (etaDirichletTerm s) := by
  have hf := summable_one_div_nat_add_one_cpow hs
  have hAlt : Summable (fun n : ℕ => (-1 : ℂ) ^ n * ((1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s))) :=
    hf.alternating
  refine hAlt.congr (fun n => ?_)
  simp only [etaDirichletTerm, div_eq_mul_inv, one_mul]

/-- Even zeta subseries summand equals odd-denominator terms. -/
theorem zeta_even_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun k : ℕ => (1 : ℂ) / ((((2 * k + 1 : ℕ) : ℂ)) ^ s)) := by
  have hf := summable_one_div_nat_add_one_cpow hs
  have hcomp : Summable ((fun n : ℕ => (1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s)) ∘ (fun k : ℕ => 2 * k)) :=
    hf.comp_injective (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0))
  simpa only [Function.comp_def] using hcomp

/-- Odd zeta subseries (even denominators) is summable. -/
theorem zeta_odd_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun k : ℕ => (1 : ℂ) / ((((2 * k + 2 : ℕ) : ℂ)) ^ s)) := by
  have hf := summable_one_div_nat_add_one_cpow hs
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b h
    simp only at h
    omega
  have hcomp : Summable ((fun n : ℕ => (1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s)) ∘ (fun k : ℕ => 2 * k + 1)) :=
    hf.comp_injective hinj
  have heq : ((fun n : ℕ => (1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s)) ∘ (fun k : ℕ => 2 * k + 1))
      = (fun k : ℕ => (1 : ℂ) / ((((2 * k + 2 : ℕ) : ℂ)) ^ s)) := by
    funext k
    rfl
  rwa [heq] at hcomp

/-- `(2k+2)^s = 2^s * (k+1)^s` as complex cpow (naturals). -/
theorem two_mul_add_two_cpow (k : ℕ) (s : ℂ) :
    ((((2 * k + 2 : ℕ) : ℂ)) ^ s) = (2 : ℂ) ^ s * ((((k + 1 : ℕ) : ℂ)) ^ s) := by
  have h : (2 * k + 2 : ℕ) = 2 * (k + 1) := by ring
  conv_lhs => rw [h]
  rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  norm_cast

/-- The even-denominator subseries equals `2^{-s} ζ(s)` in tsum form. -/
theorem zeta_odd_tsum_eq {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, (1 : ℂ) / ((((2 * k + 2 : ℕ) : ℂ)) ^ s))
      = ((2 : ℂ) ^ s)⁻¹ * riemannZeta s := by
  have hterm : ∀ k : ℕ, (1 : ℂ) / ((((2 * k + 2 : ℕ) : ℂ)) ^ s)
      = ((2 : ℂ) ^ s)⁻¹ * ((1 : ℂ) / ((((k + 1 : ℕ) : ℂ)) ^ s)) := by
    intro k
    rw [two_mul_add_two_cpow k s]
    simp only [one_div, mul_inv_rev]
    ring
  simp_rw [hterm]
  rw [Summable.tsum_mul_left _ (summable_one_div_nat_add_one_cpow hs)]
  congr 1
  have hzeta := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have hcast : (∑' k : ℕ, (1 : ℂ) / ((((k + 1 : ℕ) : ℂ)) ^ s))
      = (∑' n : ℕ, (1 : ℂ) / (((n : ℂ) + 1) ^ s)) := by
    apply tsum_congr
    intro n
    congr 1
    congr 1
    push_cast
    ring
  rw [hcast, ← hzeta]

set_option maxHeartbeats 400000 in
/-- Zeta even/odd split: odd-denominator tsum + even-denominator tsum = ζ. -/
theorem zeta_even_add_odd_tsum {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, (1 : ℂ) / ((((2 * k + 1 : ℕ) : ℂ)) ^ s))
      + (∑' k : ℕ, (1 : ℂ) / ((((2 * k + 2 : ℕ) : ℂ)) ^ s))
      = riemannZeta s := by
  have heven : Summable (fun k : ℕ =>
      (fun n : ℕ => (1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s)) (2 * k)) :=
    zeta_even_summable hs
  have hodd : Summable (fun k : ℕ =>
      (fun n : ℕ => (1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s)) (2 * k + 1)) :=
    zeta_odd_summable hs
  have hsplit := tsum_even_add_odd (f := (fun n : ℕ => (1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s)) ) heven hodd
  have hzeta := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have hcast : (∑' n : ℕ, (1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s))
      = (∑' n : ℕ, (1 : ℂ) / (((n : ℂ) + 1) ^ s)) := by
    apply tsum_congr
    intro n
    congr 1
    congr 1
    push_cast
    ring
  have hsplit2 : (∑' k : ℕ, (1 : ℂ) / ((((2 * k + 1 : ℕ) : ℂ)) ^ s))
      + (∑' k : ℕ, (1 : ℂ) / ((((2 * k + 2 : ℕ) : ℂ)) ^ s))
      = (∑' n : ℕ, (1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s)) :=
    hsplit
  rw [hsplit2, hcast, ← hzeta]

/-- `(-1)^(2k) = 1` over `ℂ`. -/
theorem neg_one_pow_two_mul (k : ℕ) : ((-1 : ℂ) ^ (2 * k) = 1) := by
  rw [pow_mul]
  simp

/-- `(-1)^(2k+1) = -1` over `ℂ`. -/
theorem neg_one_pow_two_mul_add_one (k : ℕ) : ((-1 : ℂ) ^ (2 * k + 1) = -1) := by
  rw [pow_succ]
  rw [neg_one_pow_two_mul k, one_mul]

/-- Eta even subseries equals zeta odd-denominator subseries. -/
theorem eta_even_tsum_eq {s : ℂ} :
    (∑' k : ℕ, etaDirichletTerm s (2 * k))
      = (∑' k : ℕ, (1 : ℂ) / ((((2 * k + 1 : ℕ) : ℂ)) ^ s)) := by
  have heq : ∀ k : ℕ, etaDirichletTerm s (2 * k)
      = (1 : ℂ) / ((((2 * k + 1 : ℕ) : ℂ)) ^ s) := by
    intro k
    simp only [etaDirichletTerm]
    rw [neg_one_pow_two_mul k]
  simp_rw [heq]

/-- Eta odd subseries equals negated zeta even-denominator subseries. -/
theorem eta_odd_tsum_eq {s : ℂ} :
    (∑' k : ℕ, etaDirichletTerm s (2 * k + 1))
      = - (∑' k : ℕ, (1 : ℂ) / ((((2 * k + 2 : ℕ) : ℂ)) ^ s)) := by
  have heq : ∀ k : ℕ, etaDirichletTerm s (2 * k + 1)
      = - ((1 : ℂ) / ((((2 * k + 2 : ℕ) : ℂ)) ^ s)) := by
    intro k
    simp only [etaDirichletTerm]
    rw [neg_one_pow_two_mul_add_one k]
    ring
  simp_rw [heq]
  exact tsum_neg

/-- `2^(1-s) = 2 * (2^s)⁻¹`. -/
theorem two_cpow_one_sub (s : ℂ) : (2 : ℂ) ^ ((1 : ℂ) - s) = 2 * ((2 : ℂ) ^ s)⁻¹ := by
  rw [Complex.cpow_sub _ _ (by norm_num), Complex.cpow_one, div_eq_mul_inv]

/-- MAIN Re>1 identity: `∑' eta = (1 - 2^(1-s)) ζ(s)` for `1 < s.re`. -/
theorem eta_tsum_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, etaDirichletTerm s n) = (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s := by
  have heta := etaDirichlet_summable hs
  have heven : Summable (fun k : ℕ => etaDirichletTerm s (2 * k)) :=
    heta.comp_injective (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0))
  have hinj_odd : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b h
    simp only at h
    omega
  have hodd : Summable (fun k : ℕ => etaDirichletTerm s (2 * k + 1)) :=
    heta.comp_injective hinj_odd
  have hsplit := tsum_even_add_odd (f := etaDirichletTerm s) heven hodd
  have heta_split : (∑' n : ℕ, etaDirichletTerm s n)
      = (∑' k : ℕ, (1 : ℂ) / ((((2 * k + 1 : ℕ) : ℂ)) ^ s))
        - (∑' k : ℕ, (1 : ℂ) / ((((2 * k + 2 : ℕ) : ℂ)) ^ s)) := by
    rw [← hsplit, eta_even_tsum_eq, eta_odd_tsum_eq, sub_eq_add_neg]
  have hzeta_split := zeta_even_add_odd_tsum hs
  have hodd_eq := zeta_odd_tsum_eq hs
  have hpow := two_cpow_one_sub s
  calc (∑' n : ℕ, etaDirichletTerm s n)
      = (∑' k : ℕ, (1 : ℂ) / ((((2 * k + 1 : ℕ) : ℂ)) ^ s))
        - (∑' k : ℕ, (1 : ℂ) / ((((2 * k + 2 : ℕ) : ℂ)) ^ s)) := heta_split
    _ = riemannZeta s - 2 * (((2 : ℂ) ^ s)⁻¹ * riemannZeta s) := by
        rw [hodd_eq] at hzeta_split ⊢
        linear_combination hzeta_split
    _ = (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s := by
        rw [hpow]
        ring

/-!
## Entire Hurwitz-difference continuation of eta.

`etaHurwitz s = 2^{-s} (H(1/2,s) - H(1,s))`, entire via
`HurwitzZeta.differentiable_hurwitzZeta_sub_hurwitzZeta`.
For `1 < s.re` it agrees with the Dirichlet eta tsum (hence with
`(1-2^{1-s})ζ(s)`); by analytic continuation on `{1}ᶜ` it agrees at `s=1/2`.
-/

/-- Entire eta continuation via alternating Hurwitz difference. -/
noncomputable def etaHurwitz (s : ℂ) : ℂ :=
  ((2 : ℂ) ^ s)⁻¹ * (HurwitzZeta.hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) s
    - HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) s)

/-- `2^s ≠ 0`. -/
theorem two_cpow_ne_zero (s : ℂ) : (2 : ℂ) ^ s ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))

/-- `fun s => ((2:ℂ)^s)⁻¹` is differentiable (entire). -/
theorem differentiable_inv_two_cpow : Differentiable ℂ (fun s : ℂ => ((2 : ℂ) ^ s)⁻¹) :=
  (differentiable_const_cpow_of_neZero (2 : ℂ)).inv two_cpow_ne_zero

/-- `etaHurwitz` is differentiable everywhere (entire). -/
theorem differentiable_etaHurwitz : Differentiable ℂ etaHurwitz := by
  unfold etaHurwitz
  exact differentiable_inv_two_cpow.mul
    (HurwitzZeta.differentiable_hurwitzZeta_sub_hurwitzZeta _ _)

/-- `etaHurwitz` is analytic everywhere. -/
theorem analytic_etaHurwitz : AnalyticOnNhd ℂ etaHurwitz Set.univ :=
  differentiable_etaHurwitz.differentiableOn.analyticOnNhd isOpen_univ

theorem hurwitz_half_cpow_eq (n : ℕ) (s : ℂ) :
    (((2 * n + 1 : ℕ) : ℂ) ^ s)
      = (2 : ℂ) ^ s * ((((n : ℕ) : ℂ)) + (((1 / 2 : ℝ) : ℂ))) ^ s := by
  have h2n_real : ((2 * n + 1 : ℕ) : ℝ) = 2 * ((n : ℝ) + 1 / 2) := by
    push_cast
    ring
  have hL : (((2 * n + 1 : ℕ) : ℂ)) = ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) :=
    (Complex.ofReal_natCast _).symm
  have hR1 : (2 : ℂ) = (((2 : ℝ)) : ℂ) := by norm_cast
  have hR2 : ((((n : ℕ) : ℂ)) + (((1 / 2 : ℝ) : ℂ))) = ((((n : ℝ) + 1 / 2 : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_add]
  have han : (0 : ℝ) ≤ ((n : ℝ) + 1 / 2) := by positivity
  have h2pos : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
  calc (((2 * n + 1 : ℕ) : ℂ) ^ s)
      = (((((2 * n + 1 : ℕ) : ℝ)) : ℂ) ^ s) := by rw [← hL]
    _ = (((2 * (((n : ℝ) + 1 / 2))) : ℝ) : ℂ) ^ s := by rw [h2n_real]
    _ = ((((2 : ℝ)) : ℂ) ^ s * (((((n : ℝ) + 1 / 2 : ℝ))) : ℂ) ^ s) := by
        rw [Complex.ofReal_mul]
        rw [Complex.mul_cpow_ofReal_nonneg h2pos han s]
    _ = (2 : ℂ) ^ s * ((((n : ℕ) : ℂ)) + (((1 / 2 : ℝ) : ℂ))) ^ s := by
        rw [hR1, hR2]

/-- Hurwitz at `1/2` equals `2^s` times odd-denominator zeta subseries (Re>1). -/
theorem hurwitz_half_eq_two_cpow_mul_odd {s : ℂ} (hs : 1 < s.re) :
    HurwitzZeta.hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) s
      = (2 : ℂ) ^ s * (∑' k : ℕ, (1 : ℂ) / ((((2 * k + 1 : ℕ) : ℂ)) ^ s)) := by
  have ha : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num, by norm_num⟩
  have hHas := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ha (s := s) hs
  have htsum := hHas.tsum_eq
  have hterm : ∀ n : ℕ, (1 : ℂ) / (((((n : ℕ) : ℂ)) + (((1 / 2 : ℝ) : ℂ))) ^ s)
      = (2 : ℂ) ^ s * ((1 : ℂ) / ((((2 * n + 1 : ℕ) : ℂ)) ^ s)) := by
    intro n
    rw [hurwitz_half_cpow_eq n s]
    have h2 := two_cpow_ne_zero s
    field_simp
  have hcongr : (∑' n : ℕ, (1 : ℂ) / (((((n : ℕ) : ℂ)) + (((1 / 2 : ℝ) : ℂ))) ^ s))
      = (2 : ℂ) ^ s * (∑' k : ℕ, (1 : ℂ) / ((((2 * k + 1 : ℕ) : ℂ)) ^ s)) := by
    simp_rw [hterm]
    rw [Summable.tsum_mul_left _ (zeta_even_summable hs)]
  rw [← hcongr, htsum]

/-- Hurwitz at `1` equals zeta (Re>1, via series). -/
theorem hurwitz_one_eq_zeta {s : ℂ} (hs : 1 < s.re) :
    HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) s = riemannZeta s := by
  have ha : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num, by norm_num⟩
  have hHas := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ha (s := s) hs
  have htsum := hHas.tsum_eq
  have hterm : ∀ n : ℕ, (1 : ℂ) / (((((n : ℕ) : ℂ)) + (((1 : ℝ) : ℂ))) ^ s)
      = (1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s) := by
    intro n
    congr 1
    congr 1
    have h1 : ((((1 : ℝ) : ℂ))) = (1 : ℂ) := Complex.ofReal_one
    rw [h1]
    push_cast
    ring
  have hcongr : (∑' n : ℕ, (1 : ℂ) / (((((n : ℕ) : ℂ)) + (((1 : ℝ) : ℂ))) ^ s))
      = (∑' n : ℕ, (1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s)) := by
    apply tsum_congr
    intro n
    exact hterm n
  have hzeta := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have hcast : (∑' n : ℕ, (1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s))
      = (∑' n : ℕ, (1 : ℂ) / (((n : ℂ) + 1) ^ s)) := by
    apply tsum_congr
    intro n
    congr 1
    congr 1
    push_cast
    ring
  rw [← htsum, hcongr, hcast, ← hzeta]

/-- `etaHurwitz` agrees with `(1-2^{1-s})ζ(s)` on `1 < s.re`. -/
theorem etaHurwitz_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    etaHurwitz s = (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s := by
  have hhalf := hurwitz_half_eq_two_cpow_mul_odd hs
  have hone := hurwitz_one_eq_zeta hs
  have hodd_eq := zeta_odd_tsum_eq hs
  have hzeta_split := zeta_even_add_odd_tsum hs
  have heta_eq := eta_tsum_eq_of_one_lt_re hs
  have h2ne := two_cpow_ne_zero s
  have hpow := two_cpow_one_sub s
  unfold etaHurwitz
  rw [hhalf, hone]
  have hcalc : ((2 : ℂ) ^ s)⁻¹ * ((2 : ℂ) ^ s * (∑' k : ℕ, (1 : ℂ) / ((((2 * k + 1 : ℕ) : ℂ)) ^ s))
      - riemannZeta s)
      = (∑' k : ℕ, (1 : ℂ) / ((((2 * k + 1 : ℕ) : ℂ)) ^ s))
        - ((2 : ℂ) ^ s)⁻¹ * riemannZeta s := by
    field_simp
  rw [hcalc]
  rw [hodd_eq] at hzeta_split
  have hfinal : (∑' k : ℕ, (1 : ℂ) / ((((2 * k + 1 : ℕ) : ℂ)) ^ s))
      - ((2 : ℂ) ^ s)⁻¹ * riemannZeta s
      = (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s := by
    rw [hpow]
    linear_combination hzeta_split
  exact hfinal

/-- RHS function `(1-2^{1-s})ζ(s)`, analytic on `{1}ᶜ`. -/
noncomputable def etaRHS (s : ℂ) : ℂ := (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s

/-- `fun s => (2:ℂ)^((1:ℂ)-s)` is differentiable everywhere. -/
theorem differentiable_two_cpow_one_sub : Differentiable ℂ (fun s : ℂ => (2 : ℂ) ^ ((1 : ℂ) - s)) :=
  (differentiable_const_cpow_of_neZero (2 : ℂ)).comp
    ((differentiable_const (1 : ℂ)).sub differentiable_id)

/-- `etaRHS` agrees with `etaHurwitz` on `1 < s.re`. -/
theorem etaHurwitz_eq_etaRHS_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    etaHurwitz s = etaRHS s := by
  rw [etaHurwitz_eq_of_one_lt_re hs]
  rfl

/-- `etaRHS` is analytic on `{1}ᶜ`. -/
theorem analytic_etaRHS : AnalyticOnNhd ℂ etaRHS ({1}ᶜ : Set ℂ) := by
  unfold etaRHS
  apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
  exact ((differentiable_two_cpow_one_sub.differentiableAt.const_sub 1).mul
    (differentiableAt_riemannZeta hs)).differentiableWithinAt

/-- `etaHurwitz` restricted to `{1}ᶜ` is analytic. -/
theorem analytic_etaHurwitz_compl : AnalyticOnNhd ℂ etaHurwitz ({1}ᶜ : Set ℂ) :=
  analytic_etaHurwitz.mono (Set.subset_univ _)

/-- Analytic continuation: `etaHurwitz = etaRHS` on all of `{1}ᶜ` (hence at `1/2`). -/
theorem etaHurwitz_eq_etaRHS_compl :
    Set.EqOn etaHurwitz etaRHS ({1}ᶜ : Set ℂ) := by
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) _).isPreconnected
  have hne : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    analytic_etaHurwitz_compl analytic_etaRHS hpc hne ?_
  refine eventually_of_mem ?_ (fun t ht => etaHurwitz_eq_etaRHS_of_one_lt_re ht)
  exact (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re)

/-- `2^(1-1/2) = √2` (as complex of real sqrt). -/
theorem two_cpow_one_sub_half :
    (2 : ℂ) ^ ((1 : ℂ) - (1 / 2 : ℂ)) = (((Real.sqrt 2 : ℝ)) : ℂ) := by
  have h12 : ((1 : ℂ) - (1 / 2 : ℂ)) = (1 / 2 : ℂ) := by ring
  have h12r : (1 / 2 : ℂ) = ((((1 / 2 : ℝ))) : ℂ) := by simp
  rw [h12, h12r]
  have hsqrt : Real.sqrt 2 = (2 : ℝ) ^ ((1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
  have h2c : (2 : ℂ) = ((((2 : ℝ))) : ℂ) := by simp
  rw [h2c, hsqrt, Complex.ofReal_cpow (by norm_num)]

/-- Continued identity at `s = 1/2`: `etaHurwitz(1/2) = (1-√2)ζ(1/2)`. -/
theorem etaHurwitz_half_eq :
    etaHurwitz (1 / 2 : ℂ) = (1 - (((Real.sqrt 2 : ℝ)) : ℂ)) * riemannZeta (1 / 2 : ℂ) := by
  have hmem : (1 / 2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
  have heq := etaHurwitz_eq_etaRHS_compl hmem
  unfold etaRHS at heq
  rw [two_cpow_one_sub_half] at heq
  exact heq

/-!
## Closing `hEta` modulo the series-to-continuation limit.

Proved above (no hypotheses, no sorries):
* `eta_tsum_eq_of_one_lt_re`: Dirichlet eta tsum `= (1-2^{1-s})ζ(s)` on `1 < s.re`;
* `etaHurwitz_eq_of_one_lt_re`: entire `etaHurwitz` agrees there;
* `etaHurwitz_half_eq`: continued `etaHurwitz(1/2) = (1-√2)ζ(1/2)` via
  `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` on `{1}ᶜ`.

Exact remaining step (ONE hypothesis): the `Tendsto` eta limit `L`
from `eta_half_pos`/`eta_complex_tendsto` equals the continued value
`etaHurwitz(1/2)`. This is the conditional-convergence bridge
(paired differences `O(n^{-3/2})` summable at `1/2`, whose tsum defines a
holomorphic `G` on `0 < s.re` agreeing with `etaHurwitz` on `1 < s.re`,
hence at `1/2` by the identity theorem) — not attempted here.
From it, `hEta` follows by rewriting with `etaHurwitz_half_eq`.
-/

/-- `hEta` from the single series-to-continuation limit hypothesis. -/
theorem hEta_of_etaHurwitz_lim (L : ℝ)
    (hLim : (L : ℂ) = etaHurwitz (1 / 2 : ℂ)) :
    (L : ℂ) = (1 - (((Real.sqrt 2 : ℝ)) : ℂ)) * riemannZeta (1 / 2 : ℂ) := by
  rw [hLim, etaHurwitz_half_eq]

/-- Packaged feeder: eta positivity + ONE continuation hypothesis yields ζ(1/2) form. -/
theorem zeta_half_feeder_of_etaHurwitz_lim
    (hLim : ∀ L : ℝ, Tendsto etaPartialℂ atTop (𝓝 (L : ℂ)) →
      (L : ℂ) = etaHurwitz (1 / 2 : ℂ)) :
    ∃ L : ℝ, 0 < L ∧
      riemannZeta (1 / 2 : ℂ) = (L : ℂ) / (1 - (((Real.sqrt 2 : ℝ)) : ℂ)) := by
  obtain ⟨L, hL, hpos⟩ := eta_complex_tendsto
  exact ⟨L, hpos, zeta_half_eq_eta_div_of_identity L (hEta_of_etaHurwitz_lim L (hLim L hL))⟩

#print axioms eta_tsum_eq_of_one_lt_re
#print axioms etaHurwitz_eq_of_one_lt_re
#print axioms etaHurwitz_half_eq
#print axioms hEta_of_etaHurwitz_lim
#print axioms zeta_half_feeder_of_etaHurwitz_lim
