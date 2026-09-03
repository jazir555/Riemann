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

/-!
## `hLim`: the Tendsto limit equals the continued Hurwitz value at `s = 1/2`.

Mathlib greps used (all pre-existing, only called):
* uniqueness of limits: `tendsto_nhds_unique`
  (`Mathlib/Topology/Separation/Hausdorff.lean`);
* Weierstrass M-test: `Summable.of_norm_bounded`
  (`Mathlib/Analysis/Normed/Group/InfiniteSum.lean`);
* Hurwitz API: `HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re`,
  `HurwitzZeta.differentiable_hurwitzZeta_sub_hurwitzZeta`
  (`Mathlib/NumberTheory/LSeries/HurwitzZeta.lean`);
* tsum holomorphicity: `Complex.differentiableOn_tsum_of_summable_norm`
  (`Mathlib/Analysis/Complex/LocallyUniformLimit.lean`);
* identity theorem: `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`
  (`Mathlib/Analysis/Analytic/Uniqueness.lean`).

Route (the `R00EtaConv` paired-difference pattern from `interval_arith.lean`,
generalized from `sR00` to general `s` with `0 < s.re`, closed via the
continuation framework above in this file):
1. `etaPairTerm s m`: paired increment; MVT gives
   `‖pair‖ ≤ ‖s‖ * (2m+1)^{-Re s - 1}` (`norm_etaPairTerm_le`);
2. M-test gives `Summable (etaPairTerm s)` for `0 < s.re`
   (`summable_etaPairTerm`);
3. even partial sums `S_{2M}(s)` are sums of pairs
   (`etaDirichlet_even_partial`), hence tend to `∑' m, etaPairTerm s m`
   (`etaDirichlet_even_tendsto_pair`);
4. on `1 < s.re` the same even partials tend to `∑' etaDirichletTerm s`,
   so `∑' pairs = etaHurwitz` there (`etaPairLim_eq_of_one_lt_re`);
5. `G(s) = ∑' pairs` is analytic on the ball `B = ball 1 (3/4)`
   (uniform majorant `(7/4) * (m+1)^{-5/4}`); `B` is preconnected,
   contains `1/2` and `3/2`, and `G = etaHurwitz` near `3/2` — hence
   `G = etaHurwitz` on `B`, in particular at `1/2`;
6. at `s = 1/2`, `etaDirichletTerm = etaTermℂ` termwise, so the even
   partials tend to both `(L:ℂ)` (from `hL`) and `etaHurwitz (1/2)`;
   `tendsto_nhds_unique` closes.
-/

/-- Paired Dirichlet-eta increment at general `s`: `S_{2(m+1)} - S_{2m}`. -/
noncomputable def etaPairTerm (s : ℂ) (m : ℕ) : ℂ :=
  etaDirichletTerm s (2 * m) + etaDirichletTerm s (2 * m + 1)

/-- Dirichlet eta term in cpow-neg form. -/
theorem etaDirichletTerm_eq_cpow_neg (s : ℂ) (n : ℕ) :
    etaDirichletTerm s n = (-1 : ℂ) ^ n * (((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s)) := by
  have hcast : ((((n + 1 : ℕ) : ℂ))) = (((((n : ℝ) + 1 : ℝ))) : ℂ) := by
    push_cast
    ring
  simp only [etaDirichletTerm, div_eq_mul_inv, ← Complex.cpow_neg]
  rw [hcast]

/-- Pair in cpow-difference form. -/
theorem etaPairTerm_eq_cpow_sub (s : ℂ) (m : ℕ) :
    etaPairTerm s m
      = (((((2 * m + 1 : ℕ) : ℝ)) : ℂ) ^ (-s))
        - (((((2 * m + 2 : ℕ) : ℝ)) : ℂ) ^ (-s)) := by
  have e0 := etaDirichletTerm_eq_cpow_neg s (2 * m)
  have e1 := etaDirichletTerm_eq_cpow_neg s (2 * m + 1)
  have hcast0 : ((((2 * m : ℕ) : ℝ) + 1 : ℝ)) = ((((2 * m + 1 : ℕ) : ℝ))) := by
    push_cast
    ring
  have hcast1 : ((((2 * m + 1 : ℕ) : ℝ) + 1 : ℝ)) = ((((2 * m + 2 : ℕ) : ℝ))) := by
    push_cast
    ring
  show etaDirichletTerm s (2 * m) + etaDirichletTerm s (2 * m + 1) = _
  rw [e0, e1, neg_one_pow_two_mul, neg_one_pow_two_mul_add_one, hcast0, hcast1]
  ring

/-- Mean-value pair bound `‖pair m‖ ≤ ‖s‖ * (2m+1)^{-Re s - 1}` (`0 < Re s`). -/
theorem norm_etaPairTerm_le (s : ℂ) (hs : 0 < s.re) (m : ℕ) :
    ‖etaPairTerm s m‖ ≤ ‖s‖ * (((((2 * m + 1 : ℕ) : ℝ)) ^ (-s.re - 1))) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    exact lt_irrefl _ hs
  have hnegs : -s ≠ 0 := neg_ne_zero.mpr hs0
  set a : ℝ := (((2 * m + 1 : ℕ) : ℝ)) with ha
  set b : ℝ := (((2 * m + 2 : ℕ) : ℝ)) with hb
  have ha_pos : (0 : ℝ) < a := by
    rw [ha]
    exact Nat.cast_pos.mpr (by omega)
  have hab : a ≤ b := by
    rw [ha, hb]
    exact Nat.cast_le.mpr (by omega)
  have hb_eq : b = a + 1 := by
    rw [ha, hb]
    have heq : 2 * m + 1 + 1 = 2 * m + 2 := by omega
    calc ((((2 * m + 2 : ℕ)) : ℝ))
        = ((((2 * m + 1 + 1 : ℕ)) : ℝ)) := by rw [heq]
      _ = ((((2 * m + 1 : ℕ)) : ℝ)) + 1 := by rw [Nat.cast_add, Nat.cast_one]
  have hpair : etaPairTerm s m = (a : ℂ) ^ (-s) - (b : ℂ) ^ (-s) := by
    rw [etaPairTerm_eq_cpow_sub]
  have hdiff : ∀ x ∈ Set.Icc a b,
      DifferentiableAt ℝ (fun t : ℝ => (t : ℂ) ^ (-s)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha_pos (Set.mem_Icc.mp hx).1
    exact (hasDerivAt_ofReal_cpow_const (ne_of_gt hx0) hnegs).differentiableAt
  have hderiv_eq : ∀ x : ℝ, x ≠ 0 →
      deriv (fun t : ℝ => (t : ℂ) ^ (-s)) x = (-s) * (x : ℂ) ^ (-s - 1) := by
    intro x hx0
    have h := Complex.deriv_ofReal_cpow_const hx0 (c := -s) hnegs
    simpa using h
  have hexp_nonpos : -s.re - 1 ≤ 0 := by linarith
  have hbound : ∀ x ∈ Set.Icc a b, ‖deriv (fun t : ℝ => (t : ℂ) ^ (-s)) x‖
      ≤ ‖s‖ * (a ^ (-s.re - 1)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha_pos (Set.mem_Icc.mp hx).1
    have hax : a ≤ x := (Set.mem_Icc.mp hx).1
    rw [hderiv_eq x (ne_of_gt hx0)]
    have hnorm_cpow : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ ((-s - 1).re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos hx0 _
    have hre : ((-s - 1).re) = -s.re - 1 := by
      rw [Complex.sub_re, Complex.neg_re, Complex.one_re]
    have hle : x ^ (-s.re - 1) ≤ a ^ (-s.re - 1) :=
      Real.rpow_le_rpow_of_nonpos ha_pos hax hexp_nonpos
    calc ‖-s * (x : ℂ) ^ (-s - 1)‖
        = ‖s‖ * (x ^ (-s.re - 1)) := by
          rw [norm_mul, norm_neg, hnorm_cpow, hre]
      _ ≤ ‖s‖ * (a ^ (-s.re - 1)) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_Icc a b) (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  have hba : ‖b - a‖ = 1 := by
    have hsub : b - a = 1 := by rw [hb_eq]; ring
    rw [hsub, norm_one]
  rw [hba, mul_one] at hmvt
  have hrev : ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖
      = ‖(b : ℂ) ^ (-s) - (a : ℂ) ^ (-s)‖ := norm_sub_rev _ _
  rw [hpair, hrev]
  simpa only [] using hmvt

/-- The paired series is summable for `0 < s.re` (M-test vs `p = Re+1 > 1`). -/
theorem summable_etaPairTerm {s : ℂ} (hs : 0 < s.re) :
    Summable (etaPairTerm s) := by
  have hp1 : (1 : ℝ) < s.re + 1 := by linarith
  have hbase : Summable (fun n : ℕ => ((((n : ℝ)) ^ (s.re + 1)))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hp1
  have hshift : Summable (fun m : ℕ => ((((m + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹) :=
    (summable_nat_add_iff 1).mpr hbase
  have hC : Summable (fun m : ℕ => ‖s‖ * ((((m + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹) :=
    hshift.mul_left _
  refine Summable.of_norm_bounded hC (fun m => ?_)
  have hle1 := norm_etaPairTerm_le s hs m
  have ha_pos : (0 : ℝ) < ((((2 * m + 1 : ℕ)) : ℝ)) := Nat.cast_pos.mpr (by omega)
  have hm_pos : (0 : ℝ) < ((((m + 1 : ℕ)) : ℝ)) := Nat.cast_pos.mpr (by omega)
  have hm_le : ((((m + 1 : ℕ)) : ℝ)) ≤ ((((2 * m + 1 : ℕ)) : ℝ)) :=
    Nat.cast_le.mpr (by omega)
  have hexp_nonneg : (0 : ℝ) ≤ s.re + 1 := by linarith
  have hrpow_eq : ((((2 * m + 1 : ℕ) : ℝ)) ^ (-s.re - 1))
      = ((((2 * m + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹ := by
    have e : -s.re - 1 = -(s.re + 1) := by ring
    rw [e]
    exact Real.rpow_neg (Nat.cast_nonneg _) _
  have hrpow_le : ((((2 * m + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹
      ≤ ((((m + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹ := by
    apply (inv_le_inv₀ (Real.rpow_pos_of_pos ha_pos _)
      (Real.rpow_pos_of_pos hm_pos _)).mpr
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hm_le hexp_nonneg
  calc ‖etaPairTerm s m‖ ≤ ‖s‖ * ((((2 * m + 1 : ℕ) : ℝ)) ^ (-s.re - 1)) := hle1
    _ = ‖s‖ * ((((2 * m + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹ := by rw [hrpow_eq]
    _ ≤ ‖s‖ * ((((m + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹ :=
        mul_le_mul_of_nonneg_left hrpow_le (norm_nonneg _)

/-- Even partial sums are sums of pairs (induction, two `sum_range_succ`). -/
theorem etaDirichlet_even_partial (s : ℂ) (M : ℕ) :
    (∑ k ∈ Finset.range (2 * M), etaDirichletTerm s k)
      = ∑ m ∈ Finset.range M, etaPairTerm s m := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h2s : 2 * (M + 1) = (2 * M + 1) + 1 := by ring
    have hpair : etaPairTerm s M
        = etaDirichletTerm s (2 * M) + etaDirichletTerm s (2 * M + 1) := rfl
    calc (∑ k ∈ Finset.range (2 * (M + 1)), etaDirichletTerm s k)
        = (∑ k ∈ Finset.range (2 * M), etaDirichletTerm s k)
          + etaDirichletTerm s (2 * M) + etaDirichletTerm s (2 * M + 1) := by
          rw [h2s, Finset.sum_range_succ, Finset.sum_range_succ]
      _ = (∑ m ∈ Finset.range M, etaPairTerm s m) + etaPairTerm s M := by
          rw [ih, hpair, add_assoc]
      _ = ∑ m ∈ Finset.range (M + 1), etaPairTerm s m := by
          rw [Finset.sum_range_succ]

/-- Even subsequence tends to the paired tsum. -/
theorem etaDirichlet_even_tendsto_pair {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ => ∑ k ∈ Finset.range (2 * M), etaDirichletTerm s k)
      atTop (𝓝 (∑' m, etaPairTerm s m)) := by
  have h := (summable_etaPairTerm hs).hasSum.tendsto_sum_nat
  simpa [etaDirichlet_even_partial] using h

/-- `M ↦ 2 * M` tends to `atTop`. -/
theorem tendsto_two_mul_atTop : Tendsto (fun M : ℕ => 2 * M) atTop atTop := by
  apply Filter.tendsto_atTop_mono (fun M => Nat.le_mul_of_pos_left M (by norm_num))
  exact Filter.tendsto_id

/-- On `1 < s.re`, the paired tsum equals the continued `etaHurwitz`. -/
theorem etaPairLim_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    (∑' m, etaPairTerm s m) = etaHurwitz s := by
  have hs0 : 0 < s.re := by linarith
  have hev_pair := etaDirichlet_even_tendsto_pair hs0
  have hfull : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, etaDirichletTerm s k)
      atTop (𝓝 (∑' n, etaDirichletTerm s n)) :=
    (etaDirichlet_summable hs).hasSum.tendsto_sum_nat
  have hev_full : Tendsto (fun M : ℕ => ∑ k ∈ Finset.range (2 * M), etaDirichletTerm s k)
      atTop (𝓝 (∑' n, etaDirichletTerm s n)) :=
    hfull.comp tendsto_two_mul_atTop
  have huniq := tendsto_nhds_unique hev_full hev_pair
  have h1 := eta_tsum_eq_of_one_lt_re hs
  have h2 := etaHurwitz_eq_of_one_lt_re hs
  rw [← huniq, h1]
  exact h2.symm

/-- `1/2` as a complex ofReal (for norm/Re computations). -/
theorem coe_half_eq : ((1 / 2 : ℂ)) = ((((1 / 2 : ℝ))) : ℂ) := by simp

/-- `3/2` as a complex ofReal. -/
theorem coe_three_half_eq : ((3 / 2 : ℂ)) = ((((3 / 2 : ℝ))) : ℂ) := by simp

/-- `1/2` lies in the ball `ball 1 (3/4)`. -/
theorem mem_ball_half : ((1 / 2 : ℂ)) ∈ Metric.ball (1 : ℂ) (3 / 4 : ℝ) := by
  have e1 : (1 : ℂ) = ((((1 : ℝ))) : ℂ) := by simp
  rw [Metric.mem_ball, dist_eq_norm, coe_half_eq, e1, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  norm_num

/-- `3/2` lies in the ball `ball 1 (3/4)`. -/
theorem mem_ball_three_half : ((3 / 2 : ℂ)) ∈ Metric.ball (1 : ℂ) (3 / 4 : ℝ) := by
  have e1 : (1 : ℂ) = ((((1 : ℝ))) : ℂ) := by simp
  rw [Metric.mem_ball, dist_eq_norm, coe_three_half_eq, e1, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  norm_num

/-- Real parts stay `≥ 1/4` on the ball. -/
theorem hre_ball : ∀ w ∈ Metric.ball (1 : ℂ) (3 / 4 : ℝ), (1 / 4 : ℝ) ≤ w.re := by
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have habs := Complex.abs_re_le_norm (w - 1)
  rw [abs_le] at habs
  have hre_sub : (w - 1).re = w.re - 1 := by
    rw [Complex.sub_re, Complex.one_re]
  rw [hre_sub] at habs
  linarith [habs.1, hw]

/-- Norms stay `≤ 7/4` on the ball. -/
theorem hnorm_ball : ∀ w ∈ Metric.ball (1 : ℂ) (3 / 4 : ℝ), ‖w‖ ≤ 7 / 4 := by
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have e : w = 1 + (w - 1) := by ring
  calc ‖w‖ = ‖1 + (w - 1)‖ := by conv_lhs => rw [e]
    _ ≤ ‖(1 : ℂ)‖ + ‖w - 1‖ := norm_add_le _ _
    _ ≤ 7 / 4 := by rw [norm_one]; linarith

/-- Uniform summable majorant on the ball (`p = 5/4 > 1`). -/
theorem etaPair_majorant_summable :
    Summable (fun m : ℕ => (7 / 4 : ℝ) * ((((m + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ)))⁻¹) := by
  have hp1 : (1 : ℝ) < (5 / 4 : ℝ) := by norm_num
  have hbase : Summable (fun n : ℕ => ((((n : ℝ)) ^ (5 / 4 : ℝ)))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hp1
  have hshift : Summable (fun m : ℕ => ((((m + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ)))⁻¹) :=
    (summable_nat_add_iff 1).mpr hbase
  exact hshift.mul_left _

/-- Pointwise uniform bound on the ball. -/
theorem etaPair_bound_ball (m : ℕ) (w : ℂ) (hw : w ∈ Metric.ball (1 : ℂ) (3 / 4 : ℝ)) :
    ‖etaPairTerm w m‖ ≤ (7 / 4 : ℝ) * ((((m + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ)))⁻¹ := by
  have hw14 := hre_ball w hw
  have hwnorm := hnorm_ball w hw
  have hs_pos : 0 < w.re := by linarith
  have hle1 := norm_etaPairTerm_le w hs_pos m
  have ha1 : (1 : ℝ) ≤ ((((2 * m + 1 : ℕ)) : ℝ)) := by
    exact_mod_cast (show 1 ≤ 2 * m + 1 by omega)
  have hm_pos : (0 : ℝ) < ((((m + 1 : ℕ)) : ℝ)) := Nat.cast_pos.mpr (by omega)
  have ha_pos : (0 : ℝ) < ((((2 * m + 1 : ℕ)) : ℝ)) := Nat.cast_pos.mpr (by omega)
  have hm_le : ((((m + 1 : ℕ)) : ℝ)) ≤ ((((2 * m + 1 : ℕ)) : ℝ)) :=
    Nat.cast_le.mpr (by omega)
  have hexp_le : -w.re - 1 ≤ -(5 / 4 : ℝ) := by linarith
  have hstep1 : ((((2 * m + 1 : ℕ)) : ℝ) ^ (-w.re - 1))
      ≤ ((((2 * m + 1 : ℕ)) : ℝ) ^ (-(5 / 4 : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le ha1 hexp_le
  have hrpow_eq : ((((2 * m + 1 : ℕ)) : ℝ) ^ (-(5 / 4 : ℝ)))
      = ((((2 * m + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ)))⁻¹ :=
    Real.rpow_neg (Nat.cast_nonneg _) _
  have hinv_le : ((((2 * m + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ)))⁻¹
      ≤ ((((m + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ)))⁻¹ := by
    apply (inv_le_inv₀ (Real.rpow_pos_of_pos ha_pos _)
      (Real.rpow_pos_of_pos hm_pos _)).mpr
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hm_le (by norm_num)
  calc ‖etaPairTerm w m‖ ≤ ‖w‖ * ((((2 * m + 1 : ℕ) : ℝ)) ^ (-w.re - 1)) := hle1
    _ ≤ (7 / 4) * ((((2 * m + 1 : ℕ)) : ℝ) ^ (-(5 / 4 : ℝ))) :=
        mul_le_mul hwnorm hstep1
          (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by norm_num)
    _ = (7 / 4) * ((((2 * m + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ)))⁻¹ := by rw [hrpow_eq]
    _ ≤ (7 / 4) * ((((m + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ)))⁻¹ :=
        mul_le_mul_of_nonneg_left hinv_le (by norm_num)

/-- Each pair term is entire in `s`. -/
theorem etaPairTerm_differentiable (m : ℕ) :
    Differentiable ℂ (fun s : ℂ => etaPairTerm s m) := by
  have diff_of_term : ∀ k : ℕ,
      Differentiable ℂ (fun s : ℂ => etaDirichletTerm s k) := by
    intro k
    have hbase : ((((k + 1 : ℕ) : ℂ))) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      exact Nat.succ_ne_zero k
    haveI : NeZero ((((k + 1 : ℕ) : ℂ)) : ℂ) := ⟨hbase⟩
    have hcpow : Differentiable ℂ (fun s : ℂ => ((((k + 1 : ℕ) : ℂ)) ^ s)) :=
      differentiable_const_cpow_of_neZero _
    have hdenom : ∀ s : ℂ, ((((k + 1 : ℕ) : ℂ)) ^ s) ≠ 0 :=
      fun s => Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)
    show Differentiable ℂ (fun s : ℂ => ((-1 : ℂ) ^ k) / ((((k + 1 : ℕ) : ℂ)) ^ s))
    exact (differentiable_const _).div hcpow hdenom
  show Differentiable ℂ
    (fun s : ℂ => etaDirichletTerm s (2 * m) + etaDirichletTerm s (2 * m + 1))
  exact (diff_of_term _).add (diff_of_term _)

/-- `G` is analytic on the ball (locally uniform tsum). -/
theorem analyticOn_etaPairLim_ball :
    AnalyticOnNhd ℂ (fun s => ∑' m, etaPairTerm s m)
      (Metric.ball (1 : ℂ) (3 / 4 : ℝ)) := by
  have hdiff : DifferentiableOn ℂ (fun s => ∑' m, etaPairTerm s m)
      (Metric.ball (1 : ℂ) (3 / 4 : ℝ)) :=
    Complex.differentiableOn_tsum_of_summable_norm etaPair_majorant_summable
      (fun m => (etaPairTerm_differentiable m).differentiableOn)
      Metric.isOpen_ball (fun m w hw => etaPair_bound_ball m w hw)
  exact hdiff.analyticOnNhd Metric.isOpen_ball

/-- `etaHurwitz` is analytic on the ball. -/
theorem analytic_etaHurwitz_ball :
    AnalyticOnNhd ℂ etaHurwitz (Metric.ball (1 : ℂ) (3 / 4 : ℝ)) :=
  analytic_etaHurwitz.mono (Set.subset_univ _)

/-- `G = etaHurwitz` on the ball (identity theorem from agreement on `1 < Re`). -/
theorem etaPairLim_eq_etaHurwitz_ball :
    Set.EqOn (fun s => ∑' m, etaPairTerm s m) etaHurwitz
      (Metric.ball (1 : ℂ) (3 / 4 : ℝ)) := by
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq analyticOn_etaPairLim_ball
    analytic_etaHurwitz_ball Metric.isPreconnected_ball mem_ball_three_half ?_
  refine eventually_of_mem ?_ (fun t ht => etaPairLim_eq_of_one_lt_re ht)
  exact (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by
    show (1 : ℝ) < ((3 / 2 : ℂ)).re
    rw [coe_three_half_eq, Complex.ofReal_re]
    norm_num)

/-- In particular at `s = 1/2`. -/
theorem etaPairLim_half :
    (∑' m, etaPairTerm ((1 / 2 : ℂ)) m) = etaHurwitz (1 / 2 : ℂ) :=
  etaPairLim_eq_etaHurwitz_ball mem_ball_half

/-- `etaDirichletTerm` at `1/2` is the real eta term coerced. -/
theorem etaDirichletTerm_half_eq (k : ℕ) :
    etaDirichletTerm (1 / 2 : ℂ) k = etaTermℂ k := by
  have hcast : ((((k + 1 : ℕ) : ℂ))) = (((((k : ℝ) + 1 : ℝ))) : ℂ) := by
    push_cast
    ring
  have hsqrt : ((((k : ℝ) + 1 : ℝ)) ^ ((1 / 2 : ℝ))) = Real.sqrt (((k : ℝ) + 1)) :=
    (Real.sqrt_eq_rpow _).symm
  have h1 : (((-1 : ℤ) ^ k : ℝ)) = (-1 : ℝ) ^ k := by push_cast; ring
  have hnum : ((-1 : ℂ) ^ k) = (((((-1 : ℤ) ^ k : ℝ))) : ℂ) := by
    rw [h1, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
  simp only [etaDirichletTerm, etaTermℂ, etaTerm]
  rw [hcast, coe_half_eq, ← Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1),
    hsqrt, hnum, Complex.ofReal_div]

/-- MAIN `hLim`: any `Tendsto` eta limit coerces to the continued Hurwitz value. -/
theorem etaTendsto_eq_etaHurwitz (L : ℝ)
    (hL : Tendsto etaPartialℂ atTop (𝓝 ((L : ℝ) : ℂ))) :
    ((L : ℝ) : ℂ) = etaHurwitz (1 / 2 : ℂ) := by
  have h2M := tendsto_two_mul_atTop
  have hevL : Tendsto (fun M : ℕ => etaPartialℂ (2 * M)) atTop (𝓝 ((L : ℝ) : ℂ)) :=
    hL.comp h2M
  have hevG : Tendsto
      (fun M : ℕ => ∑ k ∈ Finset.range (2 * M), etaDirichletTerm (1 / 2 : ℂ) k)
      atTop (𝓝 (∑' m, etaPairTerm (1 / 2 : ℂ) m)) :=
    etaDirichlet_even_tendsto_pair (by
      show (0 : ℝ) < ((1 / 2 : ℂ)).re
      rw [coe_half_eq, Complex.ofReal_re]
      norm_num)
  have hev_eq : (fun M : ℕ => etaPartialℂ (2 * M))
      = (fun M : ℕ => ∑ k ∈ Finset.range (2 * M), etaDirichletTerm (1 / 2 : ℂ) k) := by
    funext M
    simp only [etaPartialℂ]
    apply Finset.sum_congr rfl
    intro k _
    rw [etaDirichletTerm_half_eq]
  rw [hev_eq] at hevL
  have huniq := tendsto_nhds_unique hevL hevG
  rw [huniq]
  exact etaPairLim_half

/-- Unconditional `ζ(1/2)` feeder: positivity + `hLim` (no hypotheses). -/
theorem zeta_half_value :
    ∃ L : ℝ, 0 < L ∧
      riemannZeta (1 / 2 : ℂ) = (L : ℂ) / (1 - (((Real.sqrt 2 : ℝ)) : ℂ)) :=
  zeta_half_feeder_of_etaHurwitz_lim (fun L hL => etaTendsto_eq_etaHurwitz L hL)

#print axioms etaTendsto_eq_etaHurwitz
#print axioms zeta_half_value
#print axioms etaPairLim_half

/-!
## Higher eta partial-sum bounds `S₄–S₉` (tightening `L`).

The committed `eta_half_two_sided_tight` gives `S₂ ≤ L ≤ S₃` (width
`S₃ - S₂ = 1/√3 ≈ 0.578`). Here we push the same alternating-series API to
higher even/odd partial sums: generic even-lower / odd-upper bounds
(`eta_half_ge_even`, `eta_half_le_odd`, via
`Antitone.alternating_series_le_tendsto` /
`Antitone.tendsto_le_alternating_series`), exact `√`-forms for `S₄–S₉`
(each closed by `simp` + `ring_nf`, same pattern as `S₂`/`S₃`),
monotonicity comparisons (`S₂ ≤ S₄ ≤ S₆ ≤ S₈ ≤ L ≤ S₉ ≤ S₇ ≤ S₅ ≤ S₃`,
each via `Real.sqrt_le_sqrt` + `one_div_le_one_div_of_le`), and rigorous
numeric widths (`S₉ - S₈ = 1/3`, `S₇ - S₆ = 1/√7 < 0.38`,
`S₅ - S₄ = 1/√5 < 0.45`).

Only the `Tendsto` form is used (the `∑'` tsum form is `0`).
-/

/-- `√4 = 2` (for `S₄` onward). -/
theorem sqrt_four_eq : Real.sqrt (4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `√9 = 3` (for `S₉`). -/
theorem sqrt_nine_eq : Real.sqrt (9 : ℝ) = 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Exact `S₂` (standalone; proved inline in `eta_half_pos`). -/
theorem etaPartial_two_eq : etaPartial 2 = 1 - 1 / Real.sqrt 2 := by
  simp [etaPartial, Finset.sum_range_succ, Real.sqrt_one]
  ring_nf

/-- Exact `S₄ = 1 - 1/√2 + 1/√3 - 1/2`. -/
theorem etaPartial_four_eq :
    etaPartial 4 = 1 - 1 / Real.sqrt 2 + 1 / Real.sqrt 3 - 1 / 2 := by
  simp [etaPartial, Finset.sum_range_succ, Real.sqrt_one]
  ring_nf

/-- Exact `S₅`. -/
theorem etaPartial_five_eq :
    etaPartial 5
      = 1 - 1 / Real.sqrt 2 + 1 / Real.sqrt 3 - 1 / 2 + 1 / Real.sqrt 5 := by
  simp [etaPartial, Finset.sum_range_succ, Real.sqrt_one]
  ring_nf

/-- Exact `S₆`. -/
theorem etaPartial_six_eq :
    etaPartial 6
      = 1 - 1 / Real.sqrt 2 + 1 / Real.sqrt 3 - 1 / 2 + 1 / Real.sqrt 5
        - 1 / Real.sqrt 6 := by
  simp [etaPartial, Finset.sum_range_succ, Real.sqrt_one]
  ring_nf

/-- Exact `S₇`. -/
theorem etaPartial_seven_eq :
    etaPartial 7
      = 1 - 1 / Real.sqrt 2 + 1 / Real.sqrt 3 - 1 / 2 + 1 / Real.sqrt 5
        - 1 / Real.sqrt 6 + 1 / Real.sqrt 7 := by
  simp [etaPartial, Finset.sum_range_succ, Real.sqrt_one]
  ring_nf

/-- Exact `S₈`. -/
theorem etaPartial_eight_eq :
    etaPartial 8
      = 1 - 1 / Real.sqrt 2 + 1 / Real.sqrt 3 - 1 / 2 + 1 / Real.sqrt 5
        - 1 / Real.sqrt 6 + 1 / Real.sqrt 7 - 1 / Real.sqrt 8 := by
  simp [etaPartial, Finset.sum_range_succ, Real.sqrt_one]
  ring_nf

/-- Exact `S₉` (using `√9 = 3`). -/
theorem etaPartial_nine_eq :
    etaPartial 9
      = 1 - 1 / Real.sqrt 2 + 1 / Real.sqrt 3 - 1 / 2 + 1 / Real.sqrt 5
        - 1 / Real.sqrt 6 + 1 / Real.sqrt 7 - 1 / Real.sqrt 8 + 1 / 3 := by
  simp [etaPartial, Finset.sum_range_succ, Real.sqrt_one]
  ring_nf

/-- LOWER BOUND (general even): every eta limit `L` satisfies `S_{2N} ≤ L`. -/
theorem eta_half_ge_even (L : ℝ) (N : ℕ)
    (hL : Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L)) : etaPartial (2 * N) ≤ L := by
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
  have h_raw : Finset.sum (Finset.range (2 * N)) (fun i => (-1 : ℝ) ^ i * f i) ≤ L :=
    Antitone.alternating_series_le_tendsto hL' h_anti N
  have h_eq : Finset.sum (Finset.range (2 * N)) (fun i => (-1 : ℝ) ^ i * f i)
      = etaPartial (2 * N) := congrFun h_fun_eq (2 * N)
  linarith

/-- UPPER BOUND (general odd): every eta limit `L` satisfies `L ≤ S_{2N+1}`. -/
theorem eta_half_le_odd (L : ℝ) (N : ℕ)
    (hL : Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L)) : L ≤ etaPartial (2 * N + 1) := by
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
  have h_up := Antitone.tendsto_le_alternating_series hL' h_anti N
  have h_eq : (∑ i ∈ Finset.range (2 * N + 1), (-1 : ℝ) ^ i * f i)
      = etaPartial (2 * N + 1) := congrFun h_fun_eq (2 * N + 1)
  rw [h_eq] at h_up
  exact h_up

/-- `S₄ ≤ L` (even lower, `N = 2`). -/
theorem eta_half_ge_S4 (L : ℝ)
    (hL : Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L)) : etaPartial 4 ≤ L := by
  have h := eta_half_ge_even L 2 hL
  have h44 : (2 * 2 : ℕ) = 4 := rfl
  rwa [h44] at h

/-- `L ≤ S₅` (odd upper, `N = 2`). -/
theorem eta_half_le_S5 (L : ℝ)
    (hL : Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L)) : L ≤ etaPartial 5 := by
  have h := eta_half_le_odd L 2 hL
  have h55 : (2 * 2 + 1 : ℕ) = 5 := rfl
  rwa [h55] at h

/-- `S₆ ≤ L` (even lower, `N = 3`). -/
theorem eta_half_ge_S6 (L : ℝ)
    (hL : Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L)) : etaPartial 6 ≤ L := by
  have h := eta_half_ge_even L 3 hL
  have h66 : (2 * 3 : ℕ) = 6 := rfl
  rwa [h66] at h

/-- `L ≤ S₇` (odd upper, `N = 3`). -/
theorem eta_half_le_S7 (L : ℝ)
    (hL : Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L)) : L ≤ etaPartial 7 := by
  have h := eta_half_le_odd L 3 hL
  have h77 : (2 * 3 + 1 : ℕ) = 7 := rfl
  rwa [h77] at h

/-- `S₈ ≤ L` (even lower, `N = 4`). -/
theorem eta_half_ge_S8 (L : ℝ)
    (hL : Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L)) : etaPartial 8 ≤ L := by
  have h := eta_half_ge_even L 4 hL
  have h88 : (2 * 4 : ℕ) = 8 := rfl
  rwa [h88] at h

/-- `L ≤ S₉` (odd upper, `N = 4`). -/
theorem eta_half_le_S9 (L : ℝ)
    (hL : Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L)) : L ≤ etaPartial 9 := by
  have h := eta_half_le_odd L 4 hL
  have h99 : (2 * 4 + 1 : ℕ) = 9 := rfl
  rwa [h99] at h

/-- `S₂ ≤ S₄` (since `1/√3 ≥ 1/2`, i.e. `√3 ≤ 2`). -/
theorem etaPartial_two_le_four : etaPartial 2 ≤ etaPartial 4 := by
  rw [etaPartial_two_eq, etaPartial_four_eq]
  have h32 : Real.sqrt 3 ≤ 2 := by
    calc Real.sqrt 3 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      _ = 2 := sqrt_four_eq
  have hpos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  linarith [one_div_le_one_div_of_le hpos h32]

/-- `S₅ ≤ S₃` (since `1/√5 ≤ 1/2`, i.e. `2 ≤ √5`). -/
theorem etaPartial_five_le_three : etaPartial 5 ≤ etaPartial 3 := by
  rw [etaPartial_five_eq, etaPartial_three_eq]
  have h25 : (2 : ℝ) ≤ Real.sqrt 5 := by
    calc (2 : ℝ) = Real.sqrt 4 := sqrt_four_eq.symm
      _ ≤ Real.sqrt 5 := Real.sqrt_le_sqrt (by norm_num)
  have hle : (1 : ℝ) / Real.sqrt 5 ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) h25
  linarith

/-- `S₄ ≤ S₆` (since `1/√5 ≥ 1/√6`, i.e. `√5 ≤ √6`). -/
theorem etaPartial_four_le_six : etaPartial 4 ≤ etaPartial 6 := by
  rw [etaPartial_four_eq, etaPartial_six_eq]
  have h56 : Real.sqrt 5 ≤ Real.sqrt 6 := Real.sqrt_le_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hle : (1 : ℝ) / Real.sqrt 6 ≤ 1 / Real.sqrt 5 :=
    one_div_le_one_div_of_le hpos h56
  linarith

/-- `S₇ ≤ S₅` (since `1/√7 ≤ 1/√6`, i.e. `√6 ≤ √7`). -/
theorem etaPartial_seven_le_five : etaPartial 7 ≤ etaPartial 5 := by
  rw [etaPartial_seven_eq, etaPartial_five_eq]
  have h67 : Real.sqrt 6 ≤ Real.sqrt 7 := Real.sqrt_le_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hle : (1 : ℝ) / Real.sqrt 7 ≤ 1 / Real.sqrt 6 :=
    one_div_le_one_div_of_le hpos h67
  linarith

/-- `S₆ ≤ S₈` (since `1/√7 ≥ 1/√8`, i.e. `√7 ≤ √8`). -/
theorem etaPartial_six_le_eight : etaPartial 6 ≤ etaPartial 8 := by
  rw [etaPartial_six_eq, etaPartial_eight_eq]
  have h78 : Real.sqrt 7 ≤ Real.sqrt 8 := Real.sqrt_le_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 7 := Real.sqrt_pos.mpr (by norm_num)
  have hle : (1 : ℝ) / Real.sqrt 8 ≤ 1 / Real.sqrt 7 :=
    one_div_le_one_div_of_le hpos h78
  linarith

/-- `S₉ ≤ S₇` (since `1/3 ≤ 1/√8`, i.e. `√8 ≤ 3`). -/
theorem etaPartial_nine_le_seven : etaPartial 9 ≤ etaPartial 7 := by
  rw [etaPartial_nine_eq, etaPartial_seven_eq]
  have h89 : Real.sqrt 8 ≤ 3 := by
    calc Real.sqrt 8 ≤ Real.sqrt 9 := Real.sqrt_le_sqrt (by norm_num)
      _ = 3 := sqrt_nine_eq
  have hpos : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  linarith [one_div_le_one_div_of_le hpos h89]

/-- Full tightening chain `S₂ ≤ S₄ ≤ S₆ ≤ S₈`, `S₉ ≤ S₇ ≤ S₅ ≤ S₃`. -/
theorem eta_half_tight_chain :
    etaPartial 2 ≤ etaPartial 4 ∧ etaPartial 4 ≤ etaPartial 6 ∧
    etaPartial 6 ≤ etaPartial 8 ∧ etaPartial 9 ≤ etaPartial 7 ∧
    etaPartial 7 ≤ etaPartial 5 ∧ etaPartial 5 ≤ etaPartial 3 :=
  ⟨etaPartial_two_le_four, etaPartial_four_le_six, etaPartial_six_le_eight,
    etaPartial_nine_le_seven, etaPartial_seven_le_five, etaPartial_five_le_three⟩

/-- TWO-SIDED `S₄/S₅` interval. -/
theorem eta_half_two_sided_S4_S5 :
    ∃ L : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L) ∧ etaPartial 4 ≤ L ∧ L ≤ etaPartial 5 ∧ 0 < L := by
  obtain ⟨L, hL, hpos⟩ := eta_half_pos
  exact ⟨L, hL, eta_half_ge_S4 L hL, eta_half_le_S5 L hL, hpos⟩

/-- TWO-SIDED `S₆/S₇` interval. -/
theorem eta_half_two_sided_S6_S7 :
    ∃ L : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L) ∧ etaPartial 6 ≤ L ∧ L ≤ etaPartial 7 ∧ 0 < L := by
  obtain ⟨L, hL, hpos⟩ := eta_half_pos
  exact ⟨L, hL, eta_half_ge_S6 L hL, eta_half_le_S7 L hL, hpos⟩

/-- TWO-SIDED `S₈/S₉` interval (tightest in this file). -/
theorem eta_half_two_sided_S8_S9 :
    ∃ L : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L) ∧ etaPartial 8 ≤ L ∧ L ≤ etaPartial 9 ∧ 0 < L := by
  obtain ⟨L, hL, hpos⟩ := eta_half_pos
  exact ⟨L, hL, eta_half_ge_S8 L hL, eta_half_le_S9 L hL, hpos⟩

/-- Width `S₅ - S₄ = 1/√5`. -/
theorem etaPartial_five_sub_four :
    etaPartial 5 - etaPartial 4 = 1 / Real.sqrt 5 := by
  rw [etaPartial_five_eq, etaPartial_four_eq]
  ring

/-- Width `S₇ - S₆ = 1/√7`. -/
theorem etaPartial_seven_sub_six :
    etaPartial 7 - etaPartial 6 = 1 / Real.sqrt 7 := by
  rw [etaPartial_seven_eq, etaPartial_six_eq]
  ring

/-- Width `S₉ - S₈ = 1/3`. -/
theorem etaPartial_nine_sub_eight :
    etaPartial 9 - etaPartial 8 = 1 / 3 := by
  rw [etaPartial_nine_eq, etaPartial_eight_eq]
  ring

/-- Numeric width `S₅ - S₄ < 0.45` (`√5 > 2.23` since `2.23² = 4.9729 < 5`). -/
theorem etaWidth_S4_S5_lt : etaPartial 5 - etaPartial 4 < 0.45 := by
  rw [etaPartial_five_sub_four]
  have h5 : (2.23 : ℝ) < Real.sqrt 5 := by
    calc (2.23 : ℝ) = Real.sqrt (2.23 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 5 := Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  have hle : 1 / Real.sqrt 5 ≤ 1 / 2.23 :=
    one_div_le_one_div_of_le (by norm_num) (le_of_lt h5)
  calc (1 : ℝ) / Real.sqrt 5 ≤ 1 / 2.23 := hle
    _ < 0.45 := by norm_num

/-- Numeric width `S₇ - S₆ < 0.38` (`√7 > 2.64` since `2.64² = 6.9696 < 7`). -/
theorem etaWidth_S6_S7_lt : etaPartial 7 - etaPartial 6 < 0.38 := by
  rw [etaPartial_seven_sub_six]
  have h7 : (2.64 : ℝ) < Real.sqrt 7 := by
    calc (2.64 : ℝ) = Real.sqrt (2.64 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 7 := Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  have hle : 1 / Real.sqrt 7 ≤ 1 / 2.64 :=
    one_div_le_one_div_of_le (by norm_num) (le_of_lt h7)
  calc (1 : ℝ) / Real.sqrt 7 ≤ 1 / 2.64 := hle
    _ < 0.38 := by norm_num

/-- Numeric width `S₉ - S₈ = 1/3 < 0.334`. -/
theorem etaWidth_S8_S9_lt : etaPartial 9 - etaPartial 8 < 0.334 := by
  rw [etaPartial_nine_sub_eight]
  norm_num

#print axioms sqrt_four_eq
#print axioms etaPartial_four_eq
#print axioms eta_half_ge_even
#print axioms eta_half_le_odd
#print axioms eta_half_ge_S4
#print axioms eta_half_le_S5
#print axioms eta_half_two_sided_S4_S5
#print axioms eta_half_two_sided_S6_S7
#print axioms eta_half_two_sided_S8_S9
#print axioms eta_half_tight_chain
#print axioms etaWidth_S4_S5_lt
#print axioms etaWidth_S6_S7_lt
#print axioms etaWidth_S8_S9_lt

/-!
## Euler–Maclaurin / integral-remainder tightening of `L` (width `0.012 ≤ 0.05`).

PREVIOUS STATE: `S₈ ≤ L ≤ S₉` with width `S₉ - S₈ = 1/3 ≈ 0.333`
(`eta_half_two_sided_S8_S9`, `etaPartial_nine_sub_eight`). Pushing explicit
partial sums further needs `n ≈ 28000` for `±0.003` (infeasible: one rigorous
`√`-enclosure per term). This section builds the NEXT method: pair the series
(`d_m = a_{2m} - a_{2m+1} ≥ 0`), identify `L = S_{2M} + T_M` with
`T_M = ∑'_{m} d_{m+M}`, and bound `T_M` from BOTH sides.

MATHLIB GREPS USED (all pre-existing, only called — no duplication):
* integral test: `AntetoneOn.tsum_comp_add_le_integral`
  (`Mathlib/Analysis/SumIntegralComparisons.lean:221`), same pattern as
  `interval_arith.lean`'s `R00EtaConv.majorant_tsum_tail_le` (read-only reuse);
* `integrableOn_Ioi_rpow_of_lt`, `integral_Ioi_rpow_of_lt`
  (`Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean:130,172`);
* `Real.antitoneOn_rpow_Ioi_of_exponent_nonpos`
  (`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:623`);
* alternating-remainder API: `alternating_series_error_bound`
  (`Mathlib/Analysis/SpecificLimits/Normed.lean:856`) needs `Summable`
  (hence is inapplicable here — the eta series is NOT summable,
  `eta_not_summable`); only the even/odd partial-sum bounds
  (`Antitone.alternating_series_le_tendsto`,
  `Antitone.tendsto_le_alternating_series`) apply, and those saturate at
  width `a_N`. The paired series IS summable (`O(m^{-3/2})`), so both the
  integral test and the convexity telescoping below apply to it.

MACHINERY (general `M ≥ 1`):
1. `etaPairR` (real pairs) + `etaPairR_upper`: `d_m ≤ (1/2)·(2m+1)^{-3/2}`
   via the exact formula `1/√a - 1/√(a+1) = 1/((√a+√(a+1))·√a·√(a+1))`
   (`invSqrt_pair_eq`), the real analogue of the `R00EtaConv.norm_etaPair_le`
   MVT bound (here elementary — no complex MVT needed);
2. `eta_tail_integral_bound` (`etaPair_tail_integral`): `T_M ≤ 1/√M`
   (explicit `C = 1` in `C/√M`, i.e. `C = √2` in `C/√N` with `N = 2M`) via
   `AntetoneOn.tsum_comp_add_le_integral` on `x^{-3/2}` — the required
   integral-comparison tail bound of the form `‖L - S_N‖ ≤ C/√N`
   (`eta_limit_norm_sub_le`);
3. SHARPER two-sided convexity telescoping (`sqrt_convex_step`: `1/√x` is
   discretely convex, `1/√a + 1/√(a+2) ≥ 2/√(a+1)`): gaps
   `g_j = 1/√j - 1/√(j+1)` decrease, so
   `1/(2√(2M+1)) ≤ T_M ≤ 1/(2√(2M))` (`etaPair_tail_lower/upper`).
   This is the discrete Euler–Maclaurin idea at order 0 and is asymptotically
   sharp (both constants are best possible).

APPLICATION (`M = 4`, i.e. `N = 8`): rigorous `√`-enclosures give
`S₈ ∈ [0.4328, 0.4344]`; tail `T₄ ∈ [1/6, 0.177]`; hence
`L ∈ [0.5994, 0.6114]` (`eta_half_tight_best`), width `0.012 ≤ 0.05`
— a 27× improvement over `1/3`. Only the `Tendsto` form is used.
-/

/-- Real paired eta increment `d_m = 1/√(2m+1) - 1/√(2m+2)` (all terms `≥ 0`). -/
noncomputable def etaPairR (m : ℕ) : ℝ :=
  1 / Real.sqrt (((2 * m + 1 : ℕ)) : ℝ) - 1 / Real.sqrt (((2 * m + 2 : ℕ)) : ℝ)

/-- Inverse-sqrt helper `f(j) = 1/√j`. -/
noncomputable def etaInvSqrt (j : ℕ) : ℝ := 1 / Real.sqrt ((j : ℝ))

/-- Gap helper `g_j = f(j) - f(j+1)`. -/
noncomputable def etaGap (j : ℕ) : ℝ := etaInvSqrt j - etaInvSqrt (j + 1)

/-- Discrete convexity of `x ↦ 1/√x`: for `1 ≤ a`,
    `1/√a + 1/√(a+2) ≥ 2/√(a+1)`.
    Proof: it suffices `√(a+1)·(√a+√(a+2)) ≥ 2·√a·√(a+2)` (then clear
    denominators); the squared difference is
    `2·((b-t)·(b+2t)) ≥ 0` with `b = a+1`, `t = √a·√(a+2) = √(a(a+2)) ≤ b`. -/
theorem sqrt_convex_step {a : ℝ} (ha : 1 ≤ a) :
    2 / Real.sqrt (a + 1) ≤ 1 / Real.sqrt a + 1 / Real.sqrt (a + 2) := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < a + 1 := by linarith
  have hc0 : (0 : ℝ) < a + 2 := by linarith
  have hsa : (0 : ℝ) < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hsb : (0 : ℝ) < Real.sqrt (a + 1) := Real.sqrt_pos.mpr hb0
  have hsc : (0 : ℝ) < Real.sqrt (a + 2) := Real.sqrt_pos.mpr hc0
  have hmul : Real.sqrt a * Real.sqrt (a + 2) = Real.sqrt (a * (a + 2)) :=
    (Real.sqrt_mul (le_of_lt ha0) _).symm
  have hle : Real.sqrt (a * (a + 2)) ≤ a + 1 := by
    calc Real.sqrt (a * (a + 2)) ≤ Real.sqrt ((a + 1) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = a + 1 := Real.sqrt_sq (by linarith)
  have hsq : (2 * Real.sqrt a * Real.sqrt (a + 2)) ^ 2
      ≤ (Real.sqrt (a + 1) * (Real.sqrt a + Real.sqrt (a + 2))) ^ 2 := by
    have e : (Real.sqrt (a + 1) * (Real.sqrt a + Real.sqrt (a + 2))) ^ 2
          - (2 * Real.sqrt a * Real.sqrt (a + 2)) ^ 2
        = 2 * (((a + 1) - Real.sqrt a * Real.sqrt (a + 2))
          * ((a + 1) + 2 * (Real.sqrt a * Real.sqrt (a + 2)))) := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hb0)]
      have e13 : (Real.sqrt a + Real.sqrt (a + 2)) ^ 2
          = (a + (a + 2)) + 2 * (Real.sqrt a * Real.sqrt (a + 2)) := by
        have r : (Real.sqrt a + Real.sqrt (a + 2)) ^ 2
            = (Real.sqrt a) ^ 2 + 2 * (Real.sqrt a * Real.sqrt (a + 2))
              + (Real.sqrt (a + 2)) ^ 2 := by ring
        rw [r, Real.sq_sqrt (le_of_lt ha0), Real.sq_sqrt (le_of_lt hc0)]
        ring
      rw [e13]
      ring
    have hnn : (0 : ℝ) ≤ (Real.sqrt (a + 1) * (Real.sqrt a + Real.sqrt (a + 2))) ^ 2
          - (2 * Real.sqrt a * Real.sqrt (a + 2)) ^ 2 := by
      rw [e]
      have ht0 : (0 : ℝ) ≤ Real.sqrt a * Real.sqrt (a + 2) :=
        mul_nonneg (le_of_lt hsa) (le_of_lt hsc)
      have hbt : Real.sqrt a * Real.sqrt (a + 2) ≤ a + 1 := by
        rw [hmul]; exact hle
      exact mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
    linarith
  have hnum : 2 * Real.sqrt a * Real.sqrt (a + 2)
      ≤ Real.sqrt (a + 1) * (Real.sqrt a + Real.sqrt (a + 2)) := by
    have hX : (0 : ℝ) ≤ 2 * Real.sqrt a * Real.sqrt (a + 2) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hsa)) (le_of_lt hsc)
    have hY : (0 : ℝ) ≤ Real.sqrt (a + 1) * (Real.sqrt a + Real.sqrt (a + 2)) :=
      mul_nonneg (le_of_lt hsb) (add_nonneg (le_of_lt hsa) (le_of_lt hsc))
    have eX : 2 * Real.sqrt a * Real.sqrt (a + 2)
        = Real.sqrt ((2 * Real.sqrt a * Real.sqrt (a + 2)) ^ 2) :=
      (Real.sqrt_sq hX).symm
    have eY : Real.sqrt (a + 1) * (Real.sqrt a + Real.sqrt (a + 2))
        = Real.sqrt ((Real.sqrt (a + 1) * (Real.sqrt a + Real.sqrt (a + 2))) ^ 2) :=
      (Real.sqrt_sq hY).symm
    rw [eX, eY]
    exact Real.sqrt_le_sqrt hsq
  have hden : (0 : ℝ) < Real.sqrt a * Real.sqrt (a + 2) * Real.sqrt (a + 1) :=
    mul_pos (mul_pos hsa hsc) hsb
  have ha' : Real.sqrt a ≠ 0 := ne_of_gt hsa
  have hb' : Real.sqrt (a + 1) ≠ 0 := ne_of_gt hsb
  have hc' : Real.sqrt (a + 2) ≠ 0 := ne_of_gt hsc
  have hclear : 1 / Real.sqrt a + 1 / Real.sqrt (a + 2) - 2 / Real.sqrt (a + 1)
      = (Real.sqrt (a + 1) * (Real.sqrt a + Real.sqrt (a + 2))
        - 2 * Real.sqrt a * Real.sqrt (a + 2))
        / (Real.sqrt a * Real.sqrt (a + 2) * Real.sqrt (a + 1)) := by
    field_simp
    ring
  have hnn2 : (0 : ℝ) ≤ 1 / Real.sqrt a + 1 / Real.sqrt (a + 2)
      - 2 / Real.sqrt (a + 1) := by
    rw [hclear]
    exact div_nonneg (by linarith) (le_of_lt hden)
  linarith

/-- Gap decrease from convexity: `g(a) ≥ g(a+1)` for `1 ≤ a`. -/
theorem invSqrt_gap_anti {a : ℝ} (ha : 1 ≤ a) :
    1 / Real.sqrt (a + 1) - 1 / Real.sqrt (a + 2)
      ≤ 1 / Real.sqrt a - 1 / Real.sqrt (a + 1) := by
  have h := sqrt_convex_step ha
  have e : (2 : ℝ) / Real.sqrt (a + 1)
      = 1 / Real.sqrt (a + 1) + 1 / Real.sqrt (a + 1) := by ring
  rw [e] at h
  linarith

/-- `etaInvSqrt` is nonnegative. -/
theorem etaInvSqrt_nonneg (j : ℕ) : 0 ≤ etaInvSqrt j := by
  simp only [etaInvSqrt]
  exact one_div_nonneg.mpr (Real.sqrt_nonneg _)

/-- Gaps are nonnegative for `j ≥ 1`. -/
theorem etaGap_nonneg {j : ℕ} (hj : 1 ≤ j) : 0 ≤ etaGap j := by
  have ha : (1 : ℝ) ≤ ((((j : ℕ)) : ℝ)) := by exact_mod_cast hj
  have ha0 : (0 : ℝ) < ((((j : ℕ)) : ℝ)) := by linarith
  have e1 : ((((j + 1 : ℕ)) : ℝ)) = ((((j : ℕ)) : ℝ)) + 1 := by push_cast; ring
  have hle : Real.sqrt ((((j : ℕ)) : ℝ)) ≤ Real.sqrt ((((j + 1 : ℕ)) : ℝ)) := by
    apply Real.sqrt_le_sqrt
    rw [e1]
    linarith
  have h := one_div_le_one_div_of_le (Real.sqrt_pos.mpr ha0) hle
  simp only [etaGap, etaInvSqrt]
  linarith

/-- Gaps decrease: `g_{j+1} ≤ g_j` for `j ≥ 1`. -/
theorem etaGap_anti {j : ℕ} (hj : 1 ≤ j) : etaGap (j + 1) ≤ etaGap j := by
  have ha : (1 : ℝ) ≤ ((((j : ℕ)) : ℝ)) := by exact_mod_cast hj
  have e1 : ((((j + 1 : ℕ)) : ℝ)) = ((((j : ℕ)) : ℝ)) + 1 := by push_cast; ring
  have e2 : ((((j + 1 + 1 : ℕ)) : ℝ)) = ((((j : ℕ)) : ℝ)) + 2 := by push_cast; ring
  have h := invSqrt_gap_anti ha
  simp only [etaGap, etaInvSqrt, e1, e2]
  linarith

/-- Real pairs are nonnegative. -/
theorem etaPairR_nonneg (m : ℕ) : 0 ≤ etaPairR m := by
  simp only [etaPairR]
  have ha : (0 : ℝ) < ((((2 * m + 1 : ℕ)) : ℝ)) := Nat.cast_pos.mpr (by omega)
  have hab : ((((2 * m + 1 : ℕ)) : ℝ)) ≤ ((((2 * m + 2 : ℕ)) : ℝ)) :=
    Nat.cast_le.mpr (by omega)
  have h := one_div_le_one_div_of_le (Real.sqrt_pos.mpr ha)
    (Real.sqrt_le_sqrt hab)
  linarith

/-- A real pair is the gap at the even index: `d_m = g_{2m+1}`. -/
theorem etaPairR_eq_gap (m : ℕ) : etaPairR m = etaGap (2 * m + 1) := by
  have e : 2 * m + 1 + 1 = 2 * m + 2 := by omega
  simp only [etaPairR, etaGap, etaInvSqrt, e]

/-- Exact pair formula: `1/√a - 1/√b = 1/((√a+√b)·√a·√b)` for `b = a+1`. -/
theorem invSqrt_pair_eq {a b : ℝ} (ha : 0 < a) (hb : b = a + 1) :
    1 / Real.sqrt a - 1 / Real.sqrt b
      = 1 / ((Real.sqrt a + Real.sqrt b) * (Real.sqrt a * Real.sqrt b)) := by
  have hb0 : (0 : ℝ) < b := by linarith
  have hsa : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
  have hsb : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hb0)
  have hsq : (Real.sqrt b - Real.sqrt a) * (Real.sqrt a + Real.sqrt b) = 1 := by
    have e : (Real.sqrt b - Real.sqrt a) * (Real.sqrt a + Real.sqrt b)
        = (Real.sqrt b) ^ 2 - (Real.sqrt a) ^ 2 := by ring
    rw [e, Real.sq_sqrt (le_of_lt hb0), Real.sq_sqrt (le_of_lt ha), hb]
    ring
  have hD : (Real.sqrt a + Real.sqrt b) * (Real.sqrt a * Real.sqrt b) ≠ 0 := by
    apply ne_of_gt
    exact mul_pos (add_pos (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hb0))
      (mul_pos (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hb0))
  rw [eq_div_iff hD]
  have e2 : (1 / Real.sqrt a - 1 / Real.sqrt b)
        * ((Real.sqrt a + Real.sqrt b) * (Real.sqrt a * Real.sqrt b))
      = (Real.sqrt b - Real.sqrt a) * (Real.sqrt a + Real.sqrt b) := by
    field_simp
  rw [e2]
  exact hsq

/-- M-test majorant for real pairs: `d_m ≤ (1/2)·(2m+1)^{-3/2}`
    (real analogue of `R00EtaConv.norm_etaPair_le`, proved elementarily). -/
theorem etaPairR_upper (m : ℕ) :
    etaPairR m ≤ (1 / 2 : ℝ) * ((((2 * m + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ)) := by
  have ha : (0 : ℝ) < ((((2 * m + 1 : ℕ)) : ℝ)) := Nat.cast_pos.mpr (by omega)
  have hb : (0 : ℝ) < ((((2 * m + 2 : ℕ)) : ℝ)) := Nat.cast_pos.mpr (by omega)
  have hb_eq : ((((2 * m + 2 : ℕ)) : ℝ)) = ((((2 * m + 1 : ℕ)) : ℝ)) + 1 := by
    have e : 2 * m + 1 + 1 = 2 * m + 2 := by omega
    calc ((((2 * m + 2 : ℕ)) : ℝ)) = ((((2 * m + 1 + 1 : ℕ)) : ℝ)) := by rw [e]
      _ = ((((2 * m + 1 : ℕ)) : ℝ)) + 1 := by rw [Nat.cast_add, Nat.cast_one]
  have hform : 1 / Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
        - 1 / Real.sqrt ((((2 * m + 2 : ℕ)) : ℝ))
      = 1 / ((Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
        + Real.sqrt ((((2 * m + 2 : ℕ)) : ℝ)))
        * (Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
          * Real.sqrt ((((2 * m + 2 : ℕ)) : ℝ)))) :=
    invSqrt_pair_eq ha hb_eq
  have hsqrt_le : Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
      ≤ Real.sqrt ((((2 * m + 2 : ℕ)) : ℝ)) := by
    apply Real.sqrt_le_sqrt
    exact Nat.cast_le.mpr (by omega)
  have hsum_ge : 2 * Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
      ≤ Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
        + Real.sqrt ((((2 * m + 2 : ℕ)) : ℝ)) := by linarith
  have hrpow : ((((2 * m + 1 : ℕ)) : ℝ)) * Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
      = ((((2 * m + 1 : ℕ)) : ℝ)) ^ (3 / 2 : ℝ) := by
    have h1 : ((((2 * m + 1 : ℕ)) : ℝ)) ^ (1 : ℝ)
          * ((((2 * m + 1 : ℕ)) : ℝ)) ^ ((1 / 2 : ℝ))
        = ((((2 * m + 1 : ℕ)) : ℝ)) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_add ha]
      congr 1
      norm_num
    have h2 : ((((2 * m + 1 : ℕ)) : ℝ)) * Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
        = ((((2 * m + 1 : ℕ)) : ℝ)) ^ (1 : ℝ)
          * ((((2 * m + 1 : ℕ)) : ℝ)) ^ ((1 / 2 : ℝ)) := by
      rw [Real.rpow_one, Real.sqrt_eq_rpow]
    rw [h2]
    exact h1
  have hden_ge : 2 * ((((2 * m + 1 : ℕ)) : ℝ)) ^ (3 / 2 : ℝ)
      ≤ (Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
        + Real.sqrt ((((2 * m + 2 : ℕ)) : ℝ)))
        * (Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
          * Real.sqrt ((((2 * m + 2 : ℕ)) : ℝ))) := by
    have hA := hsum_ge
    have hB : Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
          * Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
        ≤ Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
          * Real.sqrt ((((2 * m + 2 : ℕ)) : ℝ)) :=
      mul_le_mul_of_nonneg_left hsqrt_le (Real.sqrt_nonneg _)
    have hC : (2 : ℝ) * ((((2 * m + 1 : ℕ)) : ℝ)) ^ (3 / 2 : ℝ)
        = (2 * Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ)))
          * (Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
            * Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))) := by
      have hsq1 : Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
            * Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
          = ((((2 * m + 1 : ℕ)) : ℝ)) := by
        rw [← Real.sqrt_mul (le_of_lt ha)]
        have e : ((((2 * m + 1 : ℕ)) : ℝ)) * ((((2 * m + 1 : ℕ)) : ℝ))
            = ((((2 * m + 1 : ℕ)) : ℝ)) ^ 2 := by ring
        rw [e, Real.sqrt_sq (le_of_lt ha)]
      have hrw : ((((2 * m + 1 : ℕ)) : ℝ)) ^ (3 / 2 : ℝ)
          = Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
            * (Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
              * Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))) := by
        rw [← hrpow, hsq1]
        ring
      rw [hrw]
      ring
    rw [hC]
    exact mul_le_mul hA hB
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (add_nonneg (le_of_lt (Real.sqrt_pos.mpr ha))
        (le_of_lt (Real.sqrt_pos.mpr hb)))
  have h2pos : (0 : ℝ) < 2 * ((((2 * m + 1 : ℕ)) : ℝ)) ^ (3 / 2 : ℝ) := by
    apply mul_pos (by norm_num)
    exact Real.rpow_pos_of_pos ha _
  have hexp : ((((2 * m + 1 : ℕ)) : ℝ)) ^ (-3 / 2 : ℝ)
      = (((((2 * m + 1 : ℕ)) : ℝ)) ^ (3 / 2 : ℝ))⁻¹ := by
    have eR : (-3 / 2 : ℝ) = -((3 / 2 : ℝ)) := by norm_num
    rw [eR]
    exact Real.rpow_neg (le_of_lt ha) _
  have e3 : (1 : ℝ) / (2 * ((((2 * m + 1 : ℕ)) : ℝ)) ^ (3 / 2 : ℝ))
      = (1 / 2) * (((((2 * m + 1 : ℕ)) : ℝ)) ^ (3 / 2 : ℝ))⁻¹ := by
    rw [one_div, mul_inv, one_div]
  have hmain : 1 / ((Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
        + Real.sqrt ((((2 * m + 2 : ℕ)) : ℝ)))
        * (Real.sqrt ((((2 * m + 1 : ℕ)) : ℝ))
          * Real.sqrt ((((2 * m + 2 : ℕ)) : ℝ))))
      ≤ (1 / 2) * ((((2 * m + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ)) := by
    rw [hexp, ← e3]
    exact one_div_le_one_div_of_le h2pos hden_ge
  simp only [etaPairR]
  rw [hform]
  exact hmain

/-- The real paired series is summable (M-test vs `p = 3/2 > 1`). -/
theorem summable_etaPairR : Summable etaPairR := by
  have hp : (1 : ℝ) < 3 / 2 := by norm_num
  have hbase : Summable (fun n : ℕ => ((((n : ℝ)) ^ (3 / 2 : ℝ)))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hp
  have hbaseS : Summable (fun m : ℕ => ((((m + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ))) := by
    have heq : (fun m : ℕ => ((((m + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ)))
        = (fun m : ℕ => ((((m + 1 : ℕ)) : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
      funext m
      have eR : (-3 / 2 : ℝ) = -((3 / 2 : ℝ)) := by norm_num
      rw [eR, Real.rpow_neg (Nat.cast_nonneg _)]
    rw [heq]
    exact (summable_nat_add_iff 1).mpr hbase
  have hC : Summable
      (fun m : ℕ => (1 / 2 : ℝ) * ((((m + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ))) :=
    hbaseS.mul_left _
  refine Summable.of_nonneg_of_le (fun m => etaPairR_nonneg m) (fun m => ?_) hC
  have h1 := etaPairR_upper m
  have hm : ((((m + 1 : ℕ)) : ℝ)) ≤ ((((2 * m + 1 : ℕ)) : ℝ)) :=
    Nat.cast_le.mpr (by omega)
  have hpos : (0 : ℝ) < ((((m + 1 : ℕ)) : ℝ)) := Nat.cast_pos.mpr (by omega)
  have hr : ((((2 * m + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ))
      ≤ ((((m + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hpos hm (by norm_num)
  calc etaPairR m ≤ (1 / 2) * ((((2 * m + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ)) := h1
    _ ≤ (1 / 2) * ((((m + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hr (by norm_num)

/-- Complex pairs at `s = 1/2` are the real pairs coerced
    (reuses `etaDirichletTerm_half_eq`, `etaDirichlet_even_partial`). -/
theorem etaPairTerm_half_eq (m : ℕ) :
    etaPairTerm (1 / 2 : ℂ) m = ((etaPairR m : ℝ) : ℂ) := by
  show etaDirichletTerm (1 / 2 : ℂ) (2 * m) + etaDirichletTerm (1 / 2 : ℂ) (2 * m + 1) = _
  rw [etaDirichletTerm_half_eq, etaDirichletTerm_half_eq]
  have e1 : (((-1 : ℤ) ^ (2 * m) : ℝ)) = 1 := by
    have h2 : (((-1 : ℤ) ^ (2 * m) : ℝ)) = (-1 : ℝ) ^ (2 * m) := by push_cast; ring
    rw [h2]
    exact Even.neg_one_pow ⟨m, by ring⟩
  have e2 : (((-1 : ℤ) ^ (2 * m + 1) : ℝ)) = -1 := by
    have h2 : (((-1 : ℤ) ^ (2 * m + 1) : ℝ)) = (-1 : ℝ) ^ (2 * m + 1) := by
      push_cast; ring
    rw [h2]
    exact Odd.neg_one_pow ⟨m, rfl⟩
  have ec1 : ((((2 * m : ℕ)) : ℝ) + 1) = ((((2 * m + 1 : ℕ)) : ℝ)) := by
    push_cast; ring
  have ec2 : ((((2 * m + 1 : ℕ)) : ℝ) + 1) = ((((2 * m + 2 : ℕ)) : ℝ)) := by
    push_cast; ring
  have hR : etaTerm (2 * m) + etaTerm (2 * m + 1) = etaPairR m := by
    simp only [etaTerm, etaPairR, e1, e2, ec1, ec2]
    ring
  simp only [etaTermℂ, ← Complex.ofReal_add, hR]

/-- Even real partials are sums of real pairs (via the complex transfer). -/
theorem etaPartial_even_eq (M : ℕ) :
    etaPartial (2 * M) = ∑ m ∈ Finset.range M, etaPairR m := by
  have h := etaDirichlet_even_partial (1 / 2 : ℂ) M
  have hLHS : (∑ k ∈ Finset.range (2 * M), etaDirichletTerm (1 / 2 : ℂ) k)
      = etaPartialℂ (2 * M) :=
    Finset.sum_congr rfl (fun k _ => etaDirichletTerm_half_eq k)
  have hRHS : (∑ m ∈ Finset.range M, etaPairTerm (1 / 2 : ℂ) m)
      = ((((∑ m ∈ Finset.range M, etaPairR m : ℝ))) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun m _ => etaPairTerm_half_eq m)
  rw [hLHS, hRHS, etaPartialℂ_eq_coe] at h
  exact Complex.ofReal_injective h

/-- Every `Tendsto` eta limit equals the real pair tsum. -/
theorem eta_limit_eq_pair_tsum (L : ℝ)
    (hL : Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L)) :
    L = ∑' m, etaPairR m := by
  have heq : (fun M : ℕ => etaPartial (2 * M))
      = (fun M : ℕ => ∑ i ∈ Finset.range (2 * M),
        ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ)) := by
    funext M
    simp only [etaPartial]
  have hev : Tendsto (fun M : ℕ => etaPartial (2 * M)) atTop (𝓝 L) := by
    rw [heq]
    exact hL.comp tendsto_two_mul_atTop
  have hpair : Tendsto (fun M : ℕ => ∑ m ∈ Finset.range M, etaPairR m)
      atTop (𝓝 (∑' m, etaPairR m)) :=
    summable_etaPairR.hasSum.tendsto_sum_nat
  have hsame : (fun M : ℕ => ∑ m ∈ Finset.range M, etaPairR m)
      = (fun M : ℕ => etaPartial (2 * M)) := by
    funext M
    exact (etaPartial_even_eq M).symm
  rw [hsame] at hpair
  exact tendsto_nhds_unique hev hpair

/-- Split: `L = S_{2M} + T_M` with `T_M = ∑'_{m} d_{m+M}`. -/
theorem eta_limit_split (L : ℝ) (M : ℕ)
    (hL : Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L)) :
    L = etaPartial (2 * M) + ∑' m, etaPairR (m + M) := by
  have hLtsum := eta_limit_eq_pair_tsum L hL
  have hsplit : (∑ m ∈ Finset.range M, etaPairR m) + (∑' m, etaPairR (m + M))
      = ∑' m, etaPairR m :=
    summable_etaPairR.sum_add_tsum_nat_add M
  have h3 : ∑ m ∈ Finset.range M, etaPairR m = etaPartial (2 * M) :=
    (etaPartial_even_eq M).symm
  linarith

/-- Upper telescope: consecutive gap-pairs telescope to `f(2M) - f(2M+2K)`. -/
theorem pairBlock_upper_telescope (M K : ℕ) :
    ∑ m ∈ Finset.range K, (etaGap (2 * (m + M)) + etaGap (2 * (m + M) + 1))
      = etaInvSqrt (2 * M) - etaInvSqrt (2 * M + 2 * K) := by
  induction K with
  | zero =>
    simp only [Finset.sum_range_zero]
    have e : 2 * M + 2 * 0 = 2 * M := by ring
    rw [e, sub_self]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [etaGap]
    have eA : 2 * (K + M) = 2 * M + 2 * K := by ring
    have eB : 2 * (K + M) + 1 = 2 * M + 2 * K + 1 := by ring
    have eC : 2 * (K + M) + 1 + 1 = 2 * M + 2 * K + 2 := by ring
    have eD : 2 * M + 2 * (K + 1) = 2 * M + 2 * K + 2 := by ring
    rw [eC, eB, eA, eD]
    ring

/-- Lower telescope: shifted gap-pairs telescope to `f(2M+1) - f(2M+2K+1)`. -/
theorem pairBlock_lower_telescope (M K : ℕ) :
    ∑ m ∈ Finset.range K, (etaGap (2 * (m + M) + 1) + etaGap (2 * (m + M) + 2))
      = etaInvSqrt (2 * M + 1) - etaInvSqrt (2 * M + 2 * K + 1) := by
  induction K with
  | zero =>
    simp only [Finset.sum_range_zero]
    have e : 2 * M + 2 * 0 + 1 = 2 * M + 1 := by ring
    rw [e, sub_self]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [etaGap]
    have eX : 2 * (K + M) = 2 * M + 2 * K := by ring
    have s1 : (2 * M + 2 * K) + 1 + 1 = 2 * M + 2 * K + 2 := by ring
    have s2 : (2 * M + 2 * K) + 2 + 1 = 2 * M + 2 * K + 3 := by ring
    have eE : 2 * M + 2 * (K + 1) + 1 = 2 * M + 2 * K + 3 := by ring
    rw [eX, s1, s2, eE]
    ring

/-- UPPER pair-tail bound (convexity telescoping): `T_M ≤ 1/(2√(2M))`.
    Asymptotically sharp. From `d_m = g_{2m+1} ≤ g_{2m}` the finite tail
    satisfies `2·Σ ≤ f(2M) - f(2M+2K) ≤ f(2M)`; pass to the limit. -/
theorem etaPair_tail_upper {M : ℕ} (hM : 1 ≤ M) :
    ∑' m, etaPairR (m + M) ≤ etaInvSqrt (2 * M) / 2 := by
  have hshift : Summable (fun m => etaPairR (m + M)) :=
    (summable_nat_add_iff M).mpr summable_etaPairR
  have hfin : ∀ K : ℕ, ∑ m ∈ Finset.range K, etaPairR (m + M)
      ≤ etaInvSqrt (2 * M) / 2 := by
    intro K
    have hterm : ∀ m : ℕ, 2 * etaPairR (m + M)
        ≤ etaGap (2 * (m + M)) + etaGap (2 * (m + M) + 1) := by
      intro m
      have hg : etaGap (2 * (m + M) + 1) ≤ etaGap (2 * (m + M)) :=
        etaGap_anti (show 1 ≤ 2 * (m + M) by omega)
      have hrel : etaPairR (m + M) = etaGap (2 * (m + M) + 1) :=
        etaPairR_eq_gap (m + M)
      linarith
    have hsum : ∑ m ∈ Finset.range K, (2 * etaPairR (m + M))
        ≤ ∑ m ∈ Finset.range K, (etaGap (2 * (m + M)) + etaGap (2 * (m + M) + 1)) :=
      Finset.sum_le_sum (fun m _ => hterm m)
    have h3 : ∑ m ∈ Finset.range K, (etaGap (2 * (m + M)) + etaGap (2 * (m + M) + 1))
        = etaInvSqrt (2 * M) - etaInvSqrt (2 * M + 2 * K) :=
      pairBlock_upper_telescope M K
    have h2 : 2 * (∑ m ∈ Finset.range K, etaPairR (m + M))
        = ∑ m ∈ Finset.range K, (2 * etaPairR (m + M)) := by
      rw [Finset.mul_sum]
    have hFnn : (0 : ℝ) ≤ etaInvSqrt (2 * M + 2 * K) := etaInvSqrt_nonneg _
    linarith
  have hlim : Tendsto (fun K => ∑ m ∈ Finset.range K, etaPairR (m + M))
      atTop (𝓝 (∑' m, etaPairR (m + M))) :=
    hshift.hasSum.tendsto_sum_nat
  exact le_of_tendsto hlim (Eventually.of_forall hfin)

/-- LOWER pair-tail bound (convexity telescoping): `1/(2√(2M+1)) ≤ T_M`.
    From `d_m ≥ (g_{2m+1}+g_{2m+2})/2` the finite tail satisfies
    `Σ ≥ (f(2M+1) - f(2M+2K+1))/2`; the subtrahend tends to `0`. -/
theorem etaPair_tail_lower {M : ℕ} (hM : 1 ≤ M) :
    etaInvSqrt (2 * M + 1) / 2 ≤ ∑' m, etaPairR (m + M) := by
  have hshift : Summable (fun m => etaPairR (m + M)) :=
    (summable_nat_add_iff M).mpr summable_etaPairR
  have hfin : ∀ K : ℕ, (etaInvSqrt (2 * M + 1) - etaInvSqrt (2 * M + 2 * K + 1)) / 2
      ≤ ∑ m ∈ Finset.range K, etaPairR (m + M) := by
    intro K
    have hterm : ∀ m : ℕ, (etaGap (2 * (m + M) + 1) + etaGap (2 * (m + M) + 2))
        ≤ 2 * etaPairR (m + M) := by
      intro m
      have hg : etaGap (2 * (m + M) + 2) ≤ etaGap (2 * (m + M) + 1) :=
        etaGap_anti (show 1 ≤ 2 * (m + M) + 1 by omega)
      have hrel : etaPairR (m + M) = etaGap (2 * (m + M) + 1) :=
        etaPairR_eq_gap (m + M)
      linarith
    have hsum : ∑ m ∈ Finset.range K,
          (etaGap (2 * (m + M) + 1) + etaGap (2 * (m + M) + 2))
        ≤ ∑ m ∈ Finset.range K, (2 * etaPairR (m + M)) :=
      Finset.sum_le_sum (fun m _ => hterm m)
    have h3 : ∑ m ∈ Finset.range K,
          (etaGap (2 * (m + M) + 1) + etaGap (2 * (m + M) + 2))
        = etaInvSqrt (2 * M + 1) - etaInvSqrt (2 * M + 2 * K + 1) :=
      pairBlock_lower_telescope M K
    have h2 : 2 * (∑ m ∈ Finset.range K, etaPairR (m + M))
        = ∑ m ∈ Finset.range K, (2 * etaPairR (m + M)) := by
      rw [Finset.mul_sum]
    linarith
  have hzero : Tendsto (fun K : ℕ => etaInvSqrt (2 * M + 2 * K + 1)) atTop (𝓝 0) := by
    have heq : (fun K : ℕ => etaInvSqrt (2 * M + 2 * K + 1))
        = (fun K : ℕ => 1 / Real.sqrt ((((2 * (M + K) : ℕ)) : ℝ) + 1)) := by
      funext K
      simp only [etaInvSqrt]
      congr 1
      congr 1
      have eN : 2 * M + 2 * K + 1 = 2 * (M + K) + 1 := by ring
      rw [eN]
      push_cast
      ring
    rw [heq]
    have hmap : Tendsto (fun K : ℕ => 2 * (M + K)) atTop atTop := by
      apply Filter.tendsto_atTop_mono (fun K => show K ≤ 2 * (M + K) by omega)
      exact Filter.tendsto_id
    have hcomp := eta_terms_tendsto_zero.comp hmap
    simpa [Function.comp_def] using hcomp
  have hclim : Tendsto
      (fun K : ℕ => (etaInvSqrt (2 * M + 1) - etaInvSqrt (2 * M + 2 * K + 1)) / 2)
      atTop (𝓝 (etaInvSqrt (2 * M + 1) / 2)) := by
    have h1 : Tendsto (fun K : ℕ => etaInvSqrt (2 * M + 1) - etaInvSqrt (2 * M + 2 * K + 1))
        atTop (𝓝 (etaInvSqrt (2 * M + 1) - 0)) :=
      tendsto_const_nhds.sub hzero
    have h2 := h1.div_const (2 : ℝ)
    simpa using h2
  have hTall : ∀ K : ℕ, (etaInvSqrt (2 * M + 1) - etaInvSqrt (2 * M + 2 * K + 1)) / 2
      ≤ ∑' m, etaPairR (m + M) := by
    intro K
    have hPK := hfin K
    have hPT : ∑ m ∈ Finset.range K, etaPairR (m + M) ≤ ∑' m, etaPairR (m + M) :=
      Summable.sum_le_tsum (Finset.range K) (fun m _ => etaPairR_nonneg _) hshift
    linarith
  exact le_of_tendsto hclim (Eventually.of_forall hTall)

/-- Majorant `x^{-3/2}` antitone on `Ici M` (`1 ≤ M`)
    (mirrors `R00EtaConv.majorant_antitone`). -/
theorem etaMajorant_antitone {M : ℕ} (hM : 1 ≤ M) :
    AntitoneOn (fun x : ℝ => x ^ (-3 / 2 : ℝ)) (Set.Ici ((((M : ℕ)) : ℝ))) := by
  apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono
  intro x hx
  have hM0 : (0 : ℝ) < ((((M : ℕ)) : ℝ)) := by exact_mod_cast (by omega : 0 < M)
  simp only [Set.mem_Ici] at hx
  simp only [Set.mem_Ioi]
  linarith

/-- Majorant integrable on `Ioi M`. -/
theorem etaMajorant_integrable {M : ℕ} (hM : 1 ≤ M) :
    MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-3 / 2 : ℝ))
      (Set.Ioi ((((M : ℕ)) : ℝ))) :=
  integrableOn_Ioi_rpow_of_lt (by norm_num)
    (by exact_mod_cast (by omega : 0 < M))

/-- Majorant nonnegative on `Ioi M`. -/
theorem etaMajorant_nonneg {M : ℕ} :
    ∀ t ∈ Set.Ioi ((((M : ℕ)) : ℝ)), (0 : ℝ) ≤ t ^ (-3 / 2 : ℝ) := by
  intro t ht
  exact Real.rpow_nonneg
    (le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg _) (Set.mem_Ioi.mp ht))) _

/-- Integral value `∫_{M}^{∞} x^{-3/2} = 2/√M` (mirrors
    `R00EtaConv.majorant_integral_le`, here exact). -/
theorem etaMajorant_integral {M : ℕ} (hM : 1 ≤ M) :
    (∫ x : ℝ in Set.Ioi ((((M : ℕ)) : ℝ)), x ^ (-3 / 2 : ℝ))
      = 2 / Real.sqrt ((((M : ℕ)) : ℝ)) := by
  have hM0 : (0 : ℝ) < ((((M : ℕ)) : ℝ)) := by exact_mod_cast (by omega : 0 < M)
  have h := integral_Ioi_rpow_of_lt (a := (-3 / 2 : ℝ)) (by norm_num)
    (c := ((((M : ℕ)) : ℝ))) hM0
  rw [h]
  have e : (-3 / 2 : ℝ) + 1 = -(1 / 2 : ℝ) := by norm_num
  rw [e]
  have hMne : Real.sqrt ((((M : ℕ)) : ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hM0)
  have er : ((((M : ℕ)) : ℝ)) ^ (-(1 / 2 : ℝ)) = (Real.sqrt ((((M : ℕ)) : ℝ)))⁻¹ := by
    rw [Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow]
  rw [er]
  field_simp

/-- INTEGRAL pair-tail bound: `T_M ≤ 1/√M` (explicit `C = 1`), via
    `AntetoneOn.tsum_comp_add_le_integral` — the required bound of the form
    `‖L - S_N‖ ≤ C/√N` (here `N = 2M`, so `C = √2` in `C/√N`). -/
theorem etaPair_tail_integral {M : ℕ} (hM : 1 ≤ M) :
    ∑' m, etaPairR (m + M) ≤ 1 / Real.sqrt ((((M : ℕ)) : ℝ)) := by
  have hbase : Summable (fun n : ℕ => ((((n : ℝ)) ^ (3 / 2 : ℝ)))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  have hshift : Summable (fun m => etaPairR (m + M)) :=
    (summable_nat_add_iff M).mpr summable_etaPairR
  have hbaseS : Summable (fun m : ℕ => ((((m + M + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ))) := by
    have heq : (fun m : ℕ => ((((m + M + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ)))
        = (fun m : ℕ => ((((m + (M + 1) : ℕ)) : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
      funext m
      have eN : m + M + 1 = m + (M + 1) := by omega
      rw [eN]
      have eR : (-3 / 2 : ℝ) = -((3 / 2 : ℝ)) := by norm_num
      rw [eR, Real.rpow_neg (Nat.cast_nonneg _)]
    rw [heq]
    exact (summable_nat_add_iff (f := fun n : ℕ => ((((n : ℝ)) ^ (3 / 2 : ℝ)))⁻¹)
      (M + 1)).mpr hbase
  have hC : Summable
      (fun m : ℕ => (1 / 2 : ℝ) * ((((m + M + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ))) :=
    hbaseS.mul_left _
  have hpt : ∀ m : ℕ, etaPairR (m + M)
      ≤ (1 / 2 : ℝ) * ((((m + M + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ)) := by
    intro m
    have h1 := etaPairR_upper (m + M)
    have hle : ((((m + M + 1 : ℕ)) : ℝ)) ≤ ((((2 * (m + M) + 1 : ℕ)) : ℝ)) := by
      apply Nat.cast_le.mpr
      omega
    have hpos : (0 : ℝ) < ((((m + M + 1 : ℕ)) : ℝ)) := Nat.cast_pos.mpr (by omega)
    have hr : ((((2 * (m + M) + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ))
        ≤ ((((m + M + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)
    calc etaPairR (m + M)
        ≤ (1 / 2) * ((((2 * (m + M) + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ)) := h1
      _ ≤ (1 / 2) * ((((m + M + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hr (by norm_num)
  have hle_tsum : (∑' m, etaPairR (m + M))
      ≤ (∑' m, (1 / 2 : ℝ) * ((((m + M + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ))) :=
    hshift.tsum_le_tsum hpt hC
  have hfactor : (∑' m, (1 / 2 : ℝ) * ((((m + M + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ)))
      = (1 / 2) * (∑' m, ((((m + M + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ))) :=
    Summable.tsum_mul_left _ hbaseS
  have hint : (∑' n : ℕ, ((((n + M + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ)))
      ≤ (∫ x : ℝ in Set.Ioi ((((M : ℕ)) : ℝ)), x ^ (-3 / 2 : ℝ)) :=
    AntitoneOn.tsum_comp_add_le_integral (N := M) (f := fun x : ℝ => x ^ (-3 / 2 : ℝ))
      (etaMajorant_antitone hM) (etaMajorant_integrable hM) (etaMajorant_nonneg)
  rw [hfactor] at hle_tsum
  have hval := etaMajorant_integral hM
  rw [hval] at hint
  have ehalf : (1 / 2 : ℝ) * (2 / Real.sqrt ((((M : ℕ)) : ℝ)))
      = 1 / Real.sqrt ((((M : ℕ)) : ℝ)) := by ring
  have h2 : (1 / 2 : ℝ) * (∑' m, ((((m + M + 1 : ℕ)) : ℝ) ^ (-3 / 2 : ℝ)))
      ≤ (1 / 2) * (2 / Real.sqrt ((((M : ℕ)) : ℝ))) :=
    mul_le_mul_of_nonneg_left hint (by norm_num)
  rw [ehalf] at h2
  exact hle_tsum.trans h2

/-- Packaged integral remainder: `‖L - S_{2M}‖ ≤ 1/√M` (`M ≥ 1`). -/
theorem eta_limit_norm_sub_le {M : ℕ} (hM : 1 ≤ M) (L : ℝ)
    (hL : Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L)) :
    ‖L - etaPartial (2 * M)‖ ≤ 1 / Real.sqrt ((((M : ℕ)) : ℝ)) := by
  have hsplit := eta_limit_split L M hL
  have hT := etaPair_tail_integral hM
  have hTnn : (0 : ℝ) ≤ ∑' m, etaPairR (m + M) :=
    tsum_nonneg (fun m => etaPairR_nonneg _)
  have e : L - etaPartial (2 * M) = ∑' m, etaPairR (m + M) := by linarith
  rw [e, Real.norm_eq_abs, abs_of_nonneg hTnn]
  exact hT

/-- Rigorous `√2` enclosure (3 decimals). -/
theorem sqrt2_bounds : (1.414 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.415 := by
  refine ⟨?_, ?_⟩
  · calc (1.414 : ℝ) = Real.sqrt (1.414 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · calc Real.sqrt 2 < Real.sqrt (1.415 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 1.415 := Real.sqrt_sq (by norm_num)

/-- Rigorous `√3` enclosure. -/
theorem sqrt3_bounds : (1.732 : ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < 1.733 := by
  refine ⟨?_, ?_⟩
  · calc (1.732 : ℝ) = Real.sqrt (1.732 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · calc Real.sqrt 3 < Real.sqrt (1.733 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 1.733 := Real.sqrt_sq (by norm_num)

/-- Rigorous `√5` enclosure. -/
theorem sqrt5_bounds : (2.236 : ℝ) < Real.sqrt 5 ∧ Real.sqrt 5 < 2.237 := by
  refine ⟨?_, ?_⟩
  · calc (2.236 : ℝ) = Real.sqrt (2.236 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · calc Real.sqrt 5 < Real.sqrt (2.237 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 2.237 := Real.sqrt_sq (by norm_num)

/-- Rigorous `√6` enclosure. -/
theorem sqrt6_bounds : (2.449 : ℝ) < Real.sqrt 6 ∧ Real.sqrt 6 < 2.450 := by
  refine ⟨?_, ?_⟩
  · calc (2.449 : ℝ) = Real.sqrt (2.449 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 6 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · calc Real.sqrt 6 < Real.sqrt (2.450 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 2.450 := Real.sqrt_sq (by norm_num)

/-- Rigorous `√7` enclosure. -/
theorem sqrt7_bounds : (2.645 : ℝ) < Real.sqrt 7 ∧ Real.sqrt 7 < 2.646 := by
  refine ⟨?_, ?_⟩
  · calc (2.645 : ℝ) = Real.sqrt (2.645 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 7 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · calc Real.sqrt 7 < Real.sqrt (2.646 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 2.646 := Real.sqrt_sq (by norm_num)

/-- Rigorous `√8` enclosure. -/
theorem sqrt8_bounds : (2.828 : ℝ) < Real.sqrt 8 ∧ Real.sqrt 8 < 2.829 := by
  refine ⟨?_, ?_⟩
  · calc (2.828 : ℝ) = Real.sqrt (2.828 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 8 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · calc Real.sqrt 8 < Real.sqrt (2.829 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 2.829 := Real.sqrt_sq (by norm_num)

/-- Explicit lower enclosure `0.4328 ≤ S₈`. -/
theorem etaPartial_eight_lo : (0.4328 : ℝ) ≤ etaPartial 8 := by
  rw [etaPartial_eight_eq]
  have t2 : 1 / Real.sqrt 2 ≤ 1 / 1.414 :=
    one_div_le_one_div_of_le (by norm_num) sqrt2_bounds.1.le
  have t3 : 1 / 1.733 ≤ 1 / Real.sqrt 3 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt3_bounds.2.le
  have t5 : 1 / 2.237 ≤ 1 / Real.sqrt 5 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt5_bounds.2.le
  have t6 : 1 / Real.sqrt 6 ≤ 1 / 2.449 :=
    one_div_le_one_div_of_le (by norm_num) sqrt6_bounds.1.le
  have t7 : 1 / 2.646 ≤ 1 / Real.sqrt 7 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt7_bounds.2.le
  have t8 : 1 / Real.sqrt 8 ≤ 1 / 2.828 :=
    one_div_le_one_div_of_le (by norm_num) sqrt8_bounds.1.le
  have h4 : (1 : ℝ) / Real.sqrt 4 = 1 / 2 := by
    rw [sqrt_four_eq]
  have num : (0.4328 : ℝ)
      ≤ 1 - 1 / 1.414 + 1 / 1.733 - 1 / 2 + 1 / 2.237 - 1 / 2.449 + 1 / 2.646
        - 1 / 2.828 := by
    norm_num
  linarith

/-- Explicit upper enclosure `S₈ ≤ 0.4344`. -/
theorem etaPartial_eight_hi : etaPartial 8 ≤ (0.4344 : ℝ) := by
  rw [etaPartial_eight_eq]
  have t2 : 1 / 1.415 ≤ 1 / Real.sqrt 2 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt2_bounds.2.le
  have t3 : 1 / Real.sqrt 3 ≤ 1 / 1.732 :=
    one_div_le_one_div_of_le (by norm_num) sqrt3_bounds.1.le
  have t5 : 1 / Real.sqrt 5 ≤ 1 / 2.236 :=
    one_div_le_one_div_of_le (by norm_num) sqrt5_bounds.1.le
  have t6 : 1 / 2.450 ≤ 1 / Real.sqrt 6 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt6_bounds.2.le
  have t7 : 1 / Real.sqrt 7 ≤ 1 / 2.645 :=
    one_div_le_one_div_of_le (by norm_num) sqrt7_bounds.1.le
  have t8 : 1 / 2.829 ≤ 1 / Real.sqrt 8 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt8_bounds.2.le
  have h4 : (1 : ℝ) / Real.sqrt 4 = 1 / 2 := by
    rw [sqrt_four_eq]
  have num : 1 - 1 / 1.415 + 1 / 1.732 - 1 / 2 + 1 / 2.236 - 1 / 2.450 + 1 / 2.645
        - 1 / 2.829 ≤ (0.4344 : ℝ) := by
    norm_num
  linarith

/-- Tail lower bound at `M = 4`: `T₄ ≥ 1/6` (since `f(9)/2 = 1/6`). -/
theorem etaPair_tail4_lower : (1 / 6 : ℝ) ≤ ∑' m, etaPairR (m + 4) := by
  have h := etaPair_tail_lower (M := 4) (by norm_num)
  have e : etaInvSqrt (2 * 4 + 1) = 1 / 3 := by
    have e9 : ((((2 * 4 + 1 : ℕ)) : ℝ)) = (9 : ℝ) := by norm_num
    show 1 / Real.sqrt ((((2 * 4 + 1 : ℕ)) : ℝ)) = 1 / 3
    rw [e9, sqrt_nine_eq]
  rw [e] at h
  linarith

/-- Tail upper bound at `M = 4`: `T₄ ≤ 0.177` (since `1/(2√8) ≤ 1/5.656`). -/
theorem etaPair_tail4_upper : (∑' m, etaPairR (m + 4)) ≤ (0.177 : ℝ) := by
  have h := etaPair_tail_upper (M := 4) (by norm_num)
  have e : etaInvSqrt (2 * 4) = 1 / Real.sqrt 8 := by
    have e8 : ((((2 * 4 : ℕ)) : ℝ)) = (8 : ℝ) := by norm_num
    show 1 / Real.sqrt ((((2 * 4 : ℕ)) : ℝ)) = 1 / Real.sqrt 8
    rw [e8]
  rw [e] at h
  have t8 : 1 / Real.sqrt 8 ≤ 1 / 2.828 :=
    one_div_le_one_div_of_le (by norm_num) sqrt8_bounds.1.le
  have num : (1 / 2.828 : ℝ) / 2 ≤ 0.177 := by norm_num
  linarith

/-- `L = S₈ + T₄` for every `Tendsto` eta limit. -/
theorem eta_limit_S8_split (L : ℝ)
    (hL : Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L)) :
    L = etaPartial 8 + ∑' m, etaPairR (m + 4) := by
  have h := eta_limit_split L 4 hL
  have e : (2 * 4 : ℕ) = 8 := by norm_num
  rw [e] at h
  exact h

/-- BEST two-sided eta interval: `L ∈ [0.5994, 0.6114]` (width `0.012`).
    Downstream-ready feeder for the `Λ₀(1/2)` separation. -/
theorem eta_half_tight_best :
    ∃ L : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L) ∧ (0.5994 : ℝ) ≤ L ∧ L ≤ (0.6114 : ℝ) ∧ 0 < L := by
  obtain ⟨L, hL, hpos⟩ := eta_half_pos
  refine ⟨L, hL, ?_, ?_, hpos⟩
  · have hS := eta_limit_S8_split L hL
    have hlo := etaPartial_eight_lo
    have ht := etaPair_tail4_lower
    linarith
  · have hS := eta_limit_S8_split L hL
    have hhi := etaPartial_eight_hi
    have ht := etaPair_tail4_upper
    linarith

/-- Exact width of the best interval: `0.012 ≤ 0.05`. -/
theorem eta_tight_best_width : (0.6114 : ℝ) - (0.5994 : ℝ) = 0.012 := by norm_num

#print axioms sqrt_convex_step
#print axioms etaPairR_upper
#print axioms summable_etaPairR
#print axioms etaPartial_even_eq
#print axioms eta_limit_eq_pair_tsum
#print axioms etaPair_tail_upper
#print axioms etaPair_tail_lower
#print axioms etaPair_tail_integral
#print axioms eta_limit_norm_sub_le
#print axioms eta_half_tight_best
#print axioms eta_tight_best_width

/-!
## M = 8 telescoping tightening: `L ∈ [0.6029, 0.6070]` (width `0.0041 ≤ 0.006`).

Pushes the sharp convexity telescoping `1/(2√(2M+1)) ≤ T_M ≤ 1/(2√(2M))`
(`etaPair_tail_lower/upper`) from `M = 4` to `M = 8` (i.e. `N = 16`).
`2M = 16` is a perfect square, so the UPPER tail is EXACT (`1/8`);
the LOWER tail needs only a `√17` upper enclosure.
`S₁₆` needs `√`-enclosures up to `√17` (exact squares `1,4,9,16` free).
Reuses the committed `√2..√8` 3-decimal pattern with 4-decimal (or better)
enclosures proved by exact square comparisons (`norm_num`), same as
`sqrt2_bounds..sqrt8_bounds`. Only the `Tendsto` form is used.
Gives `±0.00205`, beating the downstream `±0.003` (width `0.006`) need.
The integral bound (`etaPair_tail_integral`, `T₈ ≤ 1/√8 ≈ 0.354`) is far
weaker here and is NOT used for the final interval (recorded only for comparison).
-/

/-- `√16 = 4` (exact; makes the `M = 8` upper tail exact). -/
theorem sqrt_sixteen_eq : Real.sqrt (16 : ℝ) = 4 := by
  rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Rigorous `√2` enclosure (4 decimals, tighter, new name — old lemma untouched). -/
theorem sqrt2_bounds4 : (1.4142 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.4143 := by
  refine ⟨?_, ?_⟩
  · calc (1.4142 : ℝ) = Real.sqrt (1.4142 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · calc Real.sqrt 2 < Real.sqrt (1.4143 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 1.4143 := Real.sqrt_sq (by norm_num)

/-- Rigorous `√3` enclosure (4 decimals). -/
theorem sqrt3_bounds4 : (1.7320 : ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < 1.7321 := by
  refine ⟨?_, ?_⟩
  · calc (1.7320 : ℝ) = Real.sqrt (1.7320 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · calc Real.sqrt 3 < Real.sqrt (1.7321 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 1.7321 := Real.sqrt_sq (by norm_num)

/-- Rigorous `√5` enclosure (4 decimals). -/
theorem sqrt5_bounds4 : (2.2360 : ℝ) < Real.sqrt 5 ∧ Real.sqrt 5 < 2.2361 := by
  refine ⟨?_, ?_⟩
  · calc (2.2360 : ℝ) = Real.sqrt (2.2360 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · calc Real.sqrt 5 < Real.sqrt (2.2361 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 2.2361 := Real.sqrt_sq (by norm_num)

/-- Rigorous `√6` enclosure (4 decimals). -/
theorem sqrt6_bounds4 : (2.4494 : ℝ) < Real.sqrt 6 ∧ Real.sqrt 6 < 2.4495 := by
  refine ⟨?_, ?_⟩
  · calc (2.4494 : ℝ) = Real.sqrt (2.4494 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 6 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · calc Real.sqrt 6 < Real.sqrt (2.4495 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 2.4495 := Real.sqrt_sq (by norm_num)

/-- Rigorous `√7` enclosure (4 decimals). -/
theorem sqrt7_bounds4 : (2.6457 : ℝ) < Real.sqrt 7 ∧ Real.sqrt 7 < 2.6458 := by
  refine ⟨?_, ?_⟩
  · calc (2.6457 : ℝ) = Real.sqrt (2.6457 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 7 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · calc Real.sqrt 7 < Real.sqrt (2.6458 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 2.6458 := Real.sqrt_sq (by norm_num)

/-- Rigorous `√8` enclosure (4 decimals). -/
theorem sqrt8_bounds4 : (2.8284 : ℝ) < Real.sqrt 8 ∧ Real.sqrt 8 < 2.8285 := by
  refine ⟨?_, ?_⟩
  · calc (2.8284 : ℝ) = Real.sqrt (2.8284 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 8 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · calc Real.sqrt 8 < Real.sqrt (2.8285 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 2.8285 := Real.sqrt_sq (by norm_num)

/-- Rigorous `√10` enclosure (4 decimals). -/
theorem sqrt10_bounds : (3.1622 : ℝ) < Real.sqrt 10 ∧ Real.sqrt 10 < 3.1623 := by
  refine ⟨?_, ?_⟩
  · calc (3.1622 : ℝ) = Real.sqrt (3.1622 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 10 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · calc Real.sqrt 10 < Real.sqrt (3.1623 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 3.1623 := Real.sqrt_sq (by norm_num)

/-- Rigorous `√11` enclosure (4 decimals). -/
theorem sqrt11_bounds : (3.3166 : ℝ) < Real.sqrt 11 ∧ Real.sqrt 11 < 3.3167 := by
  refine ⟨?_, ?_⟩
  · calc (3.3166 : ℝ) = Real.sqrt (3.3166 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 11 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · calc Real.sqrt 11 < Real.sqrt (3.3167 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 3.3167 := Real.sqrt_sq (by norm_num)

/-- Rigorous `√12` enclosure (4 decimals). -/
theorem sqrt12_bounds : (3.4641 : ℝ) < Real.sqrt 12 ∧ Real.sqrt 12 < 3.4642 := by
  refine ⟨?_, ?_⟩
  · calc (3.4641 : ℝ) = Real.sqrt (3.4641 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 12 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · calc Real.sqrt 12 < Real.sqrt (3.4642 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 3.4642 := Real.sqrt_sq (by norm_num)

/-- Rigorous `√13` enclosure (4 decimals). -/
theorem sqrt13_bounds : (3.6055 : ℝ) < Real.sqrt 13 ∧ Real.sqrt 13 < 3.6056 := by
  refine ⟨?_, ?_⟩
  · calc (3.6055 : ℝ) = Real.sqrt (3.6055 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 13 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · calc Real.sqrt 13 < Real.sqrt (3.6056 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 3.6056 := Real.sqrt_sq (by norm_num)

/-- Rigorous `√14` enclosure (4 decimals). -/
theorem sqrt14_bounds : (3.7416 : ℝ) < Real.sqrt 14 ∧ Real.sqrt 14 < 3.7417 := by
  refine ⟨?_, ?_⟩
  · calc (3.7416 : ℝ) = Real.sqrt (3.7416 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 14 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · calc Real.sqrt 14 < Real.sqrt (3.7417 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 3.7417 := Real.sqrt_sq (by norm_num)

/-- Rigorous `√15` enclosure (4 decimals). -/
theorem sqrt15_bounds : (3.8729 : ℝ) < Real.sqrt 15 ∧ Real.sqrt 15 < 3.8730 := by
  refine ⟨?_, ?_⟩
  · calc (3.8729 : ℝ) = Real.sqrt (3.8729 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 15 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · calc Real.sqrt 15 < Real.sqrt (3.8730 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 3.8730 := Real.sqrt_sq (by norm_num)

/-- Rigorous `√17` enclosure (4 decimals; only the upper bound feeds the `M = 8` tail). -/
theorem sqrt17_bounds : (4.1231 : ℝ) < Real.sqrt 17 ∧ Real.sqrt 17 < 4.1232 := by
  refine ⟨?_, ?_⟩
  · calc (4.1231 : ℝ) = Real.sqrt (4.1231 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt 17 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · calc Real.sqrt 17 < Real.sqrt (4.1232 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 4.1232 := Real.sqrt_sq (by norm_num)

/-- Exact `S₁₆` (squares `4, 9, 16` written as `1/2, 1/3, 1/4`). -/
theorem etaPartial_sixteen_eq :
    etaPartial 16
      = 1 - 1 / Real.sqrt 2 + 1 / Real.sqrt 3 - 1 / 2 + 1 / Real.sqrt 5
        - 1 / Real.sqrt 6 + 1 / Real.sqrt 7 - 1 / Real.sqrt 8 + 1 / 3
        - 1 / Real.sqrt 10 + 1 / Real.sqrt 11 - 1 / Real.sqrt 12
        + 1 / Real.sqrt 13 - 1 / Real.sqrt 14 + 1 / Real.sqrt 15 - 1 / 4 := by
  simp [etaPartial, Finset.sum_range_succ, Real.sqrt_one]
  ring_nf

/-- Explicit lower enclosure `0.4817 ≤ S₁₆` (4-decimal `√`-bounds). -/
theorem etaPartial_sixteen_lo : (0.4817 : ℝ) ≤ etaPartial 16 := by
  rw [etaPartial_sixteen_eq]
  have t2 : 1 / Real.sqrt 2 ≤ 1 / 1.4142 :=
    one_div_le_one_div_of_le (by norm_num) sqrt2_bounds4.1.le
  have t3 : 1 / 1.7321 ≤ 1 / Real.sqrt 3 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt3_bounds4.2.le
  have t5 : 1 / 2.2361 ≤ 1 / Real.sqrt 5 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt5_bounds4.2.le
  have t6 : 1 / Real.sqrt 6 ≤ 1 / 2.4494 :=
    one_div_le_one_div_of_le (by norm_num) sqrt6_bounds4.1.le
  have t7 : 1 / 2.6458 ≤ 1 / Real.sqrt 7 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt7_bounds4.2.le
  have t8 : 1 / Real.sqrt 8 ≤ 1 / 2.8284 :=
    one_div_le_one_div_of_le (by norm_num) sqrt8_bounds4.1.le
  have t10 : 1 / Real.sqrt 10 ≤ 1 / 3.1622 :=
    one_div_le_one_div_of_le (by norm_num) sqrt10_bounds.1.le
  have t11 : 1 / 3.3167 ≤ 1 / Real.sqrt 11 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt11_bounds.2.le
  have t12 : 1 / Real.sqrt 12 ≤ 1 / 3.4641 :=
    one_div_le_one_div_of_le (by norm_num) sqrt12_bounds.1.le
  have t13 : 1 / 3.6056 ≤ 1 / Real.sqrt 13 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt13_bounds.2.le
  have t14 : 1 / Real.sqrt 14 ≤ 1 / 3.7416 :=
    one_div_le_one_div_of_le (by norm_num) sqrt14_bounds.1.le
  have t15 : 1 / 3.8730 ≤ 1 / Real.sqrt 15 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt15_bounds.2.le
  have num : (0.4817 : ℝ)
      ≤ 1 - 1 / 1.4142 + 1 / 1.7321 - 1 / 2 + 1 / 2.2361 - 1 / 2.4494
        + 1 / 2.6458 - 1 / 2.8284 + 1 / 3 - 1 / 3.1622 + 1 / 3.3167
        - 1 / 3.4641 + 1 / 3.6056 - 1 / 3.7416 + 1 / 3.8730 - 1 / 4 := by
    norm_num
  linarith

/-- Explicit upper enclosure `S₁₆ ≤ 0.4820`. -/
theorem etaPartial_sixteen_hi : etaPartial 16 ≤ (0.4820 : ℝ) := by
  rw [etaPartial_sixteen_eq]
  have t2 : 1 / 1.4143 ≤ 1 / Real.sqrt 2 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt2_bounds4.2.le
  have t3 : 1 / Real.sqrt 3 ≤ 1 / 1.7320 :=
    one_div_le_one_div_of_le (by norm_num) sqrt3_bounds4.1.le
  have t5 : 1 / Real.sqrt 5 ≤ 1 / 2.2360 :=
    one_div_le_one_div_of_le (by norm_num) sqrt5_bounds4.1.le
  have t6 : 1 / 2.4495 ≤ 1 / Real.sqrt 6 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt6_bounds4.2.le
  have t7 : 1 / Real.sqrt 7 ≤ 1 / 2.6457 :=
    one_div_le_one_div_of_le (by norm_num) sqrt7_bounds4.1.le
  have t8 : 1 / 2.8285 ≤ 1 / Real.sqrt 8 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt8_bounds4.2.le
  have t10 : 1 / 3.1623 ≤ 1 / Real.sqrt 10 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt10_bounds.2.le
  have t11 : 1 / Real.sqrt 11 ≤ 1 / 3.3166 :=
    one_div_le_one_div_of_le (by norm_num) sqrt11_bounds.1.le
  have t12 : 1 / 3.4642 ≤ 1 / Real.sqrt 12 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt12_bounds.2.le
  have t13 : 1 / Real.sqrt 13 ≤ 1 / 3.6055 :=
    one_div_le_one_div_of_le (by norm_num) sqrt13_bounds.1.le
  have t14 : 1 / 3.7417 ≤ 1 / Real.sqrt 14 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt14_bounds.2.le
  have t15 : 1 / Real.sqrt 15 ≤ 1 / 3.8729 :=
    one_div_le_one_div_of_le (by norm_num) sqrt15_bounds.1.le
  have num : 1 - 1 / 1.4143 + 1 / 1.7320 - 1 / 2 + 1 / 2.2360 - 1 / 2.4495
        + 1 / 2.6457 - 1 / 2.8285 + 1 / 3 - 1 / 3.1623 + 1 / 3.3166
        - 1 / 3.4642 + 1 / 3.6055 - 1 / 3.7417 + 1 / 3.8729 - 1 / 4
        ≤ (0.4820 : ℝ) := by
    norm_num
  linarith

/-- Tail lower bound at `M = 8`: `T₈ ≥ 0.1212` (since `f(17)/2 ≥ 1/(2·4.1232)`). -/
theorem etaPair_tail8_lower : (0.1212 : ℝ) ≤ ∑' m, etaPairR (m + 8) := by
  have h := etaPair_tail_lower (M := 8) (by norm_num)
  have e : etaInvSqrt (2 * 8 + 1) = 1 / Real.sqrt 17 := by
    have e17 : ((((2 * 8 + 1 : ℕ)) : ℝ)) = (17 : ℝ) := by norm_num
    show 1 / Real.sqrt ((((2 * 8 + 1 : ℕ)) : ℝ)) = 1 / Real.sqrt 17
    rw [e17]
  rw [e] at h
  have t17 : 1 / 4.1232 ≤ 1 / Real.sqrt 17 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt17_bounds.2.le
  have num : (0.1212 : ℝ) ≤ (1 / 4.1232) / 2 := by norm_num
  linarith

/-- Tail upper bound at `M = 8`: `T₈ ≤ 0.125` (exact, since `√16 = 4`). -/
theorem etaPair_tail8_upper : (∑' m, etaPairR (m + 8)) ≤ (0.125 : ℝ) := by
  have h := etaPair_tail_upper (M := 8) (by norm_num)
  have e : etaInvSqrt (2 * 8) = 1 / 4 := by
    have e16 : ((((2 * 8 : ℕ)) : ℝ)) = (16 : ℝ) := by norm_num
    show 1 / Real.sqrt ((((2 * 8 : ℕ)) : ℝ)) = 1 / 4
    rw [e16, sqrt_sixteen_eq]
  rw [e] at h
  have num : ((1 : ℝ) / 4) / 2 ≤ 0.125 := by norm_num
  linarith

/-- `L = S₁₆ + T₈` for every `Tendsto` eta limit. -/
theorem eta_limit_S16_split (L : ℝ)
    (hL : Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L)) :
    L = etaPartial 16 + ∑' m, etaPairR (m + 8) := by
  have h := eta_limit_split L 8 hL
  have e : (2 * 8 : ℕ) = 16 := by norm_num
  rw [e] at h
  exact h

/-- BEST2 two-sided eta interval: `L ∈ [0.6029, 0.6070]` (width `0.0041 ≤ 0.006`).
    Downstream-ready feeder for the `Λ₀(1/2)` separation (`±0.003`). -/
theorem eta_half_tight_best2 :
    ∃ L : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i : ℝ) / sqrt (i + 1 : ℝ))
      atTop (𝓝 L) ∧ (0.6029 : ℝ) ≤ L ∧ L ≤ (0.6070 : ℝ) ∧ 0 < L := by
  obtain ⟨L, hL, hpos⟩ := eta_half_pos
  refine ⟨L, hL, ?_, ?_, hpos⟩
  · have hS := eta_limit_S16_split L hL
    have hlo := etaPartial_sixteen_lo
    have ht := etaPair_tail8_lower
    linarith
  · have hS := eta_limit_S16_split L hL
    have hhi := etaPartial_sixteen_hi
    have ht := etaPair_tail8_upper
    linarith

/-- Exact width of the `best2` interval: `0.0041 ≤ 0.006` (`±0.00205`). -/
theorem eta_tight_best2_width : (0.6070 : ℝ) - (0.6029 : ℝ) = 0.0041 := by norm_num

#print axioms sqrt_sixteen_eq
#print axioms sqrt10_bounds
#print axioms sqrt17_bounds
#print axioms etaPartial_sixteen_eq
#print axioms etaPartial_sixteen_lo
#print axioms etaPartial_sixteen_hi
#print axioms etaPair_tail8_lower
#print axioms etaPair_tail8_upper
#print axioms eta_limit_S16_split
#print axioms eta_half_tight_best2
#print axioms eta_tight_best2_width

/-!
## ZETA-factor (1): general complex S_{2M} paired-tail remainder + explicit M with r ≤ 0.1

Grep documentation (searches run before writing; repo + Mathlib):
* `etaCvtFactor` — only in `interval_arith.lean` (R00ZetaEM section), no Mathlib hit; not imported here (avoids cycles), mirrored via existing `etaDirichletTerm` / `etaPairTerm` API in this file.
* `etaPartial` / `etaTerm` / `etaPartialℂ` — this file; complex `etaDirichletTerm` / `etaPairTerm` already general in this file.
* `zeta_half_eq` / `HasSum` / `Tendsto` eta material — this file has `eta_hasSum_imp_tendsto`, `eta_tendsto_tsum_eq_of_summable`, `etaTendsto_eq_etaHurwitz`; the `0 < ∑'` tsum form is false (proved as `eta_tsum_eq_zero`), so only `Tendsto` forms used below.
* Tail remainder: `R00EtaConv.remainder_le` (`interval_arith.lean`, `‖S₂ - L‖ ≤ 25`, `M = 1` only) and real `etaPair_tail_upper` / `etaPair_tail_lower` / `etaPair_tail_integral`, `eta_limit_norm_sub_le` (this file, real `σ = 1 / 2` only). No general complex `S_N` tail exists — proved below.
* Mathlib (all pre-existing, only called): `Complex.norm_cpow_eq_rpow_re_of_pos`, `Summable.of_norm_bounded`, `tsum_of_norm_bounded`, `Real.summable_nat_rpow_inv`, `summable_nat_add_iff`, `AntitoneOn.tsum_comp_add_le_integral`, `integrableOn_Ioi_rpow_of_lt`, `integral_Ioi_rpow_of_lt`, `Real.antitoneOn_rpow_Ioi_of_exponent_nonpos`.

Import graph: this file imports only `Mathlib`; no new imports added below (avoids cycles with `interval_arith` / `central_cover_assembly`). The R00 center is mirrored locally as `zetaCellS0 = 0.395 - 8.75 * I` (same numerals as `R00Numerics.sR00`: `Re = 0.395`, `Im = -8.75`) without importing it.

What is proved below (all unconditional, fully closed):
* `zetaCellS0_*`: local center `Re = 0.395`, `Im = -8.75`, `0 < Re`, `‖·‖ ≤ 10`.
* `zetaCell_*`: general complex paired-tail bound `‖L - S_{2M}‖ ≤ C * M ^ (-σ) / σ` for `0 < σ = s.re`, `‖s‖ ≤ C`, `1 ≤ M` (`M > 1` gives `N = 2 * M > 2`), via M-test plus integral test.
* `zetaCellS0_tail_general`: instantiation at `zetaCellS0` with `C = 10`, `σ = 0.395`.
* `zetaCellS0_r_2097152_le` plus `zetaCellS0_tail_2097152_le`: explicit `M = 2097152 = 2 ^ 21` (`N = 4194304`) gives `r ≤ 0.1` and hence `‖L - S_N‖ ≤ 0.1`.
* `zetaCellS0_r_1048576_gt`: previous power `M = 1048576 = 2 ^ 20` gives `r > 0.1`, so `2 ^ 21` is minimal among powers of two for this `r` (global minimal `M ≈ 1.21 * 10 ^ 6` not claimed).
-/

noncomputable def zetaCellS0 : ℂ := ⟨0.395, -8.75⟩

theorem zetaCellS0_re : zetaCellS0.re = 0.395 := rfl

theorem zetaCellS0_im : zetaCellS0.im = -8.75 := rfl

theorem zetaCellS0_pos : 0 < zetaCellS0.re := by
  rw [zetaCellS0_re]
  norm_num

theorem zetaCellS0_norm_le : ‖zetaCellS0‖ ≤ 10 := by
  have hsq : ‖zetaCellS0‖ ^ 2 ≤ (10 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, zetaCellS0_re, zetaCellS0_im]
    norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hsq

theorem zetaCell_majorant_antitone {s : ℂ} (hs : 0 < s.re) {M : ℕ} (hM : 0 < M) :
    AntitoneOn (fun x : ℝ => x ^ (-s.re - 1)) (Set.Ici (((M : ℕ)) : ℝ)) := by
  apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -s.re - 1 ≤ 0)).mono
  intro x hx
  have hM0 : (0 : ℝ) < (((M : ℕ)) : ℝ) := by exact_mod_cast hM
  simp only [Set.mem_Ici] at hx
  simp only [Set.mem_Ioi]
  linarith

theorem zetaCell_majorant_integrable {s : ℂ} (hs : 0 < s.re) {M : ℕ} (hM : 0 < M) :
    MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-s.re - 1)) (Set.Ioi (((M : ℕ)) : ℝ)) :=
  integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) (by exact_mod_cast hM)

theorem zetaCell_majorant_nonneg {s : ℂ} {M : ℕ} :
    ∀ t ∈ Set.Ioi (((M : ℕ)) : ℝ), 0 ≤ t ^ (-s.re - 1) := by
  intro t ht
  exact Real.rpow_nonneg
    (le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg _) (Set.mem_Ioi.mp ht))) _

theorem zetaCell_tsum_tail_le {s : ℂ} (hs : 0 < s.re) {M : ℕ} (hM : 1 ≤ M) :
    (∑' n : ℕ, ((((n + M + 1 : ℕ)) : ℝ) ^ (-s.re - 1))) ≤
      (∫ x : ℝ in Set.Ioi (((M : ℕ)) : ℝ), x ^ (-s.re - 1)) := by
  have hM0 : 0 < M := by omega
  exact AntitoneOn.tsum_comp_add_le_integral M
    (zetaCell_majorant_antitone hs hM0) (zetaCell_majorant_integrable hs hM0)
    (zetaCell_majorant_nonneg)

theorem zetaCell_integral_value {s : ℂ} (hs : 0 < s.re) {M : ℕ} (hM : 0 < M) :
    (∫ x : ℝ in Set.Ioi (((M : ℕ)) : ℝ), x ^ (-s.re - 1)) =
      ((((M : ℕ)) : ℝ) ^ (-s.re)) / s.re := by
  have hM0 : (0 : ℝ) < (((M : ℕ)) : ℝ) := by exact_mod_cast hM
  have h := integral_Ioi_rpow_of_lt (a := -s.re - 1) (by linarith : -s.re - 1 < -1) hM0
  have e1 : (-s.re - 1) + 1 = -s.re := by ring
  rw [e1] at h
  rw [h]
  rw [neg_div_neg_eq]

set_option maxHeartbeats 800000 in
theorem zetaCell_majorant_summable_shift {s : ℂ} (hs : 0 < s.re) (M : ℕ) :
    Summable (fun m : ℕ => ((((m + M + 1 : ℕ)) : ℝ) ^ (-s.re - 1))) := by
  have hp1 : (1 : ℝ) < s.re + 1 := by linarith
  have hbase : Summable (fun n : ℕ => ((((n : ℝ)) ^ (s.re + 1)))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hp1
  have hshift : Summable (fun m : ℕ => ((((m + (M + 1) : ℕ)) : ℝ) ^ (s.re + 1))⁻¹) :=
    (summable_nat_add_iff (M + 1)).mpr hbase
  have heq : (fun m : ℕ => ((((m + M + 1 : ℕ)) : ℝ) ^ (-s.re - 1))) =
      (fun m : ℕ => ((((m + (M + 1) : ℕ)) : ℝ) ^ (s.re + 1))⁻¹) := by
    funext m
    have eN : m + M + 1 = m + (M + 1) := by omega
    rw [eN]
    have eR : -s.re - 1 = -(s.re + 1) := by ring
    rw [eR, Real.rpow_neg (Nat.cast_nonneg _)]
  rw [heq]
  exact hshift

theorem zetaCell_scaled_summable {s : ℂ} (hs : 0 < s.re) {C : ℝ} (hC0 : 0 ≤ C) (M : ℕ) :
    Summable (fun m : ℕ => C * ((((m + M + 1 : ℕ)) : ℝ) ^ (-s.re - 1))) :=
  (zetaCell_majorant_summable_shift hs M).mul_left C

theorem zetaCell_tail_pointwise {s : ℂ} (hs : 0 < s.re) {C : ℝ} (hC : ‖s‖ ≤ C) (M m : ℕ) :
    ‖etaPairTerm s (m + M)‖ ≤ C * ((((m + M + 1 : ℕ)) : ℝ) ^ (-s.re - 1)) := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) hC
  have hle1 := norm_etaPairTerm_le s hs (m + M)
  have hm_pos : (0 : ℝ) < ((((m + M + 1 : ℕ)) : ℝ)) := Nat.cast_pos.mpr (by omega)
  have hm_le : ((((m + M + 1 : ℕ)) : ℝ)) ≤ ((((2 * (m + M) + 1 : ℕ)) : ℝ)) :=
    Nat.cast_le.mpr (by omega)
  have hexp_nonpos : -s.re - 1 ≤ 0 := by linarith
  have hrpow_le : ((((2 * (m + M) + 1 : ℕ)) : ℝ) ^ (-s.re - 1)) ≤
      ((((m + M + 1 : ℕ)) : ℝ) ^ (-s.re - 1)) :=
    Real.rpow_le_rpow_of_nonpos hm_pos hm_le hexp_nonpos
  calc ‖etaPairTerm s (m + M)‖ ≤ ‖s‖ * ((((2 * (m + M) + 1 : ℕ)) : ℝ) ^ (-s.re - 1)) := hle1
    _ ≤ C * ((((m + M + 1 : ℕ)) : ℝ) ^ (-s.re - 1)) :=
        mul_le_mul hC hrpow_le
          (Real.rpow_nonneg (Nat.cast_nonneg _) _) hC0

theorem zetaCell_pair_tail_norm_le {s : ℂ} (hs : 0 < s.re) {C : ℝ} (hC : ‖s‖ ≤ C)
    (hC0 : 0 ≤ C) (M : ℕ) (hM : 1 ≤ M) :
    ‖∑' m, etaPairTerm s (m + M)‖ ≤ C * (((((M : ℕ)) : ℝ) ^ (-s.re)) / s.re) := by
  have hM0 : 0 < M := by omega
  have hmajor_summ := zetaCell_scaled_summable hs hC0 M
  have hpoint := fun m => zetaCell_tail_pointwise hs hC M m
  have htsum_le : ‖∑' m, etaPairTerm s (m + M)‖ ≤
      ∑' m, C * ((((m + M + 1 : ℕ)) : ℝ) ^ (-s.re - 1)) :=
    tsum_of_norm_bounded hmajor_summ.hasSum hpoint
  have hfactor : (∑' m, C * ((((m + M + 1 : ℕ)) : ℝ) ^ (-s.re - 1))) =
      C * (∑' n, ((((n + M + 1 : ℕ)) : ℝ) ^ (-s.re - 1))) :=
    Summable.tsum_mul_left C (zetaCell_majorant_summable_shift hs M)
  have htail_le := zetaCell_tsum_tail_le hs hM
  have hval := zetaCell_integral_value hs hM0
  calc ‖∑' m, etaPairTerm s (m + M)‖ ≤ ∑' m, C * ((((m + M + 1 : ℕ)) : ℝ) ^ (-s.re - 1)) := htsum_le
    _ = C * (∑' n, ((((n + M + 1 : ℕ)) : ℝ) ^ (-s.re - 1))) := hfactor
    _ ≤ C * (∫ x : ℝ in Set.Ioi (((M : ℕ)) : ℝ), x ^ (-s.re - 1)) :=
        mul_le_mul_of_nonneg_left htail_le hC0
    _ = C * (((((M : ℕ)) : ℝ) ^ (-s.re)) / s.re) := by rw [hval]

theorem zetaCell_even_remainder_le {s : ℂ} (hs : 0 < s.re) {C : ℝ} (hC : ‖s‖ ≤ C)
    (hC0 : 0 ≤ C) (M : ℕ) (hM : 1 ≤ M) :
    ‖(∑' m, etaPairTerm s m) - (∑ k ∈ Finset.range (2 * M), etaDirichletTerm s k)‖ ≤
      C * (((((M : ℕ)) : ℝ) ^ (-s.re)) / s.re) := by
  have hsum := summable_etaPairTerm hs
  have hsplit : (∑ m ∈ Finset.range M, etaPairTerm s m) + (∑' m, etaPairTerm s (m + M)) =
      ∑' m, etaPairTerm s m :=
    hsum.sum_add_tsum_nat_add M
  have heven := etaDirichlet_even_partial s M
  have hdiff : (∑' m, etaPairTerm s m) - (∑ k ∈ Finset.range (2 * M), etaDirichletTerm s k) =
      ∑' m, etaPairTerm s (m + M) := by
    rw [heven, ← hsplit]
    ring
  rw [hdiff]
  exact zetaCell_pair_tail_norm_le hs hC hC0 M hM

theorem zetaCellS0_tail_general (M : ℕ) (hM : 1 ≤ M) :
    ‖(∑' m, etaPairTerm zetaCellS0 m) -
      (∑ k ∈ Finset.range (2 * M), etaDirichletTerm zetaCellS0 k)‖ ≤
      10 * (((((M : ℕ)) : ℝ) ^ (-0.395 : ℝ)) / (0.395 : ℝ)) := by
  have hs := zetaCellS0_pos
  have hC : ‖zetaCellS0‖ ≤ 10 := zetaCellS0_norm_le
  have h := zetaCell_even_remainder_le hs hC (by norm_num) M hM
  have hre : zetaCellS0.re = 0.395 := zetaCellS0_re
  rw [hre] at h
  exact h

theorem zetaCellS0_M2097152_eq : ((((2097152 : ℕ)) : ℝ)) = (2 : ℝ) ^ (21 : ℕ) := by
  norm_num

theorem zetaCellS0_M2097152_rpow_ge :
    (256 : ℝ) ≤ ((((2097152 : ℕ)) : ℝ) ^ (0.395 : ℝ)) := by
  rw [zetaCellS0_M2097152_eq]
  have h1 : (((2 : ℝ) ^ (21 : ℕ)) ^ (0.395 : ℝ)) = (2 : ℝ) ^ (((((21 : ℕ)) : ℝ)) * (0.395 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [h1]
  have hexp_ge : (8 : ℝ) ≤ ((((21 : ℕ)) : ℝ)) * (0.395 : ℝ) := by norm_num
  have h2 : (2 : ℝ) ^ (8 : ℝ) ≤ (2 : ℝ) ^ (((((21 : ℕ)) : ℝ)) * (0.395 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_ge
  have e8 : (8 : ℝ) = ((((8 : ℕ)) : ℝ)) := by norm_num
  have h3 : (2 : ℝ) ^ (8 : ℝ) = 256 := by
    rw [e8, Real.rpow_natCast]
    norm_num
  linarith

set_option maxHeartbeats 800000 in
theorem zetaCellS0_r_2097152_le :
    10 * ((((((2097152 : ℕ)) : ℝ) ^ (-0.395 : ℝ))) / (0.395 : ℝ)) ≤ (0.1 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((2097152 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((2097152 : ℕ)) : ℝ) ^ (0.395 : ℝ)) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := zetaCellS0_M2097152_rpow_ge
  have hrw : ((((2097152 : ℕ)) : ℝ) ^ (-0.395 : ℝ)) =
      (((((2097152 : ℕ)) : ℝ) ^ (0.395 : ℝ)))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((2097152 : ℕ)) : ℝ) ^ (0.395 : ℝ)))⁻¹ ≤ (256 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((2097152 : ℕ)) : ℝ) ^ (0.395 : ℝ)))⁻¹ / (0.395 : ℝ) ≤
      (256 : ℝ)⁻¹ / (0.395 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : 10 * ((((((2097152 : ℕ)) : ℝ) ^ (0.395 : ℝ)))⁻¹ / (0.395 : ℝ)) ≤
      10 * ((256 : ℝ)⁻¹ / (0.395 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : 10 * ((256 : ℝ)⁻¹ / (0.395 : ℝ)) ≤ (0.1 : ℝ) := by norm_num
  linarith

theorem zetaCellS0_tail_2097152_le :
    ‖(∑' m, etaPairTerm zetaCellS0 m) -
      (∑ k ∈ Finset.range (2 * 2097152), etaDirichletTerm zetaCellS0 k)‖ ≤ (0.1 : ℝ) := by
  have hgen := zetaCellS0_tail_general 2097152 (by norm_num)
  have hr := zetaCellS0_r_2097152_le
  linarith

theorem zetaCellS0_M1048576_eq : ((((1048576 : ℕ)) : ℝ)) = (2 : ℝ) ^ (20 : ℕ) := by
  norm_num

theorem zetaCellS0_10112_pow_lt : ((1.0112 : ℝ) ^ (10 : ℕ)) < 2 := by
  norm_num

theorem zetaCellS0_rpow01_gt : (1.0112 : ℝ) < (2 : ℝ) ^ (0.1 : ℝ) := by
  by_contra hle
  push Not at hle
  have hle_pow : (((2 : ℝ) ^ (0.1 : ℝ)) ^ (10 : ℕ)) ≤ ((1.0112 : ℝ) ^ (10 : ℕ)) :=
    pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) hle _
  have h2_eq : (((2 : ℝ) ^ (0.1 : ℝ)) ^ (10 : ℕ)) = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : (0.1 : ℝ) * (((10 : ℕ)) : ℝ) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [h2_eq] at hle_pow
  have hlt := zetaCellS0_10112_pow_lt
  linarith

theorem zetaCellS0_M1048576_rpow_lt :
    ((((1048576 : ℕ)) : ℝ) ^ (0.395 : ℝ)) < (20000 : ℝ) / 79 := by
  rw [zetaCellS0_M1048576_eq]
  have h1 : (((2 : ℝ) ^ (20 : ℕ)) ^ (0.395 : ℝ)) =
      (2 : ℝ) ^ (((((20 : ℕ)) : ℝ)) * (0.395 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [h1]
  have e_exp : ((((20 : ℕ)) : ℝ)) * (0.395 : ℝ) = 8 - (0.1 : ℝ) := by norm_num
  rw [e_exp]
  have hsub : (2 : ℝ) ^ (8 - (0.1 : ℝ)) = (2 : ℝ) ^ (8 : ℝ) / (2 : ℝ) ^ (0.1 : ℝ) := by
    rw [Real.rpow_sub (by norm_num)]
  rw [hsub]
  have e8 : (8 : ℝ) = ((((8 : ℕ)) : ℝ)) := by norm_num
  have h256 : (2 : ℝ) ^ (8 : ℝ) = 256 := by
    rw [e8, Real.rpow_natCast]
    norm_num
  rw [h256]
  have hgt := zetaCellS0_rpow01_gt
  have h256_pos : (0 : ℝ) < 256 := by norm_num
  have h01_pos : (0 : ℝ) < (1.0112 : ℝ) := by norm_num
  have h2_pos : (0 : ℝ) < (2 : ℝ) ^ (0.1 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hInv_lt : (256 : ℝ) / ((2 : ℝ) ^ (0.1 : ℝ)) < 256 / (1.0112 : ℝ) :=
    div_lt_div_of_pos_left h256_pos h01_pos hgt
  have heq : (256 : ℝ) / (1.0112 : ℝ) = (20000 : ℝ) / 79 := by norm_num
  linarith

set_option maxHeartbeats 800000 in
theorem zetaCellS0_r_1048576_gt :
    (0.1 : ℝ) < 10 * (((((1048576 : ℕ)) : ℝ) ^ (-0.395 : ℝ)) / (0.395 : ℝ)) := by
  have hMpos : (0 : ℝ) < ((((1048576 : ℕ)) : ℝ)) := by norm_num
  have hBpos : (0 : ℝ) < ((((1048576 : ℕ)) : ℝ) ^ (0.395 : ℝ)) :=
    Real.rpow_pos_of_pos hMpos _
  have hB_lt := zetaCellS0_M1048576_rpow_lt
  have hrw : ((((1048576 : ℕ)) : ℝ) ^ (-0.395 : ℝ)) =
      (((((1048576 : ℕ)) : ℝ) ^ (0.395 : ℝ)))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hden_pos : (0 : ℝ) < (0.395 : ℝ) * ((((1048576 : ℕ)) : ℝ) ^ (0.395 : ℝ)) :=
    mul_pos (by norm_num) hBpos
  have h10_eq : (10 : ℝ) / ((0.395 : ℝ) * ((((1048576 : ℕ)) : ℝ) ^ (0.395 : ℝ))) =
      10 * ((((((1048576 : ℕ)) : ℝ) ^ (0.395 : ℝ)))⁻¹ / (0.395 : ℝ)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  rw [← h10_eq]
  rw [lt_div_iff₀ hden_pos]
  have hthr : (0.1 : ℝ) * ((0.395 : ℝ) * (20000 / 79)) = 10 := by norm_num
  have hmul : (0.1 : ℝ) * ((0.395 : ℝ) * ((((1048576 : ℕ)) : ℝ) ^ (0.395 : ℝ))) <
      (0.1 : ℝ) * ((0.395 : ℝ) * (20000 / 79)) := by
    apply mul_lt_mul_of_pos_left _ (by norm_num)
    apply mul_lt_mul_of_pos_left hB_lt (by norm_num)
  linarith

#print axioms zetaCellS0
#print axioms zetaCellS0_re
#print axioms zetaCellS0_pos
#print axioms zetaCellS0_norm_le
#print axioms zetaCell_majorant_antitone
#print axioms zetaCell_majorant_integrable
#print axioms zetaCell_tsum_tail_le
#print axioms zetaCell_integral_value
#print axioms zetaCell_majorant_summable_shift
#print axioms zetaCell_pair_tail_norm_le
#print axioms zetaCell_even_remainder_le
#print axioms zetaCellS0_tail_general
#print axioms zetaCellS0_r_2097152_le
#print axioms zetaCellS0_tail_2097152_le
#print axioms zetaCellS0_r_1048576_gt

/-!
## Central-cover identity: `∑' pairs = etaHurwitz` on `{Re > 0}` (identity theorem).

GOAL (docs §18b.10 zeta bullet residual, lemma (a) blocking every cell's `Azeta`):
prove `∑' m, etaPairTerm s m = etaHurwitz s` at the central-cover cell centers
(`s.re ∈ {0.395, 0.3, 0.2, 0.105}`, all in `{Re > 0}`), outside every existing
pair-limit lemma's domain (`etaPairLim_eq_of_one_lt_re` needs `1 < s.re`;
`etaPairLim_half` / `etaTendsto_eq_etaHurwitz` need `s = 1/2`).

ROUTE: `G(s) = ∑' m, etaPairTerm s m` is analytic on `{Re > 0}` (locally uniform
convergence from the paired M-test tail bound — E's `r(M)` majorant, here in the
uniform-on-ball form `C * (m+1)^{-σ₀-1}`) and agrees with `etaHurwitz` on
`{Re > 1}` (via `etaPairLim_eq_of_one_lt_re`); the identity theorem extends
equality to all of `{Re > 0}`, covering every center.

GREP DOCUMENTATION (searches run before writing; repo + Mathlib):
* `dirichletEta` — no Mathlib hit (confirmed pre-existing gap; this file's
  `etaDirichletTerm` / `etaPairTerm` / `etaHurwitz` mirror is the API, no import).
* `differentiableOn_tsum_of_summable_norm` — found in
  `Mathlib/Analysis/Complex/LocallyUniformLimit.lean:171` (already used by
  `analyticOn_etaPairLim_ball` in this file); reused below for the `{Re > 0}` ball.
* `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` — found in
  `Mathlib/Analysis/Analytic/Uniqueness.lean:223` (already used by
  `etaPairLim_eq_etaHurwitz_ball` and `etaHurwitz_eq_etaRHS_compl`); reused below.
* `Convex.isPreconnected` — found in `Mathlib/Analysis/Convex/PathConnected.lean:95`
  (needs `Convex ℝ s`); proved for `{Re > 0}` below.
* `convex_iff_add_mem` — found in `Mathlib/Analysis/Convex/Basic.lean:71`.
* `Real.summable_nat_rpow_inv`, `summable_nat_add_iff` — already used in this file
  (`summable_etaPairTerm`, `etaPair_majorant_summable`, `zetaCell_majorant_*`);
  same pattern reused for the local majorant (no duplication of Mathlib).
* `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_le_rpow_of_nonpos`,
  `Real.rpow_neg`, `Real.rpow_nonneg` — already used in this file
  (`etaPair_bound_ball`, `summable_etaPairTerm`); same pattern reused.
* `Complex.continuous_re`, `isOpen_Ioi`, `Complex.abs_re_le_norm`, `Complex.sub_re`,
  `Complex.add_re`, `Complex.smul_re`, `smul_eq_mul`, `Metric.isOpen_ball`,
  `dist_eq_norm` — all pre-existing Mathlib + already used in this file
  (`hre_ball`, `hnorm_ball`, `etaPairLim_eq_etaHurwitz_ball`); reused.
* `zetaCellS0`, `zetaCellS0_pos`, `norm_etaPairTerm_le`, `etaPairTerm_differentiable`,
  `etaPairLim_eq_of_one_lt_re`, `analytic_etaHurwitz`, `coe_three_half_eq` —
  all in this file (read-only reuse, no modification).
* Import graph: this file imports only `Mathlib`; no new imports below
  (avoids cycles with `interval_arith` / `central_cover_assembly`).

WHAT IS PROVED (all unconditional, no `sorry`/`admit`/`axiom`/hypotheses):
* (1) Analyticity: `rePos_isOpen`, `rePos_convex`, `rePos_isPreconnected`,
  `etaPair_local_radius_pos`, `etaPair_local_mem_bounds`,
  `etaPair_local_majorant_summable`, `etaPair_local_bound`, `etaPair_local_diffOn`,
  `differentiableOn_etaPairG_rePos`, `analytic_etaPairG_rePos`,
  `analytic_etaHurwitz_rePos`.
* (2) Identity step: `etaPairG_eq_etaHurwitz_rePos`
  (`EqOn` on `{Re > 0}` from agreement on `{Re > 1}` at `z₀ = 3/2`).
* (3) Corner/general: `etaPairLim_eq_etaHurwitz_of_pos` (all `0 < s.re`),
  `etaPairLim_eq_etaHurwitz_cellS0` (R00 corner `zetaCellS0`),
  `etaPairLim_eq_etaHurwitz_cellCenter` (every center with
  `s.re ∈ {0.395, 0.3, 0.2, 0.105}`).
-/

/-- `{Re > 0}` is open (preimage of `Ioi 0` under continuous `Re`). -/
theorem rePos_isOpen : IsOpen {s : ℂ | 0 < s.re} := by
  have h : IsOpen (Complex.re ⁻¹' Set.Ioi (0 : ℝ)) :=
    Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have heq : {s : ℂ | 0 < s.re} = Complex.re ⁻¹' Set.Ioi (0 : ℝ) := by
    ext x
    simp
  rw [heq]
  exact h

/-- `{Re > 0}` is convex (real convex combination preserves `Re > 0`). -/
theorem rePos_convex : Convex ℝ {s : ℂ | 0 < s.re} := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  have hx' : (0 : ℝ) < x.re := hx
  have hy' : (0 : ℝ) < y.re := hy
  have hre : (a • x + b • y).re = a * x.re + b * y.re := by
    rw [Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
  show (0 : ℝ) < (a • x + b • y).re
  rw [hre]
  by_cases ha0 : a = 0
  · subst ha0
    have hb1 : b = 1 := by linarith
    rw [hb1]
    simpa using hy'
  · have ha' : (0 : ℝ) < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have h1 : (0 : ℝ) < a * x.re := mul_pos ha' hx'
    have h2 : (0 : ℝ) ≤ b * y.re := mul_nonneg hb (le_of_lt hy')
    exact add_pos_of_pos_of_nonneg h1 h2

/-- `{Re > 0}` is preconnected (from convexity). -/
theorem rePos_isPreconnected : IsPreconnected {s : ℂ | 0 < s.re} :=
  rePos_convex.isPreconnected

/-- Local radius `min (Re/2) 1` is positive on `{Re > 0}`. -/
theorem etaPair_local_radius_pos {s0 : ℂ} (hs0 : 0 < s0.re) :
    0 < min (s0.re / 2) 1 :=
  lt_min (by linarith) (by norm_num)

/-- On the local ball, `Re` stays `≥ Re₀/2` and the norm stays `≤ ‖s₀‖+1`. -/
theorem etaPair_local_mem_bounds {s0 w : ℂ} (_hs0 : 0 < s0.re)
    (hw : w ∈ Metric.ball s0 (min (s0.re / 2) 1)) :
    s0.re / 2 ≤ w.re ∧ ‖w‖ ≤ ‖s0‖ + 1 := by
  have hr_half : min (s0.re / 2) 1 ≤ s0.re / 2 := min_le_left _ _
  have hr_one : min (s0.re / 2) 1 ≤ 1 := min_le_right _ _
  have hw_norm : ‖w - s0‖ < min (s0.re / 2) 1 := by
    rw [Metric.mem_ball, dist_eq_norm] at hw
    exact hw
  have habs := Complex.abs_re_le_norm (w - s0)
  have hre_sub : (w - s0).re = w.re - s0.re := Complex.sub_re _ _
  rw [hre_sub, abs_le] at habs
  have hre_ge : s0.re / 2 ≤ w.re := by linarith [habs.1, hw_norm, hr_half]
  have hnorm_le : ‖w‖ ≤ ‖s0‖ + 1 := by
    have e : w = s0 + (w - s0) := by ring
    have hle1 : ‖w - s0‖ ≤ 1 := le_trans (le_of_lt hw_norm) hr_one
    calc ‖w‖ = ‖s0 + (w - s0)‖ := by conv_lhs => rw [e]
      _ ≤ ‖s0‖ + ‖w - s0‖ := norm_add_le _ _
      _ ≤ ‖s0‖ + 1 := by linarith
  exact ⟨hre_ge, hnorm_le⟩

/-- Local uniform summable majorant `C * (m+1)^{-σ₀-1}` with `C = ‖s₀‖+1`,
    `σ₀ = Re₀/2` (M-test; same `rpow_inv` + `nat_add_iff` pattern as
    `summable_etaPairTerm` / `zetaCell_majorant_summable_shift`). -/
theorem etaPair_local_majorant_summable {s0 : ℂ} (hs0 : 0 < s0.re) :
    Summable (fun m : ℕ => (‖s0‖ + 1) * ((((m + 1 : ℕ)) : ℝ) ^ (-(s0.re / 2) - 1))) := by
  have hp1 : (1 : ℝ) < s0.re / 2 + 1 := by linarith
  have hbase : Summable (fun n : ℕ => ((((n : ℝ)) ^ (s0.re / 2 + 1)))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hp1
  have hshift : Summable (fun m : ℕ => ((((m + 1 : ℕ)) : ℝ) ^ (s0.re / 2 + 1))⁻¹) :=
    (summable_nat_add_iff 1).mpr hbase
  have heq : (fun m : ℕ => ((((m + 1 : ℕ)) : ℝ) ^ (-(s0.re / 2) - 1))) =
      (fun m : ℕ => ((((m + 1 : ℕ)) : ℝ) ^ (s0.re / 2 + 1))⁻¹) := by
    funext m
    have eR : -(s0.re / 2) - 1 = -(s0.re / 2 + 1) := by ring
    rw [eR, Real.rpow_neg (Nat.cast_nonneg _)]
  have hbaseS : Summable (fun m : ℕ => ((((m + 1 : ℕ)) : ℝ) ^ (-(s0.re / 2) - 1))) := by
    rw [heq]
    exact hshift
  exact hbaseS.mul_left _

set_option maxHeartbeats 800000 in
/-- Pointwise uniform bound on the local ball (MVT pair bound + two `rpow`
    monotonicities; same pattern as `etaPair_bound_ball`). -/
theorem etaPair_local_bound {s0 : ℂ} (hs0 : 0 < s0.re) (m : ℕ) (w : ℂ)
    (hw : w ∈ Metric.ball s0 (min (s0.re / 2) 1)) :
    ‖etaPairTerm w m‖ ≤ (‖s0‖ + 1) * ((((m + 1 : ℕ)) : ℝ) ^ (-(s0.re / 2) - 1)) := by
  obtain ⟨hre_ge, hnorm_le⟩ := etaPair_local_mem_bounds hs0 hw
  have hs_pos : 0 < w.re := lt_of_lt_of_le (by linarith : (0 : ℝ) < s0.re / 2) hre_ge
  have hle1 := norm_etaPairTerm_le w hs_pos m
  have ha1 : (1 : ℝ) ≤ ((((2 * m + 1 : ℕ)) : ℝ)) := by
    exact_mod_cast (show 1 ≤ 2 * m + 1 by omega)
  have hm_pos : (0 : ℝ) < ((((m + 1 : ℕ)) : ℝ)) := Nat.cast_pos.mpr (by omega)
  have hm_le : ((((m + 1 : ℕ)) : ℝ)) ≤ ((((2 * m + 1 : ℕ)) : ℝ)) :=
    Nat.cast_le.mpr (by omega)
  have hexp_le : -w.re - 1 ≤ -(s0.re / 2) - 1 := by linarith
  have hexp_nonpos : -(s0.re / 2) - 1 ≤ 0 := by linarith
  have hstep1 : ((((2 * m + 1 : ℕ)) : ℝ) ^ (-w.re - 1))
      ≤ ((((2 * m + 1 : ℕ)) : ℝ) ^ (-(s0.re / 2) - 1)) :=
    Real.rpow_le_rpow_of_exponent_le ha1 hexp_le
  have hstep2 : ((((2 * m + 1 : ℕ)) : ℝ) ^ (-(s0.re / 2) - 1))
      ≤ ((((m + 1 : ℕ)) : ℝ) ^ (-(s0.re / 2) - 1)) :=
    Real.rpow_le_rpow_of_nonpos hm_pos hm_le hexp_nonpos
  have hpow_le : ((((2 * m + 1 : ℕ)) : ℝ) ^ (-w.re - 1))
      ≤ ((((m + 1 : ℕ)) : ℝ) ^ (-(s0.re / 2) - 1)) :=
    le_trans hstep1 hstep2
  have hC0 : (0 : ℝ) ≤ ‖s0‖ + 1 := add_nonneg (norm_nonneg _) (by norm_num)
  have hpow_nn : (0 : ℝ) ≤ ((((2 * m + 1 : ℕ)) : ℝ) ^ (-w.re - 1)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc ‖etaPairTerm w m‖ ≤ ‖w‖ * ((((2 * m + 1 : ℕ)) : ℝ) ^ (-w.re - 1)) := hle1
    _ ≤ (‖s0‖ + 1) * ((((m + 1 : ℕ)) : ℝ) ^ (-(s0.re / 2) - 1)) :=
        mul_le_mul hnorm_le hpow_le hpow_nn hC0

set_option maxHeartbeats 800000 in
/-- `G` is differentiable on each local ball (Weierstrass M-test tsum). -/
theorem etaPair_local_diffOn {s0 : ℂ} (hs0 : 0 < s0.re) :
    DifferentiableOn ℂ (fun s => ∑' m, etaPairTerm s m)
      (Metric.ball s0 (min (s0.re / 2) 1)) :=
  Complex.differentiableOn_tsum_of_summable_norm
    (etaPair_local_majorant_summable hs0)
    (fun m => (etaPairTerm_differentiable m).differentiableOn)
    Metric.isOpen_ball
    (fun m w hw => etaPair_local_bound hs0 m w hw)

/-- (1) ANALYTICITY: `G(s) = ∑' pairs` is differentiable on all of `{Re > 0}`
    (local balls give `DifferentiableAt` at each point, hence `WithinAt`). -/
theorem differentiableOn_etaPairG_rePos :
    DifferentiableOn ℂ (fun s => ∑' m, etaPairTerm s m) {s : ℂ | 0 < s.re} := by
  intro x hx
  have hx' : (0 : ℝ) < x.re := hx
  have hrPos : 0 < min (x.re / 2) 1 := etaPair_local_radius_pos hx'
  have hDiffBall := etaPair_local_diffOn hx'
  have hxBall : x ∈ Metric.ball x (min (x.re / 2) 1) := by
    rw [Metric.mem_ball, dist_self]
    exact hrPos
  have hAt : DifferentiableAt ℂ (fun s => ∑' m, etaPairTerm s m) x :=
    hDiffBall.differentiableAt (Metric.isOpen_ball.mem_nhds hxBall)
  exact hAt.differentiableWithinAt

/-- (1) ANALYTICITY (analytic form): `G` is analytic on `{Re > 0}`. -/
theorem analytic_etaPairG_rePos :
    AnalyticOnNhd ℂ (fun s => ∑' m, etaPairTerm s m) {s : ℂ | 0 < s.re} :=
  differentiableOn_etaPairG_rePos.analyticOnNhd rePos_isOpen

/-- `etaHurwitz` is analytic on `{Re > 0}` (restriction of the entire function). -/
theorem analytic_etaHurwitz_rePos :
    AnalyticOnNhd ℂ etaHurwitz {s : ℂ | 0 < s.re} :=
  analytic_etaHurwitz.mono (Set.subset_univ _)

set_option maxHeartbeats 800000 in
/-- (2) IDENTITY STEP: `G = etaHurwitz` on all of `{Re > 0}`.
    Both sides are analytic there (above); they agree on `{Re > 1}`
    (`etaPairLim_eq_of_one_lt_re`) which is a neighborhood of `z₀ = 3/2`,
    so `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` extends equality. -/
theorem etaPairG_eq_etaHurwitz_rePos :
    Set.EqOn (fun s => ∑' m, etaPairTerm s m) etaHurwitz {s : ℂ | 0 < s.re} := by
  have hU : IsPreconnected {s : ℂ | 0 < s.re} := rePos_isPreconnected
  have hz0 : ((3 / 2 : ℂ)) ∈ {s : ℂ | 0 < s.re} := by
    show (0 : ℝ) < ((3 / 2 : ℂ)).re
    rw [coe_three_half_eq, Complex.ofReal_re]
    norm_num
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    analytic_etaPairG_rePos analytic_etaHurwitz_rePos hU hz0 ?_
  have hOpen1 : IsOpen (Complex.re ⁻¹' Set.Ioi (1 : ℝ)) :=
    Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hmem : (Complex.re ⁻¹' Set.Ioi (1 : ℝ)) ∈ 𝓝 ((3 / 2 : ℂ)) := by
    apply hOpen1.mem_nhds
    simp only [Set.mem_preimage, Set.mem_Ioi, coe_three_half_eq, Complex.ofReal_re]
    norm_num
  refine eventually_of_mem hmem (fun t ht => ?_)
  have ht1 : (1 : ℝ) < t.re := by simpa using ht
  exact etaPairLim_eq_of_one_lt_re ht1

/-- (3) GENERAL CENTER EQUALITY: pairs-tsum equals `etaHurwitz` at every
    `s` with `0 < s.re` (covers all central-cover centers
    `s.re ∈ {0.395, 0.3, 0.2, 0.105}`). -/
theorem etaPairLim_eq_etaHurwitz_of_pos {s : ℂ} (hs : 0 < s.re) :
    (∑' m, etaPairTerm s m) = etaHurwitz s :=
  etaPairG_eq_etaHurwitz_rePos (by simpa using hs)

/-- (3) R00 CORNER: pairs-tsum equals `etaHurwitz` at `zetaCellS0`. -/
theorem etaPairLim_eq_etaHurwitz_cellS0 :
    (∑' m, etaPairTerm zetaCellS0 m) = etaHurwitz zetaCellS0 :=
  etaPairLim_eq_etaHurwitz_of_pos zetaCellS0_pos

/-- (3) ALL CENTRAL-COVER CENTERS: explicit disjunction over the four
    `Re`-values occurring at cell centers. -/
theorem etaPairLim_eq_etaHurwitz_cellCenter {s : ℂ}
    (hs : s.re = 0.395 ∨ s.re = 0.3 ∨ s.re = 0.2 ∨ s.re = 0.105) :
    (∑' m, etaPairTerm s m) = etaHurwitz s := by
  have hpos : 0 < s.re := by
    rcases hs with h | h | h | h <;> rw [h] <;> norm_num
  exact etaPairLim_eq_etaHurwitz_of_pos hpos

#print axioms rePos_isOpen
#print axioms rePos_convex
#print axioms rePos_isPreconnected
#print axioms etaPair_local_radius_pos
#print axioms etaPair_local_mem_bounds
#print axioms etaPair_local_majorant_summable
#print axioms etaPair_local_bound
#print axioms etaPair_local_diffOn
#print axioms differentiableOn_etaPairG_rePos
#print axioms analytic_etaPairG_rePos
#print axioms analytic_etaHurwitz_rePos
#print axioms etaPairG_eq_etaHurwitz_rePos
#print axioms etaPairLim_eq_etaHurwitz_of_pos
#print axioms etaPairLim_eq_etaHurwitz_cellS0
#print axioms etaPairLim_eq_etaHurwitz_cellCenter

/-!
## Zeta DIVISION bridge: pair-tsum to `riemannZeta` at cell centers + R00 `Azeta` wiring.

GOAL (docs `AGENT_INFRASTRUCTURE_GUIDE.md` §18b.10 zeta bullet residual:
"division + instantiation remain"; downstream of now-CLOSED (a)
`etaPairLim_eq_etaHurwitz_cellCenter` needs only `etaHurwitz = etaRHS`
specialization (already `etaHurwitz_eq_etaRHS_compl`), `1 - 2^{1-s} ≠ 0`
+ division to `riemannZeta s0`, and numeric `S_N` + `zetaCell_even_remainder_le`
instantiation):

Missing link closed here: `riemannZeta s = (∑' m, etaPairTerm s m) / (1 - 2^{1-s})`
for `0 < s.re`, `s ≠ 1` (via pair identity + `etaRHS` equation + factor
nonvanishing), generalizing `interval_arith.lean` (READ-ONLY, not imported:
this file keeps `import Mathlib` only, no cycles) `R00ZetaEM.zeta_lower_R00_of_eta`
`eq_div_iff` + `factor_ne_zero_R00` + `factor_upper_R00` continuation pattern
from the single `sR00` point to all `Re > 0` and all four center `Re`s.

GREP DOCUMENTATION (searches run before writing; repo + Mathlib):
* `norm_cpow_eq_rpow_re_of_pos` — found in
  `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:337` (`Complex.` namespace);
  already used in this file (`norm_etaPairTerm_le`, `hurwitz_half_cpow_eq`);
  reused for `‖2^{1-s}‖ = 2^{1-Re s}` (no new import).
* `Real.one_lt_rpow` (`Real.lean:672`), `Real.rpow_lt_one_of_one_lt_of_neg`
  (`Real.lean:664`) — for `2^x ≠ 1` when `x ≠ 0` (two-sided, no `rpow_eq_one`
  needed).
* `le_of_pow_le_pow_left₀` — found in
  `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:702`
  (`hn : n ≠ 0`, `hb : 0 ≤ b`); already used by `R00ZetaEM.rpow_two_R00_*`
  in `interval_arith.lean`; same cleared-exponent pattern reused below for the
  two numeral bounds (no duplication of Mathlib).
* `eq_div_iff`, `le_div_iff₀`/`div_le_iff₀`, `div_mul_cancel₀`, `norm_inv`,
  `norm_one`, `norm_sub_le`/`norm_add_le`, `norm_pos_iff`, `norm_mul`/`norm_div`
  — all pre-existing Mathlib, already used in this file or `interval_arith`
  (`zeta_lower_R00_of_eta` uses `eq_div_iff` + `norm_div` + `le_div_iff₀`);
  same pattern generalized in the feeder.
* `Complex.one_cpow`, `Complex.sub_re`/`Complex.one_re`, `Finset.sum_range_succ`,
  `Set.mem_compl_iff`/`Set.mem_singleton_iff`, `sub_eq_zero`/`sub_ne_zero`,
  `lt_or_gt_of_ne` — all pre-existing Mathlib, already used in this file.
* `rpow_two_R00_ge/le/thr`, `etaCPartial_two_norm_ge`, `factor_upper_R00`,
  `factor_ne_zero_R00`, `zeta_lower_R00_of_eta` — only in `interval_arith.lean`
  (`R00ZetaEM`, READ-ONLY); mirrored here via existing `etaDirichletTerm` /
  `etaPairTerm` API (no import, avoids cycles). Note: `interval_arith`
  `R00EtaConv.remainder_le` proves `‖S₂ - L‖ ≤ 25` (honest) while
  `zeta_lower_R00_of_eta` needs `‖S₂ - L‖ ≤ 1/10` (numerically false:
  `|S₂ - η| ≈ 0.96` per mpmath comment in-file there), so the `1/26` route
  cannot be instantiated at `N = 2`; the honest `r ≤ 0.1` needs `M = 2097152`
  (`N = 4194304`, `zetaCellS0_tail_2097152_le` in this file) whose explicit
  `S_N` lower bound is infeasible (4M cpow terms — E's strategic finding in
  §18b.10). Hence the R00 `Azeta` below is conditional on the single explicit
  `S_{4194304}` lower bound (exact missing lemma in residual), with all other
  premises (pair identity, continuation, factor upper/nonvanishing, `r ≤ 0.1`
  tail) discharged in-file.
* `zeta` vs `riemannZeta` — `riemann_hypothesis.lean:16`
  `def zeta : ℂ → ℂ := riemannZeta` (definitionally equal); `interval_arith`
  states `‖zeta sR00‖`, this file states `‖riemannZeta zetaCellS0‖` with
  `zetaCellS0 = 0.395 - 8.75·I` mirroring `R00Numerics.sR00` (`Re = 0.395`,
  `Im = -8.75`) without importing it (import graph: this file `import Mathlib`
  only).
* Import graph checked before any new import: no new imports added below
  (avoids cycles with `interval_arith` / `central_cover_assembly`).

WHAT IS PROVED (all unconditional implications, no `sorry`/`admit`/`axiom`):
* (1) General division bridge: `two_cpow_norm`, `two_cpow_one_sub_norm`,
  `two_rpow_ne_one_of_ne_zero`, `two_cpow_one_sub_ne_one_of_re_ne`,
  `etaFactor_ne_zero_of_re_ne`, `zeta_of_etaPairLim` (all `0 < Re`, `s ≠ 1`,
  factor hypothesis), `zeta_of_etaPairLim_of_re_ne` (factor discharged via
  `Re ≠ 1`).
* (2) Factor nonvanishing at all center `Re`s: `etaFactor_ne_zero_cellCenter`
  (`Re ∈ {0.395, 0.3, 0.2, 0.105}`), `zeta_of_etaPairLim_cellCenter`,
  `etaFactor_ne_zero_S0` + `zeta_of_etaPairLim_S0` (R00 corner `zetaCellS0`).
* (3) R00 `Azeta` wiring through YOUR bridge (consolidation, not duplication):
  numeral `zetaCellS0_rpow_0395_ge` (`5/4 ≤ 2^0.395`), `zetaCellS0_rpow_0605_le`
  (`2^0.605 ≤ 8/5`), `S₂` closed form + `1/5 ≤ ‖S₂‖`, `‖1 - 2^{1-s0}‖ ≤ 13/5`,
  honest `‖G - S₂‖ ≤ 26` (`M = 1`), general feeder
  `zeta_lower_of_Sn_tail_factor` (`(slow - rtail)/cF ≤ ‖ζ‖`), and R00
  `1/26 ≤ ‖riemannZeta zetaCellS0‖` conditional on the single explicit
  `‖S_{4194304}‖ ≥ 1/5` (honest tail `≤ 0.1` already `zetaCellS0_tail_2097152_le`).
-/

/-- Norm of `2^s`: `‖(2:ℂ)^s‖ = 2^(s.re)` (real rpow). -/
theorem two_cpow_norm (s : ℂ) :
    ‖(2 : ℂ) ^ s‖ = (2 : ℝ) ^ s.re := by
  have h2 : (2 : ℂ) = (((2 : ℝ)) : ℂ) := by norm_cast
  rw [h2, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Norm of the eta factor base: `‖2^{1-s}‖ = 2^{1-Re s}`. -/
theorem two_cpow_one_sub_norm (s : ℂ) :
    ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ = (2 : ℝ) ^ (1 - s.re) := by
  have hre : ((1 : ℂ) - s).re = 1 - s.re := by simp [Complex.sub_re]
  rw [two_cpow_norm, hre]

/-- Real `2^x ≠ 1` when `x ≠ 0` (two-sided: `>1` vs `<1`). -/
theorem two_rpow_ne_one_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    (2 : ℝ) ^ x ≠ 1 := by
  rcases lt_or_gt_of_ne hx with h | h
  · have hlt : (2 : ℝ) ^ x < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) h
    exact ne_of_lt hlt
  · have hgt : (1 : ℝ) < (2 : ℝ) ^ x := Real.one_lt_rpow (by norm_num) h
    exact ne_of_gt hgt

/-- `2^{1-s} ≠ 1` when `s.re ≠ 1` (norm is `2^{1-Re} ≠ 1`). -/
theorem two_cpow_one_sub_ne_one_of_re_ne {s : ℂ} (hre : s.re ≠ 1) :
    (2 : ℂ) ^ ((1 : ℂ) - s) ≠ 1 := by
  intro h
  have hnorm := congrArg (fun x : ℂ => ‖x‖) h
  rw [two_cpow_one_sub_norm, norm_one] at hnorm
  have hexp : (1 - s.re) ≠ 0 := sub_ne_zero.mpr (Ne.symm hre)
  exact two_rpow_ne_one_of_ne_zero hexp hnorm

/-- Eta factor `1 - 2^{1-s} ≠ 0` when `s.re ≠ 1`. -/
theorem etaFactor_ne_zero_of_re_ne {s : ℂ} (hre : s.re ≠ 1) :
    (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) ≠ 0 := by
  intro h
  have heq : (2 : ℂ) ^ ((1 : ℂ) - s) = 1 := (sub_eq_zero.mp h).symm
  exact two_cpow_one_sub_ne_one_of_re_ne hre heq

/-- (1) GENERAL DIVISION BRIDGE: `ζ(s) = (∑' pairs) / (1 - 2^{1-s})` for
    `0 < s.re`, `s ≠ 1`, given factor nonvanishing (via pair identity
    `etaPairLim_eq_etaHurwitz_of_pos` + continuation `etaHurwitz_eq_etaRHS_compl`
    + `eq_div_iff`; generalizes `R00ZetaEM.zeta_lower_R00_of_eta` division step). -/
theorem zeta_of_etaPairLim {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hF : (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) ≠ 0) :
    riemannZeta s = (∑' m, etaPairTerm s m) / (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) := by
  have hPair : (∑' m, etaPairTerm s m) = etaHurwitz s :=
    etaPairLim_eq_etaHurwitz_of_pos hs
  have hmem : s ∈ ({1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact hs1
  have hEq := etaHurwitz_eq_etaRHS_compl hmem
  unfold etaRHS at hEq
  have hId : (∑' m, etaPairTerm s m)
      = (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s := by
    rw [hPair]
    exact hEq
  rw [eq_div_iff hF]
  calc riemannZeta s * (1 - (2 : ℂ) ^ ((1 : ℂ) - s))
      = (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s := mul_comm _ _
    _ = (∑' m, etaPairTerm s m) := hId.symm

/-- (1) Bridge with `Re ≠ 1` discharging the factor (covers all centers;
    note `s ≠ 1` alone is insufficient on the `Re = 1` line where
    `2^{1-s} = 1` at `s = 1 + 2πi k / log 2`, so `Re ≠ 1` is the sharp
    hypothesis; centers satisfy it). -/
theorem zeta_of_etaPairLim_of_re_ne {s : ℂ} (hs : 0 < s.re) (hre : s.re ≠ 1) :
    riemannZeta s = (∑' m, etaPairTerm s m) / (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) := by
  have hs1 : s ≠ 1 := by
    intro h
    apply hre
    rw [h]
    exact Complex.one_re
  exact zeta_of_etaPairLim hs hs1 (etaFactor_ne_zero_of_re_ne hre)

/-- (2) Factor nonvanishing at every central-cover center `Re`. -/
theorem etaFactor_ne_zero_cellCenter {s : ℂ}
    (hs : s.re = 0.395 ∨ s.re = 0.3 ∨ s.re = 0.2 ∨ s.re = 0.105) :
    (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) ≠ 0 := by
  apply etaFactor_ne_zero_of_re_ne
  rcases hs with h | h | h | h <;> rw [h] <;> norm_num

/-- (2) Division at every central-cover center `Re`. -/
theorem zeta_of_etaPairLim_cellCenter {s : ℂ}
    (hs : s.re = 0.395 ∨ s.re = 0.3 ∨ s.re = 0.2 ∨ s.re = 0.105) :
    riemannZeta s = (∑' m, etaPairTerm s m) / (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) := by
  have hpos : 0 < s.re := by
    rcases hs with h | h | h | h <;> rw [h] <;> norm_num
  have hre : s.re ≠ 1 := by
    rcases hs with h | h | h | h <;> rw [h] <;> norm_num
  exact zeta_of_etaPairLim_of_re_ne hpos hre

/-- (2) R00 CORNER factor nonvanishing (`zetaCellS0`, `Re = 0.395`). -/
theorem etaFactor_ne_zero_S0 :
    (1 - (2 : ℂ) ^ ((1 : ℂ) - zetaCellS0)) ≠ 0 :=
  etaFactor_ne_zero_cellCenter (Or.inl zetaCellS0_re)

/-- (2) R00 CORNER division through YOUR bridge. -/
theorem zeta_of_etaPairLim_S0 :
    riemannZeta zetaCellS0 =
      (∑' m, etaPairTerm zetaCellS0 m) / (1 - (2 : ℂ) ^ ((1 : ℂ) - zetaCellS0)) :=
  zeta_of_etaPairLim_cellCenter (Or.inl zetaCellS0_re)

/-- Numeral rpow bound `5/4 ≤ 2^0.395` (cleared: `(5/4)^20 ≤ 2^7`;
    mirrors `R00ZetaEM.rpow_two_R00_ge`, re-proved in-file). -/
theorem zetaCellS0_rpow_0395_ge : (5 / 4 : ℝ) ≤ (2 : ℝ) ^ (0.395 : ℝ) := by
  have hpow : ((5 / 4 : ℝ)) ^ ((20 : ℕ))
      ≤ ((((2 : ℝ) ^ ((7 / 20 : ℝ)))) ^ ((20 : ℕ)) : ℝ) := by
    have e : ((((2 : ℝ) ^ ((7 / 20 : ℝ)))) ^ ((20 : ℕ)) : ℝ)
        = (2 : ℝ) ^ ((7 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [show (7 / 20 : ℝ) * (((20 : ℕ)) : ℝ) = (7 : ℝ) by norm_num]
      rw [show (7 : ℝ) = (((7 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 2 7
    rw [e]
    norm_num
  have hstep : (5 / 4 : ℝ) ≤ (2 : ℝ) ^ ((7 / 20 : ℝ)) :=
    le_of_pow_le_pow_left₀ (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _).le hpow
  calc (5 / 4 : ℝ) ≤ (2 : ℝ) ^ ((7 / 20 : ℝ)) := hstep
    _ ≤ (2 : ℝ) ^ (0.395 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

/-- Numeral rpow bound `2^0.605 ≤ 8/5` (cleared: `2^2 ≤ (8/5)^3`;
    mirrors `R00ZetaEM.rpow_two_R00_le`, re-proved in-file). -/
theorem zetaCellS0_rpow_0605_le : (2 : ℝ) ^ (0.605 : ℝ) ≤ (8 / 5 : ℝ) := by
  have hpow : ((((2 : ℝ) ^ ((2 / 3 : ℝ)))) ^ ((3 : ℕ)) : ℝ)
      ≤ ((8 / 5 : ℝ)) ^ ((3 : ℕ)) := by
    have e : ((((2 : ℝ) ^ ((2 / 3 : ℝ)))) ^ ((3 : ℕ)) : ℝ)
        = (2 : ℝ) ^ ((2 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [show (2 / 3 : ℝ) * (((3 : ℕ)) : ℝ) = (2 : ℝ) by norm_num]
      rw [show (2 : ℝ) = (((2 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 2 2
    rw [e]
    norm_num
  have hstep : (2 : ℝ) ^ ((2 / 3 : ℝ)) ≤ (8 / 5 : ℝ) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  calc (2 : ℝ) ^ (0.605 : ℝ) ≤ (2 : ℝ) ^ ((2 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ (8 / 5 : ℝ) := hstep

/-- `etaDirichletTerm` at `zetaCellS0`, `k = 0` equals `1`. -/
theorem etaDirichletTerm_S0_zero :
    etaDirichletTerm zetaCellS0 0 = 1 := by
  have h01 : (0 + 1 : ℕ) = 1 := rfl
  have hcast : ((((0 + 1 : ℕ)) : ℂ)) = 1 := by rw [h01, Nat.cast_one]
  simp only [etaDirichletTerm, pow_zero, hcast, Complex.one_cpow, div_one]

/-- `etaDirichletTerm` at `zetaCellS0`, `k = 1` equals `-(2^s)⁻¹`. -/
theorem etaDirichletTerm_S0_one :
    etaDirichletTerm zetaCellS0 1 = -((((2 : ℕ) : ℂ) ^ zetaCellS0)⁻¹) := by
  unfold etaDirichletTerm
  rw [pow_one]
  rw [show (((1 + 1 : ℕ) : ℂ)) = ((((2 : ℕ)) : ℂ)) by norm_num]
  rw [neg_div, one_div]

/-- Two-term partial sum `S₂` in closed form. -/
theorem etaDirichlet_S0_two_eq :
    (∑ k ∈ Finset.range 2, etaDirichletTerm zetaCellS0 k)
      = 1 - ((((2 : ℕ) : ℂ) ^ zetaCellS0)⁻¹) := by
  have hsum : (∑ k ∈ Finset.range 2, etaDirichletTerm zetaCellS0 k)
      = etaDirichletTerm zetaCellS0 0 + etaDirichletTerm zetaCellS0 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
  rw [hsum, etaDirichletTerm_S0_zero, etaDirichletTerm_S0_one]
  ring

/-- Modulus of the second term: `‖(2^s)⁻¹‖ = 2^{-0.395} ≤ 4/5`. -/
theorem norm_etaDirichlet_S0_second_le :
    ‖((((2 : ℕ) : ℂ) ^ zetaCellS0)⁻¹)‖ ≤ 4 / 5 := by
  have h2eq : ((((2 : ℕ)) : ℂ)) = (2 : ℂ) := by norm_cast
  rw [h2eq, norm_inv, two_cpow_norm, zetaCellS0_re]
  have hge := zetaCellS0_rpow_0395_ge
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (0.395 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  rw [show (4 / 5 : ℝ) = ((5 / 4 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

/-- Two-term lower bound `1/5 ≤ ‖S₂‖` (reverse triangle; mirrors
    `R00ZetaEM.etaCPartial_two_norm_ge` for `etaDirichletTerm`). -/
theorem etaDirichlet_S0_two_norm_ge :
    (1 / 5 : ℝ) ≤ ‖∑ k ∈ Finset.range 2, etaDirichletTerm zetaCellS0 k‖ := by
  rw [etaDirichlet_S0_two_eq]
  have hX := norm_etaDirichlet_S0_second_le
  have h := norm_add_le
    (1 - ((((2 : ℕ) : ℂ) ^ zetaCellS0)⁻¹))
    ((((2 : ℕ) : ℂ) ^ zetaCellS0)⁻¹)
  rw [sub_add_cancel] at h
  rw [norm_one] at h
  linarith

/-- Conversion-factor upper bound `‖1 - 2^{1-s0}‖ ≤ 13/5` (triangle +
    `2^0.605 ≤ 8/5`; mirrors `R00ZetaEM.factor_upper_R00`). -/
theorem etaFactor_upper_S0 :
    ‖(1 - (2 : ℂ) ^ ((1 : ℂ) - zetaCellS0))‖ ≤ 13 / 5 := by
  have hre : ((1 : ℂ) - zetaCellS0).re = (0.605 : ℝ) := by
    rw [Complex.sub_re, Complex.one_re, zetaCellS0_re]
    norm_num
  have hY : ‖(2 : ℂ) ^ ((1 : ℂ) - zetaCellS0)‖ ≤ 8 / 5 := by
    rw [two_cpow_norm, hre]
    exact zetaCellS0_rpow_0605_le
  calc ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - zetaCellS0)‖
        ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ ((1 : ℂ) - zetaCellS0)‖ := norm_sub_le _ _
    _ ≤ 13 / 5 := by rw [norm_one]; linarith [hY]

/-- Honest small-`N` tail: `‖G - S₂‖ ≤ 26` (`M = 1`, `C = 10`, `σ = 0.395`;
    `10/0.395 ≈ 25.32`; shows the `S₂`-direct route gives a trivial
    (negative) `Azeta`, so longer sums would be needed — infeasible). -/
theorem zetaCellS0_tail_1_le :
    ‖(∑' m, etaPairTerm zetaCellS0 m)
      - (∑ k ∈ Finset.range 2, etaDirichletTerm zetaCellS0 k)‖ ≤ 26 := by
  have hgen := zetaCellS0_tail_general 1 (by norm_num)
  have h21 : 2 * 1 = 2 := by norm_num
  rw [h21] at hgen
  have h1 : ((((1 : ℕ)) : ℝ)) = (1 : ℝ) := by norm_cast
  rw [h1, Real.one_rpow] at hgen
  have hle : (10 : ℝ) * (1 / (0.395 : ℝ)) ≤ 26 := by norm_num
  linarith

/-- (3) GENERAL FEEDER (generalizes `R00ZetaEM.zeta_lower_R00_of_eta`):
    from `‖S‖ ≥ slow`, `‖G - S‖ ≤ rtail`, `‖factor‖ ≤ cF` get
    `(slow - rtail)/cF ≤ ‖ζ‖` via YOUR bridge (no `hId` hypothesis:
    continuation is `zeta_of_etaPairLim_of_re_ne`). -/
theorem zeta_lower_of_Sn_tail_factor {s : ℂ} (hs : 0 < s.re) (hre : s.re ≠ 1)
    (N : ℕ) (S : ℂ) (hSdef : S = ∑ k ∈ Finset.range N, etaDirichletTerm s k)
    (slow : ℝ) (hSlow : slow ≤ ‖S‖)
    (rtail : ℝ) (hTail : ‖(∑' m, etaPairTerm s m) - S‖ ≤ rtail)
    (cF : ℝ) (hcFpos : 0 < cF) (hFac : ‖(1 - (2 : ℂ) ^ ((1 : ℂ) - s))‖ ≤ cF) :
    (slow - rtail) / cF ≤ ‖riemannZeta s‖ := by
  have hZ := zeta_of_etaPairLim_of_re_ne hs hre
  have hFne := etaFactor_ne_zero_of_re_ne hre
  have hGlo : slow - rtail ≤ ‖∑' m, etaPairTerm s m‖ := by
    have htri : ‖S‖ ≤ ‖∑' m, etaPairTerm s m‖ + ‖(∑' m, etaPairTerm s m) - S‖ := by
      have h := norm_sub_le (∑' m, etaPairTerm s m) ((∑' m, etaPairTerm s m) - S)
      have heq : (∑' m, etaPairTerm s m) - ((∑' m, etaPairTerm s m) - S) = S := by
        ring
      rw [heq] at h
      exact h
    linarith [hSlow, hTail, htri]
  have hG_eq : (∑' m, etaPairTerm s m)
      = riemannZeta s * (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) := by
    rw [hZ]
    exact (div_mul_cancel₀ _ hFne).symm
  have hGnorm : ‖∑' m, etaPairTerm s m‖ ≤ ‖riemannZeta s‖ * cF := by
    rw [hG_eq, norm_mul]
    exact mul_le_mul_of_nonneg_left hFac (norm_nonneg _)
  rw [div_le_iff₀ hcFpos]
  linarith [hGlo, hGnorm]

/-- (3) R00 `Azeta = 1/26` wired end-to-end through YOUR bridge, conditional on
    the single explicit `S_{4194304}` lower bound (`N = 2 * 2097152`;
    honest tail `≤ 0.1` is `zetaCellS0_tail_2097152_le`, factor `≤ 13/5` is
    `etaFactor_upper_S0`; `(1/5 - 0.1)/(13/5) = 1/26`).
    Consolidation (not duplication) of `R00ZetaEM.zeta_lower_R00_of_eta`:
    that lemma needs `‖S₂ - L‖ ≤ 1/10` (false: `≈ 0.96`) + `hId`; here `hId`
    is discharged by `zeta_of_etaPairLim_S0` and the tail is the honest `0.1`
    at large `N`, leaving only `‖S_{4194304}‖ ≥ 1/5` (4M cpow terms,
    infeasible — E's finding; smarter bound needed per §18b.10). -/
theorem zeta_S0_lower_of_Slarge (Slarge : ℂ)
    (hSdef : Slarge = ∑ k ∈ Finset.range (2 * 2097152), etaDirichletTerm zetaCellS0 k)
    (hSlow : (1 / 5 : ℝ) ≤ ‖Slarge‖) :
    (1 / 26 : ℝ) ≤ ‖riemannZeta zetaCellS0‖ := by
  have hs := zetaCellS0_pos
  have hre : zetaCellS0.re ≠ 1 := by rw [zetaCellS0_re]; norm_num
  have hTailBase := zetaCellS0_tail_2097152_le
  have hTail : ‖(∑' m, etaPairTerm zetaCellS0 m) - Slarge‖ ≤ (0.1 : ℝ) := by
    rw [hSdef]
    exact hTailBase
  have hFac := etaFactor_upper_S0
  have h := zeta_lower_of_Sn_tail_factor hs hre (2 * 2097152) Slarge hSdef
    (1 / 5) hSlow 0.1 hTail (13 / 5) (by norm_num) hFac
  have heq : (((1 / 5 : ℝ) - 0.1) / (13 / 5)) = 1 / 26 := by norm_num
  rw [heq] at h
  exact h

#print axioms two_cpow_norm
#print axioms two_cpow_one_sub_norm
#print axioms two_rpow_ne_one_of_ne_zero
#print axioms two_cpow_one_sub_ne_one_of_re_ne
#print axioms etaFactor_ne_zero_of_re_ne
#print axioms zeta_of_etaPairLim
#print axioms zeta_of_etaPairLim_of_re_ne
#print axioms etaFactor_ne_zero_cellCenter
#print axioms zeta_of_etaPairLim_cellCenter
#print axioms etaFactor_ne_zero_S0
#print axioms zeta_of_etaPairLim_S0
#print axioms zetaCellS0_rpow_0395_ge
#print axioms zetaCellS0_rpow_0605_le
#print axioms etaDirichletTerm_S0_zero
#print axioms etaDirichletTerm_S0_one
#print axioms etaDirichlet_S0_two_eq
#print axioms norm_etaDirichlet_S0_second_le
#print axioms etaDirichlet_S0_two_norm_ge
#print axioms etaFactor_upper_S0
#print axioms zetaCellS0_tail_1_le
#print axioms zeta_lower_of_Sn_tail_factor
#print axioms zeta_S0_lower_of_Slarge
