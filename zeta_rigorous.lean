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

/-!
## FE-FACTOR bounds at the R00 corner (STONES 1 / 1b / 2).

Grep-first record (searches run before writing; repo + Mathlib):

* STONE 1 (Mathlib FE — FOUND):
  - `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:178-180`
    `theorem riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :`
    `riemannZeta (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * riemannZeta s`
    (here `Gamma = Complex.Gamma`, `cos = Complex.cos`, `π = (Real.pi : ℂ)`;
    file has `open Complex`). Underlying:
    `Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:760-762`
    `hurwitzZetaEven_one_sub` (same cos-factor shape), plus completed forms
    `completedRiemannZeta_one_sub` (RiemannZeta.lean:106) and
    `completedRiemannZeta₀_one_sub` (RiemannZeta.lean:100).
  - Factor form: Mathlib does NOT use the classic
    `χ(s) = 2^s * π^(s-1) * sin(π*s/2) * Gamma(1-s)`; the available tool is the
    cos-form `F(s) = 2 * (2*π)^(-s) * Gamma s * cos(π*s/2)` above
    (equivalent via `s ↔ 1-s`). `zetaFEFactor` below is exactly this `F`.
* STONE 1b / 2 pattern (mirrored, distinct `zetaFE*` names):
  - `interval_arith.lean:CellGammaUniform.norm_sin_pi_half_le_wide` (sine majorant
    `‖sin‖ ≤ exp 16` from `|s.im| ≤ 10`) and `R00GammaLower.norm_sin_pi_half_le`
    (same), `R00GammaLower.exp_sixteen_lt` (`exp 16 < 1e7` via `(exp 1)^16`),
    `R00GammaLower.norm_Gamma_le_realGamma` (integral majorant
    `‖Gamma z‖ ≤ Real.Gamma z.re` for `0 < z.re`), `R00GammaLower.realGamma_one_sub_half_le`
    / `CellGammaUniform.realGamma_one_sub_half_le_wide` (convexity on `[1,2]`
    giving `Gamma(x+1) ≤ 1` then `Gamma(x) ≤ 1/x`). Cos upper reuses the same
    exponential estimate via `Complex.two_cos` (mirrors `two_sin` used for sine).
  - Sine LOWER (`1 ≤ ‖sin‖`) is new here (no sine lower exists in repo:
    `rg "sin_pi|norm_sin"` in `interval_arith.lean` shows only the UPPER and
    `sin_pi_half_ne_wide` nonvanishing): reverse-triangle on the exp difference
    plus `Real.add_one_le_exp` (`exp t ≥ t+1`), so no rpow lower bound is needed.
* Import check (acyclicity; mirror instead of import):
  - `rg ^import zeta_rigorous.lean` → `import Mathlib` only.
  - `rg ^import interval_arith.lean` → `Mathlib`, `riemann_hypothesis`,
    `rh_certificate_infra`, `central_cover_assembly` (NOT `zeta_rigorous`).
  - Transitive deps of `interval_arith` (`central_cover_assembly`,
    `riemann_hypothesis`, `rh_certificate_infra`, `TestAnalytic`,
    `ZeroFreeRegion*`) contain no `import zeta_rigorous`
    (`rg ^import` on each; only `JensenTranslation` / `riemann_hypothesis_newsection`
    import `zeta_rigorous`, neither is a dep of `interval_arith`). Hence
    `zeta_rigorous → interval_arith` would be DAG-safe in principle, but it would
    pull ~30k (`interval_arith`) + ~310k (`central_cover_assembly`) lines into this
    leaf module; per the brief's allowance the minimal Gamma/sine/cos material is
    mirrored below with distinct names (no new import, still `Mathlib`-only).

What is proved below (all unconditional, fully closed, `zetaCellS0 = ⟨0.395,-8.75⟩`):
* `zetaFEFactor`: Mathlib cos-form FE factor `F(s)`.
* `zetaFEw0_im`, `zetaFE_abs_im_le16`: `Im(π*s0/2) = π*(-4.375)`, `|·| ≤ 16`.
* `zetaFE_sin_upper_S0` (`‖sin‖ ≤ exp 16`), `zetaFE_exp16_lt` (`exp 16 < 1e7`),
  `zetaFE_sin_upper_num_S0` (`‖sin‖ ≤ 1e7`, STONE 1b UPPER with `C = 1e7`).
* `zetaFE_sin_lower_S0` (`1 ≤ ‖sin‖`, STONE 1b LOWER with `c = 1`).
* `zetaFE_norm_Gamma_le_realGamma` (integral majorant, mirrored),
  `zetaFE_realGamma_0395_le` (`Real.Gamma 0.395 ≤ 3` via convexity),
  `zetaFE_Gamma_upper_S0` (`‖Gamma s0‖ ≤ 3`).
* `zetaFE_cpow_upper_S0` (`‖(2*π)^(-s0)‖ ≤ 1` via `rpow_le_one_of_one_le_of_nonpos`).
* `zetaFE_cos_upper_S0` (`‖cos‖ ≤ exp 16`), `zetaFE_cos_upper_num_S0` (`≤ 1e7`).
* `zetaFE_factor_upper_S0` (`‖F(s0)‖ ≤ 60000000`, STONE 2 UPPER with `C = 6e7`).
-/

/-- Mathlib cos-form FE factor `F(s) = 2 * (2*π)^(-s) * Gamma s * cos(π*s/2)`
(`riemannZeta_one_sub`, `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:178`). -/
noncomputable def zetaFEFactor (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
    Complex.cos ((Real.pi : ℂ) * s / 2)

/-- `Im(π*s0/2) = π*(-4.375)` (`(s0/2).im = -8.75/2`). -/
theorem zetaFEw0_im :
    ((Real.pi : ℂ) * (zetaCellS0 / 2)).im = Real.pi * (-4.375) := by
  have hs2im : (zetaCellS0 / 2).im = (-4.375 : ℝ) := by
    rw [Complex.div_ofNat_im, zetaCellS0_im]
    norm_num
  simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hs2im]

/-- `|Im(π*s0/2)| ≤ 16` (`4.375*π ≤ 3.1416*5 ≤ 16`). -/
theorem zetaFE_abs_im_le16 :
    |((Real.pi : ℂ) * (zetaCellS0 / 2)).im| ≤ 16 := by
  rw [zetaFEw0_im, abs_mul]
  have h1 : |Real.pi| ≤ 3.1416 := by
    rw [abs_of_pos Real.pi_pos]
    exact le_of_lt Real.pi_lt_d4
  have h2 : |(-4.375 : ℝ)| ≤ 5 := by norm_num
  calc |Real.pi| * |(-4.375 : ℝ)| ≤ 3.1416 * 5 :=
        mul_le_mul h1 h2 (by positivity) (by norm_num)
    _ ≤ 16 := by norm_num

/-- Sine majorant at `s0`: `‖sin(π*s0/2)‖ ≤ exp 16`
(mirrors `CellGammaUniform.norm_sin_pi_half_le_wide` at the corner). -/
theorem zetaFE_sin_upper_S0 :
    ‖Complex.sin ((Real.pi : ℂ) * (zetaCellS0 / 2))‖ ≤ Real.exp 16 := by
  set w : ℂ := (Real.pi : ℂ) * (zetaCellS0 / 2) with hw
  have hw_im_eq : w.im = Real.pi * (-4.375) := by
    rw [hw, zetaFEw0_im]
  have hw_abs : |w.im| ≤ 16 := by
    rw [hw_im_eq]
    have h1 : |Real.pi| ≤ 3.1416 := by
      rw [abs_of_pos Real.pi_pos]
      exact le_of_lt Real.pi_lt_d4
    have h2 : |(-4.375 : ℝ)| ≤ 5 := by norm_num
    calc |Real.pi * (-4.375 : ℝ)| = |Real.pi| * |(-4.375 : ℝ)| := abs_mul _ _
      _ ≤ 3.1416 * 5 :=
          mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ ≤ 16 := by norm_num
  have hsin_eq : Complex.sin w =
      (Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) *
        Complex.I / 2 := by
    unfold Complex.sin; ring
  rw [hsin_eq]
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  have hle : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) *
        Complex.I / 2‖
      ≤ (‖Complex.exp (-w * Complex.I)‖ + ‖Complex.exp (w * Complex.I)‖) / 2 := by
    have h2 : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) *
          Complex.I / 2‖
        = ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ / 2 := by
      simp [norm_div, norm_mul, hI, Complex.norm_ofNat]
    rw [h2]
    exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
  have hre1 : (-w * Complex.I).re = w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]
  have hre2 : (w * Complex.I).re = -w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [Complex.norm_exp, Complex.norm_exp, hre1, hre2] at hle
  have e1 : Real.exp w.im ≤ Real.exp 16 :=
    Real.exp_le_exp.mpr (le_trans (le_abs_self _) hw_abs)
  have e2 : Real.exp (-w.im) ≤ Real.exp 16 := by
    apply Real.exp_le_exp.mpr
    have : -w.im ≤ |w.im| := neg_le_abs _
    exact le_trans this hw_abs
  linarith

/-- `Real.exp 16 < 10000000` via `(exp 1)^16` (mirrors `R00GammaLower.exp_sixteen_lt`). -/
theorem zetaFE_exp16_lt : Real.exp 16 < 10000000 := by
  have h1 : Real.exp (16 : ℝ) = (Real.exp 1) ^ (16 : ℕ) := by
    have := Real.exp_nat_mul (1 : ℝ) (16 : ℕ)
    simpa using this.symm
  have h2 : (Real.exp 1) ^ (16 : ℕ) < (2.7182818286 : ℝ) ^ (16 : ℕ) := by
    apply pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos _)) (by norm_num)
  have h3 : (2.7182818286 : ℝ) ^ (16 : ℕ) < 10000000 := by norm_num
  rw [h1]
  exact lt_trans h2 h3

/-- STONE 1b UPPER: `‖sin(π*s0/2)‖ ≤ 10000000` (`C = 1e7`). -/
theorem zetaFE_sin_upper_num_S0 :
    ‖Complex.sin ((Real.pi : ℂ) * (zetaCellS0 / 2))‖ ≤ 10000000 :=
  le_trans zetaFE_sin_upper_S0 (le_of_lt zetaFE_exp16_lt)

/-- STONE 1b LOWER: `1 ≤ ‖sin(π*s0/2)‖` (`c = 1`, reverse-triangle + `exp t ≥ t+1`). -/
theorem zetaFE_sin_lower_S0 :
    (1 : ℝ) ≤ ‖Complex.sin ((Real.pi : ℂ) * (zetaCellS0 / 2))‖ := by
  set w : ℂ := (Real.pi : ℂ) * (zetaCellS0 / 2) with hw
  have hw_im_eq : w.im = Real.pi * (-4.375) := by
    rw [hw, zetaFEw0_im]
  have hw_le : w.im ≤ (-13.125 : ℝ) := by
    rw [hw_im_eq]
    have heq : Real.pi * (-4.375 : ℝ) = -(4.375 * Real.pi) := by ring
    rw [heq]
    have hmul : (13.125 : ℝ) ≤ 4.375 * Real.pi := by
      have hpi3 := Real.pi_gt_three
      have hpos : (0 : ℝ) < 4.375 := by norm_num
      have h := mul_lt_mul_of_pos_left hpi3 hpos
      have heq2 : (4.375 : ℝ) * 3 = 13.125 := by norm_num
      linarith
    linarith
  have hsin_eq : Complex.sin w =
      (Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) *
        Complex.I / 2 := by
    unfold Complex.sin; ring
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  have hsin_norm : ‖Complex.sin w‖ =
      ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ / 2 := by
    rw [hsin_eq]
    simp [norm_div, norm_mul, hI, Complex.norm_ofNat]
  have hre1 : (-w * Complex.I).re = w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]
  have hre2 : (w * Complex.I).re = -w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  have hnorm1 : ‖Complex.exp (-w * Complex.I)‖ = Real.exp w.im := by
    rw [Complex.norm_exp, hre1]
  have hnorm2 : ‖Complex.exp (w * Complex.I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp, hre2]
  have hrev : ‖Complex.exp (w * Complex.I)‖ - ‖Complex.exp (-w * Complex.I)‖ ≤
      ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ := by
    have h := norm_sub_norm_le (Complex.exp (w * Complex.I))
      (Complex.exp (-w * Complex.I))
    rwa [norm_sub_rev] at h
  have hexp_small : Real.exp w.im ≤ 1 := by
    have h0 : w.im ≤ 0 := by linarith
    calc Real.exp w.im ≤ Real.exp 0 := Real.exp_le_exp.mpr h0
      _ = 1 := Real.exp_zero
  have hexp_big : (14.125 : ℝ) ≤ Real.exp (-w.im) := by
    have hge : (13.125 : ℝ) ≤ -w.im := by linarith
    have h1 : (-w.im) + 1 ≤ Real.exp (-w.im) := Real.add_one_le_exp _
    linarith
  have hlow : (13.125 : ℝ) ≤
      ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ := by
    rw [← hnorm2] at hexp_big
    rw [← hnorm1] at hexp_small
    linarith [hrev, hexp_big, hexp_small]
  rw [hsin_norm]
  linarith

/-- Integral majorant (mirrors `R00GammaLower.norm_Gamma_le_realGamma`):
`‖Gamma z‖ ≤ Real.Gamma z.re` for `0 < z.re`. -/
theorem zetaFE_norm_Gamma_le_realGamma {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  have hC := Complex.GammaIntegral_convergent hz
  have hR := Real.GammaIntegral_convergent hz
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz]
  unfold Complex.GammaIntegral
  calc ‖∫ x in Set.Ioi (0 : ℝ), ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (z - 1)‖
      ≤ ∫ x in Set.Ioi (0 : ℝ), ‖((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (z - 1)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ (z.re - 1) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        have hx0 : (0 : ℝ) < x := Set.mem_Ioi.mp hx
        show ‖((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (z - 1)‖ = _
        rw [norm_mul]
        have h1 : ‖((Real.exp (-x) : ℝ) : ℂ)‖ = Real.exp (-x) :=
          Complex.norm_of_nonneg (le_of_lt (Real.exp_pos _))
        have h2 : ‖(x : ℂ) ^ (z - 1)‖ = x ^ ((z - 1).re) :=
          Complex.norm_cpow_eq_rpow_re_of_pos hx0 _
        rw [h1, h2]
        have hexp : (z - 1).re = z.re - 1 := by simp [Complex.sub_re]
        rw [hexp]

/-- Real-Gamma cap at `0.395`: `Real.Gamma 0.395 ≤ 3`
(convexity on `[1,2]` gives `Gamma(1.395) ≤ 1`, then `Gamma(0.395) ≤ 1/0.395 ≤ 3`). -/
theorem zetaFE_realGamma_0395_le : Real.Gamma (0.395 : ℝ) ≤ 3 := by
  have hx_pos : (0 : ℝ) < 0.395 := by norm_num
  have hy_mem1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have hy_mem2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have hconv := Real.convexOn_Gamma
  have ha_nn : (0 : ℝ) ≤ 2 - ((0.395 : ℝ) + 1) := by norm_num
  have hb_nn : (0 : ℝ) ≤ ((0.395 : ℝ) + 1) - 1 := by norm_num
  have hab : ((2 : ℝ) - ((0.395 : ℝ) + 1)) + (((0.395 : ℝ) + 1) - 1) = 1 := by ring
  have h := hconv.2 hy_mem1 hy_mem2 ha_nn hb_nn hab
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
  have heq : ((2 : ℝ) - ((0.395 : ℝ) + 1)) * 1 + (((0.395 : ℝ) + 1) - 1) * 2 =
      (0.395 : ℝ) + 1 := by ring
  rw [heq] at h
  have hrhs : ((2 : ℝ) - ((0.395 : ℝ) + 1)) * 1 + (((0.395 : ℝ) + 1) - 1) * 1 =
      (1 : ℝ) := by ring
  rw [hrhs] at h
  have hne : (0.395 : ℝ) ≠ 0 := by norm_num
  have hadd := Real.Gamma_add_one hne
  rw [hadd] at h
  have hfin : Real.Gamma (0.395 : ℝ) ≤ 1 / 0.395 := by
    rw [le_div_iff₀ hx_pos, mul_comm]
    exact h
  have hfrac : (1 : ℝ) / 0.395 ≤ 3 := by norm_num
  exact le_trans hfin hfrac

/-- Gamma upper at `s0`: `‖Gamma s0‖ ≤ 3`. -/
theorem zetaFE_Gamma_upper_S0 : ‖Complex.Gamma zetaCellS0‖ ≤ 3 := by
  have hre : 0 < zetaCellS0.re := zetaCellS0_pos
  have hle := zetaFE_norm_Gamma_le_realGamma hre
  rw [zetaCellS0_re] at hle
  exact le_trans hle zetaFE_realGamma_0395_le

/-- Cpow upper at `s0`: `‖(2*π)^(-s0)‖ ≤ 1` (`(2π)^(-0.395) ≤ 1`). -/
theorem zetaFE_cpow_upper_S0 :
    ‖(2 * (Real.pi : ℂ)) ^ (-zetaCellS0)‖ ≤ 1 := by
  have hbase_pos : (0 : ℝ) < 2 * Real.pi := by
    have := Real.pi_pos
    linarith
  have h2pi : ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    push_cast; ring
  have hnorm : ‖(2 * (Real.pi : ℂ)) ^ (-zetaCellS0)‖ =
      (2 * Real.pi) ^ (-(zetaCellS0.re)) := by
    rw [← h2pi, Complex.norm_cpow_eq_rpow_re_of_pos hbase_pos, Complex.neg_re]
  rw [hnorm, zetaCellS0_re]
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · have hpi := Real.pi_gt_three
    linarith
  · norm_num

/-- Cosine majorant at `s0`: `‖cos(π*s0/2)‖ ≤ exp 16` (same estimate via `two_cos`). -/
theorem zetaFE_cos_upper_S0 :
    ‖Complex.cos ((Real.pi : ℂ) * (zetaCellS0 / 2))‖ ≤ Real.exp 16 := by
  set w : ℂ := (Real.pi : ℂ) * (zetaCellS0 / 2) with hw
  have hw_im_eq : w.im = Real.pi * (-4.375) := by
    rw [hw, zetaFEw0_im]
  have hw_abs : |w.im| ≤ 16 := by
    rw [hw_im_eq]
    have h1 : |Real.pi| ≤ 3.1416 := by
      rw [abs_of_pos Real.pi_pos]
      exact le_of_lt Real.pi_lt_d4
    have h2 : |(-4.375 : ℝ)| ≤ 5 := by norm_num
    calc |Real.pi * (-4.375 : ℝ)| = |Real.pi| * |(-4.375 : ℝ)| := abs_mul _ _
      _ ≤ 3.1416 * 5 :=
          mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ ≤ 16 := by norm_num
  have hcos_eq : Complex.cos w =
      (Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)) / 2 := by
    unfold Complex.cos; ring
  rw [hcos_eq]
  have hle : ‖(Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)) / 2‖
      ≤ (‖Complex.exp (w * Complex.I)‖ + ‖Complex.exp (-w * Complex.I)‖) / 2 := by
    have h2 : ‖(Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)) / 2‖
        = ‖Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)‖ / 2 := by
      simp [norm_div, Complex.norm_ofNat]
    rw [h2]
    exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
  have hre1 : (w * Complex.I).re = -w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  have hre2 : (-w * Complex.I).re = w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]
  rw [Complex.norm_exp, Complex.norm_exp, hre1, hre2] at hle
  have e1 : Real.exp (-w.im) ≤ Real.exp 16 := by
    apply Real.exp_le_exp.mpr
    have : -w.im ≤ |w.im| := neg_le_abs _
    exact le_trans this hw_abs
  have e2 : Real.exp w.im ≤ Real.exp 16 :=
    Real.exp_le_exp.mpr (le_trans (le_abs_self _) hw_abs)
  linarith

/-- Cosine numeral cap: `‖cos(π*s0/2)‖ ≤ 10000000`. -/
theorem zetaFE_cos_upper_num_S0 :
    ‖Complex.cos ((Real.pi : ℂ) * (zetaCellS0 / 2))‖ ≤ 10000000 :=
  le_trans zetaFE_cos_upper_S0 (le_of_lt zetaFE_exp16_lt)

/-- STONE 2 UPPER: `‖F(s0)‖ ≤ 60000000` (`2 * 1 * 3 * 1e7`). -/
theorem zetaFE_factor_upper_S0 : ‖zetaFEFactor zetaCellS0‖ ≤ 60000000 := by
  have hcos : ‖Complex.cos ((Real.pi : ℂ) * zetaCellS0 / 2)‖ ≤ 10000000 := by
    rw [mul_div_assoc]
    exact zetaFE_cos_upper_num_S0
  have hG := zetaFE_Gamma_upper_S0
  have hcp := zetaFE_cpow_upper_S0
  have e2 : ‖(2 : ℂ)‖ = 2 := by simp
  have hnorm_eq : ‖zetaFEFactor zetaCellS0‖ =
      ‖(2 : ℂ)‖ * ‖(2 * (Real.pi : ℂ)) ^ (-zetaCellS0)‖ *
        ‖Complex.Gamma zetaCellS0‖ *
        ‖Complex.cos ((Real.pi : ℂ) * zetaCellS0 / 2)‖ := by
    unfold zetaFEFactor
    simp [norm_mul, mul_assoc]
  rw [hnorm_eq, e2]
  have hprod : 2 * ‖(2 * (Real.pi : ℂ)) ^ (-zetaCellS0)‖ *
      ‖Complex.Gamma zetaCellS0‖ *
      ‖Complex.cos ((Real.pi : ℂ) * zetaCellS0 / 2)‖ ≤
      2 * 1 * 3 * 10000000 := by
    apply mul_le_mul
    · apply mul_le_mul
      · apply mul_le_mul (le_refl 2) hcp (norm_nonneg _) (by norm_num)
      · exact hG
      · exact norm_nonneg _
      · norm_num
    · exact hcos
    · exact norm_nonneg _
    · norm_num
  have heq : (2 : ℝ) * 1 * 3 * 10000000 = 60000000 := by norm_num
  linarith [hprod, heq]

#print axioms zetaFEFactor
#print axioms zetaFEw0_im
#print axioms zetaFE_abs_im_le16
#print axioms zetaFE_sin_upper_S0
#print axioms zetaFE_exp16_lt
#print axioms zetaFE_sin_upper_num_S0
#print axioms zetaFE_sin_lower_S0
#print axioms zetaFE_norm_Gamma_le_realGamma
#print axioms zetaFE_realGamma_0395_le
#print axioms zetaFE_Gamma_upper_S0
#print axioms zetaFE_cpow_upper_S0
#print axioms zetaFE_cos_upper_S0
#print axioms zetaFE_cos_upper_num_S0
#print axioms zetaFE_factor_upper_S0

/-!
## FE LOWER bound at the R00 corner (`c ≤ ‖F(s0)‖`, sketched `c≈1e-14` route).

Greps (verified 2026-09-03, Mathlib-only, documented per brief):
* reflection: `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:397-398`
  `Complex.Gamma_mul_Gamma_one_sub (z : ℂ) : Gamma z * Gamma (1 - z) = π / sin (π * z)`
  (+ `Gamma_ne_zero_of_re_pos` at `Beta.lean:453`); real version at `Beta.lean:478`.
* rpow: `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:615`
  `Real.rpow_le_rpow_of_exponent_le (hx : 1 ≤ x) (hyz : y ≤ z)`, `:668`
  `Real.rpow_le_one_of_one_le_of_nonpos` (used by `zetaFE_cpow_upper_S0`), `:473`
  `Real.rpow_neg_one`, `:337` `Complex.norm_cpow_eq_rpow_re_of_pos`
  (used by `zetaFE_cpow_upper_S0`).
* pi/exp: `Mathlib/Analysis/Real/Pi/Bounds.lean:151` `Real.pi_gt_three`,
  `:172` `Real.pi_lt_d4`; `Mathlib/Analysis/Complex/ExponentialBounds.lean:38`
  `Real.exp_one_lt_d9` (used by `zetaFE_exp16_lt`).
* trig: `Mathlib/Analysis/Complex/Trigonometric.lean:281` `Complex.two_sin`,
  `:284` `Complex.two_cos` (here `unfold Complex.sin/cos; ring` mirrors
  `zetaFE_sin_upper_S0` / `zetaFE_cos_upper_S0` / `zetaFE_sin_lower_S0`).
* RCLike norm: `Mathlib/Analysis/RCLike/Basic.lean:246` `RCLike.norm_ofReal`.

What is proved below (all unconditional, fully closed, `zetaCellS0 = ⟨0.395,-8.75⟩`):
* (a) `zetaFE_cpow_lower_S0` (`1/7 ≤ ‖(2π)^(-s0)‖`).
* (b) `zetaFE_cos_lower_S0` (`1 ≤ ‖cos(π*s0/2)‖`).
* (c) helpers `zetaFE_sin_pi_upper_S0` (`‖sin(π*s0)‖ ≤ exp 28`),
  `zetaFE_exp28_lt` (`exp 28 < 2e12`), `zetaFE_sin_pi_upper_num_S0` (`≤ 2e12`),
  `zetaFE_realGamma_0605_le` (`Real.Gamma 0.605 ≤ 2`),
  `zetaFE_Gamma_one_sub_upper_S0` (`‖Gamma(1-s0)‖ ≤ 2`),
  `zetaFE_Gamma_lower_S0` (`1e-13 ≤ ‖Gamma s0‖` via reflection).
* assembly `zetaFE_factor_lower_S0` (`1e-14 ≤ ‖F(s0)‖`).
-/

/-- Cpow lower at `s0`: `1/7 ≤ ‖(2π)^(-s0)‖`
(`(2π)^(-0.395) ≥ (2π)^(-1) = 1/(2π) ≥ 1/7`, mirrors `zetaFE_cpow_upper_S0`). -/
theorem zetaFE_cpow_lower_S0 :
    (1 : ℝ) / 7 ≤ ‖(2 * (Real.pi : ℂ)) ^ (-zetaCellS0)‖ := by
  have hbase_pos : (0 : ℝ) < 2 * Real.pi := by
    have := Real.pi_pos
    linarith
  have h2pi : ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    push_cast; ring
  have hnorm : ‖(2 * (Real.pi : ℂ)) ^ (-zetaCellS0)‖ =
      (2 * Real.pi) ^ (-(zetaCellS0.re)) := by
    rw [← h2pi, Complex.norm_cpow_eq_rpow_re_of_pos hbase_pos, Complex.neg_re]
  rw [hnorm, zetaCellS0_re]
  have hge1 : (1 : ℝ) ≤ 2 * Real.pi := by
    have hpi := Real.pi_gt_three
    linarith
  have hle7 : (2 : ℝ) * Real.pi ≤ 7 := by
    have h := Real.pi_lt_d4
    linarith
  have hexp : (-1 : ℝ) ≤ -(0.395 : ℝ) := by norm_num
  have hmono : (2 * Real.pi) ^ (-1 : ℝ) ≤ (2 * Real.pi) ^ (-(0.395 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hge1 hexp
  have heq : (2 * Real.pi : ℝ) ^ (-1 : ℝ) = 1 / (2 * Real.pi) := by
    rw [Real.rpow_neg_one, inv_eq_one_div]
  have hinv : (1 : ℝ) / 7 ≤ 1 / (2 * Real.pi) :=
    one_div_le_one_div_of_le hbase_pos hle7
  calc (1 : ℝ) / 7 ≤ 1 / (2 * Real.pi) := hinv
    _ = (2 * Real.pi) ^ (-1 : ℝ) := heq.symm
    _ ≤ (2 * Real.pi) ^ (-(0.395 : ℝ)) := hmono

/-- Cosine lower at `s0`: `1 ≤ ‖cos(π*s0/2)‖`
(reverse-triangle SUM form, mirrors `zetaFE_sin_lower_S0`). -/
theorem zetaFE_cos_lower_S0 :
    (1 : ℝ) ≤ ‖Complex.cos ((Real.pi : ℂ) * (zetaCellS0 / 2))‖ := by
  set w : ℂ := (Real.pi : ℂ) * (zetaCellS0 / 2) with hw
  have hw_im_eq : w.im = Real.pi * (-4.375) := by
    rw [hw, zetaFEw0_im]
  have hw_le : w.im ≤ (-13.125 : ℝ) := by
    rw [hw_im_eq]
    have heq : Real.pi * (-4.375 : ℝ) = -(4.375 * Real.pi) := by ring
    rw [heq]
    have hmul : (13.125 : ℝ) ≤ 4.375 * Real.pi := by
      have hpi3 := Real.pi_gt_three
      have hpos : (0 : ℝ) < 4.375 := by norm_num
      have h := mul_lt_mul_of_pos_left hpi3 hpos
      have heq2 : (4.375 : ℝ) * 3 = 13.125 := by norm_num
      linarith
    linarith
  have hcos_eq : Complex.cos w =
      (Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)) / 2 := by
    unfold Complex.cos; ring
  have hcos_norm : ‖Complex.cos w‖ =
      ‖Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)‖ / 2 := by
    rw [hcos_eq]
    simp [norm_div, Complex.norm_ofNat]
  have hre1 : (w * Complex.I).re = -w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  have hre2 : (-w * Complex.I).re = w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]
  have hnorm_big : ‖Complex.exp (w * Complex.I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp, hre1]
  have hnorm_small : ‖Complex.exp (-w * Complex.I)‖ = Real.exp w.im := by
    rw [Complex.norm_exp, hre2]
  have hrev : ‖Complex.exp (w * Complex.I)‖ - ‖Complex.exp (-w * Complex.I)‖ ≤
      ‖Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)‖ := by
    have htri : ‖Complex.exp (w * Complex.I)‖ ≤
        ‖Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)‖ +
          ‖Complex.exp (-w * Complex.I)‖ := by
      have h := norm_add_le (Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I))
        (-Complex.exp (-w * Complex.I))
      have heq : (Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)) +
          (-Complex.exp (-w * Complex.I)) = Complex.exp (w * Complex.I) := by
        ring
      rw [heq] at h
      simpa [norm_neg] using h
    linarith
  have hexp_small : Real.exp w.im ≤ 1 := by
    have h0 : w.im ≤ 0 := by linarith
    calc Real.exp w.im ≤ Real.exp 0 := Real.exp_le_exp.mpr h0
      _ = 1 := Real.exp_zero
  have hexp_big : (14.125 : ℝ) ≤ Real.exp (-w.im) := by
    have hge : (13.125 : ℝ) ≤ -w.im := by linarith
    have h1 : (-w.im) + 1 ≤ Real.exp (-w.im) := Real.add_one_le_exp _
    linarith
  have hlow : (13.125 : ℝ) ≤
      ‖Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)‖ := by
    rw [← hnorm_big] at hexp_big
    rw [← hnorm_small] at hexp_small
    linarith [hrev, hexp_big, hexp_small]
  rw [hcos_norm]
  linarith

/-- Sine majorant at `π*s0`: `‖sin(π*s0)‖ ≤ exp 28` (same estimate, `|Im| ≤ 28`). -/
theorem zetaFE_sin_pi_upper_S0 :
    ‖Complex.sin ((Real.pi : ℂ) * zetaCellS0)‖ ≤ Real.exp 28 := by
  set w : ℂ := (Real.pi : ℂ) * zetaCellS0 with hw
  have hw_im_eq : w.im = Real.pi * (-8.75) := by
    rw [hw]
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zetaCellS0_im]
  have hw_abs : |w.im| ≤ 28 := by
    rw [hw_im_eq, abs_mul]
    have h1 : |Real.pi| ≤ 3.1416 := by
      rw [abs_of_pos Real.pi_pos]
      exact le_of_lt Real.pi_lt_d4
    have h2 : |(-8.75 : ℝ)| ≤ 8.75 := by norm_num
    calc |Real.pi| * |(-8.75 : ℝ)| ≤ 3.1416 * 8.75 :=
          mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ ≤ 28 := by norm_num
  have hsin_eq : Complex.sin w =
      (Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) *
        Complex.I / 2 := by
    unfold Complex.sin; ring
  rw [hsin_eq]
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  have hle : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) *
        Complex.I / 2‖
      ≤ (‖Complex.exp (-w * Complex.I)‖ + ‖Complex.exp (w * Complex.I)‖) / 2 := by
    have h2 : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) *
          Complex.I / 2‖
        = ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ / 2 := by
      simp [norm_div, norm_mul, hI, Complex.norm_ofNat]
    rw [h2]
    exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
  have hre1 : (-w * Complex.I).re = w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]
  have hre2 : (w * Complex.I).re = -w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [Complex.norm_exp, Complex.norm_exp, hre1, hre2] at hle
  have e1 : Real.exp w.im ≤ Real.exp 28 :=
    Real.exp_le_exp.mpr (le_trans (le_abs_self _) hw_abs)
  have e2 : Real.exp (-w.im) ≤ Real.exp 28 := by
    apply Real.exp_le_exp.mpr
    have : -w.im ≤ |w.im| := neg_le_abs _
    exact le_trans this hw_abs
  linarith

/-- `Real.exp 28 < 2000000000000` via `(exp 1)^28` (mirrors `zetaFE_exp16_lt`). -/
theorem zetaFE_exp28_lt : Real.exp 28 < 2000000000000 := by
  have h1 : Real.exp (28 : ℝ) = (Real.exp 1) ^ (28 : ℕ) := by
    have := Real.exp_nat_mul (1 : ℝ) (28 : ℕ)
    simpa using this.symm
  have h2 : (Real.exp 1) ^ (28 : ℕ) < (2.7182818286 : ℝ) ^ (28 : ℕ) := by
    apply pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos _)) (by norm_num)
  have h3 : (2.7182818286 : ℝ) ^ (28 : ℕ) < 2000000000000 := by norm_num
  rw [h1]
  exact lt_trans h2 h3

/-- Sine numeral cap at `π*s0`: `‖sin(π*s0)‖ ≤ 2000000000000`. -/
theorem zetaFE_sin_pi_upper_num_S0 :
    ‖Complex.sin ((Real.pi : ℂ) * zetaCellS0)‖ ≤ 2000000000000 :=
  le_trans zetaFE_sin_pi_upper_S0 (le_of_lt zetaFE_exp28_lt)

/-- Real-Gamma cap at `0.605`: `Real.Gamma 0.605 ≤ 2`
(convexity on `[1,2]` gives `Gamma(1.605) ≤ 1`, then `Gamma(0.605) ≤ 1/0.605 ≤ 2`,
mirrors `zetaFE_realGamma_0395_le`). -/
theorem zetaFE_realGamma_0605_le : Real.Gamma (0.605 : ℝ) ≤ 2 := by
  have hx_pos : (0 : ℝ) < 0.605 := by norm_num
  have hy_mem1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have hy_mem2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have hconv := Real.convexOn_Gamma
  have ha_nn : (0 : ℝ) ≤ 2 - ((0.605 : ℝ) + 1) := by norm_num
  have hb_nn : (0 : ℝ) ≤ ((0.605 : ℝ) + 1) - 1 := by norm_num
  have hab : ((2 : ℝ) - ((0.605 : ℝ) + 1)) + (((0.605 : ℝ) + 1) - 1) = 1 := by ring
  have h := hconv.2 hy_mem1 hy_mem2 ha_nn hb_nn hab
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
  have heq : ((2 : ℝ) - ((0.605 : ℝ) + 1)) * 1 + (((0.605 : ℝ) + 1) - 1) * 2 =
      (0.605 : ℝ) + 1 := by ring
  rw [heq] at h
  have hrhs : ((2 : ℝ) - ((0.605 : ℝ) + 1)) * 1 + (((0.605 : ℝ) + 1) - 1) * 1 =
      (1 : ℝ) := by ring
  rw [hrhs] at h
  have hne : (0.605 : ℝ) ≠ 0 := by norm_num
  have hadd := Real.Gamma_add_one hne
  rw [hadd] at h
  have hfin : Real.Gamma (0.605 : ℝ) ≤ 1 / 0.605 := by
    rw [le_div_iff₀ hx_pos, mul_comm]
    exact h
  have hfrac : (1 : ℝ) / 0.605 ≤ 2 := by norm_num
  exact le_trans hfin hfrac

/-- Gamma upper at `1-s0`: `‖Gamma(1-s0)‖ ≤ 2` (`Re = 0.605`). -/
theorem zetaFE_Gamma_one_sub_upper_S0 : ‖Complex.Gamma (1 - zetaCellS0)‖ ≤ 2 := by
  have hre_pos : 0 < (1 - zetaCellS0).re := by
    rw [Complex.sub_re, Complex.one_re, zetaCellS0_re]
    norm_num
  have hle := zetaFE_norm_Gamma_le_realGamma hre_pos
  have hre_eq : (1 - zetaCellS0).re = (0.605 : ℝ) := by
    rw [Complex.sub_re, Complex.one_re, zetaCellS0_re]
    norm_num
  rw [hre_eq] at hle
  exact le_trans hle zetaFE_realGamma_0605_le

/-- Gamma lower at `s0`: `1e-13 ≤ ‖Gamma s0‖` via reflection
(`Gamma(s0)·Gamma(1-s0) = π/sin(π*s0)`, `‖sin‖ ≤ 2e12`, `‖Gamma(1-s0)‖ ≤ 2`). -/
theorem zetaFE_Gamma_lower_S0 :
    (1 : ℝ) / 10000000000000 ≤ ‖Complex.Gamma zetaCellS0‖ := by
  have hre0 : 0 < zetaCellS0.re := zetaCellS0_pos
  have hre1 : 0 < (1 - zetaCellS0).re := by
    rw [Complex.sub_re, Complex.one_re, zetaCellS0_re]
    norm_num
  have hG0_ne : Complex.Gamma zetaCellS0 ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hre0
  have hG1_ne : Complex.Gamma (1 - zetaCellS0) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hre1
  have hrefl := Complex.Gamma_mul_Gamma_one_sub zetaCellS0
  have hG1_le : ‖Complex.Gamma (1 - zetaCellS0)‖ ≤ 2 :=
    zetaFE_Gamma_one_sub_upper_S0
  have hS_le : ‖Complex.sin ((Real.pi : ℂ) * zetaCellS0)‖ ≤ 2000000000000 :=
    zetaFE_sin_pi_upper_num_S0
  have hprod_ne : Complex.Gamma zetaCellS0 * Complex.Gamma (1 - zetaCellS0) ≠ 0 :=
    mul_ne_zero hG0_ne hG1_ne
  have hS_ne : Complex.sin ((Real.pi : ℂ) * zetaCellS0) ≠ 0 := by
    intro hcon
    rw [hcon, div_zero] at hrefl
    exact hprod_ne hrefl
  have hS_pos : 0 < ‖Complex.sin ((Real.pi : ℂ) * zetaCellS0)‖ :=
    norm_pos_iff.mpr hS_ne
  have hG0_nonneg : 0 ≤ ‖Complex.Gamma zetaCellS0‖ := norm_nonneg _
  have hS_nonneg : 0 ≤ ‖Complex.sin ((Real.pi : ℂ) * zetaCellS0)‖ := norm_nonneg _
  have hnorm_prod : ‖Complex.Gamma zetaCellS0‖ * ‖Complex.Gamma (1 - zetaCellS0)‖ =
      Real.pi / ‖Complex.sin ((Real.pi : ℂ) * zetaCellS0)‖ := by
    calc ‖Complex.Gamma zetaCellS0‖ * ‖Complex.Gamma (1 - zetaCellS0)‖
        = ‖Complex.Gamma zetaCellS0 * Complex.Gamma (1 - zetaCellS0)‖ :=
          (norm_mul _ _).symm
      _ = ‖(Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * zetaCellS0)‖ := by
          rw [hrefl]
      _ = Real.pi / ‖Complex.sin ((Real.pi : ℂ) * zetaCellS0)‖ := by
          rw [norm_div, Complex.norm_of_nonneg (le_of_lt Real.pi_pos)]
  have hS_ne' : ‖Complex.sin ((Real.pi : ℂ) * zetaCellS0)‖ ≠ 0 :=
    ne_of_gt hS_pos
  have hprod_eq : ‖Complex.Gamma zetaCellS0‖ * ‖Complex.Gamma (1 - zetaCellS0)‖ *
      ‖Complex.sin ((Real.pi : ℂ) * zetaCellS0)‖ = Real.pi := by
    rw [hnorm_prod, div_mul_cancel₀ _ hS_ne']
  have hpi_ge : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
  have hGS_le : ‖Complex.Gamma (1 - zetaCellS0)‖ *
      ‖Complex.sin ((Real.pi : ℂ) * zetaCellS0)‖ ≤ 2 * 2000000000000 := by
    exact mul_le_mul hG1_le hS_le hS_nonneg (by norm_num)
  have hprod_le : ‖Complex.Gamma zetaCellS0‖ * ‖Complex.Gamma (1 - zetaCellS0)‖ *
      ‖Complex.sin ((Real.pi : ℂ) * zetaCellS0)‖ ≤
      ‖Complex.Gamma zetaCellS0‖ * (2 * 2000000000000) := by
    calc ‖Complex.Gamma zetaCellS0‖ * ‖Complex.Gamma (1 - zetaCellS0)‖ *
        ‖Complex.sin ((Real.pi : ℂ) * zetaCellS0)‖
        = ‖Complex.Gamma zetaCellS0‖ *
          (‖Complex.Gamma (1 - zetaCellS0)‖ *
            ‖Complex.sin ((Real.pi : ℂ) * zetaCellS0)‖) := by ring
      _ ≤ ‖Complex.Gamma zetaCellS0‖ * (2 * 2000000000000) :=
          mul_le_mul_of_nonneg_left hGS_le hG0_nonneg
  have hpi_le_prod : (3 : ℝ) ≤ ‖Complex.Gamma zetaCellS0‖ * (2 * 2000000000000) := by
    calc (3 : ℝ) ≤ Real.pi := hpi_ge
      _ = ‖Complex.Gamma zetaCellS0‖ * ‖Complex.Gamma (1 - zetaCellS0)‖ *
          ‖Complex.sin ((Real.pi : ℂ) * zetaCellS0)‖ := hprod_eq.symm
      _ ≤ ‖Complex.Gamma zetaCellS0‖ * (2 * 2000000000000) := hprod_le
  have hdiv_le : (3 : ℝ) / (2 * 2000000000000) ≤ ‖Complex.Gamma zetaCellS0‖ := by
    rw [div_le_iff₀ (by norm_num)]
    exact hpi_le_prod
  have hfinal : (1 : ℝ) / 10000000000000 ≤ (3 : ℝ) / (2 * 2000000000000) := by norm_num
  exact le_trans hfinal hdiv_le

/-- STONE 2 LOWER: `1e-14 ≤ ‖F(s0)‖` (`2·(1/7)·1e-13·1`). -/
theorem zetaFE_factor_lower_S0 :
    (1 : ℝ) / 100000000000000 ≤ ‖zetaFEFactor zetaCellS0‖ := by
  have hcp := zetaFE_cpow_lower_S0
  have hG := zetaFE_Gamma_lower_S0
  have hcos0 := zetaFE_cos_lower_S0
  have hcos : (1 : ℝ) ≤ ‖Complex.cos ((Real.pi : ℂ) * zetaCellS0 / 2)‖ := by
    rw [mul_div_assoc]
    exact hcos0
  have e2 : ‖(2 : ℂ)‖ = 2 := by simp
  have hnorm_eq : ‖zetaFEFactor zetaCellS0‖ =
      ‖(2 : ℂ)‖ * ‖(2 * (Real.pi : ℂ)) ^ (-zetaCellS0)‖ *
        ‖Complex.Gamma zetaCellS0‖ *
        ‖Complex.cos ((Real.pi : ℂ) * zetaCellS0 / 2)‖ := by
    unfold zetaFEFactor
    simp [norm_mul, mul_assoc]
  rw [hnorm_eq, e2]
  have hprod_ge : 2 * (1 / 7 : ℝ) * (1 / 10000000000000 : ℝ) * 1 ≤
      2 * ‖(2 * (Real.pi : ℂ)) ^ (-zetaCellS0)‖ * ‖Complex.Gamma zetaCellS0‖ *
        ‖Complex.cos ((Real.pi : ℂ) * zetaCellS0 / 2)‖ := by
    apply mul_le_mul
    · apply mul_le_mul
      · exact mul_le_mul (le_refl 2) hcp (by positivity) (by positivity)
      · exact hG
      · positivity
      · positivity
    · exact hcos
    · positivity
    · positivity
  have hbound : (1 : ℝ) / 100000000000000 ≤ 2 * (1 / 7 : ℝ) * (1 / 10000000000000 : ℝ) * 1 := by
    norm_num
  exact le_trans hbound hprod_ge

#print axioms zetaFE_cpow_lower_S0
#print axioms zetaFE_cos_lower_S0
#print axioms zetaFE_sin_pi_upper_S0
#print axioms zetaFE_exp28_lt
#print axioms zetaFE_sin_pi_upper_num_S0
#print axioms zetaFE_realGamma_0605_le
#print axioms zetaFE_Gamma_one_sub_upper_S0
#print axioms zetaFE_Gamma_lower_S0
#print axioms zetaFE_factor_lower_S0

/-!
## `zetaUpper` Re>1 absolute upper (EASIEST stone for R02 `≤10` route).

GOAL (READ-ONLY, `central_cover_assembly.lean:6333-6335`):
`def R02_zeta_upper_obligation : Prop := ∀ s, 0.05 ≤ s.re → s.re ≤ 0.74 →
-8.25 ≤ s.im → s.im ≤ -5.25 → ‖zeta s‖ ≤ 10`
where `zeta = riemannZeta` definitionally (`riemann_hypothesis.lean:16`
`def zeta : ℂ → ℂ := riemannZeta`; cf. `riemann_hypothesis_newsection.lean:784`
`have hzeta_eq : zeta s = riemannZeta s := rfl`). Discharging it gives
`R02_deriv_bound_of_zeta_upper` (`central_cover_assembly.lean:6390-6398`)
`‖deriv xiShifted‖ ≤ 67200` (`16800 / 0.25`, from `42*1*40*10`; cf. `:6006`,
`:6010-6014` supplier shape). This file states everything with `riemannZeta`
(`import Mathlib` only, no new imports, avoids cycles with
`central_cover_assembly`/`interval_arith`); `zeta` conversion is `rfl`.

WHY NOT eta M-test (do NOT retry): `riemann_hypothesis_newsection.lean:618-624`
proves `≤1012` sharp at `M=1` (`r(M)=C*M^{-σ}/σ≈180*M^{-0.05}` with `σ=0.05`,
`C=9`) and `r≤5` needs `M≥36^{20}≈1.3e31` terms — infeasible. Unconditional
`‖zeta‖≤1012` (`:739-743` `R02_zeta_upper_of_etaPairLim_eq`,
`:899-901` `R02_zeta_upper_unconditional`) gives `M=6800640` (`:903-905`
`R02_deriv_bound_unconditional`); `≤10` needs FE+convexity, not longer sums.

GREP VERDICT (searches run before writing; repo + Mathlib; cite file:line):
* Phragmen-Lindelof EXISTS (strip form, exact needed shape):
  `Mathlib/Analysis/Complex/PhragmenLindelof.lean:275`
  `theorem vertical_strip (hfd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b)) ... → ‖f z‖ ≤ C`
  (sub-double-exponential growth `∃ c < π/(b-a)` + boundary `≤C` → interior `≤C`).
  Variants `:303` `eq_zero_on_vertical_strip`, `:321` `eqOn_vertical_strip`.
* Hadamard three-lines EXISTS (strip form, exact needed shape — do NOT recreate):
  `Mathlib/Analysis/Complex/Hadamard.lean:608`
  `lemma norm_le_interp_of_mem_verticalClosedStrip' (hul : l < u)
  (hz : z ∈ verticalClosedStrip l u) (hd : DiffContOnCl ℂ f (verticalStrip l u))
  (hB : BddAbove ...) (ha : ∀ z ∈ re ⁻¹' {l}, ‖f z‖ ≤ a)
  (hb : ∀ z ∈ re ⁻¹' {u}, ‖f z‖ ≤ b) :
  ‖f z‖ ≤ a ^ (1 - (z.re - l)/(u - l)) * b ^ ((z.re - l)/(u - l))`.
  Also `:589` `norm_le_interpStrip_of_mem_verticalClosedStrip`,
  `:478` `norm_le_interp_of_mem_verticalClosedStrip₀₁'`,
  `:464` `norm_le_interpStrip_of_mem_verticalClosedStrip₀₁`.
  NOTE: direct `f = riemannZeta` on `[0.05,1+δ]` is BLOCKED by the pole at `s=1`
  (`DiffContOnCl` fails there); next lemma must apply it to `(s-1)*ζ(s)` or a
  pole-removed entire function (see residual below).
* Maximum modulus EXISTS (generic, not zeta-specific):
  `Mathlib/Analysis/Complex/AbsMax.lean:184`
  `theorem norm_eqOn_closedBall_of_isMaxOn`, `:201`
  `norm_eq_norm_of_isMaxOn_of_ball_subset`, `:212`
  `norm_eventually_eq_of_isLocalMax`. No zeta instantiation exists.
* Euler product for `riemannZeta` EXISTS on `1 < s.re` (no norm upper from it):
  `Mathlib/NumberTheory/EulerProduct/DirichletLSeries.lean:57`
  `lemma summable_riemannZetaSummand (hs : 1 < s.re)`,
  `:89` `theorem riemannZeta_eulerProduct_hasProd (hs : 1 < s.re)`,
  `:102` `theorem riemannZeta_eulerProduct (hs : 1 < s.re)`.
  No `‖ζ‖ ≤ ...` upper is derived from it anywhere
  (`rg "norm.*riemannZeta.*le|riemannZeta.*norm.*le|upper.*riemannZeta" → No files found`).
* Dirichlet-series absolute convergence EXISTS (the tool for the stone below):
  `Mathlib/Analysis/PSeriesComplex.lean:25`
  `lemma Complex.summable_one_div_nat_cpow : Summable (1/(n:ℂ)^p) ↔ 1 < re p`;
  `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:207`
  `theorem zeta_eq_tsum_one_div_nat_cpow (hs : 1 < re s)`,
  `:214` `theorem zeta_eq_tsum_one_div_nat_add_one_cpow (hs : 1 < re s)`;
  `Mathlib/Analysis/Normed/Group/InfiniteSum.lean:149`
  `theorem norm_tsum_le_tsum_norm (hf : Summable fun i => ‖f i‖)`,
  `:120` `HasSum.norm_le_of_bounded`;
  `Mathlib/Analysis/Normed/Module/FiniteDimension.lean:612`
  `theorem summable_norm_iff : (Summable fun x => ‖f x‖) ↔ Summable f`
  (used in-file as `summable_norm_iff.mpr`, cf. `eta_not_summable`);
  `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:337`
  `theorem norm_cpow_eq_rpow_re_of_pos (hx : 0 < x) (y : ℂ)`.
  In-file reuse (read-only, no modification): `summable_one_div_nat_add_one_cpow`
  and `zeta_eq_tsum_one_div_nat_add_one_cpow` bridging via `push_cast; ring`
  (cf. `zeta_odd_tsum_eq`, `zeta_even_add_odd_tsum`).
* Functional equation EXISTS (cos form, already mirrored as `zetaFEFactor`):
  `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:178-180`
  `theorem riemannZeta_one_sub : riemannZeta (1 - s) = 2*(2*π)^(-s)*Gamma s*cos(π*s/2)*riemannZeta s`
  (via `HurwitzZetaEven.lean:760` `hurwitzZetaEven_one_sub`).
* Lindelof/convexity bound for `zeta` MISSING:
  `rg "Lindelof|lindelof" Mathlib → only Picard-Lindelof ODE
  (Mathlib/Analysis/ODE/PicardLindelof.lean:39 `IsPicardLindelof`, unrelated) and
  topological Lindelof (`Weierstrass.lean:447`, unrelated);
  `rg "convexity.*zeta|zeta.*convex|threeLines.*zeta|Lindelof.*zeta" → No files found`.
* Direct `‖ζ‖ ≤ ζ(Re)` upper on `Re>1` MISSING (this stone closes it in tsum form):
  `rg "norm.*riemannZeta.*le|upper.*riemannZeta" → No files found`.
* `zeta` vs `riemannZeta`: `riemann_hypothesis.lean:16` (definitionally equal).
* Import graph: this file `import Mathlib` only (no new imports below; avoids cycles).

WHAT IS PROVED (all unconditional, no `sorry`/`admit`/`axiom`/hypotheses):
* `zetaUpper_norm_term_eq`: `‖1/((n+1)^s)‖ = (((n+1):ℝ)^s.re)⁻¹`.
* `zetaUpper_norm_summable`: `Summable (‖1/((n+1)^s)‖)` on `1 < s.re`
  (via `summable_norm_iff.mpr (summable_one_div_nat_add_one_cpow hs)`).
* `zetaUpper_riemannZeta_norm_le_tsum`: `‖riemannZeta s‖ ≤ ∑' n, (((n+1):ℝ)^s.re)⁻¹`
  on `1 < s.re` (via `zeta_eq_tsum_one_div_nat_add_one_cpow` + `push_cast; ring`
  bridge + `norm_tsum_le_tsum_norm`). This is `|ζ(s)| ≤ ζ(Re s)` in Real-tsum
  form (RHS is the Real Dirichlet series for `ζ(σ)`); the `tsum eta FALSE`
  rule is respected (Tendsto/majorant-free here — the `Re>1` zeta series IS
  absolutely convergent, so `norm_tsum_le_tsum_norm` + `summable_norm_iff`
  apply; no conditional `tsum` abuse).

RESIDUAL (§1h: full `≤10` assembly exceeds one session — STOP after this stone):
exact next lemma `zetaUpper_R02_of_threeLines` (NOT proved here): from (i) this
stone + a numeric Real-tsum cap at `σ=1+δ` (e.g. `∑' (n+1)^{-1.1} ≤ B_right`),
(ii) a left-edge bound on `Re=0.05` via FE
(`riemannZeta_one_sub` + `zetaFEFactor`-style `‖F‖` upper/lower + `‖ζ(1-s)‖`
upper from (i) since `1-s` has `Re∈[0.26,0.95]` — still `<1`, so one FE step
alone does NOT reach `Re>1`; needs (iii)), and (iii) Hadamard
`norm_le_interp_of_mem_verticalClosedStrip'` applied to the POLE-REMOVED entire
`f(s)=(s-1)*riemannZeta s` (with `BddAbove` + `DiffContOnCl` discharged around
`s=1`, plus Stirling Gamma upper to reach fencing-tier constants) infer
`‖riemannZeta s‖ ≤ 10` on `0.05 ≤ Re ≤ 0.74, -8.25 ≤ Im ≤ -5.25`
(i.e. `DerivCauchyBridge.R02_zeta_upper_obligation` up to `zeta=rfl`).
-/

/-- Norm of the `Re>1` zeta summand: `‖1/((n+1)^s)‖ = (((n+1):ℝ)^s.re)⁻¹`. -/
theorem zetaUpper_norm_term_eq (s : ℂ) (n : ℕ) :
    ‖(1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s)‖ = ((((n + 1 : ℕ) : ℝ) ^ s.re))⁻¹ := by
  have hpos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := Nat.cast_pos.mpr (by omega)
  have hbase : ((((n + 1 : ℕ) : ℂ))) = (((((n + 1 : ℕ) : ℝ)) : ℂ)) :=
    (Complex.ofReal_natCast _).symm
  rw [hbase, norm_div, norm_one, Complex.norm_cpow_eq_rpow_re_of_pos hpos s, one_div]

/-- Absolute summability of the `Re>1` zeta series (norm form). -/
theorem zetaUpper_norm_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ‖(1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s)‖) :=
  summable_norm_iff.mpr (summable_one_div_nat_add_one_cpow hs)

/-- EASIEST STONE: `‖ζ(s)‖ ≤ ∑' (n+1)^{-Re s}` on `1 < s.re` (absolute convergence;
`‖ζ(s)‖ ≤ ζ(s.re)` in Real-tsum form; right-edge input to three-lines). -/
theorem zetaUpper_riemannZeta_norm_le_tsum {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, ((((n + 1 : ℕ) : ℝ) ^ s.re))⁻¹ := by
  have hSum := summable_one_div_nat_add_one_cpow hs
  have hNormSum : Summable (fun n : ℕ => ‖(1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s)‖) :=
    summable_norm_iff.mpr hSum
  have hZeq : riemannZeta s = ∑' n : ℕ, (1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s) := by
    have h0 := zeta_eq_tsum_one_div_nat_add_one_cpow hs
    rw [h0]
    apply tsum_congr
    intro n
    congr 1
    congr 1
    push_cast
    ring
  rw [hZeq]
  have hle := norm_tsum_le_tsum_norm hNormSum
  calc ‖∑' n : ℕ, (1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s)‖ ≤
        ∑' n : ℕ, ‖(1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s)‖ := hle
    _ = ∑' n : ℕ, ((((n + 1 : ℕ) : ℝ) ^ s.re))⁻¹ := by
        apply tsum_congr
        intro n
        exact zetaUpper_norm_term_eq s n

#print axioms zetaUpper_norm_term_eq
#print axioms zetaUpper_norm_summable
#print axioms zetaUpper_riemannZeta_norm_le_tsum

/-!
## Reflected-eta pilot at R00 (s1 = 1 - s0, Re = 0.605).

Grep-first record (searches run 2026-09-03, repo + Mathlib, documented per brief):
* `zetaCellS0`, `zetaCellS0_re/im/pos/norm_le`, `two_cpow_norm`, `zetaCell_even_remainder_le`,
  `zeta_of_etaPairLim_of_re_ne`, `etaFactor_ne_zero_of_re_ne`, `zetaFEFactor`,
  `zetaFE_factor_upper_S0/lower_S0`, `etaDirichlet_S0_two_norm_ge`, `zetaCellS0_rpow_0395_ge/0605_le`
  -- all in this file (read-only reuse, no modification); no `zetaRefl*`, `S1refl*`, `Azeta1` exist
  (`Select-String zetaRefl|S1refl|Azeta1` -- 0 hits before writing).
* Mathlib FE cos-form `riemannZeta_one_sub` (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:178-180`):
  `riemannZeta (1 - s) = 2*(2*pi)^(-s)*Gamma s*cos(pi*s/2)*riemannZeta s`
  with `hs : forall n : Nat, s != -n` and `s != 1`; `zetaFEFactor` in this file is exactly this `F`.
  Direction is `zeta(1-s) = F(s)*zeta(s)`, so `zeta(s0) = zeta(1-s0)/F(s0)` needs `F` UPPER (6e7),
  not LOWER -- prompt orientation corrected below (any Azeta>0 still closes pilot).
* `Complex.sub_re/sub_im/one_re/one_im` (`Mathlib/Data/Complex/Basic.lean:147/151/639/643`);
  `Complex.neg_im/natCast_im` (`:188/:356`); `le_of_pow_le_pow_left0`, `inv_le_inv0`,
  `Real.rpow_le_rpow_of_exponent_le`, `Real.one_rpow`, `norm_inv`, `norm_add_le`
  -- all already used in this file (same patterns mirrored).
* Import graph: this file `import Mathlib` only (no new imports below, avoids cycles).

What is proved (all unconditional, no sorry/admit/axiom):
* (1) SHORT-SUM LOWER at s1 = 1 - s0, M = 1 (N = 2): `zetaRefl_re/im/pos/norm_le`,
  `zetaRefl_rpow_0605_ge` (3/2 <= 2^0.605 via (3/2)^5 <= 2^3 + 3/5 <= 0.605),
  `etaDirichlet_S1refl_*` closed form + `norm_..._second_le` (<= 2/3) +
  `etaDirichlet_S1refl_two_norm_ge` (1/3 <= ||S2(s1)||, reverse-triangle, mirrors S0 1/5).
  True ||S2|| ~ 0.387 (1 - 0.657*exp phase), so 1/3 is honest with small margin.
* TAIL at s1: `zetaRefl_tail_general` (C = 10, sigma = 0.605 via `zetaCell_even_remainder_le`),
  `zetaRefl_tail_1_le` (||G - S2|| <= 17, since 10/0.605 ~ 16.53).
  Hence slow - rtail = 1/3 - 17 < 0 -- no positive Azeta1 at M = 1 (wall quantified in-file).
* (2)/(3) INFRASTRUCTURE (unconditional, for future larger-M or smarter-bound work):
  `etaFactor_ne_zero_S1refl` + `zeta_of_etaPairLim_S1refl` (division at s1 via existing
  `zeta_of_etaPairLim_of_re_ne`, since s1.re = 0.605 != 1 -- generalizes cellCenter bridge which only
  covers {0.395,0.3,0.2,0.105}), `zetaCellS0_ne_neg_nat/ne_one` + `zetaFE_refl_eq_S0`
  (`zeta(1-s0) = F(s0)*zeta(s0)` via `riemannZeta_one_sub`).

Honest residual (numbers):
* M = 1, c_S = 1/3, r(1) = 10/0.605 ~ 16.53 <= 17, net negative -- Azeta1/Azeta NOT closed.
* Threshold for net positive with current tail: r(M) = 10*M^-0.605/0.605 < 1/3 needs M >= 635
  (N >= 1270 cpow terms); for c_S = 1/4 needs M >= 1021 (N >= 2042). Both infeasible for explicit
  Finset.range norm_num (each term is a complex cpow). Smarter bound (not longer sums) needed.
-/

/-- Reflected point real part: `(1 - s0).re = 0.605`. -/
theorem zetaRefl_re : (1 - zetaCellS0).re = (0.605 : ℝ) := by
  rw [Complex.sub_re, Complex.one_re, zetaCellS0_re]
  norm_num

/-- Reflected point imaginary part: `(1 - s0).im = 8.75`. -/
theorem zetaRefl_im : (1 - zetaCellS0).im = (8.75 : ℝ) := by
  rw [Complex.sub_im, Complex.one_im, zetaCellS0_im]
  norm_num

/-- Reflected point has positive real part. -/
theorem zetaRefl_pos : 0 < (1 - zetaCellS0).re := by
  rw [zetaRefl_re]
  norm_num

/-- Reflected point norm bound `||1 - s0|| <= 10` (mirrors `zetaCellS0_norm_le`). -/
theorem zetaRefl_norm_le : ‖1 - zetaCellS0‖ ≤ 10 := by
  have hre : (1 - zetaCellS0).re = (0.605 : ℝ) := zetaRefl_re
  have him : (1 - zetaCellS0).im = (8.75 : ℝ) := zetaRefl_im
  have hsq : ‖1 - zetaCellS0‖ ^ 2 ≤ (10 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hsq

/-- Numeral rpow lower `3/2 <= 2^0.605` (cleared: `(3/2)^5 <= 2^3`, since `3/5 <= 0.605`). -/
theorem zetaRefl_rpow_0605_ge : (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (0.605 : ℝ) := by
  have hpow : ((3 / 2 : ℝ)) ^ ((5 : ℕ))
      ≤ ((((2 : ℝ) ^ ((3 / 5 : ℝ)))) ^ ((5 : ℕ)) : ℝ) := by
    have e : ((((2 : ℝ) ^ ((3 / 5 : ℝ)))) ^ ((5 : ℕ)) : ℝ)
        = (2 : ℝ) ^ ((3 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [show (3 / 5 : ℝ) * (((5 : ℕ)) : ℝ) = (3 : ℝ) by norm_num]
      rw [show (3 : ℝ) = (((3 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 2 3
    rw [e]
    norm_num
  have hstep : (3 / 2 : ℝ) ≤ (2 : ℝ) ^ ((3 / 5 : ℝ)) :=
    le_of_pow_le_pow_left₀ (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _).le hpow
  calc (3 / 2 : ℝ) ≤ (2 : ℝ) ^ ((3 / 5 : ℝ)) := hstep
    _ ≤ (2 : ℝ) ^ (0.605 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

/-- `etaDirichletTerm` at `1 - s0`, `k = 0` equals `1`. -/
theorem etaDirichletTerm_S1refl_zero :
    etaDirichletTerm (1 - zetaCellS0) 0 = 1 := by
  have h01 : (0 + 1 : ℕ) = 1 := rfl
  have hcast : ((((0 + 1 : ℕ)) : ℂ)) = 1 := by rw [h01, Nat.cast_one]
  simp only [etaDirichletTerm, pow_zero, hcast, Complex.one_cpow, div_one]

/-- `etaDirichletTerm` at `1 - s0`, `k = 1` equals `-(2^s1)⁻¹`. -/
theorem etaDirichletTerm_S1refl_one :
    etaDirichletTerm (1 - zetaCellS0) 1 = -((((2 : ℕ) : ℂ) ^ (1 - zetaCellS0))⁻¹) := by
  unfold etaDirichletTerm
  rw [pow_one]
  rw [show (((1 + 1 : ℕ) : ℂ)) = ((((2 : ℕ)) : ℂ)) by norm_num]
  rw [neg_div, one_div]

/-- Two-term partial sum `S2` at `1 - s0` in closed form. -/
theorem etaDirichlet_S1refl_two_eq :
    (∑ k ∈ Finset.range 2, etaDirichletTerm (1 - zetaCellS0) k)
      = 1 - ((((2 : ℕ) : ℂ) ^ (1 - zetaCellS0))⁻¹) := by
  have hsum : (∑ k ∈ Finset.range 2, etaDirichletTerm (1 - zetaCellS0) k)
      = etaDirichletTerm (1 - zetaCellS0) 0 + etaDirichletTerm (1 - zetaCellS0) 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
  rw [hsum, etaDirichletTerm_S1refl_zero, etaDirichletTerm_S1refl_one]
  ring

/-- Modulus of the second term at `1 - s0`: `‖(2^s1)⁻¹‖ = 2^-0.605 <= 2/3`. -/
theorem norm_etaDirichlet_S1refl_second_le :
    ‖((((2 : ℕ) : ℂ) ^ (1 - zetaCellS0))⁻¹)‖ ≤ 2 / 3 := by
  have h2eq : ((((2 : ℕ)) : ℂ)) = (2 : ℂ) := by norm_cast
  rw [h2eq, norm_inv, two_cpow_norm, zetaRefl_re]
  have hge := zetaRefl_rpow_0605_ge
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  rw [show (2 / 3 : ℝ) = ((3 / 2 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

/-- Two-term lower bound `1/3 <= ||S2(1-s0)||` (reverse triangle; mirrors `etaDirichlet_S0_two_norm_ge`). -/
theorem etaDirichlet_S1refl_two_norm_ge :
    (1 / 3 : ℝ) ≤ ‖∑ k ∈ Finset.range 2, etaDirichletTerm (1 - zetaCellS0) k‖ := by
  rw [etaDirichlet_S1refl_two_eq]
  have hX := norm_etaDirichlet_S1refl_second_le
  have h := norm_add_le
    (1 - ((((2 : ℕ) : ℂ) ^ (1 - zetaCellS0))⁻¹))
    ((((2 : ℕ) : ℂ) ^ (1 - zetaCellS0))⁻¹)
  rw [sub_add_cancel] at h
  rw [norm_one] at h
  linarith

/-- Tail general at `1 - s0`: `||G - S_{2M}|| <= 10*(M^-0.605/0.605)` (via `zetaCell_even_remainder_le`). -/
theorem zetaRefl_tail_general (M : ℕ) (hM : 1 ≤ M) :
    ‖(∑' m, etaPairTerm (1 - zetaCellS0) m) -
      (∑ k ∈ Finset.range (2 * M), etaDirichletTerm (1 - zetaCellS0) k)‖ ≤
      10 * (((((M : ℕ)) : ℝ) ^ (-0.605 : ℝ)) / (0.605 : ℝ)) := by
  have hs : 0 < (1 - zetaCellS0).re := zetaRefl_pos
  have hC : ‖1 - zetaCellS0‖ ≤ 10 := zetaRefl_norm_le
  have h := zetaCell_even_remainder_le hs hC (by norm_num) M hM
  have hre : (1 - zetaCellS0).re = (0.605 : ℝ) := zetaRefl_re
  rw [hre] at h
  exact h

/-- Honest small-`N` tail at `1 - s0`: `||G - S2|| <= 17` (`M = 1`, `10/0.605 ~ 16.53`). -/
theorem zetaRefl_tail_1_le :
    ‖(∑' m, etaPairTerm (1 - zetaCellS0) m)
      - (∑ k ∈ Finset.range 2, etaDirichletTerm (1 - zetaCellS0) k)‖ ≤ 17 := by
  have hgen := zetaRefl_tail_general 1 (by norm_num)
  have h21 : 2 * 1 = 2 := by norm_num
  rw [h21] at hgen
  have h1 : ((((1 : ℕ)) : ℝ)) = (1 : ℝ) := by norm_cast
  rw [h1, Real.one_rpow] at hgen
  have hle : (10 : ℝ) * (1 / (0.605 : ℝ)) ≤ 17 := by norm_num
  linarith

/-- Factor nonvanishing at `1 - s0` (via `Re = 0.605 != 1`; generalizes `etaFactor_ne_zero_cellCenter`). -/
theorem etaFactor_ne_zero_S1refl :
    (1 - (2 : ℂ) ^ ((1 : ℂ) - (1 - zetaCellS0))) ≠ 0 := by
  apply etaFactor_ne_zero_of_re_ne
  rw [zetaRefl_re]
  norm_num

/-- Division at `1 - s0` through YOUR bridge (covers `Re = 0.605`, outside cellCenter set). -/
theorem zeta_of_etaPairLim_S1refl :
    riemannZeta (1 - zetaCellS0) =
      (∑' m, etaPairTerm (1 - zetaCellS0) m) / (1 - (2 : ℂ) ^ ((1 : ℂ) - (1 - zetaCellS0))) := by
  have hs : 0 < (1 - zetaCellS0).re := zetaRefl_pos
  have hre : (1 - zetaCellS0).re ≠ 1 := by
    rw [zetaRefl_re]
    norm_num
  exact zeta_of_etaPairLim_of_re_ne hs hre

/-- `zetaCellS0` avoids all `(-n : ℂ)` (Im = -8.75 != 0), for Mathlib FE side condition. -/
theorem zetaCellS0_ne_neg_nat : ∀ n : ℕ, zetaCellS0 ≠ -((n : ℂ)) := by
  intro n h
  have him := congrArg Complex.im h
  have hrhs : (-((n : ℂ))).im = 0 := by
    rw [Complex.neg_im, Complex.natCast_im, neg_zero]
  rw [zetaCellS0_im, hrhs] at him
  norm_num at him

/-- `zetaCellS0 != 1` (Re = 0.395 != 1), for Mathlib FE side condition. -/
theorem zetaCellS0_ne_one : zetaCellS0 ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  rw [zetaCellS0_re, Complex.one_re] at hre
  norm_num at hre

/-- FE link at R00: `zeta(1-s0) = F(s0)*zeta(s0)` via `riemannZeta_one_sub` (correct direction). -/
theorem zetaFE_refl_eq_S0 :
    riemannZeta (1 - zetaCellS0) = zetaFEFactor zetaCellS0 * riemannZeta zetaCellS0 := by
  have hs_ne : ∀ n : ℕ, zetaCellS0 ≠ -((n : ℂ)) := zetaCellS0_ne_neg_nat
  have hs1 : zetaCellS0 ≠ 1 := zetaCellS0_ne_one
  have h := riemannZeta_one_sub hs_ne hs1
  have h2 : (2 * (2 * (Real.pi : ℂ)) ^ (-zetaCellS0) * Complex.Gamma zetaCellS0 *
        Complex.cos ((Real.pi : ℂ) * zetaCellS0 / 2) * riemannZeta zetaCellS0) =
      zetaFEFactor zetaCellS0 * riemannZeta zetaCellS0 := by
    unfold zetaFEFactor
    ring
  rw [← h2]
  exact h

#print axioms zetaRefl_re
#print axioms zetaRefl_im
#print axioms zetaRefl_pos
#print axioms zetaRefl_norm_le
#print axioms zetaRefl_rpow_0605_ge
#print axioms etaDirichletTerm_S1refl_zero
#print axioms etaDirichletTerm_S1refl_one
#print axioms etaDirichlet_S1refl_two_eq
#print axioms norm_etaDirichlet_S1refl_second_le
#print axioms etaDirichlet_S1refl_two_norm_ge
#print axioms zetaRefl_tail_general
#print axioms zetaRefl_tail_1_le
#print axioms etaFactor_ne_zero_S1refl
#print axioms zeta_of_etaPairLim_S1refl
#print axioms zetaCellS0_ne_neg_nat
#print axioms zetaCellS0_ne_one
#print axioms zetaFE_refl_eq_S0

/-!
## Reflected `Azeta1` conditional closure + exact wall (`s1 = 1 - s0`, `Re = 0.605`).

GOAL (brief 2026-09-03): honest lower bound `‖ζ(1-s0)‖ ≥ Azeta1`, `Azeta1 > 0`
explicit, WITHOUT explicit 1k+ partial sums.

GREP-FIRST RECORD (searches run before writing; repo + Mathlib):
* `zetaCellS0`, `zetaRefl_*`, `zeta_lower_of_Sn_tail_factor`, `zetaFE_refl_eq_S0`,
  `zetaFE_factor_upper_S0`, `two_cpow_norm`, `zetaCellS0_rpow_0605_le`,
  `Real.rpow_le_rpow_of_exponent_le`, `inv_le_inv₀`, `div_le_div_of_nonneg_right`,
  `Real.rpow_neg`, `div_le_iff₀`, `lt_div_iff₀` -- all in this file (read-only
  reuse, patterns mirrored verbatim); no `Azeta1`/`S1refl_factor_upper` existed
  (`Azeta1` -- 0 hits before writing).
* Cancellation-tail material in Mathlib: ABSENT (`Kuzmin|kuzmin|van der
  Corput|corput|exponent pair` -- 0 hits in `Mathlib/`). A partial-summation /
  exponential-sum tail improvement would need this built from scratch (~300+
  lines: dyadic blocks + Kuzmin-Landau + Abel summation for
  `∑ (2m+1)^{-s} - (2m+2)^{-s}` with phase `t = 8.75`); not attempted here.
* Lower bounds on `‖riemannZeta‖`: ABSENT (`norm (riemannZeta|...lower...` --
  0 hits in `Mathlib/NumberTheory/LSeries/`). No Mathlib lower bound to call.
* Base-monotone rpow EXISTS: `Real.rpow_le_rpow (h : 0 ≤ x) (h₁ : x ≤ y)
  (h₂ : 0 ≤ z)` (`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:548`);
  exponent-mono `Real.rpow_le_rpow_of_exponent_le` (`:615`); `mul_inv_lt_iff₀`
  (`Mathlib/Algebra/Order/GroupWithZero/Basic.lean:1130`).
* `zeta_of_etaPairLim_cellCenter` covers only `Re ∈ {0.395,0.3,0.2,0.105}`,
  so `s1` (`Re = 0.605`) goes through the existing `zeta_of_etaPairLim_S1refl`
  instance + the general feeder `zeta_lower_of_Sn_tail_factor` (same bridge).
* Import graph: no new imports (still `Mathlib`-only).

VERDICT: unconditional `Azeta1` is INFEASIBLE in one session (see numbers).
Proved instead (all unconditional, no sorry/admit/axiom):
* (a) factor upper at `s1`: `etaFactor_upper_S1refl` (`‖1-2^{s0}‖ ≤ 13/5`,
  via new `zetaCellS0_rpow_0395_le`: `2^0.395 ≤ 2^0.605 ≤ 8/5`).
* (b) exact wall biconditional: `zetaRefl_wall_threshold_iff`
  (`r(M) < 1/3 ↔ 6000/121 < M^0.605`, since `30/0.605 = 6000/121`).
* (c) SUFFICIENCY at `M = 1024` (`N = 2048`): `zetaRefl_M1024_rpow_ge`
  (`1024^0.605 ≥ 1024^{3/5} = 2^6 = 64`, powers of two),
  `zetaRefl_r_1024_le` (`r ≤ 4/15`), `zetaRefl_tail_1024_le` (`‖G-S‖ ≤ 4/15`).
* (d) NECESSITY for `M ≤ 343`: `zetaRefl_M343_rpow_le`
  (`343^0.605 ≤ 343^{2/3} = 7^2 = 49 ≤ 6000/121`, exact cubes),
  `zetaRefl_wall_necessity` (`1 ≤ M ≤ 343 → r(M) ≥ 1/3`: no such `M` closes
  with `slow = 1/3`; ≥ 344 pairs = 688 terms needed). Plus small-`M` anchor
  `zetaRefl_r_1_ge` (`r(1) ≥ 16`: bound value `10/0.605 ≈ 16.53`, upper `≤ 17`
  is `zetaRefl_tail_1_le`).
* (e) CONDITIONAL closure: `zeta_S1_lower_of_S2048`
  (`‖S_{2048}(s1)‖ ≥ 1/3 → 1/39 ≤ ‖ζ(s1)‖`, since
  `(1/3 - 4/15)/(13/5) = 1/39`) and downstream `zeta_S0_lower_of_S1`
  (`1/39 ≤ ‖ζ(s1)‖ → 1/2340000000 ≤ ‖ζ(s0)‖`, via `zetaFE_refl_eq_S0` +
  `‖F‖ ≤ 6e7`; i.e. `Azeta = Azeta1/6e7`).

NUMBERS (python-verified, non-rigorous scratch for the report only):
* threshold `M^0.605 > 30/0.605 = 49.586776…`; `634^0.605 ≈ 49.5751` (fails,
  margin 0.02%), `635^0.605 ≈ 49.6224` (works, margin 0.07%): true minimal
  `M = 635` (`N = 1270`). Proved bracket here: `[344, 1024]`.
* `343^0.605 ≈ 34.19` (proved upper `49` loose but sufficient);
  `1024^0.605 ≈ 66.26` (proved lower `64`); `r(1024) ≈ 0.2494 ≤ 4/15`.
* true `|G(s1)| ≈ 0.5627` (200k-term eta sum, tail ~1e-3), `|1-2^s0| ≈ 0.4019`,
  `|ζ(s1)| ≈ 1.4000`: the premise `‖S_{2048}‖ ≥ 1/3` is TRUE with ~70% margin
  (`S_{2048} ≈ G ± 1e-4`), the proved tail `4/15 ≈ 0.267` is ~2500× loose vs
  the true tail (~1e-4) -- the whole gap is inter-pair phase cancellation the
  triangle inequality cannot see. Any unconditional closure must capture it
  (Kuzmin-Landau-type material, absent from Mathlib) or do rigorous complex
  interval arithmetic (`cos`/`sin` of `8.75·log n` for `n ≤ 2048`).
-/

/-- `2^0.395 ≤ 8/5` (monotonicity + existing `0605` cap). -/
theorem zetaCellS0_rpow_0395_le : (2 : ℝ) ^ (0.395 : ℝ) ≤ (8 / 5 : ℝ) :=
  le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
    zetaCellS0_rpow_0605_le

/-- Eta-factor upper at `s1 = 1 - s0`: `‖1 - 2^{1-s1}‖ ≤ 13/5`
(`1 - s1 = s0`, `‖2^s0‖ = 2^0.395 ≤ 8/5`; mirrors `etaFactor_upper_S0`). -/
theorem etaFactor_upper_S1refl :
    ‖(1 - (2 : ℂ) ^ ((1 : ℂ) - (1 - zetaCellS0)))‖ ≤ 13 / 5 := by
  have hsub : ((1 : ℂ) - (1 - zetaCellS0)) = zetaCellS0 := by ring
  rw [hsub]
  have hY : ‖(2 : ℂ) ^ zetaCellS0‖ ≤ 8 / 5 := by
    rw [two_cpow_norm, zetaCellS0_re]
    exact zetaCellS0_rpow_0395_le
  calc ‖(1 : ℂ) - (2 : ℂ) ^ zetaCellS0‖
      ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ zetaCellS0‖ := norm_sub_le _ _
    _ ≤ 13 / 5 := by rw [norm_one]; linarith [hY]

/-- EXACT WALL (biconditional): `r(M) = 10·M^{-0.605}/0.605 < 1/3`
iff `6000/121 < M^0.605` (`30/0.605 = 6000/121`). -/
theorem zetaRefl_wall_threshold_iff {x : ℝ} (hx : 0 < x) :
    (10 * ((x ^ (0.605 : ℝ))⁻¹) / (0.605 : ℝ) < (1 / 3 : ℝ)) ↔
      ((6000 / 121 : ℝ) < x ^ (0.605 : ℝ)) := by
  have hxp : (0 : ℝ) < x ^ (0.605 : ℝ) := Real.rpow_pos_of_pos hx _
  have hK : (0 : ℝ) < (1 / 3 : ℝ) * 0.605 := by norm_num
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 0.605), mul_inv_lt_iff₀ hxp]
  have heq : (10 : ℝ) / ((1 / 3) * 0.605) = 6000 / 121 := by norm_num
  rw [← heq, div_lt_iff₀ hK, mul_comm]

/-- `((1024 : ℕ) : ℝ) = 2^10`. -/
theorem zetaRefl_M1024_eq : ((((1024 : ℕ)) : ℝ)) = (2 : ℝ) ^ (10 : ℕ) := by
  norm_num

/-- `64 ≤ 1024^0.605` (`3/5 ≤ 0.605`, `(2^10)^{3/5} = 2^6`; mirrors
`zetaCellS0_M2097152_rpow_ge`). -/
theorem zetaRefl_M1024_rpow_ge :
    (64 : ℝ) ≤ ((((1024 : ℕ)) : ℝ) ^ (0.605 : ℝ)) := by
  rw [zetaRefl_M1024_eq]
  have h1 : (((2 : ℝ) ^ (10 : ℕ)) ^ (0.605 : ℝ)) =
      (2 : ℝ) ^ (((((10 : ℕ)) : ℝ)) * (0.605 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [h1]
  have hexp_ge : (6 : ℝ) ≤ ((((10 : ℕ)) : ℝ)) * (0.605 : ℝ) := by norm_num
  have h2 : (2 : ℝ) ^ (6 : ℝ) ≤ (2 : ℝ) ^ (((((10 : ℕ)) : ℝ)) * (0.605 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_ge
  have e6 : (6 : ℝ) = ((((6 : ℕ)) : ℝ)) := by norm_num
  have h3 : (2 : ℝ) ^ (6 : ℝ) = 64 := by
    rw [e6, Real.rpow_natCast]
    norm_num
  linarith

set_option maxHeartbeats 800000 in
/-- `r(1024) = 10·1024^{-0.605}/0.605 ≤ 4/15`
(`10/(64·0.605) = 0.258… ≤ 0.266…`; mirrors `zetaCellS0_r_2097152_le`). -/
theorem zetaRefl_r_1024_le :
    10 * ((((((1024 : ℕ)) : ℝ) ^ (-0.605 : ℝ))) / (0.605 : ℝ)) ≤ (4 / 15 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((1024 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((1024 : ℕ)) : ℝ) ^ (0.605 : ℝ)) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := zetaRefl_M1024_rpow_ge
  have hrw : ((((1024 : ℕ)) : ℝ) ^ (-0.605 : ℝ)) =
      (((((1024 : ℕ)) : ℝ) ^ (0.605 : ℝ)))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((1024 : ℕ)) : ℝ) ^ (0.605 : ℝ)))⁻¹ ≤ (64 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((1024 : ℕ)) : ℝ) ^ (0.605 : ℝ)))⁻¹ / (0.605 : ℝ) ≤
      (64 : ℝ)⁻¹ / (0.605 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : 10 * ((((((1024 : ℕ)) : ℝ) ^ (0.605 : ℝ)))⁻¹ / (0.605 : ℝ)) ≤
      10 * ((64 : ℝ)⁻¹ / (0.605 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : 10 * ((64 : ℝ)⁻¹ / (0.605 : ℝ)) ≤ (4 / 15 : ℝ) := by norm_num
  linarith

/-- Tail at `M = 1024` (`N = 2048`): `‖G - S_{2048}‖ ≤ 4/15`. -/
theorem zetaRefl_tail_1024_le :
    ‖(∑' m, etaPairTerm (1 - zetaCellS0) m)
      - (∑ k ∈ Finset.range (2 * 1024), etaDirichletTerm (1 - zetaCellS0) k)‖ ≤
      (4 / 15 : ℝ) := by
  have hgen := zetaRefl_tail_general 1024 (by norm_num)
  have hr := zetaRefl_r_1024_le
  linarith

/-- `((343 : ℕ) : ℝ) = 7^3`. -/
theorem zetaRefl_M343_eq : ((((343 : ℕ)) : ℝ)) = (7 : ℝ) ^ (3 : ℕ) := by
  norm_num

/-- `343^0.605 ≤ 49` (`0.605 ≤ 2/3`, `(7^3)^{2/3} = 7^2`; exact cubes). -/
theorem zetaRefl_M343_rpow_le :
    ((((343 : ℕ)) : ℝ) ^ (0.605 : ℝ)) ≤ 49 := by
  rw [zetaRefl_M343_eq]
  have h1 : (((7 : ℝ) ^ (3 : ℕ)) ^ (0.605 : ℝ)) =
      (7 : ℝ) ^ (((((3 : ℕ)) : ℝ)) * (0.605 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [h1]
  have hexp_le : ((((3 : ℕ)) : ℝ)) * (0.605 : ℝ) ≤ (2 : ℝ) := by norm_num
  have h2 : (7 : ℝ) ^ (((((3 : ℕ)) : ℝ)) * (0.605 : ℝ)) ≤ (7 : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
  have e2 : (2 : ℝ) = ((((2 : ℕ)) : ℝ)) := by norm_num
  have h3 : (7 : ℝ) ^ (2 : ℝ) = 49 := by
    rw [e2, Real.rpow_natCast]
    norm_num
  linarith

/-- NECESSITY: every `1 ≤ M ≤ 343` has `r(M) ≥ 1/3` (via `M^0.605 ≤ 343^0.605
≤ 49 ≤ 6000/121` + the threshold form `10/((6000/121)·0.605) = 1/3`).
Hence NO `M ≤ 343` closes with `slow = 1/3`: ≥ 344 pairs (688 terms) needed. -/
theorem zetaRefl_wall_necessity (M : ℕ) (hM : 1 ≤ M) (hMle : M ≤ 343) :
    (1 / 3 : ℝ) ≤ 10 * (((((M : ℕ)) : ℝ) ^ (-0.605 : ℝ)) / (0.605 : ℝ)) := by
  have hMpos : (0 : ℝ) < ((((M : ℕ)) : ℝ)) := by
    exact_mod_cast (by omega : 0 < M)
  have hbase_le : ((((M : ℕ)) : ℝ)) ≤ ((((343 : ℕ)) : ℝ)) :=
    Nat.cast_le.mpr hMle
  have hMle343 : ((((M : ℕ)) : ℝ) ^ (0.605 : ℝ)) ≤
      ((((343 : ℕ)) : ℝ) ^ (0.605 : ℝ)) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hbase_le (by norm_num)
  have h343 := zetaRefl_M343_rpow_le
  have hM_le : ((((M : ℕ)) : ℝ) ^ (0.605 : ℝ)) ≤ (6000 / 121 : ℝ) := by
    have h49 : (49 : ℝ) ≤ 6000 / 121 := by norm_num
    linarith
  have hMpos' : (0 : ℝ) < ((((M : ℕ)) : ℝ) ^ (0.605 : ℝ)) :=
    Real.rpow_pos_of_pos hMpos _
  have hrw : ((((M : ℕ)) : ℝ) ^ (-0.605 : ℝ)) =
      (((((M : ℕ)) : ℝ) ^ (0.605 : ℝ)))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_ge : ((6000 / 121 : ℝ))⁻¹ ≤ (((((M : ℕ)) : ℝ) ^ (0.605 : ℝ)))⁻¹ :=
    (inv_le_inv₀ (by norm_num) hMpos').mpr hM_le
  have hfin : (10 : ℝ) * (((6000 / 121 : ℝ))⁻¹ / 0.605) ≤
      10 * ((((((M : ℕ)) : ℝ) ^ (0.605 : ℝ)))⁻¹ / 0.605) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact div_le_div_of_nonneg_right hInv_ge (by norm_num)
  have hval : (10 : ℝ) * (((6000 / 121 : ℝ))⁻¹ / 0.605) = 1 / 3 := by norm_num
  linarith

/-- Small-`M` anchor: `r(1) = 10/0.605 ≥ 16` (bound value `≈ 16.53`;
upper `≤ 17` is `zetaRefl_tail_1_le`). -/
theorem zetaRefl_r_1_ge :
    (16 : ℝ) ≤ 10 * (((((1 : ℕ)) : ℝ) ^ (-0.605 : ℝ)) / (0.605 : ℝ)) := by
  have h1 : ((((1 : ℕ)) : ℝ)) = (1 : ℝ) := by norm_cast
  rw [h1, Real.one_rpow]
  norm_num

/-- CONDITIONAL `Azeta1`: `‖S_{2048}(s1)‖ ≥ 1/3 → 1/39 ≤ ‖ζ(s1)‖`
(`(1/3 - 4/15)/(13/5) = 1/39`, via YOUR bridge `zeta_lower_of_Sn_tail_factor`
+ `zetaRefl_tail_1024_le` + `etaFactor_upper_S1refl`). -/
theorem zeta_S1_lower_of_S2048 (Slarge : ℂ)
    (hSdef : Slarge =
      ∑ k ∈ Finset.range (2 * 1024), etaDirichletTerm (1 - zetaCellS0) k)
    (hSlow : (1 / 3 : ℝ) ≤ ‖Slarge‖) :
    (1 / 39 : ℝ) ≤ ‖riemannZeta (1 - zetaCellS0)‖ := by
  have hs := zetaRefl_pos
  have hre : (1 - zetaCellS0).re ≠ 1 := by rw [zetaRefl_re]; norm_num
  have hTailBase := zetaRefl_tail_1024_le
  have hTail : ‖(∑' m, etaPairTerm (1 - zetaCellS0) m) - Slarge‖ ≤
      (4 / 15 : ℝ) := by
    rw [hSdef]
    exact hTailBase
  have hFac := etaFactor_upper_S1refl
  have h := zeta_lower_of_Sn_tail_factor hs hre (2 * 1024) Slarge hSdef
    (1 / 3) hSlow (4 / 15) hTail (13 / 5) (by norm_num) hFac
  have heq : (((1 / 3 : ℝ) - 4 / 15) / (13 / 5)) = 1 / 39 := by norm_num
  rw [heq] at h
  exact h

/-- DOWNSTREAM: `1/39 ≤ ‖ζ(s1)‖ → 1/2340000000 ≤ ‖ζ(s0)‖`
(`ζ(s1) = F(s0)·ζ(s0)` + `‖F‖ ≤ 6e7`; i.e. `Azeta = Azeta1/6e7`). -/
theorem zeta_S0_lower_of_S1 (h1 : (1 / 39 : ℝ) ≤ ‖riemannZeta (1 - zetaCellS0)‖) :
    ((1 / 2340000000 : ℝ)) ≤ ‖riemannZeta zetaCellS0‖ := by
  have hFE := zetaFE_refl_eq_S0
  have hF := zetaFE_factor_upper_S0
  rw [hFE, norm_mul] at h1
  have hle : ‖zetaFEFactor zetaCellS0‖ * ‖riemannZeta zetaCellS0‖ ≤
      60000000 * ‖riemannZeta zetaCellS0‖ :=
    mul_le_mul_of_nonneg_right hF (norm_nonneg _)
  have heq : ((1 / 39 : ℝ)) / 60000000 = 1 / 2340000000 := by norm_num
  rw [← heq, div_le_iff₀ (by norm_num : (0 : ℝ) < 60000000)]
  linarith

#print axioms zetaCellS0_rpow_0395_le
#print axioms etaFactor_upper_S1refl
#print axioms zetaRefl_wall_threshold_iff
#print axioms zetaRefl_M1024_eq
#print axioms zetaRefl_M1024_rpow_ge
#print axioms zetaRefl_r_1024_le
#print axioms zetaRefl_tail_1024_le
#print axioms zetaRefl_M343_eq
#print axioms zetaRefl_M343_rpow_le
#print axioms zetaRefl_wall_necessity
#print axioms zetaRefl_r_1_ge
#print axioms zeta_S1_lower_of_S2048
#print axioms zeta_S0_lower_of_S1

/-!
## Kuzmin–Landau first-derivative test (linear phase) + AE phase-gap inputs.

GOAL (brief 2026-09-03, Tier 1): a standalone, reusable Kuzmin–Landau-type
exponential-sum bound proved from scratch (geometric sum + Jordan's inequality
+ elementary log phase-gaps), as the first bankable step toward cancellation
tails for AE's premise `‖S_{2048}(1-s0)‖ ≥ 1/3` in `zeta_S1_lower_of_S2048`
(`s1 = 1 - s0`, `Re = 0.605`, phase `t = 8.75`).

GREP-FIRST RECORD (searches run before writing; `Mathlib/` = repo-root `Mathlib/`):
* `Kuzmin|van der Corput|VanDerCorput|xponent.?[Pp]air` -- 0 hits: no
  Kuzmin–Landau / van der Corput / exponent-pair material exists in Mathlib.
  The test below is therefore created in-file (Tier 1 = linear phase, i.e. the
  geometric-sum core + denominator gap; the nonlinear assembly is residual).
* `sum_range_by_parts` -- EXISTS (`Mathlib/Algebra/BigOperators/Module.lean:57`,
  `Finset.sum_range_by_parts`, Abel transformation): the partial-summation half
  of a future nonlinear assembly is available; not consumed here (the linear
  test needs no summation by parts).
* Lower bounds on `‖riemannZeta‖`: ABSENT (no `norm`-`riemannZeta`-lower
  material in `Mathlib/`; agrees with the `§18b.10` record).
* Consumed Mathlib lemmas (every name verified by grep before use):
  `geom_sum_mul` (`Mathlib/Algebra/Ring/GeomSum.lean:232`, root namespace),
  `Complex.exp_nat_mul` (`Mathlib/Analysis/Complex/Exponential.lean:157`),
  `Complex.norm_exp_ofReal_mul_I`
  (`Mathlib/Analysis/Complex/Trigonometric.lean:950`),
  `Complex.exp_ofReal_mul_I_im` (same file, `:532`),
  `Complex.abs_im_le_norm` (`Mathlib/Analysis/Complex/Norm.lean:185`),
  `Real.mul_abs_le_abs_sin`
  (`Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean:93`),
  `Real.log_le_sub_one_of_pos` / `Real.log_div` / `Real.log_mul` /
  `Real.log_le_log` (`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`),
  `Real.pi_gt_three` (`Mathlib/Analysis/Real/Pi/Bounds.lean`),
  `le_div_iff₀` / `one_div_le_one_div_of_le` (order/field basics).

PROVED (all unconditional, no `sorry`/`admit`/`axiom`):
* (KL-a) `KL_geom_unit_norm_le`: geometric core
  `‖∑_{n<N} w^n‖ * ‖w-1‖ ≤ 2` for `‖w‖ = 1`.
* (KL-b) `KL_exp_lin_norm_le`: linear-phase exponential form
  (`e^{inθ} = (e^{iθ})^n` + unit modulus).
* (KL-c) `KL_denom_gap_le`: denominator ("first derivative") lower bound
  `2/π * |θ| ≤ ‖e^{iθ}-1‖` for `|θ| ≤ π/2` (Jordan via `‖z‖ ≥ |z.im|`).
* (KL-d) `KL_linear_firstDerivTest`: headline test
  `‖∑_{n<N} e^{inθ}‖ ≤ π/|θ|` for `0 < |θ| ≤ π/2`.
* (KL-e) `KL_log_gap_ge`: log phase-gap `1/(n+1) ≤ log(n+1) - log n`
  (the mean-value bound `1/ξ ≥ 1/(n+1)` via the elementary log inequality).
* (KL-f) `KL_AE_phase_gap_lower` / `KL_AE_phase_small`: exact AE numbers on
  the dyadic block `1024 ≤ n ≤ 2048` at `t = 8.75`:
  `8.75/2049 ≤ 8.75·(log(n+1)-log n)` (`≈ 0.00427`) and
  `|8.75·(log(n+1)-log n)| ≤ π/2` (so (KL-d) applies with `θ = 8.75·gap`).

RESIDUAL (quantified; Tier 2 needs, see final report):
* the nonlinear assembly (Abel bridge over `Finset.sum_range_by_parts` +
  total variation of `n ↦ 1/(e^{iΔₙ}-1)`) is still open;
* the numbers show the first-derivative test alone is quantitatively
  insufficient at AE parameters (`π/δ ≈ 736` on the `[1024,2048)` block vs the
  amplitude-weighted triangle `≈ 12.4`; per-dyadic-block KL weights diverge as
  `N^{0.395}`): closing the tail needs second-derivative / van der Corput
  machinery or rigorous complex interval arithmetic, not a sharper KL constant.
-/

/-- (KL-a) Geometric-sum core of Kuzmin–Landau: for a unit-modulus ratio,
`‖∑_{n<N} w^n‖ * ‖w-1‖ ≤ 2` (from `(∑ w^n)(w-1) = w^N-1` + triangle). -/
theorem KL_geom_unit_norm_le (w : ℂ) (hw : ‖w‖ = 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, w ^ n‖ * ‖w - 1‖ ≤ 2 := by
  have hgeom := geom_sum_mul w N
  have hnorm : ‖∑ n ∈ Finset.range N, w ^ n‖ * ‖w - 1‖ = ‖w ^ N - 1‖ := by
    rw [← norm_mul, hgeom]
  rw [hnorm]
  have htri := norm_sub_le (w ^ N) (1 : ℂ)
  rw [norm_one] at htri
  have hpow : ‖w ^ N‖ = 1 := by rw [norm_pow, hw, one_pow]
  linarith

/-- (KL-b) Linear-phase exponential form: `e^{inθ} = (e^{iθ})^n`, and
`‖e^{iθ}‖ = 1`, so (KL-a) applies directly. -/
theorem KL_exp_lin_norm_le (θ : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)‖ *
      ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ≤ 2 := by
  have hterm : ∀ n : ℕ, Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)
      = (Complex.exp ((θ : ℂ) * Complex.I)) ^ n := by
    intro n
    have e : ((n : ℂ) * (θ : ℂ) * Complex.I) = ((n : ℂ) * ((θ : ℂ) * Complex.I)) := by
      ring
    rw [e]
    exact Complex.exp_nat_mul _ n
  have hsum : (∑ n ∈ Finset.range N, Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I))
      = ∑ n ∈ Finset.range N, (Complex.exp ((θ : ℂ) * Complex.I)) ^ n :=
    Finset.sum_congr rfl (fun n _ => hterm n)
  rw [hsum]
  exact KL_geom_unit_norm_le _ (Complex.norm_exp_ofReal_mul_I θ) N

/-- (KL-c) Denominator ("first derivative") lower bound: `2/π * |θ| ≤ ‖e^{iθ}-1‖`
for `|θ| ≤ π/2`, via `‖z‖ ≥ |z.im|`, `(e^{iθ}-1).im = sin θ`, and Jordan. -/
theorem KL_denom_gap_le (θ : ℝ) (hθ : |θ| ≤ Real.pi / 2) :
    2 / Real.pi * |θ| ≤ ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ := by
  have him : (Complex.exp ((θ : ℂ) * Complex.I) - 1).im = Real.sin θ := by
    rw [Complex.sub_im, Complex.exp_ofReal_mul_I_im, Complex.one_im, sub_zero]
  have h1 : |Real.sin θ| ≤ ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ := by
    have h := Complex.abs_im_le_norm (Complex.exp ((θ : ℂ) * Complex.I) - 1)
    rwa [him] at h
  exact le_trans (Real.mul_abs_le_abs_sin hθ) h1

/-- (KL-d) Headline Kuzmin–Landau first-derivative test, linear phase:
`‖∑_{n<N} e^{inθ}‖ ≤ π/|θ|` for `θ ≠ 0`, `|θ| ≤ π/2`. -/
theorem KL_linear_firstDerivTest (θ : ℝ) (hθ0 : θ ≠ 0) (hθ : |θ| ≤ Real.pi / 2)
    (N : ℕ) :
    ‖∑ n ∈ Finset.range N, Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)‖ ≤
      Real.pi / |θ| := by
  have hpos : (0 : ℝ) < |θ| := abs_pos.mpr hθ0
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi0 : Real.pi ≠ 0 := ne_of_gt hpi
  have hθ0' : |θ| ≠ 0 := ne_of_gt hpos
  have hsmall : (0 : ℝ) < 2 / Real.pi * |θ| := mul_pos (div_pos two_pos hpi) hpos
  have hdenom : 2 / Real.pi * |θ| ≤ ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ :=
    KL_denom_gap_le θ hθ
  have hcore := KL_exp_lin_norm_le θ N
  have hmul : ‖∑ n ∈ Finset.range N, Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)‖ *
      (2 / Real.pi * |θ|) ≤ 2 :=
    le_trans (mul_le_mul_of_nonneg_left hdenom (norm_nonneg _)) hcore
  have hle : ‖∑ n ∈ Finset.range N, Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)‖ ≤
      2 / (2 / Real.pi * |θ|) := (le_div_iff₀ hsmall).mpr hmul
  have heq : (2 : ℝ) / (2 / Real.pi * |θ|) = Real.pi / |θ| := by
    field_simp
  rwa [heq] at hle

/-- (KL-e) Log phase-gap: `1/(n+1) ≤ log(n+1) - log n` for `1 ≤ n`
(the mean-value bound `log(n+1)-log n = 1/ξ ≥ 1/(n+1)` via
`log x ≤ x - 1` applied to `n/(n+1)`). -/
theorem KL_log_gap_ge (n : ℕ) (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) := by
  have hn0 : (0 : ℕ) < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by
    have hnn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    linarith
  have hfrac : (0 : ℝ) < (n : ℝ) / ((n : ℝ) + 1) := div_pos hnR h1
  have hlog := Real.log_le_sub_one_of_pos hfrac
  have hsplit : Real.log ((n : ℝ) / ((n : ℝ) + 1))
      = Real.log (n : ℝ) - Real.log ((n : ℝ) + 1) :=
    Real.log_div (ne_of_gt hnR) (ne_of_gt h1)
  have h10 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt h1
  have heq : (n : ℝ) / ((n : ℝ) + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by
    field_simp
    ring
  linarith

/-- (KL-f, lower) AE phase-gap on the dyadic block: for `1024 ≤ n ≤ 2048`,
`8.75/2049 ≤ 8.75·(log(n+1) - log n)` (value `≈ 0.00427`). -/
theorem KL_AE_phase_gap_lower (n : ℕ) (hn1 : 1024 ≤ n) (hn2 : n ≤ 2048) :
    (8.75 : ℝ) / 2049 ≤ 8.75 * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
  have hn : 1 ≤ n := by omega
  have hgap := KL_log_gap_ge n hn
  have hnR : ((n : ℝ) + 1) ≤ 2049 := by
    have hle : (n : ℝ) ≤ 2048 := by exact_mod_cast hn2
    linarith
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by
    have hnn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    linarith
  have h1 : (1 : ℝ) / 2049 ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le hpos hnR
  have h2 : (8.75 : ℝ) * (1 / 2049) ≤ 8.75 * (1 / ((n : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  have h3 : (8.75 : ℝ) * (1 / ((n : ℝ) + 1))
      ≤ 8.75 * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hgap (by norm_num)
  have e1 : (8.75 : ℝ) / 2049 = 8.75 * (1 / 2049) := by ring
  linarith

/-- (KL-f, upper) AE phase-step smallness: for `1024 ≤ n`,
`|8.75·(log(n+1) - log n)| ≤ π/2`, so (KL-d) applies with `θ = 8.75·gap`
(step `≤ 8.75/1024 ≈ 0.00854 ≪ π/2`). -/
theorem KL_AE_phase_small (n : ℕ) (hn1 : 1024 ≤ n) :
    |8.75 * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))| ≤ Real.pi / 2 := by
  have hn0 : (0 : ℕ) < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hnR0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hn1024 : (1024 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hinv : (0 : ℝ) < 1 / (n : ℝ) := one_div_pos.mpr hnR
  have h1n : (0 : ℝ) < 1 + 1 / (n : ℝ) := by linarith
  have hlog_le : Real.log (1 + 1 / (n : ℝ)) ≤ 1 / (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos h1n
    linarith
  have hsplit : Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)
      = Real.log (1 + 1 / (n : ℝ)) := by
    have h1 : ((n : ℝ) + 1) = (n : ℝ) * (1 + 1 / (n : ℝ)) := by
      field_simp
    rw [h1, Real.log_mul (ne_of_gt hnR) (ne_of_gt h1n)]
    rw [add_sub_cancel_left]
  have hnn : (0 : ℝ) ≤ Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) := by
    have hle : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have h := Real.log_le_log hnR hle
    linarith
  have hstep : (1 : ℝ) / (n : ℝ) ≤ 1 / 1024 :=
    one_div_le_one_div_of_le (by norm_num) hn1024
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hgap_nn : (0 : ℝ) ≤ 8.75 * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) :=
    mul_nonneg (by norm_num) hnn
  have hbound : 8.75 * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) ≤ Real.pi / 2 := by
    have h8 : 8.75 * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))
        ≤ 8.75 * (1 / (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [hsplit]
      exact hlog_le
    have h9 : (8.75 : ℝ) * (1 / (n : ℝ)) ≤ 8.75 * (1 / 1024) :=
      mul_le_mul_of_nonneg_left hstep (by norm_num)
    linarith
  rw [abs_of_nonneg hgap_nn]
  exact hbound

#print axioms KL_geom_unit_norm_le
#print axioms KL_exp_lin_norm_le
#print axioms KL_denom_gap_le
#print axioms KL_linear_firstDerivTest
#print axioms KL_log_gap_ge
#print axioms KL_AE_phase_gap_lower
#print axioms KL_AE_phase_small

/-!
## Tier-2 Abel assembly: partial-summation bridge + TV bound + AE block `[1024,2048)`.

GOAL (door-3 Tier-2, toward `‖S_{2048}(1-s0)‖ ≥ 1/3` premise of `zeta_S1_lower_of_S2048`
with `Azeta1 = 1/39`; `s1 = 1 - s0`, `σ = 0.605`, `t = 8.75`):
convert AK2 Tier-1 phase-gap bounds (`KL_linear_firstDerivTest`, `KL_AE_phase_gap_lower`,
`KL_AE_phase_small`) into an amplitude-weighted block bound via Abel summation, and close
the TV bound on `1/(e^{iΔ}-1)` weights that Tier-1 left open. Reuse Tier-1, do NOT add
linear-KL blocks (they scale as `N^{+0.395}`, divergent). Pair-absolute/Tendsto forms only;
no `∑'`-with-`0 <` tsum claims.

GREP-FIRST RECORD (run before writing; repo `zeta_rigorous.lean` + `Mathlib/`):
* `Finset.sum_range_by_parts` -- EXISTS (`Mathlib/Algebra/BigOperators/Module.lean:57`,
  `Finset.sum_range_by_parts`, Abel transformation, reserved/not consumed). Consumed below
  as `T2_abel_eq` (ℂ form via `smul_eq_mul`); norm form `T2_abel_norm` is new.
* `KL_geom_unit_norm_le` (`geom_sum_mul` core), `KL_log_gap_ge` (log MVT lower),
  `KL_AE_phase_gap_lower`/`KL_AE_phase_small` (AE numbers `8.75/2049`, `≪ π/2`) -- all in
  this file (read-only reuse). `T2_alt_le_one` reuses the geometric core at `w = -1`;
  `T2_gap_upper` mirrors `KL_AE_phase_small`'s `log(1+1/n) ≤ 1/n` pattern;
  `T2_gap_lower` is `KL_log_gap_ge (k+1)` + `push_cast`.
* `norm_etaPairTerm_le` (MVT pair bound `‖s‖·(2m+1)^{-Re-1}`) -- in this file; `T2_cpow_diff_le`
  below is the same MVT proof generalized from `a = 2m+1` to general consecutive `a/b = a+1`
  (needed for ALL `k`, not just even-odd pairs). No Mathlib MVT recreated:
  reuses `Convex.norm_image_sub_le_of_norm_deriv_le`, `hasDerivAt_ofReal_cpow_const`,
  `Complex.deriv_ofReal_cpow_const`, `Complex.norm_cpow_eq_rpow_re_of_pos`,
  `Real.rpow_le_rpow_of_nonpos` (same as source).
* `Complex.norm_exp_sub_one_le` (`‖exp x - 1‖ ≤ 2‖x‖`, `‖x‖ ≤ 1`,
  `Mathlib/Analysis/Complex/Exponential.lean:441`) -- EXISTS, consumed for `T2_exp_lipschitz`.
* `Complex.exp_ofReal_mul_I_re` / `_im`, `Complex.norm_exp_ofReal_mul_I`
  (`Mathlib/Analysis/Complex/Trigonometric.lean:528/532/950`) -- EXIST, consumed for the
  denominator `Re` lower bound and unit-modulus facts.
* `Complex.abs_re_le_norm` (`Mathlib/Analysis/Complex/Norm.lean:38`) -- EXISTS, consumed for
  `‖z‖ ≥ |z.re|`.
* `Real.cos_pi_sub` (`Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean:333`),
  `Real.cos_pos_of_mem_Ioo` (`:457`), `Real.pi_gt_three` -- EXIST, consumed for
  `cos(π-δ) = -cos δ ≥ 0` with `|δ| ≤ π/2`.
* `Real.rpow_le_rpow` / `Real.rpow_le_rpow_of_nonpos` / `Real.rpow_neg` / `Real.rpow_add` /
  `Real.rpow_one` / `Real.rpow_pos_of_pos`, `Real.log_le_sub_one_of_pos`, `Real.log_mul`,
  `Real.log_le_log`, `inv_le_inv₀`, `one_div_le_one_div_of_le`, `div_le_iff₀`,
  `mul_le_mul_of_nonneg_left/right`, `norm_sum_le`, `Finset.sum_le_sum`, `Nat.card_Ico`,
  `Finset.sum_const`, `nsmul_eq_mul`, `pow_add`, `pow_mul`, `Complex.exp_add`,
  `Complex.ofReal_natCast` -- all pre-existing Mathlib/already-used-in-file patterns,
  mirrored (not recreated).
* `zetaCellS0_re` (`= 0.395`), `zetaRefl_re` (`= 0.605`), `zetaRefl_pos`, `zetaRefl_norm_le`
  (`≤ 10`), `zetaRefl_M1024_rpow_ge` (`1024^0.605 ≥ 64`), `etaDirichletTerm_eq_cpow_neg` --
  all in this file (read-only reuse). No `zetaRefl*`/`Azeta1` redefined.
* `Kuzmin|van der Corput|exponent.?[Pp]air` in `Mathlib/` -- 0 hits (Tier-3 absent, not attempted).
* Name-clash check (`T2_abel|T2_alt|T2_gap|T2_AE|T2_Delta|T2_w_|T2_exp_|T2_cpow|T2_block|T2_shifted`) --
  0 hits before writing.

WHAT IS PROVED (all unconditional, FULL proofs, no `sorry`/`admit`/`axiom`):
* (A) Abel bridge: `T2_abel_eq` (ℂ equation from `sum_range_by_parts`) + `T2_abel_norm`
  (uniform-`B` norm bound).
* (B) Alternating engine: `T2_alt_le_one` (`‖∑_{<n} (-1)^i‖ ≤ 1` via the geometric core at
  `w = -1`, `‖-1-1‖ = 2`) + `T2_pow1024_one` + `T2_shifted_alt_eq`/`T2_shifted_alt_le`
  (the `[1024,1024+k)` shifted partial sums are also `≤ 1`, since `1024` is even).
* (C) Log gaps: `T2_gap_upper` (`≤ 1/(k+1)`, mirrors `KL_AE_phase_small`) + `T2_gap_lower`
  (`≥ 1/(k+2)`, from `KL_log_gap_ge`) + `T2_gap_abs_diff_le`
  (`|gap_{k+1}-gap_k| ≤ 1/(k+1)-1/(k+3)`, bracketing gives monotonicity for free).
* (D) Amplitudes at `s1 = 1 - s0`: `T2_AE_f` (`n^{-s1}` cpow form) + `T2_AE_eta_eq`
  (`eta = f·(-1)^k`, defeq to `etaDirichletTerm_eq_cpow_neg`) + `T2_AE_f_norm`
  (`‖f_k‖ = (k+1)^{-0.605}`) + `T2_AE_f_le` (`k ≥ 1024 → ‖f_k‖ ≤ 1/64`,
  from `1024^0.605 ≥ 64` + base monotonicity, Nat-cast form throughout so no
  `1025`-literal conversion is needed).
* (E) MVT single-step: `T2_cpow_diff_le` (general `a/b = a+1` cpow difference
  `≤ ‖s1‖·a^{-0.605-1}`, same MVT proof as `norm_etaPairTerm_le`) + `T2_AE_f_diff_le`
  (specialized to `a = (k:ℝ)+1`, `≤ 10/((k+1)^{0.605}·(k+1))` shape via `rpow_add`).
* (F) AE block `[1024,2048)`: `T2_block_upper`
  (`‖∑_{i<1024} eta_{1024+i}‖ ≤ 1/5`, via (A)+(B)+(D)+(E) with uniform `B = 1`,
  `sup ≤ 1/64`, per-step `≤ 10/(64·1024)`, `1023` steps `≤ 10230/65536`,
  total `≤ (4096+10230)/65536 = 14326/65536 ≤ 1/5`; all numerals by `norm_num`).
  Since `1/5 = 0.2 < 1/3`, the `[1024,2048)` Dirichlet block is SMALLER than AE's
  `1/3` threshold with margin `2/15 ≈ 0.133`.
* (G) TV bound (the Tier-1 open): `T2_Delta` (`π - 8.75·gap_k`) + `T2_w`
  (`(e^{iΔ}-1)^{-1}`) + `T2_denom_ge_one` (`‖e^{iΔ}-1‖ ≥ 1` via `Re = -cos δ - 1`,
  `|Re| = 1+cos δ ≥ 1`) + `T2_w_sup` (`‖w‖ ≤ 1`) + `T2_exp_lipschitz`
  (`‖e^{ia}-e^{ib}‖ ≤ 2|a-b|`, `|a-b| ≤ 1`, from `norm_exp_sub_one_le`) +
  `T2_gap_abs_diff_le` (C) + `T2_w_diff_le`
  (`‖w_{k+1}-w_k‖ ≤ 35/(((k:ℝ)+1)·((k:ℝ)+3))`, via
  `(e_b-e_a)/(den_a·den_b)` + denom `≥ 1` + Lipschitz `2·8.75·|gap diff|`) +
  `T2_w_TV_total` (`∑_{Ico 1024 2048} ‖w_{k+1}-w_k‖ ≤ 1/25`,
  `1024` terms `≤ 35/(1024·1024)` each, `35840/1048576 ≤ 1/25` by `norm_num`).

NUMBERS (exact, proved in-file; python scratch only for the report):
* Block: `sup ≤ 1/64 = 0.015625`; per-step `≤ 10/(64·1024) = 5/32768 ≈ 0.0001526`;
  `1023` steps `≤ 5115/32768 ≈ 0.1561`; total `≤ 1/64 + 5115/32768 = 5627/32768 ≈ 0.1717 ≤ 1/5`.
  Margin to `1/3`: `1/3 - 1/5 = 2/15 ≈ 0.1333` (block is `1.67×` BELOW the threshold).
* Weights: `sup ≤ 1`; per-step `≤ 35/((k+1)(k+3)) ≤ 35/1048576 ≈ 3.34e-05`;
  total TV `≤ 1024·35/1048576 = 35840/1048576 ≈ 0.0342 ≤ 1/25 = 0.04`.
* Triangle comparison: the same `[1024,2048)` block via amplitude triangle is
  `≈ 12.4` (guide §18b.10); Abel improves it `≈ 72×` to `≤ 0.2`. The linear-KL
  constant `π/δ ≈ 736` is never used (divergent `N^{+0.395}` scaling avoided by design).

RESIDUAL (exact, quantified -- report-and-stop, no spin):
* `‖S_{2048}(s1)‖ ≥ 1/3` is STILL OPEN. What Tier-2 gives is an UPPER bound on the
  second-half block (`≤ 1/5`); a LOWER bound on `S_{2048} = S_{1024} + block` needs a
  LOWER bound on `S_{1024}` (`‖S_{1024}‖ ≥ 1/3 + 1/5 = 8/15 ≈ 0.533` would suffice via
  reverse triangle, true value `≈ 0.56` has only `≈ 0.027` margin). The early block
  `[2,1024)` via the same Abel+MVT route is `≤ 8.6` (sup `≈ 0.514` at `k = 2` plus
  `∑_{k<1024} 10·(k+1)^{-1.605}`), i.e. `≈ 16×` too large to preserve `S_2 ≥ 1/3`
  (needs `< 1/3 - 1/3 = 0`, impossible since `‖S_2‖ = 1/3` has zero margin for the
  full `[2,2048)` block). Hence no UPPER-bound refinement of `[2,1024)` can close
  `S_{2048}` from `S_2`; the missing piece is a LOWER-bound technology for `S_{1024}`
  (rigorous complex interval arithmetic on `cos`/`sin(8.75·log n)`, `n ≤ 1024`, or
  Tier-3 second-derivative/van der Corput for a sharper early-block UPPER `< 0.05`
  to preserve a refined `S_K` lower at some `2 < K ≪ 1024`). The conditional
  `zeta_S1_lower_of_S2048` (`1/39 ≤ ‖ζ(s1)‖`) + downstream `zeta_S0_lower_of_S1`
  (`1/2340000000 ≤ ‖ζ(s0)‖`) are unchanged and ready.
-/

/-- (A) Abel bridge equation (ℂ form of `Finset.sum_range_by_parts`). -/
theorem T2_abel_eq (f g : ℕ → ℂ) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i =
      f (n - 1) * (∑ i ∈ Finset.range n, g i) -
      ∑ i ∈ Finset.range (n - 1), (f (i + 1) - f i) * (∑ j ∈ Finset.range (i + 1), g j) := by
  have h := Finset.sum_range_by_parts f g n
  simp only [smul_eq_mul] at h
  exact h

/-- (A) Abel bridge norm bound (uniform partial-sum cap `B`). -/
theorem T2_abel_norm (f g : ℕ → ℂ) (n : ℕ) (B : ℝ)
    (hB : ∀ k, k ≤ n → ‖∑ j ∈ Finset.range k, g j‖ ≤ B) (hB0 : 0 ≤ B) :
    ‖∑ i ∈ Finset.range n, f i * g i‖ ≤
      ‖f (n - 1)‖ * B + ∑ i ∈ Finset.range (n - 1), ‖f (i + 1) - f i‖ * B := by
  rw [T2_abel_eq f g n]
  have h1 : ‖f (n - 1) * (∑ i ∈ Finset.range n, g i)‖ ≤ ‖f (n - 1)‖ * B := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB n le_rfl) (norm_nonneg _)
  have h2 : ‖∑ i ∈ Finset.range (n - 1), (f (i + 1) - f i) * (∑ j ∈ Finset.range (i + 1), g j)‖ ≤
      ∑ i ∈ Finset.range (n - 1), ‖f (i + 1) - f i‖ * B := by
    calc ‖∑ i ∈ Finset.range (n - 1), (f (i + 1) - f i) * (∑ j ∈ Finset.range (i + 1), g j)‖
        ≤ ∑ i ∈ Finset.range (n - 1), ‖(f (i + 1) - f i) * (∑ j ∈ Finset.range (i + 1), g j)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (n - 1), ‖f (i + 1) - f i‖ * B := by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_mul]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply hB
          have hi2 : i < n - 1 := Finset.mem_range.mp hi
          omega
  exact le_trans (norm_sub_le _ _) (add_le_add h1 h2)

/-- (B) Alternating partial sums are `≤ 1` (geometric core at `w = -1`). -/
theorem T2_alt_le_one (n : ℕ) :
    ‖∑ i ∈ Finset.range n, (-1 : ℂ) ^ i‖ ≤ 1 := by
  have hcore := KL_geom_unit_norm_le (-1 : ℂ) (by simp) n
  have hden : ‖(-1 : ℂ) - 1‖ = 2 := by
    have heq : (-1 : ℂ) - 1 = -2 := by ring
    rw [heq, norm_neg]
    norm_num
  rw [hden] at hcore
  linarith

/-- (B) `(-1)^1024 = 1` (no parity API needed: `1024 = 2·512`). -/
theorem T2_pow1024_one : (-1 : ℂ) ^ (1024 : ℕ) = 1 := by
  have h1024 : (1024 : ℕ) = 2 * 512 := by norm_num
  rw [h1024, pow_mul]
  have h2 : (-1 : ℂ) ^ 2 = 1 := by norm_num
  rw [h2, one_pow]

/-- (B) Shifted alternating terms agree with unshifted ones (`1024` even). -/
theorem T2_shifted_alt_eq (j : ℕ) : (-1 : ℂ) ^ (1024 + j) = (-1 : ℂ) ^ j := by
  rw [pow_add, T2_pow1024_one, one_mul]

/-- (B) Shifted alternating partial sums are also `≤ 1`. -/
theorem T2_shifted_alt_le (k : ℕ) :
    ‖∑ j ∈ Finset.range k, (-1 : ℂ) ^ (1024 + j)‖ ≤ 1 := by
  have heq : (∑ j ∈ Finset.range k, (-1 : ℂ) ^ (1024 + j))
      = ∑ j ∈ Finset.range k, (-1 : ℂ) ^ j := by
    apply Finset.sum_congr rfl
    intro j _
    exact T2_shifted_alt_eq j
  rw [heq]
  exact T2_alt_le_one k

/-- (C) Log-gap upper: `log(k+2)-log(k+1) ≤ 1/(k+1)` (mirrors `KL_AE_phase_small`). -/
theorem T2_gap_upper (k : ℕ) :
    Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  have hk1ne : ((k : ℝ) + 1) ≠ 0 := ne_of_gt hk1
  have h1n : (0 : ℝ) < 1 + 1 / ((k : ℝ) + 1) := by
    have hinv : (0 : ℝ) < 1 / ((k : ℝ) + 1) := one_div_pos.mpr hk1
    linarith
  have hlog_le : Real.log (1 + 1 / ((k : ℝ) + 1)) ≤ 1 / ((k : ℝ) + 1) := by
    have h := Real.log_le_sub_one_of_pos h1n
    linarith
  have hsplit : Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)
      = Real.log (1 + 1 / ((k : ℝ) + 1)) := by
    have h1 : (k : ℝ) + 2 = ((k : ℝ) + 1) * (1 + 1 / ((k : ℝ) + 1)) := by
      field_simp
      ring
    rw [h1, Real.log_mul hk1ne (ne_of_gt h1n)]
    rw [add_sub_cancel_left]
  rw [hsplit]
  exact hlog_le

/-- (C) Log-gap lower from `KL_log_gap_ge (k+1)`. -/
theorem T2_gap_lower (k : ℕ) :
    1 / ((k : ℝ) + 2) ≤ Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1) := by
  have h := KL_log_gap_ge (k + 1) (by omega)
  push_cast at h
  have e1 : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by ring
  rw [e1] at h
  exact h

/-- (C) Gap nonnegativity (log monotonicity). -/
theorem T2_gap_nonneg (k : ℕ) :
    0 ≤ Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1) := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  have hle : (k : ℝ) + 1 ≤ (k : ℝ) + 2 := by linarith
  have h := Real.log_le_log hk1 hle
  linarith

/-- (C) Second-difference bound: `|gap_{k+1}-gap_k| ≤ 1/(k+1)-1/(k+3)` (bracketing). -/
theorem T2_gap_abs_diff_le (k : ℕ) :
    |((Real.log ((k : ℝ) + 3) - Real.log ((k : ℝ) + 2)) -
      (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)))|
      ≤ 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 3) := by
  have hUk : Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
    T2_gap_upper k
  have hLk : 1 / ((k : ℝ) + 2) ≤ Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1) :=
    T2_gap_lower k
  have hUk1raw := T2_gap_upper (k + 1)
  have hLk1raw := T2_gap_lower (k + 1)
  push_cast at hUk1raw hLk1raw
  have e32 : (k : ℝ) + 1 + 2 = (k : ℝ) + 3 := by ring
  have e21 : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by ring
  rw [e32, e21] at hUk1raw hLk1raw
  -- hUk1raw : log(k+3)-log(k+2) ≤ 1/(k+2); hLk1raw : 1/(k+3) ≤ log(k+3)-log(k+2)
  have h_nn : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 3) := by
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith
    have hk3 : (0 : ℝ) < (k : ℝ) + 3 := by linarith
    have hle : (1 : ℝ) / ((k : ℝ) + 3) ≤ 1 / ((k : ℝ) + 1) :=
      one_div_le_one_div_of_le hk1 (by linarith)
    linarith
  rw [abs_le]
  constructor
  · linarith [hUk, hLk1raw]
  · have hle0 : (Real.log ((k : ℝ) + 3) - Real.log ((k : ℝ) + 2)) -
        (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)) ≤ 0 := by
      linarith [hUk1raw, hLk]
    linarith [hle0, h_nn]

/-- (D) AE amplitude in cpow form: `((k+1):ℝ)^{-s1}` with `s1 = 1 - s0`. -/
noncomputable def T2_AE_f (k : ℕ) : ℂ :=
  (((((k : ℝ) + 1 : ℝ)) : ℂ)) ^ (-(1 - zetaCellS0))

/-- (D) `eta = f·(-1)^k` (defeq to `etaDirichletTerm_eq_cpow_neg`). -/
theorem T2_AE_eta_eq (k : ℕ) :
    etaDirichletTerm (1 - zetaCellS0) k = T2_AE_f k * (-1 : ℂ) ^ k := by
  unfold T2_AE_f
  rw [mul_comm]
  exact etaDirichletTerm_eq_cpow_neg _ _

/-- (D) Norm of the amplitude: `‖f_k‖ = (k+1)^{-0.605}`. -/
theorem T2_AE_f_norm (k : ℕ) :
    ‖T2_AE_f k‖ = (((k : ℝ) + 1 : ℝ) ^ (-0.605 : ℝ)) := by
  unfold T2_AE_f
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  have hre : (-(1 - zetaCellS0)).re = (-0.605 : ℝ) := by
    rw [Complex.neg_re, Complex.sub_re, Complex.one_re, zetaCellS0_re]
    norm_num
  have hnorm := Complex.norm_cpow_eq_rpow_re_of_pos hpos (-(1 - zetaCellS0))
  rw [hnorm, hre]

/-- (D) Head amplitude `≤ 1/64` for `k ≥ 1024` (Nat-cast form, no `1025` literal). -/
theorem T2_AE_f_le {k : ℕ} (hk : 1024 ≤ k) : ‖T2_AE_f k‖ ≤ 1 / 64 := by
  rw [T2_AE_f_norm]
  have h1024 := zetaRefl_M1024_rpow_ge
  have hkR : ((((1024 : ℕ)) : ℝ)) ≤ (k : ℝ) + 1 := by
    have hle : ((((1024 : ℕ)) : ℝ)) ≤ (k : ℝ) := Nat.cast_le.mpr hk
    linarith
  have hge : (64 : ℝ) ≤ (((k : ℝ) + 1 : ℝ) ^ (0.605 : ℝ)) := by
    have hmono : (((((1024 : ℕ)) : ℝ)) ^ (0.605 : ℝ)) ≤ ((((k : ℝ) + 1 : ℝ)) ^ (0.605 : ℝ)) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hkR (by norm_num)
    linarith [h1024, hmono]
  have hposA : (0 : ℝ) < ((((k : ℝ) + 1 : ℝ)) ^ (0.605 : ℝ)) := by
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith
    exact Real.rpow_pos_of_pos hpos _
  have hrw : ((((k : ℝ) + 1 : ℝ)) ^ (-0.605 : ℝ))
      = (((((k : ℝ) + 1 : ℝ)) ^ (0.605 : ℝ)))⁻¹ := by
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith
    exact Real.rpow_neg (le_of_lt hpos) _
  rw [hrw]
  have hInv : ((((k : ℝ) + 1 : ℝ) ^ (0.605 : ℝ)))⁻¹ ≤ (64 : ℝ)⁻¹ :=
    (inv_le_inv₀ hposA (by norm_num)).mpr hge
  have heq : (64 : ℝ)⁻¹ = 1 / 64 := by norm_num
  rw [heq] at hInv
  exact hInv

/-- (E) General consecutive-cpow MVT bound (generalizes `norm_etaPairTerm_le` from
`2m+1/2m+2` to any `a/b = a+1`). -/
theorem T2_cpow_diff_le (a b : ℝ) (ha : 0 < a) (hb : b = a + 1) :
    ‖(((b : ℂ)) ^ (-(1 - zetaCellS0)) - (((a : ℂ)) ^ (-(1 - zetaCellS0))))‖ ≤
      ‖1 - zetaCellS0‖ * (a ^ (-(1 - zetaCellS0).re - 1)) := by
  have hs : 0 < (1 - zetaCellS0).re := zetaRefl_pos
  have hs0 : (1 - zetaCellS0) ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    exact lt_irrefl _ hs
  have hnegs : -(1 - zetaCellS0) ≠ 0 := neg_ne_zero.mpr hs0
  have hab : a ≤ b := by rw [hb]; linarith
  have hdiff : ∀ x ∈ Set.Icc a b,
      DifferentiableAt ℝ (fun t : ℝ => (t : ℂ) ^ (-(1 - zetaCellS0))) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha (Set.mem_Icc.mp hx).1
    exact (hasDerivAt_ofReal_cpow_const (ne_of_gt hx0) hnegs).differentiableAt
  have hderiv_eq : ∀ x : ℝ, x ≠ 0 →
      deriv (fun t : ℝ => (t : ℂ) ^ (-(1 - zetaCellS0))) x
        = (-(1 - zetaCellS0)) * (x : ℂ) ^ (-(1 - zetaCellS0) - 1) := by
    intro x hx0
    have h := Complex.deriv_ofReal_cpow_const hx0 (c := -(1 - zetaCellS0)) hnegs
    simpa using h
  have hexp_nonpos : -(1 - zetaCellS0).re - 1 ≤ 0 := by linarith
  have hbound : ∀ x ∈ Set.Icc a b, ‖deriv (fun t : ℝ => (t : ℂ) ^ (-(1 - zetaCellS0))) x‖
      ≤ ‖1 - zetaCellS0‖ * (a ^ (-(1 - zetaCellS0).re - 1)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha (Set.mem_Icc.mp hx).1
    have hax : a ≤ x := (Set.mem_Icc.mp hx).1
    rw [hderiv_eq x (ne_of_gt hx0)]
    have hnorm_cpow : ‖(x : ℂ) ^ (-(1 - zetaCellS0) - 1)‖ = x ^ ((-((1 - zetaCellS0)) - 1).re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos hx0 _
    have hre : ((-((1 - zetaCellS0)) - 1).re) = -(1 - zetaCellS0).re - 1 := by
      rw [Complex.sub_re, Complex.neg_re, Complex.one_re]
    have hle : x ^ (-(1 - zetaCellS0).re - 1) ≤ a ^ (-(1 - zetaCellS0).re - 1) :=
      Real.rpow_le_rpow_of_nonpos ha hax hexp_nonpos
    have hnorm_neg : ‖-(1 - zetaCellS0)‖ = ‖1 - zetaCellS0‖ := norm_neg _
    calc ‖-(1 - zetaCellS0) * (x : ℂ) ^ (-(1 - zetaCellS0) - 1)‖
        = ‖1 - zetaCellS0‖ * (x ^ (-(1 - zetaCellS0).re - 1)) := by
          rw [norm_mul, hnorm_neg, hnorm_cpow, hre]
      _ ≤ ‖1 - zetaCellS0‖ * (a ^ (-(1 - zetaCellS0).re - 1)) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_Icc a b) (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  have hba : ‖b - a‖ = 1 := by
    have hsub : b - a = 1 := by rw [hb]; ring
    rw [hsub, norm_one]
  rw [hba, mul_one] at hmvt
  exact hmvt

/-- (E) Single-step amplitude difference at `k ≥ 1024`, in `rpow` form. -/
theorem T2_AE_f_diff_le {k : ℕ} (hk : 1024 ≤ k) :
    ‖T2_AE_f (k + 1) - T2_AE_f k‖ ≤ 10 * (((((k : ℝ) + 1 : ℝ)) ^ (-0.605 : ℝ)) / 1024) := by
  have hC : ‖1 - zetaCellS0‖ ≤ 10 := zetaRefl_norm_le
  have ha_pos : (0 : ℝ) < (k : ℝ) + 1 := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  have ha1024 : ((((1024 : ℕ)) : ℝ)) ≤ (k : ℝ) + 1 := by
    have hle : ((((1024 : ℕ)) : ℝ)) ≤ (k : ℝ) := Nat.cast_le.mpr hk
    linarith
  have e_next : ((((k + 1 : ℕ) : ℝ) + 1 : ℝ)) = ((k : ℝ) + 1 + 1 : ℝ) := by
    push_cast
    ring
  have e_base : T2_AE_f (k + 1) - T2_AE_f k
      = ((((k : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-(1 - zetaCellS0))
        - (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-(1 - zetaCellS0))) := by
    unfold T2_AE_f
    rw [e_next]
  rw [e_base]
  have a_eq : ((k : ℝ) + 1 + 1 : ℝ) = ((k : ℝ) + 1 : ℝ) + 1 := by ring
  rw [a_eq]
  have hMVT := T2_cpow_diff_le ((k : ℝ) + 1) (((k : ℝ) + 1) + 1) ha_pos rfl
  have hsplit : ((((k : ℝ) + 1 : ℝ)) ^ (-(1 - zetaCellS0).re - 1))
      = ((((k : ℝ) + 1 : ℝ)) ^ (-0.605 : ℝ)) * ((((k : ℝ) + 1 : ℝ)) ^ (-1 : ℝ)) := by
    have hadd : (-(1 - zetaCellS0).re - 1 : ℝ) = (-0.605 : ℝ) + (-1 : ℝ) := by
      have hre : (-(1 - zetaCellS0).re) = (-0.605 : ℝ) := by
        rw [zetaRefl_re]
      rw [hre]
      ring
    rw [hadd, Real.rpow_add ha_pos]
  have hUp : ((((k : ℝ) + 1 : ℝ)) ^ (-(1 - zetaCellS0).re - 1))
      ≤ ((((k : ℝ) + 1 : ℝ)) ^ (-0.605 : ℝ)) / 1024 := by
    rw [hsplit]
    have hInv : ((((k : ℝ) + 1 : ℝ)) ^ (-1 : ℝ)) ≤ 1 / 1024 := by
      have hrw : ((((k : ℝ) + 1 : ℝ)) ^ (-1 : ℝ)) = (((((k : ℝ) + 1 : ℝ)) ^ (1 : ℝ)))⁻¹ := by
        have hx : (0 : ℝ) ≤ (k : ℝ) + 1 := le_of_lt ha_pos
        have := Real.rpow_neg hx (1 : ℝ)
        simpa using this
      rw [hrw]
      have h1ge : (1024 : ℝ) ≤ ((((k : ℝ) + 1 : ℝ)) ^ (1 : ℝ)) := by
        rw [Real.rpow_one]
        have hle : ((((1024 : ℕ)) : ℝ)) ≤ (k : ℝ) := Nat.cast_le.mpr hk
        have e1024 : (1024 : ℝ) = ((((1024 : ℕ)) : ℝ)) := by norm_cast
        rw [e1024]
        linarith
      have hpos1 : (0 : ℝ) < ((((k : ℝ) + 1 : ℝ)) ^ (1 : ℝ)) :=
        Real.rpow_pos_of_pos ha_pos _
      have hInv2 : (((((k : ℝ) + 1 : ℝ)) ^ (1 : ℝ)))⁻¹ ≤ (1024 : ℝ)⁻¹ :=
        (inv_le_inv₀ hpos1 (by norm_num)).mpr h1ge
      have heq : (1024 : ℝ)⁻¹ = 1 / 1024 := by norm_num
      rw [heq] at hInv2
      exact hInv2
    have hnn : (0 : ℝ) ≤ ((((k : ℝ) + 1 : ℝ)) ^ (-0.605 : ℝ)) :=
      le_of_lt (Real.rpow_pos_of_pos ha_pos _)
    calc ((((k : ℝ) + 1 : ℝ)) ^ (-0.605 : ℝ)) * ((((k : ℝ) + 1 : ℝ)) ^ (-1 : ℝ))
        ≤ ((((k : ℝ) + 1 : ℝ)) ^ (-0.605 : ℝ)) * (1 / 1024) :=
          mul_le_mul_of_nonneg_left hInv hnn
      _ = ((((k : ℝ) + 1 : ℝ)) ^ (-0.605 : ℝ)) / 1024 := by ring
  calc ‖((((k : ℝ) + 1 : ℝ) + 1 : ℝ) : ℂ) ^ (-(1 - zetaCellS0))
          - (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-(1 - zetaCellS0)))‖
      ≤ ‖1 - zetaCellS0‖ * (((((k : ℝ) + 1 : ℝ)) ^ (-(1 - zetaCellS0).re - 1))) := hMVT
    _ ≤ 10 * (((((k : ℝ) + 1 : ℝ)) ^ (-0.605 : ℝ)) / 1024) := by
        have hXnn : (0 : ℝ) ≤ ((((k : ℝ) + 1 : ℝ)) ^ (-(1 - zetaCellS0).re - 1)) :=
          le_of_lt (Real.rpow_pos_of_pos ha_pos _)
        have h1 : ‖1 - zetaCellS0‖ * (((((k : ℝ) + 1 : ℝ)) ^ (-(1 - zetaCellS0).re - 1)))
            ≤ 10 * (((((k : ℝ) + 1 : ℝ)) ^ (-(1 - zetaCellS0).re - 1))) :=
          mul_le_mul_of_nonneg_right hC hXnn
        have h2 : (10 : ℝ) * (((((k : ℝ) + 1 : ℝ)) ^ (-(1 - zetaCellS0).re - 1)))
            ≤ 10 * (((((k : ℝ) + 1 : ℝ)) ^ (-0.605 : ℝ)) / 1024) :=
          mul_le_mul_of_nonneg_left hUp (by norm_num)
        linarith [h1, h2]

set_option maxHeartbeats 800000 in
/-- (F) AE block `[1024,2048)` is `≤ 1/5` (Abel with uniform `B = 1`). -/
theorem T2_block_upper :
    ‖∑ i ∈ Finset.range 1024, etaDirichletTerm (1 - zetaCellS0) (1024 + i)‖ ≤ 1 / 5 := by
  let f : ℕ → ℂ := fun i => T2_AE_f (1024 + i)
  let g : ℕ → ℂ := fun i => (-1 : ℂ) ^ (1024 + i)
  have heq : (∑ i ∈ Finset.range 1024, etaDirichletTerm (1 - zetaCellS0) (1024 + i))
      = ∑ i ∈ Finset.range 1024, f i * g i := by
    apply Finset.sum_congr rfl
    intro i _
    show etaDirichletTerm _ _ = T2_AE_f _ * _
    exact T2_AE_eta_eq _
  rw [heq]
  have hB : ∀ k, k ≤ 1024 → ‖∑ j ∈ Finset.range k, g j‖ ≤ 1 := by
    intro k _
    show ‖∑ j ∈ Finset.range k, (-1 : ℂ) ^ (1024 + j)‖ ≤ 1
    exact T2_shifted_alt_le k
  have hAbel := T2_abel_norm f g 1024 1 hB (by norm_num)
  have hsup : ‖f (1024 - 1)‖ ≤ 1 / 64 := by
    show ‖T2_AE_f (1024 + (1024 - 1))‖ ≤ 1 / 64
    have e : 1024 + (1024 - 1) = 2047 := by norm_num
    rw [e]
    exact T2_AE_f_le (by norm_num)
  have hTV : ∑ i ∈ Finset.range (1024 - 1), ‖f (i + 1) - f i‖ * 1
      ≤ 5115 / 32768 := by
    have h1023 : (1024 - 1 : ℕ) = 1023 := by norm_num
    rw [h1023]
    calc ∑ i ∈ Finset.range 1023, ‖f (i + 1) - f i‖ * 1
        = ∑ i ∈ Finset.range 1023, ‖f (i + 1) - f i‖ := by
          simp
      _ ≤ ∑ _i ∈ Finset.range 1023, (10 * ((1 / 64) / 1024)) := by
          apply Finset.sum_le_sum
          intro i _
          have hk : 1024 ≤ 1024 + i := Nat.le_add_right _ _
          have hdiff : ‖f (i + 1) - f i‖ ≤ 10 * (((((1024 + i : ℕ) : ℝ) + 1 : ℝ) ^ (-0.605 : ℝ)) / 1024) := by
            show ‖T2_AE_f (1024 + (i + 1)) - T2_AE_f (1024 + i)‖ ≤ _
            have e : 1024 + (i + 1) = (1024 + i) + 1 := by omega
            rw [e]
            exact T2_AE_f_diff_le hk
          have hamp : ((((1024 + i : ℕ) : ℝ) + 1 : ℝ) ^ (-0.605 : ℝ)) ≤ 1 / 64 := by
            have hk2 : 1024 ≤ 1024 + i := Nat.le_add_right _ _
            have hle : ‖T2_AE_f (1024 + i)‖ ≤ 1 / 64 := T2_AE_f_le hk2
            rw [T2_AE_f_norm] at hle
            exact hle
          calc ‖f (i + 1) - f i‖ ≤ 10 * (((((1024 + i : ℕ) : ℝ) + 1 : ℝ) ^ (-0.605 : ℝ)) / 1024) := hdiff
            _ ≤ 10 * ((1 / 64) / 1024) := by
                apply mul_le_mul_of_nonneg_left _ (by norm_num)
                exact div_le_div_of_nonneg_right hamp (by norm_num)
      _ = 5115 / 32768 := by
          rw [Finset.sum_const, Finset.card_range]
          norm_num [nsmul_eq_mul]
  have hfin : ‖f (1024 - 1)‖ * 1 + ∑ i ∈ Finset.range (1024 - 1), ‖f (i + 1) - f i‖ * 1
      ≤ 1 / 5 := by
    have h1023 : (1024 - 1 : ℕ) = 1023 := by norm_num
    have hsup64 : ‖f (1024 - 1)‖ * 1 ≤ 512 / 32768 := by
      have : ‖f (1024 - 1)‖ ≤ 1 / 64 := hsup
      have e : (1 : ℝ) / 64 = 512 / 32768 := by norm_num
      linarith
    linarith [hsup64, hTV]
  calc ‖∑ i ∈ Finset.range 1024, f i * g i‖
      ≤ ‖f (1024 - 1)‖ * 1 + ∑ i ∈ Finset.range (1024 - 1), ‖f (i + 1) - f i‖ * 1 := hAbel
    _ ≤ 1 / 5 := hfin

/-- (G) AE phase increment `Δ_k = π - 8.75·gap_k`. -/
noncomputable def T2_Delta (k : ℕ) : ℝ :=
  Real.pi - 8.75 * (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1))

/-- (G) AE weight `w_k = (e^{iΔ_k}-1)^{-1}` (the Tier-1 open). -/
noncomputable def T2_w (k : ℕ) : ℂ :=
  (Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I) - 1)⁻¹

/-- (G) Denominator lower `‖e^{iΔ_k}-1‖ ≥ 1` for `k ≥ 1024` (via `Re`). -/
theorem T2_denom_ge_one {k : ℕ} (hk : 1024 ≤ k) :
    1 ≤ ‖Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I) - 1‖ := by
  have hgap_up := T2_gap_upper k
  have hkR : (1024 : ℝ) ≤ (k : ℝ) := by
    have : ((((1024 : ℕ)) : ℝ)) ≤ (k : ℝ) := Nat.cast_le.mpr hk
    have e1024 : (1024 : ℝ) = ((((1024 : ℕ)) : ℝ)) := by norm_cast
    rw [e1024]
    exact this
  have hgap_le : Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1) ≤ 1 / 1025 := by
    have h1 : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / 1025 := by
      apply one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith [hgap_up, h1]
  have hdelta_nn : (0 : ℝ) ≤ 8.75 * (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)) := by
    apply mul_nonneg (by norm_num)
    exact T2_gap_nonneg k
  have hdelta_le : 8.75 * (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)) ≤ 8.75 / 1025 := by
    have := mul_le_mul_of_nonneg_left hgap_le (by norm_num : (0 : ℝ) ≤ 8.75)
    linarith [this]
  have hdelta_small : |8.75 * (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1))| ≤ Real.pi / 2 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    rw [abs_of_nonneg hdelta_nn]
    linarith
  have hcos_nn : 0 ≤ Real.cos (8.75 * (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1))) := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hmem : 8.75 * (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1))
        ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · linarith
      · linarith [hdelta_le, hpi]
    exact le_of_lt (Real.cos_pos_of_mem_Ioo hmem)
  have hRe : (Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I) - 1).re
      = -Real.cos (8.75 * (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1))) - 1 := by
    have hcos : Real.cos (T2_Delta k) = -Real.cos (8.75 * (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1))) := by
      unfold T2_Delta
      rw [Real.cos_pi_sub]
    have hre : (Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I)).re = Real.cos (T2_Delta k) := by
      have := Complex.exp_ofReal_mul_I_re (T2_Delta k)
      simpa using this
    rw [Complex.sub_re, Complex.one_re, hre, hcos]
  have habs : |((Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I) - 1).re)| ≥ 1 := by
    rw [hRe]
    have : |-Real.cos (8.75 * (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1))) - 1|
        = 1 + Real.cos (8.75 * (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1))) := by
      rw [abs_of_nonpos (by linarith [hcos_nn])]
      ring
    rw [this]
    linarith [hcos_nn]
  exact le_trans habs (Complex.abs_re_le_norm _)

/-- (G) Weight sup `‖w_k‖ ≤ 1`. -/
theorem T2_w_sup {k : ℕ} (hk : 1024 ≤ k) : ‖T2_w k‖ ≤ 1 := by
  unfold T2_w
  rw [norm_inv]
  have hden := T2_denom_ge_one hk
  have hpos : (0 : ℝ) < ‖Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I) - 1‖ :=
    lt_of_lt_of_le (by norm_num) hden
  have hInv : (‖Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I) - 1‖)⁻¹ ≤ (1 : ℝ)⁻¹ :=
    (inv_le_inv₀ hpos (by norm_num)).mpr hden
  have heq : (1 : ℝ)⁻¹ = 1 := by norm_num
  rw [heq] at hInv
  exact hInv

/-- (G) Imaginary-exponential Lipschitz: `‖e^{ia}-e^{ib}‖ ≤ 2|a-b|`, `|a-b| ≤ 1`. -/
theorem T2_exp_lipschitz (a b : ℝ) (hab : |a - b| ≤ 1) :
    ‖Complex.exp (((a : ℂ)) * Complex.I) - Complex.exp (((b : ℂ)) * Complex.I)‖ ≤ 2 * |a - b| := by
  have hsub : Complex.exp (((a : ℂ)) * Complex.I) - Complex.exp (((b : ℂ)) * Complex.I)
      = Complex.exp (((b : ℂ)) * Complex.I) * (Complex.exp (((((a - b : ℝ))) : ℂ) * Complex.I) - 1) := by
    have hadd : ((a : ℂ)) * Complex.I = ((b : ℂ)) * Complex.I + ((((a - b : ℝ))) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hadd, Complex.exp_add]
    ring
  rw [hsub, norm_mul, Complex.norm_exp_ofReal_mul_I]
  rw [one_mul]
  have hnorm_eq : ‖((((a - b : ℝ))) : ℂ) * Complex.I‖ = |a - b| := by
    rw [norm_mul, Complex.norm_I]
    rw [mul_one]
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hle : ‖((((a - b : ℝ))) : ℂ) * Complex.I‖ ≤ 1 := by
    rw [hnorm_eq]
    exact hab
  have hcore := Complex.norm_exp_sub_one_le (x := ((((a - b : ℝ))) : ℂ) * Complex.I) hle
  linarith [hcore, hnorm_eq]

/-- (G) Per-step weight TV `≤ 35/(((k:ℝ)+1)·((k:ℝ)+3))`. -/
theorem T2_w_diff_le {k : ℕ} (hk : 1024 ≤ k) :
    ‖T2_w (k + 1) - T2_w k‖ ≤ 35 / ((((k : ℝ) + 1) * ((k : ℝ) + 3))) := by
  have hkR : (0 : ℝ) < (k : ℝ) + 1 := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  have hkR3 : (0 : ℝ) < (k : ℝ) + 3 := by linarith
  have hden_a := T2_denom_ge_one hk
  have hden_b := T2_denom_ge_one (le_trans hk (Nat.le_succ _))
  have hden_a_ne : (Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I) - 1) ≠ 0 := by
    have hpos : (0 : ℝ) < ‖Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I) - 1‖ :=
      lt_of_lt_of_le (by norm_num) hden_a
    exact norm_pos_iff.mp hpos
  have hden_b_ne : (Complex.exp ((((T2_Delta (k + 1) : ℝ)) : ℂ) * Complex.I) - 1) ≠ 0 := by
    have hpos : (0 : ℝ) < ‖Complex.exp ((((T2_Delta (k + 1) : ℝ)) : ℂ) * Complex.I) - 1‖ :=
      lt_of_lt_of_le (by norm_num) hden_b
    exact norm_pos_iff.mp hpos
  have hform : T2_w (k + 1) - T2_w k
      = -((Complex.exp ((((T2_Delta (k + 1) : ℝ)) : ℂ) * Complex.I)
        - Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I))
        / ((Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I) - 1)
          * (Complex.exp ((((T2_Delta (k + 1) : ℝ)) : ℂ) * Complex.I) - 1))) := by
    unfold T2_w
    rw [inv_sub_inv hden_b_ne hden_a_ne]
    have hD : (Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I) - 1)
          - (Complex.exp ((((T2_Delta (k + 1) : ℝ)) : ℂ) * Complex.I) - 1)
        = -((Complex.exp ((((T2_Delta (k + 1) : ℝ)) : ℂ) * Complex.I)
          - Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I))) := by
      ring
    have hden_comm : (Complex.exp ((((T2_Delta (k + 1) : ℝ)) : ℂ) * Complex.I) - 1)
          * (Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I) - 1)
        = (Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I) - 1)
          * (Complex.exp ((((T2_Delta (k + 1) : ℝ)) : ℂ) * Complex.I) - 1) := by
      ring
    rw [hD, hden_comm, neg_div]
  rw [hform, norm_neg, norm_div, norm_mul]
  have hden_ge : (1 : ℝ) ≤ ‖Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I) - 1‖ *
      ‖Complex.exp ((((T2_Delta (k + 1) : ℝ)) : ℂ) * Complex.I) - 1‖ := by
    have h1 : (1 : ℝ) * 1 ≤ _ := mul_le_mul hden_a hden_b (by norm_num) (by linarith [hden_a])
    simpa using h1
  have hnum_le : ‖Complex.exp ((((T2_Delta (k + 1) : ℝ)) : ℂ) * Complex.I)
        - Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I)‖
      ≤ 17.5 * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 3)) := by
    have hDelta_eq : T2_Delta (k + 1) - T2_Delta k
        = -(8.75 * (((Real.log ((k : ℝ) + 3) - Real.log ((k : ℝ) + 2)) -
          (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1))))) := by
      unfold T2_Delta
      push_cast
      ring
    have hgap := T2_gap_abs_diff_le k
    push_cast at hgap ⊢
    have e32 : (k : ℝ) + 1 + 2 = (k : ℝ) + 3 := by ring
    have e21 : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by ring
    have habs1 : |T2_Delta (k + 1) - T2_Delta k|
        = 8.75 * |((Real.log ((k : ℝ) + 3) - Real.log ((k : ℝ) + 2)) -
          (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)))| := by
      rw [hDelta_eq, abs_neg, abs_mul]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8.75)]
    have habs_le : |T2_Delta (k + 1) - T2_Delta k| ≤ 1 := by
      rw [habs1]
      have h1 : |((Real.log ((k : ℝ) + 3) - Real.log ((k : ℝ) + 2)) -
          (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)))|
          ≤ 1 / ((k : ℝ) + 1) := by
        have h2 := T2_gap_abs_diff_le k
        have hBnn : (0 : ℝ) ≤ 1 / ((k : ℝ) + 3) :=
          le_of_lt (one_div_pos.mpr hkR3)
        linarith [h2, hBnn]
      have h2 : 8.75 * |((Real.log ((k : ℝ) + 3) - Real.log ((k : ℝ) + 2)) -
          (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)))| ≤ 8.75 * (1 / ((k : ℝ) + 1)) := by
        exact mul_le_mul_of_nonneg_left h1 (by norm_num)
      have h3 : 8.75 * (1 / ((k : ℝ) + 1)) ≤ 1 := by
        have hle : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / 1024 := by
          apply one_div_le_one_div_of_le (by norm_num) (by
            have hle2 : ((((1024 : ℕ)) : ℝ)) ≤ (k : ℝ) := Nat.cast_le.mpr hk
            have e1024 : (1024 : ℝ) = ((((1024 : ℕ)) : ℝ)) := by norm_cast
            rw [e1024]
            linarith)
        linarith [hle]
      linarith [h2, h3]
    have hlip := T2_exp_lipschitz (T2_Delta (k + 1)) (T2_Delta k) habs_le
    rw [habs1] at hlip
    have h35 : (2 : ℝ) * (8.75 * |((Real.log ((k : ℝ) + 3) - Real.log ((k : ℝ) + 2)) -
        (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)))|)
        = 35 * ((1 / 2) * |((Real.log ((k : ℝ) + 3) - Real.log ((k : ℝ) + 2)) -
          (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)))|) := by ring
    have hfin : (2 : ℝ) * (8.75 * |((Real.log ((k : ℝ) + 3) - Real.log ((k : ℝ) + 2)) -
        (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)))|)
        ≤ 17.5 * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 3)) := by
      have h1 : |((Real.log ((k : ℝ) + 3) - Real.log ((k : ℝ) + 2)) -
          (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)))|
          ≤ 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 3) := hgap
      have hmul := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2 * 8.75)
      have heq : (2 : ℝ) * 8.75 = 17.5 := by norm_num
      linarith [hmul, heq]
    linarith [hlip, hfin]
  have hdiv_le : ‖Complex.exp ((((T2_Delta (k + 1) : ℝ)) : ℂ) * Complex.I)
        - Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I)‖ /
        (‖Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I) - 1‖ *
          ‖Complex.exp ((((T2_Delta (k + 1) : ℝ)) : ℂ) * Complex.I) - 1‖)
      ≤ ‖Complex.exp ((((T2_Delta (k + 1) : ℝ)) : ℂ) * Complex.I)
        - Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I)‖ := by
    have hpos : (0 : ℝ) < ‖Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I) - 1‖ *
        ‖Complex.exp ((((T2_Delta (k + 1) : ℝ)) : ℂ) * Complex.I) - 1‖ :=
      lt_of_lt_of_le (by norm_num) hden_ge
    rw [div_le_iff₀ hpos]
    have hle : ‖Complex.exp ((((T2_Delta (k + 1) : ℝ)) : ℂ) * Complex.I)
        - Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I)‖ * 1
        ≤ ‖Complex.exp ((((T2_Delta (k + 1) : ℝ)) : ℂ) * Complex.I)
          - Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I)‖ *
          (‖Complex.exp ((((T2_Delta k : ℝ)) : ℂ) * Complex.I) - 1‖ *
            ‖Complex.exp ((((T2_Delta (k + 1) : ℝ)) : ℂ) * Complex.I) - 1‖) := by
      apply mul_le_mul_of_nonneg_left hden_ge (norm_nonneg _)
    linarith [hle]
  have hfield : (17.5 : ℝ) * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 3))
      = 35 / (((k : ℝ) + 1) * ((k : ℝ) + 3)) := by
    have hk1ne : ((k : ℝ) + 1) ≠ 0 := ne_of_gt hkR
    have hk3ne : ((k : ℝ) + 3) ≠ 0 := ne_of_gt hkR3
    field_simp
    ring_nf
  linarith [hnum_le, hdiv_le, hfield]

set_option maxHeartbeats 800000 in
/-- (G) Total weight TV over `[1024,2048)` is `≤ 1/25`. -/
theorem T2_w_TV_total :
    ∑ k ∈ Finset.Ico 1024 2048, ‖T2_w (k + 1) - T2_w k‖ ≤ 1 / 25 := by
  have hper : ∀ k ∈ Finset.Ico 1024 2048, ‖T2_w (k + 1) - T2_w k‖ ≤ 35 / (1024 * 1024 : ℝ) := by
    intro k hk
    have hk1 : 1024 ≤ k := (Finset.mem_Ico.mp hk).1
    have hle := T2_w_diff_le hk1
    have hkR1 : (1024 : ℝ) ≤ (k : ℝ) + 1 := by
      have hle2 : ((((1024 : ℕ)) : ℝ)) ≤ (k : ℝ) := Nat.cast_le.mpr hk1
      have e1024 : (1024 : ℝ) = ((((1024 : ℕ)) : ℝ)) := by norm_cast
      rw [e1024]
      linarith
    have hkR3 : (1024 : ℝ) ≤ (k : ℝ) + 3 := by linarith
    have hden_ge : (1024 * 1024 : ℝ) ≤ ((k : ℝ) + 1) * ((k : ℝ) + 3) := by
      have h1 : (1024 : ℝ) * 1024 ≤ ((k : ℝ) + 1) * ((k : ℝ) + 3) :=
        mul_le_mul hkR1 hkR3 (by norm_num) (by linarith)
      linarith [h1]
    have hpos1 : (0 : ℝ) < ((k : ℝ) + 1) * ((k : ℝ) + 3) := by positivity
    have h1div : (1 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 3)) ≤ 1 / (1024 * 1024 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hden_ge
    have h35 : (35 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 3)) ≤ 35 / (1024 * 1024 : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left h1div (by norm_num : (0 : ℝ) ≤ 35)
      rw [mul_one_div, mul_one_div] at hmul
      exact hmul
    linarith [hle, h35]
  calc ∑ k ∈ Finset.Ico 1024 2048, ‖T2_w (k + 1) - T2_w k‖
      ≤ ∑ _k ∈ Finset.Ico 1024 2048, (35 / (1024 * 1024 : ℝ)) :=
        Finset.sum_le_sum hper
    _ ≤ 1 / 25 := by
        rw [Finset.sum_const, Nat.card_Ico]
        norm_num [nsmul_eq_mul]

#print axioms T2_abel_eq
#print axioms T2_abel_norm
#print axioms T2_alt_le_one
#print axioms T2_pow1024_one
#print axioms T2_shifted_alt_eq
#print axioms T2_shifted_alt_le
#print axioms T2_gap_upper
#print axioms T2_gap_lower
#print axioms T2_gap_nonneg
#print axioms T2_gap_abs_diff_le
#print axioms T2_AE_f
#print axioms T2_AE_eta_eq
#print axioms T2_AE_f_norm
#print axioms T2_AE_f_le
#print axioms T2_cpow_diff_le
#print axioms T2_AE_f_diff_le
#print axioms T2_block_upper
#print axioms T2_Delta
#print axioms T2_w
#print axioms T2_denom_ge_one
#print axioms T2_w_sup
#print axioms T2_exp_lipschitz
#print axioms T2_w_diff_le
#print axioms T2_w_TV_total

/-!
## Door-3 early-block interval framework (D3): per-term cpow enclosure + block-sum lower + first blocks.

GOAL (door-3 closure premise, toward AE `zeta_S1_lower_of_S2048` with `s1 = 1 - s0`,
`σ = 0.605`, `t = 8.75`): LOWER-bound technology for the early partial sum `S_{1024}(s1)`
via rigorous complex interval arithmetic. AM Tier-2 gives second-half block UPPER `≤ 1/5`
(`T2_block_upper`), so a LOWER on `S_{2048}` follows from `‖S_{1024}‖ ≥ 8/15 ≈ 0.533`
(true `≈ 0.565`, margin `≈ 0.032`). Pair-absolute/Tendsto forms only; no `∑'`-with-`0 <`.

GREP-FIRST RECORD (run before writing; repo `zeta_rigorous.lean` + `Mathlib/`):
* `Real.cos_le` (bare) -- ABSENT (no such theorem; verified by grep `theorem cos_le\\b` → 0 hits).
  Do NOT cite it. What EXISTS (`Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean`):
  `Real.one_sub_sq_div_two_le_cos` (`1 - x^2/2 ≤ cos x`), `Real.sin_ge_sub_cube`
  (`0 ≤ x → x - x^3/6 ≤ sin x`), `Real.sin_le` (`0 ≤ x → sin x ≤ x`), `Real.sin_lt`,
  `Real.cos_le_one_sub_mul_cos_sq` (`|x| ≤ π → cos x ≤ 1 - 2/π^2·x^2`),
  `Real.abs_cos_sub_cos_le`/`abs_sin_sub_sin_le` (Lipschitz 1), `Real.cos_mem_Icc`/
  `Real.sin_mem_Icc` (`∈ Icc (-1) 1`), `Real.cos_sub_two_pi`/`Real.sin_sub_two_pi`,
  `Real.cos_neg`/`Real.sin_neg` (all in `Basic.lean`, verified).
* `Real.sin_bounds` / interval-Taylor material -- ABSENT as a named bundle (grep
  `sin_bounds|interval.*Taylor` → 0 hits). Built below from the cubic/quadratic lemmas above.
* `Real.log_two_gt_d9`/`lt_d9` (`0.6931471803 < log 2 < 0.6931471808`),
  `Real.log_three_gt_d9`/`lt_d9`, `Real.log_five_gt_d9`/`lt_d9`, `Real.log_four_eq`
  (`Mathlib/Analysis/Complex/ExponentialBounds.lean:71-127`, namespace `Real`) -- EXIST,
  consumed for `θ₂ = 8.75·log 2`. `Real.pi_gt_d2`/`lt_d2` (`3.14 < π < 3.15`),
  `Real.pi_gt_d4`/`lt_d4` (`Bounds.lean`) -- EXIST, consumed for `2π` reduction.
* `Complex.cpow_def_of_ne_zero` (`Pow/Complex.lean:38`), `Complex.ofReal_log`
  (`Complex/Log.lean:71`), `Complex.exp_re`/`exp_im` (`Complex/Trigonometric.lean:519/523`),
  `Complex.ofReal_pow`/`ofReal_re`/`ofReal_im`/`ofReal_ne_zero` (`Data/Complex/Basic.lean`),
  `Real.rpow_def_of_pos` -- all EXIST, consumed for `D3_cpow_re`/`im` (no cpow API recreated).
* `etaDirichletTerm_eq_cpow_neg`, `etaDirichletTerm_S1refl_zero`, `zetaCellS0_re`/`im`,
  `zetaRefl_rpow_0605_ge` (`3/2 ≤ 2^0.605`), `T2_AE_f_norm` (norm pattern), `T2_block_upper`
  (`≤ 1/5`) -- all in this file (read-only reuse). No `zetaRefl*`/`Azeta1` redefined.
* Name-clash check (`D3_amp|D3_phase|D3_cpow|D3_eta|D3_S|D3_theta|D3_delta|D3_cos|D3_sin|D3_term|D3_need|D3_block|D3_sum|D3_neg`) -- 0 hits before writing.

WHAT IS PROVED (all unconditional, FULL proofs, no `sorry`/`admit`/`axiom`):
* (F1) Per-term cpow enclosure: `D3_cpow_re`/`D3_cpow_im`
  (`(↑x^(-s1)).re = x^{-0.605}·cos(8.75·log x)`, `.im = -(x^{-0.605}·sin(...))`),
  `D3_neg_one_pow_re`/`im`, `D3_eta_re`/`D3_eta_im` (with `(-1)^k` factor).
* (F2) Block-sum lower lemma: `D3_sum_re_eq` + `D3_block_norm_ge_sum_lo`
  (`∑ lo ≤ ‖∑ eta‖` from per-term `lo ≤ Re`), `D3_S1024_split_lower`
  (`L - U ≤ ‖S_{1024}‖` from `‖S_K‖ ≥ L`, `‖mid‖ ≤ U` via `sum_range_add_sum_Ico`).
* (C) Concrete first blocks (green): `D3_amp_one`/`D3_phase_zero` (k=0 exact),
  `D3_amp_two_upper` (`≤ 2/3` from `zetaRefl_rpow_0605_ge`) + `D3_amp_two_lower`
  (`≥ 5/8` via `2^{2/3} ≤ 8/5`), `D3_phase_one_eq` + `D3_theta_two_lo`/`hi`
  (`θ₂ ∈ [6.065, 6.066]` from `log_two_d9`), `D3_delta_two_mem`
  (`θ₂ - 2π ∈ [-0.24, -0.21]` from `pi_d2`), `D3_cos_theta_two_lower` (`≥ 0.97`
  via quadratic) + `D3_cos_theta_two_le_one`, `D3_sin_theta_two_mem`
  (`∈ [-0.24, -0.20]` via cubic/linear), `D3_term1_re_lo` (`≥ -2/3`),
  `D3_S2_re_lower`/`D3_S2_norm_ge` (`≥ 1/3` via framework, cross-checks
  `etaDirichlet_S1refl_two_norm_ge`), `D3_S1_norm_ge` (`≥ 8/15` for `S_1`).
* (P) Path arithmetic (honest negatives): `D3_S1024_of_S2` (`1/3 - U ≤ ‖S₁₀₂₄‖`),
  `D3_S2_cannot_reach_8_15` (`1/3 - U < 8/15` for all `U ≥ 0`), `D3_S1024_of_S1`
  (`1 - U ≤ ‖S₁₀₂₄‖`, needs `U ≤ 7/15`), `D3_need_from_S1`/`D3_need_from_S2`.

NUMBERS (exact, proved in-file; python scratch only for the report):
* `θ₂ = 8.75·log 2 ∈ [6.065, 6.066]` (true `≈ 6.06504`); `δ₂ = θ₂ - 2π ∈ [-0.24, -0.21]`
  (true `≈ -0.21815`); `cos θ₂ ≥ 0.97` (true `≈ 0.97629`); `sin θ₂ ∈ [-0.24, -0.20]`
  (true `≈ -0.21655`); `2^{-0.605} ∈ [0.625, 0.667]` (true `≈ 0.65775`).
* `S_1 = 1 ≥ 8/15`; `S_2 ≥ 1/3` via intervals (matches direct reverse-triangle).
* True values (non-rigorous scratch): `|S_1|=1.0`, `|S_2|≈0.385`, `|S_4|≈0.586`,
  `|S_8|≈0.674`, `|S_16|≈0.652`, `|S_32|≈0.624`, `|S_1024|≈0.56507`,
  `|S_2048|≈0.56312`, `|block[1024,2048)|≈0.0029` (vs proved `≤ 0.2`),
  `|block[1,1024)|≈1.4016`, `|block[2,1024)|≈0.7529`, `|block[4,1024)|≈0.3195`,
  `|block[8,1024)|≈0.1602`, `|block[16,1024)|≈0.0953`.

RESIDUAL (exact, quantified -- report-and-stop, no spin):
* `‖S_{1024}‖ ≥ 8/15` is STILL OPEN. From `S_2 ≥ 1/3`, splitting needs
  `‖mid[2,1024)‖ ≤ 1/3 - 8/15 = -1/5 < 0`, IMPOSSIBLE for any `U ≥ 0`
  (`D3_S2_cannot_reach_8_15`). From `S_1 = 1`, needs `‖mid[1,1024)‖ ≤ 7/15 ≈ 0.467`,
  but true `≈ 1.4016` already exceeds it, so the `K = 1` route is dead exactly.
  True-margin table: `K=4`: `0.586 - 0.320 = 0.266 < 0.533` (dead exactly);
  `K=8`: `0.674 - 0.160 = 0.514 < 0.533` (fails by `0.019` exactly);
  `K=16`: `0.652 - 0.095 = 0.557 ≥ 0.533` (first feasible `K`, margin `0.024`);
  `K=32`: `0.625 - 0.059 = 0.565 ≥ 0.533` (margin `0.031`).
  Hence the path needs either (i) interval enclosures for `cos/sin(8.75·log n)` with
  `log_three`/`log_five` d9 bounds summed block-by-block to `K = 16/32` (same template as
  `θ₂` above, `≈ 16-32` cpow terms, feasible across sessions), PLUS a cancellation-aware
  middle-block UPPER (`≤ 0.12` at `K=16`; triangle gives `≈ 35`, Abel+MVT `≈ 8.6`
  per §18b.10 -- both too loose, needs Tier-3 second-derivative or block-interval uppers),
  or (ii) direct `1024`-term Re-sum intervals. Next session: `θ₃/θ₄` enclosures
  (`log_three_d9`, `log_four_eq`) + `S_4` Re lower via `D3_block_norm_ge_sum_lo`.
-/

/-- (F1) Early-block amplitude `(k+1)^{-0.605}` at `s1`. -/
noncomputable def D3_amp (k : ℕ) : ℝ := (((k : ℝ) + 1) ^ (-0.605 : ℝ))

/-- (F1) Early-block phase `8.75·log(k+1)` at `s1`. -/
noncomputable def D3_phase (k : ℕ) : ℝ := 8.75 * Real.log (((k : ℝ) + 1))

/-- (F1) cpow real part at `s1`: `(↑x^(-s1)).re = x^{-0.605}·cos(8.75·log x)`. -/
theorem D3_cpow_re (x : ℝ) (hx : 0 < x) :
    ((((x : ℂ)) ^ (-(1 - zetaCellS0)))).re = x ^ (-0.605 : ℝ) * Real.cos (8.75 * Real.log x) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log (x : ℂ) = (((Real.log x : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt hx)).symm
  rw [hlog]
  have hre_w : (-(1 - zetaCellS0)).re = (-0.605 : ℝ) := by
    rw [Complex.neg_re, Complex.sub_re, Complex.one_re, zetaCellS0_re]
    norm_num
  have him_w : (-(1 - zetaCellS0)).im = (-8.75 : ℝ) := by
    rw [Complex.neg_im, Complex.sub_im, Complex.one_im, zetaCellS0_im]
    norm_num
  have hzre : ((((Real.log x : ℝ)) : ℂ)).re = Real.log x := Complex.ofReal_re _
  have hzim : ((((Real.log x : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log x : ℝ)) : ℂ) * (-(1 - zetaCellS0))).re =
      Real.log x * (-0.605) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log x : ℝ)) : ℂ) * (-(1 - zetaCellS0))).im =
      Real.log x * (-8.75) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log x * (-0.605)) = x ^ (-0.605 : ℝ) :=
    (Real.rpow_def_of_pos hx _).symm
  have hcos : Real.cos (Real.log x * (-8.75)) = Real.cos (8.75 * Real.log x) := by
    have e : Real.log x * (-8.75) = -(8.75 * Real.log x) := by ring
    rw [e, Real.cos_neg]
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- (F1) cpow imaginary part at `s1`. -/
theorem D3_cpow_im (x : ℝ) (hx : 0 < x) :
    ((((x : ℂ)) ^ (-(1 - zetaCellS0)))).im =
      -(x ^ (-0.605 : ℝ) * Real.sin (8.75 * Real.log x)) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log (x : ℂ) = (((Real.log x : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt hx)).symm
  rw [hlog]
  have hre_w : (-(1 - zetaCellS0)).re = (-0.605 : ℝ) := by
    rw [Complex.neg_re, Complex.sub_re, Complex.one_re, zetaCellS0_re]
    norm_num
  have him_w : (-(1 - zetaCellS0)).im = (-8.75 : ℝ) := by
    rw [Complex.neg_im, Complex.sub_im, Complex.one_im, zetaCellS0_im]
    norm_num
  have hzre : ((((Real.log x : ℝ)) : ℂ)).re = Real.log x := Complex.ofReal_re _
  have hzim : ((((Real.log x : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log x : ℝ)) : ℂ) * (-(1 - zetaCellS0))).re =
      Real.log x * (-0.605) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log x : ℝ)) : ℂ) * (-(1 - zetaCellS0))).im =
      Real.log x * (-8.75) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log x * (-0.605)) = x ^ (-0.605 : ℝ) :=
    (Real.rpow_def_of_pos hx _).symm
  have hsin : Real.sin (Real.log x * (-8.75)) = -Real.sin (8.75 * Real.log x) := by
    have e : Real.log x * (-8.75) = -(8.75 * Real.log x) := by ring
    rw [e, Real.sin_neg]
  rw [Complex.exp_im, harg_re, harg_im, hexp, hsin]
  ring

/-- (F1) `((-1)^k).re`. -/
theorem D3_neg_one_pow_re (k : ℕ) : ((-1 : ℂ) ^ k).re = (-1 : ℝ) ^ k := by
  have h : (-1 : ℂ) = (((-1 : ℝ)) : ℂ) := by norm_cast
  rw [h, ← Complex.ofReal_pow, Complex.ofReal_re]

/-- (F1) `((-1)^k).im`. -/
theorem D3_neg_one_pow_im (k : ℕ) : ((-1 : ℂ) ^ k).im = 0 := by
  have h : (-1 : ℂ) = (((-1 : ℝ)) : ℂ) := by norm_cast
  rw [h, ← Complex.ofReal_pow, Complex.ofReal_im]

/-- (F1) Dirichlet-eta term real part at `s1`. -/
theorem D3_eta_re (k : ℕ) :
    (etaDirichletTerm (1 - zetaCellS0) k).re =
      (-1 : ℝ) ^ k * (D3_amp k * Real.cos (D3_phase k)) := by
  rw [etaDirichletTerm_eq_cpow_neg]
  have hx : (0 : ℝ) < (k : ℝ) + 1 := by
    have h := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hcr := D3_cpow_re ((k : ℝ) + 1) hx
  rw [Complex.mul_re, D3_neg_one_pow_re, D3_neg_one_pow_im, hcr]
  unfold D3_amp D3_phase
  ring

/-- (F1) Dirichlet-eta term imaginary part at `s1`. -/
theorem D3_eta_im (k : ℕ) :
    (etaDirichletTerm (1 - zetaCellS0) k).im =
      (-1 : ℝ) ^ k * (-(D3_amp k * Real.sin (D3_phase k))) := by
  rw [etaDirichletTerm_eq_cpow_neg]
  have hx : (0 : ℝ) < (k : ℝ) + 1 := by
    have h := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hci := D3_cpow_im ((k : ℝ) + 1) hx
  rw [Complex.mul_im, D3_neg_one_pow_re, D3_neg_one_pow_im, hci]
  unfold D3_amp D3_phase
  ring

/-- (F2) Real part of a `Finset.range` sum. -/
theorem D3_sum_re_eq (N : ℕ) (f : ℕ → ℂ) :
    (∑ k ∈ Finset.range N, f k).re = ∑ k ∈ Finset.range N, (f k).re := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, Complex.add_re, ih]

/-- (F2) Block-sum LOWER from per-term real-part lowers. -/
theorem D3_block_norm_ge_sum_lo (N : ℕ) (lo : ℕ → ℝ)
    (hlo : ∀ k, k < N → lo k ≤ (etaDirichletTerm (1 - zetaCellS0) k).re) :
    ∑ k ∈ Finset.range N, lo k ≤
      ‖∑ k ∈ Finset.range N, etaDirichletTerm (1 - zetaCellS0) k‖ := by
  have hsum_le : ∑ k ∈ Finset.range N, lo k ≤
      (∑ k ∈ Finset.range N, etaDirichletTerm (1 - zetaCellS0) k).re := by
    rw [D3_sum_re_eq]
    exact Finset.sum_le_sum (fun k hk => hlo k (Finset.mem_range.mp hk))
  calc ∑ k ∈ Finset.range N, lo k
      ≤ (∑ k ∈ Finset.range N, etaDirichletTerm (1 - zetaCellS0) k).re := hsum_le
    _ ≤ |(∑ k ∈ Finset.range N, etaDirichletTerm (1 - zetaCellS0) k).re| :=
        le_abs_self _
    _ ≤ ‖∑ k ∈ Finset.range N, etaDirichletTerm (1 - zetaCellS0) k‖ :=
        Complex.abs_re_le_norm _

/-- (F2) `S_{1024}` lower from a head lower `L` and a middle upper `U`. -/
theorem D3_S1024_split_lower (K : ℕ) (hK : K ≤ 1024) (L U : ℝ)
    (hL : L ≤ ‖∑ k ∈ Finset.range K, etaDirichletTerm (1 - zetaCellS0) k‖)
    (hU : ‖∑ k ∈ Finset.Ico K 1024, etaDirichletTerm (1 - zetaCellS0) k‖ ≤ U) :
    L - U ≤ ‖∑ k ∈ Finset.range 1024, etaDirichletTerm (1 - zetaCellS0) k‖ := by
  have hsplit : (∑ k ∈ Finset.range K, etaDirichletTerm (1 - zetaCellS0) k) +
      (∑ k ∈ Finset.Ico K 1024, etaDirichletTerm (1 - zetaCellS0) k) =
      ∑ k ∈ Finset.range 1024, etaDirichletTerm (1 - zetaCellS0) k :=
    Finset.sum_range_add_sum_Ico _ hK
  have htri : ‖∑ k ∈ Finset.range K, etaDirichletTerm (1 - zetaCellS0) k‖ ≤
      ‖∑ k ∈ Finset.range 1024, etaDirichletTerm (1 - zetaCellS0) k‖ +
      ‖∑ k ∈ Finset.Ico K 1024, etaDirichletTerm (1 - zetaCellS0) k‖ := by
    have heq : (∑ k ∈ Finset.range K, etaDirichletTerm (1 - zetaCellS0) k) =
        (∑ k ∈ Finset.range 1024, etaDirichletTerm (1 - zetaCellS0) k) -
        (∑ k ∈ Finset.Ico K 1024, etaDirichletTerm (1 - zetaCellS0) k) := by
      rw [← hsplit]
      ring
    rw [heq]
    exact norm_sub_le _ _
  linarith

/-- (C) `D3_amp 0 = 1`. -/
theorem D3_amp_one : D3_amp 0 = 1 := by
  unfold D3_amp
  have h : ((((0 : ℕ)) : ℝ) + 1 : ℝ) = 1 := by norm_num
  rw [h, Real.one_rpow]

/-- (C) `D3_phase 0 = 0`. -/
theorem D3_phase_zero : D3_phase 0 = 0 := by
  unfold D3_phase
  have h : ((((0 : ℕ)) : ℝ) + 1 : ℝ) = 1 := by norm_num
  rw [h, Real.log_one, mul_zero]

/-- (C) `D3_amp` is nonneg. -/
theorem D3_amp_nonneg (k : ℕ) : 0 ≤ D3_amp k := by
  unfold D3_amp
  have hnn : (0 : ℝ) ≤ (k : ℝ) + 1 := by
    have h := Nat.cast_nonneg (α := ℝ) k
    linarith
  exact Real.rpow_nonneg hnn _

/-- (C) Head amplitude upper `D3_amp 1 ≤ 2/3` (from `zetaRefl_rpow_0605_ge`). -/
theorem D3_amp_two_upper : D3_amp 1 ≤ 2 / 3 := by
  unfold D3_amp
  have hcast : ((((1 : ℕ)) : ℝ) + 1 : ℝ) = 2 := by norm_num
  rw [hcast]
  have hge := zetaRefl_rpow_0605_ge
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have e : (-0.605 : ℝ) = -(0.605 : ℝ) := by norm_num
  rw [e, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have heq : (2 / 3 : ℝ) = ((3 / 2 : ℝ))⁻¹ := by norm_num
  rw [heq]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

set_option maxHeartbeats 800000 in
/-- (C) Head amplitude lower `5/8 ≤ D3_amp 1` (via `2^{2/3} ≤ 8/5`). -/
theorem D3_amp_two_lower : 5 / 8 ≤ D3_amp 1 := by
  unfold D3_amp
  have hcast : ((((1 : ℕ)) : ℝ) + 1 : ℝ) = 2 := by norm_num
  rw [hcast]
  have hle_exp : (0.605 : ℝ) ≤ 2 / 3 := by norm_num
  have hmono : (2 : ℝ) ^ (0.605 : ℝ) ≤ (2 : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hle_exp
  have hcube_eq : (((2 : ℝ) ^ (2 / 3 : ℝ)) ^ (3 : ℕ)) = 4 := by
    have h1 : (((2 : ℝ) ^ (2 / 3 : ℝ)) ^ (3 : ℕ)) =
        (2 : ℝ) ^ ((2 / 3 : ℝ) * (((3 : ℕ)) : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [h1]
    have hexp : (2 / 3 : ℝ) * (((3 : ℕ)) : ℝ) = ((((2 : ℕ)) : ℝ)) := by norm_num
    rw [hexp, Real.rpow_natCast]
    norm_num
  have hpow_le : (((2 : ℝ) ^ (2 / 3 : ℝ)) ^ (3 : ℕ)) ≤ (((8 / 5 : ℝ)) ^ (3 : ℕ)) := by
    rw [hcube_eq]
    norm_num
  have h23 : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 8 / 5 :=
    le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) (by norm_num : (0 : ℝ) ≤ 8 / 5) hpow_le
  have h26 : (2 : ℝ) ^ (0.605 : ℝ) ≤ 8 / 5 := le_trans hmono h23
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have e : (-0.605 : ℝ) = -(0.605 : ℝ) := by norm_num
  rw [e, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have heq : (5 / 8 : ℝ) = ((8 / 5 : ℝ))⁻¹ := by norm_num
  rw [heq]
  exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 8 / 5) hpos).mpr h26

/-- (C) `D3_phase 1 = 8.75·log 2`. -/
theorem D3_phase_one_eq : D3_phase 1 = 8.75 * Real.log 2 := by
  unfold D3_phase
  have h : ((((1 : ℕ)) : ℝ) + 1 : ℝ) = 2 := by norm_num
  rw [h]

/-- (C) Phase lower `6.065 ≤ θ₂` (from `log_two_gt_d9`). -/
theorem D3_theta_two_lo : 6.065 ≤ D3_phase 1 := by
  rw [D3_phase_one_eq]
  have hlog := Real.log_two_gt_d9
  have hmul := mul_lt_mul_of_pos_left hlog (by norm_num : (0 : ℝ) < 8.75)
  have hnum : (6.065 : ℝ) ≤ 8.75 * 0.6931471803 := by norm_num
  linarith

/-- (C) Phase upper `θ₂ ≤ 6.066` (from `log_two_lt_d9`). -/
theorem D3_theta_two_hi : D3_phase 1 ≤ 6.066 := by
  rw [D3_phase_one_eq]
  have hlog := Real.log_two_lt_d9
  have hmul := mul_lt_mul_of_pos_left hlog (by norm_num : (0 : ℝ) < 8.75)
  have hnum : 8.75 * 0.6931471808 ≤ (6.066 : ℝ) := by norm_num
  linarith

/-- (C) Reduced phase `θ₂ - 2π ∈ [-0.24, -0.21]` (from `pi_d2`). -/
theorem D3_delta_two_mem :
    -0.24 ≤ D3_phase 1 - 2 * Real.pi ∧ D3_phase 1 - 2 * Real.pi ≤ -0.21 := by
  have hth_lo := D3_theta_two_lo
  have hth_hi := D3_theta_two_hi
  have hpi_lo := Real.pi_gt_d2
  have hpi_hi := Real.pi_lt_d2
  constructor <;> linarith

/-- (C) Trivial cosine upper `cos θ₂ ≤ 1`. -/
theorem D3_cos_theta_two_le_one : Real.cos (D3_phase 1) ≤ 1 :=
  (Real.cos_mem_Icc _).2

set_option maxHeartbeats 800000 in
/-- (C) Cosine lower `0.97 ≤ cos θ₂` (periodicity + quadratic `1 - y²/2`). -/
theorem D3_cos_theta_two_lower : 0.97 ≤ Real.cos (D3_phase 1) := by
  have hmem := D3_delta_two_mem
  have h1 : Real.cos (D3_phase 1 - 2 * Real.pi) = Real.cos (D3_phase 1) :=
    Real.cos_sub_two_pi _
  have h2 : Real.cos (D3_phase 1 - 2 * Real.pi) =
      Real.cos (2 * Real.pi - D3_phase 1) := by
    have e : D3_phase 1 - 2 * Real.pi = -((2 * Real.pi - D3_phase 1)) := by ring
    rw [e, Real.cos_neg]
  have hcos_eq : Real.cos (D3_phase 1) = Real.cos (2 * Real.pi - D3_phase 1) := by
    rw [← h1, h2]
  rw [hcos_eq]
  have hy_lo : (0.21 : ℝ) ≤ 2 * Real.pi - D3_phase 1 := by linarith [hmem.2]
  have hy_hi : 2 * Real.pi - D3_phase 1 ≤ (0.24 : ℝ) := by linarith [hmem.1]
  have hy_nn : (0 : ℝ) ≤ 2 * Real.pi - D3_phase 1 := by linarith
  have hsq : (2 * Real.pi - D3_phase 1) ^ 2 ≤ (0.24 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hy_nn hy_hi 2
  have hcos_lo := Real.one_sub_sq_div_two_le_cos
    (x := 2 * Real.pi - D3_phase 1)
  have hnum : (0.97 : ℝ) ≤ 1 - (0.24 : ℝ) ^ 2 / 2 := by norm_num
  have hle : 1 - (0.24 : ℝ) ^ 2 / 2 ≤
      1 - (2 * Real.pi - D3_phase 1) ^ 2 / 2 := by linarith [hsq]
  linarith [hcos_lo, hle, hnum]

set_option maxHeartbeats 800000 in
/-- (C) Sine enclosure `sin θ₂ ∈ [-0.24, -0.20]` (periodicity + cubic/linear). -/
theorem D3_sin_theta_two_mem :
    -0.24 ≤ Real.sin (D3_phase 1) ∧ Real.sin (D3_phase 1) ≤ -0.20 := by
  have hmem := D3_delta_two_mem
  have h1s : Real.sin (D3_phase 1 - 2 * Real.pi) = Real.sin (D3_phase 1) :=
    Real.sin_sub_two_pi _
  have h2s : Real.sin (D3_phase 1 - 2 * Real.pi) =
      -Real.sin (2 * Real.pi - D3_phase 1) := by
    have e : D3_phase 1 - 2 * Real.pi = -((2 * Real.pi - D3_phase 1)) := by ring
    rw [e, Real.sin_neg]
  have hsin_eq : Real.sin (D3_phase 1) =
      -Real.sin (2 * Real.pi - D3_phase 1) := by
    rw [← h1s, h2s]
  rw [hsin_eq]
  have hy_lo : (0.21 : ℝ) ≤ 2 * Real.pi - D3_phase 1 := by linarith [hmem.2]
  have hy_hi : 2 * Real.pi - D3_phase 1 ≤ (0.24 : ℝ) := by linarith [hmem.1]
  have hy_nn : (0 : ℝ) ≤ 2 * Real.pi - D3_phase 1 := by linarith
  have hsin_lo := Real.sin_ge_sub_cube hy_nn
  have hsin_hi := Real.sin_le hy_nn
  have hcube : (2 * Real.pi - D3_phase 1) ^ 3 ≤ (0.24 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hy_nn hy_hi 3
  have hnum : (0.20 : ℝ) ≤ (0.21 : ℝ) - (0.24 : ℝ) ^ 3 / 6 := by norm_num
  have hlo : (0.20 : ℝ) ≤ Real.sin (2 * Real.pi - D3_phase 1) := by
    have h1 : (0.21 : ℝ) - (0.24 : ℝ) ^ 3 / 6 ≤
        (2 * Real.pi - D3_phase 1) - (2 * Real.pi - D3_phase 1) ^ 3 / 6 := by
      linarith [hy_lo, hcube]
    linarith [hsin_lo, h1, hnum]
  have hhi : Real.sin (2 * Real.pi - D3_phase 1) ≤ (0.24 : ℝ) := by
    linarith [hsin_hi, hy_hi]
  constructor <;> linarith [hlo, hhi]

/-- (C) Second-term real-part lower `≥ -2/3` (interval: `amp ≤ 2/3`, `cos ≤ 1`). -/
theorem D3_term1_re_lo :
    (-2 / 3 : ℝ) ≤ (etaDirichletTerm (1 - zetaCellS0) 1).re := by
  rw [D3_eta_re]
  have hamp := D3_amp_two_upper
  have hcos_le := D3_cos_theta_two_le_one
  have hcos_nn : (0 : ℝ) ≤ Real.cos (D3_phase 1) := by
    linarith [D3_cos_theta_two_lower]
  have hamp_nn : (0 : ℝ) ≤ D3_amp 1 := D3_amp_nonneg 1
  have hprod : D3_amp 1 * Real.cos (D3_phase 1) ≤ 2 / 3 := by
    have h := mul_le_mul hamp hcos_le hcos_nn (by norm_num : (0 : ℝ) ≤ 2 / 3)
    have e : (2 / 3 : ℝ) * 1 = 2 / 3 := by ring
    rw [e] at h
    exact h
  have hpow1 : ((-1 : ℝ) ^ (1 : ℕ)) = -1 := pow_one _
  rw [hpow1]
  linarith [hprod]

/-- (C) `k = 0` term real part is `1`. -/
theorem D3_term0_re : (etaDirichletTerm (1 - zetaCellS0) 0).re = 1 := by
  rw [etaDirichletTerm_S1refl_zero, Complex.one_re]

/-- (C) `S_2` real-part lower `≥ 1/3` via the interval framework. -/
theorem D3_S2_re_lower :
    (1 / 3 : ℝ) ≤
      (∑ k ∈ Finset.range 2, etaDirichletTerm (1 - zetaCellS0) k).re := by
  rw [D3_sum_re_eq]
  have h2 : (∑ k ∈ Finset.range 2, (etaDirichletTerm (1 - zetaCellS0) k).re) =
      (etaDirichletTerm (1 - zetaCellS0) 0).re +
      (etaDirichletTerm (1 - zetaCellS0) 1).re := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [h2, D3_term0_re]
  linarith [D3_term1_re_lo]

/-- (C) `S_2` norm lower `≥ 1/3` via the interval framework. -/
theorem D3_S2_norm_ge :
    (1 / 3 : ℝ) ≤
      ‖∑ k ∈ Finset.range 2, etaDirichletTerm (1 - zetaCellS0) k‖ := by
  calc (1 / 3 : ℝ)
      ≤ (∑ k ∈ Finset.range 2, etaDirichletTerm (1 - zetaCellS0) k).re :=
        D3_S2_re_lower
    _ ≤ |(∑ k ∈ Finset.range 2, etaDirichletTerm (1 - zetaCellS0) k).re| :=
        le_abs_self _
    _ ≤ ‖∑ k ∈ Finset.range 2, etaDirichletTerm (1 - zetaCellS0) k‖ :=
        Complex.abs_re_le_norm _

/-- (C) `S_1` norm `≥ 8/15` (first block green; `S_1 = 1`). -/
theorem D3_S1_norm_ge :
    (8 / 15 : ℝ) ≤
      ‖∑ k ∈ Finset.range 1, etaDirichletTerm (1 - zetaCellS0) k‖ := by
  have h : (∑ k ∈ Finset.range 1, etaDirichletTerm (1 - zetaCellS0) k) = 1 := by
    rw [Finset.sum_range_one, etaDirichletTerm_S1refl_zero]
  rw [h, norm_one]
  norm_num

/-- (P) `S_{1024}` conditional from the `S_2` interval lower. -/
theorem D3_S1024_of_S2 (U : ℝ)
    (hU : ‖∑ k ∈ Finset.Ico 2 1024, etaDirichletTerm (1 - zetaCellS0) k‖ ≤ U) :
    (1 / 3 - U : ℝ) ≤
      ‖∑ k ∈ Finset.range 1024, etaDirichletTerm (1 - zetaCellS0) k‖ :=
  D3_S1024_split_lower 2 (by norm_num) (1 / 3) U D3_S2_norm_ge hU

/-- (P) The `S_2` route CANNOT reach `8/15` via splitting (needs `U ≤ -1/5`). -/
theorem D3_S2_cannot_reach_8_15 (U : ℝ) (hU : 0 ≤ U) :
    (1 / 3 - U : ℝ) < 8 / 15 := by
  have h : (1 / 3 : ℝ) < 8 / 15 := by norm_num
  linarith

/-- (P) `S_{1024}` conditional from the `S_1` block. -/
theorem D3_S1024_of_S1 (U : ℝ)
    (hU : ‖∑ k ∈ Finset.Ico 1 1024, etaDirichletTerm (1 - zetaCellS0) k‖ ≤ U) :
    (1 - U : ℝ) ≤
      ‖∑ k ∈ Finset.range 1024, etaDirichletTerm (1 - zetaCellS0) k‖ := by
  have hL : (1 : ℝ) ≤
      ‖∑ k ∈ Finset.range 1, etaDirichletTerm (1 - zetaCellS0) k‖ := by
    rw [Finset.sum_range_one, etaDirichletTerm_S1refl_zero, norm_one]
  exact D3_S1024_split_lower 1 (by norm_num) 1 U hL hU

/-- (P) Arithmetic needs: `1 - 8/15 = 7/15`, `1/3 - 8/15 = -1/5`. -/
theorem D3_need_from_S1 : ((1 : ℝ) - 8 / 15) = 7 / 15 := by norm_num

/-- (P) Arithmetic needs: `S_2` side. -/
theorem D3_need_from_S2 : ((1 / 3 : ℝ) - 8 / 15) = -1 / 5 := by norm_num

#print axioms D3_cpow_re
#print axioms D3_cpow_im
#print axioms D3_neg_one_pow_re
#print axioms D3_neg_one_pow_im
#print axioms D3_eta_re
#print axioms D3_eta_im
#print axioms D3_sum_re_eq
#print axioms D3_block_norm_ge_sum_lo
#print axioms D3_S1024_split_lower
#print axioms D3_amp_one
#print axioms D3_phase_zero
#print axioms D3_amp_nonneg
#print axioms D3_amp_two_upper
#print axioms D3_amp_two_lower
#print axioms D3_phase_one_eq
#print axioms D3_theta_two_lo
#print axioms D3_theta_two_hi
#print axioms D3_delta_two_mem
#print axioms D3_cos_theta_two_le_one
#print axioms D3_cos_theta_two_lower
#print axioms D3_sin_theta_two_mem
#print axioms D3_term1_re_lo
#print axioms D3_term0_re
#print axioms D3_S2_re_lower
#print axioms D3_S2_norm_ge
#print axioms D3_S1_norm_ge
#print axioms D3_S1024_of_S2
#print axioms D3_S2_cannot_reach_8_15
#print axioms D3_S1024_of_S1
#print axioms D3_need_from_S1
#print axioms D3_need_from_S2

/-!
## Door-3 `S_4` interval block (D3, tier 1): `θ₃/θ₄` enclosures + per-term Re lowers + `S_4` sum.

GOAL (tier-1 minimum viable, toward `‖S_{1024}(s1)‖ ≥ 8/15` with `s1 = 1 - s0`,
`σ = 0.605`, `t = 8.75`): extend the D3 early-block interval framework from `S_2`
to `S_4 = ∑ k ∈ range 4` via rigorous per-term cpow enclosures for `k = 2, 3`
(`x = 3, 4`), following the `S_2` template exactly. Pair-absolute/Tendsto forms
only; no `∑'`-with-`0 <` (all sums are `Finset.range`, Re-parts via `D3_sum_re_eq`,
norm via `D3_block_norm_ge_sum_lo`).

GREP-FIRST RECORD (run before writing; repo `zeta_rigorous.lean` + `Mathlib/`):
* `Real.log_three_gt_d9` (`1.0986122885 < log 3`, `:101`) / `Real.log_three_lt_d9`
  (`log 3 < 1.0986122888`, `:104`) / `Real.log_four_eq` (`log 4 = 2 * log 2`, `:107`)
  / `Real.log_two_gt_d9`/`lt_d9` (`:83`/`:86`) — all in
  `Mathlib/Analysis/Complex/ExponentialBounds.lean`, namespace `Real`. EXIST.
* `Real.cos_add_pi` (`cos (x + π) = -cos x`, `Trigonometric/Basic.lean:317`),
  `Real.sin_add_pi` (`:234`), `Real.cos_sub_two_pi` (`:329`),
  `Real.sin_sub_two_pi` (`:246`), `Real.cos_neg`/`Real.sin_neg`,
  `Real.cos_mem_Icc`/`Real.sin_mem_Icc` (`:604`/`:601`) — EXIST (same file/ns as the
  `S_2` template's trig calls).
* `Real.one_sub_sq_div_two_le_cos` (`1 - x^2/2 ≤ cos x`, no hypotheses,
  `Trigonometric/Bounds.lean:123`), `Real.sin_ge_sub_cube` (`0 ≤ x → ...`, `:163`),
  `Real.sin_le` (`0 ≤ x → sin x ≤ x`, `:54`), `Real.pi_gt_d2`/`Real.pi_lt_d2`
  (`3.14 < π < 3.15`, `Real/Pi/Bounds.lean:159/163`) — EXIST.
* `le_of_pow_le_pow_left₀` (`(hn : n ≠ 0) (hb : 0 ≤ b) (h : a^n ≤ b^n) : a ≤ b`,
  `Algebra/Order/GroupWithZero/Basic.lean:702`),
  `Real.rpow_le_rpow_of_exponent_le` (`(hx : 1 ≤ x) (hyz : y ≤ z)`,
  `SpecialFunctions/Pow/Real.lean:615`), `pow_le_pow_left₀`,
  `mul_le_mul_of_nonneg_left`, `mul_le_mul`, `inv_le_inv₀`, `Real.rpow_neg`,
  `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_add`, `Real.rpow_one` — EXIST,
  all already used in this file (`zetaRefl_rpow_0605_ge` `:4434` pattern mirrored).
* In-file reuse (read-only): `D3_amp`/`D3_phase`/`D3_cpow_re`/`D3_eta_re`
  (`:5910`-`:6013`), `D3_sum_re_eq`/`D3_block_norm_ge_sum_lo`/
  `D3_S1024_split_lower` (`:6016`-`:6057`), `D3_amp_nonneg`, `D3_term0_re`,
  `D3_term1_re_lo` (`:6217`), `zetaRefl_rpow_0605_ge` (`:4434`),
  `etaDirichletTerm_S1refl_zero`, `zetaCellS0_re`/`im`. Nothing redefined.
* Name-clash check (`D3_amp_three|D3_amp_four|D3_phase_two|D3_phase_three|D3_theta_three|
  D3_theta_four|D3_delta_three|D3_delta_four|D3_cos_theta_three|D3_sin_theta_three|
  D3_cos_theta_four|D3_sin_theta_four|D3_term2|D3_term3|D3_S4|D3_four_rpow`) — 0 hits.
* No Mathlib numeral bridge (`4^0.605 = 2^1.21`) — created in-file as
  `D3_four_rpow_eq` (documented below).

WHAT IS PROVED (all unconditional, FULL proofs, no `sorry`/`admit`/`axiom`):
* (C) Amplitudes: `D3_four_rpow_eq` (`4^0.605 = 2^1.21`), `D3_amp_three_upper`
  (`≤ 13/25` via `3^{3/5} ≥ 25/13` ⟸ `(25/13)^5 ≤ 27`, `3/5 ≤ 0.605`),
  `D3_amp_three_lower` (`≥ 10/21` via `3^{2/3} ≤ 21/10` ⟸ `9 ≤ (21/10)^3`),
  `D3_amp_four_upper` (`≤ 4/9` via `(2^0.605)^2 ≥ (3/2)^2` from
  `zetaRefl_rpow_0605_ge`), `D3_amp_four_lower` (`≥ 5/12` via `2^{5/4} = 2·2^{1/4}`,
  `(6/5)^4 ≥ 2`, `1.21 ≤ 5/4`).
* (C) Phases: `D3_phase_two_eq`/`D3_phase_three_eq`, `D3_theta_three_lo`/`hi`
  (`θ₃ ∈ [9.612, 9.613]` from `log_three_d9`), `D3_theta_four_lo`/`hi`
  (`θ₄ ∈ [12.130, 12.131]` via `log_four_eq` + `log_two_d9`, `17.5·log 2` shape).
* (C) Reduction + trig: `D3_delta_three_mem` (`θ₃ - 2π ∈ [3.312, 3.333]`),
  `D3_delta_four_mem` (`4π - θ₄ ∈ [0.429, 0.470]`, i.e. `2π - (θ₄ - 2π)`),
  `D3_cos_theta_three_upper` (`≤ -0.98` via `cos_add_pi` + quadratic, `y ≤ 0.20`),
  `D3_cos_theta_three_lower` (`≥ -1`), `D3_sin_theta_three_mem` (`∈ [-0.20, -0.15]`
  via `sin_add_pi` + cubic/linear), `D3_cos_theta_four_lower` (`≥ 0.88` via
  quadratic, `w ≤ 0.470`), `D3_cos_theta_four_le_one`, `D3_sin_theta_four_mem`
  (`∈ [-0.47, -0.41]`).
* (F2) Terms + sum: `D3_term2_re_lo` (`≥ -3/5`: `amp·cos ≥ -amp ≥ -13/25 ≥ -3/5`
  using only `cos ≥ -1` + amp upper), `D3_term3_re_lo` (`≥ -1/2`:
  `-(amp·cos) ≥ -4/9 ≥ -1/2` using only `cos ≤ 1` + amp upper), `D3_S4_re_lower`
  (`≥ -23/30` by `sum_range_succ` expansion à la `D3_S2_re_lower`),
  `D3_S4_lo`/`D3_S4_lo_sum`/`D3_S4_lo_valid` + `D3_S4_norm_ge` (`≥ -23/30` through
  `D3_block_norm_ge_sum_lo`), `D3_S1024_of_S4` + `D3_S4_cannot_reach_8_15`
  (mirroring `D3_S1024_of_S1`/`D3_S2_cannot_reach_8_15`).

NUMBERS (exact, proved in-file; python scratch only for this report):
* `θ₃ = 8.75·log 3 ∈ [9.612, 9.613]` (true `≈ 9.6128575258`);
  `y₃ = θ₃ - 3π ∈ [0.16, 0.20]` (true `≈ 0.18808`);
  `cos θ₃ ∈ [-1, -0.98]` (true `≈ -0.98237`);
  `sin θ₃ ∈ [-0.20, -0.15]` (true `≈ -0.18697`).
* `θ₄ = 8.75·log 4 = 17.5·log 2 ∈ [12.130, 12.131]` (true `≈ 12.1300756598`);
  `w₄ = 4π - θ₄ ∈ [0.429, 0.470]` (true `≈ 0.43629`);
  `cos θ₄ ∈ [0.88, 1]` (true `≈ 0.90632`); `sin θ₄ ∈ [-0.47, -0.41]`
  (true `≈ -0.42258`).
* `3^{-0.605} ∈ [10/21, 13/25] = [0.4762, 0.52]` (true `≈ 0.51445`);
  `4^{-0.605} ∈ [5/12, 4/9] = [0.4167, 0.4445]` (true `≈ 0.43227`).
* Term Re lowers: `t₂ ≥ -3/5` (true `≈ -0.50538`), `t₃ ≥ -1/2`
  (true `≈ -0.39178`); `Re S_4 ≥ -23/30 ≈ -0.7667` (true `≈ -0.53904`,
  `|S_4| ≈ 0.58558`).

RESIDUAL (exact, quantified -- report-and-stop, no spin):
* The `S_4` Re-sum lower `-23/30` is NEGATIVE (true Re `≈ -0.54 < 0`), so
  `D3_block_norm_ge_sum_lo` through Re-parts CANNOT yield a positive `‖S_4‖`
  lower — `D3_S4_norm_ge` is green but trivially-true, and `D3_S4_cannot_reach_8_15`
  records that this route never reaches `8/15` for any `U ≥ 0`. This is a property
  of the Re-projection (the true norm `≈ 0.586` lives partly in Im), not of bound
  looseness: no tightening of these per-term Re intervals flips the sign.
* The durable deliverable is the per-term enclosure technology (`θ/amplitude/cos/sin`
  for `x = 3, 4`, same shapes the `S_2` block used for `x = 2`). Next session:
  `θ₅..θ₁₆` enclosures (same template, `log_five_d9` + `log (n)` via
  `log_nat`/`log_mul` bridges, each new prime needs its d9 bound) toward the
  K-table's first feasible `K = 16` (margin `0.024`), PLUS the cancellation-aware
  middle-block `[16,1024)` UPPER (`≤ 0.12` class; triangle `≈ 35`, Abel+MVT `≈ 8.6`
  both too loose — Tier-3 second-derivative or block-interval uppers needed).
-/

/-- (C) Numeral identity `4 ^ 0.605 = 2 ^ 1.21` (new in-file; Mathlib has no
    numeral bridge between `4 ^ (0.605 : ℝ)` and `2 ^ (1.21 : ℝ)`). -/
theorem D3_four_rpow_eq : ((4 : ℝ) ^ ((0.605 : ℝ))) = (2 : ℝ) ^ ((1.21 : ℝ)) := by
  have h4 : (4 : ℝ) = (((2 : ℝ)) ^ ((2 : ℕ))) := by norm_num
  rw [h4, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show (((2 : ℕ)) : ℝ) * (0.605 : ℝ) = (1.21 : ℝ) by norm_num]

set_option maxHeartbeats 800000 in
/-- (C) Head amplitude upper `D3_amp 2 ≤ 13/25` (via `3^{3/5} ≥ 25/13`,
    cleared: `(25/13)^5 ≤ 27 = 3^3`, since `3/5 ≤ 0.605`). -/
theorem D3_amp_three_upper : D3_amp 2 ≤ 13 / 25 := by
  unfold D3_amp
  have hcast : ((((2 : ℕ)) : ℝ) + 1 : ℝ) = 3 := by norm_num
  rw [hcast]
  have h35 : (3 / 5 : ℝ) ≤ (0.605 : ℝ) := by norm_num
  have hmono : (3 : ℝ) ^ ((3 / 5 : ℝ)) ≤ (3 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h35
  have hpow : ((25 / 13 : ℝ)) ^ ((5 : ℕ))
      ≤ ((((3 : ℝ) ^ ((3 / 5 : ℝ)))) ^ ((5 : ℕ)) : ℝ) := by
    have e : ((((3 : ℝ) ^ ((3 / 5 : ℝ)))) ^ ((5 : ℕ)) : ℝ)
        = (3 : ℝ) ^ ((3 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      rw [show (3 / 5 : ℝ) * (((5 : ℕ)) : ℝ) = (3 : ℝ) by norm_num]
      rw [show (3 : ℝ) = (((3 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 3 3
    rw [e]
    norm_num
  have hstep : (25 / 13 : ℝ) ≤ (3 : ℝ) ^ ((3 / 5 : ℝ)) :=
    le_of_pow_le_pow_left₀ (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _).le hpow
  have h3ge : (25 / 13 : ℝ) ≤ (3 : ℝ) ^ (0.605 : ℝ) := le_trans hstep hmono
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have e : (-0.605 : ℝ) = -(0.605 : ℝ) := by norm_num
  rw [e, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  have heq : (13 / 25 : ℝ) = ((25 / 13 : ℝ))⁻¹ := by norm_num
  rw [heq]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr h3ge

set_option maxHeartbeats 800000 in
/-- (C) Head amplitude lower `10/21 ≤ D3_amp 2` (via `3^{2/3} ≤ 21/10`,
    cleared: `3^2 = 9 ≤ (21/10)^3`, since `0.605 ≤ 2/3`). -/
theorem D3_amp_three_lower : 10 / 21 ≤ D3_amp 2 := by
  unfold D3_amp
  have hcast : ((((2 : ℕ)) : ℝ) + 1 : ℝ) = 3 := by norm_num
  rw [hcast]
  have h65 : (0.605 : ℝ) ≤ 2 / 3 := by norm_num
  have hmono : (3 : ℝ) ^ (0.605 : ℝ) ≤ (3 : ℝ) ^ ((2 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h65
  have hpow : ((((3 : ℝ) ^ ((2 / 3 : ℝ)))) ^ ((3 : ℕ)) : ℝ)
      ≤ (((21 / 10 : ℝ)) ^ ((3 : ℕ))) := by
    have e : ((((3 : ℝ) ^ ((2 / 3 : ℝ)))) ^ ((3 : ℕ)) : ℝ)
        = (3 : ℝ) ^ ((2 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      rw [show (2 / 3 : ℝ) * (((3 : ℕ)) : ℝ) = (2 : ℝ) by norm_num]
      rw [show (2 : ℝ) = (((2 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 3 2
    rw [e]
    norm_num
  have hstep : (3 : ℝ) ^ ((2 / 3 : ℝ)) ≤ 21 / 10 :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  have h3le : (3 : ℝ) ^ (0.605 : ℝ) ≤ 21 / 10 := le_trans hmono hstep
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have e : (-0.605 : ℝ) = -(0.605 : ℝ) := by norm_num
  rw [e, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  have heq : (10 / 21 : ℝ) = ((21 / 10 : ℝ))⁻¹ := by norm_num
  rw [heq]
  exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 21 / 10) hpos).mpr h3le

set_option maxHeartbeats 800000 in
/-- (C) Head amplitude upper `D3_amp 3 ≤ 4/9` (via squaring
    `zetaRefl_rpow_0605_ge`: `(2^0.605)^2 = 2^1.21 = 4^0.605 ≥ (3/2)^2`). -/
theorem D3_amp_four_upper : D3_amp 3 ≤ 4 / 9 := by
  unfold D3_amp
  have hcast : ((((3 : ℕ)) : ℝ) + 1 : ℝ) = 4 := by norm_num
  rw [hcast]
  have h2 := zetaRefl_rpow_0605_ge
  have hsq : ((3 / 2 : ℝ)) ^ ((2 : ℕ))
      ≤ ((((2 : ℝ) ^ (0.605 : ℝ))) ^ ((2 : ℕ)) : ℝ) :=
    pow_le_pow_left₀ (by norm_num) h2 2
  have e2 : (((((2 : ℝ) ^ (0.605 : ℝ))) ^ ((2 : ℕ))) : ℝ)
      = (2 : ℝ) ^ ((1.21 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show (0.605 : ℝ) * (((2 : ℕ)) : ℝ) = (1.21 : ℝ) by norm_num]
  have h4ge : (9 / 4 : ℝ) ≤ (4 : ℝ) ^ (0.605 : ℝ) := by
    rw [D3_four_rpow_eq]
    have hsq2 : ((3 / 2 : ℝ)) ^ ((2 : ℕ)) ≤ (2 : ℝ) ^ ((1.21 : ℝ)) := by
      rw [← e2]
      exact hsq
    have h32 : ((3 / 2 : ℝ)) ^ ((2 : ℕ)) = (9 / 4 : ℝ) := by norm_num
    rw [h32] at hsq2
    exact hsq2
  have hpos : (0 : ℝ) < (4 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have e : (-0.605 : ℝ) = -(0.605 : ℝ) := by norm_num
  rw [e, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
  have heq : (4 / 9 : ℝ) = ((9 / 4 : ℝ))⁻¹ := by norm_num
  rw [heq]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr h4ge

set_option maxHeartbeats 800000 in
/-- (C) Head amplitude lower `5/12 ≤ D3_amp 3` (via `2^{1.21} ≤ 2^{5/4} = 2·2^{1/4}`,
    cleared: `2 ≤ (6/5)^4`, since `1.21 ≤ 5/4`). -/
theorem D3_amp_four_lower : 5 / 12 ≤ D3_amp 3 := by
  unfold D3_amp
  have hcast : ((((3 : ℕ)) : ℝ) + 1 : ℝ) = 4 := by norm_num
  rw [hcast]
  have hpow : ((((2 : ℝ) ^ ((1 / 4 : ℝ)))) ^ ((4 : ℕ)) : ℝ)
      ≤ (((6 / 5 : ℝ)) ^ ((4 : ℕ))) := by
    have e : ((((2 : ℝ) ^ ((1 / 4 : ℝ)))) ^ ((4 : ℕ)) : ℝ)
        = (2 : ℝ) ^ ((1 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [show (1 / 4 : ℝ) * (((4 : ℕ)) : ℝ) = (1 : ℝ) by norm_num]
      rw [show (1 : ℝ) = (((1 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 2 1
    rw [e]
    norm_num
  have hstep : (2 : ℝ) ^ ((1 / 4 : ℝ)) ≤ 6 / 5 :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  have hmono : (2 : ℝ) ^ ((1.21 : ℝ)) ≤ (2 : ℝ) ^ ((5 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hsplit : (2 : ℝ) ^ ((5 / 4 : ℝ)) = 2 * (2 : ℝ) ^ ((1 / 4 : ℝ)) := by
    have e : (5 / 4 : ℝ) = 1 + 1 / 4 := by norm_num
    rw [e, Real.rpow_add (by norm_num), Real.rpow_one]
  have h4le : (4 : ℝ) ^ ((0.605 : ℝ)) ≤ 12 / 5 := by
    rw [D3_four_rpow_eq]
    calc (2 : ℝ) ^ ((1.21 : ℝ))
        ≤ (2 : ℝ) ^ ((5 / 4 : ℝ)) := hmono
      _ = 2 * (2 : ℝ) ^ ((1 / 4 : ℝ)) := hsplit
      _ ≤ 2 * (6 / 5) := mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ = 12 / 5 := by norm_num
  have hpos : (0 : ℝ) < (4 : ℝ) ^ ((0.605 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have e : (-0.605 : ℝ) = -(0.605 : ℝ) := by norm_num
  rw [e, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
  have heq : (5 / 12 : ℝ) = ((12 / 5 : ℝ))⁻¹ := by norm_num
  rw [heq]
  exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 12 / 5) hpos).mpr h4le

/-- (C) `D3_phase 2 = 8.75·log 3`. -/
theorem D3_phase_two_eq : D3_phase 2 = 8.75 * Real.log 3 := by
  unfold D3_phase
  have h : ((((2 : ℕ)) : ℝ) + 1 : ℝ) = 3 := by norm_num
  rw [h]

/-- (C) `D3_phase 3 = 8.75·log 4`. -/
theorem D3_phase_three_eq : D3_phase 3 = 8.75 * Real.log 4 := by
  unfold D3_phase
  have h : ((((3 : ℕ)) : ℝ) + 1 : ℝ) = 4 := by norm_num
  rw [h]

/-- (C) Phase lower `9.612 ≤ θ₃` (from `log_three_gt_d9`). -/
theorem D3_theta_three_lo : 9.612 ≤ D3_phase 2 := by
  rw [D3_phase_two_eq]
  have hlog := Real.log_three_gt_d9
  have hmul := mul_lt_mul_of_pos_left hlog (by norm_num : (0 : ℝ) < 8.75)
  have hnum : (9.612 : ℝ) ≤ 8.75 * 1.0986122885 := by norm_num
  linarith

/-- (C) Phase upper `θ₃ ≤ 9.613` (from `log_three_lt_d9`). -/
theorem D3_theta_three_hi : D3_phase 2 ≤ 9.613 := by
  rw [D3_phase_two_eq]
  have hlog := Real.log_three_lt_d9
  have hmul := mul_lt_mul_of_pos_left hlog (by norm_num : (0 : ℝ) < 8.75)
  have hnum : 8.75 * 1.0986122888 ≤ (9.613 : ℝ) := by norm_num
  linarith

/-- (C) Phase lower `12.130 ≤ θ₄` (via `log_four_eq` + `log_two_gt_d9`,
    `8.75·(2·log 2) = 17.5·log 2` shape). -/
theorem D3_theta_four_lo : 12.130 ≤ D3_phase 3 := by
  rw [D3_phase_three_eq, Real.log_four_eq]
  have hlog := Real.log_two_gt_d9
  have e : 8.75 * (2 * Real.log 2) = 17.5 * Real.log 2 := by ring
  rw [e]
  have hmul := mul_lt_mul_of_pos_left hlog (by norm_num : (0 : ℝ) < 17.5)
  have hnum : (12.130 : ℝ) ≤ 17.5 * 0.6931471803 := by norm_num
  linarith

/-- (C) Phase upper `θ₄ ≤ 12.131` (via `log_four_eq` + `log_two_lt_d9`). -/
theorem D3_theta_four_hi : D3_phase 3 ≤ 12.131 := by
  rw [D3_phase_three_eq, Real.log_four_eq]
  have hlog := Real.log_two_lt_d9
  have e : 8.75 * (2 * Real.log 2) = 17.5 * Real.log 2 := by ring
  rw [e]
  have hmul := mul_lt_mul_of_pos_left hlog (by norm_num : (0 : ℝ) < 17.5)
  have hnum : 17.5 * 0.6931471808 ≤ (12.131 : ℝ) := by norm_num
  linarith

/-- (C) Reduced phase `θ₃ - 2π ∈ [3.312, 3.333]` (from `pi_d2`). -/
theorem D3_delta_three_mem :
    (3.312 : ℝ) ≤ D3_phase 2 - 2 * Real.pi ∧
    D3_phase 2 - 2 * Real.pi ≤ 3.333 := by
  have hth_lo := D3_theta_three_lo
  have hth_hi := D3_theta_three_hi
  have hpi_lo := Real.pi_gt_d2
  have hpi_hi := Real.pi_lt_d2
  constructor <;> linarith

/-- (C) Reduced phase `2π - (θ₄ - 2π) = 4π - θ₄ ∈ [0.429, 0.470]`
    (from `pi_d2`). -/
theorem D3_delta_four_mem :
    (0.429 : ℝ) ≤ 2 * Real.pi - (D3_phase 3 - 2 * Real.pi) ∧
    2 * Real.pi - (D3_phase 3 - 2 * Real.pi) ≤ 0.470 := by
  have hth_lo := D3_theta_four_lo
  have hth_hi := D3_theta_four_hi
  have hpi_lo := Real.pi_gt_d2
  have hpi_hi := Real.pi_lt_d2
  constructor <;> linarith

/-- (C) Trivial cosine lower `cos θ₃ ≥ -1`. -/
theorem D3_cos_theta_three_lower : -1 ≤ Real.cos (D3_phase 2) :=
  (Real.cos_mem_Icc _).1

set_option maxHeartbeats 800000 in
/-- (C) Cosine upper `cos θ₃ ≤ -0.98` (`cos_add_pi` shift + quadratic
    `1 - y²/2`, `y = θ₃ - 3π ≤ 0.20`). -/
theorem D3_cos_theta_three_upper : Real.cos (D3_phase 2) ≤ -0.98 := by
  have hmem := D3_delta_three_mem
  have hpi_lo := Real.pi_gt_d2
  have hpi_hi := Real.pi_lt_d2
  set y := D3_phase 2 - 2 * Real.pi - Real.pi with hy_def
  have hy_lo : (0.16 : ℝ) ≤ y := by rw [hy_def]; linarith [hmem.1, hpi_hi]
  have hy_hi : y ≤ (0.20 : ℝ) := by rw [hy_def]; linarith [hmem.2, hpi_lo]
  have hy_nn : (0 : ℝ) ≤ y := by linarith [hy_lo]
  have hsq : y ^ 2 ≤ (0.20 : ℝ) ^ 2 := pow_le_pow_left₀ hy_nn hy_hi 2
  have hcos_lo := Real.one_sub_sq_div_two_le_cos (x := y)
  have hnum : (0.98 : ℝ) ≤ 1 - (0.20 : ℝ) ^ 2 / 2 := by norm_num
  have hcosy : (0.98 : ℝ) ≤ Real.cos y := by linarith [hcos_lo, hsq, hnum]
  have hdecomp : D3_phase 2 - 2 * Real.pi = y + Real.pi := by rw [hy_def]; ring
  have h1 : Real.cos (D3_phase 2 - 2 * Real.pi) = Real.cos (D3_phase 2) :=
    Real.cos_sub_two_pi _
  rw [hdecomp, Real.cos_add_pi] at h1
  linarith [h1, hcosy]

set_option maxHeartbeats 800000 in
/-- (C) Sine enclosure `sin θ₃ ∈ [-0.20, -0.15]` (`sin_add_pi` shift +
    cubic/linear, `y ∈ [0.16, 0.20]`). -/
theorem D3_sin_theta_three_mem :
    -0.20 ≤ Real.sin (D3_phase 2) ∧ Real.sin (D3_phase 2) ≤ -0.15 := by
  have hmem := D3_delta_three_mem
  have hpi_lo := Real.pi_gt_d2
  have hpi_hi := Real.pi_lt_d2
  set y := D3_phase 2 - 2 * Real.pi - Real.pi with hy_def
  have hy_lo : (0.16 : ℝ) ≤ y := by rw [hy_def]; linarith [hmem.1, hpi_hi]
  have hy_hi : y ≤ (0.20 : ℝ) := by rw [hy_def]; linarith [hmem.2, hpi_lo]
  have hy_nn : (0 : ℝ) ≤ y := by linarith [hy_lo]
  have hsin_lo := Real.sin_ge_sub_cube hy_nn
  have hsin_hi := Real.sin_le hy_nn
  have hcube : y ^ 3 ≤ (0.20 : ℝ) ^ 3 := pow_le_pow_left₀ hy_nn hy_hi 3
  have hnum : (0.15 : ℝ) ≤ (0.16 : ℝ) - (0.20 : ℝ) ^ 3 / 6 := by norm_num
  have hlo : (0.15 : ℝ) ≤ Real.sin y := by
    have h1 : (0.16 : ℝ) - (0.20 : ℝ) ^ 3 / 6 ≤ y - y ^ 3 / 6 := by
      linarith [hy_lo, hcube]
    linarith [hsin_lo, h1, hnum]
  have hhi : Real.sin y ≤ (0.20 : ℝ) := by linarith [hsin_hi, hy_hi]
  have hdecomp : D3_phase 2 - 2 * Real.pi = y + Real.pi := by rw [hy_def]; ring
  have h1s : Real.sin (D3_phase 2 - 2 * Real.pi) = Real.sin (D3_phase 2) :=
    Real.sin_sub_two_pi _
  have h2s : Real.sin (D3_phase 2 - 2 * Real.pi) = -Real.sin y := by
    rw [hdecomp, Real.sin_add_pi]
  have hsin_eq : Real.sin (D3_phase 2) = -Real.sin y := by rw [← h1s, h2s]
  constructor <;> linarith [hlo, hhi, hsin_eq]

/-- (C) Trivial cosine upper `cos θ₄ ≤ 1`. -/
theorem D3_cos_theta_four_le_one : Real.cos (D3_phase 3) ≤ 1 :=
  (Real.cos_mem_Icc _).2

set_option maxHeartbeats 800000 in
/-- (C) Cosine lower `0.88 ≤ cos θ₄` (periodicity + quadratic `1 - w²/2`,
    `w = 2π - (θ₄ - 2π) ≤ 0.470`). -/
theorem D3_cos_theta_four_lower : 0.88 ≤ Real.cos (D3_phase 3) := by
  have hmem := D3_delta_four_mem
  have h1 : Real.cos (D3_phase 3 - 2 * Real.pi) = Real.cos (D3_phase 3) :=
    Real.cos_sub_two_pi _
  have h2 : Real.cos (D3_phase 3 - 2 * Real.pi) =
      Real.cos (2 * Real.pi - (D3_phase 3 - 2 * Real.pi)) := by
    have e : (2 * Real.pi - (D3_phase 3 - 2 * Real.pi)) =
        -((D3_phase 3 - 2 * Real.pi) - 2 * Real.pi) := by ring
    rw [e, Real.cos_neg]
    exact (Real.cos_sub_two_pi _).symm
  have hcos_eq : Real.cos (D3_phase 3) =
      Real.cos (2 * Real.pi - (D3_phase 3 - 2 * Real.pi)) := by rw [← h1, h2]
  rw [hcos_eq]
  have hw_lo := hmem.1
  have hw_hi := hmem.2
  have hw_nn : (0 : ℝ) ≤ 2 * Real.pi - (D3_phase 3 - 2 * Real.pi) := by
    linarith [hw_lo]
  have hsq : (2 * Real.pi - (D3_phase 3 - 2 * Real.pi)) ^ 2 ≤ (0.470 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hw_nn hw_hi 2
  have hcos_lo := Real.one_sub_sq_div_two_le_cos
    (x := 2 * Real.pi - (D3_phase 3 - 2 * Real.pi))
  have hnum : (0.88 : ℝ) ≤ 1 - (0.470 : ℝ) ^ 2 / 2 := by norm_num
  have hle : 1 - (0.470 : ℝ) ^ 2 / 2 ≤
      1 - (2 * Real.pi - (D3_phase 3 - 2 * Real.pi)) ^ 2 / 2 := by
    linarith [hsq]
  linarith [hcos_lo, hle, hnum]

set_option maxHeartbeats 800000 in
/-- (C) Sine enclosure `sin θ₄ ∈ [-0.47, -0.41]` (periodicity + cubic/linear,
    `w ∈ [0.429, 0.470]`). -/
theorem D3_sin_theta_four_mem :
    -0.47 ≤ Real.sin (D3_phase 3) ∧ Real.sin (D3_phase 3) ≤ -0.41 := by
  have hmem := D3_delta_four_mem
  have h1s : Real.sin (D3_phase 3 - 2 * Real.pi) = Real.sin (D3_phase 3) :=
    Real.sin_sub_two_pi _
  have h2s : Real.sin (D3_phase 3 - 2 * Real.pi) =
      -Real.sin (2 * Real.pi - (D3_phase 3 - 2 * Real.pi)) := by
    have e : (2 * Real.pi - (D3_phase 3 - 2 * Real.pi)) =
        -((D3_phase 3 - 2 * Real.pi) - 2 * Real.pi) := by ring
    rw [e, Real.sin_neg, neg_neg]
    exact (Real.sin_sub_two_pi _).symm
  have hsin_eq : Real.sin (D3_phase 3) =
      -Real.sin (2 * Real.pi - (D3_phase 3 - 2 * Real.pi)) := by
    rw [← h1s, h2s]
  rw [hsin_eq]
  have hw_lo := hmem.1
  have hw_hi := hmem.2
  have hw_nn : (0 : ℝ) ≤ 2 * Real.pi - (D3_phase 3 - 2 * Real.pi) := by
    linarith [hw_lo]
  have hsin_lo := Real.sin_ge_sub_cube hw_nn
  have hsin_hi := Real.sin_le hw_nn
  have hcube : (2 * Real.pi - (D3_phase 3 - 2 * Real.pi)) ^ 3 ≤ (0.470 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hw_nn hw_hi 3
  have hnum : (0.41 : ℝ) ≤ (0.429 : ℝ) - (0.470 : ℝ) ^ 3 / 6 := by norm_num
  have hlo : (0.41 : ℝ) ≤
      Real.sin (2 * Real.pi - (D3_phase 3 - 2 * Real.pi)) := by
    have h1 : (0.429 : ℝ) - (0.470 : ℝ) ^ 3 / 6 ≤
        (2 * Real.pi - (D3_phase 3 - 2 * Real.pi)) -
          (2 * Real.pi - (D3_phase 3 - 2 * Real.pi)) ^ 3 / 6 := by
      linarith [hw_lo, hcube]
    linarith [hsin_lo, h1, hnum]
  have hhi : Real.sin (2 * Real.pi - (D3_phase 3 - 2 * Real.pi)) ≤ (0.470 : ℝ) := by
    linarith [hsin_hi, hw_hi]
  constructor <;> linarith [hlo, hhi]

/-- (C) Third-term real-part lower `≥ -3/5` (interval: `amp ≤ 13/25`,
    `cos ≥ -1`). -/
theorem D3_term2_re_lo :
    (-3 / 5 : ℝ) ≤ (etaDirichletTerm (1 - zetaCellS0) 2).re := by
  rw [D3_eta_re]
  have hamp := D3_amp_three_upper
  have hcos_lo := D3_cos_theta_three_lower
  have hamp_nn : (0 : ℝ) ≤ D3_amp 2 := D3_amp_nonneg 2
  have hpow2 : ((-1 : ℝ) ^ (2 : ℕ)) = 1 := by norm_num [pow_two]
  rw [hpow2, one_mul]
  have h : (-(13 / 25) : ℝ) ≤ D3_amp 2 * Real.cos (D3_phase 2) := by
    have h1 : D3_amp 2 * (-1) ≤ D3_amp 2 * Real.cos (D3_phase 2) :=
      mul_le_mul_of_nonneg_left hcos_lo hamp_nn
    linarith [h1, hamp]
  linarith [h]

/-- (C) Fourth-term real-part lower `≥ -1/2` (interval: `amp ≤ 4/9`,
    `cos ≤ 1`). -/
theorem D3_term3_re_lo :
    (-1 / 2 : ℝ) ≤ (etaDirichletTerm (1 - zetaCellS0) 3).re := by
  rw [D3_eta_re]
  have hamp := D3_amp_four_upper
  have hcos_le := D3_cos_theta_four_le_one
  have hcos_nn : (0 : ℝ) ≤ Real.cos (D3_phase 3) := by
    linarith [D3_cos_theta_four_lower]
  have hamp_nn : (0 : ℝ) ≤ D3_amp 3 := D3_amp_nonneg 3
  have hprod : D3_amp 3 * Real.cos (D3_phase 3) ≤ 4 / 9 := by
    have h := mul_le_mul hamp hcos_le hcos_nn (by norm_num : (0 : ℝ) ≤ 4 / 9)
    have e : (4 / 9 : ℝ) * 1 = 4 / 9 := by ring
    rw [e] at h
    exact h
  have hpow3 : ((-1 : ℝ) ^ (3 : ℕ)) = -1 := by
    have e31 : (3 : ℕ) = 2 + 1 := rfl
    have hpow2 : ((-1 : ℝ) ^ (2 : ℕ)) = 1 := by norm_num [pow_two]
    rw [e31, pow_add, hpow2, pow_one, one_mul]
  rw [hpow3]
  linarith [hprod]

/-- (C) `S_4` real-part lower `≥ -23/30` via the interval framework
    (`1 - 2/3 - 3/5 - 1/2`, à la `D3_S2_re_lower`). -/
theorem D3_S4_re_lower :
    (-23 / 30 : ℝ) ≤
      (∑ k ∈ Finset.range 4, etaDirichletTerm (1 - zetaCellS0) k).re := by
  rw [D3_sum_re_eq]
  have h4 : (∑ k ∈ Finset.range 4, (etaDirichletTerm (1 - zetaCellS0) k).re) =
      (etaDirichletTerm (1 - zetaCellS0) 0).re +
      (etaDirichletTerm (1 - zetaCellS0) 1).re +
      (etaDirichletTerm (1 - zetaCellS0) 2).re +
      (etaDirichletTerm (1 - zetaCellS0) 3).re := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [h4, D3_term0_re]
  have h1 := D3_term1_re_lo
  have h2 := D3_term2_re_lo
  have h3 := D3_term3_re_lo
  linarith

/-- (F2) Explicit per-term Re lowers for `S_4` (sums to `-23/30`). -/
def D3_S4_lo : ℕ → ℝ := fun k =>
  if k = 0 then 1 else if k = 1 then -2 / 3 else if k = 2 then -3 / 5 else -1 / 2

/-- (F2) The `S_4` lo-sum is `-23/30`. -/
theorem D3_S4_lo_sum : ∑ k ∈ Finset.range 4, D3_S4_lo k = (-23 / 30 : ℝ) := by
  have v0 : D3_S4_lo 0 = (1 : ℝ) := by simp [D3_S4_lo]
  have v1 : D3_S4_lo 1 = (-2 / 3 : ℝ) := by simp [D3_S4_lo]
  have v2 : D3_S4_lo 2 = (-3 / 5 : ℝ) := by simp [D3_S4_lo]
  have v3 : D3_S4_lo 3 = (-1 / 2 : ℝ) := by simp [D3_S4_lo]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, v0, v1, v2, v3]
  norm_num

/-- (F2) The `S_4` lo-values bound the term real parts below. -/
theorem D3_S4_lo_valid (k : ℕ) (hk : k < 4) :
    D3_S4_lo k ≤ (etaDirichletTerm (1 - zetaCellS0) k).re := by
  have v0 : D3_S4_lo 0 = (1 : ℝ) := by simp [D3_S4_lo]
  have v1 : D3_S4_lo 1 = (-2 / 3 : ℝ) := by simp [D3_S4_lo]
  have v2 : D3_S4_lo 2 = (-3 / 5 : ℝ) := by simp [D3_S4_lo]
  have v3 : D3_S4_lo 3 = (-1 / 2 : ℝ) := by simp [D3_S4_lo]
  interval_cases k
  · rw [v0, D3_term0_re]
  · rw [v1]
    exact D3_term1_re_lo
  · rw [v2]
    exact D3_term2_re_lo
  · rw [v3]
    exact D3_term3_re_lo

/-- (F2) `S_4` norm lower `≥ -23/30` through `D3_block_norm_ge_sum_lo`. -/
theorem D3_S4_norm_ge :
    (-23 / 30 : ℝ) ≤
      ‖∑ k ∈ Finset.range 4, etaDirichletTerm (1 - zetaCellS0) k‖ := by
  have h := D3_block_norm_ge_sum_lo 4 D3_S4_lo D3_S4_lo_valid
  rw [D3_S4_lo_sum] at h
  exact h

/-- (P) `S_{1024}` conditional from the `S_4` interval lower. -/
theorem D3_S1024_of_S4 (U : ℝ)
    (hU : ‖∑ k ∈ Finset.Ico 4 1024, etaDirichletTerm (1 - zetaCellS0) k‖ ≤ U) :
    (-23 / 30 - U : ℝ) ≤
      ‖∑ k ∈ Finset.range 1024, etaDirichletTerm (1 - zetaCellS0) k‖ :=
  D3_S1024_split_lower 4 (by norm_num) (-23 / 30) U D3_S4_norm_ge hU

/-- (P) The `S_4` Re-route CANNOT reach `8/15` via splitting
    (needs `U ≤ -23/30 - 8/15 < 0`). -/
theorem D3_S4_cannot_reach_8_15 (U : ℝ) (hU : 0 ≤ U) :
    (-23 / 30 - U : ℝ) < 8 / 15 := by
  have h : (-23 / 30 : ℝ) < 8 / 15 := by norm_num
  linarith

#print axioms D3_four_rpow_eq
#print axioms D3_amp_three_upper
#print axioms D3_amp_three_lower
#print axioms D3_amp_four_upper
#print axioms D3_amp_four_lower
#print axioms D3_phase_two_eq
#print axioms D3_phase_three_eq
#print axioms D3_theta_three_lo
#print axioms D3_theta_three_hi
#print axioms D3_theta_four_lo
#print axioms D3_theta_four_hi
#print axioms D3_delta_three_mem
#print axioms D3_delta_four_mem
#print axioms D3_cos_theta_three_lower
#print axioms D3_cos_theta_three_upper
#print axioms D3_sin_theta_three_mem
#print axioms D3_cos_theta_four_le_one
#print axioms D3_cos_theta_four_lower
#print axioms D3_sin_theta_four_mem
#print axioms D3_term2_re_lo
#print axioms D3_term3_re_lo
#print axioms D3_S4_re_lower
#print axioms D3_S4_lo_sum
#print axioms D3_S4_lo_valid
#print axioms D3_S4_norm_ge
#print axioms D3_S1024_of_S4
#print axioms D3_S4_cannot_reach_8_15

/-!

## Door-3 `S_6` interval block (D3, tier 1): `θ₅/θ₆` enclosures + per-term Re lowers + `S_6` sum.

GOAL (door-3 closure premise, minimum viable `x = 5, 6`: one prime + one composite,
toward `‖S_{1024}(s1)‖ ≥ 8/15` with `s1 = 1 - s0`, `σ = 0.605`, `t = 8.75`): extend the
D3 early-block interval framework from `S_4` to `S_6 = ∑ k ∈ range 6` via rigorous
per-term cpow enclosures for `k = 4, 5` (`x = 5, 6`), following the `S_2`/`S_4` template
exactly (phase interval, cos/sin intervals, amplitude interval, term-Re lower, all
`Finset.range`, Re-parts via `D3_sum_re_eq`, norm via `D3_block_norm_ge_sum_lo`).
Pair-absolute/Tendsto forms only; no `∑'`-with-`0 <` (all sums are `Finset.range`).

GREP-FIRST RECORD (run before writing; repo `zeta_rigorous.lean` + `Mathlib/`):
* `Real.log_five_gt_d9` (`1.6094379123 < log 5`) / `Real.log_five_lt_d9`
  (`log 5 < 1.6094379126`) / `Real.log_ten_eq` (`log 10 = log 2 + log 5`) — all in
  `Mathlib/Analysis/Complex/ExponentialBounds.lean:109-127`, namespace `Real`. EXIST.
  `Real.log_four_eq` (`:107`), `Real.log_two/three_gt/lt_d9` (`:83`-`:104`) — EXIST
  (the `S_4` template's inputs).
* `log_seven|log_eleven|log_thirteen|log_six_eq|log_nine|log_eight` d9 enclosures —
  ABSENT in `Mathlib/` (only incidental `log 8` in `Behrend.lean:278`, no enclosure);
  hence `x = 7` (and `11`, `13`) phases are blocked on missing prime-log d9 bounds,
  while composite `x = 6 = 2 * 3` factors through smaller primes below.
* `Real.log_mul (hx : x ≠ 0) (hy : y ≠ 0)` (`log (x*y) = log x + log y`,
  `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:133`) — EXISTS, consumed for
  `D3_log_six_eq` (same `rw [e6, Real.log_mul ...]` pattern as `JensenTranslation.lean`;
  no log API recreated).
* Trig/rpow/pi lemmas — the same EXIST set the `S_4` template documents
  (`cos_add_pi`, `sin_add_pi`, `cos_sub_two_pi`, `sin_sub_two_pi`, `cos_neg`,
  `sin_neg`, `cos_mem_Icc`/`sin_mem_Icc`, `one_sub_sq_div_two_le_cos`,
  `sin_ge_sub_cube`, `sin_le`, `pi_gt_d2`/`pi_lt_d2`, `le_of_pow_le_pow_left₀`,
  `rpow_le_rpow_of_exponent_le`, `pow_le_pow_left₀`, `mul_le_mul_of_nonneg_left`,
  `inv_le_inv₀`, `rpow_neg/natCast/mul/add/one`; every one already used in this file).
* In-file reuse (read-only): `D3_amp`/`D3_phase`/`D3_eta_re` (`:5910`-`:6013`),
  `D3_sum_re_eq`/`D3_block_norm_ge_sum_lo`/`D3_S1024_split_lower` (`:6016`-`:6057`),
  `D3_amp_nonneg`, `D3_term0_re`, `D3_term1/2/3_re_lo`, `D3_S4_*` (`:6776`-`:6873`).
  Nothing redefined.
* Name-clash check (`D3_amp_five|D3_amp_six|D3_phase_four|D3_phase_five|D3_theta_five|
  D3_theta_six|D3_delta_five|D3_delta_six|D3_cos_theta_five|D3_sin_theta_five|
  D3_cos_theta_six|D3_sin_theta_six|D3_term4|D3_term5|D3_S6|D3_log_six`) — 0 hits.

WHAT IS PROVED (all unconditional, FULL proofs, no `sorry`/`admit`/`axiom`):
* (C) Log bridge (composite pattern): `D3_log_six_eq` (`log 6 = log 2 + log 3`
  via `Real.log_mul`, the composite analogue of AZ2's `4^0.605 = 2^1.21` bridge).
* (C) Phases: `D3_phase_four_eq`/`D3_phase_five_eq`, `D3_theta_five_lo`/`hi`
  (`θ₅ ∈ [14.082, 14.083]` from `log_five_d9`, prime pattern),
  `D3_theta_six_lo`/`hi` (`θ₆ ∈ [15.677, 15.678]` from `log_two/three_d9`
  through the `log 6` bridge, composite pattern).
* (C) Reduction + trig: `D3_delta_five_mem` (`θ₅ - 4π ∈ [1.482, 1.523]`),
  `D3_delta_six_mem` (`θ₆ - 4π ∈ [3.077, 3.118]`),
  `D3_cos_theta_five_le_one` (trivial `≤ 1`) + `D3_cos_theta_five_lower`
  (`≥ -0.16` via double-periodicity + quadratic),
  `D3_sin_theta_five_mem` (`∈ [0.89, 1]` via double-periodicity + cubic/linear +
  `sin_mem_Icc`), `D3_cos_theta_six_lower` (trivial `≥ -1`) +
  `D3_cos_theta_six_upper` (`≤ -0.99` via `cos_add_pi` + `cos_neg` + quadratic),
  `D3_sin_theta_six_mem` (`∈ [0.02, 0.08]` via `sin_add_pi` + `sin_neg` +
  cubic/linear).
* (C) Amplitudes: `D3_amp_five_upper` (`≤ 2/5` via `5^{3/5} ≥ 5/2` ⟸
  `(5/2)^5 ≤ 125`, `3/5 ≤ 0.605`), `D3_amp_five_lower` (`≥ 1/3` via
  `5^{2/3} ≤ 3` ⟸ `25 ≤ 27`, `0.605 ≤ 2/3`), `D3_amp_six_upper` (`≤ 3/8` via
  `6^{3/5} ≥ 8/3` ⟸ `(8/3)^5 ≤ 216`), `D3_amp_six_lower` (`≥ 3/10` via
  `6^{2/3} ≤ 10/3` ⟸ `36 ≤ (10/3)^3`).
* (F2) Terms + sum (trivial-cos shapes à la `D3_term2/3_re_lo`, sharp intervals
  banked unused exactly as AZ2 banked them): `D3_term4_re_lo` (`≥ -2/5`:
  even, `amp·cos ≥ -amp`), `D3_term5_re_lo` (`≥ -3/8`: odd,
  `-(amp·cos) ≥ -3/8` via `cos ≤ 1` with no positivity assumption),
  `D3_S6_re_lower` (`≥ -37/30 - ... = -37/24`), `D3_S6_lo`/`D3_S6_lo_sum`/
  `D3_S6_lo_valid` + `D3_S6_norm_ge` (through `D3_block_norm_ge_sum_lo`),
  `D3_S1024_of_S6` + `D3_S6_cannot_reach_8_15` (mirroring `of_S4`/`cannot`).

NUMBERS (exact, proved in-file; python scratch only for this report):
* `θ₅ = 8.75·log 5 ∈ [14.082, 14.083]` (true `≈ 14.0825817342`);
  `δ₅ = θ₅ - 4π ∈ [1.482, 1.523]` (true `≈ 1.51621`);
  `cos θ₅ ∈ [-0.16, 1]` (true `≈ +0.0546`); `sin θ₅ ∈ [0.89, 1]` (true `≈ 0.99851`).
* `θ₆ = 8.75·log 6 ∈ [15.677, 15.678]` (true `≈ 15.6778953556`);
  `δ₆ = θ₆ - 4π ∈ [3.077, 3.118]` (true `≈ 3.11152`);
  `y₆ = δ₆ - π ∈ [-0.073, -0.022]` (true `≈ -0.03007`);
  `cos θ₆ ∈ [-1, -0.99]` (true `≈ -0.99955`); `sin θ₆ ∈ [0.02, 0.08]`
  (true `≈ 0.03007`).
* `5^{-0.605} ∈ [1/3, 2/5] = [0.3333, 0.4]` (true `≈ 0.37774`);
  `6^{-0.605} ∈ [3/10, 3/8] = [0.3, 0.375]` (true `≈ 0.33825`).
* Term Re lowers: `t₄ ≥ -2/5` (true `≈ +0.0206`), `t₅ ≥ -3/8` (true `≈ +0.3380`);
  `Re S_6 ≥ -37/24 ≈ -1.5417` (true `≈ -0.1804`).

RESIDUAL (exact, quantified -- report-and-stop, no spin):
* The `S_6` Re-sum lower `-37/24` is NEGATIVE (true Re `≈ -0.18 < 0`), so
  `D3_block_norm_ge_sum_lo` through Re-parts CANNOT yield a positive `‖S_6‖`
  lower — `D3_S6_norm_ge` is green but trivially-true, and `D3_S6_cannot_reach_8_15`
  records that this route never reaches `8/15` for any `U ≥ 0`. The `S_6` lower is
  looser than `S_4`'s (`-37/24 ≈ -1.542 < -23/30 ≈ -0.767`) purely because the
  term lowers use trivial-cos `-amp` bounds (AZ2's exact shape); the sharp `θ₆`
  upper (`cos ≤ -0.99`, odd `k = 5`) would give a POSITIVE term lower
  (`amp·0.99 ≥ 3/10·0.99 = 0.297`) and recover `≈ +0.67` of the sum — banked as
  the next optimization, not claimed here.
* Running margin to the K-table's first feasible `K = 16` target (`8/15 ≈ 0.5333`):
  `S_6` gives `-37/24 ≈ -1.5417`, i.e. `83/40 = 2.075` SHORT of `8/15`
  (`8/15 - (-37/24) = 249/120`). Honest status: per-term technology extended to
  `x = 5, 6` (both prime and composite patterns green); `S_16` assembly still needs
  `θ₇..θ₁₆` (blocked: `x = 7, 11, 13` need missing `log_seven/eleven/thirteen` d9
  bounds — must be CREATED in-file; composites `8, 9, 10, 12, 14, 15, 16` factor
  through `log 2/3/5` bridges as `x = 6` does here) PLUS the cancellation-aware
  middle-block `[16,1024)` UPPER (`≤ 0.12` class; triangle `≈ 35`, Abel+MVT `≈ 8.6`
  both too loose — Tier-3 second-derivative or block-interval uppers needed).
-/

/-- (C) Composite log bridge `log 6 = log 2 + log 3` (new in-file; Mathlib has no
    numeral `log 6` enclosure — factors through the `log_two/three` d9 bounds). -/
theorem D3_log_six_eq : Real.log 6 = Real.log 2 + Real.log 3 := by
  have h6 : (6 : ℝ) = 2 * 3 := by norm_num
  rw [h6, Real.log_mul (by norm_num) (by norm_num)]

/-- (C) `D3_phase 4 = 8.75·log 5` (prime pattern). -/
theorem D3_phase_four_eq : D3_phase 4 = 8.75 * Real.log 5 := by
  unfold D3_phase
  have h : ((((4 : ℕ)) : ℝ) + 1 : ℝ) = 5 := by norm_num
  rw [h]

/-- (C) `D3_phase 5 = 8.75·(log 2 + log 3)` (composite pattern via `D3_log_six_eq`). -/
theorem D3_phase_five_eq : D3_phase 5 = 8.75 * (Real.log 2 + Real.log 3) := by
  unfold D3_phase
  have h : ((((5 : ℕ)) : ℝ) + 1 : ℝ) = 6 := by norm_num
  rw [h, D3_log_six_eq]

/-- (C) Phase lower `14.082 ≤ θ₅` (from `log_five_gt_d9`). -/
theorem D3_theta_five_lo : 14.082 ≤ D3_phase 4 := by
  rw [D3_phase_four_eq]
  have hlog := Real.log_five_gt_d9
  have hmul := mul_lt_mul_of_pos_left hlog (by norm_num : (0 : ℝ) < 8.75)
  have hnum : (14.082 : ℝ) ≤ 8.75 * 1.6094379123 := by norm_num
  linarith

/-- (C) Phase upper `θ₅ ≤ 14.083` (from `log_five_lt_d9`). -/
theorem D3_theta_five_hi : D3_phase 4 ≤ 14.083 := by
  rw [D3_phase_four_eq]
  have hlog := Real.log_five_lt_d9
  have hmul := mul_lt_mul_of_pos_left hlog (by norm_num : (0 : ℝ) < 8.75)
  have hnum : 8.75 * 1.6094379126 ≤ (14.083 : ℝ) := by norm_num
  linarith

/-- (C) Phase lower `15.677 ≤ θ₆` (via `D3_log_six_eq` + `log_two/three_gt_d9`). -/
theorem D3_theta_six_lo : 15.677 ≤ D3_phase 5 := by
  rw [D3_phase_five_eq]
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_three_gt_d9
  have hsum : (1.7917594688 : ℝ) < Real.log 2 + Real.log 3 := by linarith
  have hmul := mul_lt_mul_of_pos_left hsum (by norm_num : (0 : ℝ) < 8.75)
  have hnum : (15.677 : ℝ) ≤ 8.75 * 1.7917594688 := by norm_num
  linarith

/-- (C) Phase upper `θ₆ ≤ 15.678` (via `D3_log_six_eq` + `log_two/three_lt_d9`). -/
theorem D3_theta_six_hi : D3_phase 5 ≤ 15.678 := by
  rw [D3_phase_five_eq]
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_lt_d9
  have hsum : Real.log 2 + Real.log 3 < (1.7917594696 : ℝ) := by linarith
  have hmul := mul_lt_mul_of_pos_left hsum (by norm_num : (0 : ℝ) < 8.75)
  have hnum : 8.75 * 1.7917594696 ≤ (15.678 : ℝ) := by norm_num
  linarith

/-- (C) Reduced phase `θ₅ - 4π ∈ [1.482, 1.523]` (from `pi_d2`). -/
theorem D3_delta_five_mem :
    (1.482 : ℝ) ≤ D3_phase 4 - 4 * Real.pi ∧
    D3_phase 4 - 4 * Real.pi ≤ 1.523 := by
  have hth_lo := D3_theta_five_lo
  have hth_hi := D3_theta_five_hi
  have hpi_lo := Real.pi_gt_d2
  have hpi_hi := Real.pi_lt_d2
  constructor <;> linarith

/-- (C) Reduced phase `θ₆ - 4π ∈ [3.077, 3.118]` (from `pi_d2`). -/
theorem D3_delta_six_mem :
    (3.077 : ℝ) ≤ D3_phase 5 - 4 * Real.pi ∧
    D3_phase 5 - 4 * Real.pi ≤ 3.118 := by
  have hth_lo := D3_theta_six_lo
  have hth_hi := D3_theta_six_hi
  have hpi_lo := Real.pi_gt_d2
  have hpi_hi := Real.pi_lt_d2
  constructor <;> linarith

/-- (C) Trivial cosine upper `cos θ₅ ≤ 1`. -/
theorem D3_cos_theta_five_le_one : Real.cos (D3_phase 4) ≤ 1 :=
  (Real.cos_mem_Icc _).2

set_option maxHeartbeats 800000 in
/-- (C) Cosine lower `-0.16 ≤ cos θ₅` (double-periodicity + quadratic `1 - w²/2`,
    `w = θ₅ - 4π ≤ 1.523`). -/
theorem D3_cos_theta_five_lower : -0.16 ≤ Real.cos (D3_phase 4) := by
  have hmem := D3_delta_five_mem
  have hper1 : Real.cos (D3_phase 4 - 2 * Real.pi) = Real.cos (D3_phase 4) :=
    Real.cos_sub_two_pi _
  have hper2 : Real.cos ((D3_phase 4 - 2 * Real.pi) - 2 * Real.pi) =
      Real.cos (D3_phase 4 - 2 * Real.pi) :=
    Real.cos_sub_two_pi _
  have hper : Real.cos (D3_phase 4 - 4 * Real.pi) = Real.cos (D3_phase 4) := by
    have e : (D3_phase 4 - 2 * Real.pi) - 2 * Real.pi =
        D3_phase 4 - 4 * Real.pi := by ring
    rw [e] at hper2
    exact hper2.trans hper1
  have hw_lo := hmem.1
  have hw_hi := hmem.2
  have hw_nn : (0 : ℝ) ≤ D3_phase 4 - 4 * Real.pi := by linarith [hw_lo]
  have hsq : (D3_phase 4 - 4 * Real.pi) ^ 2 ≤ (1.523 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hw_nn hw_hi 2
  have hcos_lo := Real.one_sub_sq_div_two_le_cos
    (x := D3_phase 4 - 4 * Real.pi)
  have hnum : (-0.16 : ℝ) ≤ 1 - (1.523 : ℝ) ^ 2 / 2 := by norm_num
  have hle : 1 - (1.523 : ℝ) ^ 2 / 2 ≤
      1 - (D3_phase 4 - 4 * Real.pi) ^ 2 / 2 := by linarith [hsq]
  have hwcos : (-0.16 : ℝ) ≤ Real.cos (D3_phase 4 - 4 * Real.pi) := by
    linarith [hcos_lo, hle, hnum]
  rw [hper] at hwcos
  exact hwcos

set_option maxHeartbeats 800000 in
/-- (C) Sine enclosure `sin θ₅ ∈ [0.89, 1]` (double-periodicity + cubic/linear,
    `w ∈ [1.482, 1.523]`). -/
theorem D3_sin_theta_five_mem :
    0.89 ≤ Real.sin (D3_phase 4) ∧ Real.sin (D3_phase 4) ≤ 1 := by
  have hmem := D3_delta_five_mem
  have hper1 : Real.sin (D3_phase 4 - 2 * Real.pi) = Real.sin (D3_phase 4) :=
    Real.sin_sub_two_pi _
  have hper2 : Real.sin ((D3_phase 4 - 2 * Real.pi) - 2 * Real.pi) =
      Real.sin (D3_phase 4 - 2 * Real.pi) :=
    Real.sin_sub_two_pi _
  have hper : Real.sin (D3_phase 4 - 4 * Real.pi) = Real.sin (D3_phase 4) := by
    have e : (D3_phase 4 - 2 * Real.pi) - 2 * Real.pi =
        D3_phase 4 - 4 * Real.pi := by ring
    rw [e] at hper2
    exact hper2.trans hper1
  have hw_lo := hmem.1
  have hw_hi := hmem.2
  have hw_nn : (0 : ℝ) ≤ D3_phase 4 - 4 * Real.pi := by linarith [hw_lo]
  have hsin_lo := Real.sin_ge_sub_cube hw_nn
  have hcube : (D3_phase 4 - 4 * Real.pi) ^ 3 ≤ (1.523 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hw_nn hw_hi 3
  have hnum : (0.89 : ℝ) ≤ 1.482 - (1.523 : ℝ) ^ 3 / 6 := by norm_num
  have hlo : (0.89 : ℝ) ≤ Real.sin (D3_phase 4 - 4 * Real.pi) := by
    have h1 : (1.482 : ℝ) - (1.523 : ℝ) ^ 3 / 6 ≤
        (D3_phase 4 - 4 * Real.pi) - (D3_phase 4 - 4 * Real.pi) ^ 3 / 6 := by
      linarith [hw_lo, hcube]
    linarith [hsin_lo, h1, hnum]
  have hhi : Real.sin (D3_phase 4 - 4 * Real.pi) ≤ 1 :=
    (Real.sin_mem_Icc _).2
  rw [hper] at hlo hhi
  exact ⟨hlo, hhi⟩

/-- (C) Trivial cosine lower `cos θ₆ ≥ -1`. -/
theorem D3_cos_theta_six_lower : -1 ≤ Real.cos (D3_phase 5) :=
  (Real.cos_mem_Icc _).1

set_option maxHeartbeats 800000 in
/-- (C) Cosine upper `cos θ₆ ≤ -0.99` (`cos_add_pi` shift + `cos_neg` + quadratic
    `1 - z²/2`, `z = 5π - θ₆ ≤ 0.073`). -/
theorem D3_cos_theta_six_upper : Real.cos (D3_phase 5) ≤ -0.99 := by
  have hmem := D3_delta_six_mem
  have hpi_lo := Real.pi_gt_d2
  have hpi_hi := Real.pi_lt_d2
  set y := D3_phase 5 - 4 * Real.pi - Real.pi with hy_def
  have hy_lo : (-0.073 : ℝ) ≤ y := by rw [hy_def]; linarith [hmem.1, hpi_hi]
  have hy_hi : y ≤ (-0.022 : ℝ) := by rw [hy_def]; linarith [hmem.2, hpi_lo]
  have hz_lo : (0.022 : ℝ) ≤ -y := by linarith [hy_hi]
  have hz_hi : -y ≤ (0.073 : ℝ) := by linarith [hy_lo]
  have hz_nn : (0 : ℝ) ≤ -y := by linarith [hz_lo]
  have hsq : (-y) ^ 2 ≤ (0.073 : ℝ) ^ 2 := pow_le_pow_left₀ hz_nn hz_hi 2
  have hcos_lo := Real.one_sub_sq_div_two_le_cos (x := -y)
  have hnum : (0.99 : ℝ) ≤ 1 - (0.073 : ℝ) ^ 2 / 2 := by norm_num
  have hcosz : (0.99 : ℝ) ≤ Real.cos (-y) := by
    have hle : 1 - (0.073 : ℝ) ^ 2 / 2 ≤ 1 - (-y) ^ 2 / 2 := by linarith [hsq]
    linarith [hcos_lo, hle, hnum]
  have hper1 : Real.cos (D3_phase 5 - 2 * Real.pi) = Real.cos (D3_phase 5) :=
    Real.cos_sub_two_pi _
  have hper2 : Real.cos ((D3_phase 5 - 2 * Real.pi) - 2 * Real.pi) =
      Real.cos (D3_phase 5 - 2 * Real.pi) :=
    Real.cos_sub_two_pi _
  have hper : Real.cos (D3_phase 5 - 4 * Real.pi) = Real.cos (D3_phase 5) := by
    have e : (D3_phase 5 - 2 * Real.pi) - 2 * Real.pi =
        D3_phase 5 - 4 * Real.pi := by ring
    rw [e] at hper2
    exact hper2.trans hper1
  have hdecomp : D3_phase 5 - 4 * Real.pi = y + Real.pi := by
    rw [hy_def]; ring
  have h1 : Real.cos (D3_phase 5 - 4 * Real.pi) = -Real.cos y := by
    rw [hdecomp, Real.cos_add_pi]
  have hcosy : Real.cos y = Real.cos (-y) := (Real.cos_neg y).symm
  have hcos_eq : Real.cos (D3_phase 5) = -Real.cos (-y) := by
    rw [← hper, h1, hcosy]
  linarith [hcos_eq, hcosz]

set_option maxHeartbeats 800000 in
/-- (C) Sine enclosure `sin θ₆ ∈ [0.02, 0.08]` (`sin_add_pi` shift + `sin_neg` +
    cubic/linear, `-y = 5π - θ₆ ∈ [0.022, 0.073]`). -/
theorem D3_sin_theta_six_mem :
    0.02 ≤ Real.sin (D3_phase 5) ∧ Real.sin (D3_phase 5) ≤ 0.08 := by
  have hmem := D3_delta_six_mem
  have hpi_lo := Real.pi_gt_d2
  have hpi_hi := Real.pi_lt_d2
  set y := D3_phase 5 - 4 * Real.pi - Real.pi with hy_def
  have hy_lo : (-0.073 : ℝ) ≤ y := by rw [hy_def]; linarith [hmem.1, hpi_hi]
  have hy_hi : y ≤ (-0.022 : ℝ) := by rw [hy_def]; linarith [hmem.2, hpi_lo]
  have hz_lo : (0.022 : ℝ) ≤ -y := by linarith [hy_hi]
  have hz_hi : -y ≤ (0.073 : ℝ) := by linarith [hy_lo]
  have hz_nn : (0 : ℝ) ≤ -y := by linarith [hz_lo]
  have hsin_lo := Real.sin_ge_sub_cube hz_nn
  have hsin_hi := Real.sin_le hz_nn
  have hcube : (-y) ^ 3 ≤ (0.073 : ℝ) ^ 3 := pow_le_pow_left₀ hz_nn hz_hi 3
  have hnum : (0.02 : ℝ) ≤ 0.022 - (0.073 : ℝ) ^ 3 / 6 := by norm_num
  have hlo : (0.02 : ℝ) ≤ Real.sin (-y) := by
    have h1 : (0.022 : ℝ) - (0.073 : ℝ) ^ 3 / 6 ≤
        (-y) - (-y) ^ 3 / 6 := by linarith [hz_lo, hcube]
    linarith [hsin_lo, h1, hnum]
  have hhi : Real.sin (-y) ≤ (0.08 : ℝ) := by
    have hle : Real.sin (-y) ≤ -y := hsin_hi
    linarith [hle, hz_hi]
  have hper1 : Real.sin (D3_phase 5 - 2 * Real.pi) = Real.sin (D3_phase 5) :=
    Real.sin_sub_two_pi _
  have hper2 : Real.sin ((D3_phase 5 - 2 * Real.pi) - 2 * Real.pi) =
      Real.sin (D3_phase 5 - 2 * Real.pi) :=
    Real.sin_sub_two_pi _
  have hper : Real.sin (D3_phase 5 - 4 * Real.pi) = Real.sin (D3_phase 5) := by
    have e : (D3_phase 5 - 2 * Real.pi) - 2 * Real.pi =
        D3_phase 5 - 4 * Real.pi := by ring
    rw [e] at hper2
    exact hper2.trans hper1
  have hdecomp : D3_phase 5 - 4 * Real.pi = y + Real.pi := by
    rw [hy_def]; ring
  have h1s : Real.sin (D3_phase 5 - 4 * Real.pi) = -Real.sin y := by
    rw [hdecomp, Real.sin_add_pi]
  have hnegy : Real.sin y = -Real.sin (-y) := by
    have h := Real.sin_neg y
    linarith [h]
  have hsin_eq : Real.sin (D3_phase 5) = Real.sin (-y) := by
    rw [← hper, h1s, hnegy, neg_neg]
  rw [hsin_eq]
  exact ⟨hlo, hhi⟩

set_option maxHeartbeats 800000 in
/-- (C) Amplitude upper `D3_amp 4 ≤ 2/5` (via `5^{3/5} ≥ 5/2`,
    cleared: `(5/2)^5 ≤ 125 = 5^3`, since `3/5 ≤ 0.605`). -/
theorem D3_amp_five_upper : D3_amp 4 ≤ 2 / 5 := by
  unfold D3_amp
  have hcast : ((((4 : ℕ)) : ℝ) + 1 : ℝ) = 5 := by norm_num
  rw [hcast]
  have h35 : (3 / 5 : ℝ) ≤ (0.605 : ℝ) := by norm_num
  have hmono : (5 : ℝ) ^ ((3 / 5 : ℝ)) ≤ (5 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h35
  have hpow : ((5 / 2 : ℝ)) ^ ((5 : ℕ))
      ≤ ((((5 : ℝ) ^ ((3 / 5 : ℝ)))) ^ ((5 : ℕ)) : ℝ) := by
    have e : ((((5 : ℝ) ^ ((3 / 5 : ℝ)))) ^ ((5 : ℕ)) : ℝ)
        = (5 : ℝ) ^ ((3 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5)]
      rw [show (3 / 5 : ℝ) * (((5 : ℕ)) : ℝ) = (3 : ℝ) by norm_num]
      rw [show (3 : ℝ) = (((3 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 5 3
    rw [e]
    norm_num
  have hstep : (5 / 2 : ℝ) ≤ (5 : ℝ) ^ ((3 / 5 : ℝ)) :=
    le_of_pow_le_pow_left₀ (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _).le hpow
  have h5ge : (5 / 2 : ℝ) ≤ (5 : ℝ) ^ (0.605 : ℝ) := le_trans hstep hmono
  have hpos : (0 : ℝ) < (5 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have e : (-0.605 : ℝ) = -(0.605 : ℝ) := by norm_num
  rw [e, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 5)]
  have heq : (2 / 5 : ℝ) = ((5 / 2 : ℝ))⁻¹ := by norm_num
  rw [heq]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr h5ge

set_option maxHeartbeats 800000 in
/-- (C) Amplitude lower `1/3 ≤ D3_amp 4` (via `5^{2/3} ≤ 3`,
    cleared: `5^2 = 25 ≤ 27 = 3^3`, since `0.605 ≤ 2/3`). -/
theorem D3_amp_five_lower : 1 / 3 ≤ D3_amp 4 := by
  unfold D3_amp
  have hcast : ((((4 : ℕ)) : ℝ) + 1 : ℝ) = 5 := by norm_num
  rw [hcast]
  have h65 : (0.605 : ℝ) ≤ 2 / 3 := by norm_num
  have hmono : (5 : ℝ) ^ (0.605 : ℝ) ≤ (5 : ℝ) ^ ((2 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h65
  have hpow : ((((5 : ℝ) ^ ((2 / 3 : ℝ)))) ^ ((3 : ℕ)) : ℝ)
      ≤ (((3 : ℝ)) ^ ((3 : ℕ))) := by
    have e : ((((5 : ℝ) ^ ((2 / 3 : ℝ)))) ^ ((3 : ℕ)) : ℝ)
        = (5 : ℝ) ^ ((2 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5)]
      rw [show (2 / 3 : ℝ) * (((3 : ℕ)) : ℝ) = (2 : ℝ) by norm_num]
      rw [show (2 : ℝ) = (((2 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 5 2
    rw [e]
    norm_num
  have hstep : (5 : ℝ) ^ ((2 / 3 : ℝ)) ≤ 3 :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  have h5le : (5 : ℝ) ^ (0.605 : ℝ) ≤ 3 := le_trans hmono hstep
  have hpos : (0 : ℝ) < (5 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have e : (-0.605 : ℝ) = -(0.605 : ℝ) := by norm_num
  rw [e, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 5)]
  have heq : (1 / 3 : ℝ) = ((3 : ℝ))⁻¹ := by norm_num
  rw [heq]
  exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 3) hpos).mpr h5le

set_option maxHeartbeats 800000 in
/-- (C) Amplitude upper `D3_amp 5 ≤ 3/8` (via `6^{3/5} ≥ 8/3`,
    cleared: `(8/3)^5 ≤ 216 = 6^3`, since `3/5 ≤ 0.605`). -/
theorem D3_amp_six_upper : D3_amp 5 ≤ 3 / 8 := by
  unfold D3_amp
  have hcast : ((((5 : ℕ)) : ℝ) + 1 : ℝ) = 6 := by norm_num
  rw [hcast]
  have h35 : (3 / 5 : ℝ) ≤ (0.605 : ℝ) := by norm_num
  have hmono : (6 : ℝ) ^ ((3 / 5 : ℝ)) ≤ (6 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h35
  have hpow : ((8 / 3 : ℝ)) ^ ((5 : ℕ))
      ≤ ((((6 : ℝ) ^ ((3 / 5 : ℝ)))) ^ ((5 : ℕ)) : ℝ) := by
    have e : ((((6 : ℝ) ^ ((3 / 5 : ℝ)))) ^ ((5 : ℕ)) : ℝ)
        = (6 : ℝ) ^ ((3 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
      rw [show (3 / 5 : ℝ) * (((5 : ℕ)) : ℝ) = (3 : ℝ) by norm_num]
      rw [show (3 : ℝ) = (((3 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 6 3
    rw [e]
    norm_num
  have hstep : (8 / 3 : ℝ) ≤ (6 : ℝ) ^ ((3 / 5 : ℝ)) :=
    le_of_pow_le_pow_left₀ (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _).le hpow
  have h6ge : (8 / 3 : ℝ) ≤ (6 : ℝ) ^ (0.605 : ℝ) := le_trans hstep hmono
  have hpos : (0 : ℝ) < (6 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have e : (-0.605 : ℝ) = -(0.605 : ℝ) := by norm_num
  rw [e, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 6)]
  have heq : (3 / 8 : ℝ) = ((8 / 3 : ℝ))⁻¹ := by norm_num
  rw [heq]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr h6ge

set_option maxHeartbeats 800000 in
/-- (C) Amplitude lower `3/10 ≤ D3_amp 5` (via `6^{2/3} ≤ 10/3`,
    cleared: `6^2 = 36 ≤ 1000/27 = (10/3)^3`, since `0.605 ≤ 2/3`). -/
theorem D3_amp_six_lower : 3 / 10 ≤ D3_amp 5 := by
  unfold D3_amp
  have hcast : ((((5 : ℕ)) : ℝ) + 1 : ℝ) = 6 := by norm_num
  rw [hcast]
  have h65 : (0.605 : ℝ) ≤ 2 / 3 := by norm_num
  have hmono : (6 : ℝ) ^ (0.605 : ℝ) ≤ (6 : ℝ) ^ ((2 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h65
  have hpow : ((((6 : ℝ) ^ ((2 / 3 : ℝ)))) ^ ((3 : ℕ)) : ℝ)
      ≤ (((10 / 3 : ℝ)) ^ ((3 : ℕ))) := by
    have e : ((((6 : ℝ) ^ ((2 / 3 : ℝ)))) ^ ((3 : ℕ)) : ℝ)
        = (6 : ℝ) ^ ((2 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
      rw [show (2 / 3 : ℝ) * (((3 : ℕ)) : ℝ) = (2 : ℝ) by norm_num]
      rw [show (2 : ℝ) = (((2 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 6 2
    rw [e]
    norm_num
  have hstep : (6 : ℝ) ^ ((2 / 3 : ℝ)) ≤ 10 / 3 :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  have h6le : (6 : ℝ) ^ (0.605 : ℝ) ≤ 10 / 3 := le_trans hmono hstep
  have hpos : (0 : ℝ) < (6 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have e : (-0.605 : ℝ) = -(0.605 : ℝ) := by norm_num
  rw [e, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 6)]
  have heq : (3 / 10 : ℝ) = ((10 / 3 : ℝ))⁻¹ := by norm_num
  rw [heq]
  exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 10 / 3) hpos).mpr h6le

/-- (C) Fifth-term real-part lower `≥ -2/5` (interval: `amp ≤ 2/5`,
    `cos ≥ -1`; even `k = 4`). -/
theorem D3_term4_re_lo :
    (-2 / 5 : ℝ) ≤ (etaDirichletTerm (1 - zetaCellS0) 4).re := by
  rw [D3_eta_re]
  have hamp := D3_amp_five_upper
  have hcos_lo : (-1 : ℝ) ≤ Real.cos (D3_phase 4) := (Real.cos_mem_Icc _).1
  have hamp_nn : (0 : ℝ) ≤ D3_amp 4 := D3_amp_nonneg 4
  have hpow4 : ((-1 : ℝ) ^ (4 : ℕ)) = 1 := by
    have e42 : (4 : ℕ) = 2 + 2 := rfl
    have hpow2 : ((-1 : ℝ) ^ (2 : ℕ)) = 1 := by norm_num [pow_two]
    rw [e42, pow_add, hpow2, mul_one]
  rw [hpow4, one_mul]
  have h : (-(2 / 5) : ℝ) ≤ D3_amp 4 * Real.cos (D3_phase 4) := by
    have h1 : D3_amp 4 * (-1) ≤ D3_amp 4 * Real.cos (D3_phase 4) :=
      mul_le_mul_of_nonneg_left hcos_lo hamp_nn
    linarith [h1, hamp]
  linarith [h]

/-- (C) Sixth-term real-part lower `≥ -3/8` (interval: `amp ≤ 3/8`,
    `cos ≤ 1`, no positivity assumption; odd `k = 5`). -/
theorem D3_term5_re_lo :
    (-3 / 8 : ℝ) ≤ (etaDirichletTerm (1 - zetaCellS0) 5).re := by
  rw [D3_eta_re]
  have hamp := D3_amp_six_upper
  have hcos_le : Real.cos (D3_phase 5) ≤ 1 := (Real.cos_mem_Icc _).2
  have hamp_nn : (0 : ℝ) ≤ D3_amp 5 := D3_amp_nonneg 5
  have hprod : D3_amp 5 * Real.cos (D3_phase 5) ≤ 3 / 8 := by
    have h1 : D3_amp 5 * Real.cos (D3_phase 5) ≤ D3_amp 5 * 1 :=
      mul_le_mul_of_nonneg_left hcos_le hamp_nn
    linarith [h1, hamp]
  have hpow4 : ((-1 : ℝ) ^ (4 : ℕ)) = 1 := by
    have e42 : (4 : ℕ) = 2 + 2 := rfl
    have hpow2 : ((-1 : ℝ) ^ (2 : ℕ)) = 1 := by norm_num [pow_two]
    rw [e42, pow_add, hpow2, mul_one]
  have hpow5 : ((-1 : ℝ) ^ (5 : ℕ)) = -1 := by
    have e51 : (5 : ℕ) = 4 + 1 := rfl
    rw [e51, pow_add, hpow4, pow_one, one_mul]
  rw [hpow5]
  linarith [hprod]

/-- (C) `S_6` real-part lower `≥ -37/24` via the interval framework
    (`1 - 2/3 - 3/5 - 1/2 - 2/5 - 3/8`, à la `D3_S4_re_lower`). -/
theorem D3_S6_re_lower :
    (-37 / 24 : ℝ) ≤
      (∑ k ∈ Finset.range 6, etaDirichletTerm (1 - zetaCellS0) k).re := by
  rw [D3_sum_re_eq]
  have h6 : (∑ k ∈ Finset.range 6, (etaDirichletTerm (1 - zetaCellS0) k).re) =
      (etaDirichletTerm (1 - zetaCellS0) 0).re +
      (etaDirichletTerm (1 - zetaCellS0) 1).re +
      (etaDirichletTerm (1 - zetaCellS0) 2).re +
      (etaDirichletTerm (1 - zetaCellS0) 3).re +
      (etaDirichletTerm (1 - zetaCellS0) 4).re +
      (etaDirichletTerm (1 - zetaCellS0) 5).re := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
  rw [h6, D3_term0_re]
  have h1 := D3_term1_re_lo
  have h2 := D3_term2_re_lo
  have h3 := D3_term3_re_lo
  have h4 := D3_term4_re_lo
  have h5 := D3_term5_re_lo
  linarith

/-- (F2) Explicit per-term Re lowers for `S_6` (sums to `-37/24`). -/
def D3_S6_lo : ℕ → ℝ := fun k =>
  if k = 0 then 1 else if k = 1 then -2 / 3 else if k = 2 then -3 / 5
    else if k = 3 then -1 / 2 else if k = 4 then -2 / 5 else -3 / 8

/-- (F2) The `S_6` lo-sum is `-37/24`. -/
theorem D3_S6_lo_sum : ∑ k ∈ Finset.range 6, D3_S6_lo k = (-37 / 24 : ℝ) := by
  have v0 : D3_S6_lo 0 = (1 : ℝ) := by simp [D3_S6_lo]
  have v1 : D3_S6_lo 1 = (-2 / 3 : ℝ) := by simp [D3_S6_lo]
  have v2 : D3_S6_lo 2 = (-3 / 5 : ℝ) := by simp [D3_S6_lo]
  have v3 : D3_S6_lo 3 = (-1 / 2 : ℝ) := by simp [D3_S6_lo]
  have v4 : D3_S6_lo 4 = (-2 / 5 : ℝ) := by simp [D3_S6_lo]
  have v5 : D3_S6_lo 5 = (-3 / 8 : ℝ) := by simp [D3_S6_lo]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, v0, v1, v2, v3, v4, v5]
  norm_num

/-- (F2) The `S_6` lo-values bound the term real parts below. -/
theorem D3_S6_lo_valid (k : ℕ) (hk : k < 6) :
    D3_S6_lo k ≤ (etaDirichletTerm (1 - zetaCellS0) k).re := by
  have v0 : D3_S6_lo 0 = (1 : ℝ) := by simp [D3_S6_lo]
  have v1 : D3_S6_lo 1 = (-2 / 3 : ℝ) := by simp [D3_S6_lo]
  have v2 : D3_S6_lo 2 = (-3 / 5 : ℝ) := by simp [D3_S6_lo]
  have v3 : D3_S6_lo 3 = (-1 / 2 : ℝ) := by simp [D3_S6_lo]
  have v4 : D3_S6_lo 4 = (-2 / 5 : ℝ) := by simp [D3_S6_lo]
  have v5 : D3_S6_lo 5 = (-3 / 8 : ℝ) := by simp [D3_S6_lo]
  interval_cases k
  · rw [v0, D3_term0_re]
  · rw [v1]
    exact D3_term1_re_lo
  · rw [v2]
    exact D3_term2_re_lo
  · rw [v3]
    exact D3_term3_re_lo
  · rw [v4]
    exact D3_term4_re_lo
  · rw [v5]
    exact D3_term5_re_lo

/-- (F2) `S_6` norm lower `≥ -37/24` through `D3_block_norm_ge_sum_lo`. -/
theorem D3_S6_norm_ge :
    (-37 / 24 : ℝ) ≤
      ‖∑ k ∈ Finset.range 6, etaDirichletTerm (1 - zetaCellS0) k‖ := by
  have h := D3_block_norm_ge_sum_lo 6 D3_S6_lo D3_S6_lo_valid
  rw [D3_S6_lo_sum] at h
  exact h

/-- (P) `S_{1024}` conditional from the `S_6` interval lower. -/
theorem D3_S1024_of_S6 (U : ℝ)
    (hU : ‖∑ k ∈ Finset.Ico 6 1024, etaDirichletTerm (1 - zetaCellS0) k‖ ≤ U) :
    (-37 / 24 - U : ℝ) ≤
      ‖∑ k ∈ Finset.range 1024, etaDirichletTerm (1 - zetaCellS0) k‖ :=
  D3_S1024_split_lower 6 (by norm_num) (-37 / 24) U D3_S6_norm_ge hU

/-- (P) The `S_6` Re-route CANNOT reach `8/15` via splitting
    (needs `U ≤ -37/24 - 8/15 < 0`). -/
theorem D3_S6_cannot_reach_8_15 (U : ℝ) (hU : 0 ≤ U) :
    (-37 / 24 - U : ℝ) < 8 / 15 := by
  have h : (-37 / 24 : ℝ) < 8 / 15 := by norm_num
  linarith

#print axioms D3_log_six_eq
#print axioms D3_phase_four_eq
#print axioms D3_phase_five_eq
#print axioms D3_theta_five_lo
#print axioms D3_theta_five_hi
#print axioms D3_theta_six_lo
#print axioms D3_theta_six_hi
#print axioms D3_delta_five_mem
#print axioms D3_delta_six_mem
#print axioms D3_cos_theta_five_le_one
#print axioms D3_cos_theta_five_lower
#print axioms D3_sin_theta_five_mem
#print axioms D3_cos_theta_six_lower
#print axioms D3_cos_theta_six_upper
#print axioms D3_sin_theta_six_mem
#print axioms D3_amp_five_upper
#print axioms D3_amp_five_lower
#print axioms D3_amp_six_upper
#print axioms D3_amp_six_lower
#print axioms D3_term4_re_lo
#print axioms D3_term5_re_lo
#print axioms D3_S6_re_lower
#print axioms D3_S6_lo_sum
#print axioms D3_S6_lo_valid
#print axioms D3_S6_norm_ge
#print axioms D3_S1024_of_S6
#print axioms D3_S6_cannot_reach_8_15

/-!

## Door-3 prime-log d9 block (D3, tier 1): `log 7/11/13` enclosures (±1e-10).

GOAL (door-3 K=16 premise; minimum viable prime-log unlocks in order 7, 11, 13):
rigorous d9-grade `Real.log` enclosures for 7, 11, 13, both directions, ~1e-9 tight
like the committed `Real.log_five_gt/lt_d9` — in the exact shape BE's template consumes
(`log_X_gt_d9` / `log_X_lt_d9` names, here `Real.log_seven/eleven/thirteen_gt/lt_d9`;
the follower writes `D3_theta_seven_lo/hi` exactly like `D3_theta_five_lo/hi`).
Bounds only — no θ-phases here. Pair-absolute/Tendsto forms only; no `∑'`-with-`0 <`
(this block uses no `∑'` at all; the only sums are `Finset.range`).

GREP-FIRST RECORD (run before writing; method mirrored numeral-for-numeral):
* `Real.log_five_near_10` (`|log 5 - 160943791243/100000000000| ≤ 1/10^10`),
  `Real.log_five_gt_d9` (`1.6094379123 < log 5`), `Real.log_five_lt_d9`
  (`log 5 < 1.6094379126`) — `Mathlib/Analysis/Complex/ExponentialBounds.lean:109-125`,
  namespace `Real`. EXIST; proof shape copied exactly (`suffices` tail-split,
  `norm_num1 at *` + `assumption` (`log 7`), `Real.abs_log_sub_add_sum_range_le` at
  `x = (p-1)/p`, rewrite chain `1 - x = 1/p`, `Real.log_inv`, `abs_sub_le` split,
  `norm_num [Finset.sum_range_succ]`; `Finset.`/`Real.` qualified because this file
  does not `open Finset` and sits outside `namespace Real`).
  Adaptations for the 285/340-term sums (`11`, `13`): the split is closed by the
  `ring` identity `X + (C - X) = C` with an explicit `: ℝ` ascription (`norm_num1`
  evaluates the 150-digit `(6/7)^176` tail but leaves the 300/380-digit tails
  symbolic, so `assumption` misses; the bare `have` elaborated at `ℕ`), and
  `set_option exponentiation.threshold 1024 in` (default 256 refuses to evaluate
  `(10/11)^286`/`(12/13)^341`, which stalled the exact-sum combination) plus raised
  `maxHeartbeats`, both preceding the docstring (`log 7` needs neither; a split
  `simp only` unfold instead hits `maxRecDepth`).
* `Real.log_two/three_near_10|gt_d9|lt_d9` — same file `:71-105`. EXIST (untouched).
* `log_seven|log_eleven|log_thirteen` — ABSENT in `Mathlib/` (0 hits; only
  `log_two/three/five` d9 enclosures exist) and ABSENT in `zeta_rigorous.lean`
  (0 hits outside doc prose); hence created in-file below. No Mathlib edit.
* In-file consumers waiting: `D3_theta_five_lo/hi` (the template),
  `D3_log_six_eq` (composite bridge via `Real.log_mul`). Nothing redefined.

NUMBERS (proved below; true values `math.log` python scratch for this report only):
* `log 7 ∈ (1.9459101489, 1.9459101492)` (true `≈ 1.9459101490553`); width `3e-10`;
  slacks lower `≈1.55e-10`, upper `≈1.45e-10`.
  (`x = 6/7`, `n = 175`, tail `(6/7)^176/7⁻¹ ≈ 1.16e-11`,
  `|S - approx| ≈ 4.8e-12`; total `≈1.63e-11 ≤ 1e-10`, margin `≈6×`.)
* `log 11 ∈ (2.3978952726, 2.3978952730)` (true `≈ 2.3978952727984`); width `4e-10`;
  slacks lower `≈1.98e-10`, upper `≈2.02e-10`.
  (`x = 10/11`, `n = 285`, tail `(10/11)^286/11⁻¹ ≈ 1.60e-11`,
  `|S - approx| ≈ 1.7e-12`; total `≈1.77e-11 ≤ 1e-10`, margin `≈5×`.)
  (One extra ulp of width: the true-rounded approx `239789527280/1e11` sits exactly
  on the `1e-10` grid, so strict 10dp bounds need the wider pair; still ~1e-9 grade.)
* `log 13 ∈ (2.5649493573, 2.5649493576)` (true `≈ 2.5649493574615`); width `3e-10`;
  slacks lower `≈1.62e-10`, upper `≈1.38e-10`.
  (`x = 12/13`, `n = 340`, tail `(12/13)^341/13⁻¹ ≈ 1.82e-11`,
  `|S - approx| ≈ 1.5e-12`; total `≈1.97e-11 ≤ 1e-10`, margin `≈5×`.)

RESIDUAL (report-and-stop): θ₇ unlocks immediately — follower proves
`D3_theta_seven_lo/hi` (`θ₇ = 8.75·log 7 ∈ [17.026, 17.027]`, true `≈ 17.0267138`)
from `Real.log_seven_gt/lt_d9` exactly like `D3_theta_five_lo/hi`; then θ₁₁, θ₁₃.
Composites 8/9/10/12/14/15/16 factor through the log 2/3/5 bridges (no new logs).
-/

/-- (C) `log 7` near-10 enclosure (mirrors `Real.log_five_near_10`
    numeral-for-numeral: `x = 6/7`, `n = 175`). -/
theorem Real.log_seven_near_10 :
    |Real.log 7 - 194591014906 / 100000000000| ≤ 1 / 10 ^ 10 := by
  suffices |Real.log 7 - 194591014906 / 100000000000| ≤
      (6 / 7) ^ 176 / 7⁻¹ + (1 / 10 ^ 10 - (6 / 7) ^ 176 / 7⁻¹) by
    norm_num1 at *
    assumption
  have t : |6 / 7| = (6 : ℝ) / 7 := by norm_num
  have z := Real.abs_log_sub_add_sum_range_le (x := (6 / 7 : ℝ)) (by norm_num) 175
  rw [t, show (1 - (6 : ℝ) / 7) = (1 / 7 : ℝ) by norm_num, one_div (7 : ℝ),
    Real.log_inv, ← sub_eq_add_neg, _root_.abs_sub_comm] at z
  apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _)
  norm_num [Finset.sum_range_succ]

/-- (C) `log 7` lower d9 bound (mirrors `Real.log_two/three/five_gt_d9`). -/
theorem Real.log_seven_gt_d9 : 1.9459101489 < Real.log 7 :=
  lt_of_lt_of_le (by norm_num1)
    (sub_le_comm.1 (abs_sub_le_iff.1 Real.log_seven_near_10).2)

/-- (C) `log 7` upper d9 bound (mirrors `Real.log_two/three/five_lt_d9`). -/
theorem Real.log_seven_lt_d9 : Real.log 7 < 1.9459101492 :=
  lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 Real.log_seven_near_10).1)
    (by norm_num)

set_option exponentiation.threshold 1024 in
set_option maxHeartbeats 2000000 in
/-- (C) `log 11` near-10 enclosure (mirrors `Real.log_five_near_10`
    numeral-for-numeral: `x = 10/11`, `n = 285`). -/
theorem Real.log_eleven_near_10 :
    |Real.log 11 - 239789527280 / 100000000000| ≤ 1 / 10 ^ 10 := by
  suffices h : |Real.log 11 - 239789527280 / 100000000000| ≤
      (10 / 11) ^ 286 / 11⁻¹ + (1 / 10 ^ 10 - (10 / 11) ^ 286 / 11⁻¹) by
    have heq : ((10 / 11) ^ 286 / 11⁻¹ + (1 / 10 ^ 10 - (10 / 11) ^ 286 / 11⁻¹) : ℝ)
        = 1 / 10 ^ 10 := by ring
    rwa [heq] at h
  have t : |10 / 11| = (10 : ℝ) / 11 := by norm_num
  have z := Real.abs_log_sub_add_sum_range_le (x := (10 / 11 : ℝ)) (by norm_num) 285
  rw [t, show (1 - (10 : ℝ) / 11) = (1 / 11 : ℝ) by norm_num, one_div (11 : ℝ),
    Real.log_inv, ← sub_eq_add_neg, _root_.abs_sub_comm] at z
  apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _)
  norm_num [Finset.sum_range_succ]

/-- (C) `log 11` lower d9 bound (mirrors `Real.log_two/three/five_gt_d9`). -/
theorem Real.log_eleven_gt_d9 : 2.3978952726 < Real.log 11 :=
  lt_of_lt_of_le (by norm_num1)
    (sub_le_comm.1 (abs_sub_le_iff.1 Real.log_eleven_near_10).2)

/-- (C) `log 11` upper d9 bound (mirrors `Real.log_two/three/five_lt_d9`). -/
theorem Real.log_eleven_lt_d9 : Real.log 11 < 2.3978952730 :=
  lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 Real.log_eleven_near_10).1)
    (by norm_num)

set_option exponentiation.threshold 1024 in
set_option maxHeartbeats 2000000 in
/-- (C) `log 13` near-10 enclosure (mirrors `Real.log_five_near_10`
    numeral-for-numeral: `x = 12/13`, `n = 340`). -/
theorem Real.log_thirteen_near_10 :
    |Real.log 13 - 256494935746 / 100000000000| ≤ 1 / 10 ^ 10 := by
  suffices h : |Real.log 13 - 256494935746 / 100000000000| ≤
      (12 / 13) ^ 341 / 13⁻¹ + (1 / 10 ^ 10 - (12 / 13) ^ 341 / 13⁻¹) by
    have heq : ((12 / 13) ^ 341 / 13⁻¹ + (1 / 10 ^ 10 - (12 / 13) ^ 341 / 13⁻¹) : ℝ)
        = 1 / 10 ^ 10 := by ring
    rwa [heq] at h
  have t : |12 / 13| = (12 : ℝ) / 13 := by norm_num
  have z := Real.abs_log_sub_add_sum_range_le (x := (12 / 13 : ℝ)) (by norm_num) 340
  rw [t, show (1 - (12 : ℝ) / 13) = (1 / 13 : ℝ) by norm_num, one_div (13 : ℝ),
    Real.log_inv, ← sub_eq_add_neg, _root_.abs_sub_comm] at z
  apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _)
  norm_num [Finset.sum_range_succ]

/-- (C) `log 13` lower d9 bound (mirrors `Real.log_two/three/five_gt_d9`). -/
theorem Real.log_thirteen_gt_d9 : 2.5649493573 < Real.log 13 :=
  lt_of_lt_of_le (by norm_num1)
    (sub_le_comm.1 (abs_sub_le_iff.1 Real.log_thirteen_near_10).2)

/-- (C) `log 13` upper d9 bound (mirrors `Real.log_two/three/five_lt_d9`). -/
theorem Real.log_thirteen_lt_d9 : Real.log 13 < 2.5649493576 :=
  lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 Real.log_thirteen_near_10).1)
    (by norm_num)

#print axioms Real.log_seven_near_10
#print axioms Real.log_seven_gt_d9
#print axioms Real.log_seven_lt_d9
#print axioms Real.log_eleven_near_10
#print axioms Real.log_eleven_gt_d9
#print axioms Real.log_eleven_lt_d9
#print axioms Real.log_thirteen_near_10
#print axioms Real.log_thirteen_gt_d9
#print axioms Real.log_thirteen_lt_d9

/-!

## Door-3 `S_7` + `θ₁₁`/`θ₁₃` interval blocks (D3, tier 1): prime phases 7/11/13 + `S_7` sum.

GOAL (door-3 K=16 premise; minimum viable prime unlocks in order 7, 11, 13):
rigorous per-term cpow enclosures for `k = 6, 10, 12` (`x = 7, 11, 13`) in BE's
exact shapes (`D3_theta_seven_lo/hi` etc. mirroring `D3_theta_five_lo/hi`;
`D3_phase_six_eq` mirroring `D3_phase_four_eq` prime pattern; delta/cos/sin/amp/
term-Re lowers mirroring the `S_2`/`S_4`/`S_6` template), plus the running `S_7`
partial lower through `D3_block_norm_ge_sum_lo`. Pair-absolute/Tendsto forms
only; no `∑'`-with-`0 <` (all sums are `Finset.range`).

GREP-FIRST RECORD (run before writing; repo `zeta_rigorous.lean` + `Mathlib/`):
* `Real.log_seven_gt/lt_d9` (`:7592`/`:7597`), `Real.log_eleven_gt/lt_d9`
  (`:7620`/`:7625`), `Real.log_thirteen_gt/lt_d9` (`:7648`/`:7653`) — EXIST
  (BI prime-log block, committed `cd4513aa`); consumed for `θ₇/θ₁₁/θ₁₃`
  exactly like `D3_theta_five_lo/hi` consumes `log_five_d9`.
* `D3_theta_seven|D3_theta_eleven|D3_theta_thirteen|D3_phase_six_eq|
  D3_phase_ten_eq|D3_phase_twelve_eq|D3_amp_seven|D3_amp_eleven|D3_amp_thirteen|
  D3_term6_re_lo|D3_term10_re_lo|D3_term12_re_lo|D3_S7_|D3_S1024_of_S7|
  D3_delta_seven|D3_cos_theta_seven|D3_sin_theta_seven` (+ eleven/thirteen
  variants) — 0 hits outside doc prose (only the BI residual mentions
  `D3_theta_seven_lo/hi` at `:7526`/`:7571`); hence all names below are new.
* Trig/rpow/pi lemmas — the same EXIST set the `S_6` template documents
  (`cos_sub_two_pi`, `sin_sub_two_pi`, `cos_add_pi`, `sin_add_pi`, `cos_neg`,
  `sin_neg`, `cos_mem_Icc`/`sin_mem_Icc`, `one_sub_sq_div_two_le_cos`,
  `sin_ge_sub_cube`, `sin_le`, `pi_gt_d2`/`pi_lt_d2`, `le_of_pow_le_pow_left₀`,
  `pow_le_pow_left₀`, `rpow_le_rpow_of_exponent_le`, `mul_le_mul_of_nonneg_left`,
  `mul_lt_mul_of_pos_left`, `inv_le_inv₀`, `rpow_neg/natCast/mul`; every one
  already used in this file, reused numeral-for-numeral).
* In-file reuse (read-only): `D3_amp`/`D3_phase`/`D3_eta_re` (`:5910`-`:6013`),
  `D3_sum_re_eq`/`D3_block_norm_ge_sum_lo`/`D3_S1024_split_lower`
  (`:6016`-`:6057`), `D3_amp_nonneg`, `D3_term0_re`, `D3_term1/2/3/4/5_re_lo`,
  `D3_S6_lo`/`D3_S6_lo_sum` (`:7428`-`:7444`). Nothing redefined.

WHAT IS PROVED (all unconditional, FULL proofs, no `sorry`/`admit`/`axiom`):
* (C) Phase identities (prime pattern): `D3_phase_six_eq`/`D3_phase_ten_eq`/
  `D3_phase_twelve_eq` (`D3_phase k = 8.75·log(k+1)` for `k = 6, 10, 12`).
* (C) Phase enclosures: `D3_theta_seven_lo/hi` (`θ₇ ∈ [17.026, 17.027]`),
  `D3_theta_eleven_lo/hi` (`θ₁₁ ∈ [20.981, 20.982]`),
  `D3_theta_thirteen_lo/hi` (`θ₁₃ ∈ [22.443, 22.444]`).
* (C) Reduction + trig (BE shapes): `D3_delta_seven_mem`
  (`θ₇ - 4π ∈ [4.426, 4.467]`), `D3_delta_eleven_mem`
  (`θ₁₁ - 6π ∈ [2.081, 2.142]`), `D3_delta_thirteen_mem`
  (`θ₁₃ - 6π ∈ [3.543, 3.604]`); trivial cos lowers + `cos_add_pi`-shifted
  uppers (`-0.11`/`-0.42`/`-0.89` via quadratic on `y = δ - π`);
  `D3_sin_theta_seven_mem` (`∈ [-1, -0.88]`), `D3_sin_theta_eleven_mem`
  (`∈ [0.79, 1]`), `D3_sin_theta_thirteen_mem` (`∈ [-0.47, -0.37]`).
* (C) Amplitudes: `7^{-0.605} ∈ [1/4, 1/3]`, `11^{-0.605} ∈ [1/5, 1/4]`,
  `13^{-0.605} ∈ [1/6, 1/4]` (via `p^5 ≤ x^3` / `x^2 ≤ q^3` cleared forms).
* (F2) Term + sum (trivial-cos shapes à la `D3_term4_re_lo`, even `k`):
  `D3_term6_re_lo` (`≥ -1/3`), `D3_term10_re_lo` (`≥ -1/4`),
  `D3_term12_re_lo` (`≥ -1/4`); `D3_S7_re_lower` (`≥ -15/8`),
  `D3_S7_lo`/`D3_S7_lo_sum`/`D3_S7_lo_valid` + `D3_S7_norm_ge` (through
  `D3_block_norm_ge_sum_lo`), `D3_S1024_of_S7` + `D3_S7_cannot_reach_8_15`.

NUMBERS (exact, proved in-file; python scratch only for this report):
* `θ₇ = 8.75·log 7 ∈ [17.026, 17.027]` (true `≈ 17.0267138042`);
  `δ₇ = θ₇ - 4π ∈ [4.426, 4.467]` (true `≈ 4.4603431899`);
  `y₇ = δ₇ - π ∈ [1.276, 1.327]` (true `≈ 1.3187505363`);
  `cos θ₇ ∈ [-1, -0.11]` (true `≈ -0.2493856320`);
  `sin θ₇ ∈ [-1, -0.88]` (true `≈ -0.9684042578`).
* `θ₁₁ = 8.75·log 11 ∈ [20.981, 20.982]` (true `≈ 20.9815836370`);
  `δ₁₁ = θ₁₁ - 6π ∈ [2.081, 2.142]` (true `≈ 2.1320277154`);
  `z₁₁ = 7π - θ₁₁ ∈ [0.998, 1.069]` (true `≈ 1.0095649381`);
  `cos θ₁₁ ∈ [-1, -0.42]` (true `≈ -0.5322290953`);
  `sin θ₁₁ ∈ [0.79, 1]` (true `≈ 0.8466003722`).
* `θ₁₃ = 8.75·log 13 ∈ [22.443, 22.444]` (true `≈ 22.4433068778`);
  `δ₁₃ = θ₁₃ - 6π ∈ [3.543, 3.604]` (true `≈ 3.5937509562`);
  `y₁₃ = δ₁₃ - π ∈ [0.393, 0.464]` (true `≈ 0.4521583027`);
  `cos θ₁₃ ∈ [-1, -0.89]` (true `≈ -0.8995062186`);
  `sin θ₁₃ ∈ [-0.47, -0.37]` (true `≈ -0.4369079569`).
* `7^{-0.605} ∈ [1/4, 1/3]` (true `≈ 0.3081170178`);
  `11^{-0.605} ∈ [1/5, 1/4]` (true `≈ 0.2343999018`);
  `13^{-0.605} ∈ [1/6, 1/4]` (true `≈ 0.2118674658`).
* Term Re lowers: `t₆ ≥ -1/3` (true `≈ -0.0768399572`),
  `t₁₀ ≥ -1/4` (true `≈ -0.1247544477`), `t₁₂ ≥ -1/4` (true `≈ -0.1905761030`);
  `Re S_7 ≥ -15/8 = -1.875` (true `≈ -0.2571929473`, `|S_7| ≈ 0.3931399260`).

RESIDUAL (exact, quantified -- report-and-stop, no spin):
* The `S_7` Re-sum lower `-15/8` is NEGATIVE (true Re `≈ -0.26 < 0`), so
  `D3_block_norm_ge_sum_lo` through Re-parts CANNOT yield a positive `‖S_7‖`
  lower — `D3_S7_norm_ge` is green but trivially-true, and
  `D3_S7_cannot_reach_8_15` records that this route never reaches `8/15`
  for any `U ≥ 0`. The durable deliverable is the per-term enclosure
  technology (`θ/amplitude/cos/sin` for `x = 7, 11, 13`).
* `S_11`/`S_13` range assembly is NOT attempted here: it needs composite
  term lowers `k = 7, 8, 9` (`x = 8, 9, 10`) and `k = 11` (`x = 12`) through
  the `log 2/3/5` bridges (follower session per tasking). True values for
  the follower: `|S_11| ≈ 0.6789085166`, `|S_13| ≈ 0.5538057241`,
  `|S_16| ≈ 0.6523050041` (K-table: K=16 first feasible, margin `0.024`).
  Middle-block `[16,1024)` UPPER (`≤ 0.12` class) still open (triangle
  `≈ 35`, Abel+MVT `≈ 8.6` both too loose).
-/

/-- (C) `D3_phase 6 = 8.75·log 7` (prime pattern, mirrors `D3_phase_four_eq`). -/
theorem D3_phase_six_eq : D3_phase 6 = 8.75 * Real.log 7 := by
  unfold D3_phase
  have h : ((((6 : ℕ)) : ℝ) + 1 : ℝ) = 7 := by norm_num
  rw [h]

/-- (C) Phase lower `17.026 ≤ θ₇` (from `log_seven_gt_d9`). -/
theorem D3_theta_seven_lo : 17.026 ≤ D3_phase 6 := by
  rw [D3_phase_six_eq]
  have hlog := Real.log_seven_gt_d9
  have hmul := mul_lt_mul_of_pos_left hlog (by norm_num : (0 : ℝ) < 8.75)
  have hnum : (17.026 : ℝ) ≤ 8.75 * 1.9459101489 := by norm_num
  linarith

/-- (C) Phase upper `θ₇ ≤ 17.027` (from `log_seven_lt_d9`). -/
theorem D3_theta_seven_hi : D3_phase 6 ≤ 17.027 := by
  rw [D3_phase_six_eq]
  have hlog := Real.log_seven_lt_d9
  have hmul := mul_lt_mul_of_pos_left hlog (by norm_num : (0 : ℝ) < 8.75)
  have hnum : 8.75 * 1.9459101492 ≤ (17.027 : ℝ) := by norm_num
  linarith

/-- (C) Reduced phase `θ₇ - 4π ∈ [4.426, 4.467]` (from `pi_d2`). -/
theorem D3_delta_seven_mem :
    (4.426 : ℝ) ≤ D3_phase 6 - 4 * Real.pi ∧
    D3_phase 6 - 4 * Real.pi ≤ 4.467 := by
  have hth_lo := D3_theta_seven_lo
  have hth_hi := D3_theta_seven_hi
  have hpi_lo := Real.pi_gt_d2
  have hpi_hi := Real.pi_lt_d2
  constructor <;> linarith

/-- (C) Trivial cosine lower `cos θ₇ ≥ -1`. -/
theorem D3_cos_theta_seven_lower : -1 ≤ Real.cos (D3_phase 6) :=
  (Real.cos_mem_Icc _).1

set_option maxHeartbeats 800000 in
/-- (C) Cosine upper `cos θ₇ ≤ -0.11` (`cos_add_pi` shift + quadratic
    `1 - y²/2`, `y = θ₇ - 5π ∈ [1.276, 1.327]`). -/
theorem D3_cos_theta_seven_upper : Real.cos (D3_phase 6) ≤ -0.11 := by
  have hmem := D3_delta_seven_mem
  have hpi_lo := Real.pi_gt_d2
  have hpi_hi := Real.pi_lt_d2
  set y := D3_phase 6 - 4 * Real.pi - Real.pi with hy_def
  have hy_lo : (1.276 : ℝ) ≤ y := by rw [hy_def]; linarith [hmem.1, hpi_hi]
  have hy_hi : y ≤ (1.327 : ℝ) := by rw [hy_def]; linarith [hmem.2, hpi_lo]
  have hy_nn : (0 : ℝ) ≤ y := by linarith [hy_lo]
  have hsq : y ^ 2 ≤ (1.327 : ℝ) ^ 2 := pow_le_pow_left₀ hy_nn hy_hi 2
  have hcos_lo := Real.one_sub_sq_div_two_le_cos (x := y)
  have hnum : (0.11 : ℝ) ≤ 1 - (1.327 : ℝ) ^ 2 / 2 := by norm_num
  have hcosy : (0.11 : ℝ) ≤ Real.cos y := by
    have hle : 1 - (1.327 : ℝ) ^ 2 / 2 ≤ 1 - y ^ 2 / 2 := by linarith [hsq]
    linarith [hcos_lo, hle, hnum]
  have hper1 : Real.cos (D3_phase 6 - 2 * Real.pi) = Real.cos (D3_phase 6) :=
    Real.cos_sub_two_pi _
  have hper2 : Real.cos ((D3_phase 6 - 2 * Real.pi) - 2 * Real.pi) =
      Real.cos (D3_phase 6 - 2 * Real.pi) :=
    Real.cos_sub_two_pi _
  have hper : Real.cos (D3_phase 6 - 4 * Real.pi) = Real.cos (D3_phase 6) := by
    have e : (D3_phase 6 - 2 * Real.pi) - 2 * Real.pi =
        D3_phase 6 - 4 * Real.pi := by ring
    rw [e] at hper2
    exact hper2.trans hper1
  have hdecomp : D3_phase 6 - 4 * Real.pi = y + Real.pi := by
    rw [hy_def]; ring
  have h1 : Real.cos (D3_phase 6 - 4 * Real.pi) = -Real.cos y := by
    rw [hdecomp, Real.cos_add_pi]
  have hcos_eq : Real.cos (D3_phase 6) = -Real.cos y := by
    rw [← hper, h1]
  linarith [hcos_eq, hcosy]

set_option maxHeartbeats 800000 in
/-- (C) Sine enclosure `sin θ₇ ∈ [-1, -0.88]` (`sin_add_pi` shift +
    cubic, `y = θ₇ - 5π ∈ [1.276, 1.327]`). -/
theorem D3_sin_theta_seven_mem :
    -1 ≤ Real.sin (D3_phase 6) ∧ Real.sin (D3_phase 6) ≤ -0.88 := by
  have hmem := D3_delta_seven_mem
  have hpi_lo := Real.pi_gt_d2
  have hpi_hi := Real.pi_lt_d2
  set y := D3_phase 6 - 4 * Real.pi - Real.pi with hy_def
  have hy_lo : (1.276 : ℝ) ≤ y := by rw [hy_def]; linarith [hmem.1, hpi_hi]
  have hy_hi : y ≤ (1.327 : ℝ) := by rw [hy_def]; linarith [hmem.2, hpi_lo]
  have hy_nn : (0 : ℝ) ≤ y := by linarith [hy_lo]
  have hsin_lo := Real.sin_ge_sub_cube hy_nn
  have hcube : y ^ 3 ≤ (1.327 : ℝ) ^ 3 := pow_le_pow_left₀ hy_nn hy_hi 3
  have hnum : (0.88 : ℝ) ≤ 1.276 - (1.327 : ℝ) ^ 3 / 6 := by norm_num
  have hlo : (0.88 : ℝ) ≤ Real.sin y := by
    have h1 : (1.276 : ℝ) - (1.327 : ℝ) ^ 3 / 6 ≤
        y - y ^ 3 / 6 := by linarith [hy_lo, hcube]
    linarith [hsin_lo, h1, hnum]
  have hper1 : Real.sin (D3_phase 6 - 2 * Real.pi) = Real.sin (D3_phase 6) :=
    Real.sin_sub_two_pi _
  have hper2 : Real.sin ((D3_phase 6 - 2 * Real.pi) - 2 * Real.pi) =
      Real.sin (D3_phase 6 - 2 * Real.pi) :=
    Real.sin_sub_two_pi _
  have hper : Real.sin (D3_phase 6 - 4 * Real.pi) = Real.sin (D3_phase 6) := by
    have e : (D3_phase 6 - 2 * Real.pi) - 2 * Real.pi =
        D3_phase 6 - 4 * Real.pi := by ring
    rw [e] at hper2
    exact hper2.trans hper1
  have hdecomp : D3_phase 6 - 4 * Real.pi = y + Real.pi := by
    rw [hy_def]; ring
  have h1s : Real.sin (D3_phase 6 - 4 * Real.pi) = -Real.sin y := by
    rw [hdecomp, Real.sin_add_pi]
  have hsin_eq : Real.sin (D3_phase 6) = -Real.sin y := by
    rw [← hper, h1s]
  have hlo_neg : Real.sin (D3_phase 6) ≤ (-0.88 : ℝ) := by
    rw [hsin_eq]; linarith [hlo]
  have hlo_triv : (-1 : ℝ) ≤ Real.sin (D3_phase 6) :=
    (Real.sin_mem_Icc _).1
  exact ⟨hlo_triv, hlo_neg⟩

set_option maxHeartbeats 800000 in
/-- (C) Amplitude upper `D3_amp 6 ≤ 1/3` (via `7^{3/5} ≥ 3`,
    cleared: `3^5 = 243 ≤ 343 = 7^3`, since `3/5 ≤ 0.605`). -/
theorem D3_amp_seven_upper : D3_amp 6 ≤ 1 / 3 := by
  unfold D3_amp
  have hcast : ((((6 : ℕ)) : ℝ) + 1 : ℝ) = 7 := by norm_num
  rw [hcast]
  have h35 : (3 / 5 : ℝ) ≤ (0.605 : ℝ) := by norm_num
  have hmono : (7 : ℝ) ^ ((3 / 5 : ℝ)) ≤ (7 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h35
  have hpow : ((3 : ℝ)) ^ ((5 : ℕ))
      ≤ ((((7 : ℝ) ^ ((3 / 5 : ℝ)))) ^ ((5 : ℕ)) : ℝ) := by
    have e : ((((7 : ℝ) ^ ((3 / 5 : ℝ)))) ^ ((5 : ℕ)) : ℝ)
        = (7 : ℝ) ^ ((3 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 7)]
      rw [show (3 / 5 : ℝ) * (((5 : ℕ)) : ℝ) = (3 : ℝ) by norm_num]
      rw [show (3 : ℝ) = (((3 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 7 3
    rw [e]
    norm_num
  have hstep : (3 : ℝ) ≤ (7 : ℝ) ^ ((3 / 5 : ℝ)) :=
    le_of_pow_le_pow_left₀ (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _).le hpow
  have h7ge : (3 : ℝ) ≤ (7 : ℝ) ^ (0.605 : ℝ) := le_trans hstep hmono
  have hpos : (0 : ℝ) < (7 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have e : (-0.605 : ℝ) = -(0.605 : ℝ) := by norm_num
  rw [e, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 7)]
  have heq : (1 / 3 : ℝ) = ((3 : ℝ))⁻¹ := by norm_num
  rw [heq]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr h7ge

set_option maxHeartbeats 800000 in
/-- (C) Amplitude lower `1/4 ≤ D3_amp 6` (via `7^{2/3} ≤ 4`,
    cleared: `7^2 = 49 ≤ 64 = 4^3`, since `0.605 ≤ 2/3`). -/
theorem D3_amp_seven_lower : 1 / 4 ≤ D3_amp 6 := by
  unfold D3_amp
  have hcast : ((((6 : ℕ)) : ℝ) + 1 : ℝ) = 7 := by norm_num
  rw [hcast]
  have h65 : (0.605 : ℝ) ≤ 2 / 3 := by norm_num
  have hmono : (7 : ℝ) ^ (0.605 : ℝ) ≤ (7 : ℝ) ^ ((2 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h65
  have hpow : ((((7 : ℝ) ^ ((2 / 3 : ℝ)))) ^ ((3 : ℕ)) : ℝ)
      ≤ (((4 : ℝ)) ^ ((3 : ℕ))) := by
    have e : ((((7 : ℝ) ^ ((2 / 3 : ℝ)))) ^ ((3 : ℕ)) : ℝ)
        = (7 : ℝ) ^ ((2 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 7)]
      rw [show (2 / 3 : ℝ) * (((3 : ℕ)) : ℝ) = (2 : ℝ) by norm_num]
      rw [show (2 : ℝ) = (((2 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 7 2
    rw [e]
    norm_num
  have hstep : (7 : ℝ) ^ ((2 / 3 : ℝ)) ≤ 4 :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  have h7le : (7 : ℝ) ^ (0.605 : ℝ) ≤ 4 := le_trans hmono hstep
  have hpos : (0 : ℝ) < (7 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have e : (-0.605 : ℝ) = -(0.605 : ℝ) := by norm_num
  rw [e, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 7)]
  have heq : (1 / 4 : ℝ) = ((4 : ℝ))⁻¹ := by norm_num
  rw [heq]
  exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 4) hpos).mpr h7le

/-- (C) Seventh-term real-part lower `≥ -1/3` (interval: `amp ≤ 1/3`,
    `cos ≥ -1`; even `k = 6`). -/
theorem D3_term6_re_lo :
    (-1 / 3 : ℝ) ≤ (etaDirichletTerm (1 - zetaCellS0) 6).re := by
  rw [D3_eta_re]
  have hamp := D3_amp_seven_upper
  have hcos_lo : (-1 : ℝ) ≤ Real.cos (D3_phase 6) := (Real.cos_mem_Icc _).1
  have hamp_nn : (0 : ℝ) ≤ D3_amp 6 := D3_amp_nonneg 6
  have hpow6 : ((-1 : ℝ) ^ (6 : ℕ)) = 1 := by norm_num
  rw [hpow6, one_mul]
  have h : (-(1 / 3) : ℝ) ≤ D3_amp 6 * Real.cos (D3_phase 6) := by
    have h1 : D3_amp 6 * (-1) ≤ D3_amp 6 * Real.cos (D3_phase 6) :=
      mul_le_mul_of_nonneg_left hcos_lo hamp_nn
    linarith [h1, hamp]
  linarith [h]

/-- (C) `S_7` real-part lower `≥ -15/8` via the interval framework
    (`1 - 2/3 - 3/5 - 1/2 - 2/5 - 3/8 - 1/3`, à la `D3_S6_re_lower`). -/
theorem D3_S7_re_lower :
    (-15 / 8 : ℝ) ≤
      (∑ k ∈ Finset.range 7, etaDirichletTerm (1 - zetaCellS0) k).re := by
  rw [D3_sum_re_eq]
  have h7 : (∑ k ∈ Finset.range 7, (etaDirichletTerm (1 - zetaCellS0) k).re) =
      (etaDirichletTerm (1 - zetaCellS0) 0).re +
      (etaDirichletTerm (1 - zetaCellS0) 1).re +
      (etaDirichletTerm (1 - zetaCellS0) 2).re +
      (etaDirichletTerm (1 - zetaCellS0) 3).re +
      (etaDirichletTerm (1 - zetaCellS0) 4).re +
      (etaDirichletTerm (1 - zetaCellS0) 5).re +
      (etaDirichletTerm (1 - zetaCellS0) 6).re := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [h7, D3_term0_re]
  have h1 := D3_term1_re_lo
  have h2 := D3_term2_re_lo
  have h3 := D3_term3_re_lo
  have h4 := D3_term4_re_lo
  have h5 := D3_term5_re_lo
  have h6 := D3_term6_re_lo
  linarith

/-- (F2) Explicit per-term Re lowers for `S_7` (sums to `-15/8`). -/
def D3_S7_lo : ℕ → ℝ := fun k =>
  if k = 0 then 1 else if k = 1 then -2 / 3 else if k = 2 then -3 / 5
    else if k = 3 then -1 / 2 else if k = 4 then -2 / 5
      else if k = 5 then -3 / 8 else -1 / 3

/-- (F2) The `S_7` lo-sum is `-15/8`. -/
theorem D3_S7_lo_sum : ∑ k ∈ Finset.range 7, D3_S7_lo k = (-15 / 8 : ℝ) := by
  have v0 : D3_S7_lo 0 = (1 : ℝ) := by simp [D3_S7_lo]
  have v1 : D3_S7_lo 1 = (-2 / 3 : ℝ) := by simp [D3_S7_lo]
  have v2 : D3_S7_lo 2 = (-3 / 5 : ℝ) := by simp [D3_S7_lo]
  have v3 : D3_S7_lo 3 = (-1 / 2 : ℝ) := by simp [D3_S7_lo]
  have v4 : D3_S7_lo 4 = (-2 / 5 : ℝ) := by simp [D3_S7_lo]
  have v5 : D3_S7_lo 5 = (-3 / 8 : ℝ) := by simp [D3_S7_lo]
  have v6 : D3_S7_lo 6 = (-1 / 3 : ℝ) := by simp [D3_S7_lo]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    v0, v1, v2, v3, v4, v5, v6]
  norm_num

/-- (F2) The `S_7` lo-values bound the term real parts below. -/
theorem D3_S7_lo_valid (k : ℕ) (hk : k < 7) :
    D3_S7_lo k ≤ (etaDirichletTerm (1 - zetaCellS0) k).re := by
  have v0 : D3_S7_lo 0 = (1 : ℝ) := by simp [D3_S7_lo]
  have v1 : D3_S7_lo 1 = (-2 / 3 : ℝ) := by simp [D3_S7_lo]
  have v2 : D3_S7_lo 2 = (-3 / 5 : ℝ) := by simp [D3_S7_lo]
  have v3 : D3_S7_lo 3 = (-1 / 2 : ℝ) := by simp [D3_S7_lo]
  have v4 : D3_S7_lo 4 = (-2 / 5 : ℝ) := by simp [D3_S7_lo]
  have v5 : D3_S7_lo 5 = (-3 / 8 : ℝ) := by simp [D3_S7_lo]
  have v6 : D3_S7_lo 6 = (-1 / 3 : ℝ) := by simp [D3_S7_lo]
  interval_cases k
  · rw [v0, D3_term0_re]
  · rw [v1]
    exact D3_term1_re_lo
  · rw [v2]
    exact D3_term2_re_lo
  · rw [v3]
    exact D3_term3_re_lo
  · rw [v4]
    exact D3_term4_re_lo
  · rw [v5]
    exact D3_term5_re_lo
  · rw [v6]
    exact D3_term6_re_lo

/-- (F2) `S_7` norm lower `≥ -15/8` through `D3_block_norm_ge_sum_lo`. -/
theorem D3_S7_norm_ge :
    (-15 / 8 : ℝ) ≤
      ‖∑ k ∈ Finset.range 7, etaDirichletTerm (1 - zetaCellS0) k‖ := by
  have h := D3_block_norm_ge_sum_lo 7 D3_S7_lo D3_S7_lo_valid
  rw [D3_S7_lo_sum] at h
  exact h

/-- (P) `S_{1024}` conditional from the `S_7` interval lower. -/
theorem D3_S1024_of_S7 (U : ℝ)
    (hU : ‖∑ k ∈ Finset.Ico 7 1024, etaDirichletTerm (1 - zetaCellS0) k‖ ≤ U) :
    (-15 / 8 - U : ℝ) ≤
      ‖∑ k ∈ Finset.range 1024, etaDirichletTerm (1 - zetaCellS0) k‖ :=
  D3_S1024_split_lower 7 (by norm_num) (-15 / 8) U D3_S7_norm_ge hU

/-- (P) The `S_7` Re-route CANNOT reach `8/15` via splitting
    (needs `U ≤ -15/8 - 8/15 < 0`). -/
theorem D3_S7_cannot_reach_8_15 (U : ℝ) (hU : 0 ≤ U) :
    (-15 / 8 - U : ℝ) < 8 / 15 := by
  have h : (-15 / 8 : ℝ) < 8 / 15 := by norm_num
  linarith

/-- (C) `D3_phase 10 = 8.75·log 11` (prime pattern, mirrors `D3_phase_four_eq`). -/
theorem D3_phase_ten_eq : D3_phase 10 = 8.75 * Real.log 11 := by
  unfold D3_phase
  have h : ((((10 : ℕ)) : ℝ) + 1 : ℝ) = 11 := by norm_num
  rw [h]

/-- (C) Phase lower `20.981 ≤ θ₁₁` (from `log_eleven_gt_d9`). -/
theorem D3_theta_eleven_lo : 20.981 ≤ D3_phase 10 := by
  rw [D3_phase_ten_eq]
  have hlog := Real.log_eleven_gt_d9
  have hmul := mul_lt_mul_of_pos_left hlog (by norm_num : (0 : ℝ) < 8.75)
  have hnum : (20.981 : ℝ) ≤ 8.75 * 2.3978952726 := by norm_num
  linarith

/-- (C) Phase upper `θ₁₁ ≤ 20.982` (from `log_eleven_lt_d9`). -/
theorem D3_theta_eleven_hi : D3_phase 10 ≤ 20.982 := by
  rw [D3_phase_ten_eq]
  have hlog := Real.log_eleven_lt_d9
  have hmul := mul_lt_mul_of_pos_left hlog (by norm_num : (0 : ℝ) < 8.75)
  have hnum : 8.75 * 2.3978952730 ≤ (20.982 : ℝ) := by norm_num
  linarith

/-- (C) Reduced phase `θ₁₁ - 6π ∈ [2.081, 2.142]` (from `pi_d2`). -/
theorem D3_delta_eleven_mem :
    (2.081 : ℝ) ≤ D3_phase 10 - 6 * Real.pi ∧
    D3_phase 10 - 6 * Real.pi ≤ 2.142 := by
  have hth_lo := D3_theta_eleven_lo
  have hth_hi := D3_theta_eleven_hi
  have hpi_lo := Real.pi_gt_d2
  have hpi_hi := Real.pi_lt_d2
  constructor <;> linarith

/-- (C) Trivial cosine lower `cos θ₁₁ ≥ -1`. -/
theorem D3_cos_theta_eleven_lower : -1 ≤ Real.cos (D3_phase 10) :=
  (Real.cos_mem_Icc _).1

set_option maxHeartbeats 800000 in
/-- (C) Cosine upper `cos θ₁₁ ≤ -0.42` (`cos_add_pi` shift + `cos_neg` +
    quadratic `1 - z²/2`, `z = 7π - θ₁₁ ∈ [0.998, 1.069]`). -/
theorem D3_cos_theta_eleven_upper : Real.cos (D3_phase 10) ≤ -0.42 := by
  have hmem := D3_delta_eleven_mem
  have hpi_lo := Real.pi_gt_d2
  have hpi_hi := Real.pi_lt_d2
  set y := D3_phase 10 - 6 * Real.pi - Real.pi with hy_def
  have hy_lo : (-1.069 : ℝ) ≤ y := by rw [hy_def]; linarith [hmem.1, hpi_hi]
  have hy_hi : y ≤ (-0.998 : ℝ) := by rw [hy_def]; linarith [hmem.2, hpi_lo]
  have hz_lo : (0.998 : ℝ) ≤ -y := by linarith [hy_hi]
  have hz_hi : -y ≤ (1.069 : ℝ) := by linarith [hy_lo]
  have hz_nn : (0 : ℝ) ≤ -y := by linarith [hz_lo]
  have hsq : (-y) ^ 2 ≤ (1.069 : ℝ) ^ 2 := pow_le_pow_left₀ hz_nn hz_hi 2
  have hcos_lo := Real.one_sub_sq_div_two_le_cos (x := -y)
  have hnum : (0.42 : ℝ) ≤ 1 - (1.069 : ℝ) ^ 2 / 2 := by norm_num
  have hcosz : (0.42 : ℝ) ≤ Real.cos (-y) := by
    have hle : 1 - (1.069 : ℝ) ^ 2 / 2 ≤ 1 - (-y) ^ 2 / 2 := by linarith [hsq]
    linarith [hcos_lo, hle, hnum]
  have hper1 : Real.cos (D3_phase 10 - 2 * Real.pi) = Real.cos (D3_phase 10) :=
    Real.cos_sub_two_pi _
  have hper2 : Real.cos ((D3_phase 10 - 2 * Real.pi) - 2 * Real.pi) =
      Real.cos (D3_phase 10 - 2 * Real.pi) :=
    Real.cos_sub_two_pi _
  have hper3 : Real.cos (((D3_phase 10 - 2 * Real.pi) - 2 * Real.pi) - 2 * Real.pi) =
      Real.cos ((D3_phase 10 - 2 * Real.pi) - 2 * Real.pi) :=
    Real.cos_sub_two_pi _
  have hper : Real.cos (D3_phase 10 - 6 * Real.pi) = Real.cos (D3_phase 10) := by
    have e : ((D3_phase 10 - 2 * Real.pi) - 2 * Real.pi) - 2 * Real.pi =
        D3_phase 10 - 6 * Real.pi := by ring
    rw [e] at hper3
    exact hper3.trans (hper2.trans hper1)
  have hdecomp : D3_phase 10 - 6 * Real.pi = y + Real.pi := by
    rw [hy_def]; ring
  have h1 : Real.cos (D3_phase 10 - 6 * Real.pi) = -Real.cos y := by
    rw [hdecomp, Real.cos_add_pi]
  have hcosy : Real.cos y = Real.cos (-y) := (Real.cos_neg y).symm
  have hcos_eq : Real.cos (D3_phase 10) = -Real.cos (-y) := by
    rw [← hper, h1, hcosy]
  linarith [hcos_eq, hcosz]

set_option maxHeartbeats 800000 in
/-- (C) Sine enclosure `sin θ₁₁ ∈ [0.79, 1]` (`sin_add_pi` shift + `sin_neg` +
    cubic, `z = 7π - θ₁₁ ∈ [0.998, 1.069]`). -/
theorem D3_sin_theta_eleven_mem :
    0.79 ≤ Real.sin (D3_phase 10) ∧ Real.sin (D3_phase 10) ≤ 1 := by
  have hmem := D3_delta_eleven_mem
  have hpi_lo := Real.pi_gt_d2
  have hpi_hi := Real.pi_lt_d2
  set y := D3_phase 10 - 6 * Real.pi - Real.pi with hy_def
  have hy_lo : (-1.069 : ℝ) ≤ y := by rw [hy_def]; linarith [hmem.1, hpi_hi]
  have hy_hi : y ≤ (-0.998 : ℝ) := by rw [hy_def]; linarith [hmem.2, hpi_lo]
  have hz_lo : (0.998 : ℝ) ≤ -y := by linarith [hy_hi]
  have hz_hi : -y ≤ (1.069 : ℝ) := by linarith [hy_lo]
  have hz_nn : (0 : ℝ) ≤ -y := by linarith [hz_lo]
  have hsin_lo := Real.sin_ge_sub_cube hz_nn
  have hcube : (-y) ^ 3 ≤ (1.069 : ℝ) ^ 3 := pow_le_pow_left₀ hz_nn hz_hi 3
  have hnum : (0.79 : ℝ) ≤ 0.998 - (1.069 : ℝ) ^ 3 / 6 := by norm_num
  have hlo : (0.79 : ℝ) ≤ Real.sin (-y) := by
    have h1 : (0.998 : ℝ) - (1.069 : ℝ) ^ 3 / 6 ≤
        (-y) - (-y) ^ 3 / 6 := by linarith [hz_lo, hcube]
    linarith [hsin_lo, h1, hnum]
  have hhi : Real.sin (-y) ≤ 1 := (Real.sin_mem_Icc _).2
  have hper1 : Real.sin (D3_phase 10 - 2 * Real.pi) = Real.sin (D3_phase 10) :=
    Real.sin_sub_two_pi _
  have hper2 : Real.sin ((D3_phase 10 - 2 * Real.pi) - 2 * Real.pi) =
      Real.sin (D3_phase 10 - 2 * Real.pi) :=
    Real.sin_sub_two_pi _
  have hper3 : Real.sin (((D3_phase 10 - 2 * Real.pi) - 2 * Real.pi) - 2 * Real.pi) =
      Real.sin ((D3_phase 10 - 2 * Real.pi) - 2 * Real.pi) :=
    Real.sin_sub_two_pi _
  have hper : Real.sin (D3_phase 10 - 6 * Real.pi) = Real.sin (D3_phase 10) := by
    have e : ((D3_phase 10 - 2 * Real.pi) - 2 * Real.pi) - 2 * Real.pi =
        D3_phase 10 - 6 * Real.pi := by ring
    rw [e] at hper3
    exact hper3.trans (hper2.trans hper1)
  have hdecomp : D3_phase 10 - 6 * Real.pi = y + Real.pi := by
    rw [hy_def]; ring
  have h1s : Real.sin (D3_phase 10 - 6 * Real.pi) = -Real.sin y := by
    rw [hdecomp, Real.sin_add_pi]
  have hnegy : Real.sin y = -Real.sin (-y) := by
    have h := Real.sin_neg y
    linarith [h]
  have hsin_eq : Real.sin (D3_phase 10) = Real.sin (-y) := by
    rw [← hper, h1s, hnegy, neg_neg]
  rw [hsin_eq]
  exact ⟨hlo, hhi⟩

set_option maxHeartbeats 800000 in
/-- (C) Amplitude upper `D3_amp 10 ≤ 1/4` (via `11^{3/5} ≥ 4`,
    cleared: `4^5 = 1024 ≤ 1331 = 11^3`, since `3/5 ≤ 0.605`). -/
theorem D3_amp_eleven_upper : D3_amp 10 ≤ 1 / 4 := by
  unfold D3_amp
  have hcast : ((((10 : ℕ)) : ℝ) + 1 : ℝ) = 11 := by norm_num
  rw [hcast]
  have h35 : (3 / 5 : ℝ) ≤ (0.605 : ℝ) := by norm_num
  have hmono : (11 : ℝ) ^ ((3 / 5 : ℝ)) ≤ (11 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h35
  have hpow : ((4 : ℝ)) ^ ((5 : ℕ))
      ≤ ((((11 : ℝ) ^ ((3 / 5 : ℝ)))) ^ ((5 : ℕ)) : ℝ) := by
    have e : ((((11 : ℝ) ^ ((3 / 5 : ℝ)))) ^ ((5 : ℕ)) : ℝ)
        = (11 : ℝ) ^ ((3 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 11)]
      rw [show (3 / 5 : ℝ) * (((5 : ℕ)) : ℝ) = (3 : ℝ) by norm_num]
      rw [show (3 : ℝ) = (((3 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 11 3
    rw [e]
    norm_num
  have hstep : (4 : ℝ) ≤ (11 : ℝ) ^ ((3 / 5 : ℝ)) :=
    le_of_pow_le_pow_left₀ (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _).le hpow
  have h11ge : (4 : ℝ) ≤ (11 : ℝ) ^ (0.605 : ℝ) := le_trans hstep hmono
  have hpos : (0 : ℝ) < (11 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have e : (-0.605 : ℝ) = -(0.605 : ℝ) := by norm_num
  rw [e, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 11)]
  have heq : (1 / 4 : ℝ) = ((4 : ℝ))⁻¹ := by norm_num
  rw [heq]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr h11ge

set_option maxHeartbeats 800000 in
/-- (C) Amplitude lower `1/5 ≤ D3_amp 10` (via `11^{2/3} ≤ 5`,
    cleared: `11^2 = 121 ≤ 125 = 5^3`, since `0.605 ≤ 2/3`). -/
theorem D3_amp_eleven_lower : 1 / 5 ≤ D3_amp 10 := by
  unfold D3_amp
  have hcast : ((((10 : ℕ)) : ℝ) + 1 : ℝ) = 11 := by norm_num
  rw [hcast]
  have h65 : (0.605 : ℝ) ≤ 2 / 3 := by norm_num
  have hmono : (11 : ℝ) ^ (0.605 : ℝ) ≤ (11 : ℝ) ^ ((2 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h65
  have hpow : ((((11 : ℝ) ^ ((2 / 3 : ℝ)))) ^ ((3 : ℕ)) : ℝ)
      ≤ (((5 : ℝ)) ^ ((3 : ℕ))) := by
    have e : ((((11 : ℝ) ^ ((2 / 3 : ℝ)))) ^ ((3 : ℕ)) : ℝ)
        = (11 : ℝ) ^ ((2 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 11)]
      rw [show (2 / 3 : ℝ) * (((3 : ℕ)) : ℝ) = (2 : ℝ) by norm_num]
      rw [show (2 : ℝ) = (((2 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 11 2
    rw [e]
    norm_num
  have hstep : (11 : ℝ) ^ ((2 / 3 : ℝ)) ≤ 5 :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  have h11le : (11 : ℝ) ^ (0.605 : ℝ) ≤ 5 := le_trans hmono hstep
  have hpos : (0 : ℝ) < (11 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have e : (-0.605 : ℝ) = -(0.605 : ℝ) := by norm_num
  rw [e, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 11)]
  have heq : (1 / 5 : ℝ) = ((5 : ℝ))⁻¹ := by norm_num
  rw [heq]
  exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 5) hpos).mpr h11le

/-- (C) Eleventh-term real-part lower `≥ -1/4` (interval: `amp ≤ 1/4`,
    `cos ≥ -1`; even `k = 10`). -/
theorem D3_term10_re_lo :
    (-1 / 4 : ℝ) ≤ (etaDirichletTerm (1 - zetaCellS0) 10).re := by
  rw [D3_eta_re]
  have hamp := D3_amp_eleven_upper
  have hcos_lo : (-1 : ℝ) ≤ Real.cos (D3_phase 10) := (Real.cos_mem_Icc _).1
  have hamp_nn : (0 : ℝ) ≤ D3_amp 10 := D3_amp_nonneg 10
  have hpow10 : ((-1 : ℝ) ^ (10 : ℕ)) = 1 := by norm_num
  rw [hpow10, one_mul]
  have h : (-(1 / 4) : ℝ) ≤ D3_amp 10 * Real.cos (D3_phase 10) := by
    have h1 : D3_amp 10 * (-1) ≤ D3_amp 10 * Real.cos (D3_phase 10) :=
      mul_le_mul_of_nonneg_left hcos_lo hamp_nn
    linarith [h1, hamp]
  linarith [h]

/-- (C) `D3_phase 12 = 8.75·log 13` (prime pattern, mirrors `D3_phase_four_eq`). -/
theorem D3_phase_twelve_eq : D3_phase 12 = 8.75 * Real.log 13 := by
  unfold D3_phase
  have h : ((((12 : ℕ)) : ℝ) + 1 : ℝ) = 13 := by norm_num
  rw [h]

/-- (C) Phase lower `22.443 ≤ θ₁₃` (from `log_thirteen_gt_d9`). -/
theorem D3_theta_thirteen_lo : 22.443 ≤ D3_phase 12 := by
  rw [D3_phase_twelve_eq]
  have hlog := Real.log_thirteen_gt_d9
  have hmul := mul_lt_mul_of_pos_left hlog (by norm_num : (0 : ℝ) < 8.75)
  have hnum : (22.443 : ℝ) ≤ 8.75 * 2.5649493573 := by norm_num
  linarith

/-- (C) Phase upper `θ₁₃ ≤ 22.444` (from `log_thirteen_lt_d9`). -/
theorem D3_theta_thirteen_hi : D3_phase 12 ≤ 22.444 := by
  rw [D3_phase_twelve_eq]
  have hlog := Real.log_thirteen_lt_d9
  have hmul := mul_lt_mul_of_pos_left hlog (by norm_num : (0 : ℝ) < 8.75)
  have hnum : 8.75 * 2.5649493576 ≤ (22.444 : ℝ) := by norm_num
  linarith

/-- (C) Reduced phase `θ₁₃ - 6π ∈ [3.543, 3.604]` (from `pi_d2`). -/
theorem D3_delta_thirteen_mem :
    (3.543 : ℝ) ≤ D3_phase 12 - 6 * Real.pi ∧
    D3_phase 12 - 6 * Real.pi ≤ 3.604 := by
  have hth_lo := D3_theta_thirteen_lo
  have hth_hi := D3_theta_thirteen_hi
  have hpi_lo := Real.pi_gt_d2
  have hpi_hi := Real.pi_lt_d2
  constructor <;> linarith

/-- (C) Trivial cosine lower `cos θ₁₃ ≥ -1`. -/
theorem D3_cos_theta_thirteen_lower : -1 ≤ Real.cos (D3_phase 12) :=
  (Real.cos_mem_Icc _).1

set_option maxHeartbeats 800000 in
/-- (C) Cosine upper `cos θ₁₃ ≤ -0.89` (`cos_add_pi` shift + quadratic
    `1 - y²/2`, `y = θ₁₃ - 7π ∈ [0.393, 0.464]`). -/
theorem D3_cos_theta_thirteen_upper : Real.cos (D3_phase 12) ≤ -0.89 := by
  have hmem := D3_delta_thirteen_mem
  have hpi_lo := Real.pi_gt_d2
  have hpi_hi := Real.pi_lt_d2
  set y := D3_phase 12 - 6 * Real.pi - Real.pi with hy_def
  have hy_lo : (0.393 : ℝ) ≤ y := by rw [hy_def]; linarith [hmem.1, hpi_hi]
  have hy_hi : y ≤ (0.464 : ℝ) := by rw [hy_def]; linarith [hmem.2, hpi_lo]
  have hy_nn : (0 : ℝ) ≤ y := by linarith [hy_lo]
  have hsq : y ^ 2 ≤ (0.464 : ℝ) ^ 2 := pow_le_pow_left₀ hy_nn hy_hi 2
  have hcos_lo := Real.one_sub_sq_div_two_le_cos (x := y)
  have hnum : (0.89 : ℝ) ≤ 1 - (0.464 : ℝ) ^ 2 / 2 := by norm_num
  have hcosy : (0.89 : ℝ) ≤ Real.cos y := by
    have hle : 1 - (0.464 : ℝ) ^ 2 / 2 ≤ 1 - y ^ 2 / 2 := by linarith [hsq]
    linarith [hcos_lo, hle, hnum]
  have hper1 : Real.cos (D3_phase 12 - 2 * Real.pi) = Real.cos (D3_phase 12) :=
    Real.cos_sub_two_pi _
  have hper2 : Real.cos ((D3_phase 12 - 2 * Real.pi) - 2 * Real.pi) =
      Real.cos (D3_phase 12 - 2 * Real.pi) :=
    Real.cos_sub_two_pi _
  have hper3 : Real.cos (((D3_phase 12 - 2 * Real.pi) - 2 * Real.pi) - 2 * Real.pi) =
      Real.cos ((D3_phase 12 - 2 * Real.pi) - 2 * Real.pi) :=
    Real.cos_sub_two_pi _
  have hper : Real.cos (D3_phase 12 - 6 * Real.pi) = Real.cos (D3_phase 12) := by
    have e : ((D3_phase 12 - 2 * Real.pi) - 2 * Real.pi) - 2 * Real.pi =
        D3_phase 12 - 6 * Real.pi := by ring
    rw [e] at hper3
    exact hper3.trans (hper2.trans hper1)
  have hdecomp : D3_phase 12 - 6 * Real.pi = y + Real.pi := by
    rw [hy_def]; ring
  have h1 : Real.cos (D3_phase 12 - 6 * Real.pi) = -Real.cos y := by
    rw [hdecomp, Real.cos_add_pi]
  have hcos_eq : Real.cos (D3_phase 12) = -Real.cos y := by
    rw [← hper, h1]
  linarith [hcos_eq, hcosy]

set_option maxHeartbeats 800000 in
/-- (C) Sine enclosure `sin θ₁₃ ∈ [-0.47, -0.37]` (`sin_add_pi` shift +
    cubic/linear, `y = θ₁₃ - 7π ∈ [0.393, 0.464]`). -/
theorem D3_sin_theta_thirteen_mem :
    -0.47 ≤ Real.sin (D3_phase 12) ∧ Real.sin (D3_phase 12) ≤ -0.37 := by
  have hmem := D3_delta_thirteen_mem
  have hpi_lo := Real.pi_gt_d2
  have hpi_hi := Real.pi_lt_d2
  set y := D3_phase 12 - 6 * Real.pi - Real.pi with hy_def
  have hy_lo : (0.393 : ℝ) ≤ y := by rw [hy_def]; linarith [hmem.1, hpi_hi]
  have hy_hi : y ≤ (0.464 : ℝ) := by rw [hy_def]; linarith [hmem.2, hpi_lo]
  have hy_nn : (0 : ℝ) ≤ y := by linarith [hy_lo]
  have hsin_lo := Real.sin_ge_sub_cube hy_nn
  have hsin_hi := Real.sin_le hy_nn
  have hcube : y ^ 3 ≤ (0.464 : ℝ) ^ 3 := pow_le_pow_left₀ hy_nn hy_hi 3
  have hnum : (0.37 : ℝ) ≤ 0.393 - (0.464 : ℝ) ^ 3 / 6 := by norm_num
  have hlo : (0.37 : ℝ) ≤ Real.sin y := by
    have h1 : (0.393 : ℝ) - (0.464 : ℝ) ^ 3 / 6 ≤
        y - y ^ 3 / 6 := by linarith [hy_lo, hcube]
    linarith [hsin_lo, h1, hnum]
  have hhi : Real.sin y ≤ (0.47 : ℝ) := by
    have hle : Real.sin y ≤ y := hsin_hi
    linarith [hle, hy_hi]
  have hper1 : Real.sin (D3_phase 12 - 2 * Real.pi) = Real.sin (D3_phase 12) :=
    Real.sin_sub_two_pi _
  have hper2 : Real.sin ((D3_phase 12 - 2 * Real.pi) - 2 * Real.pi) =
      Real.sin (D3_phase 12 - 2 * Real.pi) :=
    Real.sin_sub_two_pi _
  have hper3 : Real.sin (((D3_phase 12 - 2 * Real.pi) - 2 * Real.pi) - 2 * Real.pi) =
      Real.sin ((D3_phase 12 - 2 * Real.pi) - 2 * Real.pi) :=
    Real.sin_sub_two_pi _
  have hper : Real.sin (D3_phase 12 - 6 * Real.pi) = Real.sin (D3_phase 12) := by
    have e : ((D3_phase 12 - 2 * Real.pi) - 2 * Real.pi) - 2 * Real.pi =
        D3_phase 12 - 6 * Real.pi := by ring
    rw [e] at hper3
    exact hper3.trans (hper2.trans hper1)
  have hdecomp : D3_phase 12 - 6 * Real.pi = y + Real.pi := by
    rw [hy_def]; ring
  have h1s : Real.sin (D3_phase 12 - 6 * Real.pi) = -Real.sin y := by
    rw [hdecomp, Real.sin_add_pi]
  have hsin_eq : Real.sin (D3_phase 12) = -Real.sin y := by
    rw [← hper, h1s]
  constructor
  · rw [hsin_eq]; linarith [hhi]
  · rw [hsin_eq]; linarith [hlo]

set_option maxHeartbeats 800000 in
/-- (C) Amplitude upper `D3_amp 12 ≤ 1/4` (via `13^{3/5} ≥ 4`,
    cleared: `4^5 = 1024 ≤ 2197 = 13^3`, since `3/5 ≤ 0.605`). -/
theorem D3_amp_thirteen_upper : D3_amp 12 ≤ 1 / 4 := by
  unfold D3_amp
  have hcast : ((((12 : ℕ)) : ℝ) + 1 : ℝ) = 13 := by norm_num
  rw [hcast]
  have h35 : (3 / 5 : ℝ) ≤ (0.605 : ℝ) := by norm_num
  have hmono : (13 : ℝ) ^ ((3 / 5 : ℝ)) ≤ (13 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h35
  have hpow : ((4 : ℝ)) ^ ((5 : ℕ))
      ≤ ((((13 : ℝ) ^ ((3 / 5 : ℝ)))) ^ ((5 : ℕ)) : ℝ) := by
    have e : ((((13 : ℝ) ^ ((3 / 5 : ℝ)))) ^ ((5 : ℕ)) : ℝ)
        = (13 : ℝ) ^ ((3 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 13)]
      rw [show (3 / 5 : ℝ) * (((5 : ℕ)) : ℝ) = (3 : ℝ) by norm_num]
      rw [show (3 : ℝ) = (((3 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 13 3
    rw [e]
    norm_num
  have hstep : (4 : ℝ) ≤ (13 : ℝ) ^ ((3 / 5 : ℝ)) :=
    le_of_pow_le_pow_left₀ (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _).le hpow
  have h13ge : (4 : ℝ) ≤ (13 : ℝ) ^ (0.605 : ℝ) := le_trans hstep hmono
  have hpos : (0 : ℝ) < (13 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have e : (-0.605 : ℝ) = -(0.605 : ℝ) := by norm_num
  rw [e, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 13)]
  have heq : (1 / 4 : ℝ) = ((4 : ℝ))⁻¹ := by norm_num
  rw [heq]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr h13ge

set_option maxHeartbeats 800000 in
/-- (C) Amplitude lower `1/6 ≤ D3_amp 12` (via `13^{2/3} ≤ 6`,
    cleared: `13^2 = 169 ≤ 216 = 6^3`, since `0.605 ≤ 2/3`). -/
theorem D3_amp_thirteen_lower : 1 / 6 ≤ D3_amp 12 := by
  unfold D3_amp
  have hcast : ((((12 : ℕ)) : ℝ) + 1 : ℝ) = 13 := by norm_num
  rw [hcast]
  have h65 : (0.605 : ℝ) ≤ 2 / 3 := by norm_num
  have hmono : (13 : ℝ) ^ (0.605 : ℝ) ≤ (13 : ℝ) ^ ((2 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h65
  have hpow : ((((13 : ℝ) ^ ((2 / 3 : ℝ)))) ^ ((3 : ℕ)) : ℝ)
      ≤ (((6 : ℝ)) ^ ((3 : ℕ))) := by
    have e : ((((13 : ℝ) ^ ((2 / 3 : ℝ)))) ^ ((3 : ℕ)) : ℝ)
        = (13 : ℝ) ^ ((2 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 13)]
      rw [show (2 / 3 : ℝ) * (((3 : ℕ)) : ℝ) = (2 : ℝ) by norm_num]
      rw [show (2 : ℝ) = (((2 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 13 2
    rw [e]
    norm_num
  have hstep : (13 : ℝ) ^ ((2 / 3 : ℝ)) ≤ 6 :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  have h13le : (13 : ℝ) ^ (0.605 : ℝ) ≤ 6 := le_trans hmono hstep
  have hpos : (0 : ℝ) < (13 : ℝ) ^ (0.605 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have e : (-0.605 : ℝ) = -(0.605 : ℝ) := by norm_num
  rw [e, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 13)]
  have heq : (1 / 6 : ℝ) = ((6 : ℝ))⁻¹ := by norm_num
  rw [heq]
  exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 6) hpos).mpr h13le

/-- (C) Thirteenth-term real-part lower `≥ -1/4` (interval: `amp ≤ 1/4`,
    `cos ≥ -1`; even `k = 12`). -/
theorem D3_term12_re_lo :
    (-1 / 4 : ℝ) ≤ (etaDirichletTerm (1 - zetaCellS0) 12).re := by
  rw [D3_eta_re]
  have hamp := D3_amp_thirteen_upper
  have hcos_lo : (-1 : ℝ) ≤ Real.cos (D3_phase 12) := (Real.cos_mem_Icc _).1
  have hamp_nn : (0 : ℝ) ≤ D3_amp 12 := D3_amp_nonneg 12
  have hpow12 : ((-1 : ℝ) ^ (12 : ℕ)) = 1 := by norm_num
  rw [hpow12, one_mul]
  have h : (-(1 / 4) : ℝ) ≤ D3_amp 12 * Real.cos (D3_phase 12) := by
    have h1 : D3_amp 12 * (-1) ≤ D3_amp 12 * Real.cos (D3_phase 12) :=
      mul_le_mul_of_nonneg_left hcos_lo hamp_nn
    linarith [h1, hamp]
  linarith [h]

#print axioms D3_phase_six_eq
#print axioms D3_theta_seven_lo
#print axioms D3_theta_seven_hi
#print axioms D3_delta_seven_mem
#print axioms D3_cos_theta_seven_lower
#print axioms D3_cos_theta_seven_upper
#print axioms D3_sin_theta_seven_mem
#print axioms D3_amp_seven_upper
#print axioms D3_amp_seven_lower
#print axioms D3_term6_re_lo
#print axioms D3_S7_re_lower
#print axioms D3_S7_lo_sum
#print axioms D3_S7_lo_valid
#print axioms D3_S7_norm_ge
#print axioms D3_S1024_of_S7
#print axioms D3_S7_cannot_reach_8_15
#print axioms D3_phase_ten_eq
#print axioms D3_theta_eleven_lo
#print axioms D3_theta_eleven_hi
#print axioms D3_delta_eleven_mem
#print axioms D3_cos_theta_eleven_lower
#print axioms D3_cos_theta_eleven_upper
#print axioms D3_sin_theta_eleven_mem
#print axioms D3_amp_eleven_upper
#print axioms D3_amp_eleven_lower
#print axioms D3_term10_re_lo
#print axioms D3_phase_twelve_eq
#print axioms D3_theta_thirteen_lo
#print axioms D3_theta_thirteen_hi
#print axioms D3_delta_thirteen_mem
#print axioms D3_cos_theta_thirteen_lower
#print axioms D3_cos_theta_thirteen_upper
#print axioms D3_sin_theta_thirteen_mem
#print axioms D3_amp_thirteen_upper
#print axioms D3_amp_thirteen_lower
#print axioms D3_term12_re_lo



