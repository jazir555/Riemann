import Mathlib
import door3_dp_trig
import door3_dp_terms
import zeta_rigorous

/-!
# Door 3 eta-prime shapes: log-weighted pair term, two-piece bound, tail shape, R05 n=2 demo.

Import closure (read-only verified before writing):
* `door3_dp_trig` imports `Mathlib` only — upstream leaf.
* `door3_dp_terms` imports `Mathlib` + `door3_dp_trig` — upstream leaf.
* This file imports `Mathlib` + `door3_dp_trig` + `door3_dp_terms` + `zeta_rigorous`.
  Import-DAG check (2026-09-22, read-only): `zeta_rigorous` imports only
  `Mathlib` + `Zeta23.MV.Final`; the `Zeta23/*` tree imports no `door3_*`
  file, so adding this import creates no cycle. The pair MVT pattern is
  still reproved locally for the weighted difference.

Recon (read-only): `etaPairTerm s m` is the sum of the two Dirichlet terms
at `2 * m` and `2 * m + 1`, hence the cpow-difference form with bases
`2 * m + 1` and `2 * m + 2`. The definitions below mirror that shape with
`-log` weights, i.e. the termwise `s`-derivative shape. The R05 center
`⟨0.395, -0.75⟩` is corroborated read-only in `door3_premise_poly` and
`door3_R05_close` (both state the R05 center with those coordinates).

What is proved here (micro-scoped shapes only, full proofs throughout):
* (1) `etaPairDeriv_term`: closed log-weighted cpow-difference form.
* helper `etaCpowDiff_le`: MVT cpow-difference bound for `0 < s.re`.
* (2) `etaDerivPair_bound`: two-piece weighted pair bound.
* (3) `etaDeriv_finblock_shape`, `etaDeriv_tsum_shape`, `etaDeriv_tail_shape`:
  finite-block, abstract shifted-tsum, and concrete tail bounds, fully general
  in `s` and `M`, with no plugged numerals.
* (4) `etaDeriv_demo_R05_n2`: single-term `n = 2` disc at the R05 center
  with center `0` and radius `1`.
-/

/-- Log-weighted Dirichlet-eta summand: termwise `s`-derivative shape. -/
noncomputable def etaDerivDirichletTerm (s : ℂ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ n * ((-Real.log ((n : ℝ) + 1) : ℂ)) *
    ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s)

/-- Log-weighted pair summand, mirroring the `etaPairTerm` index shape. -/
noncomputable def etaDerivPairTerm (s : ℂ) (m : ℕ) : ℂ :=
  etaDerivDirichletTerm s (2 * m) + etaDerivDirichletTerm s (2 * m + 1)

/-- Two-piece majorant for the log-weighted pair. -/
noncomputable def etaDerivBound (s : ℂ) (m : ℕ) : ℝ :=
  Real.log (((2 * m + 2 : ℕ) : ℝ)) * ‖s‖ * (((2 * m + 1 : ℕ) : ℝ) ^ (-s.re - 1)) +
    (Real.log (((2 * m + 2 : ℕ) : ℝ)) - Real.log (((2 * m + 1 : ℕ) : ℝ))) *
      (((2 * m + 1 : ℕ) : ℝ) ^ (-s.re))

/-- (1) Closed log-weighted cpow-difference form of the pair term. -/
theorem etaPairDeriv_term (s : ℂ) (m : ℕ) :
    etaDerivPairTerm s m =
      ((-Real.log (((2 * m + 1 : ℕ) : ℝ)) : ℂ)) *
          (((((2 * m + 1 : ℕ) : ℝ)) : ℂ) ^ (-s)) -
        ((-Real.log (((2 * m + 2 : ℕ) : ℝ)) : ℂ)) *
          (((((2 * m + 2 : ℕ) : ℝ)) : ℂ) ^ (-s)) := by
  have hA : (((2 * m : ℕ) : ℝ)) + 1 = (((2 * m + 1 : ℕ) : ℝ)) := by
    push_cast
    ring
  have hB : (((2 * m + 1 : ℕ) : ℝ)) + 1 = (((2 * m + 2 : ℕ) : ℝ)) := by
    push_cast
    ring
  have hsq : (-1 : ℂ) ^ 2 = 1 := by norm_num
  have h0 : (-1 : ℂ) ^ (2 * m) = 1 := by
    rw [pow_mul, hsq, one_pow]
  have h1 : (-1 : ℂ) ^ (2 * m + 1) = -1 := by
    rw [pow_add, h0, pow_one, one_mul]
  unfold etaDerivPairTerm etaDerivDirichletTerm
  rw [hA, hB, h0, h1]
  ring

/-- MVT cpow-difference bound for `0 < s.re` (local reproof of the banked pattern). -/
theorem etaCpowDiff_le (s : ℂ) (hs : 0 < s.re) (m : ℕ) :
    ‖((((((2 * m + 1 : ℕ) : ℝ)) : ℂ) ^ (-s)) -
      (((((2 * m + 2 : ℕ) : ℝ)) : ℂ) ^ (-s)))‖ ≤
      ‖s‖ * (((2 * m + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := by
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
  have hdiff : ∀ x : ℝ, x ∈ Set.Icc a b →
      DifferentiableAt ℝ (fun t : ℝ => (t : ℂ) ^ (-s)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha_pos (Set.mem_Icc.mp hx).1
    exact (hasDerivAt_ofReal_cpow_const (ne_of_gt hx0) hnegs).differentiableAt
  have hderiv_eq : ∀ x : ℝ, x ≠ 0 →
      deriv (fun t : ℝ => (t : ℂ) ^ (-s)) x = (-s) * (x : ℂ) ^ (-s - 1) := by
    intro x hx0
    exact Complex.deriv_ofReal_cpow_const hx0 (c := -s) hnegs
  have hexp_nonpos : -s.re - 1 ≤ 0 := by linarith
  have hbound : ∀ x : ℝ, x ∈ Set.Icc a b →
      ‖deriv (fun t : ℝ => (t : ℂ) ^ (-s)) x‖ ≤ ‖s‖ * (a ^ (-s.re - 1)) := by
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
  rw [hrev]
  exact hmvt

/-- (2) Two-piece log-weighted pair bound for `0 < s.re`. -/
theorem etaDerivPair_bound (s : ℂ) (hs : 0 < s.re) (m : ℕ) :
    ‖etaDerivPairTerm s m‖ ≤ etaDerivBound s m := by
  have hPair := etaPairDeriv_term s m
  have hDiff := etaCpowDiff_le s hs m
  have hApos : (0 : ℝ) < (((2 * m + 1 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (by omega)
  have hAB : (((2 * m + 1 : ℕ) : ℝ)) ≤ (((2 * m + 2 : ℕ) : ℝ)) :=
    Nat.cast_le.mpr (by omega)
  have h1B : (1 : ℝ) ≤ (((2 * m + 2 : ℕ) : ℝ)) := by
    rw [← Nat.cast_one]
    exact Nat.cast_le.mpr (by omega)
  have hlog_mono : Real.log (((2 * m + 1 : ℕ) : ℝ)) ≤
      Real.log (((2 * m + 2 : ℕ) : ℝ)) :=
    Real.log_le_log hApos hAB
  have hlogB_nn : 0 ≤ Real.log (((2 * m + 2 : ℕ) : ℝ)) :=
    Real.log_nonneg h1B
  have hAnorm : ‖((((((2 * m + 1 : ℕ) : ℝ))) : ℂ) ^ (-s))‖ =
      (((2 * m + 1 : ℕ) : ℝ)) ^ (-s.re) := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos hApos (-s)
    rw [Complex.neg_re] at h
    exact h
  have hDecomp : etaDerivPairTerm s m =
      ((((-(Real.log (((2 * m + 2 : ℕ) : ℝ))) : ℝ))) : ℂ) *
        (((((((2 * m + 1 : ℕ) : ℝ))) : ℂ) ^ (-s)) -
          ((((((2 * m + 2 : ℕ) : ℝ))) : ℂ) ^ (-s))) +
        (((((Real.log (((2 * m + 2 : ℕ) : ℝ)) -
          Real.log (((2 * m + 1 : ℕ) : ℝ)) : ℝ))) : ℂ) *
          ((((((2 * m + 1 : ℕ) : ℝ))) : ℂ) ^ (-s)) := by
    rw [hPair]
    rw [Complex.ofReal_neg, Complex.ofReal_neg, Complex.ofReal_sub]
    ring
  have hLBnorm : ‖((((Real.log (((2 * m + 2 : ℕ) : ℝ)) : ℝ))) : ℂ)‖ =
      Real.log (((2 * m + 2 : ℕ) : ℝ)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogB_nn]
  have hDnn : 0 ≤ Real.log (((2 * m + 2 : ℕ) : ℝ)) -
      Real.log (((2 * m + 1 : ℕ) : ℝ)) := sub_nonneg.mpr hlog_mono
  have hDnorm : ‖(((((Real.log (((2 * m + 2 : ℕ) : ℝ)) -
      Real.log (((2 * m + 1 : ℕ) : ℝ)) : ℝ))) : ℂ)‖ =
      Real.log (((2 * m + 2 : ℕ) : ℝ)) - Real.log (((2 * m + 1 : ℕ) : ℝ)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hDnn]
  have hnegLBnorm : ‖((((-(Real.log (((2 * m + 2 : ℕ) : ℝ))) : ℝ))) : ℂ)‖ =
      Real.log (((2 * m + 2 : ℕ) : ℝ)) := by
    rw [Complex.ofReal_neg, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlogB_nn]
  have e1 : ‖(((((-(Real.log (((2 * m + 2 : ℕ) : ℝ))) : ℝ))) : ℂ) *
      ((((((((2 * m + 1 : ℕ) : ℝ))) : ℂ) ^ (-s)) -
        ((((((2 * m + 2 : ℕ) : ℝ))) : ℂ) ^ (-s)))‖ ≤
      Real.log (((2 * m + 2 : ℕ) : ℝ)) * ‖s‖ *
        (((2 * m + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := by
    have hstep : ‖(((((-(Real.log (((2 * m + 2 : ℕ) : ℝ))) : ℝ))) : ℂ) *
        ((((((((2 * m + 1 : ℕ) : ℝ))) : ℂ) ^ (-s)) -
          ((((((2 * m + 2 : ℕ) : ℝ))) : ℂ) ^ (-s)))‖ ≤
        Real.log (((2 * m + 2 : ℕ) : ℝ)) *
          (‖s‖ * (((2 * m + 1 : ℕ) : ℝ) ^ (-s.re - 1))) := by
      rw [norm_mul, hnegLBnorm]
      exact mul_le_mul_of_nonneg_left hDiff hlogB_nn
    calc ‖(((((-(Real.log (((2 * m + 2 : ℕ) : ℝ))) : ℝ))) : ℂ) *
        ((((((((2 * m + 1 : ℕ) : ℝ))) : ℂ) ^ (-s)) -
          ((((((2 * m + 2 : ℕ) : ℝ))) : ℂ) ^ (-s)))‖
          ≤ Real.log (((2 * m + 2 : ℕ) : ℝ)) *
            (‖s‖ * (((2 * m + 1 : ℕ) : ℝ) ^ (-s.re - 1))) := hstep
        _ = Real.log (((2 * m + 2 : ℕ) : ℝ)) * ‖s‖ *
            (((2 * m + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := by ring
  have e2 : ‖((((((Real.log (((2 * m + 2 : ℕ) : ℝ)) -
      Real.log (((2 * m + 1 : ℕ) : ℝ)) : ℝ))) : ℂ) *
      ((((((2 * m + 1 : ℕ) : ℝ))) : ℂ) ^ (-s)))‖ ≤
      (Real.log (((2 * m + 2 : ℕ) : ℝ)) - Real.log (((2 * m + 1 : ℕ) : ℝ))) *
        ((((2 * m + 1 : ℕ) : ℝ)) ^ (-s.re)) := by
    rw [norm_mul, hDnorm, hAnorm]
  rw [hDecomp]
  refine le_trans (norm_add_le _ _) ?_
  unfold etaDerivBound
  exact add_le_add e1 e2

/-- (3a) Finite-block tail shape: fully general in `s`, `B`, `M`, `K`. -/
theorem etaDeriv_finblock_shape (s : ℂ) (B : ℕ → ℝ)
    (hB : ∀ m : ℕ, ‖etaDerivPairTerm s m‖ ≤ B m) (M K : ℕ) :
    ‖∑ m ∈ Finset.Ico M (M + K), etaDerivPairTerm s m‖ ≤
      ∑ m ∈ Finset.Ico M (M + K), B m := by
  refine le_trans (norm_sum_le _ _) ?_
  exact Finset.sum_le_sum (fun m hm => hB m)

/-- (3b) Abstract shifted-tsum tail shape: fully general in `s`, `B`, `M`. -/
theorem etaDeriv_tsum_shape (s : ℂ) (B : ℕ → ℝ) (M : ℕ)
    (hB : ∀ m : ℕ, ‖etaDerivPairTerm s m‖ ≤ B m)
    (hFn : Summable (fun k : ℕ => ‖etaDerivPairTerm s (M + k)‖))
    (hBn : Summable (fun k : ℕ => B (M + k))) :
    ‖∑' k : ℕ, etaDerivPairTerm s (M + k)‖ ≤ ∑' k : ℕ, B (M + k) := by
  have h1 : ‖∑' k : ℕ, etaDerivPairTerm s (M + k)‖ ≤
      ∑' k : ℕ, ‖etaDerivPairTerm s (M + k)‖ :=
    norm_tsum_le_tsum_norm hFn
  have h2 : (∑' k : ℕ, ‖etaDerivPairTerm s (M + k)‖) ≤ ∑' k : ℕ, B (M + k) :=
    Summable.tsum_le_tsum (fun k : ℕ => hB (M + k)) hFn hBn
  exact le_trans h1 h2

/-- (3c) Concrete tail shape with the bound from (2), general `s` and `M`. -/
theorem etaDeriv_tail_shape (s : ℂ) (hs : 0 < s.re) (M : ℕ)
    (hFn : Summable (fun k : ℕ => ‖etaDerivPairTerm s (M + k)‖))
    (hBn : Summable (fun k : ℕ => etaDerivBound s (M + k))) :
    ‖∑' k : ℕ, etaDerivPairTerm s (M + k)‖ ≤
      ∑' k : ℕ, etaDerivBound s (M + k) :=
  etaDeriv_tsum_shape s (etaDerivBound s) M
    (fun m : ℕ => etaDerivPair_bound s hs m) hFn hBn

/-- R05 demo center: `σ = 0.395`, `t = -0.75`. -/
noncomputable def sR05demo : ℂ := ⟨(0.395 : ℝ), (-0.75 : ℝ)⟩

theorem sR05demo_re : sR05demo.re = (0.395 : ℝ) := by
  unfold sR05demo
  rfl

/-- (4) Single-term `n = 2` log-weighted head disc at the R05 center. -/
theorem etaDeriv_demo_R05_n2 :
    ‖(((-Real.log 2 : ℝ)) : ℂ) * (((((2 : ℝ))) : ℂ) ^ (-sR05demo)) - 0‖ ≤
      (1 : ℝ) := by
  have hlog_hi := dp_log2_hi
  have hlog_lo := dp_log2_lo
  have hlog_le1 : Real.log 2 ≤ 1 := by linarith
  have hlog_nn : 0 ≤ Real.log 2 := by linarith
  have habs_le1 : |Real.log 2| ≤ 1 := abs_le.mpr ⟨by linarith, hlog_le1⟩
  have hbase_pos : (0 : ℝ) < 2 := by norm_num
  have hcp : ‖(((((2 : ℝ))) : ℂ) ^ (-sR05demo))‖ = (2 : ℝ) ^ (-sR05demo.re) := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos hbase_pos (-sR05demo)
    rw [Complex.neg_re] at h
    exact h
  have hcp_le1 : (2 : ℝ) ^ (-sR05demo.re) ≤ 1 := by
    rw [sR05demo_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hscalar : ‖(((-Real.log 2 : ℝ)) : ℂ)‖ = |Real.log 2| := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg]
  have hmul : ‖(((-Real.log 2 : ℝ)) : ℂ) * (((((2 : ℝ))) : ℂ) ^ (-sR05demo))‖ =
      |Real.log 2| * ((2 : ℝ) ^ (-sR05demo.re)) := by
    rw [norm_mul, hscalar, hcp]
  rw [sub_zero, hmul]
  have hnn : 0 ≤ (2 : ℝ) ^ (-sR05demo.re) :=
    Real.rpow_nonneg (by norm_num) _
  calc |Real.log 2| * ((2 : ℝ) ^ (-sR05demo.re)) ≤ 1 * 1 :=
        mul_le_mul habs_le1 hcp_le1 hnn (by norm_num)
    _ = 1 := mul_one 1

/-- Bridge (DZ-SURVEY route (ii), LEMMA SHAPE, proved wrapper).

Mathlib citations (grepped before writing):
* `hasDerivAt_tsum_of_isPreconnected`, `hasDerivAt_tsum`,
  `hasFDerivAt_tsum_of_isPreconnected` in `Mathlib/Analysis/Calculus/SmoothSeries.lean`
  (differentiation of `∑' n, g n z` under a summable uniform derivative bound `u`);
* `tendstoUniformlyOn_tsum` in `Mathlib/Analysis/Normed/Group/FunctionSeries.lean`
  (summable sup-norm bound gives `TendstoUniformlyOn` of partial sums; used
  internally by the `SmoothSeries` theorems);
* `hasDerivAt_of_tendstoUniformlyOn`, `hasFDerivAt_of_tendstoUniformlyOn` in
  `Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean` (uniform-limit
  differentiation engine underlying the `SmoothSeries` theorems);
* disc topology: `Metric.isOpen_ball` in
  `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`, `convex_ball` in
  `Mathlib/Analysis/Normed/Module/Convex.lean`, and
  `Convex.isPreconnected` in `Mathlib/Analysis/Convex/PathConnected.lean`.

Statement: conditional `HasDerivAt` for an abstract eta-pair family `pairFn`
on the open disc `Metric.ball c R` (whose closure `Metric.closedBall c R` is
compact via `Metric.isCompact_closedBall`). The termwise derivative identity
(`HasDerivAt (pairFn m)` with derivative `etaDerivPairTerm y m`) and the
summable uniform majorant `u` are explicit premises; nothing about the true
`zeta_rigorous.etaPairTerm`, `etaPairLim_eq_etaHurwitz_of_pos`, or
`etaHurwitz_eq_etaRHS_compl` is imported or assumed here. -/
theorem etaPair_tsum_hasDerivAt_of_uniformBound
    (pairFn : ℕ → ℂ → ℂ) (u : ℕ → ℝ)
    (c : ℂ) (R : ℝ)
    (hu : Summable u)
    (hderiv : ∀ m y, y ∈ Metric.ball c R →
      HasDerivAt (pairFn m) (etaDerivPairTerm y m) y)
    (hbound : ∀ m y, y ∈ Metric.ball c R →
      ‖etaDerivPairTerm y m‖ ≤ u m)
    (y₀ : ℂ) (hy₀ : y₀ ∈ Metric.ball c R)
    (h0 : Summable (fun m => pairFn m y₀))
    (y : ℂ) (hy : y ∈ Metric.ball c R) :
    HasDerivAt (fun z => ∑' m, pairFn m z) (∑' m, etaDerivPairTerm y m) y :=
  hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (Convex.isPreconnected (convex_ball c R)) hderiv hbound hy₀ h0 hy

/-- `deriv` reading of the bridge: under the same uniform premises, `deriv`
of the pair-tsum is the tsum of `etaDerivPairTerm`. -/
theorem etaPair_tsum_deriv_of_uniformBound
    (pairFn : ℕ → ℂ → ℂ) (u : ℕ → ℝ)
    (c : ℂ) (R : ℝ)
    (hu : Summable u)
    (hderiv : ∀ m y, y ∈ Metric.ball c R →
      HasDerivAt (pairFn m) (etaDerivPairTerm y m) y)
    (hbound : ∀ m y, y ∈ Metric.ball c R →
      ‖etaDerivPairTerm y m‖ ≤ u m)
    (y₀ : ℂ) (hy₀ : y₀ ∈ Metric.ball c R)
    (h0 : Summable (fun m => pairFn m y₀))
    (y : ℂ) (hy : y ∈ Metric.ball c R) :
    deriv (fun z => ∑' m, pairFn m z) y = ∑' m, etaDerivPairTerm y m :=
  (etaPair_tsum_hasDerivAt_of_uniformBound pairFn u c R hu hderiv hbound
    y₀ hy₀ h0 y hy).deriv

/-- Local cpow-difference mirror of the banked `etaPairTerm_eq_cpow_sub` shape
(no new import; `zeta_rigorous` stays out of the closure). -/
noncomputable def etaPairCpow (m : ℕ) (s : ℂ) : ℂ :=
  (((((2 * m + 1 : ℕ) : ℝ)) : ℂ) ^ (-s)) -
    (((((2 * m + 2 : ℕ) : ℝ)) : ℂ) ^ (-s))

/-- TERMWISE link, one shape: `HasDerivAt` of the cpow-difference pair with
derivative `etaDerivPairTerm`. From banked `HasDerivAt.const_cpow`
(`Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean:214`) plus
`Complex.ofReal_log`, matching the closed form `etaPairDeriv_term`. -/
theorem etaPairCpow_hasDerivAt (m : ℕ) (s : ℂ) :
    HasDerivAt (etaPairCpow m) (etaDerivPairTerm s m) s := by
  have hAposR : (0 : ℝ) < (((2 * m + 1 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (by omega)
  have hBposR : (0 : ℝ) < (((2 * m + 2 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (by omega)
  have hAne : (((((2 * m + 1 : ℕ) : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hAposR
  have hBne : (((((2 * m + 2 : ℕ) : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hBposR
  have hf : HasDerivAt (fun t : ℂ => -t) (-1 : ℂ) s :=
    hasDerivAt_neg' s
  have hA : HasDerivAt (fun t : ℂ => (((((2 * m + 1 : ℕ) : ℝ)) : ℂ) ^ (-t)))
      (((((2 * m + 1 : ℕ) : ℝ)) : ℂ) ^ (-s) *
        Complex.log (((((2 * m + 1 : ℕ) : ℝ)) : ℂ)) * (-1)) s :=
    hf.const_cpow (c := (((((2 * m + 1 : ℕ) : ℝ)) : ℂ)) (Or.inl hAne)
  have hB : HasDerivAt (fun t : ℂ => (((((2 * m + 2 : ℕ) : ℝ)) : ℂ) ^ (-t)))
      (((((2 * m + 2 : ℕ) : ℝ)) : ℂ) ^ (-s) *
        Complex.log (((((2 * m + 2 : ℕ) : ℝ)) : ℂ)) * (-1)) s :=
    hf.const_cpow (c := (((((2 * m + 2 : ℕ) : ℝ)) : ℂ)) (Or.inl hBne)
  have hSub := hA.sub hB
  have hlogA : Complex.log (((((2 * m + 1 : ℕ) : ℝ)) : ℂ) =
      (((Real.log (((2 * m + 1 : ℕ) : ℝ))) : ℝ) : ℂ) :=
    (Complex.ofReal_log (le_of_lt hAposR)).symm
  have hlogB : Complex.log (((((2 * m + 2 : ℕ) : ℝ)) : ℂ) =
      (((Real.log (((2 * m + 2 : ℕ) : ℝ))) : ℝ) : ℂ) :=
    (Complex.ofReal_log (le_of_lt hBposR)).symm
  have hDerivEq : (((((2 * m + 1 : ℕ) : ℝ)) : ℂ) ^ (-s) *
      Complex.log (((((2 * m + 1 : ℕ) : ℝ)) : ℂ)) * (-1) -
        (((((2 * m + 2 : ℕ) : ℝ)) : ℂ) ^ (-s) *
          Complex.log (((((2 * m + 2 : ℕ) : ℝ)) : ℂ)) * (-1)) =
      etaDerivPairTerm s m := by
    rw [etaPairDeriv_term, hlogA, hlogB, Complex.ofReal_neg, Complex.ofReal_neg]
    ring
  have hFunEq : (fun t : ℂ => (((((2 * m + 1 : ℕ) : ℝ)) : ℂ) ^ (-t)) -
      (((((2 * m + 2 : ℕ) : ℝ)) : ℂ) ^ (-t))) = etaPairCpow m := by
    funext t
    rfl
  rw [hFunEq, hDerivEq] at hSub
  exact hSub

/-- MAJORANT disc: center `3`, radius `1 / 2`, so every `y` in the ball
has `5 / 2 ≤ y.re` (hence `0 < y.re`). -/
noncomputable def etaMajCenter : ℂ := ((3 : ℝ) : ℂ)

noncomputable def etaMajRadius : ℝ := 1 / 2

/-- The single uniform majorant on the disc above, assembled from the RHS of
`etaDerivBound` (`:43-46`) with `‖s‖` replaced by `7 / 2` and `s.re`
replaced by the worst-case exponent `5 / 2`. -/
noncomputable def etaDerivMajorant (m : ℕ) : ℝ :=
  Real.log ((((2 * m + 2 : ℕ)) : ℝ)) * (7 / 2) *
    ((((2 * m + 1 : ℕ)) : ℝ) ^ (-(5 / 2 : ℝ) - 1)) +
    (Real.log ((((2 * m + 2 : ℕ)) : ℝ)) - Real.log ((((2 * m + 1 : ℕ)) : ℝ))) *
      ((((2 * m + 1 : ℕ)) : ℝ) ^ (-(5 / 2 : ℝ)))

/-- Pointwise majorant bound on the explicit disc, from `etaDerivPair_bound`
(`:133-134`) plus worst-case `‖y‖` / rpow monotonicity.
Cited shapes: `Complex.abs_re_le_norm`, `Real.rpow_le_rpow_of_exponent_le`,
`Real.log_le_log`, `Real.log_nonneg`, `Summable.of_norm_bounded` (latter used
only by the conditional wrapper below). -/
theorem etaDerivMajorant_bound (m : ℕ) (y : ℂ)
    (hy : y ∈ Metric.ball etaMajCenter etaMajRadius) :
    ‖etaDerivPairTerm y m‖ ≤ etaDerivMajorant m := by
  have hball : dist y etaMajCenter < etaMajRadius := Metric.mem_ball.mp hy
  have hR : etaMajRadius = 1 / 2 := by rfl
  rw [hR] at hball
  have hdist : ‖y - etaMajCenter‖ < 1 / 2 := by
    rw [dist_eq_norm] at hball
    exact hball
  have hc_re : etaMajCenter.re = 3 := by
    unfold etaMajCenter
    rw [Complex.ofReal_re]
  have hc_norm : ‖etaMajCenter‖ = 3 := by
    unfold etaMajCenter
    have hnn : (0 : ℝ) ≤ 3 := by norm_num
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  have hre_abs : |y.re - etaMajCenter.re| ≤ ‖y - etaMajCenter‖ := by
    have h := Complex.abs_re_le_norm (y - etaMajCenter)
    rw [Complex.sub_re] at h
    exact h
  rw [hc_re] at hre_abs
  have hre_lo : 5 / 2 ≤ y.re := by
    have hlt : |y.re - 3| < 1 / 2 := lt_of_le_of_lt hre_abs hdist
    have h := (abs_lt.mp hlt).1
    linarith
  have hypos : 0 < y.re := by linarith
  have hnorm_y : ‖y‖ ≤ 7 / 2 := by
    have htri : ‖y‖ ≤ ‖etaMajCenter‖ + ‖y - etaMajCenter‖ := by
      have heq : y = etaMajCenter + (y - etaMajCenter) :=
        add_sub_cancel _ _
      rw [heq]
      exact norm_add_le _ _
    rw [hc_norm] at htri
    linarith
  have hApos : (0 : ℝ) < ((((2 * m + 1 : ℕ)) : ℝ)) :=
    Nat.cast_pos.mpr (by omega)
  have h1le : (1 : ℝ) ≤ ((((2 * m + 1 : ℕ)) : ℝ)) := by
    exact_mod_cast (by omega : 1 ≤ 2 * m + 1)
  have hB1le : (1 : ℝ) ≤ ((((2 * m + 2 : ℕ)) : ℝ)) := by
    exact_mod_cast (by omega : 1 ≤ 2 * m + 2)
  have hAB : ((((2 * m + 1 : ℕ)) : ℝ)) ≤ ((((2 * m + 2 : ℕ)) : ℝ)) := by
    exact_mod_cast (by omega : 2 * m + 1 ≤ 2 * m + 2)
  have hlogB_nn : 0 ≤ Real.log ((((2 * m + 2 : ℕ)) : ℝ)) :=
    Real.log_nonneg hB1le
  have hlog_mono : Real.log ((((2 * m + 1 : ℕ)) : ℝ)) ≤
      Real.log ((((2 * m + 2 : ℕ)) : ℝ)) :=
    Real.log_le_log hApos hAB
  have hDnn : 0 ≤ Real.log ((((2 * m + 2 : ℕ)) : ℝ)) -
      Real.log ((((2 * m + 1 : ℕ)) : ℝ)) := sub_nonneg.mpr hlog_mono
  have hexp1 : -y.re - 1 ≤ -(5 / 2 : ℝ) - 1 := by linarith
  have hexp2 : -y.re ≤ -(5 / 2 : ℝ) := by linarith
  have hrpow1 : ((((2 * m + 1 : ℕ)) : ℝ)) ^ (-y.re - 1) ≤
      ((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ) - 1) :=
    Real.rpow_le_rpow_of_exponent_le h1le hexp1
  have hrpow2 : ((((2 * m + 1 : ℕ)) : ℝ)) ^ (-y.re) ≤
      ((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le h1le hexp2
  have hbound_y := etaDerivPair_bound y hypos m
  have hle : etaDerivBound y m ≤ etaDerivMajorant m := by
    unfold etaDerivBound etaDerivMajorant
    have hCnn : 0 ≤ Real.log ((((2 * m + 2 : ℕ)) : ℝ)) * (7 / 2) :=
      mul_nonneg hlogB_nn (by norm_num)
    have hXnn : 0 ≤ ((((2 * m + 1 : ℕ)) : ℝ)) ^ (-y.re - 1) :=
      Real.rpow_nonneg (le_of_lt hApos) _
    have ha : Real.log ((((2 * m + 2 : ℕ)) : ℝ)) * ‖y‖ ≤
        Real.log ((((2 * m + 2 : ℕ)) : ℝ)) * (7 / 2) :=
      mul_le_mul_of_nonneg_left hnorm_y hlogB_nn
    have hb : (Real.log ((((2 * m + 2 : ℕ)) : ℝ)) * ‖y‖) *
        ((((2 * m + 1 : ℕ)) : ℝ)) ^ (-y.re - 1) ≤
        (Real.log ((((2 * m + 2 : ℕ)) : ℝ)) * (7 / 2)) *
        ((((2 * m + 1 : ℕ)) : ℝ)) ^ (-y.re - 1) :=
      mul_le_mul_of_nonneg_right ha hXnn
    have hc : (Real.log ((((2 * m + 2 : ℕ)) : ℝ)) * (7 / 2)) *
        ((((2 * m + 1 : ℕ)) : ℝ)) ^ (-y.re - 1) ≤
        (Real.log ((((2 * m + 2 : ℕ)) : ℝ)) * (7 / 2)) *
        ((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hrpow1 hCnn
    have e1 : Real.log ((((2 * m + 2 : ℕ)) : ℝ)) * ‖y‖ *
        ((((2 * m + 1 : ℕ)) : ℝ)) ^ (-y.re - 1) ≤
        Real.log ((((2 * m + 2 : ℕ)) : ℝ)) * (7 / 2) *
        ((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ) - 1) :=
      le_trans hb hc
    have e2 : (Real.log ((((2 * m + 2 : ℕ)) : ℝ)) -
        Real.log ((((2 * m + 1 : ℕ)) : ℝ))) *
        ((((2 * m + 1 : ℕ)) : ℝ)) ^ (-y.re) ≤
        (Real.log ((((2 * m + 2 : ℕ)) : ℝ)) -
          Real.log ((((2 * m + 1 : ℕ)) : ℝ))) *
        ((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hrpow2 hDnn
    exact add_le_add e1 e2
  exact le_trans hbound_y hle

/-- SUMMABILITY, conditional wrapper (GAP noted).
Unconditional `Summable etaDerivMajorant` is not yet banked: it needs an
explicit pure-power dominator with a log-factor comparison plus a banked
p-series summability fact. This wrapper reduces it to any such dominator
`B`, so the `:297` bridge premise `Summable u` is discharged as soon as a
concrete `B` with `hB` and `hdom` is supplied. -/
theorem etaDerivMajorant_summable_of_dom (B : ℕ → ℝ) (hB : Summable B)
    (hdom : ∀ m : ℕ, ‖etaDerivMajorant m‖ ≤ B m) :
    Summable etaDerivMajorant :=
  Summable.of_norm_bounded hB hdom

/-- DOMINATOR: explicit pure-power `B m = 8 / (m+1)^2` in rpow form.
Shape `C * ((m+1):R)^(-2)`; `p = 2 > 1` for the p-series route. -/
noncomputable def etaDerivDominator (m : ℕ) : ℝ :=
  8 * (((((m + 1 : ℕ)) : ℝ)) ^ (-2 : ℝ))

/-- Shift-series summability `(m+1)^(-2)` via `Real.summable_nat_rpow_inv`
plus `summable_nat_add_iff` (mirrors `R02_D3_shift195_summable`,
`d3shift32_summable7` shapes). -/
theorem etaDerivShift2_summable :
    Summable (fun n : ℕ => ((((n + 1 : ℕ)) : ℝ)) ^ (-2 : ℝ)) := by
  have hp1 : (1 : ℝ) < (1 : ℝ) + 1 := by norm_num
  have hbase : Summable (fun n : ℕ => ((((n : ℝ)) ^ ((1 : ℝ) + 1)))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hp1
  have hshift :
      Summable (fun m : ℕ => ((((m + 1 : ℕ) : ℝ) ^ ((1 : ℝ) + 1)))⁻¹) :=
    (summable_nat_add_iff 1).mpr hbase
  have heq : (fun n : ℕ => ((((n + 1 : ℕ)) : ℝ)) ^ (-2 : ℝ)) =
      (fun m : ℕ => ((((m + 1 : ℕ) : ℝ) ^ ((1 : ℝ) + 1)))⁻¹) := by
    funext m
    have eR : (-2 : ℝ) = -((1 : ℝ) + 1) := by norm_num
    rw [eR, Real.rpow_neg (Nat.cast_nonneg _)]
  rw [heq]
  exact hshift

/-- Dominator summability via `Summable.mul_left`. -/
theorem etaDerivDominator_summable : Summable etaDerivDominator := by
  have h2 := etaDerivShift2_summable
  unfold etaDerivDominator
  exact Summable.mul_left 8 h2

/-- Log-factor bound `log (2m+2) ≤ (2m+2)` from
`Real.log_le_sub_one_of_pos`. -/
theorem eta_logBp_le (m : ℕ) :
    Real.log (((((2 * m + 2 : ℕ)) : ℝ))) ≤ (((((2 * m + 2 : ℕ)) : ℝ))) := by
  have hpos : (0 : ℝ) < (((((2 * m + 2 : ℕ)) : ℝ))) :=
    Nat.cast_pos.mpr (by omega)
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

/-- Log-difference bound `log(2m+2) - log(2m+1) ≤ (2m+1)⁻¹` from
`Real.log_le_sub_one_of_pos` applied to the ratio plus `Real.log_div`. -/
theorem eta_logDiff_le (m : ℕ) :
    Real.log (((((2 * m + 2 : ℕ)) : ℝ))) -
      Real.log (((((2 * m + 1 : ℕ)) : ℝ))) ≤
      (((((2 * m + 1 : ℕ)) : ℝ)))⁻¹ := by
  have hApos : (0 : ℝ) < (((((2 * m + 1 : ℕ)) : ℝ))) :=
    Nat.cast_pos.mpr (by omega)
  have hBpos : (0 : ℝ) < (((((2 * m + 2 : ℕ)) : ℝ))) :=
    Nat.cast_pos.mpr (by omega)
  have hAne : (((((2 * m + 1 : ℕ)) : ℝ))) ≠ 0 := ne_of_gt hApos
  have hBeq : (((((2 * m + 2 : ℕ)) : ℝ))) =
      (((((2 * m + 1 : ℕ)) : ℝ))) + 1 := by
    have heq : 2 * m + 1 + 1 = 2 * m + 2 := by omega
    calc (((((2 * m + 2 : ℕ)) : ℝ)))
        = (((((2 * m + 1 + 1 : ℕ)) : ℝ))) := by rw [heq]
      _ = (((((2 * m + 1 : ℕ)) : ℝ))) + 1 := by
          rw [Nat.cast_add, Nat.cast_one]
  have hratio_pos :
      (0 : ℝ) < (((((2 * m + 2 : ℕ)) : ℝ))) / (((((2 * m + 1 : ℕ)) : ℝ))) :=
    div_pos hBpos hApos
  have hlog_le :=
    Real.log_le_sub_one_of_pos hratio_pos
  have hlog_eq : Real.log ((((((2 * m + 2 : ℕ)) : ℝ))) /
      (((((2 * m + 1 : ℕ)) : ℝ)))) =
      Real.log (((((2 * m + 2 : ℕ)) : ℝ))) -
        Real.log (((((2 * m + 1 : ℕ)) : ℝ))) :=
    Real.log_div (ne_of_gt hBpos) (ne_of_gt hApos)
  have hratio_eq : (((((2 * m + 2 : ℕ)) : ℝ))) /
      (((((2 * m + 1 : ℕ)) : ℝ))) - 1 =
      (((((2 * m + 1 : ℕ)) : ℝ)))⁻¹ := by
    rw [hBeq]
    field_simp
    ring
  linarith

/-- Majorant is nonnegative (both pieces). -/
theorem etaDerivMajorant_nonneg (m : ℕ) : 0 ≤ etaDerivMajorant m := by
  unfold etaDerivMajorant
  have hApos : (0 : ℝ) < (((((2 * m + 1 : ℕ)) : ℝ))) :=
    Nat.cast_pos.mpr (by omega)
  have hB1le : (1 : ℝ) ≤ (((((2 * m + 2 : ℕ)) : ℝ))) := by
    exact_mod_cast (by omega : 1 ≤ 2 * m + 2)
  have hAB : (((((2 * m + 1 : ℕ)) : ℝ))) ≤ (((((2 * m + 2 : ℕ)) : ℝ))) := by
    exact_mod_cast (by omega : 2 * m + 1 ≤ 2 * m + 2)
  have hlogB_nn : 0 ≤ Real.log (((((2 * m + 2 : ℕ)) : ℝ))) :=
    Real.log_nonneg hB1le
  have hlog_mono : Real.log (((((2 * m + 1 : ℕ)) : ℝ))) ≤
      Real.log (((((2 * m + 2 : ℕ)) : ℝ))) :=
    Real.log_le_log hApos hAB
  have hDnn : 0 ≤ Real.log (((((2 * m + 2 : ℕ)) : ℝ))) -
      Real.log (((((2 * m + 1 : ℕ)) : ℝ))) := sub_nonneg.mpr hlog_mono
  have hr7nn : 0 ≤ (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ) - 1)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hr5nn : 0 ≤ (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ))) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 : 0 ≤ Real.log (((((2 * m + 2 : ℕ)) : ℝ))) * (7 / 2) *
      (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ) - 1)) := by
    exact mul_nonneg (mul_nonneg hlogB_nn (by norm_num)) hr7nn
  have h2 : 0 ≤ (Real.log (((((2 * m + 2 : ℕ)) : ℝ))) -
      Real.log (((((2 * m + 1 : ℕ)) : ℝ)))) *
      (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ))) :=
    mul_nonneg hDnn hr5nn
  exact add_nonneg h1 h2

/-- Pure-power domination `etaDerivMajorant m ≤ etaDerivDominator m`.
Crude log bounds (`eta_logBp_le`, `eta_logDiff_le`) plus rpow
monotonicity (`Real.rpow_le_rpow_of_nonpos`,
`Real.rpow_le_rpow_of_exponent_le`) and one `Real.rpow_add`
fold for `n * n^(-7/2) = n^(-5/2)`. -/
theorem etaDerivMajorant_le_dominator (m : ℕ) :
    etaDerivMajorant m ≤ etaDerivDominator m := by
  have hApos : (0 : ℝ) < (((((2 * m + 1 : ℕ)) : ℝ))) :=
    Nat.cast_pos.mpr (by omega)
  have hn1pos : (0 : ℝ) < (((((m + 1 : ℕ)) : ℝ))) :=
    Nat.cast_pos.mpr (by omega)
  have h1leA : (1 : ℝ) ≤ (((((2 * m + 1 : ℕ)) : ℝ))) := by
    exact_mod_cast (by omega : 1 ≤ 2 * m + 1)
  have h1len1 : (1 : ℝ) ≤ (((((m + 1 : ℕ)) : ℝ))) := by
    exact_mod_cast (by omega : 1 ≤ m + 1)
  have hn1leA : (((((m + 1 : ℕ)) : ℝ))) ≤ (((((2 * m + 1 : ℕ)) : ℝ))) := by
    exact_mod_cast (by omega : m + 1 ≤ 2 * m + 1)
  have hBp_eq : (((((2 * m + 2 : ℕ)) : ℝ))) = 2 * (((((m + 1 : ℕ)) : ℝ))) := by
    have heqN : 2 * m + 2 = 2 * (m + 1) := by omega
    calc (((((2 * m + 2 : ℕ)) : ℝ)))
        = (((((2 * (m + 1) : ℕ)) : ℝ))) := by rw [heqN]
      _ = 2 * (((((m + 1 : ℕ)) : ℝ))) := by push_cast; ring
  have he7 : (-(5 / 2 : ℝ) - 1) ≤ 0 := by norm_num
  have he5 : (-(5 / 2 : ℝ)) ≤ 0 := by norm_num
  have he52 : (-(5 / 2 : ℝ)) ≤ (-2 : ℝ) := by norm_num
  have hlogBp := eta_logBp_le m
  have hlogD := eta_logDiff_le m
  have hr7nn : 0 ≤ (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ) - 1)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hr5nn : 0 ≤ (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ))) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hn17nn : 0 ≤ (((((m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ) - 1)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hr7mono : (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ) - 1)) ≤
      (((((m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ) - 1)) :=
    Real.rpow_le_rpow_of_nonpos hn1pos hn1leA he7
  have hr5mono : (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ))) ≤
      (((((m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ))) :=
    Real.rpow_le_rpow_of_nonpos hn1pos hn1leA he5
  have h52mono : (((((m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ))) ≤
      (((((m + 1 : ℕ)) : ℝ)) ^ (-2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le h1len1 he52
  have hDle1 : Real.log (((((2 * m + 2 : ℕ)) : ℝ))) -
      Real.log (((((2 * m + 1 : ℕ)) : ℝ))) ≤ 1 := by
    have hinv : (((((2 * m + 1 : ℕ)) : ℝ)))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ h1leA
    exact le_trans hlogD hinv
  have hfold : (((((m + 1 : ℕ)) : ℝ))) *
      (((((m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ) - 1)) =
      (((((m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ))) := by
    have hn1_eq : (((((m + 1 : ℕ)) : ℝ))) =
        (((((m + 1 : ℕ)) : ℝ)) ^ (1 : ℝ)) := (Real.rpow_one _).symm
    have h1 : (1 : ℝ) + (-(5 / 2 : ℝ) - 1) = -(5 / 2 : ℝ) := by ring
    rw [hn1_eq, ← Real.rpow_add hn1pos, h1]
  have eT1a : Real.log (((((2 * m + 2 : ℕ)) : ℝ))) * (7 / 2) *
      (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ) - 1)) ≤
      (((((2 * m + 2 : ℕ)) : ℝ))) * (7 / 2) *
      (((((m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ) - 1)) := by
    have ha : Real.log (((((2 * m + 2 : ℕ)) : ℝ))) * (7 / 2) ≤
        (((((2 * m + 2 : ℕ)) : ℝ))) * (7 / 2) :=
      mul_le_mul_of_nonneg_right hlogBp (by norm_num)
    exact mul_le_mul_of_nonneg_right ha hn17nn
  have eT1b : (((((2 * m + 2 : ℕ)) : ℝ))) * (7 / 2) *
      (((((m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ) - 1)) =
      7 * (((((m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ))) := by
    rw [hBp_eq, ← hfold]
    ring
  have eT1 : Real.log (((((2 * m + 2 : ℕ)) : ℝ))) * (7 / 2) *
      (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ) - 1)) ≤
      7 * (((((m + 1 : ℕ)) : ℝ)) ^ (-2 : ℝ)) := by
    have hstep : (((((2 * m + 2 : ℕ)) : ℝ))) * (7 / 2) *
        (((((m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ) - 1)) ≤
        7 * (((((m + 1 : ℕ)) : ℝ)) ^ (-2 : ℝ)) := by
      rw [eT1b]
      have hmul : 7 * (((((m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ))) ≤
          7 * (((((m + 1 : ℕ)) : ℝ)) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left h52mono (by norm_num)
      exact hmul
    exact le_trans eT1a hstep
  have eT2 : (Real.log (((((2 * m + 2 : ℕ)) : ℝ))) -
      Real.log (((((2 * m + 1 : ℕ)) : ℝ)))) *
      (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ))) ≤
      1 * (((((m + 1 : ℕ)) : ℝ)) ^ (-2 : ℝ)) := by
    have ha : (Real.log (((((2 * m + 2 : ℕ)) : ℝ))) -
        Real.log (((((2 * m + 1 : ℕ)) : ℝ)))) *
        (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ))) ≤
        1 * (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_right hDle1 hr5nn
    have hb : 1 * (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ))) ≤
        1 * (((((m + 1 : ℕ)) : ℝ)) ^ (-2 : ℝ)) := by
      have hle : (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ))) ≤
          (((((m + 1 : ℕ)) : ℝ)) ^ (-2 : ℝ)) :=
        le_trans hr5mono h52mono
      exact mul_le_mul_of_nonneg_left hle (by norm_num)
    exact le_trans ha hb
  unfold etaDerivMajorant etaDerivDominator
  have hfin : Real.log (((((2 * m + 2 : ℕ)) : ℝ))) * (7 / 2) *
      (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ) - 1)) +
      (Real.log (((((2 * m + 2 : ℕ)) : ℝ))) -
        Real.log (((((2 * m + 1 : ℕ)) : ℝ)))) *
      (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(5 / 2 : ℝ))) ≤
      7 * (((((m + 1 : ℕ)) : ℝ)) ^ (-2 : ℝ)) +
      1 * (((((m + 1 : ℕ)) : ℝ)) ^ (-2 : ℝ)) :=
    add_le_add eT1 eT2
  have hrw : 7 * (((((m + 1 : ℕ)) : ℝ)) ^ (-2 : ℝ)) +
      1 * (((((m + 1 : ℕ)) : ℝ)) ^ (-2 : ℝ)) =
      8 * (((((m + 1 : ℕ)) : ℝ)) ^ (-2 : ℝ)) := by ring
  rw [hrw] at hfin
  exact hfin

/-- Norm domination for the existing conditional wrapper. -/
theorem etaDerivMajorant_norm_le_dominator (m : ℕ) :
    ‖etaDerivMajorant m‖ ≤ etaDerivDominator m := by
  have hnn := etaDerivMajorant_nonneg m
  have hle := etaDerivMajorant_le_dominator m
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hle

/-- Unconditional summability: discharges `etaDerivMajorant_summable_of_dom`. -/
theorem etaDerivMajorant_summable : Summable etaDerivMajorant :=
  etaDerivMajorant_summable_of_dom etaDerivDominator
    etaDerivDominator_summable etaDerivMajorant_norm_le_dominator

/-- Shifted Basel value in rpow form, via `hasSum_zeta_two`
(`Mathlib/NumberTheory/ZetaValues.lean:452`) plus `Summable.tsum_eq_zero_add`
(zero term vanishes). Cited shapes: `hasSum_zeta_two.summable/.tsum_eq`
(`zeta_rigorous.lean:32137/32139`), `Summable.tsum_eq_zero_add`
(`ApproxZetaLowerBound.lean:71`). -/
theorem etaDerivShift2_tsum_eq :
    ∑' n : ℕ, (((((n + 1 : ℕ)) : ℝ)) ^ (-2 : ℝ)) = Real.pi ^ 2 / 6 := by
  have hB : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) :=
    hasSum_zeta_two
  have hBsum : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    hB.summable
  have hval : (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) = Real.pi ^ 2 / 6 :=
    hB.tsum_eq
  have h0 : ((fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 0) = 0 := by
    simp
  have hshift := hBsum.tsum_eq_zero_add
  have hzero : (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) =
      ∑' n : ℕ, (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ^ 2 := by
    rw [hshift, h0, zero_add]
  have hterm : (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ^ 2) =
      (fun n : ℕ => (((((n + 1 : ℕ)) : ℝ)) ^ (-2 : ℝ))) := by
    funext n
    have hnpos : (0 : ℝ) ≤ (((((n + 1 : ℕ)) : ℝ))) := Nat.cast_nonneg _
    have eR : (-2 : ℝ) = -((2 : ℝ)) := by norm_num
    rw [eR, Real.rpow_neg hnpos, Real.rpow_two, one_div]
  have hshiftval : (∑' n : ℕ, (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ^ 2) =
      Real.pi ^ 2 / 6 := by
    rw [← hzero]
    exact hval
  rw [← hterm]
  exact hshiftval

/-- Dominator tsum value via `Summable.tsum_mul_left` factoring plus
`etaDerivShift2_tsum_eq`. Cited shapes: `Summable.tsum_mul_left`
(`zeta_rigorous.lean:2128`), `tsum_mul_left`
(`Counterexamples/NowhereDifferentiable.lean:213`). -/
theorem etaDerivDominator_tsum_eq :
    ∑' m : ℕ, etaDerivDominator m = 8 * (Real.pi ^ 2 / 6) := by
  have h2 := etaDerivShift2_tsum_eq
  unfold etaDerivDominator
  rw [tsum_mul_left, h2]

/-- TSUM VALUE bound: majorant tsum dominated by the explicit `Deta`
`8 * (π ^ 2 / 6)` via `Summable.tsum_le_tsum` comparison with the dominator.
Cited shapes: `Summable.tsum_le_tsum` (`door3_eta_prime.lean:228`),
`norm_tsum_le_tsum_norm`
(`Mathlib/Analysis/Normed/Group/InfiniteSum.lean:149`). -/
theorem etaDerivMajorant_tsum_le :
    ∑' m : ℕ, etaDerivMajorant m ≤ 8 * (Real.pi ^ 2 / 6) := by
  have hle : ∀ m : ℕ, etaDerivMajorant m ≤ etaDerivDominator m :=
    etaDerivMajorant_le_dominator
  have hD := etaDerivDominator_tsum_eq
  calc ∑' m : ℕ, etaDerivMajorant m ≤ ∑' m : ℕ, etaDerivDominator m :=
        Summable.tsum_le_tsum hle etaDerivMajorant_summable
          etaDerivDominator_summable
    _ = 8 * (Real.pi ^ 2 / 6) := hD

/-- Identification: local cpow-difference mirror equals the rigorous pair term.
Cycle check: `zeta_rigorous` imports only `Mathlib` + `Zeta23.MV.Final`
(`zeta_rigorous.lean:1-2`), and no `Zeta23/*` file imports any `door3_*`
file, so `import zeta_rigorous` above creates no cycle. Proof is the banked
`etaPairTerm_eq_cpow_sub` (`zeta_rigorous.lean:839`) read against the local
`etaPairCpow` def (`:331-333`); note the argument order is `(m s)` locally
vs `(s m)` in `zeta_rigorous`. -/
theorem etaPairCpow_eq_etaPairTerm (m : ℕ) (s : ℂ) :
    etaPairCpow m s = zeta_rigorous.etaPairTerm s m := by
  unfold etaPairCpow
  rw [zeta_rigorous.etaPairTerm_eq_cpow_sub]

/-!
## DZNUM residual: conversion-factor quotient caps on the R02 rect.

Rect hypotheses (match `R02_D3_*` in `zeta_rigorous`):
`0.05 ≤ s.re`, `s.re ≤ 0.74`, `-8.25 ≤ s.im`, `s.im ≤ -5.25`.

Quotient shape: `deriv zeta s = (etaDerivVal * conv - etaVal * conv') * convInv2`
with `conv s = 1 - 2 ^ (1 - s)`, `conv' s = 2 ^ (1 - s) * log 2`,
`convInv2 s = ((conv s)⁻¹) ^ 2`. Caps banked below:
* `C0`: `‖conv‖ ≤ 3`;
* `C1`: `‖conv'‖ ≤ 2`;
* `C2`: `‖convInv2‖ ≤ 31` from `0.18 ≤ ‖conv‖`;
* `VEta`: `‖etaHurwitz s‖ ≤ 168` (eta-value cap).
-/

/-- Conversion factor `conv s = 1 - 2 ^ (1 - s)` (matches `etaRHS` factor). -/
noncomputable def etaConv (s : ℂ) : ℂ :=
  1 - (2 : ℂ) ^ ((1 : ℂ) - s)

/-- Conversion-factor derivative value `2 ^ (1 - s) * log 2`. -/
noncomputable def etaConvDeriv (s : ℂ) : ℂ :=
  (2 : ℂ) ^ ((1 : ℂ) - s) * Complex.log 2

/-- Squared inverse factor for the quotient `(...)/conv^2`. -/
noncomputable def etaConvInvSq (s : ℂ) : ℂ :=
  ((etaConv s)⁻¹) ^ 2

/-- Lower bound `0.18 ≤ ‖conv‖` for `s.re ≤ 0.74`: direct restatement of
banked `zeta_rigorous.R02_D3_cvtFactor_ge` via the new import. -/
theorem etaConv_ge_R02 (s : ℂ) (hre_hi : s.re ≤ 0.74) :
    (0.18 : ℝ) ≤ ‖etaConv s‖ := by
  unfold etaConv
  exact zeta_rigorous.R02_D3_cvtFactor_ge s hre_hi

/-- `conv s ≠ 0` on the R02 rect (from the `0.18` lower bound). -/
theorem etaConv_ne_R02 (s : ℂ) (hre_hi : s.re ≤ 0.74) :
    etaConv s ≠ 0 := by
  have hpos : (0 : ℝ) < ‖etaConv s‖ :=
    lt_of_lt_of_le (by norm_num) (etaConv_ge_R02 s hre_hi)
  exact norm_pos_iff.mp hpos

/-- Upper cap `C0`: `‖conv‖ ≤ 3` for `0.05 ≤ s.re`.
`‖1 - w‖ ≤ 1 + ‖w‖` plus `‖2 ^ (1 - s)‖ = 2 ^ (1 - s.re) ≤ 2 ^ 1 = 2`. -/
theorem etaConv_upper_R02 (s : ℂ) (hre_lo : 0.05 ≤ s.re) :
    ‖etaConv s‖ ≤ 3 := by
  have hre1 : (((1 : ℂ) - s).re) = 1 - s.re := by
    rw [Complex.sub_re, Complex.one_re]
  have hbase : (2 : ℂ) = ((((2 : ℝ))) : ℂ) := by norm_cast
  have hnorm : ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ = (2 : ℝ) ^ (((1 : ℂ) - s).re) := by
    rw [hbase]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
  have hexp_le : (((1 : ℂ) - s).re) ≤ 1 := by
    rw [hre1]
    linarith
  have hw_le : ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ ≤ 2 := by
    rw [hnorm]
    have hle : (2 : ℝ) ^ (((1 : ℂ) - s).re) ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
    rw [Real.rpow_one] at hle
    exact hle
  have htri : ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ ≤
      ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ :=
    norm_sub_le _ _
  have h1 : ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ ≤ 1 + 2 := by
    rw [norm_one]
    exact add_le_add_left hw_le 1
  have hle : ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ ≤ 1 + 2 :=
    le_trans htri h1
  have hfold : etaConv s = (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s) := by
    rfl
  rw [hfold]
  linarith

/-- Eta-value cap `VEta`: `‖etaHurwitz s‖ ≤ 168` on the R02 rect, from
`R02_D3_pairLim_upper` plus `etaPairLim_eq_etaHurwitz_of_pos`. -/
theorem etaVal_upper_R02 (s : ℂ) (hre_lo : 0.05 ≤ s.re) (hre_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25) :
    ‖zeta_rigorous.etaHurwitz s‖ ≤ 168 := by
  have hspos : 0 < s.re := by linarith
  have hPair := zeta_rigorous.R02_D3_pairLim_upper s hre_lo hre_hi him_lo him_hi
  have hEq := zeta_rigorous.etaPairLim_eq_etaHurwitz_of_pos hspos
  rw [← hEq]
  exact hPair

/-- `‖log 2‖ ≤ 1` for the complex log, via `Complex.ofReal_log` and
`dp_log2_hi/lo` (already imported via `door3_dp_terms`). -/
theorem Complex_log2_norm_le_one : ‖Complex.log (2 : ℂ)‖ ≤ 1 := by
  have hbase : (2 : ℂ) = ((((2 : ℝ))) : ℂ) := by norm_cast
  have hlog : Complex.log (2 : ℂ) = ((((Real.log 2 : ℝ))) : ℂ) := by
    rw [hbase]
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog, Complex.norm_real, Real.norm_eq_abs]
  have hhi := dp_log2_hi
  have hlo := dp_log2_lo
  have habs : |Real.log 2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  exact habs

/-- Upper cap `C1`: `‖conv'‖ ≤ 2` for `0.05 ≤ s.re`.
Product of `‖2 ^ (1 - s)‖ ≤ 2` and `‖log 2‖ ≤ 1`. -/
theorem etaConvDeriv_bound_R02 (s : ℂ) (hre_lo : 0.05 ≤ s.re) :
    ‖etaConvDeriv s‖ ≤ 2 := by
  have hre1 : (((1 : ℂ) - s).re) = 1 - s.re := by
    rw [Complex.sub_re, Complex.one_re]
  have hbase : (2 : ℂ) = ((((2 : ℝ))) : ℂ) := by norm_cast
  have hnorm : ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ = (2 : ℝ) ^ (((1 : ℂ) - s).re) := by
    rw [hbase]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
  have hexp_le : (((1 : ℂ) - s).re) ≤ 1 := by
    rw [hre1]
    linarith
  have hw_le : ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ ≤ 2 := by
    rw [hnorm]
    have hle : (2 : ℝ) ^ (((1 : ℂ) - s).re) ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
    rw [Real.rpow_one] at hle
    exact hle
  have hlog_le := Complex_log2_norm_le_one
  unfold etaConvDeriv
  rw [norm_mul]
  have hmul : ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ * ‖Complex.log 2‖ ≤ 2 * 1 :=
    mul_le_mul hw_le hlog_le (norm_nonneg _) (by norm_num)
  rw [mul_one] at hmul
  exact hmul

/-- Upper cap `C2`: `‖convInv2‖ ≤ 31` for `s.re ≤ 0.74`.
From `0.18 ≤ ‖conv‖`: `‖conv‖⁻¹ ≤ 0.18⁻¹`, square gives
`0.18⁻¹ ^ 2 = 30.864... ≤ 31`. -/
theorem etaConvInvSq_bound_R02 (s : ℂ) (hre_hi : s.re ≤ 0.74) :
    ‖etaConvInvSq s‖ ≤ 31 := by
  have hge := etaConv_ge_R02 s hre_hi
  have hpos : (0 : ℝ) < ‖etaConv s‖ :=
    lt_of_lt_of_le (by norm_num) hge
  have hinv_le : ‖etaConv s‖⁻¹ ≤ ((0.18 : ℝ))⁻¹ :=
    (inv_le_inv₀ hpos (by norm_num)).mpr hge
  have hpow_le : (‖etaConv s‖⁻¹) ^ 2 ≤ (((0.18 : ℝ))⁻¹) ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt hpos)) hinv_le 2
  have hval : ((((0.18 : ℝ))⁻¹) ^ 2) ≤ 31 := by norm_num
  have hnorm : ‖etaConvInvSq s‖ = (‖etaConv s‖⁻¹) ^ 2 := by
    unfold etaConvInvSq
    rw [norm_pow, norm_inv]
  rw [hnorm]
  exact le_trans hpow_le hval

/-!
## GAP FILE (not forced): what remains for the DZNUM derivative quotient.

G1 `conv HasDerivAt`: `HasDerivAt etaConv (etaConvDeriv s) s` is not banked.
Route: `HasDerivAt` of `fun t => (1 : ℂ) - t` composed with
`HasDerivAt.const_cpow` for base `2` (mirrors `etaPairCpow_hasDerivAt`),
then sub from constant `1`. Needs the exact `const_cpow` derivative shape
`2 ^ (1 - s) * log 2 * (-1)` folded with negation; left open rather than
guessing the lemma form.

G2 `deriv zeta` quotient identity:
`deriv riemannZeta s = (etaDerivVal * conv - etaVal * conv') * convInv2`
needs differentiability of `riemannZeta` on the R02 rect plus the quotient
rule applied to `etaHurwitz s = conv s * riemannZeta s`
(`etaHurwitz_eq_etaRHS_compl` specialization). No `riemannZeta`
differentiability lemma is imported here; left open.

G3 `etaDerivVal` cap: `‖deriv etaHurwitz s‖` on the R02 rect needs the
uniform-derivative bridge `etaPair_tsum_hasDerivAt_of_uniformBound` with
`u := etaDerivMajorant` (`etaDerivMajorant_summable` banked) plus the
pair-tsum to `etaHurwitz` identity on a disc covering the R02 rect.
The tsum-derivative value `∑' m, etaDerivPairTerm s m` has no numeric cap
yet; left open.

G4 assembly: `VEta = 168`, `C0 = 3`, `C1 = 2`, `C2 = 31` above are banked;
the combined `‖deriv zeta s‖ ≤ (‖etaDerivVal‖ * C0 + VEta * C1) * C2`
is not stated until G2/G3 close.
-/

/-- DNUM numeral `Deta = 8 * (π ^ 2 / 6) ≤ 13.2` via `Real.pi_lt_d4`.

Grepped before writing:
* `Real.pi_lt_d4 : Real.pi < 3.1416` (`Mathlib/Analysis/Real/Pi/Bounds.lean`);
* `Real.pi_pos` for nonnegativity;
* `pow_lt_pow_left₀` for the square monotonicity.
Stated residual: none for this numeral — `3.1416 ^ 2 = 9.86965056`,
`8 * (9.86965056 / 6) = 13.15953408 ≤ 13.2` closed by `norm_num`. -/
theorem etaDerivDeta_num_le :
    8 * (Real.pi ^ 2 / 6) ≤ (13.2 : ℝ) := by
  have hpi := Real.pi_lt_d4
  have hpi_nn : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
  have hsq : Real.pi ^ 2 < (3.1416 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hpi_nn hpi (by norm_num)
  have hdiv : Real.pi ^ 2 / 6 < (3.1416 : ℝ) ^ 2 / 6 := by
    linarith
  have hmul : 8 * (Real.pi ^ 2 / 6) < 8 * (((3.1416 : ℝ) ^ 2 / 6)) := by
    linarith
  have hcap : 8 * (((3.1416 : ℝ) ^ 2 / 6)) ≤ (13.2 : ℝ) := by
    norm_num
  exact le_trans (le_of_lt hmul) hcap

/-- DNUM assembly on the majorant disc: `‖∑' m, etaDerivPairTerm y m‖ ≤ Deta`.

Grepped before writing:
* `Summable.tsum_le_tsum` (`door3_eta_prime.lean:228`, `:780-788`);
* `norm_tsum_le_tsum_norm` (`Mathlib/Analysis/Normed/Group/InfiniteSum.lean:149`);
* `Summable.of_norm_bounded` (`door3_eta_prime.lean:501-504`);
* caps `etaConv_upper_R02 :845`, `etaVal_upper_R02 :877`,
  `etaConvDeriv_bound_R02 :901`, `etaConvInvSq_bound_R02 :929` (DZNUM route,
  not needed for this Deta assembly);
* dominator value `etaDerivDominator_tsum_eq :769`,
  majorant tsum `etaDerivMajorant_tsum_le :780`.
No missing premise: norm-summability is closed locally via
`Summable.of_norm_bounded` with `etaDerivMajorant_summable`. -/
theorem etaDeriv_tsum_norm_le_Deta (y : ℂ)
    (hy : y ∈ Metric.ball etaMajCenter etaMajRadius) :
    ‖∑' m : ℕ, etaDerivPairTerm y m‖ ≤ 8 * (Real.pi ^ 2 / 6) := by
  have hpoint : ∀ m : ℕ, ‖etaDerivPairTerm y m‖ ≤ etaDerivMajorant m :=
    fun m => etaDerivMajorant_bound m y hy
  have hFnorm : Summable (fun m : ℕ => ‖etaDerivPairTerm y m‖) := by
    have hdom : ∀ m : ℕ, ‖(‖etaDerivPairTerm y m‖ : ℝ)‖ ≤ etaDerivMajorant m := by
      intro m
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hpoint m
    exact Summable.of_norm_bounded etaDerivMajorant_summable hdom
  have h1 : ‖∑' m : ℕ, etaDerivPairTerm y m‖ ≤
      ∑' m : ℕ, ‖etaDerivPairTerm y m‖ :=
    norm_tsum_le_tsum_norm hFnorm
  have h2 : (∑' m : ℕ, ‖etaDerivPairTerm y m‖) ≤
      ∑' m : ℕ, etaDerivMajorant m :=
    Summable.tsum_le_tsum hpoint hFnorm etaDerivMajorant_summable
  exact le_trans h1 (le_trans h2 etaDerivMajorant_tsum_le)

/-- DNUM numeral assembly: `‖∑' m, etaDerivPairTerm y m‖ ≤ 13.2` on the disc. -/
theorem etaDeriv_tsum_norm_le_132 (y : ℂ)
    (hy : y ∈ Metric.ball etaMajCenter etaMajRadius) :
    ‖∑' m : ℕ, etaDerivPairTerm y m‖ ≤ (13.2 : ℝ) :=
  le_trans (etaDeriv_tsum_norm_le_Deta y hy) etaDerivDeta_num_le

/-- hConvLe feed, generic quotient assembly for the `:1058` consumer shape.

Grepped before writing (read-only):
* `etaDeriv_tsum_norm_le_132 :1029` (disc `center 3, radius 1/2`, `Deta = 13.2`);
* `etaDerivDeta_num_le :982`, `etaDeriv_tsum_norm_le_Deta :1009`;
* caps `etaConv_upper_R02 :845` (`‖conv‖ ≤ 3`),
  `etaVal_upper_R02 :877` (`‖etaHurwitz‖ ≤ 168`),
  `etaConvDeriv_bound_R02 :901` (`‖conv'‖ ≤ 2`),
  `etaConvInvSq_bound_R02 :929` (`‖convInv2‖ ≤ 31`);
* consumer `door3_R02_ball_advance.lean:1051-1058`
  `‖(etaDerivVal * conv - etaVal * conv') * convInv2‖ ≤ DZetaPair`
  with `DZetaPair = (Deta * C0 + VEta * C1) * C2`
  (`R02_DZetaPair_quotient_of_caps :1488`, same norm algebra).
Proved by `norm_mul` + `norm_sub_le` transport; no rect premise needed. -/
theorem etaQuotient_bound_of_caps (Deta VEta C0 C1 C2 : ℝ)
    (hDeta0 : 0 ≤ Deta) (hVEta0 : 0 ≤ VEta)
    (hC00 : 0 ≤ C0) (hC10 : 0 ≤ C1) (hC20 : 0 ≤ C2)
    (etaDerivVal etaVal conv conv' convInv2 : ℂ)
    (hDeriv : ‖etaDerivVal‖ ≤ Deta) (hVal : ‖etaVal‖ ≤ VEta)
    (hC0 : ‖conv‖ ≤ C0) (hC1 : ‖conv'‖ ≤ C1) (hC2 : ‖convInv2‖ ≤ C2) :
    ‖(etaDerivVal * conv - etaVal * conv') * convInv2‖ ≤
      (Deta * C0 + VEta * C1) * C2 := by
  have n1 : ‖etaDerivVal * conv‖ ≤ Deta * C0 := by
    rw [norm_mul]
    exact mul_le_mul hDeriv hC0 (norm_nonneg _) hDeta0
  have n2 : ‖etaVal * conv'‖ ≤ VEta * C1 := by
    rw [norm_mul]
    exact mul_le_mul hVal hC1 (norm_nonneg _) hVEta0
  have hsub : ‖etaDerivVal * conv - etaVal * conv'‖ ≤ Deta * C0 + VEta * C1 :=
    le_trans (norm_sub_le _ _) (add_le_add n1 n2)
  have hcap0 : 0 ≤ Deta * C0 + VEta * C1 :=
    add_nonneg (mul_nonneg hDeta0 hC00) (mul_nonneg hVEta0 hC10)
  rw [norm_mul]
  exact mul_le_mul hsub hC2 (norm_nonneg _) hcap0

/-- hConvLe feed, R02 instantiation with banked caps.
Chains `etaConv_upper_R02`, `etaConvDeriv_bound_R02`,
`etaConvInvSq_bound_R02`, `etaVal_upper_R02` into the generic assembly,
leaving only `‖etaDerivVal‖ ≤ Deta` open (G3). -/
theorem etaConvQuotient_bound_R02 (Deta : ℝ) (hDeta0 : 0 ≤ Deta)
    (s : ℂ) (hre_lo : 0.05 ≤ s.re) (hre_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25)
    (etaDerivVal : ℂ) (hDeriv : ‖etaDerivVal‖ ≤ Deta) :
    ‖(etaDerivVal * etaConv s - zeta_rigorous.etaHurwitz s * etaConvDeriv s) *
      etaConvInvSq s‖ ≤ (Deta * 3 + 168 * 2) * 31 := by
  have hC0 := etaConv_upper_R02 s hre_lo
  have hC1 := etaConvDeriv_bound_R02 s hre_lo
  have hC2 := etaConvInvSq_bound_R02 s hre_hi
  have hV := etaVal_upper_R02 s hre_lo hre_hi him_lo him_hi
  exact etaQuotient_bound_of_caps Deta 168 3 2 31 hDeta0 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) etaDerivVal
    (zeta_rigorous.etaHurwitz s) (etaConv s) (etaConvDeriv s)
    (etaConvInvSq s) hDeriv hV hC0 hC1 hC2

/-- Pure-ℝ numeral for the R02 shape at `Deta = 13.2`: closed by `norm_num`.
Value-only: NOT claimed as a rect bound (see residual below). -/
theorem etaQuotient_R02_num_eq :
    ((13.2 : ℝ) * 3 + 168 * 2) * 31 = (11643.6 : ℝ) := by
  norm_num

/-- Exact residual for the `:1058` feed on the R02 rect.

What is closed above: generic quotient algebra
`etaQuotient_bound_of_caps` plus R02-cap instantiation
`etaConvQuotient_bound_R02` conditional on `‖etaDerivVal‖ ≤ Deta`.
What stays open (G3 link): a uniform `Deta` with
`etaDerivVal = ∑' m, etaDerivPairTerm s m` and
`‖etaDerivVal‖ ≤ Deta` for all `s` with
`0.05 ≤ s.re ≤ 0.74`, `-8.25 ≤ s.im ≤ -5.25`.
Non-transfer note: disc value `13.2` (`etaDeriv_tsum_norm_le_132`)
holds only for `y ∈ Metric.ball etaMajCenter etaMajRadius`
(`y.re ≥ 5 / 2`, `‖y‖ ≤ 7 / 2`, exponent `5 / 2`);
the R02 rect needs exponent `0.05` and `‖s‖ ≤ 8.29`,
so the disc dominator `8 / (m+1)^2` does not dominate there
and `11643.6` is not filed as an R02 bound. -/
def etaR02_hConvLe_residual_spec : Prop :=
  ∃ Deta : ℝ, 0 ≤ Deta ∧
    (∀ s : ℂ, 0.05 ≤ s.re → s.re ≤ 0.74 → -8.25 ≤ s.im → s.im ≤ -5.25 →
      ∀ etaDerivVal : ℂ, etaDerivVal = ∑' m, etaDerivPairTerm s m →
        ‖etaDerivVal‖ ≤ Deta)

/-!
## R02 Deta-link: INTEGRAL-comparison dominator (complementary to ball-side R02DOM p-series route).

Grep record (read-only, before writing; this file only appended below):
* residual `:1109` `etaR02_hConvLe_residual_spec`: needs `‖∑' m, etaDerivPairTerm s m‖ ≤ Deta`
  uniformly on R02 rect `0.05 ≤ s.re ≤ 0.74`, `-8.25 ≤ s.im ≤ -5.25`.
* R02 rect shapes: `zeta_rigorous.R02_D3_pairLim_upper :32536`,
  `R02_D3_cvtFactor_ge` (used at `:830-834`), `etaVal_upper_R02 :877`,
  `R02_etaWorstMajorant` (`door3_R02_ball_advance.lean:1411`,
  `log * 8.29 * (2m+1)^(-0.05-1) + diff * (2m+1)^(-0.05)`),
  `R02_etaWorst_normSq_le_829` (`‖s‖ ≤ 8.29`); ball-side R02DOM p-series attempt
  `:1650-1769` (`R02_etaWorstDominator105`, shift summability, pointwise blocker).
* integral-comparison shapes (reference only, rebuilt locally; `zeta_rigorous` untouched):
  `R02_D3_shift105_summable :34827`, `R02_D3_odd105_le_shift :34843`,
  `R02_D3_odd105_summable :34852`, `R02_D3_rpow105_antitone :34867`,
  `R02_D3_rpow105_integrable :34876`, `R02_D3_tail2_le_integral105 :34882`,
  `R02_D3_integral105_eq :34901` (`= 1 / 0.05`), `R02_D3_tail2_le_20 :34916`,
  `R02_D3_odd105_tsum_le_21 :34933`; `tail105_M15`-style
  (`R02_D3_tail105_M15_le_1761 :41284`) is the same `1.05`-decay integral-tail
  pattern at larger `M`, reference only.
* Mathlib engines: `Real.summable_nat_rpow_inv`, `summable_nat_add_iff`,
  `AntitoneOn.tsum_comp_add_le_integral`, `integrableOn_Ioi_rpow_of_lt`,
  `integral_Ioi_rpow_of_lt`, `Real.antitoneOn_rpow_Ioi_of_exponent_nonpos`.

What is banked here (integral route, different construction from ball-side p-series):
* local R02 majorant `etaDerivMajorantR02` (mirror of worst-case shape, exponent `0.05`);
* full `1.05`-decay integral tail locally: shift/odd summability, antitone,
  integrability, tail-vs-integral, closed form `1 / 0.05`, tail `≤ 20`, odd tsum `≤ 21`;
* second majorant piece dominated by the odd `1.05` power (log-difference fold).
What stays open (exact blocker, filed not forced):
* first-piece log factor `log (2m+2) * 8.29 * (2m+1)^(-1.05)` has no fixed-`C`
  pure-power cap (log grows without bound vs pure power); crude `log ≤ id`
  gives divergent exponent `-0.05`. So no value for `:1109` is filed this turn.
-/

/-- R02 worst-case majorant, local rebuild of the `R02_etaWorstMajorant` shape
(`door3_R02_ball_advance.lean:1411`): `etaDerivBound` RHS with `‖s‖ → 8.29`
and `s.re → 0.05` (worst case on the R02 rect). -/
noncomputable def etaDerivMajorantR02 (m : ℕ) : ℝ :=
  Real.log (((2 * m + 2 : ℕ)) : ℝ) * 8.29 *
    ((((2 * m + 1 : ℕ)) : ℝ) ^ (-(0.05 : ℝ) - 1)) +
    (Real.log (((2 * m + 2 : ℕ)) : ℝ) -
      Real.log (((2 * m + 1 : ℕ)) : ℝ)) *
      ((((2 * m + 1 : ℕ)) : ℝ) ^ (-(0.05 : ℝ)))

/-- Nonnegativity of the local R02 majorant (mirror of `etaDerivMajorant_nonneg :582`). -/
theorem etaDerivMajorantR02_nonneg (m : ℕ) : 0 ≤ etaDerivMajorantR02 m := by
  unfold etaDerivMajorantR02
  have hApos : (0 : ℝ) < (((((2 * m + 1 : ℕ)) : ℝ))) :=
    Nat.cast_pos.mpr (by omega)
  have hB1le : (1 : ℝ) ≤ (((((2 * m + 2 : ℕ)) : ℝ))) := by
    exact_mod_cast (by omega : 1 ≤ 2 * m + 2)
  have hAB : (((((2 * m + 1 : ℕ)) : ℝ))) ≤ (((((2 * m + 2 : ℕ)) : ℝ))) := by
    exact_mod_cast (by omega : 2 * m + 1 ≤ 2 * m + 2)
  have hlogB_nn : 0 ≤ Real.log (((((2 * m + 2 : ℕ)) : ℝ))) :=
    Real.log_nonneg hB1le
  have hlog_mono : Real.log (((((2 * m + 1 : ℕ)) : ℝ))) ≤
      Real.log (((((2 * m + 2 : ℕ)) : ℝ))) :=
    Real.log_le_log hApos hAB
  have hDnn : 0 ≤ Real.log (((((2 * m + 2 : ℕ)) : ℝ))) -
      Real.log (((((2 * m + 1 : ℕ)) : ℝ))) := sub_nonneg.mpr hlog_mono
  have hr7nn : 0 ≤ (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(0.05 : ℝ) - 1)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hr5nn : 0 ≤ (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(0.05 : ℝ))) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 : 0 ≤ Real.log (((((2 * m + 2 : ℕ)) : ℝ))) * 8.29 *
      (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(0.05 : ℝ) - 1)) := by
    exact mul_nonneg (mul_nonneg hlogB_nn (by norm_num)) hr7nn
  have h2 : 0 ≤ (Real.log (((((2 * m + 2 : ℕ)) : ℝ))) -
      Real.log (((((2 * m + 1 : ℕ)) : ℝ)))) *
      (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(0.05 : ℝ))) :=
    mul_nonneg hDnn hr5nn
  exact add_nonneg h1 h2

/-- Shift-series summability `(n+1)^(-1.05)` via `Real.summable_nat_rpow_inv`
(local rebuild of `zeta_rigorous.R02_D3_shift105_summable :34827`). -/
theorem etaR02Int_shift105_summable :
    Summable (fun n : ℕ => ((((n + 1 : ℕ)) : ℝ)) ^ (-1.05 : ℝ)) := by
  have hp1 : (1 : ℝ) < (0.05 : ℝ) + 1 := by norm_num
  have hbase : Summable (fun n : ℕ => ((((n : ℝ)) ^ ((0.05 : ℝ) + 1)))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hp1
  have hshift :
      Summable (fun m : ℕ => ((((m + 1 : ℕ) : ℝ) ^ ((0.05 : ℝ) + 1)))⁻¹) :=
    (summable_nat_add_iff 1).mpr hbase
  have heq : (fun n : ℕ => ((((n + 1 : ℕ)) : ℝ)) ^ (-1.05 : ℝ)) =
      (fun m : ℕ => ((((m + 1 : ℕ) : ℝ) ^ ((0.05 : ℝ) + 1)))⁻¹) := by
    funext m
    have eR : (-1.05 : ℝ) = -((0.05 : ℝ) + 1) := by norm_num
    rw [eR, Real.rpow_neg (Nat.cast_nonneg _)]
  rw [heq]
  exact hshift

/-- Odd-vs-shift pointwise `(2n+1)^(-1.05) ≤ (n+1)^(-1.05)`
(local rebuild of `R02_D3_odd105_le_shift :34843`). -/
theorem etaR02Int_odd105_le_shift (n : ℕ) :
    ((((2 * n + 1 : ℕ)) : ℝ)) ^ (-1.05 : ℝ) ≤
      ((((n + 1 : ℕ)) : ℝ)) ^ (-1.05 : ℝ) := by
  have hm_pos : (0 : ℝ) < ((((n + 1 : ℕ)) : ℝ)) := Nat.cast_pos.mpr (by omega)
  have hm_le : ((((n + 1 : ℕ)) : ℝ)) ≤ ((((2 * n + 1 : ℕ)) : ℝ)) :=
    Nat.cast_le.mpr (by omega)
  have hexp : (-1.05 : ℝ) ≤ 0 := by norm_num
  exact Real.rpow_le_rpow_of_nonpos hm_pos hm_le hexp

/-- Odd-series summability via norm comparison with the shift series
(local rebuild of `R02_D3_odd105_summable :34852`). -/
theorem etaR02Int_odd105_summable :
    Summable (fun n : ℕ => ((((2 * n + 1 : ℕ)) : ℝ)) ^ (-1.05 : ℝ)) := by
  apply Summable.of_norm_bounded etaR02Int_shift105_summable
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact etaR02Int_odd105_le_shift n

/-- Antitone majorant `x^(-1.05)` on `Ici 1`
(local rebuild of `R02_D3_rpow105_antitone :34867`). -/
theorem etaR02Int_rpow105_antitone :
    AntitoneOn (fun x : ℝ => x ^ (-1.05 : ℝ)) (Set.Ici ((((1 : ℕ)) : ℝ))) := by
  apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num : (-1.05 : ℝ) ≤ 0)).mono
  intro x hx
  simp only [Set.mem_Ici, Set.mem_Ioi] at hx ⊢
  have h1 : (0 : ℝ) < ((((1 : ℕ)) : ℝ)) := by norm_num
  linarith

/-- Integrability of `x^(-1.05)` on `Ioi 1`
(local rebuild of `R02_D3_rpow105_integrable :34876`). -/
theorem etaR02Int_rpow105_integrable :
    MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-1.05 : ℝ))
      (Set.Ioi ((((1 : ℕ)) : ℝ))) := by
  apply integrableOn_Ioi_rpow_of_lt (by norm_num : (-1.05 : ℝ) < -1)
  norm_num

/-- `M = 1` integral-tail comparison for the shifted tail
(local rebuild of `R02_D3_tail2_le_integral105 :34882`). -/
theorem etaR02Int_tail2_le_integral105 :
    (∑' n : ℕ, ((((n + 1 + 1 : ℕ)) : ℝ)) ^ (-1.05 : ℝ)) ≤
      (∫ x : ℝ in Set.Ioi ((((1 : ℕ)) : ℝ)), x ^ (-1.05 : ℝ)) := by
  exact AntitoneOn.tsum_comp_add_le_integral 1 etaR02Int_rpow105_antitone
    etaR02Int_rpow105_integrable (fun t ht => Real.rpow_nonneg
      (le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg _) (Set.mem_Ioi.mp ht))) _)

/-- Closed-form integral `∫ x in Ioi 1, x^(-1.05) = 1 / 0.05`
(local rebuild of `R02_D3_integral105_eq :34901`). -/
theorem etaR02Int_integral105_eq :
    (∫ x : ℝ in Set.Ioi ((((1 : ℕ)) : ℝ)), x ^ (-1.05 : ℝ)) = 1 / 0.05 := by
  have hlt : (-1.05 : ℝ) < -1 := by norm_num
  have hc : (0 : ℝ) < ((((1 : ℕ)) : ℝ)) := by norm_num
  have h := integral_Ioi_rpow_of_lt hlt hc
  have e1 : (-1.05 : ℝ) + 1 = -0.05 := by norm_num
  rw [e1] at h
  have ec : ((((1 : ℕ)) : ℝ)) ^ (-0.05 : ℝ) = (1 : ℝ) := by
    have ecast : ((((1 : ℕ)) : ℝ)) = (1 : ℝ) := by norm_num
    rw [ecast, Real.one_rpow]
  rw [ec] at h
  have e2 : (-(1 : ℝ)) / (-0.05 : ℝ) = 1 / 0.05 := by norm_num
  exact e2 ▸ h

/-- Shift-tail numeral `∑' n, (n+2)^(-1.05) ≤ 20`
(local rebuild of `R02_D3_tail2_le_20 :34916`). -/
theorem etaR02Int_tail2_le_20 :
    (∑' n : ℕ, ((((n + 1 + 1 : ℕ)) : ℝ)) ^ (-1.05 : ℝ)) ≤ 20 := by
  have htail := etaR02Int_tail2_le_integral105
  have hval := etaR02Int_integral105_eq
  have h20 : (1 : ℝ) / 0.05 ≤ 20 := by norm_num
  calc (∑' n : ℕ, ((((n + 1 + 1 : ℕ)) : ℝ)) ^ (-1.05 : ℝ))
      ≤ (∫ x : ℝ in Set.Ioi ((((1 : ℕ)) : ℝ)), x ^ (-1.05 : ℝ)) := htail
    _ = 1 / 0.05 := hval
    _ ≤ 20 := h20

/-- Odd head `((2*0+1):ℝ)^(-1.05) = 1`
(local rebuild of `R02_D3_odd105_zero_eq_one :34927`). -/
theorem etaR02Int_odd105_zero_eq_one :
    ((((2 * 0 + 1 : ℕ)) : ℝ)) ^ (-1.05 : ℝ) = 1 := by
  have e : ((((2 * 0 + 1 : ℕ)) : ℝ)) = (1 : ℝ) := by norm_num
  rw [e, Real.one_rpow]

/-- K0 cap `∑' n, (2n+1)^(-1.05) ≤ 21` (head `1` + tail `≤ 20`)
(local rebuild of `R02_D3_odd105_tsum_le_21 :34933`). -/
theorem etaR02Int_odd105_tsum_le_21 :
    (∑' n : ℕ, ((((2 * n + 1 : ℕ)) : ℝ)) ^ (-1.05 : ℝ)) ≤ 21 := by
  have hOddShift :
      Summable (fun n : ℕ => ((((2 * (n + 1) + 1 : ℕ)) : ℝ)) ^ (-1.05 : ℝ)) :=
    (summable_nat_add_iff 1).mpr etaR02Int_odd105_summable
  have hShiftShift :
      Summable (fun n : ℕ => ((((n + 1 + 1 : ℕ)) : ℝ)) ^ (-1.05 : ℝ)) :=
    (summable_nat_add_iff 1).mpr etaR02Int_shift105_summable
  have hle : ∀ n : ℕ, ((((2 * (n + 1) + 1 : ℕ)) : ℝ)) ^ (-1.05 : ℝ) ≤
      ((((n + 1 + 1 : ℕ)) : ℝ)) ^ (-1.05 : ℝ) := by
    intro n
    exact etaR02Int_odd105_le_shift (n + 1)
  have htail_mono := hOddShift.tsum_le_tsum hle hShiftShift
  have htail20 := etaR02Int_tail2_le_20
  have hsplit := etaR02Int_odd105_summable.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one, etaR02Int_odd105_zero_eq_one] at hsplit
  linarith

/-- Second R02 majorant piece dominated by the odd `1.05` power.
Uses banked `eta_logDiff_le :547` plus an `Real.rpow_add` fold
`x⁻¹ * x^(-0.05) = x^(-1.05)` (mirror of the `:657-663` fold shape). -/
theorem etaDerivMajorantR02_second_le_odd105 (m : ℕ) :
    (Real.log (((2 * m + 2 : ℕ)) : ℝ) -
      Real.log (((2 * m + 1 : ℕ)) : ℝ)) *
      ((((2 * m + 1 : ℕ)) : ℝ) ^ (-(0.05 : ℝ))) ≤
      ((((2 * m + 1 : ℕ)) : ℝ)) ^ (-1.05 : ℝ) := by
  have hApos : (0 : ℝ) < (((((2 * m + 1 : ℕ)) : ℝ))) :=
    Nat.cast_pos.mpr (by omega)
  have hlogD := eta_logDiff_le m
  have hrpow_nn : 0 ≤ (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(0.05 : ℝ))) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hstep : (Real.log (((((2 * m + 2 : ℕ)) : ℝ))) -
      Real.log (((((2 * m + 1 : ℕ)) : ℝ)))) *
      (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(0.05 : ℝ))) ≤
      (((((2 * m + 1 : ℕ)) : ℝ)))⁻¹ *
      (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(0.05 : ℝ))) :=
    mul_le_mul_of_nonneg_right hlogD hrpow_nn
  have hneg1 : (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-1 : ℝ)) =
      (((((2 * m + 1 : ℕ)) : ℝ)))⁻¹ := by
    have h := Real.rpow_neg (le_of_lt hApos) (1 : ℝ)
    rw [Real.rpow_one] at h
    exact h
  have hadd : (-1 : ℝ) + (-(0.05 : ℝ)) = (-1.05 : ℝ) := by norm_num
  have hfold : (((((2 * m + 1 : ℕ)) : ℝ)))⁻¹ *
      (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(0.05 : ℝ))) =
      (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-1.05 : ℝ)) := by
    calc (((((2 * m + 1 : ℕ)) : ℝ)))⁻¹ *
        (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(0.05 : ℝ)))
        = (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-1 : ℝ)) *
          (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-(0.05 : ℝ))) := by
          rw [hneg1]
      _ = (((((2 * m + 1 : ℕ)) : ℝ)) ^ ((-1 : ℝ) + (-(0.05 : ℝ)))) := by
          rw [← Real.rpow_add hApos]
      _ = (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-1.05 : ℝ)) := by
          rw [hadd]
  rw [hfold] at hstep
  exact hstep

/-- Exact pointwise blocker for the integral route (filed, not forced):
a fixed `C` dominating the full R02 majorant by the odd `1.05` power.
The second piece is already controlled by
`etaDerivMajorantR02_second_le_odd105`; the first piece
`log (2m+2) * 8.29 * (2m+1)^(-1.05)` carries the unbounded log factor,
so no fixed `C` is supplied this turn (same obstruction as ball-side
`R02_etaWorst_pointwise105_missing`, here against the integral `≤ 21` base). -/
def etaR02Int_pointwise_missing (C : ℝ) : Prop :=
  ∀ m : ℕ, etaDerivMajorantR02 m ≤
    C * (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-1.05 : ℝ))

/-- Exact residual for the integral-comparison R02 dominator: existence of a
fixed `C ≥ 0` with the pointwise bound. Integral summability/value
(`etaR02Int_odd105_summable`, `etaR02Int_odd105_tsum_le_21`) are banked, so this
pointwise `C` is the only gap to a `Summable etaDerivMajorantR02` dominator
and hence to the `:1109` residual `etaR02_hConvLe_residual_spec`. No tsum
numeral for `etaDerivMajorantR02` and no value for `:1109` are filed here. -/
def etaR02Int_dom_residual_spec : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ etaR02Int_pointwise_missing C
