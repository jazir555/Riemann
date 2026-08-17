import Mathlib

open Set Filter Topology Real MeasureTheory
open scoped Interval Topology

noncomputable section

namespace ZetaAsymptotics

/-- The exponential power series: `exp u = ∑ (u^k / k!)`. -/
lemma exp_hasSum_div_factorial (u : ℝ) :
    HasSum (fun k : ℕ => u ^ k / (Nat.factorial k : ℝ)) (Real.exp u) := by
  have h := NormedSpace.expSeries_div_hasSum_exp_of_mem_ball (𝕂 := ℝ) (𝔸 := ℝ) u
    ((NormedSpace.expSeries_radius_eq_top ℝ ℝ).symm ▸ by simp :
      u ∈ Metric.eball (0 : ℝ) (NormedSpace.expSeries ℝ ℝ).radius)
  simpa [Real.exp_eq_exp_ℝ] using h

/-- Coefficients of the power series of `term (n+1)` at `s₀`. -/
noncomputable def termFPScoeff (n : ℕ) (s₀ : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k / (Nat.factorial k : ℝ) * ∫ x : ℝ in (n + 1 : ℝ)..(n + 2), (x - (n + 1 : ℝ)) *
    (Real.log x) ^ k * x ^ (-(s₀ + 1))

/-- The formal power series of `term (n+1)` at `s₀`. -/
noncomputable def termFPS (n : ℕ) (s₀ : ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  fun k => (termFPScoeff n s₀ k) • (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℝ)

/-- The `k`-th coefficient of `termFPS n s₀` equals `termFPScoeff n s₀ k`. -/
lemma termFPS_coeff (n : ℕ) (s₀ : ℝ) (k : ℕ) :
    (termFPS n s₀).coeff k = termFPScoeff n s₀ k := by
  simp [termFPS, FormalMultilinearSeries.coeff, ContinuousMultilinearMap.mkPiAlgebra_apply,
    Finset.prod_const_one, smul_eq_mul, mul_one]

/-- `x ^ (-y) = 1 / x ^ y` for `0 ≤ x`. -/
lemma rpow_neg_eq_one_div' {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ (-y) = 1 / x ^ y := by
  rw [rpow_neg hx, one_div]

/-- `term (n+1)` has a power series expansion at every `s₀ > 0`. -/
lemma hasFPowerSeriesAt_term_succ (n : ℕ) {s₀ : ℝ} (hs₀ : 0 < s₀) :
    HasFPowerSeriesAt (fun s : ℝ => term (n + 1) s) (termFPS n s₀) s₀ := by
  let ρ : ℝ := s₀ / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  let c : ℝ := (n + 1 : ℝ)
  have hc : (1 : ℝ) ≤ c := by dsimp [c]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hc_le : c ≤ c + 1 := by linarith
  have hxpos_of : ∀ x ∈ Icc c (c + 1), 0 < x := by
    intro x hx
    exact lt_of_lt_of_le (by dsimp [c]; linarith) hx.1
  have hmain : ∀ {y : ℝ}, |y| < ρ →
      HasSum (fun k : ℕ => termFPScoeff n s₀ k * y ^ k) (term (n + 1) (s₀ + y)) := by
    intro y hy
    let F : ℕ → ℝ → ℝ := fun k x => (x - c) * x ^ (-(s₀ + 1)) * (-1 : ℝ) ^ k *
      (Real.log x) ^ k / (Nat.factorial k : ℝ) * y ^ k
    let f : ℝ → ℝ := fun x => (x - c) / x ^ (s₀ + y + 1)
    have hF_meas : ∀ k, AEStronglyMeasurable (F k) (volume.restrict (uIoc c (c + 1))) := by
      intro k
      have hrpow : ContinuousOn (fun x : ℝ => x ^ (-(s₀ + 1))) (Icc c (c + 1)) := by
        refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
        exact continuousAt_id.rpow_const (Or.inl (ne_of_gt (hxpos_of x hx)))
      have hlog : ContinuousOn (fun x : ℝ => Real.log x) (Icc c (c + 1)) := by
        refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
        exact Real.continuousAt_log (ne_of_gt (hxpos_of x hx))
      have hlin : ContinuousOn (fun x : ℝ => x - c) (Icc c (c + 1)) := by fun_prop
      have hconst : ContinuousOn (fun _ : ℝ => (-1 : ℝ) ^ k) (Icc c (c + 1)) := continuousOn_const
      have hyc : ContinuousOn (fun _ : ℝ => y ^ k) (Icc c (c + 1)) := continuousOn_const
      have hnum : ContinuousOn (fun x : ℝ => (x - c) * x ^ (-(s₀ + 1)) * (-1 : ℝ) ^ k *
          (Real.log x) ^ k) (Icc c (c + 1)) :=
        ((hlin.mul hrpow).mul hconst).mul (hlog.pow k)
      have hdiv : ContinuousOn (fun x : ℝ => (x - c) * x ^ (-(s₀ + 1)) * (-1 : ℝ) ^ k *
          (Real.log x) ^ k / (Nat.factorial k : ℝ)) (Icc c (c + 1)) :=
        hnum.div continuousOn_const (fun x hx => (by positivity : (Nat.factorial k : ℝ) ≠ 0))
      have hcont : ContinuousOn (F k) (Icc c (c + 1)) := by
        exact hdiv.mul hyc
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
      exact hcont.mono (by
        have hsub : Ι c (c + 1) ⊆ Icc c (c + 1) := by
          simpa [uIoc_of_le hc_le, uIcc_of_le hc_le] using
            (uIoc_subset_uIcc : Ι c (c + 1) ⊆ [[c, c + 1]])
        exact hsub)
    have h_bound : ∀ k, ∀ᵐ x ∂volume, x ∈ uIoc c (c + 1) → ‖F k x‖ ≤
        (x - c) * x ^ (-(s₀ + 1)) * (ρ * Real.log x) ^ k / (Nat.factorial k : ℝ) := by
      intro k
      refine ae_of_all _ (fun x hx => ?_)
      have hx' : x ∈ Ioc c (c + 1) := by
        simpa [uIoc_of_le hc_le] using hx
      have hx_ge : c ≤ x := le_of_lt hx'.1
      have hx_gt : 0 < x := hxpos_of x ⟨hx_ge, hx'.2⟩
      have hx_ge1 : 1 ≤ x := le_trans hc hx_ge
      have hlog : 0 ≤ Real.log x := Real.log_nonneg hx_ge1
      have hx_c : 0 ≤ x - c := sub_nonneg.mpr hx_ge
      calc
        ‖F k x‖ = (x - c) * x ^ (-(s₀ + 1)) * (|y| * Real.log x) ^ k /
            (Nat.factorial k : ℝ) := by
          dsimp [F]
          rw [div_eq_mul_inv]
          simp_rw [abs_mul]
          rw [abs_of_nonneg hx_c,
              abs_of_nonneg (by positivity : 0 ≤ x ^ (-(s₀ + 1))),
              abs_pow, abs_neg, abs_one, one_pow,
              abs_pow, abs_of_nonneg hlog,
              abs_of_nonneg (by positivity : 0 ≤ (Nat.factorial k : ℝ)⁻¹),
              abs_pow]
          field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)]
          ring
        _ ≤ (x - c) * x ^ (-(s₀ + 1)) * (ρ * Real.log x) ^ k / (Nat.factorial k : ℝ) := by
          gcongr
    have h_lim : ∀ᵐ x ∂volume, x ∈ uIoc c (c + 1) → HasSum (fun k => F k x) (f x) := by
      refine ae_of_all _ (fun x hx => ?_)
      have hx' : x ∈ Ioc c (c + 1) := by
        simpa [uIoc_of_le hc_le] using hx
      have hx_ge : c ≤ x := le_of_lt hx'.1
      have hx_gt : 0 < x := hxpos_of x ⟨hx_ge, hx'.2⟩
      have hpow : ∀ k : ℕ, F k x = (x - c) * x ^ (-(s₀ + 1)) * ((-y * Real.log x) ^ k /
          (Nat.factorial k : ℝ)) := by
        intro k
        dsimp [F]
        field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)]
        ring
      have hexp : HasSum (fun k : ℕ => (-y * Real.log x) ^ k / (Nat.factorial k : ℝ))
          (Real.exp (-y * Real.log x)) :=
        exp_hasSum_div_factorial (-y * Real.log x)
      have hsum' : HasSum (fun k : ℕ => ((x - c) * x ^ (-(s₀ + 1))) * ((-y * Real.log x) ^ k /
          (Nat.factorial k : ℝ))) (((x - c) * x ^ (-(s₀ + 1))) * Real.exp (-y * Real.log x)) :=
        HasSum.mul_left ((x - c) * x ^ (-(s₀ + 1))) hexp
      have hfunc : ∀ k : ℕ, F k x = ((x - c) * x ^ (-(s₀ + 1))) * ((-y * Real.log x) ^ k /
          (Nat.factorial k : ℝ)) := by
        intro k
        simpa [mul_assoc] using hpow k
      have hsumF : HasSum (fun k => F k x) (((x - c) * x ^ (-(s₀ + 1))) * Real.exp (-y * Real.log x)) :=
        hsum'.congr_fun hfunc
      have hfx : f x = ((x - c) * x ^ (-(s₀ + 1))) * Real.exp (-y * Real.log x) := by
        dsimp [f]
        rw [div_eq_mul_inv, ← rpow_neg (le_of_lt hx_gt)]
        rw [show x ^ (-(s₀ + y + 1)) = x ^ (-(s₀ + 1)) * x ^ (-y) by
          rw [← rpow_add hx_gt]
          congr 1
          ring]
        rw [show x ^ (-y) = Real.exp (-y * Real.log x) by
          rw [rpow_def_of_pos hx_gt]
          congr 1
          ring]
        ring
      exact hfx ▸ hsumF
    have bound_summable : ∀ᵐ x ∂volume, x ∈ uIoc c (c + 1) →
        Summable (fun k : ℕ => (x - c) * x ^ (-(s₀ + 1)) * (ρ * Real.log x) ^ k /
          (Nat.factorial k : ℝ)) := by
      refine ae_of_all _ (fun x hx => ?_)
      have hx' : x ∈ Ioc c (c + 1) := by
        simpa [uIoc_of_le hc_le] using hx
      have hx_ge : c ≤ x := le_of_lt hx'.1
      have hx_ge1 : 1 ≤ x := le_trans hc hx_ge
      simpa [mul_div_assoc] using Summable.mul_left ((x - c) * x ^ (-(s₀ + 1)))
        (exp_hasSum_div_factorial (ρ * Real.log x)).summable
    have bound_integrable :
        IntervalIntegrable (fun x : ℝ => ∑' k : ℕ,
          (x - c) * x ^ (-(s₀ + 1)) * (ρ * Real.log x) ^ k / (Nat.factorial k : ℝ)) volume c (c + 1) := by
      have hcont : ContinuousOn (fun x : ℝ => ∑' k : ℕ,
          (x - c) * x ^ (-(s₀ + 1)) * (ρ * Real.log x) ^ k / (Nat.factorial k : ℝ)) (uIcc c (c + 1)) := by
        have h_sum_exp : (fun x : ℝ => ∑' k : ℕ, (x - c) * x ^ (-(s₀ + 1)) * (ρ * Real.log x) ^ k /
            (Nat.factorial k : ℝ)) = fun x => (x - c) * x ^ (-(s₀ + 1)) * Real.exp (ρ * Real.log x) := by
          funext x
          have h_eq : (fun k : ℕ => (x - c) * x ^ (-(s₀ + 1)) * (ρ * Real.log x) ^ k /
                (Nat.factorial k : ℝ)) = fun k : ℕ => (x - c) * x ^ (-(s₀ + 1)) *
                ((ρ * Real.log x) ^ k / (Nat.factorial k : ℝ)) := by
            funext k; ring
          rw [h_eq, tsum_mul_left, ← (exp_hasSum_div_factorial (ρ * Real.log x)).tsum_eq]
        rw [h_sum_exp]
        have hxp : ContinuousOn (fun x : ℝ => x ^ (-(s₀ + 1))) (uIcc c (c + 1)) := by
          rw [uIcc_of_le hc_le]
          refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
          exact continuousAt_id.rpow_const (Or.inl (ne_of_gt (hxpos_of x hx)))
        have hlog : ContinuousOn (fun x : ℝ => Real.log x) (uIcc c (c + 1)) := by
          rw [uIcc_of_le hc_le]
          refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
          exact Real.continuousAt_log (ne_of_gt (hxpos_of x hx))
        have hlin : ContinuousOn (fun x : ℝ => x - c) (uIcc c (c + 1)) := by fun_prop
        have hloglin : ContinuousOn (fun x : ℝ => ρ * Real.log x) (uIcc c (c + 1)) :=
          continuousOn_const.mul hlog
        have hlogexp : ContinuousOn (fun x : ℝ => Real.exp (ρ * Real.log x)) (uIcc c (c + 1)) :=
          Real.continuous_exp.comp_continuousOn hloglin
        exact ((hlin.mul hxp).mul hlogexp)
      exact (ContinuousOn.intervalIntegrable hcont)
    have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
      (a := c) (b := c + 1) (F := F) (f := f)
      (bound := fun k x => (x - c) * x ^ (-(s₀ + 1)) * (ρ * Real.log x) ^ k /
        (Nat.factorial k : ℝ))
      hF_meas h_bound bound_summable bound_integrable h_lim
    have hterm : (∫ x in c..(c + 1), f x) = term (n + 1) (s₀ + y) := by
      dsimp [f, c]
      rw [term, Nat.cast_succ]
    have hcoeff : ∀ k, (∫ x in c..(c + 1), F k x) = termFPScoeff n s₀ k * y ^ k := by
      intro k
      dsimp [F, c]
      rw [show termFPScoeff n s₀ k =
            (-1) ^ k / ↑k.factorial * ∫ x in (↑n + 1)..(↑n + 1 + 1),
              (x - (↑n + 1)) * log x ^ k * x ^ (-(s₀ + 1)) by
          simp only [termFPScoeff]; norm_cast]
      simp_rw [show ∀ (x : ℝ), (x - (↑n + 1)) * x ^ (-(s₀ + 1)) * (-1) ^ k * log x ^ k / ↑k.factorial * y ^ k =
            (y ^ k * ((-1) ^ k / ↑k.factorial)) * ((x - (↑n + 1)) * log x ^ k * x ^ (-(s₀ + 1))) by
          intro x; ring,
        intervalIntegral.integral_const_mul]
      ring
    rw [← hterm]
    exact hsum.congr_fun (fun k => (hcoeff k).symm)
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds 0 hρ] with z hz
  have hz_abs : |z| < ρ := by
    simpa [Metric.mem_ball, Real.dist_eq] using hz
  simpa [termFPS, termFPS_coeff, FormalMultilinearSeries.apply_eq_pow_smul_coeff, mul_comm,
    mul_left_comm, mul_assoc, smul_eq_mul] using hmain (y := z) hz_abs

/-- `term (n+1)` is real-analytic on `(0, ∞)`. -/
lemma analyticOnNhd_term_succ (n : ℕ) :
    AnalyticOnNhd ℝ (fun s : ℝ => term (n + 1) s) (Ioi 0) := by
  intro s₀ hs₀
  exact (hasFPowerSeriesAt_term_succ n hs₀).analyticAt

end ZetaAsymptotics

end
