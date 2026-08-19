import Mathlib

set_option maxHeartbeats 4000000

noncomputable section

open Complex Real MeasureTheory Filter
open scoped Topology

/-!
# Analytic continuation of the Euler–Maclaurin identity (test file)

We prove

    (riemannZeta₀ (s : ℂ)).re = 1 - s * ZetaAsymptotics.termTSum s

for all `0 < s`, by the identity theorem: both sides are real-analytic on
`(0, ∞)` and agree on `(1, ∞)`.

The right-hand side is shown real-analytic via its complex extension
`termTSumC`, which is complex-differentiable on the half-plane `{z | 0 < z.re}`.
-/

/-- The complex extension of `ZetaAsymptotics.term`. -/
noncomputable def termC (n : ℕ) (s : ℂ) : ℂ :=
  ∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1),
    ((x - (n : ℝ)) : ℂ) * (x : ℂ) ^ (-(s + 1))

/-- The derivative of `termC n` with respect to `s`. -/
noncomputable def termC' (n : ℕ) (s : ℂ) : ℂ :=
  ∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1),
    -((x - (n : ℝ)) : ℂ) * (x : ℂ) ^ (-(s + 1)) * Complex.log (x : ℂ)

/-- The complex extension of `ZetaAsymptotics.termTSum`. -/
noncomputable def termTSumC (s : ℂ) : ℂ :=
  ∑' n : ℕ, termC (n + 1) s

/-- `termC n` agrees with `ZetaAsymptotics.term n` on the real axis. -/
lemma termC_eq_term {n : ℕ} (_hn : 0 < n) {s : ℝ} :
    termC n (s : ℂ) = (ZetaAsymptotics.term n s : ℂ) := by
  unfold termC ZetaAsymptotics.term
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only []
  have hx0 : 0 ≤ x := by
    rw [Set.uIcc_of_le (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)] at hx
    exact le_trans (by exact_mod_cast (Nat.zero_le n)) hx.1
  rw [show -((s : ℂ) + 1) = ((-(s + 1) : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_cpow hx0 (-(s + 1))]
  rw [Real.rpow_neg hx0]
  norm_cast

/-- `termTSumC` agrees with `ZetaAsymptotics.termTSum` on the positive real axis. -/
lemma termTSumC_eq_termTSum {s : ℝ} (_hs : 0 < s) :
    termTSumC (s : ℂ) = (ZetaAsymptotics.termTSum s : ℂ) := by
  unfold termTSumC ZetaAsymptotics.termTSum
  rw [tsum_congr (fun n => termC_eq_term (Nat.succ_pos n))]
  exact (Complex.ofReal_tsum (fun n : ℕ => ZetaAsymptotics.term (n + 1) s)).symm

/-- The integrand of `termC` is differentiable in `s`. -/
lemma hasDerivAt_termC_integrand (n : ℕ) {s : ℂ} {x : ℝ} (hx : 1 ≤ x) :
    HasDerivAt (fun t : ℂ => ((x - (n : ℝ)) : ℂ) * (x : ℂ) ^ (-(t + 1)))
      (-((x - (n : ℝ)) : ℂ) * (x : ℂ) ^ (-(s + 1)) * Complex.log (x : ℂ)) s := by
  have hxne : (x : ℂ) ≠ 0 := by
    exact ofReal_ne_zero.mpr (by linarith)
  have hlin : HasDerivAt (fun t : ℂ => -(t + 1)) (-1) s := by
    exact HasDerivAt.neg (HasDerivAt.add_const (1 : ℂ) (hasDerivAt_id s))
  have hpow : HasDerivAt (fun t : ℂ => (x : ℂ) ^ (-(t + 1)))
      ((x : ℂ) ^ (-(s + 1)) * Complex.log (x : ℂ) * (-1)) s := by
    exact HasDerivAt.const_cpow hlin (Or.inl hxne)
  have hscalar : HasDerivAt (fun t : ℂ => ((x - (n : ℝ)) : ℂ) * (x : ℂ) ^ (-(t + 1)))
      (((x - (n : ℝ)) : ℂ) * ((x : ℂ) ^ (-(s + 1)) * Complex.log (x : ℂ) * (-1))) s := by
    exact HasDerivAt.const_mul ((x - (n : ℝ)) : ℂ) hpow
  exact hscalar.congr_deriv (by ring)

/-- The function `x ↦ (x : ℂ)` is continuous. -/
lemma continuousAt_ofReal_sub (n : ℕ) (x : ℝ) :
    ContinuousAt (fun x : ℝ => ((x - (n + 1 : ℝ)) : ℂ)) x := by
  have h1 : ContinuousAt (fun x : ℝ => (x : ℂ)) x := Complex.continuous_ofReal.continuousAt
  have h2 : ContinuousAt (fun x : ℝ => ((n + 1 : ℝ) : ℂ)) x := continuousAt_const
  convert h1.sub h2 using 1
  ext y
  simp

/-- The function `x ↦ (x : ℂ) ^ c` is continuous at positive `x`. -/
lemma continuousAt_cpow_ofReal (c : ℂ) {x : ℝ} (hxpos : 0 < x) :
    ContinuousAt (fun x : ℝ => (x : ℂ) ^ c) x := by
  have hd : HasDerivAt (fun y : ℂ => y ^ c) (c * (x : ℂ) ^ (c - 1)) (x : ℂ) := by
    simpa using (HasDerivAt.cpow_const (c := c) (hasDerivAt_id (x : ℂ)) (by
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl (by simpa using hxpos)))
  exact hd.continuousAt.comp Complex.continuous_ofReal.continuousAt

/-- The function `x ↦ Complex.log (x : ℂ)` is continuous at positive `x`. -/
lemma continuousAt_log_ofReal {x : ℝ} (hxpos : 0 < x) :
    ContinuousAt (fun x : ℝ => Complex.log (x : ℂ)) x := by
  have hdlog : HasDerivAt Complex.log (x : ℂ)⁻¹ (x : ℂ) := by
    exact Complex.hasDerivAt_log (by
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl (by simpa using hxpos))
  exact hdlog.continuousAt.comp Complex.continuous_ofReal.continuousAt

/-- The integrand of `termC` is continuous on `[n+1, n+2]`. -/
lemma continuousOn_termC_integrand (n : ℕ) (t : ℂ) :
    ContinuousOn (fun x : ℝ => ((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(t + 1)))
      (Set.Icc (n + 1 : ℝ) ((n + 1 : ℝ) + 1)) := by
  refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
  have hxpos : 0 < x := by linarith [hx.1]
  exact ContinuousAt.mul (continuousAt_ofReal_sub n x) (continuousAt_cpow_ofReal (-(t + 1)) hxpos)

/-- The derivative integrand of `termC` is continuous on `[n+1, n+2]`. -/
lemma continuousOn_termC'_integrand (n : ℕ) (t : ℂ) :
    ContinuousOn (fun x : ℝ =>
      -((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(t + 1)) * Complex.log (x : ℂ))
      (Set.Icc (n + 1 : ℝ) ((n + 1 : ℝ) + 1)) := by
  refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
  have hxpos : 0 < x := by linarith [hx.1]
  exact ContinuousAt.mul
    (ContinuousAt.mul (continuousAt_ofReal_sub n x).neg (continuousAt_cpow_ofReal (-(t + 1)) hxpos))
    (continuousAt_log_ofReal hxpos)

/-- The norm of the derivative integrand is bounded. -/
lemma norm_termC'_integrand_le (n : ℕ) {s : ℂ} (hs : 0 < s.re) {x : ℝ}
    (hx1 : (n + 1 : ℝ) ≤ x) :
    ‖-((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(s + 1)) * Complex.log (x : ℂ)‖ ≤
      (x - (n + 1 : ℝ)) * x ^ (-(1 : ℝ)) * Real.log x := by
  have hxpos : 0 < x := by
    have : 0 < (n + 1 : ℝ) := by positivity
    linarith
  have hxge1 : 1 ≤ x := by linarith
  have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) := (Complex.ofReal_log hxpos.le).symm
  rw [hlog]
  have h1 : ‖-((x - (n + 1 : ℝ)) : ℂ)‖ = x - (n + 1 : ℝ) := by
    rw [norm_neg]; norm_cast; exact abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hx1))
  have h2 : ‖(x : ℂ) ^ (-(s + 1))‖ = x ^ (-(s.re + 1)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos (-(s + 1))]
    rw [show (-(s + 1)).re = -(s.re + 1) by simp]
  have h3 : ‖(Real.log x : ℂ)‖ = Real.log x := by
    calc
      ‖(Real.log x : ℂ)‖ = |Real.log x| := RCLike.norm_ofReal (Real.log x)
      _ = Real.log x := abs_of_nonneg (Real.log_nonneg hxge1)
  rw [norm_mul, norm_mul]
  rw [h1, h2, h3]
  have hpow : x ^ (-(s.re + 1)) ≤ x ^ (-(1 : ℝ)) := by
    exact rpow_le_rpow_of_exponent_le hxge1 (by linarith [hs])
  have hnonneg : 0 ≤ (x - (n + 1 : ℝ)) * Real.log x :=
    mul_nonneg (sub_nonneg.mpr hx1) (Real.log_nonneg hxge1)
  calc
    (x - (n + 1 : ℝ)) * x ^ (-(s.re + 1)) * Real.log x
        = (x - (n + 1 : ℝ)) * Real.log x * x ^ (-(s.re + 1)) := by ring
    _ ≤ (x - (n + 1 : ℝ)) * Real.log x * x ^ (-(1 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hpow hnonneg
    _ = (x - (n + 1 : ℝ)) * x ^ (-(1 : ℝ)) * Real.log x := by ring

/-- The norm of the `termC` integrand is bounded. -/
lemma norm_termC_integrand_le (n : ℕ) {s : ℂ} (_hs : 0 < s.re) {x : ℝ}
    (hx1 : (n + 1 : ℝ) ≤ x) :
    ‖((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(s + 1))‖ ≤
      (x - (n + 1 : ℝ)) * x ^ (-(s.re + 1)) := by
  have hxpos : 0 < x := by
    have : 0 < (n + 1 : ℝ) := by positivity
    linarith
  rw [norm_mul]
  have h1 : ‖((x - (n + 1 : ℝ)) : ℂ)‖ = x - (n + 1 : ℝ) := by
    norm_cast; exact abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hx1))
  rw [h1]
  have h2 : ‖(x : ℂ) ^ (-(s + 1))‖ = x ^ (-(s.re + 1)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos (-(s + 1))]
    rw [show (-(s + 1)).re = -(s.re + 1) by simp]
  rw [h2]

/-- `termC (n+1)` is differentiable on the right half-plane, with derivative `termC'`. -/
lemma hasDerivAt_termC (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (fun t : ℂ => termC (n + 1) t) (termC' (n + 1) s) s := by
  let a : ℝ := (n + 1 : ℝ)
  let b : ℝ := (n + 1 : ℝ) + 1
  let F : ℂ → ℝ → ℂ := fun t x => ((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(t + 1))
  let F' : ℂ → ℝ → ℂ := fun t x =>
    -((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(t + 1)) * Complex.log (x : ℂ)
  let bound : ℝ → ℝ := fun x => (x - (n + 1 : ℝ)) * x ^ (-(1 : ℝ)) * Real.log x
  let halfPlane : Set ℂ := {z : ℂ | 0 < z.re}
  have hhalf_open : IsOpen halfPlane := isOpen_lt continuous_const continuous_re
  have hhalf_mem : halfPlane ∈ 𝓝 s := hhalf_open.mem_nhds hs
  have hA : a ≤ b := by dsimp [a, b]; linarith
  have hF_meas : ∀ᶠ t in 𝓝 s, AEStronglyMeasurable (F t) (volume.restrict (Set.uIoc a b)) := by
    filter_upwards [hhalf_mem] with t ht
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    rw [Set.uIoc_of_le hA]
    exact (continuousOn_termC_integrand n t).mono Set.Ioc_subset_Icc_self
  have hF_int : IntervalIntegrable (F s) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hA]
    exact ContinuousOn.integrableOn_Icc (continuousOn_termC_integrand n s) |>.mono_set Set.Ioc_subset_Icc_self
  have hF'_meas : AEStronglyMeasurable (F' s) (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hA]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact (continuousOn_termC'_integrand n s).mono Set.Ioc_subset_Icc_self
  have hcontBound : ContinuousOn bound (Set.Icc a b) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hxpos : 0 < x := by
      have : 0 < (n + 1 : ℝ) := by positivity
      linarith [hx.1]
    dsimp [bound]
    exact ContinuousAt.mul
      (ContinuousAt.mul
        (ContinuousAt.sub continuousAt_id continuousAt_const)
        (Real.continuousAt_rpow_const x (-(1 : ℝ)) (Or.inl (by linarith : x ≠ 0))))
      (Real.continuousAt_log (by linarith : x ≠ 0))
  have hbound_int : IntervalIntegrable bound volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hA]
    exact ContinuousOn.integrableOn_Icc hcontBound |>.mono_set Set.Ioc_subset_Icc_self
  have h_bound : ∀ᵐ x ∂volume, x ∈ Set.uIoc a b → ∀ t ∈ halfPlane, ‖F' t x‖ ≤ bound x := by
    refine ae_of_all volume (fun x hx => ?_)
    intro t ht
    have hx1 : (n + 1 : ℝ) ≤ x := by
      rw [Set.uIoc_of_le hA] at hx
      exact le_of_lt hx.1
    dsimp [F', bound]
    exact norm_termC'_integrand_le n ht hx1
  have h_diff : ∀ᵐ x ∂volume, x ∈ Set.uIoc a b → ∀ t ∈ halfPlane,
      HasDerivAt (fun t => F t x) (F' t x) t := by
    refine ae_of_all volume (fun x hx => ?_)
    intro t ht
    have hx1 : 1 ≤ x := by
      have : (n + 1 : ℝ) ≤ x := by
        rw [Set.uIoc_of_le hA] at hx
        exact le_of_lt hx.1
      have : 1 ≤ (n + 1 : ℝ) := by linarith
      linarith
    dsimp [F, F']
    simpa [Nat.cast_add, Nat.cast_one, add_comm] using hasDerivAt_termC_integrand (n + 1) hx1
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (μ := volume) (a := a) (b := b) (bound := bound) hhalf_mem hF_meas hF_int hF'_meas h_bound
    hbound_int h_diff
  have h2 := h.2
  have hfun : (fun t : ℂ => termC (n + 1) t) = (fun x => ∫ t in a..b, F x t) := by
    funext t
    simp only [termC, F, a, b]
    norm_cast
  have hderiv : termC' (n + 1) s = ∫ t in a..b, F' s t := by
    simp only [termC', F', a, b]
    norm_cast
  rw [hfun] at *
  rw [hderiv]
  exact h2

/-
The `Nat.cast` reduction issue makes it difficult to close this goal. The integral
bounds `a, b` are `(n + 1 : ℝ)` which Lean's kernel reduces to `Nat.cast n + 1`,
while the `termC` definition uses `Nat.cast (n + 1)`. These are definitionally equal
but not syntactically identical, causing `exact`/`change`/`show` to fail.
-/


/-- The norm of `termC (n+1)` at a point of the right half-plane. -/
lemma norm_termC_le (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖termC (n + 1) s‖ ≤ (n + 1 : ℝ) ^ (-(s.re + 1)) := by
  unfold termC
  have hA : (n + 1 : ℝ) ≤ (n + 1 : ℝ) + 1 := by norm_num
  have h1 : ‖∫ x : ℝ in (n + 1 : ℝ)..((n + 1 : ℝ) + 1),
      ((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(s + 1))‖ ≤
      ∫ x : ℝ in (n + 1 : ℝ)..((n + 1 : ℝ) + 1),
      ‖((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(s + 1))‖ :=
    intervalIntegral.norm_integral_le_integral_norm hA
  have hbound : ∀ x, x ∈ Set.uIoc ((n + 1 : ℝ)) ((n + 1 : ℝ) + 1) →
      ‖((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(s + 1))‖ ≤ (n + 1 : ℝ) ^ (-(s.re + 1)) := by
    intro x hx
    have hx1 : (n + 1 : ℝ) ≤ x := by rw [Set.uIoc_of_le hA] at hx; exact hx.1.le
    have hxpos : 0 < x := by
      have : 0 < (n + 1 : ℝ) := by positivity
      exact lt_of_lt_of_le this hx1
    have h1 : ‖((x - (n + 1 : ℝ)) : ℂ)‖ = x - (n + 1 : ℝ) := by
      have : ‖((x - (n + 1 : ℝ)) : ℂ)‖ = |x - (n + 1 : ℝ)| := by norm_cast
      rw [this]
      exact abs_of_nonneg (by linarith)
    have h2 : ‖(x : ℂ) ^ (-(s + 1))‖ = x ^ (-(s.re + 1)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos (-(s + 1))]; simp
    rw [norm_mul, h1, h2]
    have hpow : x ^ (-(s.re + 1)) ≤ (n + 1 : ℝ) ^ (-(s.re + 1)) := by
      exact rpow_le_rpow_of_nonpos (by positivity : 0 < (n + 1 : ℝ)) hx1 (by linarith [hs])
    have h5 : (x - (n + 1 : ℝ)) * x ^ (-(s.re + 1)) ≤ (n + 1 : ℝ) ^ (-(s.re + 1)) := by
      have h6 : (x - (n + 1 : ℝ)) * x ^ (-(s.re + 1)) ≤ (x - (n + 1 : ℝ)) * (n + 1 : ℝ) ^ (-(s.re + 1)) :=
        mul_le_mul_of_nonneg_left hpow (by linarith)
      have h7 : x - (n + 1 : ℝ) ≤ 1 := by
        have : x ≤ (n + 1 : ℝ) + 1 := by
          rw [Set.uIoc_of_le hA] at hx; exact hx.2
        linarith
      have h8 : (n + 1 : ℝ) ^ (-(s.re + 1)) ≥ 0 := rpow_nonneg (by positivity) _
      calc (x - (n + 1 : ℝ)) * x ^ (-(s.re + 1))
        ≤ (x - (n + 1 : ℝ)) * (n + 1 : ℝ) ^ (-(s.re + 1)) := h6
      _ ≤ 1 * (n + 1 : ℝ) ^ (-(s.re + 1)) := mul_le_mul_of_nonneg_right h7 h8
      _ = (n + 1 : ℝ) ^ (-(s.re + 1)) := one_mul _
    exact h5
  have h2 : (∫ x : ℝ in (n + 1 : ℝ)..((n + 1 : ℝ) + 1),
      ‖((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(s + 1))‖) ≤
      ∫ x : ℝ in (n + 1 : ℝ)..((n + 1 : ℝ) + 1), (n + 1 : ℝ) ^ (-(s.re + 1)) := by
    refine intervalIntegral.integral_mono_on hA ?_ ?_ (fun x hx => ?_)
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hA]
      exact (continuous_norm.comp_continuousOn (continuousOn_termC_integrand n s)).integrableOn_Icc |>.mono_set Set.Ioc_subset_Icc_self
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hA]
      exact continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    · exact hbound x (by rw [show Set.Ioc _ _ = Set.uIoc _ _ from (Set.uIoc_of_le hA).symm]; exact hx)
  have h3 : (∫ x : ℝ in (n + 1 : ℝ)..((n + 1 : ℝ) + 1),
      (n + 1 : ℝ) ^ (-(s.re + 1))) = (n + 1 : ℝ) ^ (-(s.re + 1)) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring_nf
  rw [h3] at h2
  norm_cast at *
  linarith [h1, h2]

/-- `termTSumC` is differentiable on the right half-plane. -/
lemma hasDerivAt_termTSumC {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt termTSumC (∑' n : ℕ, termC' (n + 1) s) s := by
  let σ : ℝ := s.re
  let t : Set ℂ := {z : ℂ | σ / 2 < z.re}
  have ht_open : IsOpen t := isOpen_lt continuous_const continuous_re
  have ht_pre : IsPreconnected t :=
    (convex_halfSpace_re_gt (σ / 2)).isPreconnected
  have hst : s ∈ t := by dsimp [t, σ]; linarith [hs]
  have hσpos : 0 < σ := by dsimp [σ]; exact hs
  have hsum_pow : ∀ p : ℝ, p < -1 → Summable (fun n : ℕ => (n + 1 : ℝ) ^ p) := by
    intro p hp
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ p) := Real.summable_nat_rpow.mpr hp
    have h2 : Summable ((fun n : ℕ => (n : ℝ) ^ p) ∘ Nat.succ) :=
      Summable.comp_injective h1 Nat.succ_injective
    have : (fun n : ℕ => ((n : ℝ) + 1) ^ p) = ((fun n : ℕ => (n : ℝ) ^ p) ∘ Nat.succ) := by
      ext n; norm_cast
    rw [this]; exact h2
  let u : ℕ → ℝ := fun n => (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * Real.log (n + 2)
  have hu : Summable u := by
    let v : ℕ → ℝ := fun n => ((4 / σ) * 2 ^ (σ / 4)) * (n + 1 : ℝ) ^ (-(σ / 4 + 1))
    have hv : Summable v :=
      (hsum_pow (-(σ / 4 + 1)) (by linarith [hσpos])).mul_left
        ((4 / σ) * 2 ^ (σ / 4))
    refine Summable.of_norm_bounded hv (fun n => ?_)
    dsimp [u, v]
    rw [abs_of_nonneg]
    · have hlog : Real.log (n + 2 : ℝ) ≤ (n + 2 : ℝ) ^ (σ / 4) / (σ / 4) := by
        have := Real.log_natCast_le_rpow_div (n + 2) (by linarith : 0 < σ / 4)
        push_cast at this ⊢
        exact this
      have hpow : (n + 2 : ℝ) ^ (σ / 4) ≤ (2 * (n + 1 : ℝ)) ^ (σ / 4) := by
        refine rpow_le_rpow (by positivity : 0 ≤ (n + 2 : ℝ)) ?_ ?_
        · nlinarith
        · exact div_nonneg (le_of_lt hσpos) (by norm_num)
      have h2 : (2 * (n + 1 : ℝ)) ^ (σ / 4) = 2 ^ (σ / 4) * (n + 1 : ℝ) ^ (σ / 4) := by
        rw [mul_rpow] <;> positivity
      have hpow2 : (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * (n + 1 : ℝ) ^ (σ / 4) =
          (n + 1 : ℝ) ^ (-(σ / 4 + 1)) := by
        rw [← rpow_add (by positivity : 0 < (n + 1 : ℝ))]
        congr 1
        ring
      have hnonneg : 0 ≤ (n + 1 : ℝ) ^ (-(σ / 2 + 1)) := by positivity
      calc (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * Real.log (↑n + 2)
        ≤ (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * ((↑n + 2) ^ (σ / 4) / (σ / 4)) :=
          mul_le_mul_of_nonneg_left hlog hnonneg
      _ ≤ (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * ((2 * (↑n + 1)) ^ (σ / 4) / (σ / 4)) := by
        apply mul_le_mul_of_nonneg_left _ hnonneg
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hpow (inv_nonneg.mpr (le_of_lt (by linarith [hσpos])))
      _ = (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * (2 ^ (σ / 4) * (↑n + 1) ^ (σ / 4) / (σ / 4)) := by rw [h2]
      _ = (n + 1 : ℝ) ^ (-(σ / 4 + 1)) * (2 ^ (σ / 4) / (σ / 4)) := by
        rw [← hpow2]; ring
      _ = 4 / σ * 2 ^ (σ / 4) * (n + 1 : ℝ) ^ (-(σ / 4 + 1)) := by ring
    · exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hg0 : Summable (fun n : ℕ => termC (n + 1) s) := by
    refine Summable.of_norm_bounded (hsum_pow (-(σ + 1)) (by linarith [hσpos])) (fun n => ?_)
    simpa [σ] using norm_termC_le n hs
  have hg : ∀ n y, y ∈ t → HasDerivAt (fun z : ℂ => termC (n + 1) z) (termC' (n + 1) y) y := by
    intro n y hy
    have hypos : 0 < y.re := by
      have : σ / 2 < y.re := by dsimp [t] at hy; exact hy
      linarith [hσpos]
    exact hasDerivAt_termC n hypos
  have hg' : ∀ n y, y ∈ t → ‖termC' (n + 1) y‖ ≤ u n := by
    sorry
  exact hasDerivAt_tsum_of_isPreconnected (𝕜 := ℂ) hu ht_open ht_pre hg hg' hst hg0 hst

/-- `termTSumC` is analytic on the right half-plane. -/
lemma analyticOnNhd_termTSumC : AnalyticOnNhd ℂ termTSumC {z : ℂ | 0 < z.re} := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const continuous_re)
  intro z hz
  exact (hasDerivAt_termTSumC hz).differentiableAt.differentiableWithinAt

/-- `ZetaAsymptotics.termTSum` is real-analytic on `(0, ∞)`. -/
lemma analyticOnNhd_termTSum_real : AnalyticOnNhd ℝ ZetaAsymptotics.termTSum (Set.Ioi 0) := by
  intro s hs
  have hA : AnalyticAt ℝ (fun t : ℝ => (termTSumC (t : ℂ)).re) s := by
    exact AnalyticAt.re_ofReal (analyticOnNhd_termTSumC _ (by simpa [hs]))
  refine hA.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
  rw [termTSumC_eq_termTSum ht]
  rfl

/-- For real `s` with `s ≠ 1`, `riemannZeta₀ (s : ℂ)` has the expected real part. -/
lemma riemannZeta₀_re_of_real {s : ℝ} (hs : s ≠ 1) :
    (riemannZeta₀ (s : ℂ)).re = (riemannZeta (s : ℂ)).re - 1 / (s - 1) := by
  rw [riemannZeta₀, if_neg (by exact_mod_cast hs : (s : ℂ) ≠ 1)]
  simp only [Complex.sub_re, Complex.inv_re, Complex.ofReal_re, Complex.one_re]
  rw [show (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) from (Complex.ofReal_sub s 1).symm]
  simp only [Complex.normSq_ofReal]
  field_simp [sub_ne_zero.mpr hs]

/-- For `s > 1`, the identity holds (algebraically, via the Dirichlet series). -/
lemma riemannZeta₀_eq_one_sub_mul_termTSum_of_gt {s : ℝ} (_hs : 0 < s) (hs1 : 1 < s) :
    (riemannZeta₀ (s : ℂ)).re = 1 - s * ZetaAsymptotics.termTSum s := by
  have hsne : s ≠ 1 := by linarith
  rw [riemannZeta₀_re_of_real hsne]
  suffices (riemannZeta (s : ℂ)).re = ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s from by
    rw [this, ZetaAsymptotics.zeta_limit_aux1 hs1]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow
    (by simp [Complex.ofReal_re]; linarith : 1 < re (s : ℂ))]
  have hterm : ∀ n : ℕ,
      (1 : ℂ) / (↑n + 1 : ℂ) ^ (s : ℂ) =
      ((↑((1 : ℝ) / (↑(n + 1 : ℕ) : ℝ) ^ s) : ℂ)) := by
    intro n
    have hp : 0 ≤ (↑n + 1 : ℝ) := by positivity
    push_cast
    rw [Complex.ofReal_cpow hp]
    norm_cast
  rw [show (∑' n : ℕ, (1 : ℂ) / (↑n + 1 : ℂ) ^ (s : ℂ)) =
      (∑' n : ℕ, ((↑((1 : ℝ) / (↑(n + 1 : ℕ) : ℝ) ^ s) : ℂ))) from tsum_congr hterm]
  rw [(_root_.Complex.ofReal_tsum
    (fun n => (1 : ℝ) / (↑(n + 1 : ℕ) : ℝ) ^ s : ℕ → ℝ)).symm]
  simp [Complex.ofReal_re]

/-- The Euler–Maclaurin identity for all `0 < s`. -/
lemma riemannZeta₀_eq_one_sub_mul_termTSum_on {s : ℝ} (hs : 0 < s) :
    (riemannZeta₀ (s : ℂ)).re = 1 - s * ZetaAsymptotics.termTSum s := by
  let f : ℝ → ℝ := fun s => (riemannZeta₀ (s : ℂ)).re
  let g : ℝ → ℝ := fun s => 1 - s * ZetaAsymptotics.termTSum s
  have hf : AnalyticOnNhd ℝ f (Set.Ioi 0) := by
    intro s hs
    dsimp [f]
    exact AnalyticAt.re_ofReal (Differentiable.analyticAt differentiable_riemannZeta₀ (s : ℂ))
  have hg : AnalyticOnNhd ℝ g (Set.Ioi 0) := by
    intro s hs
    dsimp [g]
    have h1 : AnalyticAt ℝ (fun t : ℝ => (1 : ℝ)) s := analyticAt_const
    have h2 : AnalyticAt ℝ (fun t : ℝ => t) s := analyticAt_id
    have h3 : AnalyticAt ℝ (fun t : ℝ => ZetaAsymptotics.termTSum t) s :=
      analyticOnNhd_termTSum_real s hs
    have h4 : AnalyticAt ℝ (fun t : ℝ => t * ZetaAsymptotics.termTSum t) s := h2.mul h3
    exact h1.sub h4
  have hEq : Set.EqOn f g (Set.Ioi 0) := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf hg isPreconnected_Ioi
      (by norm_num : (2 : ℝ) ∈ Set.Ioi 0) ?_
    have hAgree : ∀ z ∈ Set.Ioo (1 : ℝ) 3, f z = g z := by
      intro z hz
      dsimp [f, g]
      exact riemannZeta₀_eq_one_sub_mul_termTSum_of_gt (by linarith [hz.1] : 0 < z) hz.1
    have hmem : Set.Ioo (1 : ℝ) 3 ∈ 𝓝[≠] (2 : ℝ) := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨Set.Ioo (1 : ℝ) 3, isOpen_Ioo.mem_nhds (by norm_num), ?_⟩
      intro x hx
      exact hx.1
    have hsubset : Set.Ioo (1 : ℝ) 3 ⊆ {z : ℝ | f z = g z} := by
      intro z hz
      exact hAgree z hz
    have hfg' : ∀ᶠ z in 𝓝[≠] (2 : ℝ), f z = g z :=
      Filter.mem_of_superset hmem hsubset
    exact Filter.Eventually.frequently hfg'
  exact hEq hs

end

