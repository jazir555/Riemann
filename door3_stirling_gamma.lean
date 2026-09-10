import Mathlib

/-! Stirling exponential decay for complex Gamma (Door 3 lane, self-contained).
Route: finite Weierstrass-product bound + factor counting (see `D3SG_sq_prod`).
-/

/-- Integral domination: `‖Γ(w)‖ ≤ Γ(Re w)` for `0 < Re w`. -/
theorem D3SG_Gamma_norm_le_real (w : ℂ) (hw : 0 < w.re) :
    ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := by
  have hC : Complex.Gamma w = Complex.GammaIntegral w :=
    Complex.Gamma_eq_integral hw
  have hR : Real.Gamma w.re
      = ∫ x : ℝ in Set.Ioi 0, Real.exp (-x) * x ^ (w.re - 1) :=
    Real.Gamma_eq_integral hw
  rw [hC, hR]
  unfold Complex.GammaIntegral
  have hpoint : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) →
      ‖((Real.exp (-x) : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (w - 1)‖
        = Real.exp (-x) * x ^ (w.re - 1) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := Set.mem_Ioi.mp hx
    have e1 : ‖((Real.exp (-x) : ℝ) : ℂ)‖ = Real.exp (-x) :=
      Complex.norm_of_nonneg (le_of_lt (Real.exp_pos (-x)))
    have e2 : ‖((x : ℝ) : ℂ) ^ (w - 1)‖ = x ^ (w.re - 1) := by
      have hcp := Complex.norm_cpow_eq_rpow_re_of_pos hx0 (w - 1)
      have ere : (w - 1).re = w.re - 1 := by simp
      rw [ere] at hcp
      exact hcp
    rw [norm_mul, e1, e2]
  have heq : (∫ x : ℝ in Set.Ioi (0 : ℝ),
        ‖((Real.exp (-x) : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (w - 1)‖) =
      ∫ x : ℝ in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ (w.re - 1) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => hpoint x hx)
  have hI : MeasurableSet (Set.Ioi (0 : ℝ)) := measurableSet_Ioi
  have hbound : ‖∫ x : ℝ in Set.Ioi (0 : ℝ),
        ((Real.exp (-x) : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (w - 1)‖ ≤
      ∫ x : ℝ in Set.Ioi (0 : ℝ),
        ‖((Real.exp (-x) : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (w - 1)‖ := by
    simp only [← MeasureTheory.integral_indicator hI]
    have hcomm : ∀ x : ℝ, ‖(Set.Ioi (0 : ℝ)).indicator
        (fun x => ((Real.exp (-x) : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (w - 1)) x‖ =
        (Set.Ioi (0 : ℝ)).indicator
        (fun x => ‖((Real.exp (-x) : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (w - 1)‖) x := by
      intro x
      by_cases hx : x ∈ Set.Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, norm_zero]
    calc ‖∫ x : ℝ, (Set.Ioi (0 : ℝ)).indicator
            (fun x => ((Real.exp (-x) : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (w - 1)) x‖
          ≤ ∫ x : ℝ, ‖(Set.Ioi (0 : ℝ)).indicator
            (fun x => ((Real.exp (-x) : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (w - 1)) x‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
      _ = ∫ x : ℝ, (Set.Ioi (0 : ℝ)).indicator
            (fun x => ‖((Real.exp (-x) : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (w - 1)‖) x :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcomm)
  exact le_trans hbound (le_of_eq heq)

open scoped BigOperators

/-- Shift norm identity: `‖Γ(z+n)‖ = ‖Γ(z)‖·∏‖z+k‖`. -/
theorem D3SG_gamma_shift_norm {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ‖Complex.Gamma (z + n)‖ =
      ‖Complex.Gamma z‖ * ∏ k ∈ Finset.range n, ‖z + (k : ℂ)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hzn : z + (n : ℂ) ≠ 0 := by
      intro h
      have hRe := congrArg Complex.re h
      simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hRe
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hzn,
      norm_mul, ih, Finset.prod_range_succ]
    ring

/-- Real shift identity: `Γ(x+n) = Γ(x)·∏(x+k)`. -/
theorem D3SG_real_gamma_shift {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.Gamma (x + n) = Real.Gamma x * ∏ k ∈ Finset.range n, (x + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : x + (n : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hxn, ih,
      Finset.prod_range_succ]
    ring

/-- Squared finite-product bound (modulus of every denominator kept). -/
theorem D3SG_sq_prod {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ‖Complex.Gamma z‖ ^ 2 ≤ Real.Gamma z.re ^ 2 *
      ∏ k ∈ Finset.range n,
        ((z.re + k) ^ 2 / ((z.re + k) ^ 2 + z.im ^ 2)) := by
  have hle : ‖Complex.Gamma z‖ ≤ Real.Gamma z.re *
      ∏ k ∈ Finset.range n, ((z.re + k) / ‖z + (k : ℂ)‖) := by
    have hpos : 0 < ∏ k ∈ Finset.range n, ‖z + (k : ℂ)‖ := by
      apply Finset.prod_pos
      intro k hk
      apply norm_pos_iff.mpr
      intro h
      have hRe := congrArg Complex.re h
      simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hRe
      have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hshift : ‖Complex.Gamma (z + (n : ℂ))‖ ≤ Real.Gamma (z + (n : ℂ)).re := by
      apply D3SG_Gamma_norm_le_real
      simp only [Complex.add_re, Complex.natCast_re]
      have hnn : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg n
      linarith
    rw [D3SG_gamma_shift_norm hz, Complex.add_re, Complex.natCast_re,
      D3SG_real_gamma_shift hz] at hshift
    rw [Finset.prod_div_distrib, ← mul_div_assoc, le_div_iff₀ hpos]
    exact hshift
  have h := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [mul_pow, ← Finset.prod_pow] at h
  have hf : ∀ k : ℕ, ((z.re + k) / ‖z + (k : ℂ)‖) ^ 2 =
      (z.re + k) ^ 2 / ((z.re + k) ^ 2 + z.im ^ 2) := by
    intro k
    rw [div_pow, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.natCast_re, Complex.add_im,
      Complex.natCast_im, add_zero, ← pow_two]
  simp_rw [hf] at h
  exact h

/-- Real cap `Γ(0.95) ≤ 4` (one shift + convexity on `[1,2]`). -/
theorem D3SG_Real_Gamma_095_le_four : Real.Gamma 0.95 ≤ 4 := by
  have hypos : (0 : ℝ) < 0.95 := by norm_num
  have hyne : (0.95 : ℝ) ≠ 0 := ne_of_gt hypos
  have hshift : Real.Gamma (0.95 + 1) = 0.95 * Real.Gamma 0.95 :=
    Real.Gamma_add_one hyne
  have hcap : Real.Gamma (0.95 + 1) ≤ 1 := by
    have ha : (0 : ℝ) ≤ 1 - 0.95 := by norm_num
    have hb : (0 : ℝ) ≤ 0.95 := by norm_num
    have hab : ((1 : ℝ) - 0.95) + 0.95 = 1 := by ring
    have h1mem : (1 : ℝ) ∈ Set.Ioi 0 := Set.mem_Ioi.mpr (by norm_num)
    have h2mem : (2 : ℝ) ∈ Set.Ioi 0 := Set.mem_Ioi.mpr (by norm_num)
    have hJ := Real.convexOn_Gamma.2 h1mem h2mem ha hb hab
    simp only [smul_eq_mul] at hJ
    have hpt : ((1 : ℝ) - 0.95) * 1 + 0.95 * 2 = 0.95 + 1 := by ring
    rw [hpt, Real.Gamma_one, Real.Gamma_two] at hJ
    have he : ((1 : ℝ) - 0.95) * 1 + 0.95 * 1 = 1 := by ring
    exact le_trans hJ (le_of_eq he)
  have hdiv : Real.Gamma 0.95 = Real.Gamma (0.95 + 1) / 0.95 := by
    rw [eq_div_iff_mul_eq hyne]
    rw [hshift]
    ring
  have h1 : Real.Gamma (0.95 + 1) / 0.95 ≤ 1 / 0.95 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hcap (inv_nonneg.mpr (le_of_lt hypos))
  have h2 : (1 : ℝ) / 0.95 ≤ 4 := by norm_num
  calc Real.Gamma 0.95 = Real.Gamma (0.95 + 1) / 0.95 := hdiv
    _ ≤ 1 / 0.95 := h1
    _ ≤ 4 := h2

/-- Each product factor lies in `[0,1]` for positive `σ`. -/
theorem D3SG_factor_mem_Icc (σ T : ℝ) (hσ : 0 < σ) (k : ℕ) :
    0 ≤ (σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2) ∧
    (σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2) ≤ 1 := by
  have hsk : (0 : ℝ) < σ + (k : ℝ) := by
    have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h2 : (0 : ℝ) < (σ + (k : ℝ)) ^ 2 := pow_pos hsk 2
  have hpos : (0 : ℝ) < (σ + (k : ℝ)) ^ 2 + T ^ 2 :=
    lt_of_lt_of_le h2 (le_add_of_nonneg_right (sq_nonneg T))
  constructor
  · exact div_nonneg (sq_nonneg _) (le_of_lt hpos)
  · rw [div_le_one hpos]
    linarith [sq_nonneg T]

/-- Factors at height below `|T|` are at most one half. -/
theorem D3SG_factor_le_half (σ T : ℝ) (hσ : 0 < σ) (k : ℕ)
    (h : σ + (k : ℝ) ≤ |T|) :
    (σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2) ≤ 1 / 2 := by
  have hsk : (0 : ℝ) ≤ σ + (k : ℝ) := by
    have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hT : (σ + (k : ℝ)) ^ 2 ≤ T ^ 2 := by
    have h1 : (σ + (k : ℝ)) ^ 2 ≤ |T| ^ 2 := pow_le_pow_left₀ hsk h 2
    rw [sq_abs] at h1
    exact h1
  have h2 : (0 : ℝ) < (σ + (k : ℝ)) ^ 2 := by
    apply pow_pos _ 2
    have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hpos : (0 : ℝ) < (σ + (k : ℝ)) ^ 2 + T ^ 2 :=
    lt_of_lt_of_le h2 (le_add_of_nonneg_right (sq_nonneg T))
  rw [div_le_iff₀ hpos]
  linarith

/-- Weakened banked log-two bound: `2/3 < log 2`. -/
theorem D3SG_log_two_gt : (2/3 : ℝ) < Real.log 2 := by
  have h69 : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h23 : (2/3 : ℝ) < 0.69 := by norm_num
  exact lt_trans h23 h69

/-- Index counting: enough half-factors below height `T`. -/
theorem D3SG_floor_count (T : ℝ) :
    Nat.floor (T - 0.95) + 1 ≤ Nat.floor T + 2 := by
  by_cases hc : (0 : ℝ) ≤ T - 0.95
  · have a := Nat.floor_le hc
    have b := (Nat.lt_floor_add_one T).le
    have c : ((Nat.floor (T - 0.95) + 1 : ℕ) : ℝ)
        ≤ ((Nat.floor T + 2 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact Nat.cast_le.mp c
  · have hc' : T - 0.95 < 0 := lt_of_not_ge hc
    have h0 : Nat.floor (T - 0.95) = 0 := by
      have hle : Nat.floor (T - 0.95) ≤ Nat.floor (0 : ℝ) :=
        Nat.floor_mono (le_of_lt hc')
      rw [Nat.floor_zero] at hle
      exact Nat.le_zero.mp hle
    rw [h0]
    omega

/-- Squared real cap at `0.95`. -/
theorem D3SG_Gamma095_sq : Real.Gamma 0.95 ^ 2 ≤ 16 := by
  have hnn : (0 : ℝ) ≤ Real.Gamma 0.95 :=
    le_of_lt (Real.Gamma_pos_of_pos (by norm_num))
  have h := pow_le_pow_left₀ hnn D3SG_Real_Gamma_095_le_four 2
  norm_num at h ⊢
  exact h

/-- Product of the first `j` factors, each below height `T`, is `≤ (1/2)^j`. -/
theorem D3SG_prod_le_half_pow (T : ℝ) (hT : 0 ≤ T) (j : ℕ)
    (hj : ∀ k : ℕ, k < j → (0.95 : ℝ) + (k : ℝ) ≤ T) :
    ∏ k ∈ Finset.range j,
      ((0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + T ^ 2)) ≤ (1 / 2) ^ j := by
  have hj' : ∀ k : ℕ, k < j → (0.95 : ℝ) + (k : ℝ) ≤ |T| := by
    rw [abs_of_nonneg hT]
    exact hj
  have h0 : ∀ k ∈ Finset.range j,
      (0 : ℝ) ≤ (0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + T ^ 2) :=
    fun k _ => (D3SG_factor_mem_Icc 0.95 T (by norm_num) k).1
  have h1 : ∀ k ∈ Finset.range j,
      (0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + T ^ 2) ≤ 1 / 2 :=
    fun k hk =>
      D3SG_factor_le_half 0.95 T (by norm_num) k (hj' k (Finset.mem_range.mp hk))
  have h := Finset.prod_le_prod h0 h1
  rwa [Finset.prod_const, Finset.card_range] at h

/-- Half-power as exponential. -/
theorem D3SG_half_pow_exp (m : ℕ) :
    ((1 / 2 : ℝ) ^ m) = Real.exp (-(m : ℝ) * Real.log 2) := by
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [← Real.exp_nat_mul]
  congr 1
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  ring

/-- Four as exponential of log two. -/
theorem D3SG_four_exp : (4 : ℝ) = Real.exp (2 * Real.log 2) := by
  have e : Real.exp (2 * Real.log 2) = (Real.exp (Real.log 2)) ^ 2 := by
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    calc Real.exp (2 * Real.log 2)
        = Real.exp (((2 : ℕ) : ℝ) * Real.log 2) := by rw [h2]
      _ = (Real.exp (Real.log 2)) ^ 2 := Real.exp_nat_mul _ _
  rw [e, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- Squaring the third-rate exponential. -/
theorem D3SG_exp_sq (T : ℝ) :
    (Real.exp (-(1 / 3) * T)) ^ 2 = Real.exp (-(2 / 3) * T) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Small-height case: trivial cap dominates the exponential. -/
theorem D3SG_Gamma_small_height (s : ℂ) (hre : s.re = 0.95)
    (hT : |s.im| ≤ 1) :
    ‖Complex.Gamma s‖ ≤ 8 * Real.exp (-(1 / 3) * |s.im|) := by
  have hspos : (0 : ℝ) < s.re := by rw [hre]; norm_num
  have hdom : ‖Complex.Gamma s‖ ≤ Real.Gamma 0.95 := by
    have h := D3SG_Gamma_norm_le_real s hspos
    rwa [hre] at h
  have hle : -Real.log 2 ≤ -(1 / 3) * |s.im| := by
    have hlog := D3SG_log_two_gt
    linarith
  have h2 := Real.exp_le_exp.mpr hle
  have e : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [← Real.log_inv]
    rw [Real.exp_log (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹)]
    norm_num
  have hexp : (4 : ℝ) ≤ 8 * Real.exp (-(1 / 3) * |s.im|) := by
    calc (4 : ℝ) = 8 * (1 / 2) := by norm_num
      _ = 8 * Real.exp (-Real.log 2) := by rw [e]
      _ ≤ 8 * Real.exp (-(1 / 3) * |s.im|) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
  exact le_trans (le_trans hdom D3SG_Real_Gamma_095_le_four) hexp

/-- Squared tall-height bound via half-factor counting. -/
theorem D3SG_tall_prod_bound (s : ℂ) (hre : s.re = 0.95)
    (hT095 : (0 : ℝ) ≤ |s.im| - 0.95) :
    ‖Complex.Gamma s‖ ^ 2
      ≤ 16 * (1 / 2) ^ (Nat.floor (|s.im| - 0.95) + 1) := by
  have hspos : (0 : ℝ) < s.re := by rw [hre]; norm_num
  have hprod := D3SG_sq_prod hspos (Nat.floor |s.im| + 2)
  rw [hre, ← sq_abs s.im] at hprod
  have hsub : Finset.range (Nat.floor (|s.im| - 0.95) + 1)
      ⊆ Finset.range (Nat.floor |s.im| + 2) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    exact lt_of_lt_of_le hx (D3SG_floor_count |s.im|)
  have hPsub : ∏ k ∈ Finset.range (Nat.floor |s.im| + 2),
      ((0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + |s.im| ^ 2))
      ≤ ∏ k ∈ Finset.range (Nat.floor (|s.im| - 0.95) + 1),
      ((0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + |s.im| ^ 2)) :=
    Finset.prod_le_prod_of_subset_of_le_one
      hsub
      (fun k _ => (D3SG_factor_mem_Icc (0.95 : ℝ) _ (by norm_num) k).1)
      (fun k _ _ => (D3SG_factor_mem_Icc (0.95 : ℝ) _ (by norm_num) k).2)
  have hhalf := D3SG_prod_le_half_pow |s.im| (abs_nonneg _)
    (Nat.floor (|s.im| - 0.95) + 1) (fun k hkj => by
      have hkle : k ≤ Nat.floor (|s.im| - 0.95) := Nat.lt_add_one_iff.mp hkj
      have h1 : (k : ℝ) ≤ ((Nat.floor (|s.im| - 0.95) : ℕ) : ℝ) :=
        Nat.cast_le.mpr hkle
      have h2 := Nat.floor_le hT095
      linarith)
  have hP := le_trans hPsub hhalf
  exact le_trans hprod (mul_le_mul D3SG_Gamma095_sq hP
    (Finset.prod_nonneg
      (fun k _ => (D3SG_factor_mem_Icc (0.95 : ℝ) _ (by norm_num) k).1))
    (by norm_num))

/-- Explicit Stirling-type decay on `Re = 0.95`: `‖Γ‖ ≤ 8·exp(−|Im|/3)`. -/
theorem D3SG_Gamma_line095_exp_decay (s : ℂ) (hre : s.re = 0.95) :
    ‖Complex.Gamma s‖ ≤ 8 * Real.exp (-(1 / 3) * |s.im|) := by
  by_cases hT : |s.im| ≤ 1
  · exact D3SG_Gamma_small_height s hre hT
  · have hT1 : (1 : ℝ) < |s.im| := lt_of_not_ge hT
    have hT095 : (0 : ℝ) ≤ |s.im| - 0.95 := by linarith
    have h1 := D3SG_tall_prod_bound s hre hT095
    have hkey : (2 / 3 : ℝ) * |s.im|
        ≤ (((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ) + 2) * Real.log 2 := by
      have hjm : (0 : ℝ) ≤ ((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ) + 2 := by
        have hnn := Nat.cast_nonneg (α := ℝ) (Nat.floor (|s.im| - 0.95) + 1)
        linarith
      have hTj : |s.im| ≤ ((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ) + 2 := by
        have a := Nat.floor_le hT095
        have b : ((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ)
            = ((Nat.floor (|s.im| - 0.95) : ℕ) : ℝ) + 1 := by
          rw [Nat.cast_add, Nat.cast_one]
        have c := Nat.lt_floor_add_one (|s.im| - 0.95)
        linarith
      calc (2 / 3 : ℝ) * |s.im|
          ≤ (2 / 3) * (((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ) + 2) :=
            mul_le_mul_of_nonneg_left hTj (by norm_num)
        _ ≤ (((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ) + 2) * Real.log 2 := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_left D3SG_log_two_gt.le hjm
    have hmono : Real.exp (-((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ) * Real.log 2)
        ≤ Real.exp (2 * Real.log 2 + -(2 / 3) * |s.im|) := by
      apply Real.exp_le_exp.mpr
      linarith [hkey]
    have hfin : (16 : ℝ)
        * Real.exp (-((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ) * Real.log 2)
        ≤ 8 ^ 2 * Real.exp (-(2 / 3) * |s.im|) := by
      have e : (8 : ℝ) ^ 2 * Real.exp (-(2 / 3) * |s.im|)
          = 16 * (4 * Real.exp (-(2 / 3) * |s.im|)) := by ring
      rw [e, D3SG_four_exp, ← Real.exp_add]
      exact mul_le_mul_of_nonneg_left hmono (by norm_num)
    have hsq : ‖Complex.Gamma s‖ ^ 2 ≤ (8 * Real.exp (-(1 / 3) * |s.im|)) ^ 2 := by
      rw [mul_pow, D3SG_exp_sq]
      have h1' : ‖Complex.Gamma s‖ ^ 2
          ≤ 16 * Real.exp (-((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ)
            * Real.log 2) := by
        rw [← D3SG_half_pow_exp]
        exact h1
      exact le_trans h1' hfin
    have hnn : (0 : ℝ) ≤ 8 * Real.exp (-(1 / 3) * |s.im|) := by positivity
    have hsqrt := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hnn] at hsqrt
    exact hsqrt

#print axioms D3SG_Gamma_line095_exp_decay
