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

/-- Sharpened real cap `Γ(0.95) ≤ 1.1` (same shift + convexity, tighter final step). -/
theorem D3SG_Real_Gamma_095_le_one_one : Real.Gamma 0.95 ≤ 1.1 := by
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
  have h2 : (1 : ℝ) / 0.95 ≤ 1.1 := by norm_num
  calc Real.Gamma 0.95 = Real.Gamma (0.95 + 1) / 0.95 := hdiv
    _ ≤ 1 / 0.95 := h1
    _ ≤ 1.1 := h2

/-- Squared sharpened cap at `0.95`. -/
theorem D3SG_Gamma095_sq_sharp : Real.Gamma 0.95 ^ 2 ≤ 1.21 := by
  have hnn : (0 : ℝ) ≤ Real.Gamma 0.95 :=
    le_of_lt (Real.Gamma_pos_of_pos (by norm_num))
  have h := pow_le_pow_left₀ hnn D3SG_Real_Gamma_095_le_one_one 2
  norm_num at h ⊢
  exact h

/-- Threshold factor bound: `σ+k ≤ α·|T|` gives `≤ α²/(α²+1)`. -/
theorem D3SG_factor_le_thresh (σ T α : ℝ) (hσ : 0 < σ) (k : ℕ)
    (h : σ + (k : ℝ) ≤ α * |T|) :
    (σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2) ≤ α ^ 2 / (α ^ 2 + 1) := by
  have hsk : (0 : ℝ) ≤ σ + (k : ℝ) := by
    have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hT2 : (σ + (k : ℝ)) ^ 2 ≤ α ^ 2 * T ^ 2 := by
    have h1 : (σ + (k : ℝ)) ^ 2 ≤ (α * |T|) ^ 2 := pow_le_pow_left₀ hsk h 2
    rw [mul_pow, sq_abs] at h1
    exact h1
  have hpos : (0 : ℝ) < (σ + (k : ℝ)) ^ 2 + T ^ 2 := by
    have h2 : (0 : ℝ) < (σ + (k : ℝ)) ^ 2 := by
      apply pow_pos _ 2
      have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    linarith [sq_nonneg T]
  have hden : (0 : ℝ) < α ^ 2 + 1 := by
    have hs := sq_nonneg α
    linarith
  rw [div_le_div_iff₀ hpos hden]
  nlinarith [hT2]

/-- Factors at height below `|T|/2` are at most one fifth. -/
theorem D3SG_factor_le_fifth (σ T : ℝ) (hσ : 0 < σ) (k : ℕ)
    (h : σ + (k : ℝ) ≤ |T| / 2) :
    (σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2) ≤ 1 / 5 := by
  have hα : σ + (k : ℝ) ≤ (1 / 2) * |T| := by linarith
  have h := D3SG_factor_le_thresh σ T (1 / 2) hσ k hα
  have e : ((1 / 2 : ℝ)) ^ 2 / ((1 / 2) ^ 2 + 1) = 1 / 5 := by norm_num
  rwa [e] at h

/-- Fifth implies quarter (keeps everything in powers of two). -/
theorem D3SG_factor_le_quarter (σ T : ℝ) (hσ : 0 < σ) (k : ℕ)
    (h : σ + (k : ℝ) ≤ |T| / 2) :
    (σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2) ≤ 1 / 4 :=
  le_trans (D3SG_factor_le_fifth σ T hσ k h) (by norm_num)

/-- Half-height count is dominated by the full count. -/
theorem D3SG_floor_half_le (T : ℝ) (hT : 2 ≤ T) :
    Nat.floor (T / 2 - 0.95) + 1 ≤ Nat.floor (T - 0.95) + 1 := by
  have hnn : (0 : ℝ) ≤ T / 2 - 0.95 := by linarith
  have hle : T / 2 - 0.95 ≤ T - 0.95 := by linarith
  have c : ((Nat.floor (T / 2 - 0.95) + 1 : ℕ) : ℝ)
      ≤ ((Nat.floor (T - 0.95) + 1 : ℕ) : ℝ) := by
    push_cast
    have a := Nat.floor_le hnn
    have b := (Nat.lt_floor_add_one (T - 0.95)).le
    linarith
  exact Nat.cast_le.mp c

/-- Quarter-power product over the half-height range. -/
theorem D3SG_prod_quarter_pow (T : ℝ) (hT : 2 ≤ T) :
    ∏ k ∈ Finset.range (Nat.floor (T / 2 - 0.95) + 1),
      ((0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + T ^ 2))
      ≤ (1 / 2) ^ (2 * (Nat.floor (T / 2 - 0.95) + 1)) := by
  have hTh : (0 : ℝ) ≤ T / 2 - 0.95 := by linarith
  have h1 : ∀ k ∈ Finset.range (Nat.floor (T / 2 - 0.95) + 1),
      (0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + T ^ 2) ≤ 1 / 4 := by
    intro k hk
    apply D3SG_factor_le_quarter 0.95 T (by norm_num) k
    have hkle : k ≤ Nat.floor (T / 2 - 0.95) :=
      Nat.lt_add_one_iff.mp (Finset.mem_range.mp hk)
    have hc : (k : ℝ) ≤ ((Nat.floor (T / 2 - 0.95) : ℕ) : ℝ) :=
      Nat.cast_le.mpr hkle
    have hf := Nat.floor_le hTh
    have hTnn : (0 : ℝ) ≤ T := by linarith
    rw [abs_of_nonneg hTnn]
    linarith
  have h := Finset.prod_le_prod
    (fun k _ => (D3SG_factor_mem_Icc 0.95 T (by norm_num) k).1) h1
  rw [Finset.prod_const, Finset.card_range] at h
  have e : ((1 / 4 : ℝ)) ^ (Nat.floor (T / 2 - 0.95) + 1)
      = (1 / 2) ^ (2 * (Nat.floor (T / 2 - 0.95) + 1)) := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, ← pow_mul]
  rwa [e] at h

/-- Half-power product over the middle interval. -/
theorem D3SG_prod_Ico_half_pow (T : ℝ) (hT : 2 ≤ T) :
    ∏ k ∈ Finset.Ico (Nat.floor (T / 2 - 0.95) + 1) (Nat.floor (T - 0.95) + 1),
      ((0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + T ^ 2))
      ≤ (1 / 2) ^ (Nat.floor (T - 0.95) + 1 - (Nat.floor (T / 2 - 0.95) + 1)) := by
  have hT0 : (0 : ℝ) ≤ T - 0.95 := by linarith
  have h1 : ∀ k ∈ Finset.Ico (Nat.floor (T / 2 - 0.95) + 1)
      (Nat.floor (T - 0.95) + 1),
      (0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + T ^ 2) ≤ 1 / 2 := by
    intro k hk
    apply D3SG_factor_le_half 0.95 T (by norm_num) k
    have hlt : k < Nat.floor (T - 0.95) + 1 := (Finset.mem_Ico.mp hk).2
    have hkle : k ≤ Nat.floor (T - 0.95) := Nat.lt_add_one_iff.mp hlt
    have hc : (k : ℝ) ≤ ((Nat.floor (T - 0.95) : ℕ) : ℝ) := Nat.cast_le.mpr hkle
    have hf := Nat.floor_le hT0
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T)]
    linarith
  have h := Finset.prod_le_prod
    (fun k _ => (D3SG_factor_mem_Icc 0.95 T (by norm_num) k).1) h1
  rwa [Finset.prod_const, Nat.card_Ico] at h

/-- Two-tier product: quarter-factors below `T/2`, half-factors up to `T`. -/
theorem D3SG_prod_two_tier (T : ℝ) (hT : 2 ≤ T) :
    ∏ k ∈ Finset.range (Nat.floor (T - 0.95) + 1),
      ((0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + T ^ 2))
      ≤ (1 / 2) ^ (Nat.floor (T / 2 - 0.95) + 1 + (Nat.floor (T - 0.95) + 1)) := by
  have hj : Nat.floor (T / 2 - 0.95) + 1 ≤ Nat.floor (T - 0.95) + 1 :=
    D3SG_floor_half_le T hT
  have hsplit : Nat.floor (T / 2 - 0.95) + 1
      + (Nat.floor (T - 0.95) + 1 - (Nat.floor (T / 2 - 0.95) + 1))
      = Nat.floor (T - 0.95) + 1 := Nat.add_sub_cancel' hj
  have hprod := Finset.prod_range_add
    (fun k => (0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + T ^ 2))
    (Nat.floor (T / 2 - 0.95) + 1)
    (Nat.floor (T - 0.95) + 1 - (Nat.floor (T / 2 - 0.95) + 1))
  rw [hsplit] at hprod
  rw [hprod]
  have hbig' := D3SG_prod_Ico_half_pow T hT
  rw [Finset.prod_Ico_eq_prod_range] at hbig'
  have hmul := mul_le_mul (D3SG_prod_quarter_pow T hT) hbig'
    (Finset.prod_nonneg (fun k _ => (D3SG_factor_mem_Icc 0.95 T (by norm_num)
      (Nat.floor (T / 2 - 0.95) + 1 + k)).1))
    (by positivity)
  rw [← pow_add] at hmul
  have hexp : 2 * (Nat.floor (T / 2 - 0.95) + 1)
      + (Nat.floor (T - 0.95) + 1 - (Nat.floor (T / 2 - 0.95) + 1))
      = Nat.floor (T / 2 - 0.95) + 1 + (Nat.floor (T - 0.95) + 1) := by omega
  rwa [hexp] at hmul

/-- Squared tall-height bound via two-tier counting (`|T| ≥ 2`). -/
theorem D3SG_tall_prod_bound_half (s : ℂ) (hre : s.re = 0.95)
    (hT : 2 ≤ |s.im|) :
    ‖Complex.Gamma s‖ ^ 2
      ≤ 1.21 * (1 / 2) ^ (Nat.floor (|s.im| / 2 - 0.95) + 1
        + (Nat.floor (|s.im| - 0.95) + 1)) := by
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
  have hP := le_trans hPsub (D3SG_prod_two_tier |s.im| hT)
  exact le_trans hprod (mul_le_mul D3SG_Gamma095_sq_sharp hP
    (Finset.prod_nonneg
      (fun k _ => (D3SG_factor_mem_Icc (0.95 : ℝ) _ (by norm_num) k).1))
    (by norm_num))

/-- Squaring the half-rate exponential. -/
theorem D3SG_exp_half_sq (T : ℝ) :
    (Real.exp (-(1 / 2) * T)) ^ 2 = Real.exp (-T) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Small-height case at the `|T| ≤ 2` split with the sharp cap. -/
theorem D3SG_Gamma_small_height_half (s : ℂ) (hre : s.re = 0.95)
    (hT : |s.im| ≤ 2) :
    ‖Complex.Gamma s‖ ≤ 4 * Real.exp (-(1 / 2) * |s.im|) := by
  have hspos : (0 : ℝ) < s.re := by rw [hre]; norm_num
  have hdom : ‖Complex.Gamma s‖ ≤ Real.Gamma 0.95 := by
    have h := D3SG_Gamma_norm_le_real s hspos
    rwa [hre] at h
  have hub : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hbase : (1.1 : ℝ) ≤ 4 * (Real.exp 1)⁻¹ := by
    have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    rw [le_mul_inv_iff₀ hpos]
    linarith [hub]
  have hmono : Real.exp (-1) ≤ Real.exp (-(1 / 2) * |s.im|) := by
    apply Real.exp_le_exp.mpr
    have habs := abs_nonneg s.im
    linarith
  have hexp : (1.1 : ℝ) ≤ 4 * Real.exp (-(1 / 2) * |s.im|) := by
    have hinv : Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
    calc (1.1 : ℝ) ≤ 4 * (Real.exp 1)⁻¹ := hbase
      _ = 4 * Real.exp (-1) := by rw [hinv]
      _ ≤ 4 * Real.exp (-(1 / 2) * |s.im|) :=
          mul_le_mul_of_nonneg_left hmono (by norm_num)
  exact le_trans (le_trans hdom D3SG_Real_Gamma_095_le_one_one) hexp

/-- Explicit Stirling-type decay on `Re = 0.95`: `‖Γ‖ ≤ 4·exp(−|Im|/2)`. -/
theorem D3SG_Gamma_line095_exp_decay_half (s : ℂ) (hre : s.re = 0.95) :
    ‖Complex.Gamma s‖ ≤ 4 * Real.exp (-(1 / 2) * |s.im|) := by
  by_cases hT : |s.im| ≤ 2
  · exact D3SG_Gamma_small_height_half s hre hT
  · have hT2 : (2 : ℝ) ≤ |s.im| := le_of_not_ge hT
    have habs := abs_nonneg s.im
    have h1 := D3SG_tall_prod_bound_half s hre hT2
    have hM : |s.im| ≤ (2 / 3) * ((((Nat.floor (|s.im| / 2 - 0.95) + 1 : ℕ) : ℝ)
        + ((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ)) + 2) := by
      have c1 : |s.im| / 2 - 0.95
          < ((Nat.floor (|s.im| / 2 - 0.95) + 1 : ℕ) : ℝ) := by
        push_cast
        exact Nat.lt_floor_add_one _
      have c2 : |s.im| - 0.95
          < ((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ) := by
        push_cast
        exact Nat.lt_floor_add_one _
      linarith
    have hkey : |s.im| ≤ ((((Nat.floor (|s.im| / 2 - 0.95) + 1 : ℕ) : ℝ)
        + ((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ)) + 2) * Real.log 2 := by
      have hnn : (0 : ℝ) ≤ (((Nat.floor (|s.im| / 2 - 0.95) + 1 : ℕ) : ℝ)
          + ((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ)) + 2 := by
        have n1 := Nat.cast_nonneg (α := ℝ) (Nat.floor (|s.im| / 2 - 0.95) + 1)
        have n2 := Nat.cast_nonneg (α := ℝ) (Nat.floor (|s.im| - 0.95) + 1)
        linarith
      calc |s.im| ≤ (2 / 3) * _ := hM
        _ ≤ _ * Real.log 2 := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left D3SG_log_two_gt.le hnn
    have hmono : Real.exp (-(((Nat.floor (|s.im| / 2 - 0.95) + 1 : ℕ) : ℝ)
        + ((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ)) * Real.log 2)
        ≤ Real.exp (2 * Real.log 2 + -|s.im|) := by
      apply Real.exp_le_exp.mpr
      linarith [hkey]
    have hfin : (1.21 : ℝ)
        * Real.exp (-(((Nat.floor (|s.im| / 2 - 0.95) + 1 : ℕ) : ℝ)
          + ((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ)) * Real.log 2)
        ≤ (4 : ℝ) ^ 2 * Real.exp (-|s.im|) := by
      have hle : (1.21 : ℝ) * Real.exp (2 * Real.log 2 + -|s.im|)
          ≤ (4 : ℝ) ^ 2 * Real.exp (-|s.im|) := by
        rw [Real.exp_add, ← D3SG_four_exp]
        have hnn : (0 : ℝ) ≤ Real.exp (-|s.im|) := (Real.exp_pos _).le
        calc (1.21 : ℝ) * (4 * Real.exp (-|s.im|))
            = 4.84 * Real.exp (-|s.im|) := by ring
          _ ≤ 4 ^ 2 * Real.exp (-|s.im|) := by
            have h16 : (4 : ℝ) ^ 2 = 16 := by norm_num
            rw [h16]
            linarith [hnn]
      exact le_trans
        (mul_le_mul_of_nonneg_left hmono (by norm_num)) hle
    have hsq : ‖Complex.Gamma s‖ ^ 2
        ≤ (4 * Real.exp (-(1 / 2) * |s.im|)) ^ 2 := by
      rw [mul_pow, D3SG_exp_half_sq]
      have h1' := h1
      rw [D3SG_half_pow_exp, Nat.cast_add] at h1'
      exact le_trans h1' hfin
    have hnn : (0 : ℝ) ≤ 4 * Real.exp (-(1 / 2) * |s.im|) := by positivity
    have hsqrt := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hnn] at hsqrt
    exact hsqrt

#print axioms D3SG_Gamma_line095_exp_decay_half

/-- Small-height case at the `|T| ≤ 2` split, constant `3` (tight `1.1·e ≤ 3`). -/
theorem D3SG_Gamma_small_height_C3 (s : ℂ) (hre : s.re = 0.95)
    (hT : |s.im| ≤ 2) :
    ‖Complex.Gamma s‖ ≤ 3 * Real.exp (-(1 / 2) * |s.im|) := by
  have hspos : (0 : ℝ) < s.re := by rw [hre]; norm_num
  have hdom : ‖Complex.Gamma s‖ ≤ Real.Gamma 0.95 := by
    have h := D3SG_Gamma_norm_le_real s hspos
    rwa [hre] at h
  have hub : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hbase : (1.1 : ℝ) ≤ 3 * (Real.exp 1)⁻¹ := by
    have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    rw [le_mul_inv_iff₀ hpos]
    linarith [hub]
  have hmono : Real.exp (-1) ≤ Real.exp (-(1 / 2) * |s.im|) := by
    apply Real.exp_le_exp.mpr
    have habs := abs_nonneg s.im
    linarith
  have hexp : (1.1 : ℝ) ≤ 3 * Real.exp (-(1 / 2) * |s.im|) := by
    have hinv : Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
    calc (1.1 : ℝ) ≤ 3 * (Real.exp 1)⁻¹ := hbase
      _ = 3 * Real.exp (-1) := by rw [hinv]
      _ ≤ 3 * Real.exp (-(1 / 2) * |s.im|) :=
          mul_le_mul_of_nonneg_left hmono (by norm_num)
  exact le_trans (le_trans hdom D3SG_Real_Gamma_095_le_one_one) hexp

#print axioms D3SG_Gamma_small_height_C3

/-- Explicit Stirling-type decay on `Re = 0.95`: `‖Γ‖ ≤ 3·exp(−|Im|/2)`. -/
theorem D3SG_Gamma_line095_exp_decay_C3 (s : ℂ) (hre : s.re = 0.95) :
    ‖Complex.Gamma s‖ ≤ 3 * Real.exp (-(1 / 2) * |s.im|) := by
  by_cases hT : |s.im| ≤ 2
  · exact D3SG_Gamma_small_height_C3 s hre hT
  · have hT2 : (2 : ℝ) ≤ |s.im| := le_of_not_ge hT
    have h1 := D3SG_tall_prod_bound_half s hre hT2
    have hM : |s.im| ≤ (2 / 3) * ((((Nat.floor (|s.im| / 2 - 0.95) + 1 : ℕ) : ℝ)
        + ((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ)) + 2) := by
      have c1 : |s.im| / 2 - 0.95 < ((Nat.floor (|s.im| / 2 - 0.95) + 1 : ℕ) : ℝ) := by
        push_cast
        exact Nat.lt_floor_add_one _
      have c2 : |s.im| - 0.95 < ((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ) := by
        push_cast
        exact Nat.lt_floor_add_one _
      linarith
    have hkey : |s.im| ≤ ((((Nat.floor (|s.im| / 2 - 0.95) + 1 : ℕ) : ℝ)
        + ((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ)) + 2) * Real.log 2 := by
      have hnn : (0 : ℝ) ≤ (((Nat.floor (|s.im| / 2 - 0.95) + 1 : ℕ) : ℝ)
          + ((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ)) + 2 := by
        have n1 := Nat.cast_nonneg (α := ℝ) (Nat.floor (|s.im| / 2 - 0.95) + 1)
        have n2 := Nat.cast_nonneg (α := ℝ) (Nat.floor (|s.im| - 0.95) + 1)
        linarith
      calc |s.im| ≤ (2 / 3) * _ := hM
        _ ≤ _ * Real.log 2 := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left D3SG_log_two_gt.le hnn
    have hmono : Real.exp (-(((Nat.floor (|s.im| / 2 - 0.95) + 1 : ℕ) : ℝ)
        + ((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ)) * Real.log 2)
        ≤ Real.exp (2 * Real.log 2 + -|s.im|) := by
      apply Real.exp_le_exp.mpr
      linarith [hkey]
    have hfin : (1.21 : ℝ)
        * Real.exp (-(((Nat.floor (|s.im| / 2 - 0.95) + 1 : ℕ) : ℝ)
          + ((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ)) * Real.log 2)
        ≤ (3 : ℝ) ^ 2 * Real.exp (-|s.im|) := by
      have hle : (1.21 : ℝ) * Real.exp (2 * Real.log 2 + -|s.im|)
          ≤ (3 : ℝ) ^ 2 * Real.exp (-|s.im|) := by
        rw [Real.exp_add, ← D3SG_four_exp]
        have hnn : (0 : ℝ) ≤ Real.exp (-|s.im|) := (Real.exp_pos _).le
        have h9 : (3 : ℝ) ^ 2 = 9 := by norm_num
        rw [h9]
        linarith [hnn]
      exact le_trans
        (mul_le_mul_of_nonneg_left hmono (by norm_num)) hle
    have hsq : ‖Complex.Gamma s‖ ^ 2 ≤ (3 * Real.exp (-(1 / 2) * |s.im|)) ^ 2 := by
      rw [mul_pow, D3SG_exp_half_sq]
      have h1' := h1
      rw [D3SG_half_pow_exp, Nat.cast_add] at h1'
      exact le_trans h1' hfin
    have hnn : (0 : ℝ) ≤ 3 * Real.exp (-(1 / 2) * |s.im|) := by positivity
    have hsqrt := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hnn] at hsqrt
    exact hsqrt

#print axioms D3SG_Gamma_line095_exp_decay_C3

/-- Factors at height below `|T|/4` are at most one sixteenth (via `1/17 ≤ 1/16`). -/
theorem D3SG_factor_le_sixteenth (σ T : ℝ) (hσ : 0 < σ) (k : ℕ)
    (h : σ + (k : ℝ) ≤ |T| / 4) :
    (σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2) ≤ 1 / 16 := by
  have hα : σ + (k : ℝ) ≤ (1 / 4) * |T| := by linarith
  have hth := D3SG_factor_le_thresh σ T (1 / 4) hσ k hα
  have e : ((1 / 4 : ℝ)) ^ 2 / ((1 / 4) ^ 2 + 1) = 1 / 17 := by norm_num
  rw [e] at hth
  exact le_trans hth (by norm_num)

/-- Quarter-height count is dominated by the half-height count. -/
theorem D3SG_floor_quarter_le (T : ℝ) (hT : 4 ≤ T) :
    Nat.floor (T / 4 - 0.95) + 1 ≤ Nat.floor (T / 2 - 0.95) + 1 := by
  have hnn : (0 : ℝ) ≤ T / 4 - 0.95 := by linarith
  have hle : T / 4 - 0.95 ≤ T / 2 - 0.95 := by linarith
  have c : ((Nat.floor (T / 4 - 0.95) + 1 : ℕ) : ℝ)
      ≤ ((Nat.floor (T / 2 - 0.95) + 1 : ℕ) : ℝ) := by
    push_cast
    have a := Nat.floor_le hnn
    have b := (Nat.lt_floor_add_one (T / 2 - 0.95)).le
    linarith
  exact Nat.cast_le.mp c

/-- Sixteenth-power product over the quarter-height range. -/
theorem D3SG_prod_sixteenth_pow (T : ℝ) (hT : 4 ≤ T) :
    ∏ k ∈ Finset.range (Nat.floor (T / 4 - 0.95) + 1),
      ((0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + T ^ 2))
      ≤ (1 / 2) ^ (4 * (Nat.floor (T / 4 - 0.95) + 1)) := by
  have hTh : (0 : ℝ) ≤ T / 4 - 0.95 := by linarith
  have h1 : ∀ k ∈ Finset.range (Nat.floor (T / 4 - 0.95) + 1),
      (0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + T ^ 2) ≤ 1 / 16 := by
    intro k hk
    apply D3SG_factor_le_sixteenth 0.95 T (by norm_num) k
    have hkle : k ≤ Nat.floor (T / 4 - 0.95) :=
      Nat.lt_add_one_iff.mp (Finset.mem_range.mp hk)
    have hc : (k : ℝ) ≤ ((Nat.floor (T / 4 - 0.95) : ℕ) : ℝ) :=
      Nat.cast_le.mpr hkle
    have hf := Nat.floor_le hTh
    have hTnn : (0 : ℝ) ≤ T := by linarith
    rw [abs_of_nonneg hTnn]
    linarith
  have h := Finset.prod_le_prod
    (fun k _ => (D3SG_factor_mem_Icc 0.95 T (by norm_num) k).1) h1
  rw [Finset.prod_const, Finset.card_range] at h
  have e : ((1 / 16 : ℝ)) ^ (Nat.floor (T / 4 - 0.95) + 1)
      = (1 / 2) ^ (4 * (Nat.floor (T / 4 - 0.95) + 1)) := by
    rw [show (1 / 16 : ℝ) = (1 / 2) ^ 4 by norm_num, ← pow_mul]
  rwa [e] at h

#print axioms D3SG_prod_sixteenth_pow

/-- Index counting, `σ`-general (`0 ≤ σ` suffices). -/
theorem D3SG_floor_count_sigma (σ T : ℝ) (hσ : 0 ≤ σ) :
    Nat.floor (T - σ) + 1 ≤ Nat.floor T + 2 := by
  by_cases hc : (0 : ℝ) ≤ T - σ
  · have a := Nat.floor_le hc
    have b := (Nat.lt_floor_add_one T).le
    have c : ((Nat.floor (T - σ) + 1 : ℕ) : ℝ)
        ≤ ((Nat.floor T + 2 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact Nat.cast_le.mp c
  · have hc' : T - σ < 0 := lt_of_not_ge hc
    have h0 : Nat.floor (T - σ) = 0 := by
      have hle : Nat.floor (T - σ) ≤ Nat.floor (0 : ℝ) :=
        Nat.floor_mono (le_of_lt hc')
      rw [Nat.floor_zero] at hle
      exact Nat.le_zero.mp hle
    rw [h0]
    omega

/-- Product of the first `j` factors, each below height `T`, `σ`-general. -/
theorem D3SG_prod_le_half_pow_sigma (σ T : ℝ) (hσ : 0 < σ) (hT : 0 ≤ T) (j : ℕ)
    (hj : ∀ k : ℕ, k < j → σ + (k : ℝ) ≤ T) :
    ∏ k ∈ Finset.range j,
      ((σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2)) ≤ (1 / 2) ^ j := by
  have hj' : ∀ k : ℕ, k < j → σ + (k : ℝ) ≤ |T| := by
    rw [abs_of_nonneg hT]
    exact hj
  have h0 : ∀ k ∈ Finset.range j,
      (0 : ℝ) ≤ (σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2) :=
    fun k _ => (D3SG_factor_mem_Icc σ T hσ k).1
  have h1 : ∀ k ∈ Finset.range j,
      (σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2) ≤ 1 / 2 :=
    fun k hk =>
      D3SG_factor_le_half σ T hσ k (hj' k (Finset.mem_range.mp hk))
  have h := Finset.prod_le_prod h0 h1
  rwa [Finset.prod_const, Finset.card_range] at h

#print axioms D3SG_prod_le_half_pow_sigma

/-- Middle-tier product: quarter-factors on `Ico Q H` (half range minus quarter). -/
theorem D3SG_prod_Ico_quarter_pow (T : ℝ) (hT : 4 ≤ T) :
    ∏ k ∈ Finset.Ico (Nat.floor (T / 4 - 0.95) + 1)
      (Nat.floor (T / 2 - 0.95) + 1),
      ((0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + T ^ 2))
      ≤ (1 / 2) ^ (2 * (Nat.floor (T / 2 - 0.95) + 1
        - (Nat.floor (T / 4 - 0.95) + 1))) := by
  have hT0 : (0 : ℝ) ≤ T / 2 - 0.95 := by linarith
  have h1 : ∀ k ∈ Finset.Ico (Nat.floor (T / 4 - 0.95) + 1)
      (Nat.floor (T / 2 - 0.95) + 1),
      (0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + T ^ 2) ≤ 1 / 4 := by
    intro k hk
    apply D3SG_factor_le_quarter 0.95 T (by norm_num) k
    have hlt : k < Nat.floor (T / 2 - 0.95) + 1 := (Finset.mem_Ico.mp hk).2
    have hkle : k ≤ Nat.floor (T / 2 - 0.95) := Nat.lt_add_one_iff.mp hlt
    have hc : (k : ℝ) ≤ ((Nat.floor (T / 2 - 0.95) : ℕ) : ℝ) := Nat.cast_le.mpr hkle
    have hf := Nat.floor_le hT0
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T)]
    linarith
  have h := Finset.prod_le_prod
    (fun k _ => (D3SG_factor_mem_Icc 0.95 T (by norm_num) k).1) h1
  rw [Finset.prod_const, Nat.card_Ico] at h
  have e : ((1 / 4 : ℝ)) ^ (Nat.floor (T / 2 - 0.95) + 1
      - (Nat.floor (T / 4 - 0.95) + 1))
      = (1 / 2) ^ (2 * (Nat.floor (T / 2 - 0.95) + 1
        - (Nat.floor (T / 4 - 0.95) + 1))) := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, ← pow_mul]
  rwa [e] at h

#print axioms D3SG_prod_Ico_quarter_pow

/-- Top-tier product in shifted-range form (matches `prod_range_add` tails). -/
theorem D3SG_prod_range_top_shift (T : ℝ) (hT : 2 ≤ T) :
    (∏ k ∈ Finset.range (Nat.floor (T - 0.95) + 1 - (Nat.floor (T / 2 - 0.95) + 1)),
      (0.95 + ((((Nat.floor (T / 2 - 0.95) + 1 + k : ℕ))) : ℝ)) ^ 2
      / ((0.95 + ((((Nat.floor (T / 2 - 0.95) + 1 + k : ℕ))) : ℝ)) ^ 2 + T ^ 2))
    ≤ (1 / 2) ^ (Nat.floor (T - 0.95) + 1 - (Nat.floor (T / 2 - 0.95) + 1)) := by
  have h := D3SG_prod_Ico_half_pow T hT
  rw [Finset.prod_Ico_eq_prod_range] at h
  exact h

/-- Three-tier product: sixteenth-factors on `[0,Q)`, quarter on `[Q,H)`, half on `[H,N)`.
Weights `4·(T/4)+2·(T/4)+1·(T/2)` drive the `c ≈ 0.69` tall bound. -/
theorem D3SG_prod_three_tier (T : ℝ) (hT : 4 ≤ T) :
    ∏ k ∈ Finset.range (Nat.floor (T - 0.95) + 1),
      ((0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + T ^ 2))
      ≤ (1 / 2) ^ (4 * (Nat.floor (T / 4 - 0.95) + 1)
        + 2 * (Nat.floor (T / 2 - 0.95) + 1 - (Nat.floor (T / 4 - 0.95) + 1))
        + (Nat.floor (T - 0.95) + 1 - (Nat.floor (T / 2 - 0.95) + 1))) := by
  have hT2 : (2 : ℝ) ≤ T := by linarith
  have hQH : Nat.floor (T / 4 - 0.95) + 1 ≤ Nat.floor (T / 2 - 0.95) + 1 :=
    D3SG_floor_quarter_le T hT
  have hHN : Nat.floor (T / 2 - 0.95) + 1 ≤ Nat.floor (T - 0.95) + 1 :=
    D3SG_floor_half_le T hT2
  have hsplitHN : Nat.floor (T / 2 - 0.95) + 1
      + (Nat.floor (T - 0.95) + 1 - (Nat.floor (T / 2 - 0.95) + 1))
      = Nat.floor (T - 0.95) + 1 := Nat.add_sub_cancel' hHN
  have hsplitQH : Nat.floor (T / 4 - 0.95) + 1
      + (Nat.floor (T / 2 - 0.95) + 1 - (Nat.floor (T / 4 - 0.95) + 1))
      = Nat.floor (T / 2 - 0.95) + 1 := Nat.add_sub_cancel' hQH
  have hprodT := Finset.prod_range_add
    (fun k : ℕ => (0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + T ^ 2))
    (Nat.floor (T / 2 - 0.95) + 1)
    (Nat.floor (T - 0.95) + 1 - (Nat.floor (T / 2 - 0.95) + 1))
  rw [hsplitHN] at hprodT
  have hprodM := Finset.prod_range_add
    (fun k : ℕ => (0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + T ^ 2))
    (Nat.floor (T / 4 - 0.95) + 1)
    (Nat.floor (T / 2 - 0.95) + 1 - (Nat.floor (T / 4 - 0.95) + 1))
  rw [hsplitQH] at hprodM
  have h1 := D3SG_prod_sixteenth_pow T hT
  have h2 := D3SG_prod_Ico_quarter_pow T hT
  rw [Finset.prod_Ico_eq_prod_range] at h2
  have h3 := D3SG_prod_range_top_shift T hT2
  have hmul := mul_le_mul (mul_le_mul h1 h2
    (Finset.prod_nonneg (fun k _ => (D3SG_factor_mem_Icc 0.95 T (by norm_num)
      (Nat.floor (T / 4 - 0.95) + 1 + k)).1))
    (by positivity)) h3
    (Finset.prod_nonneg (fun k _ => (D3SG_factor_mem_Icc 0.95 T (by norm_num)
      (Nat.floor (T / 2 - 0.95) + 1 + k)).1))
    (by positivity)
  rw [← pow_add, ← pow_add] at hmul
  rw [hprodT, hprodM]
  exact hmul

#print axioms D3SG_prod_three_tier

/-- Squared tall-height bound via three-tier counting (`|T| ≥ 4`). -/
theorem D3SG_tall_prod_bound_three (s : ℂ) (hre : s.re = 0.95)
    (hT : 4 ≤ |s.im|) :
    ‖Complex.Gamma s‖ ^ 2
      ≤ 1.21 * (1 / 2) ^ (4 * (Nat.floor (|s.im| / 4 - 0.95) + 1)
        + 2 * (Nat.floor (|s.im| / 2 - 0.95) + 1 - (Nat.floor (|s.im| / 4 - 0.95) + 1))
        + (Nat.floor (|s.im| - 0.95) + 1 - (Nat.floor (|s.im| / 2 - 0.95) + 1))) := by
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
  have hP := le_trans hPsub (D3SG_prod_three_tier |s.im| hT)
  exact le_trans hprod (mul_le_mul D3SG_Gamma095_sq_sharp hP
    (Finset.prod_nonneg
      (fun k _ => (D3SG_factor_mem_Icc (0.95 : ℝ) _ (by norm_num) k).1))
    (by norm_num))

/-- Squaring the `log 2`-rate exponential. -/
theorem D3SG_exp_log2_sq (T : ℝ) :
    (Real.exp (-Real.log 2 * T)) ^ 2 = Real.exp (-(2 * Real.log 2) * T) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Four `log 2`s exponentiate to sixteen (exact, no upper bound needed). -/
theorem D3SG_exp_four_log2 : Real.exp (4 * Real.log 2) = 16 := by
  have e : Real.exp (4 * Real.log 2) = (Real.exp (Real.log 2)) ^ 4 := by
    have h4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
    calc Real.exp (4 * Real.log 2)
        = Real.exp (((4 : ℕ) : ℝ) * Real.log 2) := by rw [h4]
      _ = (Real.exp (Real.log 2)) ^ 4 := Real.exp_nat_mul _ _
  rw [e, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

#print axioms D3SG_tall_prod_bound_three

/-- Tall three-tier decay on `Re = 0.95`: `‖Γ‖ ≤ 5·exp(−log 2·|Im|)`, `c = log 2 ≈ 0.69`. -/
theorem D3SG_tall_three_tier (s : ℂ) (hre : s.re = 0.95)
    (hT : 4 ≤ |s.im|) :
    ‖Complex.Gamma s‖ ≤ 5 * Real.exp (-Real.log 2 * |s.im|) := by
  have h1 := D3SG_tall_prod_bound_three s hre hT
  have cQ : |s.im| / 4 - 0.95 < ((Nat.floor (|s.im| / 4 - 0.95) + 1 : ℕ) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one _
  have cH : |s.im| / 2 - 0.95 < ((Nat.floor (|s.im| / 2 - 0.95) + 1 : ℕ) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one _
  have cN : |s.im| - 0.95 < ((Nat.floor (|s.im| - 0.95) + 1 : ℕ) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one _
  have dQ : |s.im| / 4 - 0.95 < ((Nat.floor (|s.im| / 4 - 0.95) : ℕ) : ℝ) + 1 := by
    have h := cQ
    rwa [Nat.cast_add, Nat.cast_one] at h
  have dH : |s.im| / 2 - 0.95 < ((Nat.floor (|s.im| / 2 - 0.95) : ℕ) : ℝ) + 1 := by
    have h := cH
    rwa [Nat.cast_add, Nat.cast_one] at h
  have dN : |s.im| - 0.95 < ((Nat.floor (|s.im| - 0.95) : ℕ) : ℝ) + 1 := by
    have h := cN
    rwa [Nat.cast_add, Nat.cast_one] at h
  have hnat : 4 * (Nat.floor (|s.im| / 4 - 0.95) + 1)
      + 2 * (Nat.floor (|s.im| / 2 - 0.95) + 1 - (Nat.floor (|s.im| / 4 - 0.95) + 1))
      + (Nat.floor (|s.im| - 0.95) + 1 - (Nat.floor (|s.im| / 2 - 0.95) + 1))
      = 2 * (Nat.floor (|s.im| / 4 - 0.95) + 1)
      + (Nat.floor (|s.im| / 2 - 0.95) + 1) + (Nat.floor (|s.im| - 0.95) + 1) := by
    have g1 := D3SG_floor_quarter_le |s.im| hT
    have g2 := D3SG_floor_half_le |s.im| (by linarith)
    omega
  have hE : 2 * |s.im| - 3.8 ≤ ((((4 * (Nat.floor (|s.im| / 4 - 0.95) + 1)
      + 2 * (Nat.floor (|s.im| / 2 - 0.95) + 1 - (Nat.floor (|s.im| / 4 - 0.95) + 1))
      + (Nat.floor (|s.im| - 0.95) + 1 - (Nat.floor (|s.im| / 2 - 0.95) + 1))) : ℕ)) : ℝ) := by
    rw [hnat]
    push_cast
    linarith [dQ, dH, dN]
  have hlog2 : (0 : ℝ) < Real.log 2 := lt_trans (by norm_num) D3SG_log_two_gt
  have hmul0 := mul_le_mul_of_nonneg_right hE hlog2.le
  have hmono : Real.exp (-((((4 * (Nat.floor (|s.im| / 4 - 0.95) + 1)
      + 2 * (Nat.floor (|s.im| / 2 - 0.95) + 1 - (Nat.floor (|s.im| / 4 - 0.95) + 1))
      + (Nat.floor (|s.im| - 0.95) + 1 - (Nat.floor (|s.im| / 2 - 0.95) + 1))) : ℕ)) : ℝ)
      * Real.log 2)
      ≤ Real.exp (-(2 * |s.im| - 3.8) * Real.log 2) :=
    Real.exp_le_exp.mpr (by linarith [hmul0])
  have hsplit : -(2 * |s.im| - 3.8) * Real.log 2
      = 3.8 * Real.log 2 + (-(2 * Real.log 2) * |s.im|) := by ring
  have hcap : Real.exp (3.8 * Real.log 2) ≤ 16 := by
    have hle : 3.8 * Real.log 2 ≤ 4 * Real.log 2 :=
      mul_le_mul_of_nonneg_right (by norm_num) hlog2.le
    rw [← D3SG_exp_four_log2]
    exact Real.exp_le_exp.mpr hle
  have hfin : (1.21 : ℝ) * Real.exp (-((((4 * (Nat.floor (|s.im| / 4 - 0.95) + 1)
      + 2 * (Nat.floor (|s.im| / 2 - 0.95) + 1 - (Nat.floor (|s.im| / 4 - 0.95) + 1))
      + (Nat.floor (|s.im| - 0.95) + 1 - (Nat.floor (|s.im| / 2 - 0.95) + 1))) : ℕ)) : ℝ)
      * Real.log 2)
      ≤ 25 * Real.exp (-(2 * Real.log 2) * |s.im|) := by
    have hbase : (1.21 : ℝ) * Real.exp (3.8 * Real.log 2) ≤ 25 := by
      calc (1.21 : ℝ) * Real.exp (3.8 * Real.log 2) ≤ 1.21 * 16 :=
          mul_le_mul_of_nonneg_left hcap (by norm_num)
        _ ≤ 25 := by norm_num
    calc (1.21 : ℝ) * Real.exp (-((((4 * (Nat.floor (|s.im| / 4 - 0.95) + 1)
        + 2 * (Nat.floor (|s.im| / 2 - 0.95) + 1 - (Nat.floor (|s.im| / 4 - 0.95) + 1))
        + (Nat.floor (|s.im| - 0.95) + 1 - (Nat.floor (|s.im| / 2 - 0.95) + 1))) : ℕ)) : ℝ)
        * Real.log 2)
        ≤ 1.21 * Real.exp (-(2 * |s.im| - 3.8) * Real.log 2) :=
          mul_le_mul_of_nonneg_left hmono (by norm_num)
      _ = 1.21 * (Real.exp (3.8 * Real.log 2)
          * Real.exp (-(2 * Real.log 2) * |s.im|)) := by
          rw [hsplit, Real.exp_add]
      _ = (1.21 * Real.exp (3.8 * Real.log 2))
          * Real.exp (-(2 * Real.log 2) * |s.im|) := by ring
      _ ≤ 25 * Real.exp (-(2 * Real.log 2) * |s.im|) :=
          mul_le_mul_of_nonneg_right hbase (Real.exp_pos _).le
  have h1' : ‖Complex.Gamma s‖ ^ 2 ≤ (1.21 : ℝ) * Real.exp
      (-((((4 * (Nat.floor (|s.im| / 4 - 0.95) + 1)
      + 2 * (Nat.floor (|s.im| / 2 - 0.95) + 1 - (Nat.floor (|s.im| / 4 - 0.95) + 1))
      + (Nat.floor (|s.im| - 0.95) + 1 - (Nat.floor (|s.im| / 2 - 0.95) + 1))) : ℕ)) : ℝ)
      * Real.log 2) := by
    rw [← D3SG_half_pow_exp]
    exact h1
  have hsq : ‖Complex.Gamma s‖ ^ 2
      ≤ (5 * Real.exp (-Real.log 2 * |s.im|)) ^ 2 := by
    rw [mul_pow, D3SG_exp_log2_sq, show (5 : ℝ) ^ 2 = 25 by norm_num]
    exact le_trans h1' hfin
  have hnn : (0 : ℝ) ≤ 5 * Real.exp (-Real.log 2 * |s.im|) := by positivity
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hnn] at hsqrt
  exact hsqrt

#print axioms D3SG_tall_three_tier

/-- Small-height global piece: `|T| ≤ 4 → ‖Γ‖ ≤ 18·exp(−log2·|T|)` on `Re = 0.95`. -/
theorem D3SG_small_height_four (s : ℂ) (hre : s.re = 0.95)
    (hT : |s.im| ≤ 4) :
    ‖Complex.Gamma s‖ ≤ 18 * Real.exp (-Real.log 2 * |s.im|) := by
  have hspos : (0 : ℝ) < s.re := by rw [hre]; norm_num
  have hdom : ‖Complex.Gamma s‖ ≤ Real.Gamma 0.95 := by
    have h := D3SG_Gamma_norm_le_real s hspos
    rwa [hre] at h
  have hlog2 : (0 : ℝ) < Real.log 2 := lt_trans (by norm_num) D3SG_log_two_gt
  have h4 : ((1 / 2 : ℝ) ^ 4) = Real.exp (-(4 : ℝ) * Real.log 2) := by
    have h := D3SG_half_pow_exp 4
    have hc : (((4 : ℕ)) : ℝ) = 4 := by norm_num
    rw [hc] at h
    exact h
  have hexp16 : Real.exp (-(4 : ℝ) * Real.log 2) = 1 / 16 := by
    rw [← h4]
    norm_num
  have hle : Real.log 2 * |s.im| ≤ Real.log 2 * 4 :=
    mul_le_mul_of_nonneg_left hT hlog2.le
  have harg : -(4 : ℝ) * Real.log 2 ≤ -Real.log 2 * |s.im| := by
    have e1 : -(4 : ℝ) * Real.log 2 = -(Real.log 2 * 4) := by ring
    have e2 : -Real.log 2 * |s.im| = -(Real.log 2 * |s.im|) := by ring
    rw [e1, e2]
    exact neg_le_neg hle
  have hmono : Real.exp (-(4 : ℝ) * Real.log 2)
      ≤ Real.exp (-Real.log 2 * |s.im|) := Real.exp_le_exp.mpr harg
  have hexp : (1.1 : ℝ) ≤ 18 * Real.exp (-Real.log 2 * |s.im|) := by
    calc (1.1 : ℝ) ≤ 18 * (1 / 16) := by norm_num
      _ = 18 * Real.exp (-(4 : ℝ) * Real.log 2) := by rw [hexp16]
      _ ≤ 18 * Real.exp (-Real.log 2 * |s.im|) :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)
  exact le_trans (le_trans hdom D3SG_Real_Gamma_095_le_one_one) hexp

#print axioms D3SG_small_height_four

/-- Global merge on `Re = 0.95`: `‖Γ‖ ≤ 18·exp(−log2·|Im|)` (`c = log 2`). -/
theorem D3SG_Gamma_line095_exp_decay_global (s : ℂ) (hre : s.re = 0.95) :
    ‖Complex.Gamma s‖ ≤ 18 * Real.exp (-Real.log 2 * |s.im|) := by
  by_cases hT : |s.im| ≤ 4
  · exact D3SG_small_height_four s hre hT
  · have hT4 : (4 : ℝ) ≤ |s.im| := le_of_not_ge hT
    have h1 := D3SG_tall_three_tier s hre hT4
    have hpos : (0 : ℝ) ≤ Real.exp (-Real.log 2 * |s.im|) :=
      (Real.exp_pos _).le
    have h518 : (5 : ℝ) * Real.exp (-Real.log 2 * |s.im|)
        ≤ 18 * Real.exp (-Real.log 2 * |s.im|) :=
      mul_le_mul_of_nonneg_right (by norm_num) hpos
    exact le_trans h1 h518

#print axioms D3SG_Gamma_line095_exp_decay_global

/-- Half-height count, `σ`-general (`σ ≤ 1`, `2 ≤ T`). -/
theorem D3SG_floor_half_le_sigma (σ T : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hT : 2 ≤ T) :
    Nat.floor (T / 2 - σ) + 1 ≤ Nat.floor (T - σ) + 1 := by
  have hnn : (0 : ℝ) ≤ T / 2 - σ := by linarith
  have hle : T / 2 - σ ≤ T - σ := by linarith
  have c : ((Nat.floor (T / 2 - σ) + 1 : ℕ) : ℝ)
      ≤ ((Nat.floor (T - σ) + 1 : ℕ) : ℝ) := by
    push_cast
    have a := Nat.floor_le hnn
    have b := (Nat.lt_floor_add_one (T - σ)).le
    linarith
  exact Nat.cast_le.mp c

#print axioms D3SG_floor_half_le_sigma

/-- Quarter-height count, `σ`-general (`σ ≤ 1`, `4 ≤ T`). -/
theorem D3SG_floor_quarter_le_sigma (σ T : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hT : 4 ≤ T) :
    Nat.floor (T / 4 - σ) + 1 ≤ Nat.floor (T / 2 - σ) + 1 := by
  have hnn : (0 : ℝ) ≤ T / 4 - σ := by linarith
  have hle : T / 4 - σ ≤ T / 2 - σ := by linarith
  have c : ((Nat.floor (T / 4 - σ) + 1 : ℕ) : ℝ)
      ≤ ((Nat.floor (T / 2 - σ) + 1 : ℕ) : ℝ) := by
    push_cast
    have a := Nat.floor_le hnn
    have b := (Nat.lt_floor_add_one (T / 2 - σ)).le
    linarith
  exact Nat.cast_le.mp c

#print axioms D3SG_floor_quarter_le_sigma

/-- Quarter-power product, `σ`-general (`σ ≤ 1`, `2 ≤ T`). -/
theorem D3SG_prod_quarter_pow_sigma (σ T : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hT : 2 ≤ T) :
    ∏ k ∈ Finset.range (Nat.floor (T / 2 - σ) + 1),
      ((σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2))
      ≤ (1 / 2) ^ (2 * (Nat.floor (T / 2 - σ) + 1)) := by
  have hTh : (0 : ℝ) ≤ T / 2 - σ := by linarith
  have h1 : ∀ k ∈ Finset.range (Nat.floor (T / 2 - σ) + 1),
      (σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2) ≤ 1 / 4 := by
    intro k hk
    apply D3SG_factor_le_quarter σ T hσ k
    have hkle : k ≤ Nat.floor (T / 2 - σ) :=
      Nat.lt_add_one_iff.mp (Finset.mem_range.mp hk)
    have hc : (k : ℝ) ≤ ((Nat.floor (T / 2 - σ) : ℕ) : ℝ) :=
      Nat.cast_le.mpr hkle
    have hf := Nat.floor_le hTh
    have hTnn : (0 : ℝ) ≤ T := by linarith
    rw [abs_of_nonneg hTnn]
    linarith
  have h := Finset.prod_le_prod
    (fun k _ => (D3SG_factor_mem_Icc σ T hσ k).1) h1
  rw [Finset.prod_const, Finset.card_range] at h
  have e : ((1 / 4 : ℝ)) ^ (Nat.floor (T / 2 - σ) + 1)
      = (1 / 2) ^ (2 * (Nat.floor (T / 2 - σ) + 1)) := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, ← pow_mul]
  rwa [e] at h

/-- Half-power product on the middle interval, `σ`-general. -/
theorem D3SG_prod_Ico_half_pow_sigma (σ T : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hT : 2 ≤ T) :
    ∏ k ∈ Finset.Ico (Nat.floor (T / 2 - σ) + 1) (Nat.floor (T - σ) + 1),
      ((σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2))
      ≤ (1 / 2) ^ (Nat.floor (T - σ) + 1 - (Nat.floor (T / 2 - σ) + 1)) := by
  have hT0 : (0 : ℝ) ≤ T - σ := by linarith
  have h1 : ∀ k ∈ Finset.Ico (Nat.floor (T / 2 - σ) + 1) (Nat.floor (T - σ) + 1),
      (σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2) ≤ 1 / 2 := by
    intro k hk
    apply D3SG_factor_le_half σ T hσ k
    have hlt : k < Nat.floor (T - σ) + 1 := (Finset.mem_Ico.mp hk).2
    have hkle : k ≤ Nat.floor (T - σ) := Nat.lt_add_one_iff.mp hlt
    have hc : (k : ℝ) ≤ ((Nat.floor (T - σ) : ℕ) : ℝ) := Nat.cast_le.mpr hkle
    have hf := Nat.floor_le hT0
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T)]
    linarith
  have h := Finset.prod_le_prod
    (fun k _ => (D3SG_factor_mem_Icc σ T hσ k).1) h1
  rwa [Finset.prod_const, Nat.card_Ico] at h

#print axioms D3SG_prod_quarter_pow_sigma

#print axioms D3SG_prod_Ico_half_pow_sigma

/-- Two-tier product, `σ`-general (`σ ≤ 1`, `2 ≤ T`). -/
theorem D3SG_prod_two_tier_sigma (σ T : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hT : 2 ≤ T) :
    ∏ k ∈ Finset.range (Nat.floor (T - σ) + 1),
      ((σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2))
      ≤ (1 / 2) ^ (Nat.floor (T / 2 - σ) + 1 + (Nat.floor (T - σ) + 1)) := by
  have hj : Nat.floor (T / 2 - σ) + 1 ≤ Nat.floor (T - σ) + 1 :=
    D3SG_floor_half_le_sigma σ T hσ hσ1 hT
  have hsplit : Nat.floor (T / 2 - σ) + 1
      + (Nat.floor (T - σ) + 1 - (Nat.floor (T / 2 - σ) + 1))
      = Nat.floor (T - σ) + 1 := Nat.add_sub_cancel' hj
  have hprod := Finset.prod_range_add
    (fun k => (σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2))
    (Nat.floor (T / 2 - σ) + 1)
    (Nat.floor (T - σ) + 1 - (Nat.floor (T / 2 - σ) + 1))
  rw [hsplit] at hprod
  rw [hprod]
  have hbig' := D3SG_prod_Ico_half_pow_sigma σ T hσ hσ1 hT
  rw [Finset.prod_Ico_eq_prod_range] at hbig'
  have hmul := mul_le_mul (D3SG_prod_quarter_pow_sigma σ T hσ hσ1 hT) hbig'
    (Finset.prod_nonneg (fun (k : ℕ) (_ : k ∈ Finset.range _) =>
      (D3SG_factor_mem_Icc σ T hσ (Nat.floor (T / 2 - σ) + 1 + k)).1))
    (by positivity)
  rw [← pow_add] at hmul
  have hexp : 2 * (Nat.floor (T / 2 - σ) + 1)
      + (Nat.floor (T - σ) + 1 - (Nat.floor (T / 2 - σ) + 1))
      = Nat.floor (T / 2 - σ) + 1 + (Nat.floor (T - σ) + 1) := by omega
  rwa [hexp] at hmul

#print axioms D3SG_prod_two_tier_sigma

/-- Squared tall-height bound, `σ`-general, capped by `M`. -/
theorem D3SG_tall_prod_bound_half_sigma (s : ℂ) (σ M : ℝ) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hre : s.re = σ) (hM : 0 ≤ M)
    (hcap : Real.Gamma σ ≤ M) (hT : 2 ≤ |s.im|) :
    ‖Complex.Gamma s‖ ^ 2
      ≤ M ^ 2 * (1 / 2) ^ (Nat.floor (|s.im| / 2 - σ) + 1
        + (Nat.floor (|s.im| - σ) + 1)) := by
  have hspos : (0 : ℝ) < s.re := by rw [hre]; exact hσ
  have hprod := D3SG_sq_prod hspos (Nat.floor |s.im| + 2)
  rw [hre, ← sq_abs s.im] at hprod
  have hsub : Finset.range (Nat.floor (|s.im| - σ) + 1)
      ⊆ Finset.range (Nat.floor |s.im| + 2) := by
    intro (x : ℕ) (hx : x ∈ Finset.range _)
    rw [Finset.mem_range] at hx ⊢
    exact lt_of_lt_of_le hx (D3SG_floor_count_sigma σ |s.im| hσ.le)
  have hPsub : ∏ k ∈ Finset.range (Nat.floor |s.im| + 2),
      ((σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + |s.im| ^ 2))
      ≤ ∏ k ∈ Finset.range (Nat.floor (|s.im| - σ) + 1),
      ((σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + |s.im| ^ 2)) :=
    Finset.prod_le_prod_of_subset_of_le_one
      hsub
      (fun (k : ℕ) (_ : k ∈ Finset.range _) =>
        (D3SG_factor_mem_Icc σ _ hσ k).1)
      (fun (k : ℕ) (_ : k ∈ Finset.range _) (_ : k ∉ Finset.range _) =>
        (D3SG_factor_mem_Icc σ _ hσ k).2)
  have hP := le_trans hPsub (D3SG_prod_two_tier_sigma σ |s.im| hσ hσ1 hT)
  have hcap2 : Real.Gamma σ ^ 2 ≤ M ^ 2 :=
    pow_le_pow_left₀ (le_of_lt (Real.Gamma_pos_of_pos hσ)) hcap 2
  exact le_trans hprod (mul_le_mul hcap2 hP
    (Finset.prod_nonneg
      (fun (k : ℕ) (_ : k ∈ Finset.range _) =>
        (D3SG_factor_mem_Icc σ _ hσ k).1))
    (by positivity))

#print axioms D3SG_tall_prod_bound_half_sigma

/-- Small-height bound, `σ`-general, capped by `M`. -/
theorem D3SG_small_height_sigma (s : ℂ) (σ M : ℝ) (hσ : 0 < σ)
    (hre : s.re = σ) (hM : 0 ≤ M) (hcap : Real.Gamma σ ≤ M)
    (hT : |s.im| ≤ 2) :
    ‖Complex.Gamma s‖ ≤ 3 * M * Real.exp (-(1 / 2) * |s.im|) := by
  have hspos : (0 : ℝ) < s.re := by rw [hre]; exact hσ
  have hdom : ‖Complex.Gamma s‖ ≤ Real.Gamma σ := by
    have h := D3SG_Gamma_norm_le_real s hspos
    rwa [hre] at h
  have hub : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hbase : (1 : ℝ) ≤ 3 * (Real.exp 1)⁻¹ := by
    rw [le_mul_inv_iff₀ hpos]
    linarith [hub]
  have hmono : Real.exp (-1) ≤ Real.exp (-(1 / 2) * |s.im|) := by
    apply Real.exp_le_exp.mpr
    have habs := abs_nonneg s.im
    linarith
  have hinv : Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
  have hexp : (1 : ℝ) ≤ 3 * Real.exp (-(1 / 2) * |s.im|) := by
    calc (1 : ℝ) ≤ 3 * (Real.exp 1)⁻¹ := hbase
      _ = 3 * Real.exp (-1) := by rw [hinv]
      _ ≤ 3 * Real.exp (-(1 / 2) * |s.im|) :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)
  have hMle : Real.Gamma σ ≤ 3 * M * Real.exp (-(1 / 2) * |s.im|) := by
    calc Real.Gamma σ ≤ M := hcap
      _ = M * 1 := by ring
      _ ≤ M * (3 * Real.exp (-(1 / 2) * |s.im|)) :=
        mul_le_mul_of_nonneg_left hexp hM
      _ = 3 * M * Real.exp (-(1 / 2) * |s.im|) := by ring
  exact le_trans hdom hMle

#print axioms D3SG_small_height_sigma
/-- Stirling decay, `σ`-general: `‖Γ‖ ≤ 3·M·exp(−|Im|/2)` for `0 < σ ≤ 1`. -/
theorem D3SG_decay_sigma (s : ℂ) (σ M : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hre : s.re = σ) (hM : 0 ≤ M) (hcap : Real.Gamma σ ≤ M) :
    ‖Complex.Gamma s‖ ≤ 3 * M * Real.exp (-(1 / 2) * |s.im|) := by
  by_cases hT : |s.im| ≤ 2
  · exact D3SG_small_height_sigma s σ M hσ hre hM hcap hT
  · have hT2 : (2 : ℝ) ≤ |s.im| := le_of_not_ge hT
    have h1 := D3SG_tall_prod_bound_half_sigma s σ M hσ hσ1 hre hM hcap hT2
    have hMle : |s.im| ≤ (2 / 3) * ((((Nat.floor (|s.im| / 2 - σ) + 1 : ℕ) : ℝ)
        + ((Nat.floor (|s.im| - σ) + 1 : ℕ) : ℝ)) + 2) := by
      have c1 : |s.im| / 2 - σ < ((Nat.floor (|s.im| / 2 - σ) + 1 : ℕ) : ℝ) := by
        push_cast
        exact Nat.lt_floor_add_one _
      have c2 : |s.im| - σ < ((Nat.floor (|s.im| - σ) + 1 : ℕ) : ℝ) := by
        push_cast
        exact Nat.lt_floor_add_one _
      linarith [hσ1]
    have hkey : |s.im| ≤ ((((Nat.floor (|s.im| / 2 - σ) + 1 : ℕ) : ℝ)
        + ((Nat.floor (|s.im| - σ) + 1 : ℕ) : ℝ)) + 2) * Real.log 2 := by
      have hnn : (0 : ℝ) ≤ (((Nat.floor (|s.im| / 2 - σ) + 1 : ℕ) : ℝ)
          + ((Nat.floor (|s.im| - σ) + 1 : ℕ) : ℝ)) + 2 := by
        have n1 := Nat.cast_nonneg (α := ℝ) (Nat.floor (|s.im| / 2 - σ) + 1)
        have n2 := Nat.cast_nonneg (α := ℝ) (Nat.floor (|s.im| - σ) + 1)
        linarith
      calc |s.im| ≤ (2 / 3) * _ := hMle
        _ ≤ _ * Real.log 2 := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left D3SG_log_two_gt.le hnn
    have hmono : Real.exp (-(((Nat.floor (|s.im| / 2 - σ) + 1 : ℕ) : ℝ)
        + ((Nat.floor (|s.im| - σ) + 1 : ℕ) : ℝ)) * Real.log 2)
        ≤ Real.exp (2 * Real.log 2 + -|s.im|) := by
      apply Real.exp_le_exp.mpr
      linarith [hkey]
    have hfin : M ^ 2
        * Real.exp (-(((Nat.floor (|s.im| / 2 - σ) + 1 : ℕ) : ℝ)
          + ((Nat.floor (|s.im| - σ) + 1 : ℕ) : ℝ)) * Real.log 2)
        ≤ (3 * M) ^ 2 * Real.exp (-|s.im|) := by
      have hle : M ^ 2 * Real.exp (2 * Real.log 2 + -|s.im|)
          ≤ (3 * M) ^ 2 * Real.exp (-|s.im|) := by
        rw [Real.exp_add, ← D3SG_four_exp]
        have hnn : (0 : ℝ) ≤ M ^ 2 * Real.exp (-|s.im|) := by positivity
        have e : (3 * M) ^ 2 = 9 * M ^ 2 := by ring
        rw [e]
        calc M ^ 2 * (4 * Real.exp (-|s.im|))
            = 4 * (M ^ 2 * Real.exp (-|s.im|)) := by ring
          _ ≤ 9 * (M ^ 2 * Real.exp (-|s.im|)) := by linarith [hnn]
          _ = 9 * M ^ 2 * Real.exp (-|s.im|) := by ring
      exact le_trans
        (mul_le_mul_of_nonneg_left hmono (by positivity)) hle
    have hsq : ‖Complex.Gamma s‖ ^ 2
        ≤ (3 * M * Real.exp (-(1 / 2) * |s.im|)) ^ 2 := by
      rw [mul_pow, D3SG_exp_half_sq]
      have h1' := h1
      rw [D3SG_half_pow_exp, Nat.cast_add] at h1'
      exact le_trans h1' hfin
    have hsqrt := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 3 * M * Real.exp (-(1 / 2) * |s.im|))] at hsqrt
    exact hsqrt
#print axioms D3SG_decay_sigma
