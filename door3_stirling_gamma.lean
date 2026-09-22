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

/-- Cap `Γ ≤ 1` on `[1,2]` via convexity (`Γ 1 = Γ 2 = 1`). -/
theorem D3SG_Gamma_one_two_le_one (x : ℝ) (h1 : 1 ≤ x) (h2 : x ≤ 2) :
    Real.Gamma x ≤ 1 := by
  have ha : (0 : ℝ) ≤ 2 - x := by linarith
  have hb : (0 : ℝ) ≤ x - 1 := by linarith
  have hab : ((2 : ℝ) - x) + (x - 1) = 1 := by ring
  have h1mem : (1 : ℝ) ∈ Set.Ioi 0 := Set.mem_Ioi.mpr (by norm_num)
  have h2mem : (2 : ℝ) ∈ Set.Ioi 0 := Set.mem_Ioi.mpr (by norm_num)
  have hJ := Real.convexOn_Gamma.2 h1mem h2mem ha hb hab
  simp only [smul_eq_mul] at hJ
  have hpt : ((2 : ℝ) - x) * 1 + (x - 1) * 2 = x := by ring
  rw [hpt, Real.Gamma_one, Real.Gamma_two] at hJ
  have he : ((2 : ℝ) - x) * 1 + (x - 1) * 1 = 1 := by ring
  exact le_trans hJ (le_of_eq he)

/-- Uniform cap `Γ σ ≤ 20` on `[0.05,0.95]` (shift + `[1,2]` cap). -/
theorem D3SG_Real_Gamma_uniform_005_095_le_20 (σ : ℝ)
    (hlo : 0.05 ≤ σ) (hhi : σ ≤ 0.95) :
    Real.Gamma σ ≤ 20 := by
  have hpos : (0 : ℝ) < σ := by linarith
  have hne : σ ≠ 0 := ne_of_gt hpos
  have hshift : Real.Gamma (σ + 1) = σ * Real.Gamma σ :=
    Real.Gamma_add_one hne
  have h1 : (1 : ℝ) ≤ σ + 1 := by linarith
  have h2 : σ + 1 ≤ 2 := by linarith
  have hcap : Real.Gamma (σ + 1) ≤ 1 :=
    D3SG_Gamma_one_two_le_one (σ + 1) h1 h2
  have hdiv : Real.Gamma σ = Real.Gamma (σ + 1) / σ := by
    rw [eq_div_iff_mul_eq hne]
    rw [hshift]
    ring
  have h1div : Real.Gamma (σ + 1) / σ ≤ 1 / σ := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hcap (inv_nonneg.mpr (le_of_lt hpos))
  have h20 : (1 : ℝ) / σ ≤ 20 := by
    rw [div_le_iff₀ hpos]
    linarith
  calc Real.Gamma σ = Real.Gamma (σ + 1) / σ := hdiv
    _ ≤ 1 / σ := h1div
    _ ≤ 20 := h20

#print axioms D3SG_Gamma_one_two_le_one
#print axioms D3SG_Real_Gamma_uniform_005_095_le_20

/-- Tier-C decay on strip `Re ∈ [0.05,0.95]`: `‖Γ s‖ ≤ 60·exp(−|Im|/2)`. -/
theorem D3SG_TierC_gamma_rect (s : ℂ)
    (hlo : 0.05 ≤ s.re) (hhi : s.re ≤ 0.95) :
    ‖Complex.Gamma s‖ ≤ 60 * Real.exp (-(1 / 2) * |s.im|) := by
  have hpos : (0 : ℝ) < s.re := by linarith
  have hle1 : s.re ≤ 1 := by linarith
  have hcap : Real.Gamma s.re ≤ 20 :=
    D3SG_Real_Gamma_uniform_005_095_le_20 s.re hlo hhi
  have h := D3SG_decay_sigma s s.re 20 hpos hle1 rfl (by norm_num) hcap
  have e : (3 : ℝ) * 20 = 60 := by norm_num
  calc ‖Complex.Gamma s‖ ≤ 3 * 20 * Real.exp (-(1 / 2) * |s.im|) := h
    _ = 60 * Real.exp (-(1 / 2) * |s.im|) := by rw [e]

#print axioms D3SG_TierC_gamma_rect

/-- Uniform sliver cap `Γ σ ≤ 200` on `[0.005,0.05]` (shift + `[1,2]` cap). -/
theorem D3SG_Real_Gamma_uniform_0005_005_le_200 (σ : ℝ)
    (hlo : 0.005 ≤ σ) (hhi : σ ≤ 0.05) :
    Real.Gamma σ ≤ 200 := by
  have hpos : (0 : ℝ) < σ := by linarith
  have hne : σ ≠ 0 := ne_of_gt hpos
  have hshift : Real.Gamma (σ + 1) = σ * Real.Gamma σ :=
    Real.Gamma_add_one hne
  have h1 : (1 : ℝ) ≤ σ + 1 := by linarith
  have h2 : σ + 1 ≤ 2 := by linarith
  have hcap : Real.Gamma (σ + 1) ≤ 1 :=
    D3SG_Gamma_one_two_le_one (σ + 1) h1 h2
  have hdiv : Real.Gamma σ = Real.Gamma (σ + 1) / σ := by
    rw [eq_div_iff_mul_eq hne]
    rw [hshift]
    ring
  have h1div : Real.Gamma (σ + 1) / σ ≤ 1 / σ := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hcap (inv_nonneg.mpr (le_of_lt hpos))
  have h200 : (1 : ℝ) / σ ≤ 200 := by
    rw [div_le_iff₀ hpos]
    linarith
  calc Real.Gamma σ = Real.Gamma (σ + 1) / σ := hdiv
    _ ≤ 1 / σ := h1div
    _ ≤ 200 := h200

#print axioms D3SG_Real_Gamma_uniform_0005_005_le_200

/-- Tier-C decay on sliver `Re ∈ [0.005,0.05]`: `‖Γ s‖ ≤ 600·exp(−|Im|/2)`. -/
theorem D3SG_TierC_gamma_rect_sliver (s : ℂ)
    (hlo : 0.005 ≤ s.re) (hhi : s.re ≤ 0.05) :
    ‖Complex.Gamma s‖ ≤ 600 * Real.exp (-(1 / 2) * |s.im|) := by
  have hpos : (0 : ℝ) < s.re := by linarith
  have hle1 : s.re ≤ 1 := by linarith
  have hcap : Real.Gamma s.re ≤ 200 :=
    D3SG_Real_Gamma_uniform_0005_005_le_200 s.re hlo hhi
  have h := D3SG_decay_sigma s s.re 200 (by linarith) (by linarith) rfl (by norm_num) hcap
  have e : (3 : ℝ) * 200 = 600 := by norm_num
  calc ‖Complex.Gamma s‖ ≤ 3 * 200 * Real.exp (-(1 / 2) * |s.im|) := h
    _ = 600 * Real.exp (-(1 / 2) * |s.im|) := by rw [e]

#print axioms D3SG_TierC_gamma_rect_sliver

/-- Tier-C wide join on `Re ∈ [0.005,0.95]`: `‖Γ s‖ ≤ 600·exp(−|Im|/2)`. -/
theorem D3SG_TierC_gamma_wide (s : ℂ)
    (hlo : 0.005 ≤ s.re) (hhi : s.re ≤ 0.95) :
    ‖Complex.Gamma s‖ ≤ 600 * Real.exp (-(1 / 2) * |s.im|) := by
  by_cases hc : s.re ≤ 0.05
  · exact D3SG_TierC_gamma_rect_sliver s hlo hc
  · have h05 : (0.05 : ℝ) ≤ s.re := le_of_not_ge hc
    have h60 : ‖Complex.Gamma s‖ ≤ 60 * Real.exp (-(1 / 2) * |s.im|) :=
      D3SG_TierC_gamma_rect s h05 hhi
    have hle : (60 : ℝ) * Real.exp (-(1 / 2) * |s.im|)
        ≤ 600 * Real.exp (-(1 / 2) * |s.im|) :=
      mul_le_mul_of_nonneg_right (by norm_num : (60 : ℝ) ≤ 600)
        (le_of_lt (Real.exp_pos _))
    exact le_trans h60 hle

#print axioms D3SG_TierC_gamma_wide

/-!
# Door-3 chi·reflected sup-product (write-only append; report-and-stop).

Consumer: `door3_cutR10_ballsup.lean:cutR10_hFE_of_chi_and_middle` needs, for
`t.re ∈ [-1.06, 3/2]` and `t.im ∈ [8.44, 11.56]`, chi cap `‖chi(1-t)‖ ≤ 3`
times middle reflected cap `‖zeta(1-t)‖ ≤ 2`, giving `‖zeta t‖ ≤ 3 * 2`.
(Box note: the brief wrote `t.re ∈ [-1.06,2.06]`; the exact consumer statement
uses `t.re ≤ 3 / 2`, hence `(1-t).re ∈ [-0.50,2.06]`, matching `hMid` exactly.)

Route: banked Tier-C decay lane (`D3SG_TierC_gamma_wide`, rate `c = 1 / 2`) plus
recurrence shift paying explicit polynomial factors. The `π / 2` rate needs the
open full-tail integral route (`door3_gamma_pi2.lean`: dyadic tiers cap at
`c ≈ 0.87`); with banked `c = 1 / 2` the cos growth `exp (π * |Im| / 2)` cannot
cancel, so the honest closed product below is exp-scale with explicit gap vs 6.
Sin-form remark: Mathlib FE at `1 - s` turns the cos-form below into the
classical `χ(t) = 2 ^ t * π ^ (t - 1) * sin (π * t / 2) * Γ (1 - t)`; the product
is stated at `(1 - t)` in cos-form, which is what the bridge consumes.

Banked here (full proofs, explicit binders, small numerals only):
* `D3SG_CHI_cos_le_exp_abs_im`, `D3SG_CHI_sin_le_exp_abs_im` (generic trig);
* `D3SG_CHI_sin_box_le` (sin-upper `≤ exp 19` on the box);
* `D3SG_CHI_norm_le` (symbolic chi upper);
* real caps `D3SG_CHI_Real_Gamma_095_1_le_two`, `D3SG_CHI_Real_Gamma_1_206_le_two`;
* `D3SG_CHI_Gamma_upper_mid/high/neg`, `D3SG_CHI_Gamma_refl_box_le` (`≤ 600`);
* `D3SG_CHI_cpow_box_le7`, `D3SG_CHI_arg_im_le19`, `D3SG_CHI_cos_box_le`;
* `D3SG_CHI_box_le` (`‖chi(1-t)‖ ≤ 2 * 7 * 600 * exp 19`);
* `D3SG_chi_refl_product_le` (conditional sup-product; ONE assembly attempt).
Honest account: at `Z = 2` this closes `(2 * 7 * 600 * exp 19) * 2 ≈ 3e12`;
target `6` is NOT closed; gap factor `≈ 5e11`. Missing pieces: middle-strip
`Z = 2` (Euler covers only the `t.re ≤ -1` sliver) and the `π / 2` Gamma tail.
-/

/-- Elementary complex-cosine upper: `‖cos z‖ ≤ exp |Im z|` (via `Complex.two_cos`;
mirrors `zeta_rigorous.norm_cos_le_exp_abs_im`). -/
theorem D3SG_CHI_cos_le_exp_abs_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h2 : (2 : ℂ) * Complex.cos z
      = Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I) :=
    Complex.two_cos z
  have e1 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have e2 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hcos : Complex.cos z
      = (Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)) / 2 := by
    have h2ne : (2 : ℂ) ≠ 0 := by norm_num
    rw [eq_div_iff h2ne]
    linear_combination h2
  have hle : ‖Complex.cos z‖ ≤ (Real.exp (-z.im) + Real.exp z.im) / 2 := by
    rw [hcos, norm_div]
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2n, ← e1, ← e2]
    exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
  have hmax : (Real.exp (-z.im) + Real.exp z.im) / 2 ≤ Real.exp |z.im| := by
    have g1 : Real.exp (-z.im) ≤ Real.exp |z.im| :=
      Real.exp_le_exp.mpr (neg_le_abs _)
    have g2 : Real.exp z.im ≤ Real.exp |z.im| :=
      Real.exp_le_exp.mpr (le_abs_self _)
    linarith
  exact le_trans hle hmax

#print axioms D3SG_CHI_cos_le_exp_abs_im

/-- Elementary complex-sine upper: `‖sin w‖ ≤ exp |Im w|` (via `Complex.sin`;
mirrors `RowFE_norm_sin_le`). -/
theorem D3SG_CHI_sin_le_exp_abs_im (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
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
  have e1 : Real.exp w.im ≤ Real.exp |w.im| :=
    Real.exp_le_exp.mpr (le_abs_self _)
  have e2 : Real.exp (-w.im) ≤ Real.exp |w.im| := by
    apply Real.exp_le_exp.mpr
    have hnb : -w.im ≤ |w.im| := neg_le_abs _
    exact hnb
  linarith

#print axioms D3SG_CHI_sin_le_exp_abs_im

/-- Local FE chi factor, same shape as `cutR10_chiFE` / `zetaChi`
(`chi(s) = 2 * (2*pi)^(-s) * Gamma s * cos (pi * s / 2)`; mirrored locally,
no import of ballsup). -/
noncomputable def D3SG_chiFE (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
    Complex.cos ((Real.pi : ℂ) * s / 2)

/-- Chi-factor upper with only `‖Γ s‖` symbolic (cpow exact-norm + cos bound;
mirrors `zeta_rigorous.zetaChi_norm_le`). -/
theorem D3SG_CHI_norm_le (s : ℂ) :
    ‖D3SG_chiFE s‖ ≤ 2 * (2 * Real.pi) ^ (-s.re) * ‖Complex.Gamma s‖
      * Real.exp |(((Real.pi : ℂ)) * s / 2).im| := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  have hcast : (2 * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ)) : ℂ) := by
    push_cast
    ring
  have hcos := D3SG_CHI_cos_le_exp_abs_im (((Real.pi : ℂ)) * s / 2)
  have e2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hrnn : (0 : ℝ) ≤ (2 * Real.pi) ^ (-s.re) :=
    Real.rpow_nonneg (le_of_lt h2pi) _
  have hgnn : (0 : ℝ) ≤ ‖Complex.Gamma s‖ := norm_nonneg _
  unfold D3SG_chiFE
  simp only [norm_mul, e2]
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos h2pi (-s), Complex.neg_re]
  exact mul_le_mul_of_nonneg_left hcos (by positivity)

#print axioms D3SG_CHI_norm_le

/-- Chi-argument imaginary part at `1 - t` (mirrors `zeta_rigorous.chi_arg_im_eq`). -/
theorem D3SG_CHI_arg_im_eq (t : ℂ) :
    ((((Real.pi : ℂ)) * (1 - t) / 2)).im = -(Real.pi * t.im / 2) := by
  have harg : ((Real.pi : ℂ) * (1 - t) / 2) = (((Real.pi / 2 : ℝ)) : ℂ) * (1 - t) := by
    push_cast
    ring
  rw [harg]
  have him : ((((Real.pi / 2 : ℝ)) : ℂ) * (1 - t)).im
      = (Real.pi / 2) * (1 - t).im := by
    simp [Complex.mul_im]
  have him2 : (1 - t).im = -t.im := by simp
  rw [him, him2]
  ring

#print axioms D3SG_CHI_arg_im_eq

/-- Sine-argument imaginary part at `t`
(mirrors `R02_D3_chiArg_im_eq_direct`). -/
theorem D3SG_CHI_sin_arg_im_eq (t : ℂ) :
    ((((Real.pi : ℂ)) * t / 2)).im = Real.pi * t.im / 2 := by
  have harg : ((Real.pi : ℂ) * t / 2) = (((Real.pi / 2 : ℝ)) : ℂ) * t := by
    push_cast
    ring
  rw [harg]
  have him : ((((Real.pi / 2 : ℝ)) : ℂ) * t).im = (Real.pi / 2) * t.im := by
    simp [Complex.mul_im]
  rw [him]
  ring

#print axioms D3SG_CHI_sin_arg_im_eq

/-- Real cap `Γ x ≤ 2` on `[0.95,1]` (shift into the banked `[1,2]` cap). -/
theorem D3SG_CHI_Real_Gamma_095_1_le_two (x : ℝ)
    (hlo : 0.95 ≤ x) (hhi : x ≤ 1) :
    Real.Gamma x ≤ 2 := by
  have hpos : (0 : ℝ) < x := by linarith
  have hne : x ≠ 0 := ne_of_gt hpos
  have hshift : Real.Gamma (x + 1) = x * Real.Gamma x :=
    Real.Gamma_add_one hne
  have h1 : (1 : ℝ) ≤ x + 1 := by linarith
  have h2 : x + 1 ≤ 2 := by linarith
  have hcap : Real.Gamma (x + 1) ≤ 1 :=
    D3SG_Gamma_one_two_le_one (x + 1) h1 h2
  have hdiv : Real.Gamma x = Real.Gamma (x + 1) / x := by
    rw [eq_div_iff_mul_eq hne]
    rw [hshift]
    ring
  have h1div : Real.Gamma (x + 1) / x ≤ 1 / x := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hcap (inv_nonneg.mpr (le_of_lt hpos))
  have h2b : (1 : ℝ) / x ≤ 2 := by
    rw [div_le_iff₀ hpos]
    linarith
  calc Real.Gamma x = Real.Gamma (x + 1) / x := hdiv
    _ ≤ 1 / x := h1div
    _ ≤ 2 := h2b

#print axioms D3SG_CHI_Real_Gamma_095_1_le_two

/-- Real cap `Γ x ≤ 2` on `[1,2.06]` (banked `[1,2]` cap + one shift). -/
theorem D3SG_CHI_Real_Gamma_1_206_le_two (x : ℝ)
    (hlo : 1 ≤ x) (hhi : x ≤ 2.06) :
    Real.Gamma x ≤ 2 := by
  by_cases h2 : x ≤ 2
  · have h := D3SG_Gamma_one_two_le_one x hlo h2
    linarith
  · have h2lt : (2 : ℝ) < x := by linarith
    have hne : x - 1 ≠ 0 := by
      have hpos1 : (0 : ℝ) < x - 1 := by linarith
      exact ne_of_gt hpos1
    have hshift := Real.Gamma_add_one hne
    have heq : (x - 1) + 1 = x := by ring
    rw [heq] at hshift
    have hg : Real.Gamma (x - 1) ≤ 1 :=
      D3SG_Gamma_one_two_le_one (x - 1) (by linarith) (by linarith)
    rw [hshift]
    calc (x - 1) * Real.Gamma (x - 1) ≤ (x - 1) * 1 :=
          mul_le_mul_of_nonneg_left hg (by linarith)
      _ = x - 1 := by ring
      _ ≤ 2 := by linarith

#print axioms D3SG_CHI_Real_Gamma_1_206_le_two

/-- Gamma numeral cap `‖Γ w‖ ≤ 600` on `Re ∈ [0.005,0.95]`
(banked `D3SG_TierC_gamma_wide` with `exp ≤ 1`). -/
theorem D3SG_CHI_Gamma_upper_mid (w : ℂ)
    (hlo : 0.005 ≤ w.re) (hhi : w.re ≤ 0.95) :
    ‖Complex.Gamma w‖ ≤ 600 := by
  have hT := D3SG_TierC_gamma_wide w hlo hhi
  have he1 : Real.exp (-(1 / 2) * |w.im|) ≤ 1 := by
    have hle : Real.exp (-(1 / 2) * |w.im|) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr (by
        have hnn : (0 : ℝ) ≤ (1 / 2) * |w.im| :=
          mul_nonneg (by norm_num) (abs_nonneg _)
        linarith)
    rw [Real.exp_zero] at hle
    exact hle
  have h := mul_le_mul_of_nonneg_left he1 (by norm_num : (0 : ℝ) ≤ 600)
  rw [mul_one] at h
  exact le_trans hT h

#print axioms D3SG_CHI_Gamma_upper_mid

/-- Gamma numeral cap `‖Γ w‖ ≤ 2` on `Re ∈ (0.95,2.06]`
(integral domination + real caps). -/
theorem D3SG_CHI_Gamma_upper_high (w : ℂ)
    (hlo : 0.95 < w.re) (hhi : w.re ≤ 2.06) :
    ‖Complex.Gamma w‖ ≤ 2 := by
  have hpos : (0 : ℝ) < w.re := by linarith
  have hdom : ‖Complex.Gamma w‖ ≤ Real.Gamma w.re :=
    D3SG_Gamma_norm_le_real w hpos
  by_cases h1 : w.re ≤ 1
  · have h := D3SG_CHI_Real_Gamma_095_1_le_two w.re (by linarith) h1
    exact le_trans hdom h
  · have h1lt : (1 : ℝ) ≤ w.re := by linarith
    have h := D3SG_CHI_Real_Gamma_1_206_le_two w.re h1lt hhi
    exact le_trans hdom h

#print axioms D3SG_CHI_Gamma_upper_high

/-- Gamma numeral cap `‖Γ w‖ ≤ 600` on `Re ∈ [-0.50,0.005)`, `8.44 ≤ |Im|`
(shift `Γ(w+1) = w·Γ(w)` up into the banked lane, paying `‖w‖ ≥ 1`;
the in-file `D3SG_gamma_shift_norm` needs `0 < Re`, so the `n = 1` step is
reproved here from `Complex.Gamma_add_one` at `w ≠ 0`). -/
theorem D3SG_CHI_Gamma_upper_neg (w : ℂ)
    (hlo : -0.50 ≤ w.re) (hhi : w.re < 0.005)
    (him : 8.44 ≤ |w.im|) :
    ‖Complex.Gamma w‖ ≤ 600 := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_im, abs_zero] at him
    norm_num at him
  have hG : Complex.Gamma (w + 1) = w * Complex.Gamma w :=
    Complex.Gamma_add_one w hw0
  have hGn : ‖Complex.Gamma (w + 1)‖ = ‖w‖ * ‖Complex.Gamma w‖ := by
    rw [hG, norm_mul]
  have hw1 : (1 : ℝ) ≤ ‖w‖ := by
    have h := Complex.abs_im_le_norm w
    linarith
  have hle : ‖Complex.Gamma w‖ ≤ ‖w‖ * ‖Complex.Gamma w‖ :=
    le_mul_of_one_le_left (norm_nonneg _) hw1
  rw [← hGn] at hle
  have hre1 : (0.50 : ℝ) ≤ (w + 1).re := by
    have heq : (w + 1).re = w.re + 1 := by simp
    rw [heq]
    linarith
  have hre2 : (w + 1).re ≤ 1.005 := by
    have heq : (w + 1).re = w.re + 1 := by simp
    rw [heq]
    linarith
  by_cases hmid : (w + 1).re ≤ 0.95
  · have hcap := D3SG_CHI_Gamma_upper_mid (w + 1) (by linarith) hmid
    exact le_trans hle hcap
  · have hlt : (0.95 : ℝ) < (w + 1).re := by linarith
    have hcap := D3SG_CHI_Gamma_upper_high (w + 1) hlt (by linarith)
    have h2le : ‖Complex.Gamma (w + 1)‖ ≤ 600 := le_trans hcap (by norm_num)
    exact le_trans hle h2le

#print axioms D3SG_CHI_Gamma_upper_neg

/-- Uniform Gamma cap `‖Γ(1-t)‖ ≤ 600` on the box
(`(1-t).re ∈ [-0.50,2.06]`; Gamma-tail core at banked rate `c = 1 / 2`). -/
theorem D3SG_CHI_Gamma_refl_box_le (t : ℂ)
    (hlo : -1.06 ≤ t.re) (hhi : t.re ≤ 3 / 2)
    (hilo : 8.44 ≤ t.im) (hihi : t.im ≤ 11.56) :
    ‖Complex.Gamma (1 - t)‖ ≤ 600 := by
  have hre1 : (-0.50 : ℝ) ≤ (1 - t).re := by
    have heq : (1 - t).re = 1 - t.re := by simp
    rw [heq]
    linarith
  have hre2 : (1 - t).re ≤ (2.06 : ℝ) := by
    have heq : (1 - t).re = 1 - t.re := by simp
    rw [heq]
    linarith
  have him_eq : (1 - t).im = -t.im := by
    rw [Complex.sub_im, Complex.one_im, zero_sub]
  have habs : (8.44 : ℝ) ≤ |(1 - t).im| := by
    rw [him_eq, abs_neg, abs_of_nonneg (by linarith)]
    linarith
  by_cases hneg : (1 - t).re < 0.005
  · exact D3SG_CHI_Gamma_upper_neg (1 - t) hre1 hneg habs
  · have hlo_mid : (0.005 : ℝ) ≤ (1 - t).re := by linarith
    by_cases hmid : (1 - t).re ≤ 0.95
    · exact D3SG_CHI_Gamma_upper_mid (1 - t) hlo_mid hmid
    · have hlt : (0.95 : ℝ) < (1 - t).re := by linarith
      exact le_trans (D3SG_CHI_Gamma_upper_high (1 - t) hlt hre2) (by norm_num)

#print axioms D3SG_CHI_Gamma_refl_box_le

/-- Chi-argument imaginary part on the box is `≤ 19`
(`π < 3.1416`, `|Im| ≤ 12`). -/
theorem D3SG_CHI_arg_im_le19 (t : ℂ)
    (hilo : 8.44 ≤ t.im) (hihi : t.im ≤ 11.56) :
    |((((Real.pi : ℂ)) * (1 - t) / 2)).im| ≤ 19 := by
  rw [D3SG_CHI_arg_im_eq, abs_neg]
  have habs : |t.im| ≤ 12 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have e : |Real.pi * t.im / 2| = (Real.pi / 2) * |t.im| := by
    rw [show Real.pi * t.im / 2 = (Real.pi / 2) * t.im by ring, abs_mul,
      abs_of_nonneg (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]
  rw [e]
  have h2 := mul_le_mul (le_of_lt (by linarith : Real.pi / 2 < 3.1416 / 2)) habs
    (abs_nonneg _) (show (0 : ℝ) ≤ 3.1416 / 2 by norm_num)
  have hnum : (3.1416 / 2 : ℝ) * 12 ≤ 19 := by norm_num
  linarith

#print axioms D3SG_CHI_arg_im_le19

/-- Cos chi-factor on the box is `≤ exp 19`. -/
theorem D3SG_CHI_cos_box_le (t : ℂ)
    (hilo : 8.44 ≤ t.im) (hihi : t.im ≤ 11.56) :
    ‖Complex.cos ((Real.pi : ℂ) * (1 - t) / 2)‖ ≤ Real.exp 19 := by
  exact le_trans (D3SG_CHI_cos_le_exp_abs_im _)
    (Real.exp_le_exp.mpr (D3SG_CHI_arg_im_le19 t hilo hihi))

#print axioms D3SG_CHI_cos_box_le

/-- Sin-upper on the box: `‖sin(π·t/2)‖ ≤ exp 19` (the banked `exp 16`
covered `|Im| ≤ 10`; the box needs `|Im| ≤ 11.56`). -/
theorem D3SG_CHI_sin_box_le (t : ℂ)
    (hilo : 8.44 ≤ t.im) (hihi : t.im ≤ 11.56) :
    ‖Complex.sin ((Real.pi : ℂ) * t / 2)‖ ≤ Real.exp 19 := by
  have habs : |t.im| ≤ 12 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have e : |Real.pi * t.im / 2| = (Real.pi / 2) * |t.im| := by
    rw [show Real.pi * t.im / 2 = (Real.pi / 2) * t.im by ring, abs_mul,
      abs_of_nonneg (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]
  have harg : |((((Real.pi : ℂ)) * t / 2)).im| ≤ 19 := by
    rw [D3SG_CHI_sin_arg_im_eq, e]
    have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
    have h2 := mul_le_mul (le_of_lt (by linarith : Real.pi / 2 < 3.1416 / 2)) habs
      (abs_nonneg _) (show (0 : ℝ) ≤ 3.1416 / 2 by norm_num)
    have hnum : (3.1416 / 2 : ℝ) * 12 ≤ 19 := by norm_num
    linarith
  exact le_trans (D3SG_CHI_sin_le_exp_abs_im _) (Real.exp_le_exp.mpr harg)

#print axioms D3SG_CHI_sin_box_le

/-- Cpow chi-factor on the box is `≤ 7` (base `2π ≥ 1`, exponent `≤ 1`;
mirrors the `cutR10_pi_norm_upper` rpow pattern). -/
theorem D3SG_CHI_cpow_box_le7 (t : ℂ)
    (hlo : -1.06 ≤ t.re) (hhi : t.re ≤ 3 / 2) :
    (2 * Real.pi) ^ (-(1 - t).re) ≤ 7 := by
  have hbase : (1 : ℝ) ≤ 2 * Real.pi := by
    have h := Real.pi_gt_three
    linarith
  have hexp : (-(1 - t).re) ≤ (1 : ℝ) := by
    have heq : (1 - t).re = 1 - t.re := by simp
    rw [heq]
    linarith
  have hle : (2 * Real.pi) ^ (-(1 - t).re) ≤ (2 * Real.pi) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp
  rw [Real.rpow_one] at hle
  have hpi : 2 * Real.pi ≤ 7 := by
    have h := Real.pi_lt_d4
    linarith
  linarith

#print axioms D3SG_CHI_cpow_box_le7

/-- Chi cap on the box: `‖chi(1-t)‖ ≤ 2 * 7 * 600 * exp 19`
(`2` exact, cpow `≤ 7`, Gamma `≤ 600`, cos `≤ exp 19`). -/
theorem D3SG_CHI_box_le (t : ℂ)
    (hlo : -1.06 ≤ t.re) (hhi : t.re ≤ 3 / 2)
    (hilo : 8.44 ≤ t.im) (hihi : t.im ≤ 11.56) :
    ‖D3SG_chiFE (1 - t)‖ ≤ 2 * 7 * 600 * Real.exp 19 := by
  have hchi := D3SG_CHI_norm_le (1 - t)
  have hcpow : (2 * Real.pi) ^ (-(1 - t).re) ≤ 7 :=
    D3SG_CHI_cpow_box_le7 t hlo hhi
  have hG : ‖Complex.Gamma (1 - t)‖ ≤ 600 :=
    D3SG_CHI_Gamma_refl_box_le t hlo hhi hilo hihi
  have him_le : Real.exp |((((Real.pi : ℂ)) * (1 - t) / 2)).im| ≤ Real.exp 19 :=
    Real.exp_le_exp.mpr (D3SG_CHI_arg_im_le19 t hilo hihi)
  have hA : 2 * (2 * Real.pi) ^ (-(1 - t).re) * ‖Complex.Gamma (1 - t)‖
      ≤ 2 * 7 * 600 := by
    have h2c : 2 * (2 * Real.pi) ^ (-(1 - t).re) ≤ 2 * 7 :=
      mul_le_mul_of_nonneg_left hcpow (by norm_num)
    exact mul_le_mul h2c hG (norm_nonneg _) (by norm_num)
  have hGnn : (0 : ℝ) ≤ 2 * 7 * 600 := by norm_num
  exact le_trans hchi (mul_le_mul hA him_le (Real.exp_nonneg _) hGnn)

#print axioms D3SG_CHI_box_le

/-- Sup-product, conditional bridge (ONE assembly attempt of max 3):
chi cap times reflected-zeta premise `Z`. At `Z = 2` this closes
`(2 * 7 * 600 * exp 19) * 2`; the middle-strip `Z = 2` (`hMid` shape in
`cutR10_hFE_of_chi_and_middle`) is the remaining open piece — Euler covers
only the `t.re ≤ -1` sliver — so `≤ 6` is NOT closed here; gap recorded. -/
theorem D3SG_chi_refl_product_le (t : ℂ)
    (hlo : -1.06 ≤ t.re) (hhi : t.re ≤ 3 / 2)
    (hilo : 8.44 ≤ t.im) (hihi : t.im ≤ 11.56)
    (Z : ℝ) (hZ : ‖riemannZeta (1 - t)‖ ≤ Z) :
    ‖D3SG_chiFE (1 - t)‖ * ‖riemannZeta (1 - t)‖ ≤
      (2 * 7 * 600 * Real.exp 19) * Z := by
  have hC := D3SG_CHI_box_le t hlo hhi hilo hihi
  have hC0 : (0 : ℝ) ≤ 2 * 7 * 600 * Real.exp 19 := by positivity
  exact mul_le_mul hC hZ (norm_nonneg _) hC0

#print axioms D3SG_chi_refl_product_le

/-- R02 disc upper via one-step recurrence shift into the banked `[1,2]` cap.
For `w.re ∈ [0.025,0.37]`, `w.im ∈ [-4.125,-2.625]`: `w + 1` has
`Re ∈ [1.025,1.37] ⊆ [1,2]`, so `‖Γ(w+1)‖ ≤ Real.Gamma ≤ 1` by
`D3SG_Gamma_norm_le_real` + `D3SG_Gamma_one_two_le_one`; paying
`‖w‖ ≥ |Im| ≥ 2.625 ≥ 2` via `Complex.Gamma_add_one` gives `‖Γ w‖ ≤ 1/2`.
This is the DG-leaf / E05-E06 complex-Γ disc piece on the R02 w-plane. -/
theorem D3SG_R02_disc_upper (w : ℂ)
    (hre_lo : 0.025 ≤ w.re) (hre_hi : w.re ≤ 0.37)
    (him_lo : -4.125 ≤ w.im) (him_hi : w.im ≤ -2.625) :
    ‖Complex.Gamma w‖ ≤ 1 / 2 := by
  have him_neg : w.im < 0 := by linarith
  have him_abs : (2.625 : ℝ) ≤ |w.im| := by
    rw [abs_of_neg him_neg]
    linarith
  have hw_norm_ge : (2.625 : ℝ) ≤ ‖w‖ :=
    le_trans him_abs (Complex.abs_im_le_norm w)
  have hNorm2 : (2 : ℝ) ≤ ‖w‖ := by linarith
  have hw0 : w ≠ 0 := by
    intro h
    have him0 : w.im = 0 := by
      rw [h]
      simp
    linarith
  have hG : Complex.Gamma (w + 1) = w * Complex.Gamma w :=
    Complex.Gamma_add_one w hw0
  have hGn : ‖Complex.Gamma (w + 1)‖ = ‖w‖ * ‖Complex.Gamma w‖ := by
    rw [hG, norm_mul]
  have hre1_eq : (w + 1).re = w.re + 1 := by simp
  have hRe1_pos : (0 : ℝ) < (w + 1).re := by
    rw [hre1_eq]
    linarith
  have hRe1_lo : (1 : ℝ) ≤ (w + 1).re := by
    rw [hre1_eq]
    linarith
  have hRe1_hi : (w + 1).re ≤ 2 := by
    rw [hre1_eq]
    linarith
  have hDom : ‖Complex.Gamma (w + 1)‖ ≤ Real.Gamma (w + 1).re :=
    D3SG_Gamma_norm_le_real (w + 1) hRe1_pos
  have hRealCap : Real.Gamma (w + 1).re ≤ 1 :=
    D3SG_Gamma_one_two_le_one _ hRe1_lo hRe1_hi
  have hCap1 : ‖Complex.Gamma (w + 1)‖ ≤ 1 :=
    le_trans hDom hRealCap
  have hMul : ‖w‖ * ‖Complex.Gamma w‖ ≤ 1 := by
    rw [← hGn]
    exact hCap1
  have hGamma_nn : (0 : ℝ) ≤ ‖Complex.Gamma w‖ := norm_nonneg _
  have h2Mul : 2 * ‖Complex.Gamma w‖ ≤ ‖w‖ * ‖Complex.Gamma w‖ :=
    mul_le_mul_of_nonneg_right hNorm2 hGamma_nn
  have h2le1 : 2 * ‖Complex.Gamma w‖ ≤ 1 := le_trans h2Mul hMul
  linarith

#print axioms D3SG_R02_disc_upper

/-! ## E05-SEQ5-UPPER: explicit `‖GammaSeq s 5‖ ≤ 0.684` feeder at E05 shifted `s`.

At E05 shifted `s = w_E05 / 2 + 1` (`Re s = 1.1975`, `Im s = -0.375`):
* cpow upper: `‖(5 : ℂ) ^ s‖ = 5 ^ 1.1975 ≤ 6.9` (TRUE `≈ 6.87095`) via
  `Complex.norm_cpow_eq_rpow_re_of_pos` plus `5 ^ 1.1975 = 5 * 5 ^ 0.1975 ≤
  5 * 5 ^ (1/5) ≤ 5 * 1.38 = 6.9` (`0.1975 ≤ 1/5`; `1.38^5 = 5.0049003168 ≥ 5`,
  all `norm_num`).
* denominator norm LOWERS (`sq_norm` shapes with the `Im` contribution kept,
  mirroring the banked denominator norm UPPERS in `door3_premise_gamma.lean`):
  `‖s‖ ≥ 1.25`, `‖s+1‖ ≥ 2.22`, `‖s+2‖ ≥ 3.21`, `‖s+3‖ ≥ 4.21`,
  `‖s+4‖ ≥ 5.21`, `‖s+5‖ ≥ 6.20`; product
  `1.25 * 2.22 * 3.21 * 4.21 * 5.21 * 6.20 = 1211.377571505 ≥ 1211.37`.
* quotient: `6.9 * 120 / 1211.37 = 828 / 1211.37 ≈ 0.68352 ≤ 0.684`
  (`0.684 * 1211.37 = 828.57708 ≥ 828`) — honest upper just above the true
  `‖GammaSeq s 5‖ ≈ 0.6712`, inside the `0.671 + 0.014` budget window.
* status: conditional on the `N = 5` GammaSeq norm-link identity (same open L1
  as the filed `premGamma_E05_GammaSeq5_link` in `door3_premise_gamma.lean`;
  NOT proved here). The `0.014` rate leaf itself (`‖Seq5 - Γ‖ ≤ 0.014`) still
  needs a Stirling-disc / Cauchy convergence estimate elsewhere, NOT this file.
-/

/-- E05 `5 ^ (1/5)` real fifth-root upper: `5 ^ (1/5) ≤ 1.38`
(`1.38^5 = 5.0049003168 ≥ 5`). -/
theorem D3SG_E05_rpow_fifth_root_upper :
    (5 : ℝ) ^ ((1 / 5 : ℝ)) ≤ (1.38 : ℝ) := by
  have hR : (((5 : ℝ) ^ ((1 / 5) : ℝ)) ^ (5 : ℕ)) = (5 : ℝ) ^ (1 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5)]
    have e : (1 / 5 : ℝ) * (((5 : ℕ)) : ℝ) = (((1 : ℕ)) : ℝ) := by norm_num
    rw [e, Real.rpow_natCast]
  have hint : (((5 : ℝ) ^ ((1 / 5) : ℝ)) ^ (5 : ℕ)) ≤ (1.38 : ℝ) ^ (5 : ℕ) := by
    rw [hR]
    norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num : 5 ≠ 0)
    (by norm_num : (0 : ℝ) ≤ (1.38 : ℝ)) hint

#print axioms D3SG_E05_rpow_fifth_root_upper

/-- E05 `5 ^ 1.1975` upper: `5 ^ 1.1975 ≤ 6.9` (TRUE `≈ 6.87095`).
Splits `1.1975 = 1 + 0.1975`, uses `0.1975 ≤ 1/5` monotonicity plus the
fifth-root upper above (`5 * 1.38 = 6.9`). -/
theorem D3SG_E05_rpow_Re_upper :
    (5 : ℝ) ^ ((1.1975 : ℝ)) ≤ (6.9 : ℝ) := by
  have hexp : (1.1975 : ℝ) = 1 + 0.1975 := by norm_num
  have hfrac : (0.1975 : ℝ) ≤ 1 / 5 := by norm_num
  have hmono : (5 : ℝ) ^ ((0.1975) : ℝ) ≤ (5 : ℝ) ^ ((1 / 5) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 5) hfrac
  have h138 : (5 : ℝ) ^ ((0.1975) : ℝ) ≤ (1.38 : ℝ) :=
    le_trans hmono D3SG_E05_rpow_fifth_root_upper
  have h69 : (6.9 : ℝ) = 5 * 1.38 := by norm_num
  rw [hexp, Real.rpow_add (show (0 : ℝ) < 5 by norm_num), Real.rpow_one, h69]
  exact mul_le_mul_of_nonneg_left h138 (by norm_num : (0 : ℝ) ≤ 5)

#print axioms D3SG_E05_rpow_Re_upper

/-- E05 shifted cpow norm upper: `‖(5 : ℂ) ^ s‖ ≤ 6.9` at `s = w_E05 / 2 + 1`. -/
theorem D3SG_E05_cpow5_norm_upper :
    ‖(((5 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))))‖ ≤
      (6.9 : ℝ) := by
  have hre : (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have hbase : ((5 : ℝ) : ℂ) = (5 : ℂ) := by simp
  have hcn := Complex.norm_cpow_eq_rpow_re_of_pos (show (0 : ℝ) < 5 by norm_num)
    (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))
  rw [← hbase, hcn, hre]
  exact D3SG_E05_rpow_Re_upper

#print axioms D3SG_E05_cpow5_norm_upper

/-- E05 shifted `s` norm lower: `1.25 ≤ ‖s‖`
(TRUE `≈ 1.25485`; `1.1975^2 + 0.375^2 = 1.57463125 ≥ 1.25^2`). -/
theorem D3SG_E05_add0_norm_ge :
    (1.25 : ℝ) ≤ ‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ := by
  have hre : (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)).re
      = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)).im
      = (-0.375 : ℝ) := by
    rw [Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).im = (-0.75 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : (1.25 : ℝ) ^ 2 ≤ ‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have habs := abs_le_of_sq_le_sq h2 (norm_nonneg _)
  rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1.25 : ℝ))] at habs

#print axioms D3SG_E05_add0_norm_ge

/-- E05 shifted `s+1` norm lower: `2.22 ≤ ‖s + 1‖`
(TRUE `≈ 2.22953`; `2.1975^2 + 0.375^2 = 4.96963125 ≥ 2.22^2`). -/
theorem D3SG_E05_add1_norm_ge :
    (2.22 : ℝ) ≤ ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ := by
  have hre : ((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)).re
      = (2.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : ((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)).im
      = (-0.375 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).im = (-0.75 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : (2.22 : ℝ) ^ 2 ≤ ‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have habs := abs_le_of_sq_le_sq h2 (norm_nonneg _)
  rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2.22 : ℝ))] at habs

#print axioms D3SG_E05_add1_norm_ge

/-- E05 shifted `s+2` norm lower: `3.21 ≤ ‖s + 2‖`
(TRUE `≈ 3.21944`; `3.1975^2 + 0.375^2 = 10.36463125 ≥ 3.21^2`). -/
theorem D3SG_E05_add2_norm_ge :
    (3.21 : ℝ) ≤ ‖((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ := by
  have hre : ((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1))).re
      = (3.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : ((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1))).im
      = (-0.375 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).im = (-0.75 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : (3.21 : ℝ) ^ 2 ≤ ‖((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have habs := abs_le_of_sq_le_sq h2 (norm_nonneg _)
  rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (3.21 : ℝ))] at habs

#print axioms D3SG_E05_add2_norm_ge

/-- E05 shifted `s+3` norm lower: `4.21 ≤ ‖s + 3‖`
(TRUE `≈ 4.21428`; `4.1975^2 + 0.375^2 = 17.75963125 ≥ 4.21^2`). -/
theorem D3SG_E05_add3_norm_ge :
    (4.21 : ℝ) ≤ ‖(((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ := by
  have hre : (((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1))).re
      = (4.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : (((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1))).im
      = (-0.375 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im,
      Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).im = (-0.75 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : (4.21 : ℝ) ^ 2 ≤ ‖(((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have habs := abs_le_of_sq_le_sq h2 (norm_nonneg _)
  rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (4.21 : ℝ))] at habs

#print axioms D3SG_E05_add3_norm_ge

/-- E05 shifted `s+4` norm lower: `5.21 ≤ ‖s + 4‖`
(TRUE `≈ 5.21103`; `5.1975^2 + 0.375^2 = 27.15463125 ≥ 5.21^2`). -/
theorem D3SG_E05_add4_norm_ge :
    (5.21 : ℝ) ≤ ‖((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ := by
  have hre : ((((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1))).re
      = (5.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : ((((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1))).im
      = (-0.375 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im,
      Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).im = (-0.75 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : (5.21 : ℝ) ^ 2 ≤ ‖((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have habs := abs_le_of_sq_le_sq h2 (norm_nonneg _)
  rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (5.21 : ℝ))] at habs

#print axioms D3SG_E05_add4_norm_ge

/-- E05 shifted `s+5` norm lower: `6.20 ≤ ‖s + 5‖`
(TRUE `≈ 6.20884`; `6.1975^2 + 0.375^2 = 38.54963125 ≥ 6.20^2`). -/
theorem D3SG_E05_add5_norm_ge :
    (6.20 : ℝ) ≤ ‖(((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ := by
  have hre : (((((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1))).re
      = (6.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.add_re, Complex.div_ofNat_re,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).re = (0.395 : ℝ) from rfl,
      Complex.one_re]
    norm_num
  have him : (((((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1))).im
      = (-0.375 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im, Complex.add_im,
      Complex.add_im, Complex.div_ofNat_im,
      show (Complex.mk (0.395 : ℝ) (-0.75 : ℝ)).im = (-0.75 : ℝ) from rfl,
      Complex.one_im]
    norm_num
  have h2 : (6.20 : ℝ) ^ 2 ≤ ‖(((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  have habs := abs_le_of_sq_le_sq h2 (norm_nonneg _)
  rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (6.20 : ℝ))] at habs

#print axioms D3SG_E05_add5_norm_ge

/-- E05 `N = 5` denominator norm-product lower, right-nested to match the
`N = 5` norm-link shape (`1211.377571505 ≥ 1211.37`). -/
theorem D3SG_E05_prod5_norm_ge :
    (1211.37 : ℝ) ≤
    ‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ *
      (‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
        (‖((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
          (‖(((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
            (‖((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
              ‖(((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖)))) := by
  have h45 := mul_le_mul D3SG_E05_add4_norm_ge D3SG_E05_add5_norm_ge
    (by norm_num) (norm_nonneg _)
  have h345 := mul_le_mul D3SG_E05_add3_norm_ge h45
    (by norm_num) (norm_nonneg _)
  have h2345 := mul_le_mul D3SG_E05_add2_norm_ge h345
    (by norm_num) (norm_nonneg _)
  have h12345 := mul_le_mul D3SG_E05_add1_norm_ge h2345
    (by norm_num) (norm_nonneg _)
  have h012345 := mul_le_mul D3SG_E05_add0_norm_ge h12345
    (by norm_num) (norm_nonneg _)
  have heq : (1.25 : ℝ) * (2.22 * (3.21 * (4.21 * (5.21 * 6.20)))) = 1211.377571505 := by
    norm_num
  rw [heq] at h012345
  exact le_trans (by norm_num : (1211.37 : ℝ) ≤ 1211.377571505) h012345

#print axioms D3SG_E05_prod5_norm_ge

/-- E05 `N = 5` explicit Seq5 upper: `‖GammaSeq s 5‖ ≤ 0.684`, conditional on
the `N = 5` norm-link identity (same open L1 as `premGamma_E05_GammaSeq5_link`).
From cpow upper `6.9` + denominator lower `1211.37`
(`6.9 * 120 = 828 ≤ 0.684 * 1211.37 = 828.57708`). -/
theorem D3SG_E05_GammaSeq5_upper_of_link
    (hLink : ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 5‖ =
      ‖(((5 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))))‖ * 120 /
      (‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ *
        (‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
          (‖((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
            (‖(((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
              (‖((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
                ‖(((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖)))))) :
    ‖Complex.GammaSeq (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)) 5‖ ≤
      (0.684 : ℝ) := by
  have hD := D3SG_E05_prod5_norm_ge
  have hDpos : (0 : ℝ) <
      (‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ *
        (‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
          (‖((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
            (‖(((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
              (‖((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
                ‖(((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖))))) := by
    linarith
  rw [hLink, div_le_iff₀ hDpos]
  have h1 : ‖(((5 : ℂ) ^ (((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1))))‖ * 120 ≤
      6.9 * 120 :=
    mul_le_mul_of_nonneg_right D3SG_E05_cpow5_norm_upper (by norm_num : (0 : ℝ) ≤ 120)
  have hD2 : (0.684 : ℝ) * 1211.37 ≤ 0.684 *
      (‖((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1)‖ *
        (‖(((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1)‖ *
          (‖((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1)‖ *
            (‖(((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1)‖ *
              (‖((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1)‖ *
                ‖(((((((((Complex.mk (0.395 : ℝ) (-0.75 : ℝ)) : ℂ) / 2) + 1) + 1) + 1) + 1) + 1) + 1)‖))))) :=
    mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 0.684)
  have h3 : (6.9 : ℝ) * 120 ≤ 0.684 * 1211.37 := by norm_num
  linarith

#print axioms D3SG_E05_GammaSeq5_upper_of_link

/-! ## GAMNEED-OUTER-ADAPTIVE: honest shift-1 attempt at `‖Γ wOuter‖ ≤ 0.002`.

RATE grep (2026-09-22): `D3SG_E05_GammaSeq5_upper_of_link` PRESENT at
`2219-2254` (conditional Seq5 upper `≤ 0.684`). No silent gap there.
Shift shapes reused: `D3SG_gamma_shift_norm`, `D3SG_Gamma_norm_le_real`,
`D3SG_Gamma_one_two_le_one`, plus the R02 one-step template
`D3SG_R02_disc_upper` (`Gamma_add_one` + `[1,2]` real cap + `‖w‖ ≥ |Im|`).

Target: `gamNeed_outer` (`door3_digamma.lean:419`) `‖Γ wOuter‖ ≤ 0.002`
at `wOuter = sOuter / 2`, `sOuter = mk 0.395 (-8.75)`, i.e.
`wOuter = mk 0.1975 (-4.375)` (`Re = 0.1975`, `Im = -4.375`).
This is the TIGHTEST of the four leaves, so no loose-cap claim is made.

Attempt (`N = 1` shift-up + real cap, R02 shape):
`w + 1` has `Re = 1.1975 ∈ [1,2]`, so `‖Γ(w+1)‖ ≤ 1` by domination +
`D3SG_Gamma_one_two_le_one`; paying `‖w‖ ≥ |Im| = 4.375` gives
`‖Γ w‖ ≤ 1 / 4.375 ≈ 0.22857 ≤ 0.229`.
That is `≈ 114x` above `0.002`: honest GAP, banked below as
quotient (`0.229`) + gap (`0.002 < 0.229`, ratio `114 < 0.229/0.002`).
No force toward `0.002`; `N = 2+` would tighten toward `≈ 0.06/0.03`
but keeps a double-digit gap (large-`Im` decay factor unbanked here),
so it is recorded as residual, not attempted in this fenced step.
-/

/-- Adaptive outer shift-1 quotient: `‖Γ(mk 0.1975 (-4.375))‖ ≤ 0.229`
(`1 / 4.375 ≈ 0.22857`). R02-shaped one-step shift into `[1,2]`. -/
theorem D3SG_gamNeed_outer_shift1_upper :
    ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ ≤ (0.229 : ℝ) := by
  have hre1 : ((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1).re = (1.1975 : ℝ) := by
    rw [Complex.add_re, Complex.one_re,
      show (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)).re = (0.1975 : ℝ) from rfl]
    norm_num
  have him_abs : (4.375 : ℝ) ≤ ‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ := by
    have him_eq : (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)).im = (-4.375 : ℝ) := rfl
    have habs : |(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)).im| = (4.375 : ℝ) := by
      rw [him_eq, abs_of_neg (by norm_num : (-4.375 : ℝ) < 0)]
      norm_num
    have h := Complex.abs_im_le_norm (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))
    rw [habs] at h
    exact h
  have hw0 : (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) ≠ 0 := by
    intro h
    have him0 : (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)).im = 0 := by
      rw [h]
      simp
    rw [show (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)).im = (-4.375 : ℝ) from rfl] at him0
    norm_num at him0
  have hG : Complex.Gamma ((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1)
      = (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) *
        Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) :=
    Complex.Gamma_add_one _ hw0
  have hGn : ‖Complex.Gamma ((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1)‖
      = ‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ *
        ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ := by
    rw [hG, norm_mul]
  have hRe1_pos : (0 : ℝ) < ((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1).re := by
    rw [hre1]
    norm_num
  have hRe1_lo : (1 : ℝ) ≤ ((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1).re := by
    rw [hre1]
    norm_num
  have hRe1_hi : ((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1).re ≤ 2 := by
    rw [hre1]
    norm_num
  have hDom : ‖Complex.Gamma ((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1)‖
      ≤ Real.Gamma (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1).re) :=
    D3SG_Gamma_norm_le_real _ hRe1_pos
  have hRealCap : Real.Gamma (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1).re) ≤ 1 :=
    D3SG_Gamma_one_two_le_one _ hRe1_lo hRe1_hi
  have hCap1 : ‖Complex.Gamma ((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1)‖ ≤ 1 :=
    le_trans hDom hRealCap
  have hMul : ‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ *
      ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ ≤ 1 := by
    rw [← hGn]
    exact hCap1
  have hmono : (4.375 : ℝ) *
      ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖
      ≤ ‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ *
        ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ :=
    mul_le_mul_of_nonneg_right him_abs (norm_nonneg _)
  have hle1 : ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖
      ≤ 1 / (4.375 : ℝ) := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4.375), mul_comm]
    exact le_trans hmono hMul
  have h229 : (1 : ℝ) / (4.375 : ℝ) ≤ (0.229 : ℝ) := by norm_num
  exact le_trans hle1 h229

#print axioms D3SG_gamNeed_outer_shift1_upper

/-- Adaptive outer gap: shift-1 quotient `0.229` is above `0.002` (gap, no close). -/
theorem D3SG_gamNeed_outer_shift1_gap :
    (0.002 : ℝ) < (0.229 : ℝ) := by norm_num

#print axioms D3SG_gamNeed_outer_shift1_gap

/-- Adaptive outer ratio: `0.229 / 0.002 ≈ 114.5`, so gap factor exceeds `114`. -/
theorem D3SG_gamNeed_outer_shift1_ratio :
    (114 : ℝ) < (0.229 : ℝ) / (0.002 : ℝ) := by norm_num

#print axioms D3SG_gamNeed_outer_shift1_ratio

/-! ## GAMNEED-LEAF-ADAPTIVE: honest shift-1 attempt at `‖Γ wLeaf‖ ≤ 0.008`.

Target: `gamNeed_leaf` (`door3_digamma.lean:421`) `‖Γ wLeaf‖ ≤ 0.008`
at `wLeaf = mk 0.1 (-3.375)` (`Re = 0.1`, `Im = -3.375`).

Attempt (`N = 1` shift-up + real cap, R02 / outer shape, `‖w‖` paid explicitly):
`w + 1` has `Re = 1.1 ∈ [1,2]`, so `‖Γ(w+1)‖ ≤ 1` by domination +
`D3SG_Gamma_one_two_le_one`; paying `‖w‖ ≥ |Im| = 3.375` gives
`‖Γ w‖ ≤ 1 / 3.375 ≈ 0.29630 ≤ 0.297`.
That is `≈ 37x` above `0.008`: honest GAP, banked below as
quotient (`0.297`) + gap (`0.008 < 0.297`, ratio `37 < 0.297/0.008`).
No force toward `0.008`; `N = 2+` would tighten but keeps a large gap
(large-`Im` decay factor unbanked here), so it is recorded as residual,
not attempted in this fenced step.
-/

/-- Adaptive leaf shift-1 quotient: `‖Γ(mk 0.1 (-3.375))‖ ≤ 0.297`
(`1 / 3.375 ≈ 0.29630`). R02 / outer-shaped one-step shift into `[1,2]`. -/
theorem D3SG_gamNeed_leaf_shift1_upper :
    ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ ≤ (0.297 : ℝ) := by
  have hre1 : ((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1).re = (1.1 : ℝ) := by
    rw [Complex.add_re, Complex.one_re,
      show (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)).re = (0.1 : ℝ) from rfl]
    norm_num
  have him_abs : (3.375 : ℝ) ≤ ‖(Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ := by
    have him_eq : (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)).im = (-3.375 : ℝ) := rfl
    have habs : |(Complex.mk (0.1 : ℝ) (-3.375 : ℝ)).im| = (3.375 : ℝ) := by
      rw [him_eq, abs_of_neg (by norm_num : (-3.375 : ℝ) < 0)]
      norm_num
    have h := Complex.abs_im_le_norm (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))
    rw [habs] at h
    exact h
  have hw0 : (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) ≠ 0 := by
    intro h
    have him0 : (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)).im = 0 := by
      rw [h]
      simp
    rw [show (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)).im = (-3.375 : ℝ) from rfl] at him0
    norm_num at him0
  have hG : Complex.Gamma ((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1)
      = (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) *
        Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) :=
    Complex.Gamma_add_one _ hw0
  have hGn : ‖Complex.Gamma ((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1)‖
      = ‖(Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ *
        ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ := by
    rw [hG, norm_mul]
  have hRe1_pos : (0 : ℝ) < ((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1).re := by
    rw [hre1]
    norm_num
  have hRe1_lo : (1 : ℝ) ≤ ((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1).re := by
    rw [hre1]
    norm_num
  have hRe1_hi : ((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1).re ≤ 2 := by
    rw [hre1]
    norm_num
  have hDom : ‖Complex.Gamma ((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1)‖
      ≤ Real.Gamma (((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1).re) :=
    D3SG_Gamma_norm_le_real _ hRe1_pos
  have hRealCap : Real.Gamma (((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1).re) ≤ 1 :=
    D3SG_Gamma_one_two_le_one _ hRe1_lo hRe1_hi
  have hCap1 : ‖Complex.Gamma ((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1)‖ ≤ 1 :=
    le_trans hDom hRealCap
  have hMul : ‖(Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ *
      ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ ≤ 1 := by
    rw [← hGn]
    exact hCap1
  have hmono : (3.375 : ℝ) *
      ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖
      ≤ ‖(Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ *
        ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ :=
    mul_le_mul_of_nonneg_right him_abs (norm_nonneg _)
  have hle1 : ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖
      ≤ 1 / (3.375 : ℝ) := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3.375), mul_comm]
    exact le_trans hmono hMul
  have h297 : (1 : ℝ) / (3.375 : ℝ) ≤ (0.297 : ℝ) := by norm_num
  exact le_trans hle1 h297

#print axioms D3SG_gamNeed_leaf_shift1_upper

/-- Adaptive leaf gap: shift-1 quotient `0.297` is above `0.008` (gap, no close). -/
theorem D3SG_gamNeed_leaf_shift1_gap :
    (0.008 : ℝ) < (0.297 : ℝ) := by norm_num

#print axioms D3SG_gamNeed_leaf_shift1_gap

/-- Adaptive leaf ratio: `0.297 / 0.008 = 37.125`, so gap factor exceeds `37`. -/
theorem D3SG_gamNeed_leaf_shift1_ratio :
    (37 : ℝ) < (0.297 : ℝ) / (0.008 : ℝ) := by norm_num

#print axioms D3SG_gamNeed_leaf_shift1_ratio

/-! ## DISC-UPPER-RUNG2: R02 tight `‖Γ w‖ ≤ 0.381` (same region, full `‖w‖` paid).

Grep (2026-09-22): latest disc-upper rung is `D3SG_R02_disc_upper` at `:1918`
(`‖Γ w‖ ≤ 1/2` on `Re ∈ [0.025,0.37]`, `Im ∈ [-4.125,-2.625]`).
E05-upper `D3SG_E05_GammaSeq5_upper_of_link` at `:2219` (`≤ 0.684`, conditional).
gamNeed gaps banked: outer `0.229` vs `0.002` (`114x`), leaf `0.297` vs `0.008`
(`37x`) at `:2282-2448`.

This rung tightens R02 from `1/2` to `0.381` by paying the full
`‖w‖ ≥ |Im| ≥ 2.625` (`1/2.625 ≈ 0.38095 ≤ 0.381`) instead of rounding the
denominator down to `2`. Same one-step shift into `[1,2]`
(`D3SG_Gamma_norm_le_real` + `D3SG_Gamma_one_two_le_one`).

Residual: gamNeed_outer (`≤ 0.002`) and gamNeed_leaf (`≤ 0.008`) remain open;
shift-1 quotients above stand; `N = 2` tightenings need a `Re > 2` real cap
(`Γ(2.1)-` style), not banked here. -/

/-- R02 disc tight upper: `‖Γ w‖ ≤ 0.381` on the R02 window
(`1 / 2.625 ≈ 0.38095`). -/
theorem D3SG_R02_disc_upper_tight (w : ℂ)
    (hre_lo : 0.025 ≤ w.re) (hre_hi : w.re ≤ 0.37)
    (him_lo : -4.125 ≤ w.im) (him_hi : w.im ≤ -2.625) :
    ‖Complex.Gamma w‖ ≤ (0.381 : ℝ) := by
  have him_neg : w.im < 0 := by linarith
  have him_abs : (2.625 : ℝ) ≤ |w.im| := by
    rw [abs_of_neg him_neg]
    linarith
  have hw_norm_ge : (2.625 : ℝ) ≤ ‖w‖ :=
    le_trans him_abs (Complex.abs_im_le_norm w)
  have hw0 : w ≠ 0 := by
    intro h
    have him0 : w.im = 0 := by
      rw [h]
      simp
    linarith
  have hG : Complex.Gamma (w + 1) = w * Complex.Gamma w :=
    Complex.Gamma_add_one w hw0
  have hGn : ‖Complex.Gamma (w + 1)‖ = ‖w‖ * ‖Complex.Gamma w‖ := by
    rw [hG, norm_mul]
  have hre1_eq : (w + 1).re = w.re + 1 := by simp
  have hRe1_pos : (0 : ℝ) < (w + 1).re := by
    rw [hre1_eq]
    linarith
  have hRe1_lo : (1 : ℝ) ≤ (w + 1).re := by
    rw [hre1_eq]
    linarith
  have hRe1_hi : (w + 1).re ≤ 2 := by
    rw [hre1_eq]
    linarith
  have hDom : ‖Complex.Gamma (w + 1)‖ ≤ Real.Gamma (w + 1).re :=
    D3SG_Gamma_norm_le_real (w + 1) hRe1_pos
  have hRealCap : Real.Gamma (w + 1).re ≤ 1 :=
    D3SG_Gamma_one_two_le_one _ hRe1_lo hRe1_hi
  have hCap1 : ‖Complex.Gamma (w + 1)‖ ≤ 1 :=
    le_trans hDom hRealCap
  have hMul : ‖w‖ * ‖Complex.Gamma w‖ ≤ 1 := by
    rw [← hGn]
    exact hCap1
  have hGamma_nn : (0 : ℝ) ≤ ‖Complex.Gamma w‖ := norm_nonneg _
  have h2625Mul : (2.625 : ℝ) * ‖Complex.Gamma w‖ ≤ ‖w‖ * ‖Complex.Gamma w‖ :=
    mul_le_mul_of_nonneg_right hw_norm_ge hGamma_nn
  have hle : (2.625 : ℝ) * ‖Complex.Gamma w‖ ≤ 1 := le_trans h2625Mul hMul
  have hdiv : ‖Complex.Gamma w‖ ≤ 1 / (2.625 : ℝ) := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2.625), mul_comm]
    exact hle
  have h381 : (1 : ℝ) / (2.625 : ℝ) ≤ (0.381 : ℝ) := by norm_num
  exact le_trans hdiv h381

#print axioms D3SG_R02_disc_upper_tight

/-! ## E05-TIGHTEN-ATTEMPT + GAMNEED-OUTER-SHIFT2 (STIRLING-E05, 2026-09-22).

Grep first (this file unless noted):
* E05 link: `D3SG_E05_GammaSeq5_upper_of_link` at `:2219-2254`
  (`‖GammaSeq s 5‖ ≤ 0.684` conditional on `hLink` norm identity, same open L1
  as `premGamma_E05_GammaSeq5_link` in `door3_premise_gamma.lean:3005-3013`).
* disc-upper: `D3SG_R02_disc_upper` at `:1918` (`≤ 1/2`),
  tight rung `D3SG_R02_disc_upper_tight` at `:2469-2518` (`≤ 0.381`).
* gamNeed specs: `gamNeed_outer` (`door3_digamma.lean:419`, `‖Γ wOuter‖ ≤ 0.002`,
  `wOuter = mk 0.1975 (-4.375)`), `gamNeed_leaf` (`door3_digamma.lean:421`,
  `‖Γ wLeaf‖ ≤ 0.008`, `wLeaf = mk 0.1 (-3.375)`); banked shift-1 quotients
  `:2282-2448` (outer `0.229` gap `114x`, leaf `0.297` gap `37x`).

E05 tighten via `0.381` disc: BLOCKED honestly. The R02 disc window
(`Re ∈ [0.025,0.37]`, `Im ∈ [-4.125,-2.625]`) does not contain the E05 shifted
point (`Re = 1.1975`, `Im = -0.375`), and the E05 `0.684` upper is conditional
on the `N = 5` GammaSeq norm-link identity (open L1 above), not on a
complex-Γ disc value. No silent chaining; no change to `:2219`.

ONE honest gamNeed feeder instead (outer `N = 2`, R02-shaped, banked caps only):
`wOuter+2` has `Re = 2.1975`, so `‖Γ(w+2)‖ ≤ Real.Gamma 2.1975 ≤ 1.2` by
domination + `D3SG_Real_Gamma_21975_le_one_two`
(`Γ 2.1975 = 1.1975 * Γ 1.1975 ≤ 1.1975 ≤ 1.2`, `Γ ≤ 1` on `[1,2]` banked).
Paying `‖w‖ ≥ 4.375`, `‖w+1‖ ≥ 4.375` (`|Im|` lowers) gives
`‖Γ w‖ ≤ 1.2 / (4.375 * 4.375) ≈ 0.06269 ≤ 0.063`.
That is `0.063 / 0.002 = 31.5`, i.e. `≈ 31x` above `0.002`: IMPROVES the
shift-1 `114x` gap but does NOT close `gamNeed_outer`. Filed as quotient +
gap + ratio below; residual stands.

Residual: `D3SG_E05_GammaSeq5_upper_of_link` stays conditional (`≤ 0.684`);
`gamNeed_outer (≤ 0.002)` OPEN (`0.063` banked here, `31x` gap);
`gamNeed_leaf (≤ 0.008)` OPEN (`0.297` banked at `:2375`, `37x` gap).
-/

/-- Outer shift-2 real cap: `Real.Gamma 2.1975 ≤ 1.2`
(`Γ 2.1975 = 1.1975 * Γ 1.1975 ≤ 1.1975 ≤ 1.2`). -/
theorem D3SG_Real_Gamma_21975_le_one_two : Real.Gamma 2.1975 ≤ 1.2 := by
  have h1 : (1 : ℝ) ≤ 1.1975 := by norm_num
  have h2 : (1.1975 : ℝ) ≤ 2 := by norm_num
  have hcap : Real.Gamma 1.1975 ≤ 1 :=
    D3SG_Gamma_one_two_le_one _ h1 h2
  have hne : (1.1975 : ℝ) ≠ 0 := by norm_num
  have hshift : Real.Gamma (1.1975 + 1) = 1.1975 * Real.Gamma 1.1975 :=
    Real.Gamma_add_one hne
  have heq : (1.1975 : ℝ) + 1 = 2.1975 := by norm_num
  rw [heq] at hshift
  rw [hshift]
  calc (1.1975 : ℝ) * Real.Gamma 1.1975
      ≤ 1.1975 * 1 :=
        mul_le_mul_of_nonneg_left hcap (by norm_num : (0 : ℝ) ≤ 1.1975)
    _ ≤ 1.2 := by norm_num

#print axioms D3SG_Real_Gamma_21975_le_one_two

/-- Outer shift-2 quotient: `‖Γ(mk 0.1975 (-4.375))‖ ≤ 0.063`
(`1.2 / (4.375 * 4.375) ≈ 0.06269`). Two-step shift into `Re = 2.1975`. -/
theorem D3SG_gamNeed_outer_shift2_upper :
    ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ ≤ (0.063 : ℝ) := by
  have hre2 : ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1)).re
      = (2.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.one_re, Complex.one_re,
      show (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)).re = (0.1975 : ℝ) from rfl]
    norm_num
  have him_w : (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)).im = (-4.375 : ℝ) := rfl
  have him_w1 : (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1)).im
      = (-4.375 : ℝ) := by
    rw [Complex.add_im, Complex.one_im, him_w]
    norm_num
  have habs_w : |(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)).im| = (4.375 : ℝ) := by
    rw [him_w, abs_of_neg (by norm_num : (-4.375 : ℝ) < 0)]
    norm_num
  have habs_w1 : |(((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1)).im|
      = (4.375 : ℝ) := by
    rw [him_w1, abs_of_neg (by norm_num : (-4.375 : ℝ) < 0)]
    norm_num
  have hnorm_w : (4.375 : ℝ) ≤ ‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ := by
    have h := Complex.abs_im_le_norm (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))
    rw [habs_w] at h
    exact h
  have hnorm_w1 : (4.375 : ℝ)
      ≤ ‖(((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖ := by
    have h := Complex.abs_im_le_norm (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))
    rw [habs_w1] at h
    exact h
  have hw0 : (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) ≠ 0 := by
    intro h
    have him0 : (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)).im = 0 := by
      rw [h]
      simp
    rw [him_w] at him0
    norm_num at him0
  have hw10 : (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1)) ≠ 0 := by
    intro h
    have him0 : ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))).im = 0 := by
      rw [h]
      simp
    rw [him_w1] at him0
    norm_num at him0
  have hG1 : Complex.Gamma (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))
      = (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) *
        Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) :=
    Complex.Gamma_add_one _ hw0
  have hG2 : Complex.Gamma ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))
      = (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1)) *
        Complex.Gamma (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1)) :=
    Complex.Gamma_add_one _ hw10
  have hGn1 : ‖Complex.Gamma (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖
      = ‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ *
        ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ := by
    rw [hG1, norm_mul]
  have hGn2 : ‖Complex.Gamma ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))‖
      = ‖(((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖ *
        ‖Complex.Gamma (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖ := by
    rw [hG2, norm_mul]
  have hRe2_pos : (0 : ℝ)
      < ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1)).re := by
    rw [hre2]
    norm_num
  have hDom : ‖Complex.Gamma ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))‖
      ≤ Real.Gamma ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1)).re :=
    D3SG_Gamma_norm_le_real _ hRe2_pos
  rw [hre2] at hDom
  have hCap12 : ‖Complex.Gamma ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))‖
      ≤ (1.2 : ℝ) :=
    le_trans hDom D3SG_Real_Gamma_21975_le_one_two
  have hMul : ‖(((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖ *
      (‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ *
        ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖)
      ≤ (1.2 : ℝ) := by
    rw [← hGn1, ← hGn2]
    exact hCap12
  have hGamma_nn : (0 : ℝ)
      ≤ ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ :=
    norm_nonneg _
  have hmono1 : (4.375 : ℝ)
      * ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖
      ≤ ‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ *
        ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ :=
    mul_le_mul_of_nonneg_right hnorm_w hGamma_nn
  have hmono2 : (4.375 : ℝ) * ((4.375 : ℝ)
      * ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖)
      ≤ ‖(((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖ *
        (‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ *
          ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖) :=
    mul_le_mul hnorm_w1 hmono1
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4.375) hGamma_nn)
      (norm_nonneg _)
  have hle : (4.375 : ℝ) * ((4.375 : ℝ)
      * ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖)
      ≤ (1.2 : ℝ) :=
    le_trans hmono2 hMul
  have hle2 : ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖
      * (4.375 * 4.375) ≤ (1.2 : ℝ) := by
    have heq : ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖
        * (4.375 * 4.375)
        = (4.375 : ℝ) * ((4.375 : ℝ)
          * ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖) := by
      ring
    rw [heq]
    exact hle
  have hdiv : ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖
      ≤ (1.2 : ℝ) / (4.375 * 4.375) := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4.375 * 4.375)]
    exact hle2
  have h063 : (1.2 : ℝ) / (4.375 * 4.375) ≤ (0.063 : ℝ) := by norm_num
  exact le_trans hdiv h063

#print axioms D3SG_gamNeed_outer_shift2_upper

/-- Outer shift-2 gap: `0.063` is above `0.002` (gap, no close). -/
theorem D3SG_gamNeed_outer_shift2_gap :
    (0.002 : ℝ) < (0.063 : ℝ) := by norm_num

#print axioms D3SG_gamNeed_outer_shift2_gap

/-- Outer shift-2 ratio: `0.063 / 0.002 = 31.5`, so gap factor exceeds `31`. -/
theorem D3SG_gamNeed_outer_shift2_ratio :
    (31 : ℝ) < (0.063 : ℝ) / (0.002 : ℝ) := by norm_num

#print axioms D3SG_gamNeed_outer_shift2_ratio

/-! ## GAMNEED-LEAF-SHIFT2 (STIRLING-LEAF2, 2026-09-22).

Grep first (this file unless noted):
* outer shift-2 shape: `D3SG_Real_Gamma_21975_le_one_two` at `:2554-2572`
  (`Real.Gamma 2.1975 ≤ 1.2` via `Γ 2.1975 = 1.1975 * Γ 1.1975`, `Γ ≤ 1` on
  `[1,2]` banked as `D3SG_Gamma_one_two_le_one` at `:1366`), quotient
  `D3SG_gamNeed_outer_shift2_upper` at `:2576` (`‖Γ(mk 0.1975 (-4.375))‖ ≤ 0.063`
  via `1.2 / (4.375 * 4.375) ≈ 0.06269`, two-step shift into `Re = 2.1975`,
  `‖w‖ ≥ 4.375`, `‖w+1‖ ≥ 4.375` from `|Im|` lowers).
* leaf specs: `gamNeed_leaf` (`door3_digamma.lean:421`, `‖Γ wLeaf‖ ≤ 0.008`,
  `wLeaf = mk 0.1 (-3.375)`); banked shift-1 quotient
  `D3SG_gamNeed_leaf_shift1_upper` at `:2375` (`≤ 0.297` via `1 / 3.375`).

Leaf shift-2 mirror (honest, same chain at leaf point): `wLeaf+2` has
`Re = 2.1`, so `‖Γ(w+2)‖ ≤ Real.Gamma 2.1 ≤ 1.1` by domination +
`D3SG_Real_Gamma_21_le_one_one` (`Γ 2.1 = 1.1 * Γ 1.1 ≤ 1.1`, `Γ ≤ 1` on
`[1,2]` banked). Paying `‖w‖ ≥ 3.375`, `‖w+1‖ ≥ 3.375` (`|Im|` lowers) gives
`‖Γ w‖ ≤ 1.1 / (3.375 * 3.375) ≈ 0.09657 ≤ 0.097`.
That is `0.097 / 0.008 = 12.125`, i.e. `≈ 12x` above `0.008`: IMPROVES the
shift-1 `37x` gap but does NOT close `gamNeed_leaf`. Filed as quotient +
gap + ratio below; residual stands.

Residual: `gamNeed_outer (≤ 0.002)` OPEN (`0.063` banked at `:2576`, `31x` gap);
`gamNeed_leaf (≤ 0.008)` OPEN (`0.097` banked here, `12x` gap; prior `0.297`
at `:2375` superseded as best quotient but gap remains).
-/

/-- Leaf shift-2 real cap: `Real.Gamma 2.1 ≤ 1.1`
(`Γ 2.1 = 1.1 * Γ 1.1 ≤ 1.1`). -/
theorem D3SG_Real_Gamma_21_le_one_one : Real.Gamma 2.1 ≤ 1.1 := by
  have h1 : (1 : ℝ) ≤ 1.1 := by norm_num
  have h2 : (1.1 : ℝ) ≤ 2 := by norm_num
  have hcap : Real.Gamma 1.1 ≤ 1 :=
    D3SG_Gamma_one_two_le_one _ h1 h2
  have hne : (1.1 : ℝ) ≠ 0 := by norm_num
  have hshift : Real.Gamma (1.1 + 1) = 1.1 * Real.Gamma 1.1 :=
    Real.Gamma_add_one hne
  have heq : (1.1 : ℝ) + 1 = 2.1 := by norm_num
  rw [heq] at hshift
  rw [hshift]
  calc (1.1 : ℝ) * Real.Gamma 1.1
      ≤ 1.1 * 1 :=
        mul_le_mul_of_nonneg_left hcap (by norm_num : (0 : ℝ) ≤ 1.1)
    _ ≤ 1.1 := by norm_num

#print axioms D3SG_Real_Gamma_21_le_one_one

/-- Leaf shift-2 quotient: `‖Γ(mk 0.1 (-3.375))‖ ≤ 0.097`
(`1.1 / (3.375 * 3.375) ≈ 0.09657`). Two-step shift into `Re = 2.1`. -/
theorem D3SG_gamNeed_leaf_shift2_upper :
    ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ ≤ (0.097 : ℝ) := by
  have hre2 : ((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1)).re
      = (2.1 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.one_re, Complex.one_re,
      show (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)).re = (0.1 : ℝ) from rfl]
    norm_num
  have him_w : (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)).im = (-3.375 : ℝ) := rfl
  have him_w1 : (((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1)).im
      = (-3.375 : ℝ) := by
    rw [Complex.add_im, Complex.one_im, him_w]
    norm_num
  have habs_w : |(Complex.mk (0.1 : ℝ) (-3.375 : ℝ)).im| = (3.375 : ℝ) := by
    rw [him_w, abs_of_neg (by norm_num : (-3.375 : ℝ) < 0)]
    norm_num
  have habs_w1 : |(((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1)).im|
      = (3.375 : ℝ) := by
    rw [him_w1, abs_of_neg (by norm_num : (-3.375 : ℝ) < 0)]
    norm_num
  have hnorm_w : (3.375 : ℝ) ≤ ‖(Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ := by
    have h := Complex.abs_im_le_norm (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))
    rw [habs_w] at h
    exact h
  have hnorm_w1 : (3.375 : ℝ)
      ≤ ‖(((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1))‖ := by
    have h := Complex.abs_im_le_norm (((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1))
    rw [habs_w1] at h
    exact h
  have hw0 : (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) ≠ 0 := by
    intro h
    have him0 : (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)).im = 0 := by
      rw [h]
      simp
    rw [him_w] at him0
    norm_num at him0
  have hw10 : (((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1)) ≠ 0 := by
    intro h
    have him0 : ((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1))).im = 0 := by
      rw [h]
      simp
    rw [him_w1] at him0
    norm_num at him0
  have hG1 : Complex.Gamma (((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1))
      = (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) *
        Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) :=
    Complex.Gamma_add_one _ hw0
  have hG2 : Complex.Gamma ((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1))
      = (((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1)) *
        Complex.Gamma (((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1)) :=
    Complex.Gamma_add_one _ hw10
  have hGn1 : ‖Complex.Gamma (((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1))‖
      = ‖(Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ *
        ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ := by
    rw [hG1, norm_mul]
  have hGn2 : ‖Complex.Gamma ((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1))‖
      = ‖(((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1))‖ *
        ‖Complex.Gamma (((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1))‖ := by
    rw [hG2, norm_mul]
  have hRe2_pos : (0 : ℝ)
      < ((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1)).re := by
    rw [hre2]
    norm_num
  have hDom : ‖Complex.Gamma ((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1))‖
      ≤ Real.Gamma ((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1)).re :=
    D3SG_Gamma_norm_le_real _ hRe2_pos
  rw [hre2] at hDom
  have hCap11 : ‖Complex.Gamma ((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1))‖
      ≤ (1.1 : ℝ) :=
    le_trans hDom D3SG_Real_Gamma_21_le_one_one
  have hMul : ‖(((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1))‖ *
      (‖(Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ *
        ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖)
      ≤ (1.1 : ℝ) := by
    rw [← hGn1, ← hGn2]
    exact hCap11
  have hGamma_nn : (0 : ℝ)
      ≤ ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ :=
    norm_nonneg _
  have hmono1 : (3.375 : ℝ)
      * ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖
      ≤ ‖(Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ *
        ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ :=
    mul_le_mul_of_nonneg_right hnorm_w hGamma_nn
  have hmono2 : (3.375 : ℝ) * ((3.375 : ℝ)
      * ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖)
      ≤ ‖(((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1))‖ *
        (‖(Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ *
          ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖) :=
    mul_le_mul hnorm_w1 hmono1
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3.375) hGamma_nn)
      (norm_nonneg _)
  have hle : (3.375 : ℝ) * ((3.375 : ℝ)
      * ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖)
      ≤ (1.1 : ℝ) :=
    le_trans hmono2 hMul
  have hle2 : ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖
      * (3.375 * 3.375) ≤ (1.1 : ℝ) := by
    have heq : ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖
        * (3.375 * 3.375)
        = (3.375 : ℝ) * ((3.375 : ℝ)
          * ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖) := by
      ring
    rw [heq]
    exact hle
  have hdiv : ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖
      ≤ (1.1 : ℝ) / (3.375 * 3.375) := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3.375 * 3.375)]
    exact hle2
  have h097 : (1.1 : ℝ) / (3.375 * 3.375) ≤ (0.097 : ℝ) := by norm_num
  exact le_trans hdiv h097

#print axioms D3SG_gamNeed_leaf_shift2_upper

/-- Leaf shift-2 gap: `0.097` is above `0.008` (gap, no close). -/
theorem D3SG_gamNeed_leaf_shift2_gap :
    (0.008 : ℝ) < (0.097 : ℝ) := by norm_num

#print axioms D3SG_gamNeed_leaf_shift2_gap

/-- Leaf shift-2 ratio: `0.097 / 0.008 = 12.125`, so gap factor exceeds `12`. -/
theorem D3SG_gamNeed_leaf_shift2_ratio :
    (12 : ℝ) < (0.097 : ℝ) / (0.008 : ℝ) := by norm_num

#print axioms D3SG_gamNeed_leaf_shift2_ratio

/-! ## GAMNEED-OUTER-SHIFT3 (STIRLING-SHIFT3, 2026-09-22).

Grep first (this file unless noted):
* outer shift-2 shape: `D3SG_Real_Gamma_21975_le_one_two` at `:2556`
  (`Real.Gamma 2.1975 ≤ 1.2` via `Γ 2.1975 = 1.1975 * Γ 1.1975`, `Γ ≤ 1` on
  `[1,2]` banked as `D3SG_Gamma_one_two_le_one` at `:1366`), quotient
  `D3SG_gamNeed_outer_shift2_upper` at `:2576` (`‖Γ(mk 0.1975 (-4.375))‖ ≤ 0.063`
  via `1.2 / (4.375 * 4.375) ≈ 0.06269`, two-step shift into `Re = 2.1975`,
  `‖w‖ ≥ 4.375`, `‖w+1‖ ≥ 4.375` from `|Im|` lowers), gap `:2690`, ratio `:2696`.
* leaf shift-2 shape: `D3SG_Real_Gamma_21_le_one_one` at `:2730`
  (`Real.Gamma 2.1 ≤ 1.1`), quotient `D3SG_gamNeed_leaf_shift2_upper` at `:2750`
  (`‖Γ(mk 0.1 (-3.375))‖ ≤ 0.097` via `1.1 / (3.375 * 3.375)`), gap `:2863`,
  ratio `:2870`.

Outer shift-3 mirror (honest, same chain at outer point): `wOuter+3` has
`Re = 3.1975`, so `‖Γ(w+3)‖ ≤ Real.Gamma 3.1975 ≤ 2.64` by domination +
`D3SG_Real_Gamma_31975_le_two_sixfour`
(`Γ 3.1975 = 2.1975 * Γ 2.1975 ≤ 2.1975 * 1.2 = 2.637 ≤ 2.64`, reusing
`D3SG_Real_Gamma_21975_le_one_two`). Paying `‖w‖ ≥ 4.375`,
`‖w+1‖ ≥ 4.375`, `‖w+2‖ ≥ 4.375` (`|Im|` lowers) gives
`‖Γ w‖ ≤ 2.64 / (4.375 ^ 3) ≈ 0.03152 ≤ 0.032`.
That is `0.032 / 0.002 = 16`, i.e. `≈ 16x` above `0.002`: IMPROVES the
shift-2 `31x` gap but does NOT close `gamNeed_outer`. Filed as quotient +
gap + ratio below; residual stands.

Residual: `gamNeed_outer (≤ 0.002)` OPEN (`0.032` banked here, `16x` gap;
prior `0.063` at `:2576` superseded as best quotient but gap remains);
`gamNeed_leaf (≤ 0.008)` OPEN (`0.097` banked at `:2750`, `12x` gap).
-/

/-- Outer shift-3 real cap: `Real.Gamma 3.1975 ≤ 2.64`
(`Γ 3.1975 = 2.1975 * Γ 2.1975 ≤ 2.1975 * 1.2 ≤ 2.64`). -/
theorem D3SG_Real_Gamma_31975_le_two_sixfour : Real.Gamma 3.1975 ≤ 2.64 := by
  have hne : (2.1975 : ℝ) ≠ 0 := by norm_num
  have hshift : Real.Gamma (2.1975 + 1) = 2.1975 * Real.Gamma 2.1975 :=
    Real.Gamma_add_one hne
  have heq : (2.1975 : ℝ) + 1 = 3.1975 := by norm_num
  rw [heq] at hshift
  rw [hshift]
  calc (2.1975 : ℝ) * Real.Gamma 2.1975
      ≤ 2.1975 * 1.2 :=
        mul_le_mul_of_nonneg_left D3SG_Real_Gamma_21975_le_one_two (by norm_num)
    _ ≤ 2.64 := by norm_num

#print axioms D3SG_Real_Gamma_31975_le_two_sixfour

/-- Outer shift-3 quotient: `‖Γ(mk 0.1975 (-4.375))‖ ≤ 0.032`
(`2.64 / (4.375 ^ 3) ≈ 0.03152`). Three-step shift into `Re = 3.1975`. -/
theorem D3SG_gamNeed_outer_shift3_upper :
    ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ ≤ (0.032 : ℝ) := by
  have hre3 : (((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1)).re
      = (3.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.one_re,
      Complex.one_re, Complex.one_re,
      show (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)).re = (0.1975 : ℝ) from rfl]
    norm_num
  have him_w : (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)).im = (-4.375 : ℝ) := rfl
  have him_w1 : (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1)).im
      = (-4.375 : ℝ) := by
    rw [Complex.add_im, Complex.one_im, him_w]
    norm_num
  have him_w2 : ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1)).im
      = (-4.375 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.one_im, Complex.one_im, him_w]
    norm_num
  have habs_w : |(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)).im| = (4.375 : ℝ) := by
    rw [him_w, abs_of_neg (by norm_num : (-4.375 : ℝ) < 0)]
    norm_num
  have habs_w1 : |(((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1)).im|
      = (4.375 : ℝ) := by
    rw [him_w1, abs_of_neg (by norm_num : (-4.375 : ℝ) < 0)]
    norm_num
  have habs_w2 : |((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1)).im|
      = (4.375 : ℝ) := by
    rw [him_w2, abs_of_neg (by norm_num : (-4.375 : ℝ) < 0)]
    norm_num
  have hnorm_w : (4.375 : ℝ) ≤ ‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ := by
    have h := Complex.abs_im_le_norm (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))
    rw [habs_w] at h
    exact h
  have hnorm_w1 : (4.375 : ℝ)
      ≤ ‖(((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖ := by
    have h := Complex.abs_im_le_norm (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))
    rw [habs_w1] at h
    exact h
  have hnorm_w2 : (4.375 : ℝ)
      ≤ ‖((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))‖ := by
    have h := Complex.abs_im_le_norm ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))
    rw [habs_w2] at h
    exact h
  have hw0 : (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) ≠ 0 := by
    intro h
    have him0 : (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)).im = 0 := by
      rw [h]
      simp
    rw [him_w] at him0
    norm_num at him0
  have hw10 : (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1)) ≠ 0 := by
    intro h
    have him0 : ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))).im = 0 := by
      rw [h]
      simp
    rw [him_w1] at him0
    norm_num at him0
  have hw20 : ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1)) ≠ 0 := by
    intro h
    have him0 : (((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))).im = 0 := by
      rw [h]
      simp
    rw [him_w2] at him0
    norm_num at him0
  have hG1 : Complex.Gamma (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))
      = (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) *
        Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) :=
    Complex.Gamma_add_one _ hw0
  have hG2 : Complex.Gamma ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))
      = (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1)) *
        Complex.Gamma (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1)) :=
    Complex.Gamma_add_one _ hw10
  have hG3 : Complex.Gamma (((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1))
      = ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1)) *
        Complex.Gamma ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1)) :=
    Complex.Gamma_add_one _ hw20
  have hGn1 : ‖Complex.Gamma (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖
      = ‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ *
        ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ := by
    rw [hG1, norm_mul]
  have hGn2 : ‖Complex.Gamma ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))‖
      = ‖(((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖ *
        ‖Complex.Gamma (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖ := by
    rw [hG2, norm_mul]
  have hGn3 : ‖Complex.Gamma (((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1))‖
      = ‖((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))‖ *
        ‖Complex.Gamma ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))‖ := by
    rw [hG3, norm_mul]
  have hRe3_pos : (0 : ℝ)
      < (((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1)).re := by
    rw [hre3]
    norm_num
  have hDom : ‖Complex.Gamma (((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1))‖
      ≤ Real.Gamma (((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1)).re :=
    D3SG_Gamma_norm_le_real _ hRe3_pos
  rw [hre3] at hDom
  have hCap : ‖Complex.Gamma (((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1))‖
      ≤ (2.64 : ℝ) :=
    le_trans hDom D3SG_Real_Gamma_31975_le_two_sixfour
  have hMul : ‖((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))‖ *
      (‖(((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖ *
        (‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ *
          ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖))
      ≤ (2.64 : ℝ) := by
    rw [← hGn1, ← hGn2, ← hGn3]
    exact hCap
  have hGamma_nn : (0 : ℝ)
      ≤ ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ :=
    norm_nonneg _
  have hmono1 : (4.375 : ℝ)
      * ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖
      ≤ ‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ *
        ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ :=
    mul_le_mul_of_nonneg_right hnorm_w hGamma_nn
  have hmono2 : (4.375 : ℝ) * ((4.375 : ℝ)
      * ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖)
      ≤ ‖(((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖ *
        (‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ *
          ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖) :=
    mul_le_mul hnorm_w1 hmono1
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4.375) hGamma_nn)
      (norm_nonneg _)
  have hmono3 : (4.375 : ℝ) * ((4.375 : ℝ) * ((4.375 : ℝ)
      * ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖))
      ≤ ‖((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))‖ *
        (‖(((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖ *
          (‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ *
            ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖)) :=
    mul_le_mul hnorm_w2 hmono2
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4.375)
        (by norm_num : (0 : ℝ) ≤ 4.375)) hGamma_nn)
      (norm_nonneg _)
  have hle : (4.375 : ℝ) * ((4.375 : ℝ) * ((4.375 : ℝ)
      * ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖))
      ≤ (2.64 : ℝ) :=
    le_trans hmono3 hMul
  have hle2 : ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖
      * (4.375 * 4.375 * 4.375) ≤ (2.64 : ℝ) := by
    have heq : ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖
        * (4.375 * 4.375 * 4.375)
        = (4.375 : ℝ) * ((4.375 : ℝ) * ((4.375 : ℝ)
          * ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖)) := by
      ring
    rw [heq]
    exact hle
  have hdiv : ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖
      ≤ (2.64 : ℝ) / (4.375 * 4.375 * 4.375) := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4.375 * 4.375 * 4.375)]
    exact hle2
  have h032 : (2.64 : ℝ) / (4.375 * 4.375 * 4.375) ≤ (0.032 : ℝ) := by norm_num
  exact le_trans hdiv h032

#print axioms D3SG_gamNeed_outer_shift3_upper

/-- Outer shift-3 gap: `0.032` is above `0.002` (gap, no close). -/
theorem D3SG_gamNeed_outer_shift3_gap :
    (0.002 : ℝ) < (0.032 : ℝ) := by norm_num

#print axioms D3SG_gamNeed_outer_shift3_gap

/-- Outer shift-3 ratio: `0.032 / 0.002 = 16`, so gap factor exceeds `15`. -/
theorem D3SG_gamNeed_outer_shift3_ratio :
    (15 : ℝ) < (0.032 : ℝ) / (0.002 : ℝ) := by norm_num

#print axioms D3SG_gamNeed_outer_shift3_ratio

/-! ## GAMNEED-LEAF-SHIFT3 (STIRLING-LEAF3, 2026-09-22).

Grep first (this file unless noted):
* outer shift-3 shape: `D3SG_Real_Gamma_31975_le_two_sixfour` at `:2907`
  (`Real.Gamma 3.1975 ≤ 2.64` via `Γ 3.1975 = 2.1975 * Γ 2.1975`, reusing
  `D3SG_Real_Gamma_21975_le_one_two` at `:2556`), quotient
  `D3SG_gamNeed_outer_shift3_upper` at `:2923` (`‖Γ(mk 0.1975 (-4.375))‖ ≤ 0.032`
  via `2.64 / (4.375 ^ 3) ≈ 0.03152`, three-step shift into `Re = 3.1975`,
  `‖w‖ ≥ 4.375`, `‖w+1‖ ≥ 4.375`, `‖w+2‖ ≥ 4.375` from `|Im|` lowers),
  gap `:3077`, ratio `:3083` (`16x`).
* leaf shift-2 shape: `D3SG_Real_Gamma_21_le_one_one` at `:2730`
  (`Real.Gamma 2.1 ≤ 1.1`), quotient `D3SG_gamNeed_leaf_shift2_upper` at `:2750`
  (`‖Γ(mk 0.1 (-3.375))‖ ≤ 0.097` via `1.1 / (3.375 * 3.375) ≈ 0.09657`,
  two-step shift into `Re = 2.1`), gap `:2863`, ratio `:2870` (`12x`).

Leaf shift-3 mirror (honest, same chain at leaf point): `wLeaf+3` has
`Re = 3.1`, so `‖Γ(w+3)‖ ≤ Real.Gamma 3.1 ≤ 2.31` by domination +
`D3SG_Real_Gamma_31_le_two_three_one`
(`Γ 3.1 = 2.1 * Γ 2.1 ≤ 2.1 * 1.1 = 2.31`, reusing
`D3SG_Real_Gamma_21_le_one_one`). Paying `‖w‖ ≥ 3.375`,
`‖w+1‖ ≥ 3.375`, `‖w+2‖ ≥ 3.375` (`|Im|` lowers) gives
`‖Γ w‖ ≤ 2.31 / (3.375 ^ 3) ≈ 0.06009 ≤ 0.061`.
That is `0.061 / 0.008 = 7.625`, i.e. `≈ 7x` above `0.008`: IMPROVES the
shift-2 `12x` gap but does NOT close `gamNeed_leaf`. Filed as quotient +
gap + ratio below; residual stands.

Residual: `gamNeed_outer (≤ 0.002)` OPEN (`0.032` banked at `:2923`, `16x` gap);
`gamNeed_leaf (≤ 0.008)` OPEN (`0.061` banked here, `7x` gap; prior `0.097`
at `:2750` superseded as best quotient but gap remains).
-/

/-- Leaf shift-3 real cap: `Real.Gamma 3.1 ≤ 2.31`
(`Γ 3.1 = 2.1 * Γ 2.1 ≤ 2.1 * 1.1 ≤ 2.31`). -/
theorem D3SG_Real_Gamma_31_le_two_three_one : Real.Gamma 3.1 ≤ 2.31 := by
  have hne : (2.1 : ℝ) ≠ 0 := by norm_num
  have hshift : Real.Gamma (2.1 + 1) = 2.1 * Real.Gamma 2.1 :=
    Real.Gamma_add_one hne
  have heq : (2.1 : ℝ) + 1 = 3.1 := by norm_num
  rw [heq] at hshift
  rw [hshift]
  calc (2.1 : ℝ) * Real.Gamma 2.1
      ≤ 2.1 * 1.1 :=
        mul_le_mul_of_nonneg_left D3SG_Real_Gamma_21_le_one_one (by norm_num)
    _ ≤ 2.31 := by norm_num

#print axioms D3SG_Real_Gamma_31_le_two_three_one

/-- Leaf shift-3 quotient: `‖Γ(mk 0.1 (-3.375))‖ ≤ 0.061`
(`2.31 / (3.375 ^ 3) ≈ 0.06009`). Three-step shift into `Re = 3.1`. -/
theorem D3SG_gamNeed_leaf_shift3_upper :
    ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ ≤ (0.061 : ℝ) := by
  have hre3 : (((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1) + 1)).re
      = (3.1 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.one_re,
      Complex.one_re, Complex.one_re,
      show (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)).re = (0.1 : ℝ) from rfl]
    norm_num
  have him_w : (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)).im = (-3.375 : ℝ) := rfl
  have him_w1 : (((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1)).im
      = (-3.375 : ℝ) := by
    rw [Complex.add_im, Complex.one_im, him_w]
    norm_num
  have him_w2 : ((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1)).im
      = (-3.375 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.one_im, Complex.one_im, him_w]
    norm_num
  have habs_w : |(Complex.mk (0.1 : ℝ) (-3.375 : ℝ)).im| = (3.375 : ℝ) := by
    rw [him_w, abs_of_neg (by norm_num : (-3.375 : ℝ) < 0)]
    norm_num
  have habs_w1 : |(((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1)).im|
      = (3.375 : ℝ) := by
    rw [him_w1, abs_of_neg (by norm_num : (-3.375 : ℝ) < 0)]
    norm_num
  have habs_w2 : |((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1)).im|
      = (3.375 : ℝ) := by
    rw [him_w2, abs_of_neg (by norm_num : (-3.375 : ℝ) < 0)]
    norm_num
  have hnorm_w : (3.375 : ℝ) ≤ ‖(Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ := by
    have h := Complex.abs_im_le_norm (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))
    rw [habs_w] at h
    exact h
  have hnorm_w1 : (3.375 : ℝ)
      ≤ ‖(((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1))‖ := by
    have h := Complex.abs_im_le_norm (((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1))
    rw [habs_w1] at h
    exact h
  have hnorm_w2 : (3.375 : ℝ)
      ≤ ‖((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1))‖ := by
    have h := Complex.abs_im_le_norm ((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1))
    rw [habs_w2] at h
    exact h
  have hw0 : (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) ≠ 0 := by
    intro h
    have him0 : (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)).im = 0 := by
      rw [h]
      simp
    rw [him_w] at him0
    norm_num at him0
  have hw10 : (((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1)) ≠ 0 := by
    intro h
    have him0 : ((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1))).im = 0 := by
      rw [h]
      simp
    rw [him_w1] at him0
    norm_num at him0
  have hw20 : ((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1)) ≠ 0 := by
    intro h
    have him0 : (((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1))).im = 0 := by
      rw [h]
      simp
    rw [him_w2] at him0
    norm_num at him0
  have hG1 : Complex.Gamma (((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1))
      = (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) *
        Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) :=
    Complex.Gamma_add_one _ hw0
  have hG2 : Complex.Gamma ((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1))
      = (((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1)) *
        Complex.Gamma (((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1)) :=
    Complex.Gamma_add_one _ hw10
  have hG3 : Complex.Gamma (((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1) + 1))
      = ((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1)) *
        Complex.Gamma ((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1)) :=
    Complex.Gamma_add_one _ hw20
  have hGn1 : ‖Complex.Gamma (((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1))‖
      = ‖(Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ *
        ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ := by
    rw [hG1, norm_mul]
  have hGn2 : ‖Complex.Gamma ((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1))‖
      = ‖(((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1))‖ *
        ‖Complex.Gamma (((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1))‖ := by
    rw [hG2, norm_mul]
  have hGn3 : ‖Complex.Gamma (((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1) + 1))‖
      = ‖((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1))‖ *
        ‖Complex.Gamma ((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1))‖ := by
    rw [hG3, norm_mul]
  have hRe3_pos : (0 : ℝ)
      < (((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1) + 1)).re := by
    rw [hre3]
    norm_num
  have hDom : ‖Complex.Gamma (((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1) + 1))‖
      ≤ Real.Gamma (((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1) + 1)).re :=
    D3SG_Gamma_norm_le_real _ hRe3_pos
  rw [hre3] at hDom
  have hCap : ‖Complex.Gamma (((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1) + 1))‖
      ≤ (2.31 : ℝ) :=
    le_trans hDom D3SG_Real_Gamma_31_le_two_three_one
  have hMul : ‖((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1))‖ *
      (‖(((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1))‖ *
        (‖(Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ *
          ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖))
      ≤ (2.31 : ℝ) := by
    rw [← hGn1, ← hGn2, ← hGn3]
    exact hCap
  have hGamma_nn : (0 : ℝ)
      ≤ ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ :=
    norm_nonneg _
  have hmono1 : (3.375 : ℝ)
      * ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖
      ≤ ‖(Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ *
        ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ :=
    mul_le_mul_of_nonneg_right hnorm_w hGamma_nn
  have hmono2 : (3.375 : ℝ) * ((3.375 : ℝ)
      * ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖)
      ≤ ‖(((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1))‖ *
        (‖(Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ *
          ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖) :=
    mul_le_mul hnorm_w1 hmono1
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3.375) hGamma_nn)
      (norm_nonneg _)
  have hmono3 : (3.375 : ℝ) * ((3.375 : ℝ) * ((3.375 : ℝ)
      * ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖))
      ≤ ‖((((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1) + 1))‖ *
        (‖(((Complex.mk (0.1 : ℝ) (-3.375 : ℝ)) + 1))‖ *
          (‖(Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖ *
            ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖)) :=
    mul_le_mul hnorm_w2 hmono2
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3.375)
        (by norm_num : (0 : ℝ) ≤ 3.375)) hGamma_nn)
      (norm_nonneg _)
  have hle : (3.375 : ℝ) * ((3.375 : ℝ) * ((3.375 : ℝ)
      * ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖))
      ≤ (2.31 : ℝ) :=
    le_trans hmono3 hMul
  have hle2 : ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖
      * (3.375 * 3.375 * 3.375) ≤ (2.31 : ℝ) := by
    have heq : ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖
        * (3.375 * 3.375 * 3.375)
        = (3.375 : ℝ) * ((3.375 : ℝ) * ((3.375 : ℝ)
          * ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖)) := by
      ring
    rw [heq]
    exact hle
  have hdiv : ‖Complex.Gamma (Complex.mk (0.1 : ℝ) (-3.375 : ℝ))‖
      ≤ (2.31 : ℝ) / (3.375 * 3.375 * 3.375) := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3.375 * 3.375 * 3.375)]
    exact hle2
  have h061 : (2.31 : ℝ) / (3.375 * 3.375 * 3.375) ≤ (0.061 : ℝ) := by norm_num
  exact le_trans hdiv h061

#print axioms D3SG_gamNeed_leaf_shift3_upper

/-- Leaf shift-3 gap: `0.061` is above `0.008` (gap, no close). -/
theorem D3SG_gamNeed_leaf_shift3_gap :
    (0.008 : ℝ) < (0.061 : ℝ) := by norm_num

#print axioms D3SG_gamNeed_leaf_shift3_gap

/-- Leaf shift-3 ratio: `0.061 / 0.008 = 7.625`, so gap factor exceeds `7`. -/
theorem D3SG_gamNeed_leaf_shift3_ratio :
    (7 : ℝ) < (0.061 : ℝ) / (0.008 : ℝ) := by norm_num

#print axioms D3SG_gamNeed_leaf_shift3_ratio

/-! ## GAMNEED-OUTER-SHIFT4 (STIRLING-SHIFT4, 2026-09-22).

Grep first (this file unless noted):
* outer shift-3 shape: `D3SG_Real_Gamma_31975_le_two_sixfour` at `:2907`
  (`Real.Gamma 3.1975 ≤ 2.64` via `Γ 3.1975 = 2.1975 * Γ 2.1975`, reusing
  `D3SG_Real_Gamma_21975_le_one_two`), quotient
  `D3SG_gamNeed_outer_shift3_upper` at `:2923` (`‖Γ(mk 0.1975 (-4.375))‖ ≤ 0.032`
  via `2.64 / (4.375 ^ 3) ≈ 0.03152`, three-step shift into `Re = 3.1975`),
  gap `:3077`, ratio `:3083` (`16x`).
* leaf shift-3 shape: `D3SG_Real_Gamma_31_le_two_three_one` at `:3121`
  (`Real.Gamma 3.1 ≤ 2.31`), quotient `D3SG_gamNeed_leaf_shift3_upper` at `:3137`
  (`‖Γ(mk 0.1 (-3.375))‖ ≤ 0.061` via `2.31 / (3.375 ^ 3) ≈ 0.06009`),
  gap `:3291`, ratio `:3297` (`7x`).

Outer shift-4 mirror (honest, same chain at outer point): `wOuter+4` has
`Re = 4.1975`, so `‖Γ(w+4)‖ ≤ Real.Gamma 4.1975 ≤ 8.45` by domination +
`D3SG_Real_Gamma_41975_le_eight_fourfive`
(`Γ 4.1975 = 3.1975 * Γ 3.1975 ≤ 3.1975 * 2.64 ≤ 8.45`, reusing
`D3SG_Real_Gamma_31975_le_two_sixfour`). Paying `‖w‖ ≥ 4.375`,
`‖w+1‖ ≥ 4.375`, `‖w+2‖ ≥ 4.375`, `‖w+3‖ ≥ 4.375` (`|Im|` lowers) gives
`‖Γ w‖ ≤ 8.45 / (4.375 ^ 4) ≈ 0.02306 ≤ 0.024`.
That is `0.024 / 0.002 = 12`, i.e. `12x` above `0.002`: IMPROVES the
shift-3 `16x` gap but does NOT close `gamNeed_outer`. Filed as quotient +
gap + ratio below; residual stands.

Residual: `gamNeed_outer (≤ 0.002)` OPEN (`0.024` banked here, `12x` gap;
prior `0.032` at `:2923` superseded as best quotient but gap remains);
`gamNeed_leaf (≤ 0.008)` OPEN (`0.061` banked at `:3137`, `7x` gap).
-/

/-- Outer shift-4 real cap: `Real.Gamma 4.1975 ≤ 8.45`
(`Γ 4.1975 = 3.1975 * Γ 3.1975 ≤ 3.1975 * 2.64 ≤ 8.45`). -/
theorem D3SG_Real_Gamma_41975_le_eight_fourfive : Real.Gamma 4.1975 ≤ 8.45 := by
  have hne : (3.1975 : ℝ) ≠ 0 := by norm_num
  have hshift : Real.Gamma (3.1975 + 1) = 3.1975 * Real.Gamma 3.1975 :=
    Real.Gamma_add_one hne
  have heq : (3.1975 : ℝ) + 1 = 4.1975 := by norm_num
  rw [heq] at hshift
  rw [hshift]
  calc (3.1975 : ℝ) * Real.Gamma 3.1975
      ≤ 3.1975 * 2.64 :=
        mul_le_mul_of_nonneg_left D3SG_Real_Gamma_31975_le_two_sixfour (by norm_num)
    _ ≤ 8.45 := by norm_num

#print axioms D3SG_Real_Gamma_41975_le_eight_fourfive

/-- Outer shift-4 quotient: `‖Γ(mk 0.1975 (-4.375))‖ ≤ 0.024`
(`8.45 / (4.375 ^ 4) ≈ 0.02306`). Four-step shift into `Re = 4.1975`. -/
theorem D3SG_gamNeed_outer_shift4_upper :
    ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ ≤ (0.024 : ℝ) := by
  have hre4 : ((((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1)) + 1).re
      = (4.1975 : ℝ) := by
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.one_re, Complex.one_re, Complex.one_re, Complex.one_re,
      show (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)).re = (0.1975 : ℝ) from rfl]
    norm_num
  have him_w : (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)).im = (-4.375 : ℝ) := rfl
  have him_w1 : (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1)).im
      = (-4.375 : ℝ) := by
    rw [Complex.add_im, Complex.one_im, him_w]
    norm_num
  have him_w2 : ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1)).im
      = (-4.375 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.one_im, Complex.one_im, him_w]
    norm_num
  have him_w3 : (((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1)).im
      = (-4.375 : ℝ) := by
    rw [Complex.add_im, Complex.add_im, Complex.add_im,
      Complex.one_im, Complex.one_im, Complex.one_im, him_w]
    norm_num
  have habs_w : |(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)).im| = (4.375 : ℝ) := by
    rw [him_w, abs_of_neg (by norm_num : (-4.375 : ℝ) < 0)]
    norm_num
  have habs_w1 : |(((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1)).im|
      = (4.375 : ℝ) := by
    rw [him_w1, abs_of_neg (by norm_num : (-4.375 : ℝ) < 0)]
    norm_num
  have habs_w2 : |((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1)).im|
      = (4.375 : ℝ) := by
    rw [him_w2, abs_of_neg (by norm_num : (-4.375 : ℝ) < 0)]
    norm_num
  have habs_w3 : |(((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1)).im|
      = (4.375 : ℝ) := by
    rw [him_w3, abs_of_neg (by norm_num : (-4.375 : ℝ) < 0)]
    norm_num
  have hnorm_w : (4.375 : ℝ) ≤ ‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ := by
    have h := Complex.abs_im_le_norm (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))
    rw [habs_w] at h
    exact h
  have hnorm_w1 : (4.375 : ℝ)
      ≤ ‖(((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖ := by
    have h := Complex.abs_im_le_norm (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))
    rw [habs_w1] at h
    exact h
  have hnorm_w2 : (4.375 : ℝ)
      ≤ ‖((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))‖ := by
    have h := Complex.abs_im_le_norm ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))
    rw [habs_w2] at h
    exact h
  have hnorm_w3 : (4.375 : ℝ)
      ≤ ‖(((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1))‖ := by
    have h := Complex.abs_im_le_norm (((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1))
    rw [habs_w3] at h
    exact h
  have hw0 : (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) ≠ 0 := by
    intro h
    have him0 : (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)).im = 0 := by
      rw [h]
      simp
    rw [him_w] at him0
    norm_num at him0
  have hw10 : (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1)) ≠ 0 := by
    intro h
    have him0 : ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))).im = 0 := by
      rw [h]
      simp
    rw [him_w1] at him0
    norm_num at him0
  have hw20 : ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1)) ≠ 0 := by
    intro h
    have him0 : (((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))).im = 0 := by
      rw [h]
      simp
    rw [him_w2] at him0
    norm_num at him0
  have hw30 : (((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1)) ≠ 0 := by
    intro h
    have him0 : ((((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1))).im = 0 := by
      rw [h]
      simp
    rw [him_w3] at him0
    norm_num at him0
  have hG1 : Complex.Gamma (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))
      = (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) *
        Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) :=
    Complex.Gamma_add_one _ hw0
  have hG2 : Complex.Gamma ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))
      = (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1)) *
        Complex.Gamma (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1)) :=
    Complex.Gamma_add_one _ hw10
  have hG3 : Complex.Gamma (((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1))
      = ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1)) *
        Complex.Gamma ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1)) :=
    Complex.Gamma_add_one _ hw20
  have hG4 : Complex.Gamma ((((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1)) + 1)
      = (((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1)) *
        Complex.Gamma (((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1)) :=
    Complex.Gamma_add_one _ hw30
  have hGn1 : ‖Complex.Gamma (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖
      = ‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ *
        ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ := by
    rw [hG1, norm_mul]
  have hGn2 : ‖Complex.Gamma ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))‖
      = ‖(((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖ *
        ‖Complex.Gamma (((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖ := by
    rw [hG2, norm_mul]
  have hGn3 : ‖Complex.Gamma (((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1))‖
      = ‖((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))‖ *
        ‖Complex.Gamma ((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))‖ := by
    rw [hG3, norm_mul]
  have hGn4 : ‖Complex.Gamma ((((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1)) + 1)‖
      = ‖(((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1))‖ *
        ‖Complex.Gamma (((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1))‖ := by
    rw [hG4, norm_mul]
  have hRe4_pos : (0 : ℝ)
      < ((((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1)) + 1).re := by
    rw [hre4]
    norm_num
  have hDom : ‖Complex.Gamma ((((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1)) + 1)‖
      ≤ Real.Gamma ((((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1)) + 1).re :=
    D3SG_Gamma_norm_le_real _ hRe4_pos
  rw [hre4] at hDom
  have hCap : ‖Complex.Gamma ((((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1)) + 1)‖
      ≤ (8.45 : ℝ) :=
    le_trans hDom D3SG_Real_Gamma_41975_le_eight_fourfive
  have hMul : ‖(((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1))‖ *
      (‖((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))‖ *
        (‖(((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖ *
          (‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ *
            ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖)))
      ≤ (8.45 : ℝ) := by
    rw [← hGn1, ← hGn2, ← hGn3, ← hGn4]
    exact hCap
  have hGamma_nn : (0 : ℝ)
      ≤ ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ :=
    norm_nonneg _
  have hmono1 : (4.375 : ℝ)
      * ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖
      ≤ ‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ *
        ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ :=
    mul_le_mul_of_nonneg_right hnorm_w hGamma_nn
  have hmono2 : (4.375 : ℝ) * ((4.375 : ℝ)
      * ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖)
      ≤ ‖(((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖ *
        (‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ *
          ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖) :=
    mul_le_mul hnorm_w1 hmono1
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4.375) hGamma_nn)
      (norm_nonneg _)
  have hmono3 : (4.375 : ℝ) * ((4.375 : ℝ) * ((4.375 : ℝ)
      * ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖))
      ≤ ‖((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))‖ *
        (‖(((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖ *
          (‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ *
            ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖)) :=
    mul_le_mul hnorm_w2 hmono2
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4.375)
        (by norm_num : (0 : ℝ) ≤ 4.375)) hGamma_nn)
      (norm_nonneg _)
  have hmono4 : (4.375 : ℝ) * ((4.375 : ℝ) * ((4.375 : ℝ) * ((4.375 : ℝ)
      * ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖)))
      ≤ ‖(((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1) + 1))‖ *
        (‖((((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1) + 1))‖ *
          (‖(((Complex.mk (0.1975 : ℝ) (-4.375 : ℝ)) + 1))‖ *
            (‖(Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖ *
              ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖))) :=
    mul_le_mul hnorm_w3 hmono3
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4.375)
        (by norm_num : (0 : ℝ) ≤ 4.375)) (by norm_num : (0 : ℝ) ≤ 4.375)) hGamma_nn)
      (norm_nonneg _)
  have hle : (4.375 : ℝ) * ((4.375 : ℝ) * ((4.375 : ℝ) * ((4.375 : ℝ)
      * ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖)))
      ≤ (8.45 : ℝ) :=
    le_trans hmono4 hMul
  have hle2 : ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖
      * (4.375 * 4.375 * 4.375 * 4.375) ≤ (8.45 : ℝ) := by
    have heq : ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖
        * (4.375 * 4.375 * 4.375 * 4.375)
        = (4.375 : ℝ) * ((4.375 : ℝ) * ((4.375 : ℝ) * ((4.375 : ℝ)
          * ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖))) := by
      ring
    rw [heq]
    exact hle
  have hdiv : ‖Complex.Gamma (Complex.mk (0.1975 : ℝ) (-4.375 : ℝ))‖
      ≤ (8.45 : ℝ) / (4.375 * 4.375 * 4.375 * 4.375) := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4.375 * 4.375 * 4.375 * 4.375)]
    exact hle2
  have h024 : (8.45 : ℝ) / (4.375 * 4.375 * 4.375 * 4.375) ≤ (0.024 : ℝ) := by norm_num
  exact le_trans hdiv h024

#print axioms D3SG_gamNeed_outer_shift4_upper

/-- Outer shift-4 gap: `0.024` is above `0.002` (gap, no close). -/
theorem D3SG_gamNeed_outer_shift4_gap :
    (0.002 : ℝ) < (0.024 : ℝ) := by norm_num

#print axioms D3SG_gamNeed_outer_shift4_gap

/-- Outer shift-4 ratio: `0.024 / 0.002 = 12`, so gap factor exceeds `11`. -/
theorem D3SG_gamNeed_outer_shift4_ratio :
    (11 : ℝ) < (0.024 : ℝ) / (0.002 : ℝ) := by norm_num

#print axioms D3SG_gamNeed_outer_shift4_ratio
