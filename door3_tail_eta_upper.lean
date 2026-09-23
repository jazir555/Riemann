import zeta_rigorous

open Complex Real Set Topology
open scoped BigOperators

noncomputable section

/-!
  A hypothesis-free eta-pair upper on the part of the high-height strip with
  `1/4 ≤ Re s ≤ 1/2`.  This is a small but useful feeder for the Door-3/FE
  tail route: unlike the old `R02` rectangle, its denominator is bounded away
  from zero directly by `Re s ≤ 1/2`.
-/

namespace Door3TailEtaUpper

private theorem eta_s2_upper {s : ℂ} (hsre : (0 : ℝ) ≤ s.re) :
    ‖∑ k ∈ Finset.range 2, etaDirichletTerm s k‖ ≤ (2 : ℝ) := by
  have h0 : etaDirichletTerm s 0 = 1 := by
    simp only [etaDirichletTerm]
    simp
  have hterm1_eq : etaDirichletTerm s 1 =
      -1 / ((((2 : ℕ)) : ℂ) ^ s) := by
    simp only [etaDirichletTerm]
    norm_num
  have h2cast : ((((2 : ℕ)) : ℂ)) = (((2 : ℝ) : ℂ)) := by norm_num
  have h2norm : ‖((((2 : ℕ)) : ℂ) ^ s)‖ = (2 : ℝ) ^ s.re := by
    rw [h2cast]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
  have h2ge : (1 : ℝ) ≤ (2 : ℝ) ^ s.re := by
    exact le_trans (by norm_num)
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hsre)
  have h1_norm : ‖etaDirichletTerm s 1‖ ≤ 1 := by
    rw [hterm1_eq, norm_div, norm_neg, norm_one, h2norm]
    rw [div_le_one (Real.rpow_pos_of_pos (by norm_num) _)]
    exact h2ge
  have hsum2 : (∑ k ∈ Finset.range 2, etaDirichletTerm s k) =
      etaDirichletTerm s 0 + etaDirichletTerm s 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
  rw [hsum2, h0]
  calc
    ‖(1 : ℂ) + etaDirichletTerm s 1‖ ≤
        ‖(1 : ℂ)‖ + ‖etaDirichletTerm s 1‖ := norm_add_le _ _
    _ ≤ 1 + 1 := by rw [norm_one]; linarith
    _ = 2 := by norm_num

theorem eta_factor_ge_two_fifths {s : ℂ} (hs : s.re ≤ (1 / 2 : ℝ)) :
    (2 / 5 : ℝ) ≤ ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ := by
  let q : ℂ := (2 : ℂ) ^ ((1 : ℂ) - s)
  have hqnorm : ‖q‖ = (2 : ℝ) ^ ((1 - s).re) := by
    dsimp [q]
    have hb : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
    rw [hb]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
  have hexp : (1 / 2 : ℝ) ≤ (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hsqrt : (7 / 5 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := by
    have hsq : (7 / 5 : ℝ) ^ (2 : ℕ) ≤ (2 : ℝ) := by norm_num
    have hpow : ((2 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← hpow] at hsq
    exact le_of_pow_le_pow_left₀ (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _).le hsq
  have hqge : (7 / 5 : ℝ) ≤ ‖q‖ := by
    rw [hqnorm]
    exact le_trans hsqrt
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
  have htri := norm_add_le (q - 1) (1 : ℂ)
  have hqdecomp : q - 1 + 1 = q := by ring
  rw [hqdecomp, norm_one, norm_sub_rev] at htri
  linarith

theorem eta_pair_sum_upper_quarter {s : ℂ}
    (hsre : (1 / 4 : ℝ) ≤ s.re) (hsnorm : ‖s‖ ≤ 12) :
    ‖∑' m, etaPairTerm s m‖ ≤ (50 : ℝ) := by
  have hspos : 0 < s.re := by linarith
  have htail := zetaCell_even_remainder_le hspos hsnorm
    (by norm_num : (0 : ℝ) ≤ 12) 1 (by norm_num)
  have hone : ((((1 : ℕ)) : ℝ) ^ (-s.re)) = 1 := by
    rw [Nat.cast_one, Real.one_rpow]
  rw [hone] at htail
  have hdiv : (12 : ℝ) / s.re ≤ 48 := by
    apply (div_le_iff₀ hspos).2
    nlinarith
  have htail0 : ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range 2, etaDirichletTerm s k)‖ ≤ (48 : ℝ) := by
    have htail' : ‖(∑' m, etaPairTerm s m) -
        (∑ k ∈ Finset.range 2, etaDirichletTerm s k)‖ ≤ (12 : ℝ) / s.re := by
      simpa [div_eq_mul_inv] using htail
    exact le_trans htail' hdiv
  have hS2 : ‖∑ k ∈ Finset.range 2, etaDirichletTerm s k‖ ≤ (2 : ℝ) :=
    eta_s2_upper (by linarith)
  have htri := norm_add_le (∑ k ∈ Finset.range 2, etaDirichletTerm s k)
    ((∑' m, etaPairTerm s m) - (∑ k ∈ Finset.range 2, etaDirichletTerm s k))
  rw [add_sub_cancel] at htri
  linarith

/-! A coarser companion remains useful below `Re s = 1/4`: the same paired
tail estimate with `M = 1` costs only `12 / Re s`, hence gives a fully
unconditional finite upper on the tenth-line strip. -/

theorem eta_pair_sum_upper_tenth {s : ℂ}
    (hsre : (1 / 10 : ℝ) ≤ s.re) (hsnorm : ‖s‖ ≤ 12) :
    ‖∑' m, etaPairTerm s m‖ ≤ (122 : ℝ) := by
  have hspos : 0 < s.re := by linarith
  have htail := zetaCell_even_remainder_le hspos hsnorm
    (by norm_num : (0 : ℝ) ≤ 12) 1 (by norm_num)
  have hone : ((((1 : ℕ)) : ℝ) ^ (-s.re)) = 1 := by
    rw [Nat.cast_one, Real.one_rpow]
  rw [hone] at htail
  have hdiv : (12 : ℝ) / s.re ≤ 120 := by
    apply (div_le_iff₀ hspos).2
    nlinarith
  have htail0 : ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range 2, etaDirichletTerm s k)‖ ≤ (120 : ℝ) := by
    have htail' : ‖(∑' m, etaPairTerm s m) -
        (∑ k ∈ Finset.range 2, etaDirichletTerm s k)‖ ≤ (12 : ℝ) / s.re := by
      simpa [div_eq_mul_inv] using htail
    exact le_trans htail' hdiv
  have hS2 : ‖∑ k ∈ Finset.range 2, etaDirichletTerm s k‖ ≤ (2 : ℝ) :=
    eta_s2_upper (by linarith)
  have htri := norm_add_le (∑ k ∈ Finset.range 2, etaDirichletTerm s k)
    ((∑' m, etaPairTerm s m) - (∑ k ∈ Finset.range 2, etaDirichletTerm s k))
  rw [add_sub_cancel] at htri
  linarith

theorem zeta_upper_tenth_threequarters {s : ℂ}
    (hsre_lo : (1 / 10 : ℝ) ≤ s.re) (hsre_hi : s.re ≤ (3 / 4 : ℝ))
    (hsnorm : ‖s‖ ≤ 12) :
    ‖riemannZeta s‖ ≤ (1220 : ℝ) := by
  have hspos : 0 < s.re := by linarith
  have hre : s.re ≠ 1 := by linarith
  have hZ := zeta_of_etaPairLim_of_re_ne hspos hre
  rw [hZ, norm_div]
  have hnum := eta_pair_sum_upper_tenth hsre_lo hsnorm
  let q : ℂ := (2 : ℂ) ^ ((1 : ℂ) - s)
  have hqnorm : (11 / 10 : ℝ) ≤ ‖q‖ := by
    dsimp [q]
    rw [two_cpow_one_sub_norm]
    have hexp : (1 / 4 : ℝ) ≤ 1 - s.re := by linarith
    have hroot : (11 / 10 : ℝ) ≤ (2 : ℝ) ^ (1 / 4 : ℝ) := by
      have hpow : ((11 / 10 : ℝ) ^ (4 : ℕ)) ≤ (2 : ℝ) := by norm_num
      have hpow' : (((2 : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℕ)) = 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [← hpow'] at hpow
      exact le_of_pow_le_pow_left₀ (by norm_num)
        (Real.rpow_pos_of_pos (by norm_num) _).le hpow
    exact le_trans hroot
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
  have hden : (1 / 10 : ℝ) ≤ ‖(1 : ℂ) - q‖ := by
    have hrev := norm_sub_norm_le q (1 : ℂ)
    rw [norm_one, norm_sub_rev] at hrev
    linarith
  have hdenpos : 0 < ‖(1 : ℂ) - q‖ :=
    lt_of_lt_of_le (by norm_num) hden
  have hscale : (122 : ℝ) ≤ 1220 * ‖(1 : ℂ) - q‖ := by
    nlinarith
  have hle : ‖∑' m, etaPairTerm s m‖ ≤
      1220 * ‖(1 : ℂ) - q‖ := le_trans hnum hscale
  apply (div_le_iff₀ hdenpos).2
  simpa [q] using hle

theorem zeta_upper_tail_quarter {s : ℂ}
    (hsre_lo : (1 / 4 : ℝ) ≤ s.re) (hsre_hi : s.re ≤ (1 / 2 : ℝ))
    (him : |s.im| ≤ 11) :
    ‖riemannZeta s‖ ≤ (125 : ℝ) := by
  have hspos : 0 < s.re := by linarith
  have hre : s.re ≠ 1 := by linarith
  have hZ := zeta_of_etaPairLim_of_re_ne hspos hre
  rw [hZ, norm_div]
  have hnorm : ‖s‖ ≤ 12 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    have hreabs : |s.re| ≤ (1 / 2 : ℝ) := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hnum := eta_pair_sum_upper_quarter hsre_lo hnorm
  have hden := eta_factor_ge_two_fifths hsre_hi
  have hdenpos : 0 < ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ :=
    lt_of_lt_of_le (by norm_num) hden
  apply (div_le_iff₀ hdenpos).2
  have hscale : (50 : ℝ) ≤ 125 *
      ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ := by
    nlinarith
  exact le_trans hnum hscale

/-! The complex-Gamma numeral needed by the FE tail bridge.  The integral
majorant reduces it to a real-Gamma bound; convexity on `[1,2]` and the
recurrence then give the uniform constant `2` on `1/2 ≤ Re s ≤ 1`. -/

theorem realGamma_half_one_le_two {x : ℝ}
    (hx0 : (1 / 2 : ℝ) ≤ x) (hx1 : x ≤ 1) :
    Real.Gamma x ≤ 2 := by
  have hxpos : 0 < x := by linarith
  have hy_lo : (1 : ℝ) ≤ x + 1 := by linarith
  have hy_hi : x + 1 ≤ (2 : ℝ) := by linarith
  have hconv := Real.convexOn_Gamma
  have ha_nn : (0 : ℝ) ≤ 2 - (x + 1) := by linarith
  have hb_nn : (0 : ℝ) ≤ (x + 1) - 1 := by linarith
  have hab : (2 - (x + 1)) + ((x + 1) - 1) = 1 := by ring
  have h := hconv.2
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
    ha_nn hb_nn hab
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
  have heq : (2 - (x + 1)) * 1 + ((x + 1) - 1) * 2 = x + 1 := by ring
  rw [heq] at h
  have hrhs : (2 - (x + 1)) * 1 + ((x + 1) - 1) * 1 = (1 : ℝ) := by ring
  rw [hrhs] at h
  have hadd := Real.Gamma_add_one (ne_of_gt hxpos)
  rw [show x + 1 = x + 1 by rfl, hadd] at h
  have hfin : Real.Gamma x ≤ 1 / x := by
    rw [le_div_iff₀ hxpos, mul_comm]
    exact h
  have hfrac : (1 : ℝ) / x ≤ 2 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hx0
    linarith
  exact le_trans hfin hfrac

theorem gamma_tail_upper {s : ℂ}
    (hre0 : (1 / 2 : ℝ) ≤ s.re) (hre1 : s.re ≤ 1) :
    ‖Complex.Gamma s‖ ≤ (2 : ℝ) := by
  have hpos : 0 < s.re := by linarith
  exact le_trans (zetaFE_norm_Gamma_le_realGamma hpos)
    (realGamma_half_one_le_two hre0 hre1)

#print axioms eta_factor_ge_two_fifths
#print axioms eta_pair_sum_upper_quarter
#print axioms eta_pair_sum_upper_tenth
#print axioms zeta_upper_tenth_threequarters
#print axioms zeta_upper_tail_quarter
#print axioms realGamma_half_one_le_two
#print axioms gamma_tail_upper

end Door3TailEtaUpper

/-! An unconditional FE tail-rectangle specialization.  The reflected point
`1-s` lies in the strip `1/2 ≤ Re ≤ 1` and has norm at most `12`, so the
eta-pair upper and the Gamma integral majorant discharge both symbolic inputs
of `zeta_tail_rect_of_chi_gamma`. -/

theorem zeta_tail_rect_upper_exp22 {s : ℂ}
    (hre0 : (1 / 4 : ℝ) ≤ s.re) (hre1 : s.re ≤ (1 / 2 : ℝ))
    (him_lo : (10 : ℝ) ≤ |s.im|) (him_hi : |s.im| ≤ 11) :
    ‖riemannZeta s‖ ≤ (5000 : ℝ) * Real.exp 22 := by
  have hnorm : ‖1 - s‖ ≤ (12 : ℝ) := by
    have h := Complex.norm_le_abs_re_add_abs_im (1 - s)
    have hre : |(1 - s).re| ≤ (1 : ℝ) := by
      rw [Complex.sub_re, Complex.one_re]
      rw [abs_le]
      constructor <;> linarith
    have him : |(1 - s).im| ≤ (11 : ℝ) := by
      simpa [Complex.sub_im, abs_neg] using him_hi
    linarith [h]
  have hG : ‖Complex.Gamma (1 - s)‖ ≤ (2 : ℝ) := by
    apply Door3TailEtaUpper.gamma_tail_upper
    · rw [Complex.sub_re, Complex.one_re]
      linarith
    · rw [Complex.sub_re, Complex.one_re]
      linarith
  have hZ : ‖riemannZeta (1 - s)‖ ≤ (1220 : ℝ) := by
    apply Door3TailEtaUpper.zeta_upper_tenth_threequarters
    · rw [Complex.sub_re, Complex.one_re]
      linarith
    · rw [Complex.sub_re, Complex.one_re]
      linarith
    · exact hnorm
  have h := zeta_tail_rect_of_chi_gamma (by linarith : (0 : ℝ) ≤ s.re)
    hre1 him_lo him_hi
    (2 : ℝ) (1220 : ℝ) hG hZ
  calc
    ‖riemannZeta s‖ ≤ (2 * 1 * 2 * Real.exp 22) * 1220 := h
    _ = (4880 : ℝ) * Real.exp 22 := by ring_nf
    _ ≤ (5000 : ℝ) * Real.exp 22 := by
      have he : (0 : ℝ) ≤ Real.exp 22 := (Real.exp_pos _).le
      nlinarith

#print axioms zeta_tail_rect_upper_exp22

/-! The same certificate in the shifted Door 3 coordinates. -/

theorem zeta_shifted_tail_rect_upper_exp22 {z : ℂ}
    (hre0 : (10 : ℝ) ≤ |z.re|) (hre1 : |z.re| ≤ 11)
    (him0 : 0 ≤ z.im) (him1 : z.im ≤ (1 / 4 : ℝ)) :
    ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * z)‖ ≤
      (5000 : ℝ) * Real.exp 22 := by
  apply zeta_tail_rect_upper_exp22
  · simp only [Complex.add_re, Complex.I_mul_re]
    norm_num
    linarith
  · simp only [Complex.add_re, Complex.I_mul_re]
    norm_num
    linarith
  · simp only [Complex.add_im, Complex.I_mul_im]
    norm_num
    exact hre0
  · simp only [Complex.add_im, Complex.I_mul_im]
    norm_num
    exact hre1

#print axioms zeta_shifted_tail_rect_upper_exp22



namespace Door3TailEtaUpper
def etaPairRGeneral (t : ℝ) (m : ℕ) : ℝ :=
  ((((2 * m + 1 : ℕ) : ℝ) ^ (-t)) -
   (((2 * m + 2 : ℕ) : ℝ) ^ (-t)))

lemma etaPairTerm_ofReal (t : ℝ) (m : ℕ) :
    etaPairTerm (t : ℂ) m = (etaPairRGeneral t m : ℂ) := by
  rw [etaPairTerm_eq_cpow_sub]
  unfold etaPairRGeneral
  have h1 := Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ (((2 * m + 1 : ℕ) : ℝ))) (-t)
  have h2 := Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ (((2 * m + 2 : ℕ) : ℝ))) (-t)
  have he : ((-t : ℝ) : ℂ) = -(t : ℂ) := by simp
  rw [he] at h1 h2
  rw [← h1, ← h2]
  simp

lemma etaPairRGeneral_pos {t : ℝ} (ht : 0 < t) (m : ℕ) :
    0 < etaPairRGeneral t m := by
  unfold etaPairRGeneral
  have h1 : (0 : ℝ) < (((2 * m + 1 : ℕ) : ℝ)) := by positivity
  have hle : (((2 * m + 1 : ℕ) : ℝ)) < (((2 * m + 2 : ℕ) : ℝ)) := by norm_num
  have hpow : (((2 * m + 1 : ℕ) : ℝ) ^ (-t)) >
      (((2 * m + 2 : ℕ) : ℝ) ^ (-t)) := by
    exact Real.rpow_lt_rpow_of_neg h1 hle (by linarith)
  linarith

lemma etaPairRGeneral_summable {t : ℝ} (ht : 0 < t) :
    Summable (etaPairRGeneral t) := by
  have h := summable_etaPairTerm (s := (t : ℂ)) (by simpa using ht)
  have hc : Summable (fun m => (etaPairRGeneral t m : ℂ)) :=
    h.congr (fun m => etaPairTerm_ofReal t m)
  exact summable_ofReal.mp hc

lemma etaPairLim_real_pos {t : ℝ} (ht0 : 0 < t) :
    0 < ∑' m, etaPairRGeneral t m := by
  apply Summable.tsum_pos (etaPairRGeneral_summable ht0)
  · intro m
    exact (etaPairRGeneral_pos ht0 m).le
  · exact etaPairRGeneral_pos ht0 0

lemma zeta_real_nonzero_critical {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    riemannZeta (t : ℂ) ≠ 0 := by
  have hpos : 0 < (t : ℂ).re := by simpa using ht0
  have hne : (t : ℂ).re ≠ 1 := by simpa using (ne_of_lt ht1)
  have hz := zeta_of_etaPairLim_of_re_ne hpos hne
  intro hz0
  rw [hz] at hz0
  have hfac : (1 - (2 : ℂ) ^ (1 - (t : ℂ))) ≠ 0 :=
    etaFactor_ne_zero_of_re_ne hne
  have hsum : (∑' m, etaPairTerm (t : ℂ) m) = 0 := by
    exact (div_eq_zero_iff.mp hz0).resolve_right hfac
  have hsumC : ((∑' m, etaPairRGeneral t m : ℝ) : ℂ) = 0 := by
    rw [Complex.ofReal_tsum]
    simpa only [etaPairTerm_ofReal] using hsum
  have hsumR : (∑' m, etaPairRGeneral t m : ℝ) = 0 :=
    Complex.ofReal_inj.mp hsumC
  linarith [etaPairLim_real_pos ht0]

lemma zeta_real_nonzero_positive {t : ℝ} (ht : 0 < t) :
    riemannZeta (t : ℂ) ≠ 0 := by
  by_cases hlt : t < 1
  · exact zeta_real_nonzero_critical ht hlt
  by_cases heq : t = 1
  · subst t
    simpa using riemannZeta_one_ne_zero
  have hgt : (1 : ℝ) < t :=
    lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
  exact riemannZeta_ne_zero_of_one_lt_re (by simpa using hgt)

/-! The open imaginary axis is another unconditional zeta feeder.  The
functional equation moves a hypothetical zero at `Re s = 0` to `Re (1-s)=1`,
where the Euler-product nonvanishing theorem applies. -/

lemma zeta_re_zero_nonzero {s : ℂ} (hRe : s.re = 0) (hIm : s.im ≠ 0) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hs1 : s ≠ 1 := by
    intro h
    have hr := congr_arg Complex.re h
    simp [hRe] at hr
  have hs_ne : ∀ n : ℕ, s ≠ -n := by
    intro n h
    have hi := congr_arg Complex.im h
    simp at hi
    exact hIm hi
  have h1s_re : (1 - s).re = 1 := by simp [Complex.sub_re, hRe]
  have h1s_ne1 : 1 - s ≠ 1 := by
    intro h
    have hi := congr_arg Complex.im h
    simp only [Complex.sub_im, Complex.one_im] at hi
    exact hIm (by linarith)
  have hz1 : riemannZeta (1 - s) = 0 := by
    rw [riemannZeta_one_sub hs_ne hs1, hz, mul_zero]
  exact riemannZeta_ne_zero_of_one_le_re (by rw [h1s_re]) hz1

/-- Rpow value for the generic `M = 16384` tail (`16384^{1/2} = 128` exact;
generic mirror of `sSCUT_M8192_rpow_ge` at pilot `:4797`; honest via
`128^2 = 16384` by `norm_num`; `16384 = 2^14` so the root is exact, unlike
`8192^{1/2} ≈ 90.509`). -/
theorem M16384_rpow_eq :
    ((((16384 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (128 : ℝ) := by
  have hx2 : ((((((16384 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((16384 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((128 : ℝ) ^ (2 : ℕ)) = ((((16384 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((16384 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (128 : ℝ) := by norm_num
  have hle1 : ((((((16384 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((128 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((128 : ℝ) ^ (2 : ℕ)) ≤
      ((((((16384 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 16384` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/128 = 3/16`; generic mirror of `sSCUT_r_8192_le`
at pilot `:4812`; decay recomputed honestly with `norm_num` via the exact
`M16384_rpow_eq`; tightest honest `T'' = 3/16 = 0.1875` for this root). -/
theorem r_16384_le :
    (12 : ℝ) * ((((((16384 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 16 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((16384 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M16384_rpow_eq
  have hrw : ((((16384 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((16384 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((128 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 16 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 16384` (`‖G - S32768‖ ≤ 3/16`; generic mirror
of `sSCUT_eta_tail_8192_le` at pilot `:4837` — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_16384_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 16384), etaDirichletTerm s k)‖ ≤
      (3 / 16 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 16384 (by norm_num)
  have h2M : 2 * 16384 = 32768 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_16384_le
  linarith

/-- The `M = 16384` constant honestly improves on the banked `M = 8192`
constant (`3/16 = 0.1875 < 48/181 ≈ 0.26519`). -/
theorem tail_16384_lt_8192 : (3 / 16 : ℝ) < (48 / 181 : ℝ) := by
  norm_num

/-- Rpow lower for the generic `M = 32768` tail (`181 ≤ 32768^{1/2}`;
generic mirror of `M16384_rpow_eq` at `:408` and `sSCUT_M8192_rpow_ge` at
pilot `:4797`; honest floor via `181^2 = 32761 ≤ 32768` by `norm_num`;
`32768 = 2^15` so root `128·√2 ≈ 181.02` is NOT exact, unlike `16384`). -/
theorem M32768_rpow_ge :
    (181 : ℝ) ≤ ((((32768 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((181 : ℝ) ^ (2 : ℕ)) ≤ ((((32768 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((32768 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((32768 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 32768` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/181`; generic mirror of `r_16384_le` at `:433`
and `sSCUT_r_8192_le` at pilot `:4812`; decay recomputed honestly with
`norm_num` via `M32768_rpow_ge`; tightest honest `T''' = 24/181 ≈ 0.1326`
for the `181` root lower). -/
theorem r_32768_le :
    (12 : ℝ) * ((((((32768 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 181 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((32768 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((32768 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M32768_rpow_ge
  have hrw : ((((32768 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((32768 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((32768 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (181 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((32768 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (181 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((32768 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((181 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((181 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 181 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 32768` (`‖G - S65536‖ ≤ 24/181`; generic mirror
of `eta_tail_16384_le` at `:449` and `sSCUT_eta_tail_8192_le` at pilot `:4837`
— numerals use only `Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_32768_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 32768), etaDirichletTerm s k)‖ ≤
      (24 / 181 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 32768 (by norm_num)
  have h2M : 2 * 32768 = 65536 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_32768_le
  linarith

/-- The `M = 32768` constant honestly improves on the banked `M = 16384`
constant (`24/181 ≈ 0.1326 < 3/16 = 0.1875`). -/
theorem tail_32768_lt_16384 : (24 / 181 : ℝ) < (3 / 16 : ℝ) := by
  norm_num

/-- Rpow value for the generic `M = 65536` tail (`65536^{1/2} = 256` exact;
generic mirror of `M16384_rpow_eq` at `:408` and `M32768_rpow_ge` at `:471`;
honest via `256^2 = 65536` by `norm_num`; `65536 = 2^16` so the root is exact,
unlike `32768`). -/
theorem M65536_rpow_eq :
    ((((65536 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (256 : ℝ) := by
  have hx2 : ((((((65536 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((65536 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((256 : ℝ) ^ (2 : ℕ)) = ((((65536 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((65536 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (256 : ℝ) := by norm_num
  have hle1 : ((((((65536 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((256 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((256 : ℝ) ^ (2 : ℕ)) ≤
      ((((((65536 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 65536` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/256 = 3/32`; generic mirror of `r_32768_le`
at `:487` and `r_16384_le` at `:433`; decay recomputed honestly with
`norm_num` via the exact `M65536_rpow_eq`; tightest honest `T'''' = 3/32 =
0.09375` for this root). -/
theorem r_65536_le :
    (12 : ℝ) * ((((((65536 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 32 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((65536 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M65536_rpow_eq
  have hrw : ((((65536 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((65536 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((256 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 32 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 65536` (`‖G - S131072‖ ≤ 3/32`; generic mirror
of `eta_tail_32768_le` at `:513` and `eta_tail_16384_le` at `:449`
— numerals use only `Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_65536_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 65536), etaDirichletTerm s k)‖ ≤
      (3 / 32 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 65536 (by norm_num)
  have h2M : 2 * 65536 = 131072 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_65536_le
  linarith

/-- The `M = 65536` constant honestly improves on the banked `M = 32768`
constant (`3/32 = 0.09375 < 24/181 ≈ 0.1326`). -/
theorem tail_65536_lt_32768 : (3 / 32 : ℝ) < (24 / 181 : ℝ) := by
  norm_num

/-- Rpow lower for the generic `M = 131072` tail (`362 ≤ 131072^{1/2}`;
generic mirror of `M65536_rpow_eq` at `:535` and `M32768_rpow_ge` at `:471`;
honest floor via `362^2 = 131044 ≤ 131072` by `norm_num`;
`131072 = 2^17` so root `256·√2 ≈ 362.04` is NOT exact, unlike `65536`). -/
theorem M131072_rpow_ge :
    (362 : ℝ) ≤ ((((131072 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((362 : ℝ) ^ (2 : ℕ)) ≤ ((((131072 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((131072 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((131072 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 131072` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/362`; generic mirror of `r_65536_le`
at `:561` and `r_32768_le` at `:487`; decay recomputed honestly with
`norm_num` via `M131072_rpow_ge`; tightest honest `T''''' = 24/362 ≈ 0.0663`
for the `362` root lower). -/
theorem r_131072_le :
    (12 : ℝ) * ((((((131072 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 362 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((131072 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((131072 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M131072_rpow_ge
  have hrw : ((((131072 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((131072 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((131072 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (362 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((131072 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (362 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((131072 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((362 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((362 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 362 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 131072` (`‖G - S262144‖ ≤ 24/362`; generic mirror
of `eta_tail_65536_le` at `:577` and `eta_tail_32768_le` at `:513`
— numerals use only `Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_131072_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 131072), etaDirichletTerm s k)‖ ≤
      (24 / 362 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 131072 (by norm_num)
  have h2M : 2 * 131072 = 262144 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_131072_le
  linarith

/-- The `M = 131072` constant honestly improves on the banked `M = 65536`
constant (`24/362 ≈ 0.0663 < 3/32 = 0.09375`). -/
theorem tail_131072_lt_65536 : (24 / 362 : ℝ) < (3 / 32 : ℝ) := by
  norm_num

/-- Rpow value for the generic `M = 262144` tail (`262144^{1/2} = 512` exact;
generic mirror of `M65536_rpow_eq` at `:535` and `M16384_rpow_eq` at `:408`;
honest via `512^2 = 262144` by `norm_num`; `262144 = 2^18` so the root is exact,
unlike `131072`). -/
theorem M262144_rpow_eq :
    ((((262144 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (512 : ℝ) := by
  have hx2 : ((((((262144 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((262144 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((512 : ℝ) ^ (2 : ℕ)) = ((((262144 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((262144 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (512 : ℝ) := by norm_num
  have hle1 : ((((((262144 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((512 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((512 : ℝ) ^ (2 : ℕ)) ≤
      ((((((262144 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 262144` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/512 = 3/64`; generic mirror of `r_65536_le`
at `:561` and `r_16384_le` at `:433`; decay recomputed honestly with
`norm_num` via the exact `M262144_rpow_eq`; tightest honest `T'''''' = 3/64 =
0.046875` for this root). -/
theorem r_262144_le :
    (12 : ℝ) * ((((((262144 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 64 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((262144 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M262144_rpow_eq
  have hrw : ((((262144 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((262144 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((512 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 64 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 262144` (`‖G - S524288‖ ≤ 3/64`; generic mirror
of `eta_tail_65536_le` at `:577` and `eta_tail_32768_le` at `:513`
— numerals use only `Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_262144_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 262144), etaDirichletTerm s k)‖ ≤
      (3 / 64 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 262144 (by norm_num)
  have h2M : 2 * 262144 = 524288 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_262144_le
  linarith

/-- The `M = 262144` constant honestly improves on the banked `M = 131072`
constant (`3/64 = 0.046875 < 24/362 ≈ 0.0663`). -/
theorem tail_262144_lt_131072 : (3 / 64 : ℝ) < (24 / 362 : ℝ) := by
  norm_num

#print axioms M131072_rpow_ge
#print axioms r_131072_le
#print axioms eta_tail_131072_le
#print axioms tail_131072_lt_65536

#print axioms M65536_rpow_eq
#print axioms r_65536_le
#print axioms eta_tail_65536_le
#print axioms tail_65536_lt_32768

#print axioms M32768_rpow_ge
#print axioms r_32768_le
#print axioms eta_tail_32768_le
#print axioms tail_32768_lt_16384

#print axioms M16384_rpow_eq
#print axioms r_16384_le
#print axioms eta_tail_16384_le
#print axioms tail_16384_lt_8192


#print axioms zeta_real_nonzero_critical
#print axioms zeta_real_nonzero_positive
#print axioms zeta_re_zero_nonzero

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 524288` tail (`724 ≤ 524288^{1/2}`;
generic mirror of `M131072_rpow_ge` at `:599` and latest exact `M262144_rpow_eq`
at `:663`; honest floor via `724^2 = 524176 ≤ 524288` by `norm_num`;
`524288 = 2^19` so root `512·√2 ≈ 724.07` is NOT exact, unlike `262144`). -/
theorem M524288_rpow_ge :
    (724 : ℝ) ≤ ((((524288 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((724 : ℝ) ^ (2 : ℕ)) ≤ ((((524288 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((524288 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((524288 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 524288` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/724`; generic mirror of `r_131072_le`
at `:615` and latest exact `r_262144_le` at `:689`; decay recomputed honestly
with `norm_num` via `M524288_rpow_ge`; tightest honest `T = 24/724 ≈ 0.03315`
for the `724` root lower). -/
theorem r_524288_le :
    (12 : ℝ) * ((((((524288 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 724 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((524288 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((524288 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M524288_rpow_ge
  have hrw : ((((524288 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((524288 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((524288 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (724 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((524288 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (724 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((524288 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((724 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((724 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 724 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 524288` (`‖G - S1048576‖ ≤ 24/724`; generic mirror
of `eta_tail_131072_le` at `:641` and latest exact `eta_tail_262144_le` at `:705`
— numerals use only `Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_524288_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 524288), etaDirichletTerm s k)‖ ≤
      (24 / 724 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 524288 (by norm_num)
  have h2M : 2 * 524288 = 1048576 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_524288_le
  linarith

/-- The `M = 524288` constant honestly improves on the banked `M = 262144`
constant (`24/724 ≈ 0.03315 < 3/64 = 0.046875`). -/
theorem tail_524288_lt_262144 : (24 / 724 : ℝ) < (3 / 64 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 1048576` tail (`1048576^{1/2} = 1024` exact;
exact shape mirror of `M262144_rpow_eq` at `:663-682` and `M524288_rpow_ge` at
`:756-765`; honest via `1024^2 = 1048576` by `norm_num`; `1048576 = 2^20` so the
root is exact, unlike `524288`). -/
theorem M1048576_rpow_eq :
    ((((1048576 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (1024 : ℝ) := by
  have hx2 : ((((((1048576 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((1048576 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((1024 : ℝ) ^ (2 : ℕ)) = ((((1048576 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((1048576 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (1024 : ℝ) := by norm_num
  have hle1 : ((((((1048576 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((1024 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((1024 : ℝ) ^ (2 : ℕ)) ≤
      ((((((1048576 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 1048576` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/1024 = 3/128`; exact shape mirror of `r_262144_le`
at `:689-700` and `r_524288_le` at `:772-793`; decay recomputed honestly with
`norm_num` via the exact `M1048576_rpow_eq`; tightest honest `T = 3/128 =
0.0234375` for this root). -/
theorem r_1048576_le :
    (12 : ℝ) * ((((((1048576 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 128 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((1048576 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M1048576_rpow_eq
  have hrw : ((((1048576 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((1048576 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((1024 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 128 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 1048576` (`‖G - S2097152‖ ≤ 3/128`; exact shape
mirror of `eta_tail_262144_le` at `:705-716` and `eta_tail_524288_le` at
`:798-809` — numerals use only `Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_1048576_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 1048576), etaDirichletTerm s k)‖ ≤
      (3 / 128 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1048576 (by norm_num)
  have h2M : 2 * 1048576 = 2097152 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_1048576_le
  linarith

/-- The `M = 1048576` constant honestly improves on the banked `M = 524288`
constant (`3/128 = 0.0234375 < 24/724 ≈ 0.03315`). -/
theorem tail_1048576_lt_524288 : (3 / 128 : ℝ) < (24 / 724 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 2097152` tail (`1448 ≤ 2097152^{1/2}`;
generic mirror of `M524288_rpow_ge` at `:756` and latest exact `M1048576_rpow_eq`
at `:824`; honest floor via `1448^2 = 2096704 ≤ 2097152` by `norm_num`;
`2097152 = 2^21` so root `1024·√2 ≈ 1448.15` is NOT exact; lower gap `448`,
upper witness `1449^2 = 2099601 = 2097152 + 2449`). -/
theorem M2097152_rpow_ge :
    (1448 : ℝ) ≤ ((((2097152 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((1448 : ℝ) ^ (2 : ℕ)) ≤ ((((2097152 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((2097152 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((2097152 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 2097152` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/1448`; generic mirror of `r_524288_le`
at `:772` and latest exact `r_1048576_le` at `:850`; decay recomputed honestly
with `norm_num` via `M2097152_rpow_ge`; tightest honest `T = 24/1448 = 3/181 ≈
0.01657` for the `1448` root lower). -/
theorem r_2097152_le :
    (12 : ℝ) * ((((((2097152 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 1448 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((2097152 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((2097152 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M2097152_rpow_ge
  have hrw : ((((2097152 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((2097152 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((2097152 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (1448 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((2097152 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (1448 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((2097152 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((1448 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((1448 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 1448 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 2097152` (`‖G - S4194304‖ ≤ 24/1448`; generic mirror
of `eta_tail_524288_le` at `:798` and latest exact `eta_tail_1048576_le` at
`:866` — numerals use only `Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_2097152_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 2097152), etaDirichletTerm s k)‖ ≤
      (24 / 1448 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 2097152 (by norm_num)
  have h2M : 2 * 2097152 = 4194304 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_2097152_le
  linarith

/-- The `M = 2097152` constant honestly improves on the banked `M = 1048576`
constant (`24/1448 = 3/181 ≈ 0.01657 < 3/128 = 0.0234375`). -/
theorem tail_2097152_lt_1048576 : (24 / 1448 : ℝ) < (3 / 128 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

theorem M4194304_rpow_eq :
    ((((4194304 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (2048 : ℝ) := by
  have hx2 : ((((((4194304 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((4194304 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((2048 : ℝ) ^ (2 : ℕ)) = ((((4194304 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((4194304 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (2048 : ℝ) := by norm_num
  have hle1 : ((((((4194304 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((2048 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((2048 : ℝ) ^ (2 : ℕ)) ≤
      ((((((4194304 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 4194304` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/2048 = 3/256`; exact shape mirror of `r_1048576_le`
at `:850-861`; decay recomputed honestly with `norm_num` via the exact
`M4194304_rpow_eq`; tightest honest `T = 3/256 = 0.01171875` for this root). -/
theorem r_4194304_le :
    (12 : ℝ) * ((((((4194304 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 256 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((4194304 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M4194304_rpow_eq
  have hrw : ((((4194304 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((4194304 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((2048 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 256 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 4194304` (`‖G - S8388608‖ ≤ 3/256`; exact shape
mirror of `eta_tail_1048576_le` at `:866-877` — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_4194304_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 4194304), etaDirichletTerm s k)‖ ≤
      (3 / 256 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 4194304 (by norm_num)
  have h2M : 2 * 4194304 = 8388608 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_4194304_le
  linarith

/-- The `M = 4194304` constant honestly improves on the banked `M = 2097152`
constant (`3/256 ≈ 0.01171875 < 24/1448 = 3/181 ≈ 0.01657`). -/
theorem tail_4194304_lt_2097152 : (3 / 256 : ℝ) < (24 / 1448 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 8388608` tail (`2896 ≤ 8388608^{1/2}`;
generic mirror of `M2097152_rpow_ge` at `:893` and latest exact `M4194304_rpow_eq`
at `:957`; honest floor via `2896^2 = 8386816 ≤ 8388608` by `norm_num`;
`8388608 = 2^23` so root `2048·√2 ≈ 2896.31` is NOT exact; lower gap `1792`,
upper witness `2897^2 = 8392609 = 8388608 + 4001`). -/
theorem M8388608_rpow_ge :
    (2896 : ℝ) ≤ ((((8388608 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((2896 : ℝ) ^ (2 : ℕ)) ≤ ((((8388608 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((8388608 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((8388608 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 8388608` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/2896`; generic mirror of `r_2097152_le`
at `:909` and latest exact `r_4194304_le` at `:982`; decay recomputed honestly
with `norm_num` via `M8388608_rpow_ge`; tightest honest `T = 24/2896 = 3/362 ≈
0.00829` for the `2896` root lower). -/
theorem r_8388608_le :
    (12 : ℝ) * ((((((8388608 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 2896 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((8388608 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((8388608 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M8388608_rpow_ge
  have hrw : ((((8388608 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((8388608 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((8388608 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (2896 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((8388608 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (2896 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((8388608 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((2896 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((2896 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 2896 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 8388608` (`‖G - S16777216‖ ≤ 24/2896`; generic mirror
of `eta_tail_2097152_le` at `:935` and latest exact `eta_tail_4194304_le` at
`:998` — numerals use only `Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_8388608_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 8388608), etaDirichletTerm s k)‖ ≤
      (24 / 2896 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 8388608 (by norm_num)
  have h2M : 2 * 8388608 = 16777216 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_8388608_le
  linarith

/-- The `M = 8388608` constant honestly improves on the banked `M = 4194304`
constant (`24/2896 = 3/362 ≈ 0.00829 < 3/256 = 0.01171875`). -/
theorem tail_8388608_lt_4194304 : (24 / 2896 : ℝ) < (3 / 256 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

theorem M16777216_rpow_eq :
    ((((16777216 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (4096 : ℝ) := by
  have hx2 : ((((((16777216 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((16777216 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((4096 : ℝ) ^ (2 : ℕ)) = ((((16777216 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((16777216 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (4096 : ℝ) := by norm_num
  have hle1 : ((((((16777216 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((4096 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((4096 : ℝ) ^ (2 : ℕ)) ≤
      ((((((16777216 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 16777216` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/4096 = 3/512`; exact shape mirror of `r_4194304_le`
at `:982-993`; decay recomputed honestly with `norm_num` via the exact
`M16777216_rpow_eq`; tightest honest `T = 3/512 = 0.005859375` for this root). -/
theorem r_16777216_le :
    (12 : ℝ) * ((((((16777216 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 512 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((16777216 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M16777216_rpow_eq
  have hrw : ((((16777216 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((16777216 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((4096 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 512 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 16777216` (`‖G - S33554432‖ ≤ 3/512`; exact shape
mirror of `eta_tail_4194304_le` at `:998-1009` — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_16777216_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 16777216), etaDirichletTerm s k)‖ ≤
      (3 / 512 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 16777216 (by norm_num)
  have h2M : 2 * 16777216 = 33554432 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_16777216_le
  linarith

/-- The `M = 16777216` constant honestly improves on the banked `M = 8388608`
constant (`3/512 ≈ 0.005859375 < 24/2896 = 3/362 ≈ 0.00829`). -/
theorem tail_16777216_lt_8388608 : (3 / 512 : ℝ) < (24 / 2896 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 33554432` tail (`5792 ≤ 33554432^{1/2}`;
generic mirror of `M8388608_rpow_ge` at `:1025-1034` and latest exact
`M16777216_rpow_eq` at `:1089-1108`; honest floor via `5792^2 = 33547264 ≤
33554432` by `norm_num`; `33554432 = 2^25` so root `4096·√2 ≈ 5792.62` is NOT
exact; lower gap `7168`, upper witness `5793^2 = 33558849 = 33554432 + 4417`). -/
theorem M33554432_rpow_ge :
    (5792 : ℝ) ≤ ((((33554432 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((5792 : ℝ) ^ (2 : ℕ)) ≤ ((((33554432 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((33554432 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((33554432 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 33554432` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/5792`; generic mirror of `r_8388608_le`
at `:1041-1062` and latest exact `r_16777216_le` at `:1114-1125`; decay
recomputed honestly with `norm_num` via `M33554432_rpow_ge`; tightest honest
`T = 24/5792 = 3/724 ≈ 0.00414` for the `5792` root lower). -/
theorem r_33554432_le :
    (12 : ℝ) * ((((((33554432 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 5792 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((33554432 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((33554432 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M33554432_rpow_ge
  have hrw : ((((33554432 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((33554432 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((33554432 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (5792 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((33554432 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (5792 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((33554432 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((5792 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((5792 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 5792 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 33554432` (`‖G - S67108864‖ ≤ 24/5792`; generic
mirror of `eta_tail_8388608_le` at `:1067-1078` and latest exact
`eta_tail_16777216_le` at `:1130-1141` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_33554432_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 33554432), etaDirichletTerm s k)‖ ≤
      (24 / 5792 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 33554432 (by norm_num)
  have h2M : 2 * 33554432 = 67108864 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_33554432_le
  linarith

/-- The `M = 33554432` constant honestly improves on the banked `M = 16777216`
constant (`24/5792 = 3/724 ≈ 0.00414 < 3/512 ≈ 0.005859375`). -/
theorem tail_33554432_lt_16777216 : (24 / 5792 : ℝ) < (3 / 512 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 67108864` tail (`67108864^{1/2} = 8192` exact;
exact shape mirror of `M16777216_rpow_eq` at `:1089-1108` and latest odd-floor
`M33554432_rpow_ge` at `:1157-1166`; honest via `8192^2 = 67108864` by `norm_num`;
`67108864 = 2^26` so the root is exact, unlike `33554432`). -/
theorem M67108864_rpow_eq :
    ((((67108864 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (8192 : ℝ) := by
  have hx2 : ((((((67108864 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((67108864 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((8192 : ℝ) ^ (2 : ℕ)) = ((((67108864 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((67108864 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (8192 : ℝ) := by norm_num
  have hle1 : ((((((67108864 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((8192 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((8192 : ℝ) ^ (2 : ℕ)) ≤
      ((((((67108864 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 67108864` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/8192 = 3/1024`; exact shape mirror of `r_16777216_le`
at `:1114-1125` and latest odd-floor `r_33554432_le` at `:1173-1194`; decay
recomputed honestly with `norm_num` via the exact `M67108864_rpow_eq`; tightest
honest `T = 3/1024 = 0.0029296875` for this root). -/
theorem r_67108864_le :
    (12 : ℝ) * ((((((67108864 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 1024 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((67108864 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M67108864_rpow_eq
  have hrw : ((((67108864 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((67108864 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((8192 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 1024 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 67108864` (`‖G - S134217728‖ ≤ 3/1024`; exact shape
mirror of `eta_tail_16777216_le` at `:1130-1141` and latest odd-floor
`eta_tail_33554432_le` at `:1200-1211` — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_67108864_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 67108864), etaDirichletTerm s k)‖ ≤
      (3 / 1024 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 67108864 (by norm_num)
  have h2M : 2 * 67108864 = 134217728 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_67108864_le
  linarith

/-- The `M = 67108864` constant honestly improves on the banked `M = 33554432`
constant (`3/1024 ≈ 0.0029296875 < 24/5792 = 3/724 ≈ 0.00414`). -/
theorem tail_67108864_lt_33554432 : (3 / 1024 : ℝ) < (24 / 5792 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 134217728` tail (`11585 ≤ 134217728^{1/2}`;
generic mirror of `M33554432_rpow_ge` at `:1157` and latest exact
`M67108864_rpow_eq` at `:1226`; honest floor via `11585^2 = 134212225 ≤
134217728` by `norm_num`; `134217728 = 2^27` so root `8192·√2 ≈ 11585.24` is NOT
exact; lower gap `5503`, upper witness `11586^2 = 134235396 = 134217728 +
17668`). -/
theorem M134217728_rpow_ge :
    (11585 : ℝ) ≤ ((((134217728 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((11585 : ℝ) ^ (2 : ℕ)) ≤ ((((134217728 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((134217728 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((134217728 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 134217728` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/11585`; generic mirror of `r_8388608_le`
at `:1041-1062` and latest exact `r_67108864_le` at `:1252-1263`; decay
recomputed honestly with `norm_num` via `M134217728_rpow_ge`; tightest honest
`T = 24/11585 ≈ 0.00207` for the `11585` root lower). -/
theorem r_134217728_le :
    (12 : ℝ) * ((((((134217728 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 11585 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((134217728 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((134217728 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M134217728_rpow_ge
  have hrw : ((((134217728 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((134217728 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((134217728 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (11585 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((134217728 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (11585 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((134217728 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((11585 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((11585 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 11585 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 134217728` (`‖G - S268435456‖ ≤ 24/11585`;
generic mirror of `eta_tail_8388608_le` at `:1067-1078` and latest exact
`eta_tail_67108864_le` at `:1269-1280` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_134217728_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 134217728), etaDirichletTerm s k)‖ ≤
      (24 / 11585 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 134217728 (by norm_num)
  have h2M : 2 * 134217728 = 268435456 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_134217728_le
  linarith

/-- The `M = 134217728` constant honestly improves on the banked `M = 67108864`
constant (`24/11585 ≈ 0.00207 < 3/1024 ≈ 0.0029296875`). -/
theorem tail_134217728_lt_67108864 : (24 / 11585 : ℝ) < (3 / 1024 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 268435456` tail (`268435456^{1/2} = 16384`
exact; exact shape mirror of `M16777216_rpow_eq` at `:1089-1108` and
`M67108864_rpow_eq` at `:1226-1245`; honest via `16384^2 = 268435456` by
`norm_num`; `268435456 = 2^28` so the root is exact, unlike `134217728`). -/
theorem M268435456_rpow_eq :
    ((((268435456 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (16384 : ℝ) := by
  have hx2 : ((((((268435456 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((268435456 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((16384 : ℝ) ^ (2 : ℕ)) = ((((268435456 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((268435456 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (16384 : ℝ) := by norm_num
  have hle1 : ((((((268435456 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((16384 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((16384 : ℝ) ^ (2 : ℕ)) ≤
      ((((((268435456 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 268435456` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/16384 = 3/2048`; exact shape mirror of
`r_16777216_le` at `:1114-1125` and `r_67108864_le` at `:1252-1263`; decay
recomputed honestly with `norm_num` via the exact `M268435456_rpow_eq`;
tightest honest `T = 3/2048 = 0.00146484375` for this root). -/
theorem r_268435456_le :
    (12 : ℝ) * ((((((268435456 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 2048 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((268435456 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M268435456_rpow_eq
  have hrw : ((((268435456 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((268435456 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((16384 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 2048 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 268435456` (`‖G - S536870912‖ ≤ 3/2048`; exact
shape mirror of `eta_tail_16777216_le` at `:1130-1141` and `eta_tail_67108864_le`
at `:1269-1280` — numerals use only `Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_268435456_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 268435456), etaDirichletTerm s k)‖ ≤
      (3 / 2048 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 268435456 (by norm_num)
  have h2M : 2 * 268435456 = 536870912 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_268435456_le
  linarith

/-- The `M = 268435456` constant honestly improves on the banked `M = 134217728`
constant (`3/2048 ≈ 0.00146484375 < 24/11585 ≈ 0.00207`). -/
theorem tail_268435456_lt_134217728 : (3 / 2048 : ℝ) < (24 / 11585 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 536870912` tail (`23170 ≤ 536870912^{1/2}`;
generic mirror of `M134217728_rpow_ge` at `:1297` and latest exact
`M268435456_rpow_eq` at `:1366`; honest floor via `23170^2 = 536848900 ≤
536870912` by `norm_num`; `536870912 = 2^29` so root `16384·√2 ≈ 23170.47` is NOT
exact; lower gap `22012`, upper witness `23171^2 = 536895241 = 536870912 +
24329`). -/
theorem M536870912_rpow_ge :
    (23170 : ℝ) ≤ ((((536870912 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((23170 : ℝ) ^ (2 : ℕ)) ≤ ((((536870912 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((536870912 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((536870912 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 536870912` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/23170`; generic mirror of `r_134217728_le`
at `:1313-1334` and latest exact `r_268435456_le` at `:1392-1403`; decay
recomputed honestly with `norm_num` via `M536870912_rpow_ge`; tightest honest
`T = 24/23170 = 12/11585 ≈ 0.00104` for the `23170` root lower). -/
theorem r_536870912_le :
    (12 : ℝ) * ((((((536870912 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 23170 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((536870912 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((536870912 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M536870912_rpow_ge
  have hrw : ((((536870912 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((536870912 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((536870912 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (23170 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((536870912 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (23170 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((536870912 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((23170 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((23170 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 23170 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 536870912` (`‖G - S1073741824‖ ≤ 24/23170`;
generic mirror of `eta_tail_134217728_le` at `:1340-1351` and latest exact
`eta_tail_268435456_le` at `:1408-1419` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_536870912_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 536870912), etaDirichletTerm s k)‖ ≤
      (24 / 23170 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 536870912 (by norm_num)
  have h2M : 2 * 536870912 = 1073741824 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_536870912_le
  linarith

/-- The `M = 536870912` constant honestly improves on the banked `M = 268435456`
constant (`24/23170 = 12/11585 ≈ 0.00104 < 3/2048 ≈ 0.00146484375`). -/
theorem tail_536870912_lt_268435456 : (24 / 23170 : ℝ) < (3 / 2048 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 1073741824` tail (`1073741824^{1/2} = 32768`
exact; exact shape mirror of `M268435456_rpow_eq` at `:1366-1385` and
`M4194304_rpow_eq` at `:957-976`; honest via `32768^2 = 1073741824` by
`norm_num`; `1073741824 = 2^30` so the root is exact, unlike `536870912`). -/
theorem M1073741824_rpow_eq :
    ((((1073741824 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (32768 : ℝ) := by
  have hx2 : ((((((1073741824 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((1073741824 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((32768 : ℝ) ^ (2 : ℕ)) = ((((1073741824 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((1073741824 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (32768 : ℝ) := by norm_num
  have hle1 : ((((((1073741824 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((32768 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((32768 : ℝ) ^ (2 : ℕ)) ≤
      ((((((1073741824 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 1073741824` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/32768 = 3/4096`; exact shape mirror of
`r_268435456_le` at `:1392-1403` and `r_4194304_le` at `:982-993`; decay
recomputed honestly with `norm_num` via the exact `M1073741824_rpow_eq`;
tightest honest `T = 3/4096 = 0.000732421875` for this root). -/
theorem r_1073741824_le :
    (12 : ℝ) * ((((((1073741824 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 4096 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((1073741824 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M1073741824_rpow_eq
  have hrw : ((((1073741824 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((1073741824 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((32768 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 4096 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 1073741824` (`‖G - S2147483648‖ ≤ 3/4096`; exact
shape mirror of `eta_tail_268435456_le` at `:1408-1419` and
`eta_tail_4194304_le` at `:998-1009` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_1073741824_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 1073741824), etaDirichletTerm s k)‖ ≤
      (3 / 4096 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1073741824 (by norm_num)
  have h2M : 2 * 1073741824 = 2147483648 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_1073741824_le
  linarith

/-- The `M = 1073741824` constant honestly improves on the banked `M = 536870912`
constant (`3/4096 ≈ 0.0007324 < 24/23170 = 12/11585 ≈ 0.00104`). -/
theorem tail_1073741824_lt_536870912 : (3 / 4096 : ℝ) < (24 / 23170 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 2147483648` tail (`46340 ≤ 2147483648^{1/2}`;
generic mirror of `M536870912_rpow_ge` at `:1436` and latest exact
`M1073741824_rpow_eq` at `:1505`; honest floor via `46340^2 = 2147395600 ≤
2147483648` by `norm_num`; `2147483648 = 2^31` so root `32768·√2 ≈ 46340.95` is NOT
exact; lower gap `88048`, upper witness `46341^2 = 2147488281 = 2147483648 +
4633`). -/
theorem M2147483648_rpow_ge :
    (46340 : ℝ) ≤ ((((2147483648 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((46340 : ℝ) ^ (2 : ℕ)) ≤ ((((2147483648 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((2147483648 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((2147483648 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 2147483648` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/46340`; generic mirror of `r_536870912_le`
at `:1452` and latest exact `r_1073741824_le` at `:1531`; decay recomputed honestly
with `norm_num` via `M2147483648_rpow_ge`; tightest honest
`T = 24/46340 = 12/23170 ≈ 0.000518` for the `46340` root lower). -/
theorem r_2147483648_le :
    (12 : ℝ) * ((((((2147483648 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 46340 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((2147483648 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((2147483648 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M2147483648_rpow_ge
  have hrw : ((((2147483648 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((2147483648 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((2147483648 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (46340 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((2147483648 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (46340 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((2147483648 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((46340 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((46340 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 46340 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 2147483648` (`‖G - S4294967296‖ ≤ 24/46340`;
generic mirror of `eta_tail_536870912_le` at `:1479` and latest exact
`eta_tail_1073741824_le` at `:1548` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_2147483648_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 2147483648), etaDirichletTerm s k)‖ ≤
      (24 / 46340 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 2147483648 (by norm_num)
  have h2M : 2 * 2147483648 = 4294967296 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_2147483648_le
  linarith

/-- The `M = 2147483648` constant honestly improves on the banked `M = 1073741824`
constant (`24/46340 = 12/23170 ≈ 0.000518 < 3/4096 ≈ 0.0007324`). -/
theorem tail_2147483648_lt_1073741824 : (24 / 46340 : ℝ) < (3 / 4096 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 4294967296` tail (`4294967296^{1/2} = 65536`
exact; exact shape mirror of `M1073741824_rpow_eq` at `:1505-1524` and
`M268435456_rpow_eq` at `:1366-1385`; honest via `65536^2 = 4294967296` by
`norm_num`; `4294967296 = 2^32` so the root is exact, unlike `2147483648`). -/
theorem M4294967296_rpow_eq :
    ((((4294967296 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (65536 : ℝ) := by
  have hx2 : ((((((4294967296 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((4294967296 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((65536 : ℝ) ^ (2 : ℕ)) = ((((4294967296 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((4294967296 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (65536 : ℝ) := by norm_num
  have hle1 : ((((((4294967296 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((65536 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((65536 : ℝ) ^ (2 : ℕ)) ≤
      ((((((4294967296 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 4294967296` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/65536 = 3/8192`; exact shape mirror of
`r_1073741824_le` at `:1531-1542` and `r_268435456_le` at `:1392-1403`; decay
recomputed honestly with `norm_num` via the exact `M4294967296_rpow_eq`;
tightest honest `T = 3/8192 = 0.0003662109375` for this root). -/
theorem r_4294967296_le :
    (12 : ℝ) * ((((((4294967296 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 8192 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((4294967296 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M4294967296_rpow_eq
  have hrw : ((((4294967296 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((4294967296 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((65536 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 8192 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 4294967296` (`‖G - S8589934592‖ ≤ 3/8192`; exact
shape mirror of `eta_tail_1073741824_le` at `:1548-1559` and
`eta_tail_268435456_le` at `:1408-1419` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_4294967296_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 4294967296), etaDirichletTerm s k)‖ ≤
      (3 / 8192 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 4294967296 (by norm_num)
  have h2M : 2 * 4294967296 = 8589934592 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_4294967296_le
  linarith

/-- The `M = 4294967296` constant honestly improves on the banked `M = 2147483648`
constant (`3/8192 ≈ 0.0003662 < 24/46340 = 12/23170 ≈ 0.000518`). -/
theorem tail_4294967296_lt_2147483648 : (3 / 8192 : ℝ) < (24 / 46340 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 8589934592` tail (`92681 ≤ 8589934592^{1/2}`;
generic mirror of `M2147483648_rpow_ge` at `:1576` and latest exact `M4294967296_rpow_eq`
at `:1645`; honest floor via `92681^2 = 8589767761 ≤ 8589934592` by `norm_num`;
`8589934592 = 2^33` so root `65536·√2 ≈ 92681.9` is NOT exact; lower gap `166831`,
upper witness `92682^2 = 8589953124 = 8589934592 + 18532`). -/
theorem M8589934592_rpow_ge :
    (92681 : ℝ) ≤ ((((8589934592 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((92681 : ℝ) ^ (2 : ℕ)) ≤ ((((8589934592 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((8589934592 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((8589934592 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 8589934592` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/92681`; generic mirror of `r_2147483648_le`
at `:1592` and latest exact `r_4294967296_le` at `:1671`; decay recomputed honestly
with `norm_num` via `M8589934592_rpow_ge`; tightest honest
`T = 24/92681 ≈ 0.000259` for the `92681` root lower). -/
theorem r_8589934592_le :
    (12 : ℝ) * ((((((8589934592 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 92681 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((8589934592 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((8589934592 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M8589934592_rpow_ge
  have hrw : ((((8589934592 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((8589934592 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((8589934592 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (92681 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((8589934592 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (92681 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((8589934592 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((92681 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((92681 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 92681 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 8589934592` (`‖G - S17179869184‖ ≤ 24/92681`;
generic mirror of `eta_tail_2147483648_le` at `:1619` and latest exact
`eta_tail_4294967296_le` at `:1688` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_8589934592_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 8589934592), etaDirichletTerm s k)‖ ≤
      (24 / 92681 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 8589934592 (by norm_num)
  have h2M : 2 * 8589934592 = 17179869184 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_8589934592_le
  linarith

/-- The `M = 8589934592` constant honestly improves on the banked `M = 4294967296`
constant (`24/92681 ≈ 0.000259 < 3/8192 ≈ 0.0003662`). -/
theorem tail_8589934592_lt_4294967296 : (24 / 92681 : ℝ) < (3 / 8192 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 17179869184` tail (`17179869184^{1/2} = 131072`
exact; exact shape mirror of `M4294967296_rpow_eq` at `:1645-1664` and
`M268435456_rpow_eq` at `:1366-1385`; honest via `131072^2 = 17179869184` by
`norm_num`; `17179869184 = 2^34` so the root is exact, unlike `8589934592`). -/
theorem M17179869184_rpow_eq :
    ((((17179869184 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (131072 : ℝ) := by
  have hx2 : ((((((17179869184 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((17179869184 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((131072 : ℝ) ^ (2 : ℕ)) = ((((17179869184 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((17179869184 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (131072 : ℝ) := by norm_num
  have hle1 : ((((((17179869184 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((131072 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((131072 : ℝ) ^ (2 : ℕ)) ≤
      ((((((17179869184 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 17179869184` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/131072 = 3/16384`; exact shape mirror of
`r_4294967296_le` at `:1671-1682`; decay recomputed honestly with `norm_num`
via the exact `M17179869184_rpow_eq`; tightest honest `T = 3/16384 =
0.00018310546875` for this root). -/
theorem r_17179869184_le :
    (12 : ℝ) * ((((((17179869184 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 16384 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((17179869184 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M17179869184_rpow_eq
  have hrw : ((((17179869184 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((17179869184 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((131072 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 16384 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 17179869184` (`‖G - S34359738368‖ ≤ 3/16384`;
exact shape mirror of `eta_tail_4294967296_le` at `:1688-1699` — numerals use
only `Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_17179869184_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 17179869184), etaDirichletTerm s k)‖ ≤
      (3 / 16384 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 17179869184 (by norm_num)
  have h2M : 2 * 17179869184 = 34359738368 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_17179869184_le
  linarith

/-- The `M = 17179869184` constant honestly improves on the banked `M = 8589934592`
constant (`3/16384 ≈ 0.0001831 < 24/92681 ≈ 0.000259`). -/
theorem tail_17179869184_lt_8589934592 : (3 / 16384 : ℝ) < (24 / 92681 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 34359738368` tail (`185363 ≤ 34359738368^{1/2}`;
generic mirror of `M8589934592_rpow_ge` at `:1715` and latest exact `M17179869184_rpow_eq`
at `:1784`; honest floor via `185363^2 = 34359441769 ≤ 34359738368` by `norm_num`;
`34359738368 = 2^35` so root `131072·√2 ≈ 185363.80` is NOT exact; lower gap `296599`,
upper witness `185364^2 = 34359812496 = 34359738368 + 74128`). -/
theorem M34359738368_rpow_ge :
    (185363 : ℝ) ≤ ((((34359738368 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((185363 : ℝ) ^ (2 : ℕ)) ≤ ((((34359738368 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((34359738368 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((34359738368 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 34359738368` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/185363`; generic mirror of `r_8589934592_le`
at `:1731` and latest exact `r_17179869184_le` at `:1810`; decay recomputed honestly
with `norm_num` via `M34359738368_rpow_ge`; tightest honest
`T = 24/185363 ≈ 0.0001295` for the `185363` root lower). -/
theorem r_34359738368_le :
    (12 : ℝ) * ((((((34359738368 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 185363 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((34359738368 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((34359738368 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M34359738368_rpow_ge
  have hrw : ((((34359738368 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((34359738368 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((34359738368 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (185363 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((34359738368 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (185363 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((34359738368 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((185363 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((185363 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 185363 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 34359738368` (`‖G - S68719476736‖ ≤ 24/185363`;
generic mirror of `eta_tail_8589934592_le` at `:1758` and latest exact
`eta_tail_17179869184_le` at `:1826` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_34359738368_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 34359738368), etaDirichletTerm s k)‖ ≤
      (24 / 185363 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 34359738368 (by norm_num)
  have h2M : 2 * 34359738368 = 68719476736 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_34359738368_le
  linarith

/-- The `M = 34359738368` constant honestly improves on the banked `M = 17179869184`
constant (`24/185363 ≈ 0.0001295 < 3/16384 ≈ 0.0001831`). -/
theorem tail_34359738368_lt_17179869184 : (24 / 185363 : ℝ) < (3 / 16384 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 68719476736` tail (`68719476736^{1/2} = 262144`
exact; exact shape mirror of `M17179869184_rpow_eq` at `:1784-1803` and
`M4194304_rpow_eq`; honest via `262144^2 = 68719476736` by `norm_num`;
`68719476736 = 2^36` so the root is exact, unlike `34359738368`). -/
theorem M68719476736_rpow_eq :
    ((((68719476736 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (262144 : ℝ) := by
  have hx2 : ((((((68719476736 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((68719476736 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((262144 : ℝ) ^ (2 : ℕ)) = ((((68719476736 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((68719476736 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (262144 : ℝ) := by norm_num
  have hle1 : ((((((68719476736 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((262144 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((262144 : ℝ) ^ (2 : ℕ)) ≤
      ((((((68719476736 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 68719476736` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/262144 = 3/32768`; exact shape mirror of
`r_17179869184_le` at `:1810-1821`; decay recomputed honestly with `norm_num`
via the exact `M68719476736_rpow_eq`; tightest honest `T = 3/32768 =
0.000091552734375` for this root). -/
theorem r_68719476736_le :
    (12 : ℝ) * ((((((68719476736 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 32768 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((68719476736 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M68719476736_rpow_eq
  have hrw : ((((68719476736 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((68719476736 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((262144 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 32768 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 68719476736` (`‖G - S137438953472‖ ≤ 3/32768`;
exact shape mirror of `eta_tail_17179869184_le` at `:1826-1837` — numerals use
only `Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_68719476736_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 68719476736), etaDirichletTerm s k)‖ ≤
      (3 / 32768 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 68719476736 (by norm_num)
  have h2M : 2 * 68719476736 = 137438953472 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_68719476736_le
  linarith

/-- The `M = 68719476736` constant honestly improves on the banked `M = 34359738368`
constant (`3/32768 ≈ 0.00009155 < 24/185363 ≈ 0.0001295`). -/
theorem tail_68719476736_lt_34359738368 : (3 / 32768 : ℝ) < (24 / 185363 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 137438953472` tail (`370727 ≤ 137438953472^{1/2}`;
generic mirror of `M34359738368_rpow_ge` at `:1853` and latest exact
`M68719476736_rpow_eq` at `:1922`; honest floor via `370727^2 = 137438508529 ≤
137438953472` by `norm_num`; `137438953472 = 2^37` so root `262144·√2 ≈ 370727.60`
is NOT exact; lower gap `444943`, upper witness `370728^2 = 137439249984 =
137438953472 + 296512`). -/
theorem M137438953472_rpow_ge :
    (370727 : ℝ) ≤ ((((137438953472 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((370727 : ℝ) ^ (2 : ℕ)) ≤ ((((137438953472 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((137438953472 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((137438953472 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 137438953472` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/370727`; generic mirror of `r_34359738368_le`
at `:1869` and latest exact `r_68719476736_le` at `:1948`; decay recomputed honestly
with `norm_num` via `M137438953472_rpow_ge`; tightest honest `T = 24/370727 ≈
0.00006474` for the `370727` root lower). -/
theorem r_137438953472_le :
    (12 : ℝ) * ((((((137438953472 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 370727 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((137438953472 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((137438953472 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M137438953472_rpow_ge
  have hrw : ((((137438953472 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((137438953472 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((137438953472 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (370727 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((137438953472 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (370727 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((137438953472 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((370727 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((370727 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 370727 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 137438953472` (`‖G - S274877906944‖ ≤ 24/370727`;
generic mirror of `eta_tail_34359738368_le` at `:1896` and latest exact
`eta_tail_68719476736_le` at `:1964` — numerals use only `Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_137438953472_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 137438953472), etaDirichletTerm s k)‖ ≤
      (24 / 370727 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 137438953472 (by norm_num)
  have h2M : 2 * 137438953472 = 274877906944 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_137438953472_le
  linarith

/-- The `M = 137438953472` constant honestly improves on the banked `M = 68719476736`
constant (`24/370727 ≈ 0.00006474 < 3/32768 ≈ 0.00009155`). -/
theorem tail_137438953472_lt_68719476736 : (24 / 370727 : ℝ) < (3 / 32768 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 274877906944` tail (`274877906944^{1/2} = 524288`
exact; exact shape mirror of `M68719476736_rpow_eq` at `:1922-1941` and
`M17179869184_rpow_eq` at `:1784-1803`; honest via `524288^2 = 274877906944` by
`norm_num`; `274877906944 = 2^38` so the root is exact, unlike `137438953472`). -/
theorem M274877906944_rpow_eq :
    ((((274877906944 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (524288 : ℝ) := by
  have hx2 : ((((((274877906944 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((274877906944 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((524288 : ℝ) ^ (2 : ℕ)) = ((((274877906944 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((274877906944 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (524288 : ℝ) := by norm_num
  have hle1 : ((((((274877906944 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((524288 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((524288 : ℝ) ^ (2 : ℕ)) ≤
      ((((((274877906944 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 274877906944` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/524288 = 3/65536`; exact shape mirror of
`r_68719476736_le` at `:1948-1959`; decay recomputed honestly with `norm_num`
via the exact `M274877906944_rpow_eq`; tightest honest `T = 3/65536 =
0.0000457763671875` for this root). -/
theorem r_274877906944_le :
    (12 : ℝ) * ((((((274877906944 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 65536 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((274877906944 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M274877906944_rpow_eq
  have hrw : ((((274877906944 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((274877906944 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((524288 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 65536 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 274877906944` (`‖G - S549755813888‖ ≤ 3/65536`;
exact shape mirror of `eta_tail_68719476736_le` at `:1964-1975` — numerals use
only `Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_274877906944_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 274877906944), etaDirichletTerm s k)‖ ≤
      (3 / 65536 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 274877906944 (by norm_num)
  have h2M : 2 * 274877906944 = 549755813888 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_274877906944_le
  linarith

/-- The `M = 274877906944` constant honestly improves on the banked `M = 137438953472`
constant (`3/65536 ≈ 0.00004578 < 24/370727 ≈ 0.00006474`). -/
theorem tail_274877906944_lt_137438953472 : (3 / 65536 : ℝ) < (24 / 370727 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 549755813888` tail (`741455 ≤ 549755813888^{1/2}`;
generic mirror of `M137438953472_rpow_ge` at `:1992` and latest exact
`M274877906944_rpow_eq` at `:2060`; honest floor via `741455^2 = 549755517025 ≤
549755813888` by `norm_num`; `549755813888 = 2^39` so root `524288·√2 ≈ 741455.20`
is NOT exact; lower gap `296863`, upper witness `741456^2 = 549756999936 =
549755813888 + 1186048`). -/
theorem M549755813888_rpow_ge :
    (741455 : ℝ) ≤ ((((549755813888 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((741455 : ℝ) ^ (2 : ℕ)) ≤ ((((549755813888 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((549755813888 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((549755813888 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 549755813888` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/741455`; generic mirror of `r_137438953472_le`
at `:2008` and latest exact `r_274877906944_le` at `:2086`; decay recomputed honestly
with `norm_num` via `M549755813888_rpow_ge`; tightest honest `T = 24/741455 ≈
0.00003237` for the `741455` root lower). -/
theorem r_549755813888_le :
    (12 : ℝ) * ((((((549755813888 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 741455 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((549755813888 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((549755813888 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M549755813888_rpow_ge
  have hrw : ((((549755813888 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((549755813888 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((549755813888 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (741455 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((549755813888 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (741455 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((549755813888 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((741455 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((741455 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 741455 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 549755813888` (`‖G - S1099511627776‖ ≤ 24/741455`;
generic mirror of `eta_tail_137438953472_le` at `:2034` and latest exact
`eta_tail_274877906944_le` at `:2102` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_549755813888_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 549755813888), etaDirichletTerm s k)‖ ≤
      (24 / 741455 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 549755813888 (by norm_num)
  have h2M : 2 * 549755813888 = 1099511627776 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_549755813888_le
  linarith

/-- The `M = 549755813888` constant honestly improves on the banked `M = 274877906944`
constant (`24/741455 ≈ 0.00003237 < 3/65536 ≈ 0.00004578`). -/
theorem tail_549755813888_lt_274877906944 : (24 / 741455 : ℝ) < (3 / 65536 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 1099511627776` tail (`1099511627776^{1/2} = 1048576`
exact; exact shape mirror of `M274877906944_rpow_eq` at `:2060-2079` and
`M68719476736_rpow_eq` at `:1922-1941`; honest via `1048576^2 = 1099511627776` by
`norm_num`; `1099511627776 = 2^40` so the root is exact, unlike `549755813888`). -/
theorem M1099511627776_rpow_eq :
    ((((1099511627776 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (1048576 : ℝ) := by
  have hx2 : ((((((1099511627776 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((1099511627776 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((1048576 : ℝ) ^ (2 : ℕ)) = ((((1099511627776 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((1099511627776 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (1048576 : ℝ) := by norm_num
  have hle1 : ((((((1099511627776 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((1048576 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((1048576 : ℝ) ^ (2 : ℕ)) ≤
      ((((((1099511627776 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 1099511627776` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/1048576 = 3/131072`; exact shape mirror of
`r_274877906944_le` at `:2086-2097`; decay recomputed honestly with `norm_num`
via the exact `M1099511627776_rpow_eq`; tightest honest `T = 3/131072 =
0.00002288818359375` for this root). -/
theorem r_1099511627776_le :
    (12 : ℝ) * ((((((1099511627776 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 131072 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((1099511627776 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M1099511627776_rpow_eq
  have hrw : ((((1099511627776 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((1099511627776 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((1048576 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 131072 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 1099511627776` (`‖G - S2199023255552‖ ≤ 3/131072`;
exact shape mirror of `eta_tail_274877906944_le` at `:2102-2113` — numerals use
only `Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_1099511627776_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 1099511627776), etaDirichletTerm s k)‖ ≤
      (3 / 131072 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1099511627776 (by norm_num)
  have h2M : 2 * 1099511627776 = 2199023255552 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_1099511627776_le
  linarith

/-- The `M = 1099511627776` constant honestly improves on the banked `M = 549755813888`
constant (`3/131072 ≈ 0.00002289 < 24/741455 ≈ 0.00003237`). -/
theorem tail_1099511627776_lt_549755813888 : (3 / 131072 : ℝ) < (24 / 741455 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 2199023255552` tail (`1482910 ≤ 2199023255552^{1/2}`;
generic mirror of `M549755813888_rpow_ge` at `:2130` and latest exact
`M1099511627776_rpow_eq` at `:2199`; honest floor via `1482910^2 = 2199022068100 ≤
2199023255552` by `norm_num`; `2199023255552 = 2^41` so root `1048576·√2 ≈ 1482910.40`
is NOT exact; lower gap `1187452`, upper witness `1482911^2 = 2199025033921 =
2199023255552 + 1778369`). -/
theorem M2199023255552_rpow_ge :
    (1482910 : ℝ) ≤ ((((2199023255552 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((1482910 : ℝ) ^ (2 : ℕ)) ≤ ((((2199023255552 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((2199023255552 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((2199023255552 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 2199023255552` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/1482910`; generic mirror of `r_549755813888_le`
at `:2146` and latest exact `r_1099511627776_le` at `:2225`; decay recomputed honestly
with `norm_num` via `M2199023255552_rpow_ge`; tightest honest `T = 24/1482910 ≈
0.00001618` for the `1482910` root lower). -/
theorem r_2199023255552_le :
    (12 : ℝ) * ((((((2199023255552 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 1482910 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((2199023255552 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((2199023255552 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M2199023255552_rpow_ge
  have hrw : ((((2199023255552 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((2199023255552 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((2199023255552 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (1482910 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((2199023255552 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (1482910 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((2199023255552 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((1482910 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((1482910 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 1482910 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 2199023255552` (`‖G - S4398046511104‖ ≤ 24/1482910`;
generic mirror of `eta_tail_549755813888_le` at `:2173` and latest exact
`eta_tail_1099511627776_le` at `:2241` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_2199023255552_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 2199023255552), etaDirichletTerm s k)‖ ≤
      (24 / 1482910 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 2199023255552 (by norm_num)
  have h2M : 2 * 2199023255552 = 4398046511104 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_2199023255552_le
  linarith

/-- The `M = 2199023255552` constant honestly improves on the banked `M = 1099511627776`
constant (`24/1482910 ≈ 0.00001618 < 3/131072 ≈ 0.00002289`). -/
theorem tail_2199023255552_lt_1099511627776 : (24 / 1482910 : ℝ) < (3 / 131072 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 4398046511104` tail (`4398046511104^{1/2} = 2097152`
exact; exact shape mirror of `M1099511627776_rpow_eq` at `:2199-2218` and
`M274877906944_rpow_eq` at `:2060-2079`; honest via `2097152^2 = 4398046511104` by
`norm_num`; `4398046511104 = 2^42` so the root is exact, unlike `2199023255552`). -/
theorem M4398046511104_rpow_eq :
    ((((4398046511104 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (2097152 : ℝ) := by
  have hx2 : ((((((4398046511104 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((4398046511104 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((2097152 : ℝ) ^ (2 : ℕ)) = ((((4398046511104 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((4398046511104 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (2097152 : ℝ) := by norm_num
  have hle1 : ((((((4398046511104 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((2097152 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((2097152 : ℝ) ^ (2 : ℕ)) ≤
      ((((((4398046511104 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 4398046511104` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/2097152 = 3/262144`; exact shape mirror of
`r_1099511627776_le` at `:2225-2236`; decay recomputed honestly with `norm_num`
via the exact `M4398046511104_rpow_eq`; tightest honest `T = 3/262144 =
0.000011444091796875` for this root). -/
theorem r_4398046511104_le :
    (12 : ℝ) * ((((((4398046511104 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 262144 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((4398046511104 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M4398046511104_rpow_eq
  have hrw : ((((4398046511104 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((4398046511104 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((2097152 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 262144 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 4398046511104` (`‖G - S8796093022208‖ ≤ 3/262144`;
exact shape mirror of `eta_tail_1099511627776_le` at `:2241-2252` — numerals use
only `Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_4398046511104_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 4398046511104), etaDirichletTerm s k)‖ ≤
      (3 / 262144 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 4398046511104 (by norm_num)
  have h2M : 2 * 4398046511104 = 8796093022208 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_4398046511104_le
  linarith

/-- The `M = 4398046511104` constant honestly improves on the banked `M = 2199023255552`
constant (`3/262144 ≈ 0.00001144 < 24/1482910 ≈ 0.00001618`). -/
theorem tail_4398046511104_lt_2199023255552 : (3 / 262144 : ℝ) < (24 / 1482910 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 8796093022208` tail (`2965820 ≤ 8796093022208^{1/2}`;
generic mirror of `M2199023255552_rpow_ge` at `:2269` and latest exact
`M4398046511104_rpow_eq` at `:2338`; honest floor via `2965820^2 = 8796088272400 ≤
8796093022208` by `norm_num`; `8796093022208 = 2^43` so root `2097152·√2 ≈ 2965820.80`
is NOT exact; lower gap `4749808`, upper witness `2965821^2 = 8796094204041 =
8796093022208 + 1181833`). -/
theorem M8796093022208_rpow_ge :
    (2965820 : ℝ) ≤ ((((8796093022208 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((2965820 : ℝ) ^ (2 : ℕ)) ≤ ((((8796093022208 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((8796093022208 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((8796093022208 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 8796093022208` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/2965820`; generic mirror of `r_2199023255552_le`
at `:2285` and latest exact `r_4398046511104_le` at `:2364`; decay recomputed honestly
with `norm_num` via `M8796093022208_rpow_ge`; tightest honest `T = 24/2965820 ≈
0.00000809` for the `2965820` root lower). -/
theorem r_8796093022208_le :
    (12 : ℝ) * ((((((8796093022208 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 2965820 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((8796093022208 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((8796093022208 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M8796093022208_rpow_ge
  have hrw : ((((8796093022208 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((8796093022208 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((8796093022208 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (2965820 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((8796093022208 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (2965820 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((8796093022208 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((2965820 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((2965820 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 2965820 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 8796093022208` (`‖G - S17592186044416‖ ≤ 24/2965820`;
generic mirror of `eta_tail_2199023255552_le` at `:2312` and latest exact
`eta_tail_4398046511104_le` at `:2380` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_8796093022208_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 8796093022208), etaDirichletTerm s k)‖ ≤
      (24 / 2965820 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 8796093022208 (by norm_num)
  have h2M : 2 * 8796093022208 = 17592186044416 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_8796093022208_le
  linarith

/-- The `M = 8796093022208` constant honestly improves on the banked `M = 4398046511104`
constant (`24/2965820 ≈ 0.00000809 < 3/262144 ≈ 0.00001144`). -/
theorem tail_8796093022208_lt_4398046511104 : (24 / 2965820 : ℝ) < (3 / 262144 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 17592186044416` tail (`17592186044416^{1/2} = 4194304`
exact; exact shape mirror of `M4398046511104_rpow_eq` at `:2338-2357` and latest odd-floor
`M8796093022208_rpow_ge` at `:2408-2417`; honest via `4194304^2 = 17592186044416` by
`norm_num`; `17592186044416 = 2^44` so the root is exact, unlike `8796093022208`). -/
theorem M17592186044416_rpow_eq :
    ((((17592186044416 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (4194304 : ℝ) := by
  have hx2 : ((((((17592186044416 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((17592186044416 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((4194304 : ℝ) ^ (2 : ℕ)) = ((((17592186044416 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((17592186044416 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (4194304 : ℝ) := by norm_num
  have hle1 : ((((((17592186044416 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((4194304 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((4194304 : ℝ) ^ (2 : ℕ)) ≤
      ((((((17592186044416 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 17592186044416` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/4194304 = 3/524288`; exact shape mirror of `r_4398046511104_le`
at `:2364-2375`; decay recomputed honestly with `norm_num` via the exact
`M17592186044416_rpow_eq`; tightest honest `T = 3/524288 = 0.0000057220458984375`
for this root). -/
theorem r_17592186044416_le :
    (12 : ℝ) * ((((((17592186044416 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 524288 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((17592186044416 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M17592186044416_rpow_eq
  have hrw : ((((17592186044416 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((17592186044416 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((4194304 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 524288 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 17592186044416` (`‖G - S35184372088832‖ ≤ 3/524288`;
exact shape mirror of `eta_tail_4398046511104_le` at `:2380-2391` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_17592186044416_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 17592186044416), etaDirichletTerm s k)‖ ≤
      (3 / 524288 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 17592186044416 (by norm_num)
  have h2M : 2 * 17592186044416 = 35184372088832 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_17592186044416_le
  linarith

/-- The `M = 17592186044416` constant honestly improves on the banked `M = 8796093022208`
constant (`3/524288 ≈ 0.00000572 < 24/2965820 ≈ 0.00000809`). -/
theorem tail_17592186044416_lt_8796093022208 : (3 / 524288 : ℝ) < (24 / 2965820 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 35184372088832` tail (`5931641 ≤ 35184372088832^{1/2}`;
generic mirror of `M8796093022208_rpow_ge` at `:2408` and latest exact
`M17592186044416_rpow_eq` at `:2477`; honest floor via `5931641^2 = 35184364952881 ≤
35184372088832` by `norm_num`; `35184372088832 = 2^45` so root `4194304·√2 ≈ 5931641.60`
is NOT exact; lower gap `7135951`, upper witness `5931642^2 = 35184376816164 =
35184372088832 + 4727332`). -/
theorem M35184372088832_rpow_ge :
    (5931641 : ℝ) ≤ ((((35184372088832 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((5931641 : ℝ) ^ (2 : ℕ)) ≤ ((((35184372088832 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((35184372088832 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((35184372088832 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 35184372088832` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/5931641`; generic mirror of `r_8796093022208_le`
at `:2424` and latest exact `r_17592186044416_le` at `:2503`; decay recomputed honestly
with `norm_num` via `M35184372088832_rpow_ge`; tightest honest `T = 24/5931641 ≈
0.00000405` for the `5931641` root lower). -/
theorem r_35184372088832_le :
    (12 : ℝ) * ((((((35184372088832 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 5931641 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((35184372088832 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((35184372088832 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M35184372088832_rpow_ge
  have hrw : ((((35184372088832 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((35184372088832 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((35184372088832 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (5931641 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((35184372088832 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (5931641 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((35184372088832 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((5931641 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((5931641 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 5931641 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 35184372088832` (`‖G - S70368744177664‖ ≤ 24/5931641`;
generic mirror of `eta_tail_8796093022208_le` at `:2451` and latest exact
`eta_tail_17592186044416_le` at `:2519` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_35184372088832_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 35184372088832), etaDirichletTerm s k)‖ ≤
      (24 / 5931641 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 35184372088832 (by norm_num)
  have h2M : 2 * 35184372088832 = 70368744177664 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_35184372088832_le
  linarith

/-- The `M = 35184372088832` constant honestly improves on the banked `M = 17592186044416`
constant (`24/5931641 ≈ 0.00000405 < 3/524288 ≈ 0.00000572`). -/
theorem tail_35184372088832_lt_17592186044416 : (24 / 5931641 : ℝ) < (3 / 524288 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 70368744177664` tail (`70368744177664^{1/2} = 8388608`
exact; exact shape mirror of `M17592186044416_rpow_eq` at `:2477-2496` and latest odd-floor
`M35184372088832_rpow_ge` at `:2547-2556`; honest via `8388608^2 = 70368744177664` by
`norm_num`; `70368744177664 = 2^46` so the root is exact, unlike `35184372088832`). -/
theorem M70368744177664_rpow_eq :
    ((((70368744177664 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (8388608 : ℝ) := by
  have hx2 : ((((((70368744177664 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((70368744177664 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((8388608 : ℝ) ^ (2 : ℕ)) = ((((70368744177664 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((70368744177664 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (8388608 : ℝ) := by norm_num
  have hle1 : ((((((70368744177664 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((8388608 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((8388608 : ℝ) ^ (2 : ℕ)) ≤
      ((((((70368744177664 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 70368744177664` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/8388608 = 3/1048576`; exact shape mirror of
`r_17592186044416_le` at `:2503-2514`; decay recomputed honestly with `norm_num`
via the exact `M70368744177664_rpow_eq`; tightest honest `T = 3/1048576 =
0.00000286102294921875` for this root). -/
theorem r_70368744177664_le :
    (12 : ℝ) * ((((((70368744177664 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 1048576 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((70368744177664 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M70368744177664_rpow_eq
  have hrw : ((((70368744177664 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((70368744177664 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((8388608 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 1048576 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 70368744177664` (`‖G - S140737488355328‖ ≤ 3/1048576`;
exact shape mirror of `eta_tail_17592186044416_le` at `:2519-2530` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_70368744177664_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 70368744177664), etaDirichletTerm s k)‖ ≤
      (3 / 1048576 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 70368744177664 (by norm_num)
  have h2M : 2 * 70368744177664 = 140737488355328 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_70368744177664_le
  linarith

/-- The `M = 70368744177664` constant honestly improves on the banked `M = 35184372088832`
constant (`3/1048576 ≈ 0.00000286 < 24/5931641 ≈ 0.00000405`). -/
theorem tail_70368744177664_lt_35184372088832 : (3 / 1048576 : ℝ) < (24 / 5931641 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 140737488355328` tail (`11863283 ≤ 140737488355328^{1/2}`;
generic mirror of `M35184372088832_rpow_ge` at `:2547` and latest exact
`M70368744177664_rpow_eq` at `:2616`; honest floor via `11863283^2 = 140737483538089 ≤
140737488355328` by `norm_num`; `140737488355328 = 2^47` so root `8388608·√2 ≈ 11863283.43`
is NOT exact; lower gap `4817239`, upper witness `11863284^2 = 140737507264656 =
140737488355328 + 18909328`). -/
theorem M140737488355328_rpow_ge :
    (11863283 : ℝ) ≤ ((((140737488355328 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((11863283 : ℝ) ^ (2 : ℕ)) ≤ ((((140737488355328 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((140737488355328 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((140737488355328 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 140737488355328` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/11863283`; generic mirror of `r_35184372088832_le`
at `:2563` and latest exact `r_70368744177664_le` at `:2642`; decay recomputed honestly
with `norm_num` via `M140737488355328_rpow_ge`; tightest honest `T = 24/11863283 ≈
0.00000202` for the `11863283` root lower). -/
theorem r_140737488355328_le :
    (12 : ℝ) * ((((((140737488355328 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 11863283 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((140737488355328 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((140737488355328 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M140737488355328_rpow_ge
  have hrw : ((((140737488355328 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((140737488355328 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((140737488355328 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (11863283 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((140737488355328 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (11863283 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((140737488355328 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((11863283 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((11863283 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 11863283 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 140737488355328` (`‖G - S281474976710656‖ ≤ 24/11863283`;
generic mirror of `eta_tail_35184372088832_le` at `:2590` and latest exact
`eta_tail_70368744177664_le` at `:2658` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_140737488355328_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 140737488355328), etaDirichletTerm s k)‖ ≤
      (24 / 11863283 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 140737488355328 (by norm_num)
  have h2M : 2 * 140737488355328 = 281474976710656 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_140737488355328_le
  linarith

/-- The `M = 140737488355328` constant honestly improves on the banked `M = 70368744177664`
constant (`24/11863283 ≈ 0.00000202 < 3/1048576 ≈ 0.00000286`). -/
theorem tail_140737488355328_lt_70368744177664 : (24 / 11863283 : ℝ) < (3 / 1048576 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 281474976710656` tail (`281474976710656^{1/2} = 16777216`
exact; exact shape mirror of `M70368744177664_rpow_eq` at `:2616` and latest odd-floor
`M140737488355328_rpow_ge` at `:2686`; honest via `16777216^2 = 281474976710656` by
`norm_num`; `281474976710656 = 2^48` so the root is exact, unlike `140737488355328`). -/
theorem M281474976710656_rpow_eq :
    ((((281474976710656 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (16777216 : ℝ) := by
  have hx2 : ((((((281474976710656 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((281474976710656 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((16777216 : ℝ) ^ (2 : ℕ)) = ((((281474976710656 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((281474976710656 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (16777216 : ℝ) := by norm_num
  have hle1 : ((((((281474976710656 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((16777216 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((16777216 : ℝ) ^ (2 : ℕ)) ≤
      ((((((281474976710656 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 281474976710656` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/16777216 = 3/2097152`; exact shape mirror of
`r_70368744177664_le` at `:2642-2653`; decay recomputed honestly with `norm_num`
via the exact `M281474976710656_rpow_eq`; tightest honest `T = 3/2097152 =
0.000001430511474609375` for this root). -/
theorem r_281474976710656_le :
    (12 : ℝ) * ((((((281474976710656 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 2097152 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((281474976710656 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M281474976710656_rpow_eq
  have hrw : ((((281474976710656 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((281474976710656 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((16777216 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 2097152 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 281474976710656` (`‖G - S562949953421312‖ ≤ 3/2097152`;
exact shape mirror of `eta_tail_70368744177664_le` at `:2658-2669` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_281474976710656_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 281474976710656), etaDirichletTerm s k)‖ ≤
      (3 / 2097152 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 281474976710656 (by norm_num)
  have h2M : 2 * 281474976710656 = 562949953421312 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_281474976710656_le
  linarith

/-- The `M = 281474976710656` constant honestly improves on the banked `M = 140737488355328`
constant (`3/2097152 ≈ 0.00000143 < 24/11863283 ≈ 0.00000202`). -/
theorem tail_281474976710656_lt_140737488355328 : (3 / 2097152 : ℝ) < (24 / 11863283 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 562949953421312` tail (`23726566 ≤ 562949953421312^{1/2}`;
generic mirror of `M140737488355328_rpow_ge` at `:2686` and latest exact
`M281474976710656_rpow_eq` at `:2755`; honest floor via `23726566^2 = 562949934152356 ≤
562949953421312` by `norm_num`; `562949953421312 = 2^49` so root `16777216·√2 ≈ 23726566.41`
is NOT exact; lower gap `19268956`, upper witness `23726567^2 = 562949981605489 =
562949953421312 + 28184177`). -/
theorem M562949953421312_rpow_ge :
    (23726566 : ℝ) ≤ ((((562949953421312 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((23726566 : ℝ) ^ (2 : ℕ)) ≤ ((((562949953421312 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((562949953421312 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((562949953421312 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 562949953421312` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/23726566`; generic mirror of `r_140737488355328_le`
at `:2702` and latest exact `r_281474976710656_le` at `:2781`; decay recomputed honestly
with `norm_num` via `M562949953421312_rpow_ge`; tightest honest `T = 24/23726566 ≈
0.00000101` for the `23726566` root lower). -/
theorem r_562949953421312_le :
    (12 : ℝ) * ((((((562949953421312 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 23726566 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((562949953421312 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((562949953421312 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M562949953421312_rpow_ge
  have hrw : ((((562949953421312 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((562949953421312 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((562949953421312 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (23726566 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((562949953421312 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (23726566 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((562949953421312 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((23726566 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((23726566 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 23726566 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 562949953421312` (`‖G - S1125899906842624‖ ≤ 24/23726566`;
generic mirror of `eta_tail_140737488355328_le` at `:2729` and latest exact
`eta_tail_281474976710656_le` at `:2797` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_562949953421312_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 562949953421312), etaDirichletTerm s k)‖ ≤
      (24 / 23726566 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 562949953421312 (by norm_num)
  have h2M : 2 * 562949953421312 = 1125899906842624 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_562949953421312_le
  linarith

/-- The `M = 562949953421312` constant honestly improves on the banked `M = 281474976710656`
constant (`24/23726566 ≈ 0.00000101 < 3/2097152 ≈ 0.00000143`). -/
theorem tail_562949953421312_lt_281474976710656 : (24 / 23726566 : ℝ) < (3 / 2097152 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 1125899906842624` tail (`1125899906842624^{1/2} = 33554432`
exact; exact shape mirror of `M281474976710656_rpow_eq` at `:2755` and latest odd-floor
`M562949953421312_rpow_ge` at `:2825`; honest via `33554432^2 = 1125899906842624` by
`norm_num`; `1125899906842624 = 2^50` so the root is exact, unlike `562949953421312`). -/
theorem M1125899906842624_rpow_eq :
    ((((1125899906842624 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (33554432 : ℝ) := by
  have hx2 : ((((((1125899906842624 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((1125899906842624 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((33554432 : ℝ) ^ (2 : ℕ)) = ((((1125899906842624 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((1125899906842624 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (33554432 : ℝ) := by norm_num
  have hle1 : ((((((1125899906842624 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((33554432 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((33554432 : ℝ) ^ (2 : ℕ)) ≤
      ((((((1125899906842624 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 1125899906842624` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/33554432 = 3/4194304`; exact shape mirror of
`r_281474976710656_le` at `:2781-2792`; decay recomputed honestly with `norm_num`
via the exact `M1125899906842624_rpow_eq`; tightest honest `T = 3/4194304 ≈
0.000000715` for this root). -/
theorem r_1125899906842624_le :
    (12 : ℝ) * ((((((1125899906842624 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 4194304 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((1125899906842624 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M1125899906842624_rpow_eq
  have hrw : ((((1125899906842624 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((1125899906842624 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((33554432 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 4194304 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 1125899906842624` (`‖G - S2251799813685248‖ ≤ 3/4194304`;
exact shape mirror of `eta_tail_281474976710656_le` at `:2797-2808` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_1125899906842624_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 1125899906842624), etaDirichletTerm s k)‖ ≤
      (3 / 4194304 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1125899906842624 (by norm_num)
  have h2M : 2 * 1125899906842624 = 2251799813685248 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_1125899906842624_le
  linarith

/-- The `M = 1125899906842624` constant honestly improves on the banked `M = 562949953421312`
constant (`3/4194304 ≈ 0.000000715 < 24/23726566 ≈ 0.00000101`). -/
theorem tail_1125899906842624_lt_562949953421312 : (3 / 4194304 : ℝ) < (24 / 23726566 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 2251799813685248` tail (`47453132 ≤ 2251799813685248^{1/2}`;
generic mirror of `M562949953421312_rpow_ge` at `:2825` and latest exact
`M1125899906842624_rpow_eq` at `:2894`; honest floor via `47453132^2 = 2251799736609424 ≤
2251799813685248` by `norm_num`; `2251799813685248 = 2^51` so root `33554432·√2 ≈ 47453132.68`
is NOT exact; lower gap `77075824`, upper witness `47453133^2 = 2251799831515689 =
2251799813685248 + 17830441`). -/
theorem M2251799813685248_rpow_ge :
    (47453132 : ℝ) ≤ ((((2251799813685248 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((47453132 : ℝ) ^ (2 : ℕ)) ≤ ((((2251799813685248 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((2251799813685248 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((2251799813685248 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 2251799813685248` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/47453132`; generic mirror of `r_562949953421312_le`
at `:2841` and latest exact `r_1125899906842624_le` at `:2920`; decay recomputed honestly
with `norm_num` via `M2251799813685248_rpow_ge`; tightest honest `T = 24/47453132 ≈
0.000000506` for the `47453132` root lower). -/
theorem r_2251799813685248_le :
    (12 : ℝ) * ((((((2251799813685248 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 47453132 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((2251799813685248 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((2251799813685248 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M2251799813685248_rpow_ge
  have hrw : ((((2251799813685248 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((2251799813685248 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((2251799813685248 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (47453132 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((2251799813685248 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (47453132 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((2251799813685248 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((47453132 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((47453132 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 47453132 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 2251799813685248` (`‖G - S4503599627370496‖ ≤ 24/47453132`;
generic mirror of `eta_tail_562949953421312_le` at `:2868` and latest exact
`eta_tail_1125899906842624_le` at `:2936` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_2251799813685248_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 2251799813685248), etaDirichletTerm s k)‖ ≤
      (24 / 47453132 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 2251799813685248 (by norm_num)
  have h2M : 2 * 2251799813685248 = 4503599627370496 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_2251799813685248_le
  linarith

/-- The `M = 2251799813685248` constant honestly improves on the banked `M = 1125899906842624`
constant (`24/47453132 ≈ 0.000000506 < 3/4194304 ≈ 0.000000715`). -/
theorem tail_2251799813685248_lt_1125899906842624 : (24 / 47453132 : ℝ) < (3 / 4194304 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 4503599627370496` tail (`4503599627370496^{1/2} = 67108864`
exact; exact shape mirror of `M1125899906842624_rpow_eq` at `:2894` and latest odd-floor
`M2251799813685248_rpow_ge` at `:2964`; honest via `67108864^2 = 4503599627370496` by
`norm_num`; `4503599627370496 = 2^52` so the root is exact, unlike `2251799813685248`). -/
theorem M4503599627370496_rpow_eq :
    ((((4503599627370496 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (67108864 : ℝ) := by
  have hx2 : ((((((4503599627370496 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((4503599627370496 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((67108864 : ℝ) ^ (2 : ℕ)) = ((((4503599627370496 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((4503599627370496 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (67108864 : ℝ) := by norm_num
  have hle1 : ((((((4503599627370496 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((67108864 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((67108864 : ℝ) ^ (2 : ℕ)) ≤
      ((((((4503599627370496 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 4503599627370496` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/67108864 = 3/8388608`; exact shape mirror of
`r_1125899906842624_le` at `:2920-2931`; decay recomputed honestly with `norm_num`
via the exact `M4503599627370496_rpow_eq`; tightest honest `T = 3/8388608 ≈
0.000000358` for this root). -/
theorem r_4503599627370496_le :
    (12 : ℝ) * ((((((4503599627370496 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 8388608 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((4503599627370496 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M4503599627370496_rpow_eq
  have hrw : ((((4503599627370496 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((4503599627370496 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((67108864 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 8388608 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 4503599627370496` (`‖G - S9007199254740992‖ ≤ 3/8388608`;
exact shape mirror of `eta_tail_1125899906842624_le` at `:2936-2947` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_4503599627370496_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 4503599627370496), etaDirichletTerm s k)‖ ≤
      (3 / 8388608 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 4503599627370496 (by norm_num)
  have h2M : 2 * 4503599627370496 = 9007199254740992 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_4503599627370496_le
  linarith

/-- The `M = 4503599627370496` constant honestly improves on the banked `M = 2251799813685248`
constant (`3/8388608 ≈ 0.000000358 < 24/47453132 ≈ 0.000000506`). -/
theorem tail_4503599627370496_lt_2251799813685248 : (3 / 8388608 : ℝ) < (24 / 47453132 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 9007199254740992` tail (`94906265 ≤ 9007199254740992^{1/2}`;
generic mirror of `M2251799813685248_rpow_ge` at `:2964` and latest exact
`M4503599627370496_rpow_eq` at `:3033`; honest floor via `94906265^2 = 9007199136250225 ≤
9007199254740992` by `norm_num`; `9007199254740992 = 2^53` so root `67108864·√2 ≈ 94906265.62`
is NOT exact; lower gap `118490767`, upper witness `94906266^2 = 9007199326062756 =
9007199254740992 + 71321764`). -/
theorem M9007199254740992_rpow_ge :
    (94906265 : ℝ) ≤ ((((9007199254740992 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((94906265 : ℝ) ^ (2 : ℕ)) ≤ ((((9007199254740992 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((9007199254740992 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((9007199254740992 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 9007199254740992` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/94906265`; generic mirror of `r_2251799813685248_le`
at `:2980` and latest exact `r_4503599627370496_le` at `:3059`; decay recomputed honestly
with `norm_num` via `M9007199254740992_rpow_ge`; tightest honest `T = 24/94906265 ≈
0.000000253` for the `94906265` root lower). -/
theorem r_9007199254740992_le :
    (12 : ℝ) * ((((((9007199254740992 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 94906265 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((9007199254740992 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((9007199254740992 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M9007199254740992_rpow_ge
  have hrw : ((((9007199254740992 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((9007199254740992 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((9007199254740992 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (94906265 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((9007199254740992 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (94906265 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((9007199254740992 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((94906265 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((94906265 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 94906265 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 9007199254740992` (`‖G - S18014398509481984‖ ≤ 24/94906265`;
generic mirror of `eta_tail_2251799813685248_le` at `:3007` and latest exact
`eta_tail_4503599627370496_le` at `:3075` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_9007199254740992_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 9007199254740992), etaDirichletTerm s k)‖ ≤
      (24 / 94906265 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 9007199254740992 (by norm_num)
  have h2M : 2 * 9007199254740992 = 18014398509481984 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_9007199254740992_le
  linarith

/-- The `M = 9007199254740992` constant honestly improves on the banked `M = 4503599627370496`
constant (`24/94906265 ≈ 0.000000253 < 3/8388608 ≈ 0.000000358`). -/
theorem tail_9007199254740992_lt_4503599627370496 : (24 / 94906265 : ℝ) < (3 / 8388608 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 18014398509481984` tail (`18014398509481984^{1/2} = 134217728`
exact; exact shape mirror of `M4503599627370496_rpow_eq` at `:3033` and latest odd-floor
`M9007199254740992_rpow_ge` at `:3103`; honest via `134217728^2 = 18014398509481984` by
`norm_num`; `18014398509481984 = 2^54` so the root is exact, unlike `9007199254740992`). -/
theorem M18014398509481984_rpow_eq :
    ((((18014398509481984 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (134217728 : ℝ) := by
  have hx2 : ((((((18014398509481984 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((18014398509481984 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((134217728 : ℝ) ^ (2 : ℕ)) = ((((18014398509481984 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((18014398509481984 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (134217728 : ℝ) := by norm_num
  have hle1 : ((((((18014398509481984 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((134217728 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((134217728 : ℝ) ^ (2 : ℕ)) ≤
      ((((((18014398509481984 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 18014398509481984` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/134217728 = 3/16777216`; exact shape mirror of
`r_4503599627370496_le` at `:3059-3070`; decay recomputed honestly with `norm_num`
via the exact `M18014398509481984_rpow_eq`; tightest honest `T = 3/16777216 ≈
0.000000179` for this root). -/
theorem r_18014398509481984_le :
    (12 : ℝ) * ((((((18014398509481984 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 16777216 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((18014398509481984 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M18014398509481984_rpow_eq
  have hrw : ((((18014398509481984 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((18014398509481984 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((134217728 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 16777216 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 18014398509481984` (`‖G - S36028797018963968‖ ≤ 3/16777216`;
exact shape mirror of `eta_tail_4503599627370496_le` at `:3075-3086` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_18014398509481984_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 18014398509481984), etaDirichletTerm s k)‖ ≤
      (3 / 16777216 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 18014398509481984 (by norm_num)
  have h2M : 2 * 18014398509481984 = 36028797018963968 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_18014398509481984_le
  linarith

/-- The `M = 18014398509481984` constant honestly improves on the banked `M = 9007199254740992`
constant (`3/16777216 ≈ 0.000000179 < 24/94906265 ≈ 0.000000253`). -/
theorem tail_18014398509481984_lt_9007199254740992 : (3 / 16777216 : ℝ) < (24 / 94906265 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 36028797018963968` tail (`189812530 ≤ 36028797018963968^{1/2}`;
generic mirror of `M9007199254740992_rpow_ge` at `:3103` and latest exact
`M18014398509481984_rpow_eq` at `:3172`; honest floor via `189812530^2 = 36028796545000900 ≤
36028797018963968` by `norm_num`; `36028797018963968 = 2^55` so root `134217728·√2 ≈ 189812531.24`
is NOT exact; conservative doubling `2 * 94906265 = 189812530` (one below the true floor
`189812531`); lower gap `473963068`). -/
theorem M36028797018963968_rpow_ge :
    (189812530 : ℝ) ≤ ((((36028797018963968 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((189812530 : ℝ) ^ (2 : ℕ)) ≤ ((((36028797018963968 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((36028797018963968 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((36028797018963968 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 36028797018963968` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/189812530`; generic mirror of `r_9007199254740992_le`
at `:3119` and latest exact `r_18014398509481984_le` at `:3198`; decay recomputed honestly
with `norm_num` via `M36028797018963968_rpow_ge`; honest conservative `T = 24/189812530 ≈
0.000000126` for the `189812530` root lower). -/
theorem r_36028797018963968_le :
    (12 : ℝ) * ((((((36028797018963968 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 189812530 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((36028797018963968 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((36028797018963968 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M36028797018963968_rpow_ge
  have hrw : ((((36028797018963968 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((36028797018963968 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((36028797018963968 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (189812530 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((36028797018963968 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (189812530 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((36028797018963968 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((189812530 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((189812530 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 189812530 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 36028797018963968` (`‖G - S72057594037927936‖ ≤ 24/189812530`;
generic mirror of `eta_tail_9007199254740992_le` at `:3146` and latest exact
`eta_tail_18014398509481984_le` at `:3214` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_36028797018963968_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 36028797018963968), etaDirichletTerm s k)‖ ≤
      (24 / 189812530 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 36028797018963968 (by norm_num)
  have h2M : 2 * 36028797018963968 = 72057594037927936 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_36028797018963968_le
  linarith

/-- The `M = 36028797018963968` constant honestly improves on the banked `M = 18014398509481984`
constant (`24/189812530 ≈ 0.000000126 < 3/16777216 ≈ 0.000000179`). -/
theorem tail_36028797018963968_lt_18014398509481984 : (24 / 189812530 : ℝ) < (3 / 16777216 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 72057594037927936` tail (`72057594037927936^{1/2} = 268435456`
exact; exact shape mirror of `M18014398509481984_rpow_eq` at `:3172` and latest odd-floor
`M36028797018963968_rpow_ge`; honest via `268435456^2 = 72057594037927936` by
`norm_num`; `72057594037927936 = 2^56` so the root is exact, unlike `36028797018963968`). -/
theorem M72057594037927936_rpow_eq :
    ((((72057594037927936 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (268435456 : ℝ) := by
  have hx2 : ((((((72057594037927936 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((72057594037927936 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((268435456 : ℝ) ^ (2 : ℕ)) = ((((72057594037927936 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((72057594037927936 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (268435456 : ℝ) := by norm_num
  have hle1 : ((((((72057594037927936 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((268435456 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((268435456 : ℝ) ^ (2 : ℕ)) ≤
      ((((((72057594037927936 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 72057594037927936` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/268435456 = 3/33554432`; exact shape mirror of
`r_18014398509481984_le` at `:3198-3209`; decay recomputed honestly with `norm_num`
via the exact `M72057594037927936_rpow_eq`; tightest honest `T = 3/33554432 ≈
0.000000089` for this root). -/
theorem r_72057594037927936_le :
    (12 : ℝ) * ((((((72057594037927936 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 33554432 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((72057594037927936 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M72057594037927936_rpow_eq
  have hrw : ((((72057594037927936 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((72057594037927936 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((268435456 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 33554432 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 72057594037927936` (`‖G - S144115188075855872‖ ≤ 3/33554432`;
exact shape mirror of `eta_tail_18014398509481984_le` at `:3214-3225` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_72057594037927936_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 72057594037927936), etaDirichletTerm s k)‖ ≤
      (3 / 33554432 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 72057594037927936 (by norm_num)
  have h2M : 2 * 72057594037927936 = 144115188075855872 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_72057594037927936_le
  linarith

/-- The `M = 72057594037927936` constant honestly improves on the banked `M = 36028797018963968`
constant (`3/33554432 ≈ 0.000000089 < 24/189812530 ≈ 0.000000126`). -/
theorem tail_72057594037927936_lt_36028797018963968 : (3 / 33554432 : ℝ) < (24 / 189812530 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 144115188075855872` tail (`379625060 ≤ 144115188075855872^{1/2}`;
generic mirror of `M36028797018963968_rpow_ge` at `:3242` and latest exact
`M72057594037927936_rpow_eq` at `:3311`; honest floor via `379625060^2 = 144115186180003600 ≤
144115188075855872` by `norm_num`; `144115188075855872 = 2^57` so root `268435456·√2 ≈ 379625062.49`
is NOT exact; conservative doubling `2 * 189812530 = 379625060` (two below the true floor
`379625062`); lower gap `1895852272`). -/
theorem M144115188075855872_rpow_ge :
    (379625060 : ℝ) ≤ ((((144115188075855872 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((379625060 : ℝ) ^ (2 : ℕ)) ≤ ((((144115188075855872 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((144115188075855872 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((144115188075855872 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 144115188075855872` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/379625060`; generic mirror of `r_36028797018963968_le`
at `:3258` and latest exact `r_72057594037927936_le` at `:3337`; decay recomputed honestly
with `norm_num` via `M144115188075855872_rpow_ge`; honest conservative `T = 24/379625060 ≈
0.000000063` for the `379625060` root lower). -/
theorem r_144115188075855872_le :
    (12 : ℝ) * ((((((144115188075855872 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 379625060 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((144115188075855872 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((144115188075855872 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M144115188075855872_rpow_ge
  have hrw : ((((144115188075855872 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((144115188075855872 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((144115188075855872 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (379625060 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((144115188075855872 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (379625060 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((144115188075855872 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((379625060 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((379625060 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 379625060 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 144115188075855872` (`‖G - S288230376151711744‖ ≤ 24/379625060`;
generic mirror of `eta_tail_36028797018963968_le` at `:3285` and latest exact
`eta_tail_72057594037927936_le` at `:3353` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_144115188075855872_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 144115188075855872), etaDirichletTerm s k)‖ ≤
      (24 / 379625060 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 144115188075855872 (by norm_num)
  have h2M : 2 * 144115188075855872 = 288230376151711744 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_144115188075855872_le
  linarith

/-- The `M = 144115188075855872` constant honestly improves on the banked `M = 72057594037927936`
constant (`24/379625060 ≈ 0.000000063 < 3/33554432 ≈ 0.000000089`). -/
theorem tail_144115188075855872_lt_72057594037927936 : (24 / 379625060 : ℝ) < (3 / 33554432 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 288230376151711744` tail (`288230376151711744^{1/2} = 536870912`
exact; exact shape mirror of `M72057594037927936_rpow_eq` at `:3311` and latest odd-floor
`M144115188075855872_rpow_ge`; honest via `536870912^2 = 288230376151711744` by
`norm_num`; `288230376151711744 = 2^58` so the root is exact, unlike `144115188075855872`). -/
theorem M288230376151711744_rpow_eq :
    ((((288230376151711744 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (536870912 : ℝ) := by
  have hx2 : ((((((288230376151711744 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((288230376151711744 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((536870912 : ℝ) ^ (2 : ℕ)) = ((((288230376151711744 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((288230376151711744 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (536870912 : ℝ) := by norm_num
  have hle1 : ((((((288230376151711744 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((536870912 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((536870912 : ℝ) ^ (2 : ℕ)) ≤
      ((((((288230376151711744 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 288230376151711744` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/536870912 = 3/67108864`; exact shape mirror of
`r_72057594037927936_le` at `:3337-3348`; decay recomputed honestly with `norm_num`
via the exact `M288230376151711744_rpow_eq`; tightest honest `T = 3/67108864 ≈
0.000000044` for this root). -/
theorem r_288230376151711744_le :
    (12 : ℝ) * ((((((288230376151711744 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 67108864 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((288230376151711744 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M288230376151711744_rpow_eq
  have hrw : ((((288230376151711744 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((288230376151711744 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((536870912 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 67108864 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 288230376151711744` (`‖G - S576460752303423488‖ ≤ 3/67108864`;
exact shape mirror of `eta_tail_72057594037927936_le` at `:3353-3364` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_288230376151711744_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 288230376151711744), etaDirichletTerm s k)‖ ≤
      (3 / 67108864 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 288230376151711744 (by norm_num)
  have h2M : 2 * 288230376151711744 = 576460752303423488 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_288230376151711744_le
  linarith

/-- The `M = 288230376151711744` constant honestly improves on the banked `M = 144115188075855872`
constant (`3/67108864 ≈ 0.000000044 < 24/379625060 ≈ 0.000000063`). -/
theorem tail_288230376151711744_lt_144115188075855872 : (3 / 67108864 : ℝ) < (24 / 379625060 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 576460752303423488` tail (`759250120 ≤ 576460752303423488^{1/2}`;
generic mirror of `M144115188075855872_rpow_ge` at `:3381` and latest exact
`M288230376151711744_rpow_eq` at `:3450`; honest floor via `759250120^2 = 576460744720014400 ≤
576460752303423488` by `norm_num`; `576460752303423488 = 2^59` so root `536870912·√2 ≈ 759250124.99`
is NOT exact; conservative doubling `2 * 379625060 = 759250120` (four below the true floor
`759250124`); lower gap `7583409088`). -/
theorem M576460752303423488_rpow_ge :
    (759250120 : ℝ) ≤ ((((576460752303423488 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((759250120 : ℝ) ^ (2 : ℕ)) ≤ ((((576460752303423488 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((576460752303423488 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((576460752303423488 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 576460752303423488` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/759250120`; generic mirror of `r_144115188075855872_le`
at `:3397` and latest exact `r_288230376151711744_le` at `:3476`; decay recomputed honestly
with `norm_num` via `M576460752303423488_rpow_ge`; honest conservative `T = 24/759250120 ≈
0.000000031` for the `759250120` root lower). -/
theorem r_576460752303423488_le :
    (12 : ℝ) * ((((((576460752303423488 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 759250120 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((576460752303423488 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((576460752303423488 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M576460752303423488_rpow_ge
  have hrw : ((((576460752303423488 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((576460752303423488 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((576460752303423488 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (759250120 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((576460752303423488 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (759250120 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((576460752303423488 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((759250120 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((759250120 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 759250120 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 576460752303423488` (`‖G - S1152921504606846976‖ ≤ 24/759250120`;
generic mirror of `eta_tail_144115188075855872_le` at `:3424` and latest exact
`eta_tail_288230376151711744_le` at `:3492` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_576460752303423488_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 576460752303423488), etaDirichletTerm s k)‖ ≤
      (24 / 759250120 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 576460752303423488 (by norm_num)
  have h2M : 2 * 576460752303423488 = 1152921504606846976 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_576460752303423488_le
  linarith

/-- The `M = 576460752303423488` constant honestly improves on the banked `M = 288230376151711744`
constant (`24/759250120 ≈ 0.000000031 < 3/67108864 ≈ 0.000000044`). -/
theorem tail_576460752303423488_lt_288230376151711744 : (24 / 759250120 : ℝ) < (3 / 67108864 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 1152921504606846976` tail (`1152921504606846976^{1/2} = 1073741824`
exact; exact shape mirror of `M288230376151711744_rpow_eq` at `:3450` and latest odd-floor
`M576460752303423488_rpow_ge`; honest via `1073741824^2 = 1152921504606846976` by
`norm_num`; `1152921504606846976 = 2^60` so the root is exact, unlike `576460752303423488`). -/
theorem M1152921504606846976_rpow_eq :
    ((((1152921504606846976 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (1073741824 : ℝ) := by
  have hx2 : ((((((1152921504606846976 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((1152921504606846976 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((1073741824 : ℝ) ^ (2 : ℕ)) = ((((1152921504606846976 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((1152921504606846976 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (1073741824 : ℝ) := by norm_num
  have hle1 : ((((((1152921504606846976 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((1073741824 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((1073741824 : ℝ) ^ (2 : ℕ)) ≤
      ((((((1152921504606846976 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 1152921504606846976` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/1073741824 = 3/134217728`; exact shape mirror of
`r_288230376151711744_le` at `:3476`; decay recomputed honestly with `norm_num`
via the exact `M1152921504606846976_rpow_eq`; tightest honest `T = 3/134217728 ≈
0.000000022` for this root). -/
theorem r_1152921504606846976_le :
    (12 : ℝ) * ((((((1152921504606846976 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 134217728 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((1152921504606846976 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M1152921504606846976_rpow_eq
  have hrw : ((((1152921504606846976 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((1152921504606846976 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((1073741824 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 134217728 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 1152921504606846976` (`‖G - S2305843009213693952‖ ≤ 3/134217728`;
exact shape mirror of `eta_tail_288230376151711744_le` at `:3492` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_1152921504606846976_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 1152921504606846976), etaDirichletTerm s k)‖ ≤
      (3 / 134217728 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1152921504606846976 (by norm_num)
  have h2M : 2 * 1152921504606846976 = 2305843009213693952 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_1152921504606846976_le
  linarith

/-- The `M = 1152921504606846976` constant honestly improves on the banked `M = 576460752303423488`
constant (`3/134217728 ≈ 0.000000022 < 24/759250120 ≈ 0.000000031`). -/
theorem tail_1152921504606846976_lt_576460752303423488 : (3 / 134217728 : ℝ) < (24 / 759250120 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 2305843009213693952` tail (`1518500240 ≤ 2305843009213693952^{1/2}`;
generic mirror of `M576460752303423488_rpow_ge` at `:3520` and latest exact
`M1152921504606846976_rpow_eq` at `:3589`; honest floor via `1518500240^2 = 2305842978880057600 ≤
2305843009213693952` by `norm_num`; `2305843009213693952 = 2^61` so root `1073741824·√2 ≈ 1518500249.63`
is NOT exact; conservative doubling `2 * 759250120 = 1518500240` (nine below the true floor
`1518500249`); lower gap `30333636352`). -/
theorem M2305843009213693952_rpow_ge :
    (1518500240 : ℝ) ≤ ((((2305843009213693952 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((1518500240 : ℝ) ^ (2 : ℕ)) ≤ ((((2305843009213693952 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((2305843009213693952 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((2305843009213693952 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 2305843009213693952` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/1518500240`; generic mirror of `r_576460752303423488_le`
at `:3536` and latest exact `r_1152921504606846976_le` at `:3615`; decay recomputed honestly
with `norm_num` via `M2305843009213693952_rpow_ge`; honest conservative `T = 24/1518500240 ≈
0.000000015` for the `1518500240` root lower). -/
theorem r_2305843009213693952_le :
    (12 : ℝ) * ((((((2305843009213693952 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 1518500240 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((2305843009213693952 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((2305843009213693952 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M2305843009213693952_rpow_ge
  have hrw : ((((2305843009213693952 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((2305843009213693952 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((2305843009213693952 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (1518500240 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((2305843009213693952 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (1518500240 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((2305843009213693952 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((1518500240 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((1518500240 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 1518500240 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 2305843009213693952` (`‖G - S4611686018427387904‖ ≤ 24/1518500240`;
generic mirror of `eta_tail_576460752303423488_le` at `:3563` and latest exact
`eta_tail_1152921504606846976_le` at `:3631` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_2305843009213693952_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 2305843009213693952), etaDirichletTerm s k)‖ ≤
      (24 / 1518500240 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 2305843009213693952 (by norm_num)
  have h2M : 2 * 2305843009213693952 = 4611686018427387904 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_2305843009213693952_le
  linarith

/-- The `M = 2305843009213693952` constant honestly improves on the banked `M = 1152921504606846976`
constant (`24/1518500240 ≈ 0.000000015 < 3/134217728 ≈ 0.000000022`). -/
theorem tail_2305843009213693952_lt_1152921504606846976 : (24 / 1518500240 : ℝ) < (3 / 134217728 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 4611686018427387904` tail (`4611686018427387904^{1/2} = 2147483648`
exact; exact shape mirror of `M1152921504606846976_rpow_eq` at `:3589` and latest odd-floor
`M2305843009213693952_rpow_ge`; honest via `2147483648^2 = 4611686018427387904` by
`norm_num`; `4611686018427387904 = 2^62` so the root is exact, unlike `2305843009213693952`). -/
theorem M4611686018427387904_rpow_eq :
    ((((4611686018427387904 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (2147483648 : ℝ) := by
  have hx2 : ((((((4611686018427387904 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((4611686018427387904 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((2147483648 : ℝ) ^ (2 : ℕ)) = ((((4611686018427387904 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((4611686018427387904 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (2147483648 : ℝ) := by norm_num
  have hle1 : ((((((4611686018427387904 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((2147483648 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((2147483648 : ℝ) ^ (2 : ℕ)) ≤
      ((((((4611686018427387904 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 4611686018427387904` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/2147483648 = 3/268435456`; exact shape mirror of
`r_1152921504606846976_le` at `:3615`; decay recomputed honestly with `norm_num`
via the exact `M4611686018427387904_rpow_eq`; tightest honest `T = 3/268435456 ≈
0.000000011` for this root). -/
theorem r_4611686018427387904_le :
    (12 : ℝ) * ((((((4611686018427387904 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 268435456 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((4611686018427387904 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M4611686018427387904_rpow_eq
  have hrw : ((((4611686018427387904 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((4611686018427387904 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((2147483648 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 268435456 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 4611686018427387904` (`‖G - S9223372036854775808‖ ≤ 3/268435456`;
exact shape mirror of `eta_tail_1152921504606846976_le` at `:3631` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_4611686018427387904_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 4611686018427387904), etaDirichletTerm s k)‖ ≤
      (3 / 268435456 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 4611686018427387904 (by norm_num)
  have h2M : 2 * 4611686018427387904 = 9223372036854775808 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_4611686018427387904_le
  linarith

/-- The `M = 4611686018427387904` constant honestly improves on the banked `M = 2305843009213693952`
constant (`3/268435456 ≈ 0.000000011 < 24/1518500240 ≈ 0.000000015`). -/
theorem tail_4611686018427387904_lt_2305843009213693952 : (3 / 268435456 : ℝ) < (24 / 1518500240 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 9223372036854775808` tail (`3037000480 ≤ 9223372036854775808^{1/2}`;
generic mirror of `M2305843009213693952_rpow_ge` at `:3659` and latest exact
`M4611686018427387904_rpow_eq` at `:3728`; honest floor via `3037000480^2 = 9223371915520230400 ≤
9223372036854775808` by `norm_num`; `9223372036854775808 = 2^63` so root `2147483648·√2 ≈ 3037000499.97`
is NOT exact; conservative doubling `2 * 1518500240 = 3037000480` (nineteen below the true floor
`3037000499`); lower gap `121334545408`). -/
theorem M9223372036854775808_rpow_ge :
    (3037000480 : ℝ) ≤ ((((9223372036854775808 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((3037000480 : ℝ) ^ (2 : ℕ)) ≤ ((((9223372036854775808 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((9223372036854775808 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((9223372036854775808 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 9223372036854775808` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/3037000480`; generic mirror of `r_2305843009213693952_le`
at `:3675` and latest exact `r_4611686018427387904_le` at `:3754`; decay recomputed honestly
with `norm_num` via `M9223372036854775808_rpow_ge`; honest conservative `T = 24/3037000480 ≈
0.0000000079` for the `3037000480` root lower). -/
theorem r_9223372036854775808_le :
    (12 : ℝ) * ((((((9223372036854775808 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 3037000480 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((9223372036854775808 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((9223372036854775808 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M9223372036854775808_rpow_ge
  have hrw : ((((9223372036854775808 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((9223372036854775808 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((9223372036854775808 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (3037000480 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((9223372036854775808 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (3037000480 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((9223372036854775808 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((3037000480 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((3037000480 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 3037000480 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 9223372036854775808` (`‖G - S18446744073709551616‖ ≤ 24/3037000480`;
generic mirror of `eta_tail_2305843009213693952_le` at `:3702` and latest exact
`eta_tail_4611686018427387904_le` at `:3770` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_9223372036854775808_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 9223372036854775808), etaDirichletTerm s k)‖ ≤
      (24 / 3037000480 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 9223372036854775808 (by norm_num)
  have h2M : 2 * 9223372036854775808 = 18446744073709551616 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_9223372036854775808_le
  linarith

/-- The `M = 9223372036854775808` constant honestly improves on the banked `M = 4611686018427387904`
constant (`24/3037000480 ≈ 0.0000000079 < 3/268435456 ≈ 0.000000011`). -/
theorem tail_9223372036854775808_lt_4611686018427387904 : (24 / 3037000480 : ℝ) < (3 / 268435456 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 18446744073709551616` tail (`18446744073709551616^{1/2} = 4294967296`
exact; exact shape mirror of `M4611686018427387904_rpow_eq` at `:3728` and latest odd-floor
`M9223372036854775808_rpow_ge`; honest via `4294967296^2 = 18446744073709551616` by
`norm_num`; `18446744073709551616 = 2^64` so the root is exact, unlike `9223372036854775808`). -/
theorem M18446744073709551616_rpow_eq :
    ((((18446744073709551616 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (4294967296 : ℝ) := by
  have hx2 : ((((((18446744073709551616 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((18446744073709551616 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((4294967296 : ℝ) ^ (2 : ℕ)) = ((((18446744073709551616 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((18446744073709551616 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (4294967296 : ℝ) := by norm_num
  have hle1 : ((((((18446744073709551616 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((4294967296 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((4294967296 : ℝ) ^ (2 : ℕ)) ≤
      ((((((18446744073709551616 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 18446744073709551616` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/4294967296 = 3/536870912`; exact shape mirror of
`r_4611686018427387904_le` at `:3754`; decay recomputed honestly with `norm_num`
via the exact `M18446744073709551616_rpow_eq`; tightest honest `T = 3/536870912 ≈
0.0000000055` for this root). -/
theorem r_18446744073709551616_le :
    (12 : ℝ) * ((((((18446744073709551616 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 536870912 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((18446744073709551616 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M18446744073709551616_rpow_eq
  have hrw : ((((18446744073709551616 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((18446744073709551616 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((4294967296 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 536870912 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 18446744073709551616` (`‖G - S36893488147419103232‖ ≤ 3/536870912`;
exact shape mirror of `eta_tail_4611686018427387904_le` at `:3770` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_18446744073709551616_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 18446744073709551616), etaDirichletTerm s k)‖ ≤
      (3 / 536870912 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 18446744073709551616 (by norm_num)
  have h2M : 2 * 18446744073709551616 = 36893488147419103232 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_18446744073709551616_le
  linarith

/-- The `M = 18446744073709551616` constant honestly improves on the banked `M = 9223372036854775808`
constant (`3/536870912 ≈ 0.0000000055 < 24/3037000480 ≈ 0.0000000079`). -/
theorem tail_18446744073709551616_lt_9223372036854775808 : (3 / 536870912 : ℝ) < (24 / 3037000480 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 36893488147419103232` tail (`6074000960 ≤ 36893488147419103232^{1/2}`;
generic mirror of `M9223372036854775808_rpow_ge` at `:3798` and latest exact
`M18446744073709551616_rpow_eq` at `:3867`; honest floor via `6074000960^2 = 36893487662080921600 ≤
36893488147419103232` by `norm_num`; `36893488147419103232 = 2^65` so root `4294967296·√2 ≈ 6074000999.95`
is NOT exact; conservative doubling `2 * 3037000480 = 6074000960` (thirty-nine below the true floor
`6074000999`); lower gap `485338181632`). -/
theorem M36893488147419103232_rpow_ge :
    (6074000960 : ℝ) ≤ ((((36893488147419103232 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((6074000960 : ℝ) ^ (2 : ℕ)) ≤ ((((36893488147419103232 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((36893488147419103232 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((36893488147419103232 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 36893488147419103232` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/6074000960`; generic mirror of `r_9223372036854775808_le`
at `:3814` and latest exact `r_18446744073709551616_le` at `:3893`; decay recomputed honestly
with `norm_num` via `M36893488147419103232_rpow_ge`; honest conservative `T = 24/6074000960 ≈
0.0000000039` for the `6074000960` root lower). -/
theorem r_36893488147419103232_le :
    (12 : ℝ) * ((((((36893488147419103232 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 6074000960 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((36893488147419103232 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((36893488147419103232 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M36893488147419103232_rpow_ge
  have hrw : ((((36893488147419103232 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((36893488147419103232 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((36893488147419103232 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (6074000960 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((36893488147419103232 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (6074000960 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((36893488147419103232 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((6074000960 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((6074000960 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 6074000960 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 36893488147419103232` (`‖G - S73786976294838206464‖ ≤ 24/6074000960`;
generic mirror of `eta_tail_9223372036854775808_le` at `:3841` and latest exact
`eta_tail_18446744073709551616_le` at `:3909` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_36893488147419103232_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 36893488147419103232), etaDirichletTerm s k)‖ ≤
      (24 / 6074000960 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 36893488147419103232 (by norm_num)
  have h2M : 2 * 36893488147419103232 = 73786976294838206464 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_36893488147419103232_le
  linarith

/-- The `M = 36893488147419103232` constant honestly improves on the banked `M = 18446744073709551616`
constant (`24/6074000960 ≈ 0.0000000039 < 3/536870912 ≈ 0.0000000055`). -/
theorem tail_36893488147419103232_lt_18446744073709551616 : (24 / 6074000960 : ℝ) < (3 / 536870912 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 73786976294838206464` tail (`73786976294838206464^{1/2} = 8589934592`
exact; exact shape mirror of `M18446744073709551616_rpow_eq` at `:3867` and latest odd-floor
`M36893488147419103232_rpow_ge`; honest via `8589934592^2 = 73786976294838206464` by
`norm_num`; `73786976294838206464 = 2^66` so the root is exact, unlike `36893488147419103232`). -/
theorem M73786976294838206464_rpow_eq :
    ((((73786976294838206464 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (8589934592 : ℝ) := by
  have hx2 : ((((((73786976294838206464 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((73786976294838206464 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((8589934592 : ℝ) ^ (2 : ℕ)) = ((((73786976294838206464 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((73786976294838206464 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (8589934592 : ℝ) := by norm_num
  have hle1 : ((((((73786976294838206464 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((8589934592 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((8589934592 : ℝ) ^ (2 : ℕ)) ≤
      ((((((73786976294838206464 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 73786976294838206464` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/8589934592 = 3/1073741824`; exact shape mirror of
`r_18446744073709551616_le` at `:3893`; decay recomputed honestly with `norm_num`
via the exact `M73786976294838206464_rpow_eq`; tightest honest `T = 3/1073741824 ≈
0.0000000027` for this root). -/
theorem r_73786976294838206464_le :
    (12 : ℝ) * ((((((73786976294838206464 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 1073741824 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((73786976294838206464 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M73786976294838206464_rpow_eq
  have hrw : ((((73786976294838206464 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((73786976294838206464 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((8589934592 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 1073741824 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 73786976294838206464` (`‖G - S147573952589676412928‖ ≤ 3/1073741824`;
exact shape mirror of `eta_tail_18446744073709551616_le` at `:3909` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_73786976294838206464_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 73786976294838206464), etaDirichletTerm s k)‖ ≤
      (3 / 1073741824 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 73786976294838206464 (by norm_num)
  have h2M : 2 * 73786976294838206464 = 147573952589676412928 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_73786976294838206464_le
  linarith

/-- The `M = 73786976294838206464` constant honestly improves on the banked `M = 36893488147419103232`
constant (`3/1073741824 ≈ 0.0000000027 < 24/6074000960 ≈ 0.0000000039`). -/
theorem tail_73786976294838206464_lt_36893488147419103232 : (3 / 1073741824 : ℝ) < (24 / 6074000960 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 147573952589676412928` tail (`12148001920 ≤ 147573952589676412928^{1/2}`;
generic mirror of `M36893488147419103232_rpow_ge` at `:3937` and latest exact
`M73786976294838206464_rpow_eq` at `:4006`; honest floor via `12148001920^2 = 147573950648323686400 ≤
147573952589676412928` by `norm_num`; `147573952589676412928 = 2^67` so root `8589934592·√2 ≈ 12148001999.9`
is NOT exact; conservative doubling `2 * 6074000960 = 12148001920` (seventy-nine below the true floor
`12148001999`); lower gap `1941352726528`). -/
theorem M147573952589676412928_rpow_ge :
    (12148001920 : ℝ) ≤ ((((147573952589676412928 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((12148001920 : ℝ) ^ (2 : ℕ)) ≤ ((((147573952589676412928 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((147573952589676412928 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((147573952589676412928 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 147573952589676412928` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/12148001920`; generic mirror of `r_36893488147419103232_le`
at `:3953` and latest exact `r_73786976294838206464_le` at `:4032`; decay recomputed honestly
with `norm_num` via `M147573952589676412928_rpow_ge`; honest conservative `T = 24/12148001920 ≈
0.0000000019` for the `12148001920` root lower). -/
theorem r_147573952589676412928_le :
    (12 : ℝ) * ((((((147573952589676412928 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 12148001920 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((147573952589676412928 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((147573952589676412928 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M147573952589676412928_rpow_ge
  have hrw : ((((147573952589676412928 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((147573952589676412928 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((147573952589676412928 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (12148001920 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((147573952589676412928 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (12148001920 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((147573952589676412928 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((12148001920 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((12148001920 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 12148001920 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 147573952589676412928` (`‖G - S295147905179352825856‖ ≤ 24/12148001920`;
generic mirror of `eta_tail_36893488147419103232_le` at `:3980` and latest exact
`eta_tail_73786976294838206464_le` at `:4048` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_147573952589676412928_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 147573952589676412928), etaDirichletTerm s k)‖ ≤
      (24 / 12148001920 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 147573952589676412928 (by norm_num)
  have h2M : 2 * 147573952589676412928 = 295147905179352825856 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_147573952589676412928_le
  linarith

/-- The `M = 147573952589676412928` constant honestly improves on the banked `M = 73786976294838206464`
constant (`24/12148001920 ≈ 0.0000000019 < 3/1073741824 ≈ 0.0000000027`). -/
theorem tail_147573952589676412928_lt_73786976294838206464 : (24 / 12148001920 : ℝ) < (3 / 1073741824 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 295147905179352825856` tail (`295147905179352825856^{1/2} = 17179869184`
exact; exact shape mirror of `M73786976294838206464_rpow_eq` at `:4006` and latest odd-floor
`M147573952589676412928_rpow_ge`; honest via `17179869184^2 = 295147905179352825856` by
`norm_num`; `295147905179352825856 = 2^68` so the root is exact, unlike `147573952589676412928`). -/
theorem M295147905179352825856_rpow_eq :
    ((((295147905179352825856 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (17179869184 : ℝ) := by
  have hx2 : ((((((295147905179352825856 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((295147905179352825856 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((17179869184 : ℝ) ^ (2 : ℕ)) = ((((295147905179352825856 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((295147905179352825856 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (17179869184 : ℝ) := by norm_num
  have hle1 : ((((((295147905179352825856 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((17179869184 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((17179869184 : ℝ) ^ (2 : ℕ)) ≤
      ((((((295147905179352825856 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 295147905179352825856` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/17179869184 = 3/2147483648`; exact shape mirror of
`r_73786976294838206464_le` at `:4032`; decay recomputed honestly with `norm_num`
via the exact `M295147905179352825856_rpow_eq`; tightest honest `T = 3/2147483648 ≈
0.0000000013` for this root). -/
theorem r_295147905179352825856_le :
    (12 : ℝ) * ((((((295147905179352825856 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 2147483648 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((295147905179352825856 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M295147905179352825856_rpow_eq
  have hrw : ((((295147905179352825856 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((295147905179352825856 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((17179869184 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 2147483648 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 295147905179352825856` (`‖G - S590295810358705651712‖ ≤ 3/2147483648`;
exact shape mirror of `eta_tail_73786976294838206464_le` at `:4048` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_295147905179352825856_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 295147905179352825856), etaDirichletTerm s k)‖ ≤
      (3 / 2147483648 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 295147905179352825856 (by norm_num)
  have h2M : 2 * 295147905179352825856 = 590295810358705651712 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_295147905179352825856_le
  linarith

/-- The `M = 295147905179352825856` constant honestly improves on the banked `M = 147573952589676412928`
constant (`3/2147483648 ≈ 0.0000000013 < 24/12148001920 ≈ 0.0000000019`). -/
theorem tail_295147905179352825856_lt_147573952589676412928 : (3 / 2147483648 : ℝ) < (24 / 12148001920 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 590295810358705651712` tail (`24296003840 ≤ 590295810358705651712^{1/2}`;
generic mirror of `M147573952589676412928_rpow_ge` at `:4076` and latest exact
`M295147905179352825856_rpow_eq` at `:4145`; honest floor via `24296003840^2 = 590295802593294745600 ≤
590295810358705651712` by `norm_num`; `590295810358705651712 = 2^69` so root `17179869184·√2 ≈ 24296003999.81`
is NOT exact; conservative doubling `2 * 12148001920 = 24296003840` (one hundred fifty-nine below the true floor
`24296003999`); lower gap `7765410906112`). -/
theorem M590295810358705651712_rpow_ge :
    (24296003840 : ℝ) ≤ ((((590295810358705651712 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((24296003840 : ℝ) ^ (2 : ℕ)) ≤ ((((590295810358705651712 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((590295810358705651712 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((590295810358705651712 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 590295810358705651712` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/24296003840`; generic mirror of `r_147573952589676412928_le`
at `:4092` and latest exact `r_295147905179352825856_le` at `:4171`; decay recomputed honestly
with `norm_num` via `M590295810358705651712_rpow_ge`; honest conservative `T = 24/24296003840 ≈
0.00000000098` for the `24296003840` root lower). -/
theorem r_590295810358705651712_le :
    (12 : ℝ) * ((((((590295810358705651712 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 24296003840 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((590295810358705651712 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((590295810358705651712 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M590295810358705651712_rpow_ge
  have hrw : ((((590295810358705651712 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((590295810358705651712 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((590295810358705651712 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (24296003840 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((590295810358705651712 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (24296003840 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((590295810358705651712 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((24296003840 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((24296003840 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 24296003840 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 590295810358705651712` (`‖G - S1180591620717411303424‖ ≤ 24/24296003840`;
generic mirror of `eta_tail_147573952589676412928_le` at `:4119` and latest exact
`eta_tail_295147905179352825856_le` at `:4187` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_590295810358705651712_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 590295810358705651712), etaDirichletTerm s k)‖ ≤
      (24 / 24296003840 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 590295810358705651712 (by norm_num)
  have h2M : 2 * 590295810358705651712 = 1180591620717411303424 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_590295810358705651712_le
  linarith

/-- The `M = 590295810358705651712` constant honestly improves on the banked `M = 295147905179352825856`
constant (`24/24296003840 ≈ 0.00000000098 < 3/2147483648 ≈ 0.0000000013`). -/
theorem tail_590295810358705651712_lt_295147905179352825856 : (24 / 24296003840 : ℝ) < (3 / 2147483648 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 1180591620717411303424` tail (`1180591620717411303424^{1/2} = 34359738368`
exact; exact shape mirror of `M295147905179352825856_rpow_eq` at `:4145` and latest odd-floor
`M590295810358705651712_rpow_ge`; honest via `34359738368^2 = 1180591620717411303424` by
`norm_num`; `1180591620717411303424 = 2^70` so the root is exact, unlike `590295810358705651712`). -/
theorem M1180591620717411303424_rpow_eq :
    ((((1180591620717411303424 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (34359738368 : ℝ) := by
  have hx2 : ((((((1180591620717411303424 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((1180591620717411303424 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((34359738368 : ℝ) ^ (2 : ℕ)) = ((((1180591620717411303424 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((1180591620717411303424 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (34359738368 : ℝ) := by norm_num
  have hle1 : ((((((1180591620717411303424 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((34359738368 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((34359738368 : ℝ) ^ (2 : ℕ)) ≤
      ((((((1180591620717411303424 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 1180591620717411303424` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/34359738368 = 3/4294967296`; exact shape mirror of
`r_295147905179352825856_le` at `:4171`; decay recomputed honestly with `norm_num`
via the exact `M1180591620717411303424_rpow_eq`; tightest honest `T = 3/4294967296 ≈
0.00000000069` for this root). -/
theorem r_1180591620717411303424_le :
    (12 : ℝ) * ((((((1180591620717411303424 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 4294967296 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((1180591620717411303424 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M1180591620717411303424_rpow_eq
  have hrw : ((((1180591620717411303424 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((1180591620717411303424 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((34359738368 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 4294967296 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 1180591620717411303424` (`‖G - S2361183241434822606848‖ ≤ 3/4294967296`;
exact shape mirror of `eta_tail_295147905179352825856_le` at `:4187` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_1180591620717411303424_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 1180591620717411303424), etaDirichletTerm s k)‖ ≤
      (3 / 4294967296 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1180591620717411303424 (by norm_num)
  have h2M : 2 * 1180591620717411303424 = 2361183241434822606848 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_1180591620717411303424_le
  linarith

/-- The `M = 1180591620717411303424` constant honestly improves on the banked `M = 590295810358705651712`
constant (`3/4294967296 ≈ 0.00000000069 < 24/24296003840 ≈ 0.00000000098`). -/
theorem tail_1180591620717411303424_lt_590295810358705651712 : (3 / 4294967296 : ℝ) < (24 / 24296003840 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 2361183241434822606848` tail (`48592007680 ≤ 2361183241434822606848^{1/2}`;
generic mirror of `M590295810358705651712_rpow_ge` at `:4215` and latest exact
`M1180591620717411303424_rpow_eq` at `:4284`; honest floor via `48592007680^2 = 2361183210373178982400 ≤
2361183241434822606848` by `norm_num`; `2361183241434822606848 = 2^71` so root `34359738368·√2 ≈ 48592007999.61`
is NOT exact; conservative doubling `2 * 24296003840 = 48592007680` (three hundred nineteen below the true floor
`48592007999`); lower gap `31061643624448`). -/
theorem M2361183241434822606848_rpow_ge :
    (48592007680 : ℝ) ≤ ((((2361183241434822606848 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((48592007680 : ℝ) ^ (2 : ℕ)) ≤ ((((2361183241434822606848 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((2361183241434822606848 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((2361183241434822606848 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 2361183241434822606848` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/48592007680`; generic mirror of `r_590295810358705651712_le`
at `:4231` and latest exact `r_1180591620717411303424_le` at `:4310`; decay recomputed honestly
with `norm_num` via `M2361183241434822606848_rpow_ge`; honest conservative `T = 24/48592007680 ≈
0.00000000049` for the `48592007680` root lower). -/
theorem r_2361183241434822606848_le :
    (12 : ℝ) * ((((((2361183241434822606848 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 48592007680 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((2361183241434822606848 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((2361183241434822606848 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M2361183241434822606848_rpow_ge
  have hrw : ((((2361183241434822606848 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((2361183241434822606848 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((2361183241434822606848 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (48592007680 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((2361183241434822606848 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (48592007680 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((2361183241434822606848 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((48592007680 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((48592007680 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 48592007680 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 2361183241434822606848` (`‖G - S4722366482869645213696‖ ≤ 24/48592007680`;
generic mirror of `eta_tail_590295810358705651712_le` at `:4258` and latest exact
`eta_tail_1180591620717411303424_le` at `:4326` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_2361183241434822606848_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 2361183241434822606848), etaDirichletTerm s k)‖ ≤
      (24 / 48592007680 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 2361183241434822606848 (by norm_num)
  have h2M : 2 * 2361183241434822606848 = 4722366482869645213696 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_2361183241434822606848_le
  linarith

/-- The `M = 2361183241434822606848` constant honestly improves on the banked `M = 1180591620717411303424`
constant (`24/48592007680 ≈ 0.00000000049 < 3/4294967296 ≈ 0.00000000069`). -/
theorem tail_2361183241434822606848_lt_1180591620717411303424 : (24 / 48592007680 : ℝ) < (3 / 4294967296 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 4722366482869645213696` tail (`4722366482869645213696^{1/2} = 68719476736`
exact; exact shape mirror of `M1180591620717411303424_rpow_eq` at `:4284` and latest odd-floor
`M2361183241434822606848_rpow_ge`; honest via `68719476736^2 = 4722366482869645213696` by
`norm_num`; `4722366482869645213696 = 2^72` so the root is exact, unlike `2361183241434822606848`). -/
theorem M4722366482869645213696_rpow_eq :
    ((((4722366482869645213696 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (68719476736 : ℝ) := by
  have hx2 : ((((((4722366482869645213696 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((4722366482869645213696 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((68719476736 : ℝ) ^ (2 : ℕ)) = ((((4722366482869645213696 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((4722366482869645213696 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (68719476736 : ℝ) := by norm_num
  have hle1 : ((((((4722366482869645213696 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((68719476736 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((68719476736 : ℝ) ^ (2 : ℕ)) ≤
      ((((((4722366482869645213696 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 4722366482869645213696` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/68719476736 = 3/8589934592`; exact shape mirror of
`r_1180591620717411303424_le` at `:4310`; decay recomputed honestly with `norm_num`
via the exact `M4722366482869645213696_rpow_eq`; tightest honest `T = 3/8589934592 ≈
0.00000000034` for this root). -/
theorem r_4722366482869645213696_le :
    (12 : ℝ) * ((((((4722366482869645213696 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 8589934592 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((4722366482869645213696 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M4722366482869645213696_rpow_eq
  have hrw : ((((4722366482869645213696 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((4722366482869645213696 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((68719476736 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 8589934592 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 4722366482869645213696` (`‖G - S9444732965739290427392‖ ≤ 3/8589934592`;
exact shape mirror of `eta_tail_1180591620717411303424_le` at `:4326` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_4722366482869645213696_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 4722366482869645213696), etaDirichletTerm s k)‖ ≤
      (3 / 8589934592 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 4722366482869645213696 (by norm_num)
  have h2M : 2 * 4722366482869645213696 = 9444732965739290427392 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_4722366482869645213696_le
  linarith

/-- The `M = 4722366482869645213696` constant honestly improves on the banked `M = 2361183241434822606848`
constant (`3/8589934592 ≈ 0.00000000034 < 24/48592007680 ≈ 0.00000000049`). -/
theorem tail_4722366482869645213696_lt_2361183241434822606848 : (3 / 8589934592 : ℝ) < (24 / 48592007680 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 9444732965739290427392` tail (`97184015360 ≤ 9444732965739290427392^{1/2}`;
generic mirror of `M2361183241434822606848_rpow_ge` at `:4348` and latest exact
`M4722366482869645213696_rpow_eq` at `:4423`; honest floor via `97184015360^2 = 9444732841492715929600 ≤
9444732965739290427392` by `norm_num`; `9444732965739290427392 = 2^73` so root `68719476736·√2 ≈ 97184015999.22`
is NOT exact; conservative doubling `2 * 48592007680 = 97184015360` (six hundred thirty nine below the true floor
`97184015999`); lower gap `124246574497792`). -/
theorem M9444732965739290427392_rpow_ge :
    (97184015360 : ℝ) ≤ ((((9444732965739290427392 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((97184015360 : ℝ) ^ (2 : ℕ)) ≤ ((((9444732965739290427392 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((9444732965739290427392 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((9444732965739290427392 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 9444732965739290427392` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/97184015360`; generic mirror of `r_2361183241434822606848_le`
at `:4370` and latest exact `r_4722366482869645213696_le` at `:4449`; decay recomputed honestly
with `norm_num` via `M9444732965739290427392_rpow_ge`; honest conservative `T = 24/97184015360 ≈
0.00000000024` for the `97184015360` root lower). -/
theorem r_9444732965739290427392_le :
    (12 : ℝ) * ((((((9444732965739290427392 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 97184015360 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((9444732965739290427392 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((9444732965739290427392 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M9444732965739290427392_rpow_ge
  have hrw : ((((9444732965739290427392 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((9444732965739290427392 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((9444732965739290427392 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (97184015360 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((9444732965739290427392 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (97184015360 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((9444732965739290427392 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((97184015360 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((97184015360 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 97184015360 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 9444732965739290427392` (`‖G - S18889465931478580854784‖ ≤ 24/97184015360`;
generic mirror of `eta_tail_2361183241434822606848_le` at `:4397` and latest exact
`eta_tail_4722366482869645213696_le` at `:4465` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_9444732965739290427392_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 9444732965739290427392), etaDirichletTerm s k)‖ ≤
      (24 / 97184015360 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 9444732965739290427392 (by norm_num)
  have h2M : 2 * 9444732965739290427392 = 18889465931478580854784 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_9444732965739290427392_le
  linarith

/-- The `M = 9444732965739290427392` constant honestly improves on the banked `M = 4722366482869645213696`
constant (`24/97184015360 ≈ 0.00000000024 < 3/8589934592 ≈ 0.00000000034`). -/
theorem tail_9444732965739290427392_lt_4722366482869645213696 : (24 / 97184015360 : ℝ) < (3 / 8589934592 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 18889465931478580854784` tail (`18889465931478580854784^{1/2} = 137438953472`
exact; exact shape mirror of `M4722366482869645213696_rpow_eq` at `:4423` and latest odd-floor
`M9444732965739290427392_rpow_ge`; honest via `137438953472^2 = 18889465931478580854784` by
`norm_num`; `18889465931478580854784 = 2^74` so the root is exact, unlike `9444732965739290427392`). -/
theorem M18889465931478580854784_rpow_eq :
    ((((18889465931478580854784 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (137438953472 : ℝ) := by
  have hx2 : ((((((18889465931478580854784 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((18889465931478580854784 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((137438953472 : ℝ) ^ (2 : ℕ)) = ((((18889465931478580854784 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((18889465931478580854784 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (137438953472 : ℝ) := by norm_num
  have hle1 : ((((((18889465931478580854784 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((137438953472 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((137438953472 : ℝ) ^ (2 : ℕ)) ≤
      ((((((18889465931478580854784 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 18889465931478580854784` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/137438953472 = 3/17179869184`; exact shape mirror of
`r_4722366482869645213696_le` at `:4449`; decay recomputed honestly with `norm_num`
via the exact `M18889465931478580854784_rpow_eq`; tightest honest `T = 3/17179869184 ≈
0.00000000017` for this root). -/
theorem r_18889465931478580854784_le :
    (12 : ℝ) * ((((((18889465931478580854784 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 17179869184 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((18889465931478580854784 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M18889465931478580854784_rpow_eq
  have hrw : ((((18889465931478580854784 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((18889465931478580854784 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((137438953472 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 17179869184 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 18889465931478580854784` (`‖G - S37778931862957161709568‖ ≤ 3/17179869184`;
exact shape mirror of `eta_tail_4722366482869645213696_le` at `:4465` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_18889465931478580854784_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 18889465931478580854784), etaDirichletTerm s k)‖ ≤
      (3 / 17179869184 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 18889465931478580854784 (by norm_num)
  have h2M : 2 * 18889465931478580854784 = 37778931862957161709568 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_18889465931478580854784_le
  linarith

/-- The `M = 18889465931478580854784` constant honestly improves on the banked `M = 9444732965739290427392`
constant (`3/17179869184 ≈ 0.00000000017 < 24/97184015360 ≈ 0.00000000024`). -/
theorem tail_18889465931478580854784_lt_9444732965739290427392 : (3 / 17179869184 : ℝ) < (24 / 97184015360 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 37778931862957161709568` tail (`194368030720 ≤ 37778931862957161709568^{1/2}`;
generic mirror of `M9444732965739290427392_rpow_ge` at `:4493` and latest exact
`M18889465931478580854784_rpow_eq` at `:4562`; honest floor via `194368030720^2 = 37778931365970863718400 ≤
37778931862957161709568` by `norm_num`; `37778931862957161709568 = 2^75` so root `137438953472·√2 ≈ 194368031998.46`
is NOT exact; conservative doubling `2 * 97184015360 = 194368030720` (one thousand two hundred seventy eight below the true floor
`194368031998`); lower gap `496986297991168`). -/
theorem M37778931862957161709568_rpow_ge :
    (194368030720 : ℝ) ≤ ((((37778931862957161709568 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((194368030720 : ℝ) ^ (2 : ℕ)) ≤ ((((37778931862957161709568 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((37778931862957161709568 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((37778931862957161709568 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 37778931862957161709568` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/194368030720`; generic mirror of `r_9444732965739290427392_le`
at `:4509` and latest exact `r_18889465931478580854784_le` at `:4588`; decay recomputed honestly
with `norm_num` via `M37778931862957161709568_rpow_ge`; honest conservative `T = 24/194368030720 ≈
0.00000000012` for the `194368030720` root lower). -/
theorem r_37778931862957161709568_le :
    (12 : ℝ) * ((((((37778931862957161709568 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 194368030720 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((37778931862957161709568 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((37778931862957161709568 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M37778931862957161709568_rpow_ge
  have hrw : ((((37778931862957161709568 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((37778931862957161709568 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((37778931862957161709568 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (194368030720 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((37778931862957161709568 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (194368030720 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((37778931862957161709568 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((194368030720 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((194368030720 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 194368030720 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 37778931862957161709568` (`‖G - S75557863725914323419136‖ ≤ 24/194368030720`;
generic mirror of `eta_tail_9444732965739290427392_le` at `:4536` and latest exact
`eta_tail_18889465931478580854784_le` at `:4604` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_37778931862957161709568_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 37778931862957161709568), etaDirichletTerm s k)‖ ≤
      (24 / 194368030720 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 37778931862957161709568 (by norm_num)
  have h2M : 2 * 37778931862957161709568 = 75557863725914323419136 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_37778931862957161709568_le
  linarith

/-- The `M = 37778931862957161709568` constant honestly improves on the banked `M = 18889465931478580854784`
constant (`24/194368030720 ≈ 0.00000000012 < 3/17179869184 ≈ 0.00000000017`). -/
theorem tail_37778931862957161709568_lt_18889465931478580854784 : (24 / 194368030720 : ℝ) < (3 / 17179869184 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 75557863725914323419136` tail (`75557863725914323419136^{1/2} = 274877906944`
exact; exact shape mirror of `M18889465931478580854784_rpow_eq` at `:4562` and latest odd-floor
`M37778931862957161709568_rpow_ge`; honest via `274877906944^2 = 75557863725914323419136` by
`norm_num`; `75557863725914323419136 = 2^76` so the root is exact, unlike `37778931862957161709568`). -/
theorem M75557863725914323419136_rpow_eq :
    ((((75557863725914323419136 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (274877906944 : ℝ) := by
  have hx2 : ((((((75557863725914323419136 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((75557863725914323419136 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((274877906944 : ℝ) ^ (2 : ℕ)) = ((((75557863725914323419136 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((75557863725914323419136 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (274877906944 : ℝ) := by norm_num
  have hle1 : ((((((75557863725914323419136 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((274877906944 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((274877906944 : ℝ) ^ (2 : ℕ)) ≤
      ((((((75557863725914323419136 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 75557863725914323419136` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/274877906944 = 3/34359738368`; exact shape mirror of
`r_18889465931478580854784_le` at `:4588`; decay recomputed honestly with `norm_num`
via the exact `M75557863725914323419136_rpow_eq`; tightest honest `T = 3/34359738368 ≈
0.00000000008` for this root). -/
theorem r_75557863725914323419136_le :
    (12 : ℝ) * ((((((75557863725914323419136 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 34359738368 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((75557863725914323419136 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M75557863725914323419136_rpow_eq
  have hrw : ((((75557863725914323419136 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((75557863725914323419136 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((274877906944 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 34359738368 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 75557863725914323419136` (`‖G - S151115727451828646838272‖ ≤ 3/34359738368`;
exact shape mirror of `eta_tail_18889465931478580854784_le` at `:4604` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_75557863725914323419136_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 75557863725914323419136), etaDirichletTerm s k)‖ ≤
      (3 / 34359738368 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 75557863725914323419136 (by norm_num)
  have h2M : 2 * 75557863725914323419136 = 151115727451828646838272 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_75557863725914323419136_le
  linarith

/-- The `M = 75557863725914323419136` constant honestly improves on the banked `M = 37778931862957161709568`
constant (`3/34359738368 ≈ 0.00000000008 < 24/194368030720 ≈ 0.00000000012`). -/
theorem tail_75557863725914323419136_lt_37778931862957161709568 : (3 / 34359738368 : ℝ) < (24 / 194368030720 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 151115727451828646838272` tail (`388736061440 ≤ 151115727451828646838272^{1/2}`;
generic mirror of `M37778931862957161709568_rpow_ge` at `:4632` and latest exact
`M75557863725914323419136_rpow_eq` at `:4701`; honest floor via `388736061440^2 = 151115725463883454873600 ≤
151115727451828646838272` by `norm_num`; `151115727451828646838272 = 2^77` so root `274877906944·√2 ≈ 388736063996`
is NOT exact; conservative doubling `2 * 194368030720 = 388736061440` (two thousand five hundred fifty six below the true floor
`388736063996`); lower gap `1987945191964672`). -/
theorem M151115727451828646838272_rpow_ge :
    (388736061440 : ℝ) ≤ ((((151115727451828646838272 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((388736061440 : ℝ) ^ (2 : ℕ)) ≤ ((((151115727451828646838272 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((151115727451828646838272 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((151115727451828646838272 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 151115727451828646838272` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/388736061440`; generic mirror of `r_37778931862957161709568_le`
at `:4648` and latest exact `r_75557863725914323419136_le` at `:4727`; decay recomputed honestly
with `norm_num` via `M151115727451828646838272_rpow_ge`; honest conservative `T = 24/388736061440 ≈
0.00000000006` for the `388736061440` root lower). -/
theorem r_151115727451828646838272_le :
    (12 : ℝ) * ((((((151115727451828646838272 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 388736061440 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((151115727451828646838272 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((151115727451828646838272 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M151115727451828646838272_rpow_ge
  have hrw : ((((151115727451828646838272 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((151115727451828646838272 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((151115727451828646838272 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (388736061440 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((151115727451828646838272 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (388736061440 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((151115727451828646838272 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((388736061440 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((388736061440 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 388736061440 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 151115727451828646838272` (`‖G - S302231454903657293676544‖ ≤ 24/388736061440`;
generic mirror of `eta_tail_37778931862957161709568_le` at `:4675` and latest exact
`eta_tail_75557863725914323419136_le` at `:4743` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_151115727451828646838272_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 151115727451828646838272), etaDirichletTerm s k)‖ ≤
      (24 / 388736061440 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 151115727451828646838272 (by norm_num)
  have h2M : 2 * 151115727451828646838272 = 302231454903657293676544 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_151115727451828646838272_le
  linarith

/-- The `M = 151115727451828646838272` constant honestly improves on the banked `M = 75557863725914323419136`
constant (`24/388736061440 ≈ 0.00000000006 < 3/34359738368 ≈ 0.00000000008`). -/
theorem tail_151115727451828646838272_lt_75557863725914323419136 : (24 / 388736061440 : ℝ) < (3 / 34359738368 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 302231454903657293676544` tail (`302231454903657293676544^{1/2} = 549755813888`
exact; exact shape mirror of `M75557863725914323419136_rpow_eq` at `:4701` and latest odd-floor
`M151115727451828646838272_rpow_ge`; honest via `549755813888^2 = 302231454903657293676544` by
`norm_num`; `302231454903657293676544 = 2^78` so the root is exact, unlike `151115727451828646838272`). -/
theorem M302231454903657293676544_rpow_eq :
    ((((302231454903657293676544 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (549755813888 : ℝ) := by
  have hx2 : ((((((302231454903657293676544 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((302231454903657293676544 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((549755813888 : ℝ) ^ (2 : ℕ)) = ((((302231454903657293676544 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((302231454903657293676544 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (549755813888 : ℝ) := by norm_num
  have hle1 : ((((((302231454903657293676544 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((549755813888 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((549755813888 : ℝ) ^ (2 : ℕ)) ≤
      ((((((302231454903657293676544 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 302231454903657293676544` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/549755813888 = 3/68719476736`; exact shape mirror of
`r_75557863725914323419136_le` at `:4727`; decay recomputed honestly with `norm_num`
via the exact `M302231454903657293676544_rpow_eq`; tightest honest `T = 3/68719476736 ≈
0.00000000004` for this root). -/
theorem r_302231454903657293676544_le :
    (12 : ℝ) * ((((((302231454903657293676544 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 68719476736 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((302231454903657293676544 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M302231454903657293676544_rpow_eq
  have hrw : ((((302231454903657293676544 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((302231454903657293676544 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((549755813888 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 68719476736 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 302231454903657293676544` (`‖G - S604462909807314587353088‖ ≤ 3/68719476736`;
exact shape mirror of `eta_tail_75557863725914323419136_le` at `:4743` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_302231454903657293676544_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 302231454903657293676544), etaDirichletTerm s k)‖ ≤
      (3 / 68719476736 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 302231454903657293676544 (by norm_num)
  have h2M : 2 * 302231454903657293676544 = 604462909807314587353088 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_302231454903657293676544_le
  linarith

/-- The `M = 302231454903657293676544` constant honestly improves on the banked `M = 151115727451828646838272`
constant (`3/68719476736 ≈ 0.00000000004 < 24/388736061440 ≈ 0.00000000006`). -/
theorem tail_302231454903657293676544_lt_151115727451828646838272 : (3 / 68719476736 : ℝ) < (24 / 388736061440 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 604462909807314587353088` tail (`777472122880 ≤ 604462909807314587353088^{1/2}`;
generic mirror of `M151115727451828646838272_rpow_ge` at `:4771` and latest exact
`M302231454903657293676544_rpow_eq` at `:4840`; honest floor via `777472122880^2 = 604462901855533819494400 ≤
604462909807314587353088` by `norm_num`; `604462909807314587353088 = 2^79` so root `549755813888·√2 ≈ 777472127993`
is NOT exact; conservative doubling `2 * 388736061440 = 777472122880` (five thousand one hundred thirteen below the true floor
`777472127993`); lower gap `7951780767858688`). -/
theorem M604462909807314587353088_rpow_ge :
    (777472122880 : ℝ) ≤ ((((604462909807314587353088 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((777472122880 : ℝ) ^ (2 : ℕ)) ≤ ((((604462909807314587353088 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((604462909807314587353088 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((604462909807314587353088 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 604462909807314587353088` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/777472122880`; generic mirror of `r_151115727451828646838272_le`
at `:4787` and latest exact `r_302231454903657293676544_le` at `:4866`; decay recomputed honestly
with `norm_num` via `M604462909807314587353088_rpow_ge`; honest conservative `T = 24/777472122880 ≈
0.00000000003` for the `777472122880` root lower). -/
theorem r_604462909807314587353088_le :
    (12 : ℝ) * ((((((604462909807314587353088 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 777472122880 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((604462909807314587353088 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((604462909807314587353088 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M604462909807314587353088_rpow_ge
  have hrw : ((((604462909807314587353088 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((604462909807314587353088 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((604462909807314587353088 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (777472122880 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((604462909807314587353088 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (777472122880 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((604462909807314587353088 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((777472122880 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((777472122880 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 777472122880 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 604462909807314587353088` (`‖G - S1208925819614629174706176‖ ≤ 24/777472122880`;
generic mirror of `eta_tail_151115727451828646838272_le` at `:4814` and latest exact
`eta_tail_302231454903657293676544_le` at `:4882` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_604462909807314587353088_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 604462909807314587353088), etaDirichletTerm s k)‖ ≤
      (24 / 777472122880 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 604462909807314587353088 (by norm_num)
  have h2M : 2 * 604462909807314587353088 = 1208925819614629174706176 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_604462909807314587353088_le
  linarith

/-- The `M = 604462909807314587353088` constant honestly improves on the banked `M = 302231454903657293676544`
constant (`24/777472122880 ≈ 0.00000000003 < 3/68719476736 ≈ 0.00000000004`). -/
theorem tail_604462909807314587353088_lt_302231454903657293676544 : (24 / 777472122880 : ℝ) < (3 / 68719476736 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 1208925819614629174706176` tail (`1208925819614629174706176^{1/2} = 1099511627776`
exact; exact shape mirror of `M302231454903657293676544_rpow_eq` at `:4840` and latest odd-floor
`M604462909807314587353088_rpow_ge`; honest via `1099511627776^2 = 1208925819614629174706176` by
`norm_num`; `1208925819614629174706176 = 2^80` so the root is exact, unlike `604462909807314587353088`). -/
theorem M1208925819614629174706176_rpow_eq :
    ((((1208925819614629174706176 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (1099511627776 : ℝ) := by
  have hx2 : ((((((1208925819614629174706176 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((1208925819614629174706176 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((1099511627776 : ℝ) ^ (2 : ℕ)) = ((((1208925819614629174706176 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((1208925819614629174706176 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (1099511627776 : ℝ) := by norm_num
  have hle1 : ((((((1208925819614629174706176 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((1099511627776 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((1099511627776 : ℝ) ^ (2 : ℕ)) ≤
      ((((((1208925819614629174706176 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 1208925819614629174706176` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/1099511627776 = 3/137438953472`; exact shape mirror of
`r_302231454903657293676544_le` at `:4866`; decay recomputed honestly with `norm_num`
via the exact `M1208925819614629174706176_rpow_eq`; tightest honest `T = 3/137438953472 ≈
0.00000000002` for this root). -/
theorem r_1208925819614629174706176_le :
    (12 : ℝ) * ((((((1208925819614629174706176 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 137438953472 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((1208925819614629174706176 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M1208925819614629174706176_rpow_eq
  have hrw : ((((1208925819614629174706176 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((1208925819614629174706176 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((1099511627776 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 137438953472 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 1208925819614629174706176` (`‖G - S2417851639229258349412352‖ ≤ 3/137438953472`;
exact shape mirror of `eta_tail_302231454903657293676544_le` at `:4882` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_1208925819614629174706176_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 1208925819614629174706176), etaDirichletTerm s k)‖ ≤
      (3 / 137438953472 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1208925819614629174706176 (by norm_num)
  have h2M : 2 * 1208925819614629174706176 = 2417851639229258349412352 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_1208925819614629174706176_le
  linarith

/-- The `M = 1208925819614629174706176` constant honestly improves on the banked `M = 604462909807314587353088`
constant (`3/137438953472 ≈ 0.00000000002 < 24/777472122880 ≈ 0.00000000003`). -/
theorem tail_1208925819614629174706176_lt_604462909807314587353088 : (3 / 137438953472 : ℝ) < (24 / 777472122880 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 2417851639229258349412352` tail (`1554944245760 ≤ 2417851639229258349412352^{1/2}`;
generic mirror of `M604462909807314587353088_rpow_ge` at `:4910` and latest exact
`M1208925819614629174706176_rpow_eq` at `:4979`; honest floor via `1554944245760^2 = 2417851607422135277977600 ≤
2417851639229258349412352` by `norm_num`; `2417851639229258349412352 = 2^81` so root `1099511627776·√2 ≈ 1554944255987`
is NOT exact; conservative doubling `2 * 777472122880 = 1554944245760` (ten thousand two hundred twenty seven below the true floor
`1554944255987`); lower gap `31807123071434752`). -/
theorem M2417851639229258349412352_rpow_ge :
    (1554944245760 : ℝ) ≤ ((((2417851639229258349412352 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((1554944245760 : ℝ) ^ (2 : ℕ)) ≤ ((((2417851639229258349412352 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((2417851639229258349412352 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((2417851639229258349412352 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 2417851639229258349412352` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/1554944245760`; generic mirror of `r_604462909807314587353088_le`
at `:4926` and latest exact `r_1208925819614629174706176_le` at `:5005`; decay recomputed honestly
with `norm_num` via `M2417851639229258349412352_rpow_ge`; honest conservative `T = 24/1554944245760 ≈
0.00000000001` for the `1554944245760` root lower). -/
theorem r_2417851639229258349412352_le :
    (12 : ℝ) * ((((((2417851639229258349412352 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 1554944245760 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((2417851639229258349412352 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((2417851639229258349412352 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M2417851639229258349412352_rpow_ge
  have hrw : ((((2417851639229258349412352 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((2417851639229258349412352 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((2417851639229258349412352 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (1554944245760 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((2417851639229258349412352 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (1554944245760 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((2417851639229258349412352 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((1554944245760 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((1554944245760 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 1554944245760 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 2417851639229258349412352` (`‖G - S4835703278458516698824704‖ ≤ 24/1554944245760`;
generic mirror of `eta_tail_604462909807314587353088_le` at `:4953` and latest exact
`eta_tail_1208925819614629174706176_le` at `:5021` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_2417851639229258349412352_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 2417851639229258349412352), etaDirichletTerm s k)‖ ≤
      (24 / 1554944245760 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 2417851639229258349412352 (by norm_num)
  have h2M : 2 * 2417851639229258349412352 = 4835703278458516698824704 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_2417851639229258349412352_le
  linarith

/-- The `M = 2417851639229258349412352` constant honestly improves on the banked `M = 1208925819614629174706176`
constant (`24/1554944245760 ≈ 0.00000000001 < 3/137438953472 ≈ 0.00000000002`). -/
theorem tail_2417851639229258349412352_lt_1208925819614629174706176 : (24 / 1554944245760 : ℝ) < (3 / 137438953472 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 4835703278458516698824704` tail (`4835703278458516698824704^{1/2} = 2199023255552`
exact; exact shape mirror of `M1208925819614629174706176_rpow_eq` at `:4979` and latest odd-floor
`M2417851639229258349412352_rpow_ge`; honest via `2199023255552^2 = 4835703278458516698824704` by
`norm_num`; `4835703278458516698824704 = 2^82` so the root is exact, unlike `2417851639229258349412352`). -/
theorem M4835703278458516698824704_rpow_eq :
    ((((4835703278458516698824704 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (2199023255552 : ℝ) := by
  have hx2 : ((((((4835703278458516698824704 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((4835703278458516698824704 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((2199023255552 : ℝ) ^ (2 : ℕ)) = ((((4835703278458516698824704 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((4835703278458516698824704 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (2199023255552 : ℝ) := by norm_num
  have hle1 : ((((((4835703278458516698824704 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((2199023255552 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((2199023255552 : ℝ) ^ (2 : ℕ)) ≤
      ((((((4835703278458516698824704 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 4835703278458516698824704` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/2199023255552 = 3/274877906944`; exact shape mirror of
`r_1208925819614629174706176_le` at `:5005`; decay recomputed honestly with `norm_num`
via the exact `M4835703278458516698824704_rpow_eq`; tightest honest `T = 3/274877906944 ≈
0.00000000001` for this root). -/
theorem r_4835703278458516698824704_le :
    (12 : ℝ) * ((((((4835703278458516698824704 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 274877906944 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((4835703278458516698824704 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M4835703278458516698824704_rpow_eq
  have hrw : ((((4835703278458516698824704 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((4835703278458516698824704 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((2199023255552 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 274877906944 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 4835703278458516698824704` (`‖G - S9671406556917033397649408‖ ≤ 3/274877906944`;
exact shape mirror of `eta_tail_1208925819614629174706176_le` at `:5021` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_4835703278458516698824704_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 4835703278458516698824704), etaDirichletTerm s k)‖ ≤
      (3 / 274877906944 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 4835703278458516698824704 (by norm_num)
  have h2M : 2 * 4835703278458516698824704 = 9671406556917033397649408 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_4835703278458516698824704_le
  linarith

/-- The `M = 4835703278458516698824704` constant honestly improves on the banked `M = 2417851639229258349412352`
constant (`3/274877906944 ≈ 0.00000000001 < 24/1554944245760 ≈ 0.00000000001`). -/
theorem tail_4835703278458516698824704_lt_2417851639229258349412352 : (3 / 274877906944 : ℝ) < (24 / 1554944245760 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 9671406556917033397649408` tail (`3109888491520 ≤ 9671406556917033397649408^{1/2}`;
generic mirror of `M2417851639229258349412352_rpow_ge` at `:5049` and latest exact
`M4835703278458516698824704_rpow_eq` at `:5118`; honest floor via `3109888491520^2 = 9671406429688541111910400 ≤
9671406556917033397649408` by `norm_num`; `9671406556917033397649408 = 2^83` so root `2199023255552·√2 ≈ 3109888511975`
is NOT exact; conservative doubling `2 * 1554944245760 = 3109888491520` (twenty thousand four hundred fifty five below the true floor
`3109888511975`); lower gap `127228492285739008`). -/
theorem M9671406556917033397649408_rpow_ge :
    (3109888491520 : ℝ) ≤ ((((9671406556917033397649408 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((3109888491520 : ℝ) ^ (2 : ℕ)) ≤ ((((9671406556917033397649408 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((9671406556917033397649408 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((9671406556917033397649408 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 9671406556917033397649408` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/3109888491520`; generic mirror of `r_2417851639229258349412352_le`
at `:5065` and latest exact `r_4835703278458516698824704_le` at `:5144`; decay recomputed honestly
with `norm_num` via `M9671406556917033397649408_rpow_ge`; honest conservative `T = 24/3109888491520 ≈
0.00000000001` for the `3109888491520` root lower). -/
theorem r_9671406556917033397649408_le :
    (12 : ℝ) * ((((((9671406556917033397649408 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 3109888491520 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((9671406556917033397649408 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((9671406556917033397649408 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M9671406556917033397649408_rpow_ge
  have hrw : ((((9671406556917033397649408 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((9671406556917033397649408 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((9671406556917033397649408 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (3109888491520 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((9671406556917033397649408 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (3109888491520 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((9671406556917033397649408 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((3109888491520 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((3109888491520 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 3109888491520 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 9671406556917033397649408` (`‖G - S19342813113834066795298816‖ ≤ 24/3109888491520`;
generic mirror of `eta_tail_2417851639229258349412352_le` at `:5092` and latest exact
`eta_tail_4835703278458516698824704_le` at `:5160` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_9671406556917033397649408_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 9671406556917033397649408), etaDirichletTerm s k)‖ ≤
      (24 / 3109888491520 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 9671406556917033397649408 (by norm_num)
  have h2M : 2 * 9671406556917033397649408 = 19342813113834066795298816 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_9671406556917033397649408_le
  linarith

/-- The `M = 9671406556917033397649408` constant honestly improves on the banked `M = 4835703278458516698824704`
constant (`24/3109888491520 ≈ 0.00000000001 < 3/274877906944 ≈ 0.00000000001`). -/
theorem tail_9671406556917033397649408_lt_4835703278458516698824704 : (24 / 3109888491520 : ℝ) < (3 / 274877906944 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 19342813113834066795298816` tail (`19342813113834066795298816^{1/2} = 4398046511104`
exact; exact shape mirror of `M4835703278458516698824704_rpow_eq` at `:5118` and latest odd-floor
`M9671406556917033397649408_rpow_ge`; honest via `4398046511104^2 = 19342813113834066795298816` by
`norm_num`; `19342813113834066795298816 = 2^84` so the root is exact, unlike `9671406556917033397649408`). -/
theorem M19342813113834066795298816_rpow_eq :
    ((((19342813113834066795298816 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (4398046511104 : ℝ) := by
  have hx2 : ((((((19342813113834066795298816 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((19342813113834066795298816 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((4398046511104 : ℝ) ^ (2 : ℕ)) = ((((19342813113834066795298816 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((19342813113834066795298816 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (4398046511104 : ℝ) := by norm_num
  have hle1 : ((((((19342813113834066795298816 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((4398046511104 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((4398046511104 : ℝ) ^ (2 : ℕ)) ≤
      ((((((19342813113834066795298816 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 19342813113834066795298816` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/4398046511104 = 3/549755813888`; exact shape mirror of
`r_4835703278458516698824704_le` at `:5144`; decay recomputed honestly with `norm_num`
via the exact `M19342813113834066795298816_rpow_eq`; tightest honest `T = 3/549755813888 ≈
0.00000000001` for this root). -/
theorem r_19342813113834066795298816_le :
    (12 : ℝ) * ((((((19342813113834066795298816 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 549755813888 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((19342813113834066795298816 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M19342813113834066795298816_rpow_eq
  have hrw : ((((19342813113834066795298816 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((19342813113834066795298816 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((4398046511104 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 549755813888 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 19342813113834066795298816` (`‖G - S38685626227668133590597632‖ ≤ 3/549755813888`;
exact shape mirror of `eta_tail_4835703278458516698824704_le` at `:5160` — numerals use only
`Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_19342813113834066795298816_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 19342813113834066795298816), etaDirichletTerm s k)‖ ≤
      (3 / 549755813888 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 19342813113834066795298816 (by norm_num)
  have h2M : 2 * 19342813113834066795298816 = 38685626227668133590597632 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_19342813113834066795298816_le
  linarith

/-- The `M = 19342813113834066795298816` constant honestly improves on the banked `M = 9671406556917033397649408`
constant (`3/549755813888 ≈ 0.00000000001 < 24/3109888491520 ≈ 0.00000000001`). -/
theorem tail_19342813113834066795298816_lt_9671406556917033397649408 : (3 / 549755813888 : ℝ) < (24 / 3109888491520 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 38685626227668133590597632` tail
(`6219776983040 ≤ 38685626227668133590597632^{1/2}`; generic mirror of
`M9671406556917033397649408_rpow_ge` at `:5188` and latest exact
`M19342813113834066795298816_rpow_eq` at `:5257`; honest floor via
`6219776983040 = 2 * 3109888491520` with `6219776983040^2 ≤ 38685626227668133590597632`
by `norm_num`; `38685626227668133590597632 = 2^85` so root `4398046511104·√2 ≈
6219776983040.xx` is NOT exact, unlike `19342813113834066795298816`). -/
theorem M38685626227668133590597632_rpow_ge :
    (6219776983040 : ℝ) ≤ ((((38685626227668133590597632 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((6219776983040 : ℝ) ^ (2 : ℕ)) ≤ ((((38685626227668133590597632 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((38685626227668133590597632 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((38685626227668133590597632 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 38685626227668133590597632` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/6219776983040`; generic mirror of
`r_9671406556917033397649408_le` at `:5204` and latest exact
`r_19342813113834066795298816_le` at `:5283`; decay recomputed honestly with
`norm_num` via `M38685626227668133590597632_rpow_ge`; honest conservative
`T = 24/6219776983040 ≈ 0.00000000001` for the `6219776983040` root lower). -/
theorem r_38685626227668133590597632_le :
    (12 : ℝ) * ((((((38685626227668133590597632 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 6219776983040 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((38685626227668133590597632 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((38685626227668133590597632 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M38685626227668133590597632_rpow_ge
  have hrw : ((((38685626227668133590597632 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((38685626227668133590597632 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((38685626227668133590597632 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (6219776983040 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((38685626227668133590597632 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (6219776983040 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((38685626227668133590597632 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((6219776983040 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((6219776983040 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 6219776983040 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 38685626227668133590597632`
(`‖G - S77371252455336267181195264‖ ≤ 24/6219776983040`; generic mirror of
`eta_tail_9671406556917033397649408_le` at `:5231` and latest exact
`eta_tail_19342813113834066795298816_le` at `:5299` — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_38685626227668133590597632_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 38685626227668133590597632), etaDirichletTerm s k)‖ ≤
      (24 / 6219776983040 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 38685626227668133590597632 (by norm_num)
  have h2M : 2 * 38685626227668133590597632 = 77371252455336267181195264 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_38685626227668133590597632_le
  linarith

/-- The `M = 38685626227668133590597632` constant honestly improves on the banked
`M = 19342813113834066795298816` constant
(`24/6219776983040 ≈ 0.00000000001 < 3/549755813888 ≈ 0.00000000001`). -/
theorem tail_38685626227668133590597632_lt_19342813113834066795298816 : (24 / 6219776983040 : ℝ) < (3 / 549755813888 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 77371252455336267181195264` tail
(`77371252455336267181195264^{1/2} = 8796093022208` exact; exact shape mirror of
`M19342813113834066795298816_rpow_eq` at `:5257` and latest odd-floor
`M38685626227668133590597632_rpow_ge` above; honest via
`8796093022208^2 = 77371252455336267181195264` by `norm_num`;
`77371252455336267181195264 = 2^86` so the root is exact, unlike
`38685626227668133590597632`). -/
theorem M77371252455336267181195264_rpow_eq :
    ((((77371252455336267181195264 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (8796093022208 : ℝ) := by
  have hx2 : ((((((77371252455336267181195264 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((77371252455336267181195264 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((8796093022208 : ℝ) ^ (2 : ℕ)) = ((((77371252455336267181195264 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((77371252455336267181195264 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (8796093022208 : ℝ) := by norm_num
  have hle1 : ((((((77371252455336267181195264 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((8796093022208 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((8796093022208 : ℝ) ^ (2 : ℕ)) ≤
      ((((((77371252455336267181195264 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 77371252455336267181195264` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/8796093022208 = 3/1099511627776`; exact shape mirror of
`r_19342813113834066795298816_le` at `:5283`; decay recomputed honestly with
`norm_num` via the exact `M77371252455336267181195264_rpow_eq`; tightest honest
`T = 3/1099511627776 ≈ 0.00000000001` for this root). -/
theorem r_77371252455336267181195264_le :
    (12 : ℝ) * ((((((77371252455336267181195264 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 1099511627776 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((77371252455336267181195264 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M77371252455336267181195264_rpow_eq
  have hrw : ((((77371252455336267181195264 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((77371252455336267181195264 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((8796093022208 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 1099511627776 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 77371252455336267181195264`
(`‖G - S154742504910672534362390528‖ ≤ 3/1099511627776`; exact shape mirror of
`eta_tail_19342813113834066795298816_le` at `:5299` — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_77371252455336267181195264_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 77371252455336267181195264), etaDirichletTerm s k)‖ ≤
      (3 / 1099511627776 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 77371252455336267181195264 (by norm_num)
  have h2M : 2 * 77371252455336267181195264 = 154742504910672534362390528 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_77371252455336267181195264_le
  linarith

/-- The `M = 77371252455336267181195264` constant honestly improves on the banked
`M = 38685626227668133590597632` constant
(`3/1099511627776 ≈ 0.00000000001 < 24/6219776983040 ≈ 0.00000000001`). -/
theorem tail_77371252455336267181195264_lt_38685626227668133590597632 : (3 / 1099511627776 : ℝ) < (24 / 6219776983040 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 154742504910672534362390528` tail
(`12439553966080 ≤ 154742504910672534362390528^{1/2}`; generic mirror of
`M38685626227668133590597632_rpow_ge` and latest exact
`M77371252455336267181195264_rpow_eq` above; honest floor via
`12439553966080 = 2 * 6219776983040` with `12439553966080^2 ≤ 154742504910672534362390528`
by `norm_num`; `154742504910672534362390528 = 2^87` so root `8796093022208·√2 ≈
12439553966080.xx` is NOT exact, unlike `77371252455336267181195264`). -/
theorem M154742504910672534362390528_rpow_ge :
    (12439553966080 : ℝ) ≤ ((((154742504910672534362390528 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((12439553966080 : ℝ) ^ (2 : ℕ)) ≤ ((((154742504910672534362390528 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((154742504910672534362390528 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((154742504910672534362390528 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 154742504910672534362390528` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/12439553966080`; generic mirror of
`r_38685626227668133590597632_le` and latest exact
`r_77371252455336267181195264_le`; decay recomputed honestly with
`norm_num` via `M154742504910672534362390528_rpow_ge`; honest conservative
`T = 24/12439553966080 ≈ 0.00000000001` for the `12439553966080` root lower). -/
theorem r_154742504910672534362390528_le :
    (12 : ℝ) * ((((((154742504910672534362390528 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 12439553966080 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((154742504910672534362390528 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((154742504910672534362390528 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M154742504910672534362390528_rpow_ge
  have hrw : ((((154742504910672534362390528 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((154742504910672534362390528 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((154742504910672534362390528 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (12439553966080 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((154742504910672534362390528 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (12439553966080 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((154742504910672534362390528 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((12439553966080 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((12439553966080 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 12439553966080 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 154742504910672534362390528`
(`‖G - S309485009821345068724781056‖ ≤ 24/12439553966080`; generic mirror of
`eta_tail_38685626227668133590597632_le` and latest exact
`eta_tail_77371252455336267181195264_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_154742504910672534362390528_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 154742504910672534362390528), etaDirichletTerm s k)‖ ≤
      (24 / 12439553966080 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 154742504910672534362390528 (by norm_num)
  have h2M : 2 * 154742504910672534362390528 = 309485009821345068724781056 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_154742504910672534362390528_le
  linarith

/-- The `M = 154742504910672534362390528` constant honestly improves on the banked
`M = 77371252455336267181195264` constant
(`24/12439553966080 ≈ 0.00000000001 < 3/1099511627776 ≈ 0.00000000001`). -/
theorem tail_154742504910672534362390528_lt_77371252455336267181195264 : (24 / 12439553966080 : ℝ) < (3 / 1099511627776 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 309485009821345068724781056` tail
(`309485009821345068724781056^{1/2} = 17592186044416` exact; exact shape mirror of
`M77371252455336267181195264_rpow_eq` above and latest odd-floor
`M154742504910672534362390528_rpow_ge` above; honest via
`17592186044416^2 = 309485009821345068724781056` by `norm_num`;
`309485009821345068724781056 = 2^88` so the root is exact, unlike
`154742504910672534362390528`). -/
theorem M309485009821345068724781056_rpow_eq :
    ((((309485009821345068724781056 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (17592186044416 : ℝ) := by
  have hx2 : ((((((309485009821345068724781056 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((309485009821345068724781056 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((17592186044416 : ℝ) ^ (2 : ℕ)) = ((((309485009821345068724781056 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((309485009821345068724781056 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (17592186044416 : ℝ) := by norm_num
  have hle1 : ((((((309485009821345068724781056 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((17592186044416 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((17592186044416 : ℝ) ^ (2 : ℕ)) ≤
      ((((((309485009821345068724781056 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 309485009821345068724781056` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/17592186044416 = 3/2199023255552`; exact shape mirror of
`r_77371252455336267181195264_le`; decay recomputed honestly with
`norm_num` via the exact `M309485009821345068724781056_rpow_eq`; tightest honest
`T = 3/2199023255552 ≈ 0.00000000001` for this root). -/
theorem r_309485009821345068724781056_le :
    (12 : ℝ) * ((((((309485009821345068724781056 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 2199023255552 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((309485009821345068724781056 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M309485009821345068724781056_rpow_eq
  have hrw : ((((309485009821345068724781056 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((309485009821345068724781056 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((17592186044416 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 2199023255552 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 309485009821345068724781056`
(`‖G - S618970019642690137449562112‖ ≤ 3/2199023255552`; exact shape mirror of
`eta_tail_77371252455336267181195264_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_309485009821345068724781056_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 309485009821345068724781056), etaDirichletTerm s k)‖ ≤
      (3 / 2199023255552 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 309485009821345068724781056 (by norm_num)
  have h2M : 2 * 309485009821345068724781056 = 618970019642690137449562112 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_309485009821345068724781056_le
  linarith

/-- The `M = 309485009821345068724781056` constant honestly improves on the banked
`M = 154742504910672534362390528` constant
(`3/2199023255552 ≈ 0.00000000001 < 24/12439553966080 ≈ 0.00000000001`). -/
theorem tail_309485009821345068724781056_lt_154742504910672534362390528 : (3 / 2199023255552 : ℝ) < (24 / 12439553966080 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 618970019642690137449562112` tail
(`24879107932160 ≤ 618970019642690137449562112^{1/2}`; generic mirror of
`M154742504910672534362390528_rpow_ge` and latest exact
`M309485009821345068724781056_rpow_eq` above; honest floor via
`24879107932160 = 2 * 12439553966080` with `24879107932160^2 ≤ 618970019642690137449562112`
by `norm_num`; `618970019642690137449562112 = 2^89` so root `17592186044416·√2 ≈
24879107932160.xx` is NOT exact, unlike `309485009821345068724781056`). -/
theorem M618970019642690137449562112_rpow_ge :
    (24879107932160 : ℝ) ≤ ((((618970019642690137449562112 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((24879107932160 : ℝ) ^ (2 : ℕ)) ≤ ((((618970019642690137449562112 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((618970019642690137449562112 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((618970019642690137449562112 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 618970019642690137449562112` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/24879107932160`; generic mirror of
`r_154742504910672534362390528_le` and latest exact
`r_309485009821345068724781056_le`; decay recomputed honestly with
`norm_num` via `M618970019642690137449562112_rpow_ge`; honest conservative
`T = 24/24879107932160 ≈ 0.00000000001` for the `24879107932160` root lower). -/
theorem r_618970019642690137449562112_le :
    (12 : ℝ) * ((((((618970019642690137449562112 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 24879107932160 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((618970019642690137449562112 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((618970019642690137449562112 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M618970019642690137449562112_rpow_ge
  have hrw : ((((618970019642690137449562112 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((618970019642690137449562112 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((618970019642690137449562112 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (24879107932160 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((618970019642690137449562112 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (24879107932160 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((618970019642690137449562112 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((24879107932160 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((24879107932160 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 24879107932160 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 618970019642690137449562112`
(`‖G - S1237940039285380274899124224‖ ≤ 24/24879107932160`; generic mirror of
`eta_tail_154742504910672534362390528_le` and latest exact
`eta_tail_309485009821345068724781056_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_618970019642690137449562112_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 618970019642690137449562112), etaDirichletTerm s k)‖ ≤
      (24 / 24879107932160 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 618970019642690137449562112 (by norm_num)
  have h2M : 2 * 618970019642690137449562112 = 1237940039285380274899124224 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_618970019642690137449562112_le
  linarith

/-- The `M = 618970019642690137449562112` constant honestly improves on the banked
`M = 309485009821345068724781056` constant
(`24/24879107932160 ≈ 0.00000000001 < 3/2199023255552 ≈ 0.00000000001`). -/
theorem tail_618970019642690137449562112_lt_309485009821345068724781056 : (24 / 24879107932160 : ℝ) < (3 / 2199023255552 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 1237940039285380274899124224` tail
(`1237940039285380274899124224^{1/2} = 35184372088832` exact; exact shape mirror of
`M309485009821345068724781056_rpow_eq` above and latest odd-floor
`M618970019642690137449562112_rpow_ge` above; honest via
`35184372088832^2 = 1237940039285380274899124224` by `norm_num`;
`1237940039285380274899124224 = 2^90` so the root is exact, unlike
`618970019642690137449562112`). -/
theorem M1237940039285380274899124224_rpow_eq :
    ((((1237940039285380274899124224 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (35184372088832 : ℝ) := by
  have hx2 : ((((((1237940039285380274899124224 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((1237940039285380274899124224 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((35184372088832 : ℝ) ^ (2 : ℕ)) = ((((1237940039285380274899124224 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((1237940039285380274899124224 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (35184372088832 : ℝ) := by norm_num
  have hle1 : ((((((1237940039285380274899124224 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((35184372088832 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((35184372088832 : ℝ) ^ (2 : ℕ)) ≤
      ((((((1237940039285380274899124224 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 1237940039285380274899124224` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/35184372088832 = 3/4398046511104`; exact shape mirror of
`r_309485009821345068724781056_le`; decay recomputed honestly with
`norm_num` via the exact `M1237940039285380274899124224_rpow_eq`; tightest honest
`T = 3/4398046511104 ≈ 0.00000000001` for this root). -/
theorem r_1237940039285380274899124224_le :
    (12 : ℝ) * ((((((1237940039285380274899124224 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 4398046511104 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((1237940039285380274899124224 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M1237940039285380274899124224_rpow_eq
  have hrw : ((((1237940039285380274899124224 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((1237940039285380274899124224 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((35184372088832 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 4398046511104 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 1237940039285380274899124224`
(`‖G - S2475880078570760549798248448‖ ≤ 3/4398046511104`; exact shape mirror of
`eta_tail_309485009821345068724781056_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_1237940039285380274899124224_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 1237940039285380274899124224), etaDirichletTerm s k)‖ ≤
      (3 / 4398046511104 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1237940039285380274899124224 (by norm_num)
  have h2M : 2 * 1237940039285380274899124224 = 2475880078570760549798248448 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_1237940039285380274899124224_le
  linarith

/-- The `M = 1237940039285380274899124224` constant honestly improves on the banked
`M = 618970019642690137449562112` constant
(`3/4398046511104 ≈ 0.00000000001 < 24/24879107932160 ≈ 0.00000000001`). -/
theorem tail_1237940039285380274899124224_lt_618970019642690137449562112 : (3 / 4398046511104 : ℝ) < (24 / 24879107932160 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 2475880078570760549798248448` tail
(`49758215864320 ≤ 2475880078570760549798248448^{1/2}`; generic mirror of
`M618970019642690137449562112_rpow_ge` and latest exact
`M1237940039285380274899124224_rpow_eq` above; honest floor via
`49758215864320 = 2 * 24879107932160` with `49758215864320^2 ≤ 2475880078570760549798248448`
by `norm_num`; `2475880078570760549798248448 = 2^91` so root `35184372088832·√2 ≈
49758215864320.xx` is NOT exact, unlike `1237940039285380274899124224`). -/
theorem M2475880078570760549798248448_rpow_ge :
    (49758215864320 : ℝ) ≤ ((((2475880078570760549798248448 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((49758215864320 : ℝ) ^ (2 : ℕ)) ≤ ((((2475880078570760549798248448 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((2475880078570760549798248448 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((2475880078570760549798248448 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 2475880078570760549798248448` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/49758215864320`; generic mirror of
`r_618970019642690137449562112_le` and latest exact
`r_1237940039285380274899124224_le`; decay recomputed honestly with
`norm_num` via `M2475880078570760549798248448_rpow_ge`; honest conservative
`T = 24/49758215864320 ≈ 0.00000000001` for the `49758215864320` root lower). -/
theorem r_2475880078570760549798248448_le :
    (12 : ℝ) * ((((((2475880078570760549798248448 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 49758215864320 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((2475880078570760549798248448 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((2475880078570760549798248448 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M2475880078570760549798248448_rpow_ge
  have hrw : ((((2475880078570760549798248448 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((2475880078570760549798248448 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((2475880078570760549798248448 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (49758215864320 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((2475880078570760549798248448 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (49758215864320 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((2475880078570760549798248448 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((49758215864320 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((49758215864320 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 49758215864320 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 2475880078570760549798248448`
(`‖G - S4951760157141521099596496896‖ ≤ 24/49758215864320`; generic mirror of
`eta_tail_618970019642690137449562112_le` and latest exact
`eta_tail_1237940039285380274899124224_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_2475880078570760549798248448_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 2475880078570760549798248448), etaDirichletTerm s k)‖ ≤
      (24 / 49758215864320 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 2475880078570760549798248448 (by norm_num)
  have h2M : 2 * 2475880078570760549798248448 = 4951760157141521099596496896 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_2475880078570760549798248448_le
  linarith

/-- The `M = 2475880078570760549798248448` constant honestly improves on the banked
`M = 1237940039285380274899124224` constant
(`24/49758215864320 ≈ 0.00000000001 < 3/4398046511104 ≈ 0.00000000001`). -/
theorem tail_2475880078570760549798248448_lt_1237940039285380274899124224 : (24 / 49758215864320 : ℝ) < (3 / 4398046511104 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 4951760157141521099596496896` tail
(`4951760157141521099596496896^{1/2} = 70368744177664` exact; exact shape mirror of
`M1237940039285380274899124224_rpow_eq` above and latest odd-floor
`M2475880078570760549798248448_rpow_ge` above; honest via
`70368744177664^2 = 4951760157141521099596496896` by `norm_num`;
`4951760157141521099596496896 = 2^92` so the root is exact, unlike
`2475880078570760549798248448`). -/
theorem M4951760157141521099596496896_rpow_eq :
    ((((4951760157141521099596496896 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (70368744177664 : ℝ) := by
  have hx2 : ((((((4951760157141521099596496896 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((4951760157141521099596496896 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((70368744177664 : ℝ) ^ (2 : ℕ)) = ((((4951760157141521099596496896 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((4951760157141521099596496896 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (70368744177664 : ℝ) := by norm_num
  have hle1 : ((((((4951760157141521099596496896 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((70368744177664 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((70368744177664 : ℝ) ^ (2 : ℕ)) ≤
      ((((((4951760157141521099596496896 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 4951760157141521099596496896` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/70368744177664 = 3/8796093022208`; exact shape mirror of
`r_1237940039285380274899124224_le`; decay recomputed honestly with
`norm_num` via the exact `M4951760157141521099596496896_rpow_eq`; tightest honest
`T = 3/8796093022208 ≈ 0.00000000001` for this root). -/
theorem r_4951760157141521099596496896_le :
    (12 : ℝ) * ((((((4951760157141521099596496896 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 8796093022208 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((4951760157141521099596496896 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M4951760157141521099596496896_rpow_eq
  have hrw : ((((4951760157141521099596496896 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((4951760157141521099596496896 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((70368744177664 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 8796093022208 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 4951760157141521099596496896`
(`‖G - S9903520314283042199192993792‖ ≤ 3/8796093022208`; exact shape mirror of
`eta_tail_1237940039285380274899124224_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_4951760157141521099596496896_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 4951760157141521099596496896), etaDirichletTerm s k)‖ ≤
      (3 / 8796093022208 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 4951760157141521099596496896 (by norm_num)
  have h2M : 2 * 4951760157141521099596496896 = 9903520314283042199192993792 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_4951760157141521099596496896_le
  linarith

/-- The `M = 4951760157141521099596496896` constant honestly improves on the banked
`M = 2475880078570760549798248448` constant
(`3/8796093022208 ≈ 0.00000000001 < 24/49758215864320 ≈ 0.00000000001`). -/
theorem tail_4951760157141521099596496896_lt_2475880078570760549798248448 : (3 / 8796093022208 : ℝ) < (24 / 49758215864320 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 9903520314283042199192993792` tail
(`99516431728640 ≤ 9903520314283042199192993792^{1/2}`; generic mirror of
`M2475880078570760549798248448_rpow_ge` and latest exact
`M4951760157141521099596496896_rpow_eq` above; honest floor via
`99516431728640 = 2 * 49758215864320` with `99516431728640^2 ≤ 9903520314283042199192993792`
by `norm_num`; `9903520314283042199192993792 = 2^93` so root `70368744177664·√2 ≈
99516431728640.xx` is NOT exact, unlike `4951760157141521099596496896`). -/
theorem M9903520314283042199192993792_rpow_ge :
    (99516431728640 : ℝ) ≤ ((((9903520314283042199192993792 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((99516431728640 : ℝ) ^ (2 : ℕ)) ≤ ((((9903520314283042199192993792 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((9903520314283042199192993792 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((9903520314283042199192993792 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 9903520314283042199192993792` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/99516431728640`; generic mirror of
`r_2475880078570760549798248448_le` and latest exact
`r_4951760157141521099596496896_le`; decay recomputed honestly with
`norm_num` via `M9903520314283042199192993792_rpow_ge`; honest conservative
`T = 24/99516431728640 ≈ 0.00000000001` for the `99516431728640` root lower). -/
theorem r_9903520314283042199192993792_le :
    (12 : ℝ) * ((((((9903520314283042199192993792 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 99516431728640 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((9903520314283042199192993792 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((9903520314283042199192993792 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M9903520314283042199192993792_rpow_ge
  have hrw : ((((9903520314283042199192993792 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((9903520314283042199192993792 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((9903520314283042199192993792 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (99516431728640 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((9903520314283042199192993792 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (99516431728640 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((9903520314283042199192993792 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((99516431728640 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((99516431728640 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 99516431728640 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 9903520314283042199192993792`
(`‖G - S19807040628566084398385987584‖ ≤ 24/99516431728640`; generic mirror of
`eta_tail_2475880078570760549798248448_le` and latest exact
`eta_tail_4951760157141521099596496896_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_9903520314283042199192993792_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 9903520314283042199192993792), etaDirichletTerm s k)‖ ≤
      (24 / 99516431728640 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 9903520314283042199192993792 (by norm_num)
  have h2M : 2 * 9903520314283042199192993792 = 19807040628566084398385987584 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_9903520314283042199192993792_le
  linarith

/-- The `M = 9903520314283042199192993792` constant honestly improves on the banked
`M = 4951760157141521099596496896` constant
(`24/99516431728640 ≈ 0.00000000001 < 3/8796093022208 ≈ 0.00000000001`). -/
theorem tail_9903520314283042199192993792_lt_4951760157141521099596496896 : (24 / 99516431728640 : ℝ) < (3 / 8796093022208 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 19807040628566084398385987584` tail
(`19807040628566084398385987584^{1/2} = 140737488355328` exact; exact shape mirror of
`M4951760157141521099596496896_rpow_eq` above and latest odd-floor
`M9903520314283042199192993792_rpow_ge` above; honest via
`140737488355328^2 = 19807040628566084398385987584` by `norm_num`;
`19807040628566084398385987584 = 2^94` so the root is exact, unlike
`9903520314283042199192993792`). -/
theorem M19807040628566084398385987584_rpow_eq :
    ((((19807040628566084398385987584 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (140737488355328 : ℝ) := by
  have hx2 : ((((((19807040628566084398385987584 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((19807040628566084398385987584 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((140737488355328 : ℝ) ^ (2 : ℕ)) = ((((19807040628566084398385987584 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((19807040628566084398385987584 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (140737488355328 : ℝ) := by norm_num
  have hle1 : ((((((19807040628566084398385987584 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((140737488355328 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((140737488355328 : ℝ) ^ (2 : ℕ)) ≤
      ((((((19807040628566084398385987584 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 19807040628566084398385987584` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/140737488355328 = 3/17592186044416`; exact shape mirror of
`r_4951760157141521099596496896_le`; decay recomputed honestly with
`norm_num` via the exact `M19807040628566084398385987584_rpow_eq`; tightest honest
`T = 3/17592186044416 ≈ 0.00000000001` for this root). -/
theorem r_19807040628566084398385987584_le :
    (12 : ℝ) * ((((((19807040628566084398385987584 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 17592186044416 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((19807040628566084398385987584 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M19807040628566084398385987584_rpow_eq
  have hrw : ((((19807040628566084398385987584 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((19807040628566084398385987584 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((140737488355328 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 17592186044416 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 19807040628566084398385987584`
(`‖G - S39614081257132168796771975168‖ ≤ 3/17592186044416`; exact shape mirror of
`eta_tail_4951760157141521099596496896_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_19807040628566084398385987584_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 19807040628566084398385987584), etaDirichletTerm s k)‖ ≤
      (3 / 17592186044416 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 19807040628566084398385987584 (by norm_num)
  have h2M : 2 * 19807040628566084398385987584 = 39614081257132168796771975168 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_19807040628566084398385987584_le
  linarith

/-- The `M = 19807040628566084398385987584` constant honestly improves on the banked
`M = 9903520314283042199192993792` constant
(`3/17592186044416 ≈ 0.00000000001 < 24/99516431728640 ≈ 0.00000000001`). -/
theorem tail_19807040628566084398385987584_lt_9903520314283042199192993792 : (3 / 17592186044416 : ℝ) < (24 / 99516431728640 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 39614081257132168796771975168` tail
(`199032863457280 ≤ 39614081257132168796771975168^{1/2}`; generic mirror of
`M9903520314283042199192993792_rpow_ge` and latest exact
`M19807040628566084398385987584_rpow_eq` above; honest floor via
`199032863457280 = 2 * 99516431728640` with `199032863457280^2 = 39614080736004264394384998400 ≤ 39614081257132168796771975168`
by `norm_num`; `39614081257132168796771975168 = 2^95` so root `140737488355328·√2 ≈
199032863457280.xx` is NOT exact, unlike `19807040628566084398385987584`;
conservative doubling `2 * 99516431728640 = 199032863457280`; lower gap `521127904402386976768`). -/
theorem M39614081257132168796771975168_rpow_ge :
    (199032863457280 : ℝ) ≤ ((((39614081257132168796771975168 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((199032863457280 : ℝ) ^ (2 : ℕ)) ≤ ((((39614081257132168796771975168 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((39614081257132168796771975168 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((39614081257132168796771975168 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 39614081257132168796771975168` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/199032863457280`; generic mirror of
`r_9903520314283042199192993792_le` and latest exact
`r_19807040628566084398385987584_le`; decay recomputed honestly with
`norm_num` via `M39614081257132168796771975168_rpow_ge`; honest conservative
`T = 24/199032863457280` for the `199032863457280` root lower). -/
theorem r_39614081257132168796771975168_le :
    (12 : ℝ) * ((((((39614081257132168796771975168 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 199032863457280 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((39614081257132168796771975168 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((39614081257132168796771975168 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M39614081257132168796771975168_rpow_ge
  have hrw : ((((39614081257132168796771975168 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((39614081257132168796771975168 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((39614081257132168796771975168 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (199032863457280 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((39614081257132168796771975168 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (199032863457280 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((39614081257132168796771975168 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((199032863457280 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((199032863457280 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 199032863457280 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 39614081257132168796771975168`
(`‖G - S79228162514264337593543950336‖ ≤ 24/199032863457280`; generic mirror of
`eta_tail_9903520314283042199192993792_le` and latest exact
`eta_tail_19807040628566084398385987584_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_39614081257132168796771975168_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 39614081257132168796771975168), etaDirichletTerm s k)‖ ≤
      (24 / 199032863457280 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 39614081257132168796771975168 (by norm_num)
  have h2M : 2 * 39614081257132168796771975168 = 79228162514264337593543950336 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_39614081257132168796771975168_le
  linarith

/-- The `M = 39614081257132168796771975168` constant honestly improves on the banked
`M = 19807040628566084398385987584` constant
(`24/199032863457280 < 3/17592186044416`). -/
theorem tail_39614081257132168796771975168_lt_19807040628566084398385987584 : (24 / 199032863457280 : ℝ) < (3 / 17592186044416 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 79228162514264337593543950336` tail
(`79228162514264337593543950336^{1/2} = 281474976710656` exact; exact shape mirror of
`M19807040628566084398385987584_rpow_eq` above and latest odd-floor
`M39614081257132168796771975168_rpow_ge` above; honest via
`281474976710656^2 = 79228162514264337593543950336` by `norm_num`;
`79228162514264337593543950336 = 2^96` so the root is exact, unlike
`39614081257132168796771975168`). -/
theorem M79228162514264337593543950336_rpow_eq :
    ((((79228162514264337593543950336 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (281474976710656 : ℝ) := by
  have hx2 : ((((((79228162514264337593543950336 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((79228162514264337593543950336 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((281474976710656 : ℝ) ^ (2 : ℕ)) = ((((79228162514264337593543950336 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((79228162514264337593543950336 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (281474976710656 : ℝ) := by norm_num
  have hle1 : ((((((79228162514264337593543950336 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((281474976710656 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((281474976710656 : ℝ) ^ (2 : ℕ)) ≤
      ((((((79228162514264337593543950336 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 79228162514264337593543950336` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/281474976710656 = 3/35184372088832`; exact shape mirror of
`r_19807040628566084398385987584_le`; decay recomputed honestly with
`norm_num` via the exact `M79228162514264337593543950336_rpow_eq`; tightest honest
`T = 3/35184372088832` for this root). -/
theorem r_79228162514264337593543950336_le :
    (12 : ℝ) * ((((((79228162514264337593543950336 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 35184372088832 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((79228162514264337593543950336 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M79228162514264337593543950336_rpow_eq
  have hrw : ((((79228162514264337593543950336 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((79228162514264337593543950336 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((281474976710656 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 35184372088832 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 79228162514264337593543950336`
(`‖G - S158456325028528675187087900672‖ ≤ 3/35184372088832`; exact shape mirror of
`eta_tail_19807040628566084398385987584_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_79228162514264337593543950336_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 79228162514264337593543950336), etaDirichletTerm s k)‖ ≤
      (3 / 35184372088832 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 79228162514264337593543950336 (by norm_num)
  have h2M : 2 * 79228162514264337593543950336 = 158456325028528675187087900672 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_79228162514264337593543950336_le
  linarith

/-- The `M = 79228162514264337593543950336` constant honestly improves on the banked
`M = 39614081257132168796771975168` constant
(`3/35184372088832 < 24/199032863457280`). -/
theorem tail_79228162514264337593543950336_lt_39614081257132168796771975168 : (3 / 35184372088832 : ℝ) < (24 / 199032863457280 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 158456325028528675187087900672` tail
(`398065726914560 ≤ 158456325028528675187087900672^{1/2}`; generic mirror of
`M39614081257132168796771975168_rpow_ge` above and latest exact
`M79228162514264337593543950336_rpow_eq` above; honest floor via
`398065726914560 = 2 * 199032863457280` with `398065726914560^2 = 158456322944017057577539993600 ≤ 158456325028528675187087900672`
by `norm_num`; `158456325028528675187087900672 = 2^97` so root `281474976710656·√2 ≈
398065726914560.xx` is NOT exact, unlike `79228162514264337593543950336`;
conservative doubling `2 * 199032863457280 = 398065726914560`; lower gap `2084511617609547907072`). -/
theorem M158456325028528675187087900672_rpow_ge :
    (398065726914560 : ℝ) ≤ ((((158456325028528675187087900672 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((398065726914560 : ℝ) ^ (2 : ℕ)) ≤ ((((158456325028528675187087900672 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((158456325028528675187087900672 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((158456325028528675187087900672 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 158456325028528675187087900672` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/398065726914560`; generic mirror of
`r_39614081257132168796771975168_le` above and latest exact
`r_79228162514264337593543950336_le` above; decay recomputed honestly with
`norm_num` via `M158456325028528675187087900672_rpow_ge`; honest conservative
`T = 24/398065726914560` for the `398065726914560` root lower). -/
theorem r_158456325028528675187087900672_le :
    (12 : ℝ) * ((((((158456325028528675187087900672 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 398065726914560 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((158456325028528675187087900672 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((158456325028528675187087900672 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M158456325028528675187087900672_rpow_ge
  have hrw : ((((158456325028528675187087900672 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((158456325028528675187087900672 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((158456325028528675187087900672 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (398065726914560 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((158456325028528675187087900672 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (398065726914560 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((158456325028528675187087900672 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((398065726914560 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((398065726914560 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 398065726914560 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 158456325028528675187087900672`
(`‖G - S316912650057057350374175801344‖ ≤ 24/398065726914560`; generic mirror of
`eta_tail_39614081257132168796771975168_le` above and latest exact
`eta_tail_79228162514264337593543950336_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_158456325028528675187087900672_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 158456325028528675187087900672), etaDirichletTerm s k)‖ ≤
      (24 / 398065726914560 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 158456325028528675187087900672 (by norm_num)
  have h2M : 2 * 158456325028528675187087900672 = 316912650057057350374175801344 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_158456325028528675187087900672_le
  linarith

/-- The `M = 158456325028528675187087900672` constant honestly improves on the banked
`M = 79228162514264337593543950336` constant
(`24/398065726914560 < 3/35184372088832`). -/
theorem tail_158456325028528675187087900672_lt_79228162514264337593543950336 : (24 / 398065726914560 : ℝ) < (3 / 35184372088832 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 316912650057057350374175801344` tail
(`316912650057057350374175801344^{1/2} = 562949953421312` exact; exact shape mirror of
`M79228162514264337593543950336_rpow_eq` above and latest odd-floor
`M158456325028528675187087900672_rpow_ge` above; honest via
`562949953421312^2 = 316912650057057350374175801344` by `norm_num`;
`316912650057057350374175801344 = 2^98` so the root is exact, unlike
`158456325028528675187087900672`). -/
theorem M316912650057057350374175801344_rpow_eq :
    ((((316912650057057350374175801344 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (562949953421312 : ℝ) := by
  have hx2 : ((((((316912650057057350374175801344 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((316912650057057350374175801344 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((562949953421312 : ℝ) ^ (2 : ℕ)) = ((((316912650057057350374175801344 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((316912650057057350374175801344 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (562949953421312 : ℝ) := by norm_num
  have hle1 : ((((((316912650057057350374175801344 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((562949953421312 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((562949953421312 : ℝ) ^ (2 : ℕ)) ≤
      ((((((316912650057057350374175801344 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 316912650057057350374175801344` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/562949953421312 = 3/70368744177664`; exact shape mirror of
`r_79228162514264337593543950336_le` above; decay recomputed honestly with
`norm_num` via the exact `M316912650057057350374175801344_rpow_eq`; tightest honest
`T = 3/70368744177664` for this root). -/
theorem r_316912650057057350374175801344_le :
    (12 : ℝ) * ((((((316912650057057350374175801344 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 70368744177664 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((316912650057057350374175801344 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M316912650057057350374175801344_rpow_eq
  have hrw : ((((316912650057057350374175801344 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((316912650057057350374175801344 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((562949953421312 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 70368744177664 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 316912650057057350374175801344`
(`‖G - S633825300114114700748351602688‖ ≤ 3/70368744177664`; exact shape mirror of
`eta_tail_79228162514264337593543950336_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_316912650057057350374175801344_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 316912650057057350374175801344), etaDirichletTerm s k)‖ ≤
      (3 / 70368744177664 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 316912650057057350374175801344 (by norm_num)
  have h2M : 2 * 316912650057057350374175801344 = 633825300114114700748351602688 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_316912650057057350374175801344_le
  linarith

/-- The `M = 316912650057057350374175801344` constant honestly improves on the banked
`M = 158456325028528675187087900672` constant
(`3/70368744177664 < 24/398065726914560`). -/
theorem tail_316912650057057350374175801344_lt_158456325028528675187087900672 : (3 / 70368744177664 : ℝ) < (24 / 398065726914560 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 633825300114114700748351602688` tail
(`796131453829120 ≤ 633825300114114700748351602688^{1/2}`; generic mirror of
`M158456325028528675187087900672_rpow_ge` above and latest exact
`M316912650057057350374175801344_rpow_eq` above; honest floor via
`796131453829120 = 2 * 398065726914560` with `796131453829120^2 = 633825291776068230310159974400 ≤ 633825300114114700748351602688`
by `norm_num`; `633825300114114700748351602688 = 2^99` so root `562949953421312·√2 ≈
796131453829120.xx` is NOT exact, unlike `316912650057057350374175801344`;
conservative doubling `2 * 398065726914560 = 796131453829120`; lower gap `8338046470438191628288`). -/
theorem M633825300114114700748351602688_rpow_ge :
    (796131453829120 : ℝ) ≤ ((((633825300114114700748351602688 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((796131453829120 : ℝ) ^ (2 : ℕ)) ≤ ((((633825300114114700748351602688 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((633825300114114700748351602688 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((633825300114114700748351602688 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 633825300114114700748351602688` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/796131453829120`; generic mirror of
`r_158456325028528675187087900672_le` above and latest exact
`r_316912650057057350374175801344_le` above; decay recomputed honestly with
`norm_num` via `M633825300114114700748351602688_rpow_ge`; honest conservative
`T = 24/796131453829120` for the `796131453829120` root lower). -/
theorem r_633825300114114700748351602688_le :
    (12 : ℝ) * ((((((633825300114114700748351602688 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 796131453829120 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((633825300114114700748351602688 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((633825300114114700748351602688 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M633825300114114700748351602688_rpow_ge
  have hrw : ((((633825300114114700748351602688 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((633825300114114700748351602688 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((633825300114114700748351602688 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (796131453829120 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((633825300114114700748351602688 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (796131453829120 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((633825300114114700748351602688 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((796131453829120 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((796131453829120 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 796131453829120 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 633825300114114700748351602688`
(`‖G - S1267650600228229401496703205376‖ ≤ 24/796131453829120`; generic mirror of
`eta_tail_158456325028528675187087900672_le` above and latest exact
`eta_tail_316912650057057350374175801344_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_633825300114114700748351602688_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 633825300114114700748351602688), etaDirichletTerm s k)‖ ≤
      (24 / 796131453829120 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 633825300114114700748351602688 (by norm_num)
  have h2M : 2 * 633825300114114700748351602688 = 1267650600228229401496703205376 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_633825300114114700748351602688_le
  linarith

/-- The `M = 633825300114114700748351602688` constant honestly improves on the banked
`M = 316912650057057350374175801344` constant
(`24/796131453829120 < 3/70368744177664`). -/
theorem tail_633825300114114700748351602688_lt_316912650057057350374175801344 : (24 / 796131453829120 : ℝ) < (3 / 70368744177664 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 1267650600228229401496703205376` tail
(`1267650600228229401496703205376^{1/2} = 1125899906842624` exact; exact shape mirror of
`M316912650057057350374175801344_rpow_eq` above and latest odd-floor
`M633825300114114700748351602688_rpow_ge` above; honest via
`1125899906842624^2 = 1267650600228229401496703205376` by `norm_num`;
`1267650600228229401496703205376 = 2^100` so the root is exact, unlike
`633825300114114700748351602688`). -/
theorem M1267650600228229401496703205376_rpow_eq :
    ((((1267650600228229401496703205376 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (1125899906842624 : ℝ) := by
  have hx2 : ((((((1267650600228229401496703205376 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((1267650600228229401496703205376 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((1125899906842624 : ℝ) ^ (2 : ℕ)) = ((((1267650600228229401496703205376 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((1267650600228229401496703205376 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (1125899906842624 : ℝ) := by norm_num
  have hle1 : ((((((1267650600228229401496703205376 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((1125899906842624 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((1125899906842624 : ℝ) ^ (2 : ℕ)) ≤
      ((((((1267650600228229401496703205376 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 1267650600228229401496703205376` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/1125899906842624 = 3/140737488355328`; exact shape mirror of
`r_316912650057057350374175801344_le` above; decay recomputed honestly with
`norm_num` via the exact `M1267650600228229401496703205376_rpow_eq`; tightest honest
`T = 3/140737488355328` for this root). -/
theorem r_1267650600228229401496703205376_le :
    (12 : ℝ) * ((((((1267650600228229401496703205376 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 140737488355328 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((1267650600228229401496703205376 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M1267650600228229401496703205376_rpow_eq
  have hrw : ((((1267650600228229401496703205376 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((1267650600228229401496703205376 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((1125899906842624 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 140737488355328 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 1267650600228229401496703205376`
(`‖G - S2535301200456458802993406410752‖ ≤ 3/140737488355328`; exact shape mirror of
`eta_tail_316912650057057350374175801344_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_1267650600228229401496703205376_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 1267650600228229401496703205376), etaDirichletTerm s k)‖ ≤
      (3 / 140737488355328 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1267650600228229401496703205376 (by norm_num)
  have h2M : 2 * 1267650600228229401496703205376 = 2535301200456458802993406410752 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_1267650600228229401496703205376_le
  linarith

/-- The `M = 1267650600228229401496703205376` constant honestly improves on the banked
`M = 633825300114114700748351602688` constant
(`3/140737488355328 < 24/796131453829120`). -/
theorem tail_1267650600228229401496703205376_lt_633825300114114700748351602688 : (3 / 140737488355328 : ℝ) < (24 / 796131453829120 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 2535301200456458802993406410752` tail
(`1592262907658240 ≤ 2535301200456458802993406410752^{1/2}`; generic mirror of
`M633825300114114700748351602688_rpow_ge` above and latest exact
`M1267650600228229401496703205376_rpow_eq` above; honest floor via
`1592262907658240 = 2 * 796131453829120` with `1592262907658240^2 =
2535301167104272921240639897600 ≤ 2535301200456458802993406410752`
by `norm_num`; `2535301200456458802993406410752 = 2^101` so root
`1125899906842624·√2 ≈ 1592262911877644.xx` is NOT exact, unlike
`1267650600228229401496703205376`; lower gap `33352185881752766513152`). -/
theorem M2535301200456458802993406410752_rpow_ge :
    (1592262907658240 : ℝ) ≤ ((((2535301200456458802993406410752 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((1592262907658240 : ℝ) ^ (2 : ℕ)) ≤ ((((2535301200456458802993406410752 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((2535301200456458802993406410752 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((2535301200456458802993406410752 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 2535301200456458802993406410752` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/1592262907658240`; generic mirror of
`r_633825300114114700748351602688_le` above and latest exact
`r_1267650600228229401496703205376_le` above; decay recomputed honestly with
`norm_num` via `M2535301200456458802993406410752_rpow_ge`; honest conservative
`T = 24/1592262907658240` for the `1592262907658240` root lower). -/
theorem r_2535301200456458802993406410752_le :
    (12 : ℝ) * ((((((2535301200456458802993406410752 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 1592262907658240 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((2535301200456458802993406410752 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((2535301200456458802993406410752 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M2535301200456458802993406410752_rpow_ge
  have hrw : ((((2535301200456458802993406410752 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((2535301200456458802993406410752 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((2535301200456458802993406410752 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (1592262907658240 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((2535301200456458802993406410752 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (1592262907658240 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((2535301200456458802993406410752 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((1592262907658240 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((1592262907658240 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 1592262907658240 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 2535301200456458802993406410752`
(`‖G - S5070602400912917605986812821504‖ ≤ 24/1592262907658240`; generic mirror of
`eta_tail_633825300114114700748351602688_le` above and latest exact
`eta_tail_1267650600228229401496703205376_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_2535301200456458802993406410752_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 2535301200456458802993406410752), etaDirichletTerm s k)‖ ≤
      (24 / 1592262907658240 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 2535301200456458802993406410752 (by norm_num)
  have h2M : 2 * 2535301200456458802993406410752 = 5070602400912917605986812821504 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_2535301200456458802993406410752_le
  linarith

/-- The `M = 2535301200456458802993406410752` constant honestly improves on the banked
`M = 1267650600228229401496703205376` constant
(`24/1592262907658240 < 3/140737488355328`). -/
theorem tail_2535301200456458802993406410752_lt_1267650600228229401496703205376 : (24 / 1592262907658240 : ℝ) < (3 / 140737488355328 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 5070602400912917605986812821504` tail
(`5070602400912917605986812821504^{1/2} = 2251799813685248` exact; exact shape mirror of
`M1267650600228229401496703205376_rpow_eq` above and latest odd-floor
`M2535301200456458802993406410752_rpow_ge` above; honest via
`2251799813685248^2 = 5070602400912917605986812821504` by `norm_num`;
`5070602400912917605986812821504 = 2^102` so the root is exact, unlike
`2535301200456458802993406410752`). -/
theorem M5070602400912917605986812821504_rpow_eq :
    ((((5070602400912917605986812821504 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (2251799813685248 : ℝ) := by
  have hx2 : ((((((5070602400912917605986812821504 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((5070602400912917605986812821504 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((2251799813685248 : ℝ) ^ (2 : ℕ)) = ((((5070602400912917605986812821504 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((5070602400912917605986812821504 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (2251799813685248 : ℝ) := by norm_num
  have hle1 : ((((((5070602400912917605986812821504 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((2251799813685248 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((2251799813685248 : ℝ) ^ (2 : ℕ)) ≤
      ((((((5070602400912917605986812821504 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 5070602400912917605986812821504` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/2251799813685248 = 3/281474976710656`; exact shape mirror of
`r_1267650600228229401496703205376_le` above; decay recomputed honestly with
`norm_num` via the exact `M5070602400912917605986812821504_rpow_eq`; tightest honest
`T = 3/281474976710656` for this root). -/
theorem r_5070602400912917605986812821504_le :
    (12 : ℝ) * ((((((5070602400912917605986812821504 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 281474976710656 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((5070602400912917605986812821504 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M5070602400912917605986812821504_rpow_eq
  have hrw : ((((5070602400912917605986812821504 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((5070602400912917605986812821504 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((2251799813685248 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 281474976710656 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 5070602400912917605986812821504`
(`‖G - S10141204801825835211973625643008‖ ≤ 3/281474976710656`; exact shape mirror of
`eta_tail_1267650600228229401496703205376_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_5070602400912917605986812821504_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 5070602400912917605986812821504), etaDirichletTerm s k)‖ ≤
      (3 / 281474976710656 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 5070602400912917605986812821504 (by norm_num)
  have h2M : 2 * 5070602400912917605986812821504 = 10141204801825835211973625643008 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_5070602400912917605986812821504_le
  linarith

/-- The `M = 5070602400912917605986812821504` constant honestly improves on the banked
`M = 2535301200456458802993406410752` constant
(`3/281474976710656 < 24/1592262907658240`). -/
theorem tail_5070602400912917605986812821504_lt_2535301200456458802993406410752 : (3 / 281474976710656 : ℝ) < (24 / 1592262907658240 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 10141204801825835211973625643008` tail
(`3184525815316480 ≤ 10141204801825835211973625643008^{1/2}`; generic mirror of
`M2535301200456458802993406410752_rpow_ge` above and latest exact
`M5070602400912917605986812821504_rpow_eq` above; honest floor via
`3184525815316480 = 2 * 1592262907658240` with `3184525815316480^2 =
10141204668417091684962559590400 ≤ 10141204801825835211973625643008`
by `norm_num`; `10141204801825835211973625643008 = 2^103` so root
`2251799813685248·√2 ≈ 3184525836262886.28` is NOT exact, unlike
`5070602400912917605986812821504`; lower gap `133408743527011066052608`). -/
theorem M10141204801825835211973625643008_rpow_ge :
    (3184525815316480 : ℝ) ≤ ((((10141204801825835211973625643008 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((3184525815316480 : ℝ) ^ (2 : ℕ)) ≤ ((((10141204801825835211973625643008 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((10141204801825835211973625643008 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((10141204801825835211973625643008 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 10141204801825835211973625643008` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/3184525815316480`; generic mirror of
`r_2535301200456458802993406410752_le` above and latest exact
`r_5070602400912917605986812821504_le` above; decay recomputed honestly with
`norm_num` via `M10141204801825835211973625643008_rpow_ge`; honest conservative
`T = 24/3184525815316480` for the `3184525815316480` root lower). -/
theorem r_10141204801825835211973625643008_le :
    (12 : ℝ) * ((((((10141204801825835211973625643008 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 3184525815316480 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((10141204801825835211973625643008 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((10141204801825835211973625643008 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M10141204801825835211973625643008_rpow_ge
  have hrw : ((((10141204801825835211973625643008 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((10141204801825835211973625643008 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((10141204801825835211973625643008 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (3184525815316480 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((10141204801825835211973625643008 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (3184525815316480 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((10141204801825835211973625643008 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((3184525815316480 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((3184525815316480 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 3184525815316480 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 10141204801825835211973625643008`
(`‖G - S20282409603651670423947251286016‖ ≤ 24/3184525815316480`; generic mirror of
`eta_tail_2535301200456458802993406410752_le` above and latest exact
`eta_tail_5070602400912917605986812821504_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_10141204801825835211973625643008_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 10141204801825835211973625643008), etaDirichletTerm s k)‖ ≤
      (24 / 3184525815316480 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 10141204801825835211973625643008 (by norm_num)
  have h2M : 2 * 10141204801825835211973625643008 = 20282409603651670423947251286016 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_10141204801825835211973625643008_le
  linarith

/-- The `M = 10141204801825835211973625643008` constant honestly improves on the banked
`M = 5070602400912917605986812821504` constant
(`24/3184525815316480 < 3/281474976710656`). -/
theorem tail_10141204801825835211973625643008_lt_5070602400912917605986812821504 : (24 / 3184525815316480 : ℝ) < (3 / 281474976710656 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 20282409603651670423947251286016` tail
(`20282409603651670423947251286016^{1/2} = 4503599627370496` exact; exact shape mirror of
`M5070602400912917605986812821504_rpow_eq` above and latest odd-floor
`M10141204801825835211973625643008_rpow_ge` above; honest via
`4503599627370496^2 = 20282409603651670423947251286016` by `norm_num`;
`20282409603651670423947251286016 = 2^104` so the root is exact, unlike
`10141204801825835211973625643008`). -/
theorem M20282409603651670423947251286016_rpow_eq :
    ((((20282409603651670423947251286016 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (4503599627370496 : ℝ) := by
  have hx2 : ((((((20282409603651670423947251286016 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((20282409603651670423947251286016 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((4503599627370496 : ℝ) ^ (2 : ℕ)) = ((((20282409603651670423947251286016 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((20282409603651670423947251286016 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (4503599627370496 : ℝ) := by norm_num
  have hle1 : ((((((20282409603651670423947251286016 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((4503599627370496 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((4503599627370496 : ℝ) ^ (2 : ℕ)) ≤
      ((((((20282409603651670423947251286016 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 20282409603651670423947251286016` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/4503599627370496 = 3/562949953421312`; exact shape mirror of
`r_5070602400912917605986812821504_le` above; decay recomputed honestly with
`norm_num` via the exact `M20282409603651670423947251286016_rpow_eq`; tightest honest
`T = 3/562949953421312` for this root). -/
theorem r_20282409603651670423947251286016_le :
    (12 : ℝ) * ((((((20282409603651670423947251286016 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 562949953421312 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((20282409603651670423947251286016 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M20282409603651670423947251286016_rpow_eq
  have hrw : ((((20282409603651670423947251286016 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((20282409603651670423947251286016 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((4503599627370496 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 562949953421312 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 20282409603651670423947251286016`
(`‖G - S40564819207303340847894502572032‖ ≤ 3/562949953421312`; exact shape mirror of
`eta_tail_5070602400912917605986812821504_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_20282409603651670423947251286016_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 20282409603651670423947251286016), etaDirichletTerm s k)‖ ≤
      (3 / 562949953421312 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 20282409603651670423947251286016 (by norm_num)
  have h2M : 2 * 20282409603651670423947251286016 = 40564819207303340847894502572032 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_20282409603651670423947251286016_le
  linarith

/-- The `M = 20282409603651670423947251286016` constant honestly improves on the banked
`M = 10141204801825835211973625643008` constant
(`3/562949953421312 < 24/3184525815316480`). -/
theorem tail_20282409603651670423947251286016_lt_10141204801825835211973625643008 : (3 / 562949953421312 : ℝ) < (24 / 3184525815316480 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 40564819207303340847894502572032` tail
(`6369051630632960 ≤ 40564819207303340847894502572032^{1/2}`; generic mirror of
`M10141204801825835211973625643008_rpow_ge` above and latest exact
`M20282409603651670423947251286016_rpow_eq` above; honest floor via
`6369051630632960 = 2 * 3184525815316480` with `6369051630632960^2 =
40564818673668366739850238361600 ≤ 40564819207303340847894502572032`
by `norm_num`; `40564819207303340847894502572032 = 2^105` so root
`4503599627370496·√2 ≈ 6369051672525772.38` is NOT exact, unlike
`20282409603651670423947251286016`; lower gap `533634974108044264210432`). -/
theorem M40564819207303340847894502572032_rpow_ge :
    (6369051630632960 : ℝ) ≤ ((((40564819207303340847894502572032 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((6369051630632960 : ℝ) ^ (2 : ℕ)) ≤ ((((40564819207303340847894502572032 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((40564819207303340847894502572032 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((40564819207303340847894502572032 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 40564819207303340847894502572032` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/6369051630632960`; generic mirror of
`r_10141204801825835211973625643008_le` above and latest exact
`r_20282409603651670423947251286016_le` above; decay recomputed honestly with
`norm_num` via `M40564819207303340847894502572032_rpow_ge`; honest conservative
`T = 24/6369051630632960` for the `6369051630632960` root lower). -/
theorem r_40564819207303340847894502572032_le :
    (12 : ℝ) * ((((((40564819207303340847894502572032 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 6369051630632960 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((40564819207303340847894502572032 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((40564819207303340847894502572032 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M40564819207303340847894502572032_rpow_ge
  have hrw : ((((40564819207303340847894502572032 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((40564819207303340847894502572032 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((40564819207303340847894502572032 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (6369051630632960 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((40564819207303340847894502572032 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (6369051630632960 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((40564819207303340847894502572032 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((6369051630632960 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((6369051630632960 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 6369051630632960 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 40564819207303340847894502572032`
(`‖G - S81129638414606681695789005144064‖ ≤ 24/6369051630632960`; generic mirror of
`eta_tail_10141204801825835211973625643008_le` above and latest exact
`eta_tail_20282409603651670423947251286016_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_40564819207303340847894502572032_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 40564819207303340847894502572032), etaDirichletTerm s k)‖ ≤
      (24 / 6369051630632960 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 40564819207303340847894502572032 (by norm_num)
  have h2M : 2 * 40564819207303340847894502572032 = 81129638414606681695789005144064 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_40564819207303340847894502572032_le
  linarith

/-- The `M = 40564819207303340847894502572032` constant honestly improves on the banked
`M = 20282409603651670423947251286016` constant
(`24/6369051630632960 < 3/562949953421312`). -/
theorem tail_40564819207303340847894502572032_lt_20282409603651670423947251286016 : (24 / 6369051630632960 : ℝ) < (3 / 562949953421312 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 81129638414606681695789005144064` tail
(`81129638414606681695789005144064^{1/2} = 9007199254740992` exact; exact shape mirror of
`M20282409603651670423947251286016_rpow_eq` above and latest odd-floor
`M40564819207303340847894502572032_rpow_ge` above; honest via
`9007199254740992^2 = 81129638414606681695789005144064` by `norm_num`;
`81129638414606681695789005144064 = 2^106` so the root is exact, unlike
`40564819207303340847894502572032`). -/
theorem M81129638414606681695789005144064_rpow_eq :
    ((((81129638414606681695789005144064 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (9007199254740992 : ℝ) := by
  have hx2 : ((((((81129638414606681695789005144064 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((81129638414606681695789005144064 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((9007199254740992 : ℝ) ^ (2 : ℕ)) = ((((81129638414606681695789005144064 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((81129638414606681695789005144064 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (9007199254740992 : ℝ) := by norm_num
  have hle1 : ((((((81129638414606681695789005144064 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((9007199254740992 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((9007199254740992 : ℝ) ^ (2 : ℕ)) ≤
      ((((((81129638414606681695789005144064 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 81129638414606681695789005144064` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/9007199254740992 = 3/1125899906842624`; exact shape mirror of
`r_20282409603651670423947251286016_le` above; decay recomputed honestly with
`norm_num` via the exact `M81129638414606681695789005144064_rpow_eq`; tightest honest
`T = 3/1125899906842624` for this root). -/
theorem r_81129638414606681695789005144064_le :
    (12 : ℝ) * ((((((81129638414606681695789005144064 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 1125899906842624 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((81129638414606681695789005144064 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M81129638414606681695789005144064_rpow_eq
  have hrw : ((((81129638414606681695789005144064 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((81129638414606681695789005144064 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((9007199254740992 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 1125899906842624 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 81129638414606681695789005144064`
(`‖G - S162259276829213363391578010288128‖ ≤ 3/1125899906842624`; exact shape mirror of
`eta_tail_20282409603651670423947251286016_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_81129638414606681695789005144064_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 81129638414606681695789005144064), etaDirichletTerm s k)‖ ≤
      (3 / 1125899906842624 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 81129638414606681695789005144064 (by norm_num)
  have h2M : 2 * 81129638414606681695789005144064 = 162259276829213363391578010288128 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_81129638414606681695789005144064_le
  linarith

/-- The `M = 81129638414606681695789005144064` constant honestly improves on the banked
`M = 40564819207303340847894502572032` constant
(`3/1125899906842624 < 24/6369051630632960`). -/
theorem tail_81129638414606681695789005144064_lt_40564819207303340847894502572032 : (3 / 1125899906842624 : ℝ) < (24 / 6369051630632960 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 162259276829213363391578010288128` tail
(`12738103261265920 ≤ 162259276829213363391578010288128^{1/2}`; generic mirror of
`M40564819207303340847894502572032_rpow_ge` above and latest exact
`M81129638414606681695789005144064_rpow_eq` above; honest floor via
`12738103261265920 = 2 * 6369051630632960` with `12738103261265920^2 =
162259274694673466959400953446400 ≤ 162259276829213363391578010288128`
by `norm_num`; `162259276829213363391578010288128 = 2^107` so root
`9007199254740992·√2 ≈ 12738103345...` is NOT exact, unlike
`81129638414606681695789005144064`; lower gap `2134539896432177056841728`). -/
theorem M162259276829213363391578010288128_rpow_ge :
    (12738103261265920 : ℝ) ≤ ((((162259276829213363391578010288128 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((12738103261265920 : ℝ) ^ (2 : ℕ)) ≤ ((((162259276829213363391578010288128 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((162259276829213363391578010288128 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((162259276829213363391578010288128 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 162259276829213363391578010288128` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/12738103261265920`; generic mirror of
`r_40564819207303340847894502572032_le` above and latest exact
`r_81129638414606681695789005144064_le` above; decay recomputed honestly with
`norm_num` via `M162259276829213363391578010288128_rpow_ge`; honest conservative
`T = 24/12738103261265920` for the `12738103261265920` root lower). -/
theorem r_162259276829213363391578010288128_le :
    (12 : ℝ) * ((((((162259276829213363391578010288128 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 12738103261265920 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((162259276829213363391578010288128 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((162259276829213363391578010288128 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M162259276829213363391578010288128_rpow_ge
  have hrw : ((((162259276829213363391578010288128 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((162259276829213363391578010288128 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((162259276829213363391578010288128 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (12738103261265920 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((162259276829213363391578010288128 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (12738103261265920 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((162259276829213363391578010288128 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((12738103261265920 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((12738103261265920 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 12738103261265920 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 162259276829213363391578010288128`
(`‖G - S324518553658426726783156020576256‖ ≤ 24/12738103261265920`; generic mirror of
`eta_tail_40564819207303340847894502572032_le` above and latest exact
`eta_tail_81129638414606681695789005144064_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_162259276829213363391578010288128_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 162259276829213363391578010288128), etaDirichletTerm s k)‖ ≤
      (24 / 12738103261265920 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 162259276829213363391578010288128 (by norm_num)
  have h2M : 2 * 162259276829213363391578010288128 = 324518553658426726783156020576256 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_162259276829213363391578010288128_le
  linarith

/-- The `M = 162259276829213363391578010288128` constant honestly improves on the banked
`M = 81129638414606681695789005144064` constant
(`24/12738103261265920 < 3/1125899906842624`). -/
theorem tail_162259276829213363391578010288128_lt_81129638414606681695789005144064 : (24 / 12738103261265920 : ℝ) < (3 / 1125899906842624 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 324518553658426726783156020576256` tail
(`324518553658426726783156020576256^{1/2} = 18014398509481984` exact; exact shape mirror of
`M81129638414606681695789005144064_rpow_eq` above and latest odd-floor
`M162259276829213363391578010288128_rpow_ge` above; honest via
`18014398509481984^2 = 324518553658426726783156020576256` by `norm_num`;
`324518553658426726783156020576256 = 2^108` so the root is exact, unlike
`162259276829213363391578010288128`). -/
theorem M324518553658426726783156020576256_rpow_eq :
    ((((324518553658426726783156020576256 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (18014398509481984 : ℝ) := by
  have hx2 : ((((((324518553658426726783156020576256 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((324518553658426726783156020576256 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((18014398509481984 : ℝ) ^ (2 : ℕ)) = ((((324518553658426726783156020576256 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((324518553658426726783156020576256 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (18014398509481984 : ℝ) := by norm_num
  have hle1 : ((((((324518553658426726783156020576256 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((18014398509481984 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((18014398509481984 : ℝ) ^ (2 : ℕ)) ≤
      ((((((324518553658426726783156020576256 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 324518553658426726783156020576256` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/18014398509481984 = 3/2251799813685248`; exact shape mirror of
`r_81129638414606681695789005144064_le` above; decay recomputed honestly with
`norm_num` via the exact `M324518553658426726783156020576256_rpow_eq`; tightest honest
`T = 3/2251799813685248` for this root). -/
theorem r_324518553658426726783156020576256_le :
    (12 : ℝ) * ((((((324518553658426726783156020576256 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 2251799813685248 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((324518553658426726783156020576256 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M324518553658426726783156020576256_rpow_eq
  have hrw : ((((324518553658426726783156020576256 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((324518553658426726783156020576256 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((18014398509481984 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 2251799813685248 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 324518553658426726783156020576256`
(`‖G - S649037107316853453566312041152512‖ ≤ 3/2251799813685248`; exact shape mirror of
`eta_tail_81129638414606681695789005144064_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_324518553658426726783156020576256_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 324518553658426726783156020576256), etaDirichletTerm s k)‖ ≤
      (3 / 2251799813685248 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 324518553658426726783156020576256 (by norm_num)
  have h2M : 2 * 324518553658426726783156020576256 = 649037107316853453566312041152512 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_324518553658426726783156020576256_le
  linarith

/-- The `M = 324518553658426726783156020576256` constant honestly improves on the banked
`M = 162259276829213363391578010288128` constant
(`3/2251799813685248 < 24/12738103261265920`). -/
theorem tail_324518553658426726783156020576256_lt_162259276829213363391578010288128 : (3 / 2251799813685248 : ℝ) < (24 / 12738103261265920 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 649037107316853453566312041152512` tail
(`25476206522531840 ≤ 649037107316853453566312041152512^{1/2}`; generic mirror of
`M162259276829213363391578010288128_rpow_ge` above and latest exact
`M324518553658426726783156020576256_rpow_eq` above; honest floor via
`25476206522531840 = 2 * 12738103261265920` with `25476206522531840^2 =
649037098778693867837603813785600 ≤ 649037107316853453566312041152512`
by `norm_num`; `649037107316853453566312041152512 = 2^109` so root
`18014398509481984·√2 ≈ 25476206522...` is NOT exact, unlike
`324518553658426726783156020576256`; lower gap `8538159585728708227366912`). -/
theorem M649037107316853453566312041152512_rpow_ge :
    (25476206522531840 : ℝ) ≤ ((((649037107316853453566312041152512 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((25476206522531840 : ℝ) ^ (2 : ℕ)) ≤ ((((649037107316853453566312041152512 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((649037107316853453566312041152512 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((649037107316853453566312041152512 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 649037107316853453566312041152512` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/25476206522531840`; generic mirror of
`r_162259276829213363391578010288128_le` above and latest exact
`r_324518553658426726783156020576256_le` above; decay recomputed honestly with
`norm_num` via `M649037107316853453566312041152512_rpow_ge`; honest conservative
`T = 24/25476206522531840` for the `25476206522531840` root lower). -/
theorem r_649037107316853453566312041152512_le :
    (12 : ℝ) * ((((((649037107316853453566312041152512 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 25476206522531840 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((649037107316853453566312041152512 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((649037107316853453566312041152512 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M649037107316853453566312041152512_rpow_ge
  have hrw : ((((649037107316853453566312041152512 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((649037107316853453566312041152512 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((649037107316853453566312041152512 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (25476206522531840 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((649037107316853453566312041152512 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (25476206522531840 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((649037107316853453566312041152512 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((25476206522531840 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((25476206522531840 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 25476206522531840 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 649037107316853453566312041152512`
(`‖G - S1298074214633706907132624082305024‖ ≤ 24/25476206522531840`; generic mirror of
`eta_tail_162259276829213363391578010288128_le` above and latest exact
`eta_tail_324518553658426726783156020576256_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_649037107316853453566312041152512_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 649037107316853453566312041152512), etaDirichletTerm s k)‖ ≤
      (24 / 25476206522531840 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 649037107316853453566312041152512 (by norm_num)
  have h2M : 2 * 649037107316853453566312041152512 = 1298074214633706907132624082305024 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_649037107316853453566312041152512_le
  linarith

/-- The `M = 649037107316853453566312041152512` constant honestly improves on the banked
`M = 324518553658426726783156020576256` constant
(`24/25476206522531840 < 3/2251799813685248`). -/
theorem tail_649037107316853453566312041152512_lt_324518553658426726783156020576256 : (24 / 25476206522531840 : ℝ) < (3 / 2251799813685248 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 1298074214633706907132624082305024` tail
(`1298074214633706907132624082305024^{1/2} = 36028797018963968` exact; exact shape mirror of
`M324518553658426726783156020576256_rpow_eq` above and latest odd-floor
`M649037107316853453566312041152512_rpow_ge` above; honest via
`36028797018963968^2 = 1298074214633706907132624082305024` by `norm_num`;
`1298074214633706907132624082305024 = 2^110` so the root is exact, unlike
`649037107316853453566312041152512`). -/
theorem M1298074214633706907132624082305024_rpow_eq :
    ((((1298074214633706907132624082305024 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (36028797018963968 : ℝ) := by
  have hx2 : ((((((1298074214633706907132624082305024 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((1298074214633706907132624082305024 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((36028797018963968 : ℝ) ^ (2 : ℕ)) = ((((1298074214633706907132624082305024 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((1298074214633706907132624082305024 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (36028797018963968 : ℝ) := by norm_num
  have hle1 : ((((((1298074214633706907132624082305024 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((36028797018963968 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((36028797018963968 : ℝ) ^ (2 : ℕ)) ≤
      ((((((1298074214633706907132624082305024 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 1298074214633706907132624082305024` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/36028797018963968 = 3/4503599627370496`; exact shape mirror of
`r_324518553658426726783156020576256_le` above; decay recomputed honestly with
`norm_num` via the exact `M1298074214633706907132624082305024_rpow_eq`; tightest honest
`T = 3/4503599627370496` for this root). -/
theorem r_1298074214633706907132624082305024_le :
    (12 : ℝ) * ((((((1298074214633706907132624082305024 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 4503599627370496 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((1298074214633706907132624082305024 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M1298074214633706907132624082305024_rpow_eq
  have hrw : ((((1298074214633706907132624082305024 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((1298074214633706907132624082305024 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((36028797018963968 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 4503599627370496 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 1298074214633706907132624082305024`
(`‖G - S2596148429267413814265248164610048‖ ≤ 3/4503599627370496`; exact shape mirror of
`eta_tail_324518553658426726783156020576256_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_1298074214633706907132624082305024_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 1298074214633706907132624082305024), etaDirichletTerm s k)‖ ≤
      (3 / 4503599627370496 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1298074214633706907132624082305024 (by norm_num)
  have h2M : 2 * 1298074214633706907132624082305024 = 2596148429267413814265248164610048 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_1298074214633706907132624082305024_le
  linarith

/-- The `M = 1298074214633706907132624082305024` constant honestly improves on the banked
`M = 649037107316853453566312041152512` constant
(`3/4503599627370496 < 24/25476206522531840`). -/
theorem tail_1298074214633706907132624082305024_lt_649037107316853453566312041152512 : (3 / 4503599627370496 : ℝ) < (24 / 25476206522531840 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 2596148429267413814265248164610048` tail
(`50952413045063680 ≤ 2596148429267413814265248164610048^{1/2}`; generic mirror of
`M649037107316853453566312041152512_rpow_ge` above and latest exact
`M1298074214633706907132624082305024_rpow_eq` above; honest floor via
`50952413045063680 = 2 * 25476206522531840` with `50952413045063680^2 =
2596148395114775471350415255142400 ≤ 2596148429267413814265248164610048`
by `norm_num`; `2596148429267413814265248164610048 = 2^111` so root
`36028797018963968·√2 ≈ 50952413380...` is NOT exact, unlike
`1298074214633706907132624082305024`; lower gap `34152638342914832909467648`). -/
theorem M2596148429267413814265248164610048_rpow_ge :
    (50952413045063680 : ℝ) ≤ ((((2596148429267413814265248164610048 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((50952413045063680 : ℝ) ^ (2 : ℕ)) ≤ ((((2596148429267413814265248164610048 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((2596148429267413814265248164610048 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((2596148429267413814265248164610048 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 2596148429267413814265248164610048` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/50952413045063680`; generic mirror of
`r_649037107316853453566312041152512_le` above and latest exact
`r_1298074214633706907132624082305024_le` above; decay recomputed honestly with
`norm_num` via `M2596148429267413814265248164610048_rpow_ge`; honest conservative
`T = 24/50952413045063680` for the `50952413045063680` root lower). -/
theorem r_2596148429267413814265248164610048_le :
    (12 : ℝ) * ((((((2596148429267413814265248164610048 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 50952413045063680 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((2596148429267413814265248164610048 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((2596148429267413814265248164610048 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M2596148429267413814265248164610048_rpow_ge
  have hrw : ((((2596148429267413814265248164610048 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((2596148429267413814265248164610048 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((2596148429267413814265248164610048 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (50952413045063680 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((2596148429267413814265248164610048 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (50952413045063680 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((2596148429267413814265248164610048 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((50952413045063680 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((50952413045063680 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 50952413045063680 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 2596148429267413814265248164610048`
(`‖G - S5192296858534827628530496329220096‖ ≤ 24/50952413045063680`; generic mirror of
`eta_tail_649037107316853453566312041152512_le` above and latest exact
`eta_tail_1298074214633706907132624082305024_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_2596148429267413814265248164610048_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 2596148429267413814265248164610048), etaDirichletTerm s k)‖ ≤
      (24 / 50952413045063680 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 2596148429267413814265248164610048 (by norm_num)
  have h2M : 2 * 2596148429267413814265248164610048 = 5192296858534827628530496329220096 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_2596148429267413814265248164610048_le
  linarith

/-- The `M = 2596148429267413814265248164610048` constant honestly improves on the banked
`M = 1298074214633706907132624082305024` constant
(`24/50952413045063680 < 3/4503599627370496`). -/
theorem tail_2596148429267413814265248164610048_lt_1298074214633706907132624082305024 : (24 / 50952413045063680 : ℝ) < (3 / 4503599627370496 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 5192296858534827628530496329220096` tail
(`5192296858534827628530496329220096^{1/2} = 72057594037927936` exact; exact shape mirror of
`M1298074214633706907132624082305024_rpow_eq` above and latest odd-floor
`M2596148429267413814265248164610048_rpow_ge` above; honest via
`72057594037927936^2 = 5192296858534827628530496329220096` by `norm_num`;
`5192296858534827628530496329220096 = 2^112` so the root is exact, unlike
`2596148429267413814265248164610048`). -/
theorem M5192296858534827628530496329220096_rpow_eq :
    ((((5192296858534827628530496329220096 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (72057594037927936 : ℝ) := by
  have hx2 : ((((((5192296858534827628530496329220096 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((5192296858534827628530496329220096 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((72057594037927936 : ℝ) ^ (2 : ℕ)) = ((((5192296858534827628530496329220096 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((5192296858534827628530496329220096 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (72057594037927936 : ℝ) := by norm_num
  have hle1 : ((((((5192296858534827628530496329220096 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((72057594037927936 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((72057594037927936 : ℝ) ^ (2 : ℕ)) ≤
      ((((((5192296858534827628530496329220096 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 5192296858534827628530496329220096` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/72057594037927936 = 3/9007199254740992`; exact shape mirror of
`r_1298074214633706907132624082305024_le` above; decay recomputed honestly with
`norm_num` via the exact `M5192296858534827628530496329220096_rpow_eq`; tightest honest
`T = 3/9007199254740992` for this root). -/
theorem r_5192296858534827628530496329220096_le :
    (12 : ℝ) * ((((((5192296858534827628530496329220096 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 9007199254740992 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((5192296858534827628530496329220096 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M5192296858534827628530496329220096_rpow_eq
  have hrw : ((((5192296858534827628530496329220096 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((5192296858534827628530496329220096 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((72057594037927936 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 9007199254740992 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 5192296858534827628530496329220096`
(`‖G - S10384593717069655257060992658440192‖ ≤ 3/9007199254740992`; exact shape mirror of
`eta_tail_1298074214633706907132624082305024_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_5192296858534827628530496329220096_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 5192296858534827628530496329220096), etaDirichletTerm s k)‖ ≤
      (3 / 9007199254740992 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 5192296858534827628530496329220096 (by norm_num)
  have h2M : 2 * 5192296858534827628530496329220096 = 10384593717069655257060992658440192 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_5192296858534827628530496329220096_le
  linarith

/-- The `M = 5192296858534827628530496329220096` constant honestly improves on the banked
`M = 2596148429267413814265248164610048` constant
(`3/9007199254740992 < 24/50952413045063680`). -/
theorem tail_5192296858534827628530496329220096_lt_2596148429267413814265248164610048 : (3 / 9007199254740992 : ℝ) < (24 / 50952413045063680 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 10384593717069655257060992658440192` tail
(`101904826090127360 ≤ 10384593717069655257060992658440192^{1/2}`; generic mirror of
`M2596148429267413814265248164610048_rpow_ge` above and latest exact
`M5192296858534827628530496329220096_rpow_eq` above; honest floor via
`101904826090127360 = 2 * 50952413045063680` with `101904826090127360^2 =
10384593580459101885401661020569600 ≤ 10384593717069655257060992658440192`
by `norm_num`; `10384593717069655257060992658440192 = 2^113` so root
`72057594037927936·√2` is NOT exact, unlike
`5192296858534827628530496329220096`; lower gap `136610553371659331637870592`). -/
theorem M10384593717069655257060992658440192_rpow_ge :
    (101904826090127360 : ℝ) ≤ ((((10384593717069655257060992658440192 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((101904826090127360 : ℝ) ^ (2 : ℕ)) ≤ ((((10384593717069655257060992658440192 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((10384593717069655257060992658440192 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((10384593717069655257060992658440192 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 10384593717069655257060992658440192` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/101904826090127360`; generic mirror of
`r_2596148429267413814265248164610048_le` above and latest exact
`r_5192296858534827628530496329220096_le` above; decay recomputed honestly with
`norm_num` via `M10384593717069655257060992658440192_rpow_ge`; honest conservative
`T = 24/101904826090127360` for the `101904826090127360` root lower). -/
theorem r_10384593717069655257060992658440192_le :
    (12 : ℝ) * ((((((10384593717069655257060992658440192 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 101904826090127360 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((10384593717069655257060992658440192 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((10384593717069655257060992658440192 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M10384593717069655257060992658440192_rpow_ge
  have hrw : ((((10384593717069655257060992658440192 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((10384593717069655257060992658440192 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((10384593717069655257060992658440192 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (101904826090127360 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((10384593717069655257060992658440192 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (101904826090127360 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((10384593717069655257060992658440192 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((101904826090127360 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((101904826090127360 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 101904826090127360 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 10384593717069655257060992658440192`
(`‖G - S20769187434139310514121985316880384‖ ≤ 24/101904826090127360`; generic mirror of
`eta_tail_2596148429267413814265248164610048_le` above and latest exact
`eta_tail_5192296858534827628530496329220096_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_10384593717069655257060992658440192_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 10384593717069655257060992658440192), etaDirichletTerm s k)‖ ≤
      (24 / 101904826090127360 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 10384593717069655257060992658440192 (by norm_num)
  have h2M : 2 * 10384593717069655257060992658440192 = 20769187434139310514121985316880384 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_10384593717069655257060992658440192_le
  linarith

/-- The `M = 10384593717069655257060992658440192` constant honestly improves on the banked
`M = 5192296858534827628530496329220096` constant
(`24/101904826090127360 < 3/9007199254740992`). -/
theorem tail_10384593717069655257060992658440192_lt_5192296858534827628530496329220096 : (24 / 101904826090127360 : ℝ) < (3 / 9007199254740992 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 20769187434139310514121985316880384` tail
(`20769187434139310514121985316880384^{1/2} = 144115188075855872` exact; exact shape mirror of
`M5192296858534827628530496329220096_rpow_eq` above and latest odd-floor
`M10384593717069655257060992658440192_rpow_ge` above; honest via
`144115188075855872^2 = 20769187434139310514121985316880384` by `norm_num`;
`20769187434139310514121985316880384 = 2^114` so the root is exact, unlike
`10384593717069655257060992658440192`). -/
theorem M20769187434139310514121985316880384_rpow_eq :
    ((((20769187434139310514121985316880384 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (144115188075855872 : ℝ) := by
  have hx2 : ((((((20769187434139310514121985316880384 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((20769187434139310514121985316880384 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((144115188075855872 : ℝ) ^ (2 : ℕ)) = ((((20769187434139310514121985316880384 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((20769187434139310514121985316880384 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (144115188075855872 : ℝ) := by norm_num
  have hle1 : ((((((20769187434139310514121985316880384 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((144115188075855872 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((144115188075855872 : ℝ) ^ (2 : ℕ)) ≤
      ((((((20769187434139310514121985316880384 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 20769187434139310514121985316880384` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/144115188075855872 = 3/18014398509481984`; exact shape mirror of
`r_5192296858534827628530496329220096_le` above; decay recomputed honestly with
`norm_num` via the exact `M20769187434139310514121985316880384_rpow_eq`; tightest honest
`T = 3/18014398509481984` for this root). -/
theorem r_20769187434139310514121985316880384_le :
    (12 : ℝ) * ((((((20769187434139310514121985316880384 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 18014398509481984 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((20769187434139310514121985316880384 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M20769187434139310514121985316880384_rpow_eq
  have hrw : ((((20769187434139310514121985316880384 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((20769187434139310514121985316880384 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((144115188075855872 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 18014398509481984 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 20769187434139310514121985316880384`
(`‖G - S41538374868278621028243970633760768‖ ≤ 3/18014398509481984`; exact shape mirror of
`eta_tail_5192296858534827628530496329220096_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_20769187434139310514121985316880384_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 20769187434139310514121985316880384), etaDirichletTerm s k)‖ ≤
      (3 / 18014398509481984 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 20769187434139310514121985316880384 (by norm_num)
  have h2M : 2 * 20769187434139310514121985316880384 = 41538374868278621028243970633760768 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_20769187434139310514121985316880384_le
  linarith

/-- The `M = 20769187434139310514121985316880384` constant honestly improves on the banked
`M = 10384593717069655257060992658440192` constant
(`3/18014398509481984 < 24/101904826090127360`). -/
theorem tail_20769187434139310514121985316880384_lt_10384593717069655257060992658440192 : (3 / 18014398509481984 : ℝ) < (24 / 101904826090127360 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 41538374868278621028243970633760768` tail
(`203809652180254720 ≤ 41538374868278621028243970633760768^{1/2}`; generic mirror of
`M10384593717069655257060992658440192_rpow_ge` above and latest exact
`M20769187434139310514121985316880384_rpow_eq` above; honest floor via
`203809652180254720 = 2 * 101904826090127360` with `203809652180254720^2 =
41538374321836407541606644082278400 ≤ 41538374868278621028243970633760768`
by `norm_num`; `41538374868278621028243970633760768 = 2^115` so root
`144115188075855872·√2` is NOT exact, unlike
`20769187434139310514121985316880384`; lower gap `546442213486637326551482368`). -/
theorem M41538374868278621028243970633760768_rpow_ge :
    (203809652180254720 : ℝ) ≤ ((((41538374868278621028243970633760768 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((203809652180254720 : ℝ) ^ (2 : ℕ)) ≤ ((((41538374868278621028243970633760768 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((41538374868278621028243970633760768 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((41538374868278621028243970633760768 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 41538374868278621028243970633760768` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/203809652180254720`; generic mirror of
`r_10384593717069655257060992658440192_le` above and latest exact
`r_20769187434139310514121985316880384_le` above; decay recomputed honestly with
`norm_num` via `M41538374868278621028243970633760768_rpow_ge`; honest conservative
`T = 24/203809652180254720` for the `203809652180254720` root lower). -/
theorem r_41538374868278621028243970633760768_le :
    (12 : ℝ) * ((((((41538374868278621028243970633760768 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 203809652180254720 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((41538374868278621028243970633760768 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((41538374868278621028243970633760768 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M41538374868278621028243970633760768_rpow_ge
  have hrw : ((((41538374868278621028243970633760768 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((41538374868278621028243970633760768 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((41538374868278621028243970633760768 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (203809652180254720 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((41538374868278621028243970633760768 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (203809652180254720 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((41538374868278621028243970633760768 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((203809652180254720 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((203809652180254720 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 203809652180254720 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 41538374868278621028243970633760768`
(`‖G - S83076749736557242056487941267521536‖ ≤ 24/203809652180254720`; generic mirror of
`eta_tail_10384593717069655257060992658440192_le` above and latest exact
`eta_tail_20769187434139310514121985316880384_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_41538374868278621028243970633760768_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 41538374868278621028243970633760768), etaDirichletTerm s k)‖ ≤
      (24 / 203809652180254720 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 41538374868278621028243970633760768 (by norm_num)
  have h2M : 2 * 41538374868278621028243970633760768 = 83076749736557242056487941267521536 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_41538374868278621028243970633760768_le
  linarith

/-- The `M = 41538374868278621028243970633760768` constant honestly improves on the banked
`M = 20769187434139310514121985316880384` constant
(`24/203809652180254720 < 3/18014398509481984`). -/
theorem tail_41538374868278621028243970633760768_lt_20769187434139310514121985316880384 : (24 / 203809652180254720 : ℝ) < (3 / 18014398509481984 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 83076749736557242056487941267521536` tail
(`83076749736557242056487941267521536^{1/2} = 288230376151711744` exact; exact shape mirror of
`M20769187434139310514121985316880384_rpow_eq` above and latest odd-floor
`M41538374868278621028243970633760768_rpow_ge` above; honest via
`288230376151711744^2 = 83076749736557242056487941267521536` by `norm_num`;
`83076749736557242056487941267521536 = 2^116` so the root is exact, unlike
`41538374868278621028243970633760768`). -/
theorem M83076749736557242056487941267521536_rpow_eq :
    ((((83076749736557242056487941267521536 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (288230376151711744 : ℝ) := by
  have hx2 : ((((((83076749736557242056487941267521536 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((83076749736557242056487941267521536 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((288230376151711744 : ℝ) ^ (2 : ℕ)) = ((((83076749736557242056487941267521536 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((83076749736557242056487941267521536 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (288230376151711744 : ℝ) := by norm_num
  have hle1 : ((((((83076749736557242056487941267521536 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((288230376151711744 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((288230376151711744 : ℝ) ^ (2 : ℕ)) ≤
      ((((((83076749736557242056487941267521536 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 83076749736557242056487941267521536` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/288230376151711744 = 3/36028797018963968`; exact shape mirror of
`r_20769187434139310514121985316880384_le` above; decay recomputed honestly with
`norm_num` via the exact `M83076749736557242056487941267521536_rpow_eq`; tightest honest
`T = 3/36028797018963968` for this root). -/
theorem r_83076749736557242056487941267521536_le :
    (12 : ℝ) * ((((((83076749736557242056487941267521536 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 36028797018963968 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((83076749736557242056487941267521536 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M83076749736557242056487941267521536_rpow_eq
  have hrw : ((((83076749736557242056487941267521536 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((83076749736557242056487941267521536 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((288230376151711744 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 36028797018963968 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 83076749736557242056487941267521536`
(`‖G - S166153499473114484112975882535043072‖ ≤ 3/36028797018963968`; exact shape mirror of
`eta_tail_20769187434139310514121985316880384_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_83076749736557242056487941267521536_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 83076749736557242056487941267521536), etaDirichletTerm s k)‖ ≤
      (3 / 36028797018963968 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 83076749736557242056487941267521536 (by norm_num)
  have h2M : 2 * 83076749736557242056487941267521536 = 166153499473114484112975882535043072 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_83076749736557242056487941267521536_le
  linarith

/-- The `M = 83076749736557242056487941267521536` constant honestly improves on the banked
`M = 41538374868278621028243970633760768` constant
(`3/36028797018963968 < 24/203809652180254720`). -/
theorem tail_83076749736557242056487941267521536_lt_41538374868278621028243970633760768 : (3 / 36028797018963968 : ℝ) < (24 / 203809652180254720 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 166153499473114484112975882535043072` tail
(`407619304360509440 ≤ 166153499473114484112975882535043072^{1/2}`; generic mirror of
`M41538374868278621028243970633760768_rpow_ge` above and latest exact
`M83076749736557242056487941267521536_rpow_eq` above; honest floor via
`407619304360509440 = 2 * 203809652180254720` with `407619304360509440^2 =
166153497287345630166426576329113600 ≤ 166153499473114484112975882535043072`
by `norm_num`; `166153499473114484112975882535043072 = 2^117` so root
`288230376151711744·√2` is NOT exact, unlike
`83076749736557242056487941267521536`; lower gap `2185768853946549306205929472`). -/
theorem M166153499473114484112975882535043072_rpow_ge :
    (407619304360509440 : ℝ) ≤ ((((166153499473114484112975882535043072 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((407619304360509440 : ℝ) ^ (2 : ℕ)) ≤ ((((166153499473114484112975882535043072 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((166153499473114484112975882535043072 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((166153499473114484112975882535043072 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 166153499473114484112975882535043072` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/407619304360509440`; generic mirror of
`r_41538374868278621028243970633760768_le` above and latest exact
`r_83076749736557242056487941267521536_le` above; decay recomputed honestly with
`norm_num` via `M166153499473114484112975882535043072_rpow_ge`; honest conservative
`T = 24/407619304360509440` for the `407619304360509440` root lower). -/
theorem r_166153499473114484112975882535043072_le :
    (12 : ℝ) * ((((((166153499473114484112975882535043072 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 407619304360509440 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((166153499473114484112975882535043072 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((166153499473114484112975882535043072 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M166153499473114484112975882535043072_rpow_ge
  have hrw : ((((166153499473114484112975882535043072 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((166153499473114484112975882535043072 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((166153499473114484112975882535043072 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (407619304360509440 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((166153499473114484112975882535043072 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (407619304360509440 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((166153499473114484112975882535043072 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((407619304360509440 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((407619304360509440 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 407619304360509440 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 166153499473114484112975882535043072`
(`‖G - S332306998946228968225951765070086144‖ ≤ 24/407619304360509440`; generic mirror of
`eta_tail_41538374868278621028243970633760768_le` above and latest exact
`eta_tail_83076749736557242056487941267521536_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_166153499473114484112975882535043072_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 166153499473114484112975882535043072), etaDirichletTerm s k)‖ ≤
      (24 / 407619304360509440 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 166153499473114484112975882535043072 (by norm_num)
  have h2M : 2 * 166153499473114484112975882535043072 = 332306998946228968225951765070086144 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_166153499473114484112975882535043072_le
  linarith

/-- The `M = 166153499473114484112975882535043072` constant honestly improves on the banked
`M = 83076749736557242056487941267521536` constant
(`24/407619304360509440 < 3/36028797018963968`). -/
theorem tail_166153499473114484112975882535043072_lt_83076749736557242056487941267521536 : (24 / 407619304360509440 : ℝ) < (3 / 36028797018963968 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 332306998946228968225951765070086144` tail
(`332306998946228968225951765070086144^{1/2} = 576460752303423488` exact; exact shape mirror of
`M83076749736557242056487941267521536_rpow_eq` above and latest odd-floor
`M166153499473114484112975882535043072_rpow_ge` above; honest via
`576460752303423488^2 = 332306998946228968225951765070086144` by `norm_num`;
`332306998946228968225951765070086144 = 2^118` so the root is exact, unlike
`166153499473114484112975882535043072`). -/
theorem M332306998946228968225951765070086144_rpow_eq :
    ((((332306998946228968225951765070086144 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (576460752303423488 : ℝ) := by
  have hx2 : ((((((332306998946228968225951765070086144 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((332306998946228968225951765070086144 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((576460752303423488 : ℝ) ^ (2 : ℕ)) = ((((332306998946228968225951765070086144 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((332306998946228968225951765070086144 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (576460752303423488 : ℝ) := by norm_num
  have hle1 : ((((((332306998946228968225951765070086144 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((576460752303423488 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((576460752303423488 : ℝ) ^ (2 : ℕ)) ≤
      ((((((332306998946228968225951765070086144 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 332306998946228968225951765070086144` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/576460752303423488 = 3/72057594037927936`; exact shape mirror of
`r_83076749736557242056487941267521536_le` above; decay recomputed honestly with
`norm_num` via the exact `M332306998946228968225951765070086144_rpow_eq`; tightest honest
`T = 3/72057594037927936` for this root). -/
theorem r_332306998946228968225951765070086144_le :
    (12 : ℝ) * ((((((332306998946228968225951765070086144 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 72057594037927936 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((332306998946228968225951765070086144 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M332306998946228968225951765070086144_rpow_eq
  have hrw : ((((332306998946228968225951765070086144 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((332306998946228968225951765070086144 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((576460752303423488 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 72057594037927936 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 332306998946228968225951765070086144`
(`‖G - S664613997892457936451903530140172288‖ ≤ 3/72057594037927936`; exact shape mirror of
`eta_tail_83076749736557242056487941267521536_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_332306998946228968225951765070086144_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 332306998946228968225951765070086144), etaDirichletTerm s k)‖ ≤
      (3 / 72057594037927936 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 332306998946228968225951765070086144 (by norm_num)
  have h2M : 2 * 332306998946228968225951765070086144 = 664613997892457936451903530140172288 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_332306998946228968225951765070086144_le
  linarith

/-- The `M = 332306998946228968225951765070086144` constant honestly improves on the banked
`M = 166153499473114484112975882535043072` constant
(`3/72057594037927936 < 24/407619304360509440`). -/
theorem tail_332306998946228968225951765070086144_lt_166153499473114484112975882535043072 : (3 / 72057594037927936 : ℝ) < (24 / 407619304360509440 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 664613997892457936451903530140172288` tail
(`815238608721018880 ≤ 664613997892457936451903530140172288^{1/2}`; generic mirror of
`M166153499473114484112975882535043072_rpow_ge` above and latest exact
`M332306998946228968225951765070086144_rpow_eq` above; honest floor via
`815238608721018880 = 2 * 407619304360509440` with `815238608721018880^2 =
664613989149382520665706305316454400 ≤ 664613997892457936451903530140172288`
by `norm_num`; `664613997892457936451903530140172288 = 2^119` so root
`576460752303423488·√2 ≈ 815238614083298888.27` is NOT exact, unlike
`332306998946228968225951765070086144`; conservative doubling below true floor
`815238614083298888`; lower gap `8743075415786197224823717888`). -/
theorem M664613997892457936451903530140172288_rpow_ge :
    (815238608721018880 : ℝ) ≤ ((((664613997892457936451903530140172288 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((815238608721018880 : ℝ) ^ (2 : ℕ)) ≤ ((((664613997892457936451903530140172288 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((664613997892457936451903530140172288 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((664613997892457936451903530140172288 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 664613997892457936451903530140172288` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/815238608721018880`; generic mirror of
`r_166153499473114484112975882535043072_le` above and latest exact
`r_332306998946228968225951765070086144_le` above; decay recomputed honestly with
`norm_num` via `M664613997892457936451903530140172288_rpow_ge`; honest conservative
`T = 24/815238608721018880` for the `815238608721018880` root lower). -/
theorem r_664613997892457936451903530140172288_le :
    (12 : ℝ) * ((((((664613997892457936451903530140172288 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 815238608721018880 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((664613997892457936451903530140172288 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((664613997892457936451903530140172288 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M664613997892457936451903530140172288_rpow_ge
  have hrw : ((((664613997892457936451903530140172288 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((664613997892457936451903530140172288 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((664613997892457936451903530140172288 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (815238608721018880 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((664613997892457936451903530140172288 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (815238608721018880 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((664613997892457936451903530140172288 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((815238608721018880 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((815238608721018880 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 815238608721018880 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 664613997892457936451903530140172288`
(`‖G - S1329227995784915872903807060280344576‖ ≤ 24/815238608721018880`; generic mirror of
`eta_tail_166153499473114484112975882535043072_le` above and latest exact
`eta_tail_332306998946228968225951765070086144_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_664613997892457936451903530140172288_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 664613997892457936451903530140172288), etaDirichletTerm s k)‖ ≤
      (24 / 815238608721018880 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 664613997892457936451903530140172288 (by norm_num)
  have h2M : 2 * 664613997892457936451903530140172288 = 1329227995784915872903807060280344576 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_664613997892457936451903530140172288_le
  linarith

/-- The `M = 664613997892457936451903530140172288` constant honestly improves on the banked
`M = 332306998946228968225951765070086144` constant
(`24/815238608721018880 < 3/72057594037927936`). -/
theorem tail_664613997892457936451903530140172288_lt_332306998946228968225951765070086144 : (24 / 815238608721018880 : ℝ) < (3 / 72057594037927936 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 1329227995784915872903807060280344576` tail
(`1329227995784915872903807060280344576^{1/2} = 1152921504606846976` exact; exact shape mirror of
`M332306998946228968225951765070086144_rpow_eq` above and latest odd-floor
`M664613997892457936451903530140172288_rpow_ge` above; honest via
`1152921504606846976^2 = 1329227995784915872903807060280344576` by `norm_num`;
`1329227995784915872903807060280344576 = 2^120` so the root is exact, unlike
`664613997892457936451903530140172288`). -/
theorem M1329227995784915872903807060280344576_rpow_eq :
    ((((1329227995784915872903807060280344576 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (1152921504606846976 : ℝ) := by
  have hx2 : ((((((1329227995784915872903807060280344576 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((1329227995784915872903807060280344576 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((1152921504606846976 : ℝ) ^ (2 : ℕ)) = ((((1329227995784915872903807060280344576 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((1329227995784915872903807060280344576 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (1152921504606846976 : ℝ) := by norm_num
  have hle1 : ((((((1329227995784915872903807060280344576 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((1152921504606846976 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((1152921504606846976 : ℝ) ^ (2 : ℕ)) ≤
      ((((((1329227995784915872903807060280344576 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 1329227995784915872903807060280344576` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/1152921504606846976 = 3/144115188075855872`; exact shape mirror of
`r_332306998946228968225951765070086144_le` above; decay recomputed honestly with
`norm_num` via the exact `M1329227995784915872903807060280344576_rpow_eq`; tightest honest
`T = 3/144115188075855872` for this root). -/
theorem r_1329227995784915872903807060280344576_le :
    (12 : ℝ) * ((((((1329227995784915872903807060280344576 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 144115188075855872 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((1329227995784915872903807060280344576 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M1329227995784915872903807060280344576_rpow_eq
  have hrw : ((((1329227995784915872903807060280344576 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((1329227995784915872903807060280344576 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((1152921504606846976 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 144115188075855872 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 1329227995784915872903807060280344576`
(`‖G - S2658455991569831745807614120560689152‖ ≤ 3/144115188075855872`; exact shape mirror of
`eta_tail_332306998946228968225951765070086144_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_1329227995784915872903807060280344576_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 1329227995784915872903807060280344576), etaDirichletTerm s k)‖ ≤
      (3 / 144115188075855872 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1329227995784915872903807060280344576 (by norm_num)
  have h2M : 2 * 1329227995784915872903807060280344576 = 2658455991569831745807614120560689152 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_1329227995784915872903807060280344576_le
  linarith

/-- The `M = 1329227995784915872903807060280344576` constant honestly improves on the banked
`M = 664613997892457936451903530140172288` constant
(`3/144115188075855872 < 24/815238608721018880`). -/
theorem tail_1329227995784915872903807060280344576_lt_664613997892457936451903530140172288 : (3 / 144115188075855872 : ℝ) < (24 / 815238608721018880 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 2658455991569831745807614120560689152` tail
(`1630477217442037760 ≤ 2658455991569831745807614120560689152^{1/2}`; generic mirror of
`M664613997892457936451903530140172288_rpow_ge` above and latest exact
`M1329227995784915872903807060280344576_rpow_eq` above; honest floor via
`1630477217442037760 = 2 * 815238608721018880` with `1630477217442037760^2 =
2658455956597530082662825221265817600 ≤ 2658455991569831745807614120560689152`
by `norm_num`; `2658455991569831745807614120560689152 = 2^121` so root
`1152921504606846976·√2 ≈ 1630477224898547623` is NOT exact, unlike
`1329227995784915872903807060280344576`; conservative doubling below true floor;
lower gap `34972301663144788899294871552`). -/
theorem M2658455991569831745807614120560689152_rpow_ge :
    (1630477217442037760 : ℝ) ≤ ((((2658455991569831745807614120560689152 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((1630477217442037760 : ℝ) ^ (2 : ℕ)) ≤ ((((2658455991569831745807614120560689152 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((2658455991569831745807614120560689152 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((2658455991569831745807614120560689152 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 2658455991569831745807614120560689152` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/1630477217442037760`; generic mirror of
`r_664613997892457936451903530140172288_le` above and latest exact
`r_1329227995784915872903807060280344576_le` above; decay recomputed honestly with
`norm_num` via `M2658455991569831745807614120560689152_rpow_ge`; honest conservative
`T = 24/1630477217442037760` for the `1630477217442037760` root lower). -/
theorem r_2658455991569831745807614120560689152_le :
    (12 : ℝ) * ((((((2658455991569831745807614120560689152 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 1630477217442037760 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((2658455991569831745807614120560689152 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((2658455991569831745807614120560689152 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M2658455991569831745807614120560689152_rpow_ge
  have hrw : ((((2658455991569831745807614120560689152 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((2658455991569831745807614120560689152 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((2658455991569831745807614120560689152 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (1630477217442037760 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((2658455991569831745807614120560689152 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (1630477217442037760 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((2658455991569831745807614120560689152 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((1630477217442037760 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((1630477217442037760 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 1630477217442037760 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 2658455991569831745807614120560689152`
(`‖G - S5316911983139663491615228241121378304‖ ≤ 24/1630477217442037760`; generic mirror of
`eta_tail_664613997892457936451903530140172288_le` above and latest exact
`eta_tail_1329227995784915872903807060280344576_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_2658455991569831745807614120560689152_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 2658455991569831745807614120560689152), etaDirichletTerm s k)‖ ≤
      (24 / 1630477217442037760 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 2658455991569831745807614120560689152 (by norm_num)
  have h2M : 2 * 2658455991569831745807614120560689152 = 5316911983139663491615228241121378304 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_2658455991569831745807614120560689152_le
  linarith

/-- The `M = 2658455991569831745807614120560689152` constant honestly improves on the banked
`M = 1329227995784915872903807060280344576` constant
(`24/1630477217442037760 < 3/144115188075855872`). -/
theorem tail_2658455991569831745807614120560689152_lt_1329227995784915872903807060280344576 : (24 / 1630477217442037760 : ℝ) < (3 / 144115188075855872 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 5316911983139663491615228241121378304` tail
(`5316911983139663491615228241121378304^{1/2} = 2305843009213693952` exact; exact shape mirror of
`M1329227995784915872903807060280344576_rpow_eq` above and latest odd-floor
`M2658455991569831745807614120560689152_rpow_ge` above; honest via
`2305843009213693952^2 = 5316911983139663491615228241121378304` by `norm_num`;
`5316911983139663491615228241121378304 = 2^122` so the root is exact, unlike
`2658455991569831745807614120560689152`). -/
theorem M5316911983139663491615228241121378304_rpow_eq :
    ((((5316911983139663491615228241121378304 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (2305843009213693952 : ℝ) := by
  have hx2 : ((((((5316911983139663491615228241121378304 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((5316911983139663491615228241121378304 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((2305843009213693952 : ℝ) ^ (2 : ℕ)) = ((((5316911983139663491615228241121378304 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((5316911983139663491615228241121378304 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (2305843009213693952 : ℝ) := by norm_num
  have hle1 : ((((((5316911983139663491615228241121378304 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((2305843009213693952 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((2305843009213693952 : ℝ) ^ (2 : ℕ)) ≤
      ((((((5316911983139663491615228241121378304 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 5316911983139663491615228241121378304` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/2305843009213693952 = 3/288230376151711744`; exact shape mirror of
`r_1329227995784915872903807060280344576_le` above; decay recomputed honestly with
`norm_num` via the exact `M5316911983139663491615228241121378304_rpow_eq`; tightest honest
`T = 3/288230376151711744` for this root). -/
theorem r_5316911983139663491615228241121378304_le :
    (12 : ℝ) * ((((((5316911983139663491615228241121378304 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 288230376151711744 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((5316911983139663491615228241121378304 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M5316911983139663491615228241121378304_rpow_eq
  have hrw : ((((5316911983139663491615228241121378304 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((5316911983139663491615228241121378304 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((2305843009213693952 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 288230376151711744 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 5316911983139663491615228241121378304`
(`‖G - S10633823966279326983230456482242756608‖ ≤ 3/288230376151711744`; exact shape mirror of
`eta_tail_1329227995784915872903807060280344576_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_5316911983139663491615228241121378304_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 5316911983139663491615228241121378304), etaDirichletTerm s k)‖ ≤
      (3 / 288230376151711744 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 5316911983139663491615228241121378304 (by norm_num)
  have h2M : 2 * 5316911983139663491615228241121378304 = 10633823966279326983230456482242756608 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_5316911983139663491615228241121378304_le
  linarith

/-- The `M = 5316911983139663491615228241121378304` constant honestly improves on the banked
`M = 2658455991569831745807614120560689152` constant
(`3/288230376151711744 < 24/1630477217442037760`). -/
theorem tail_5316911983139663491615228241121378304_lt_2658455991569831745807614120560689152 : (3 / 288230376151711744 : ℝ) < (24 / 1630477217442037760 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 10633823966279326983230456482242756608` tail
(`3260954434884075520 ≤ 10633823966279326983230456482242756608^{1/2}`; generic mirror of
`M2658455991569831745807614120560689152_rpow_ge` above and latest exact
`M5316911983139663491615228241121378304_rpow_eq` above; honest floor via
`3260954434884075520 = 2 * 1630477217442037760` with `3260954434884075520^2 =
10633823826390120330651300885063270400 ≤ 10633823966279326983230456482242756608`
by `norm_num`; `10633823966279326983230456482242756608 = 2^123` so root
`2305843009213693952·√2 ≈ 3260954456333195776` is NOT exact, unlike
`5316911983139663491615228241121378304`; conservative doubling below true floor;
lower gap `139889206652579155597179486208`). -/
theorem M10633823966279326983230456482242756608_rpow_ge :
    (3260954434884075520 : ℝ) ≤ ((((10633823966279326983230456482242756608 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((3260954434884075520 : ℝ) ^ (2 : ℕ)) ≤ ((((10633823966279326983230456482242756608 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((10633823966279326983230456482242756608 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((10633823966279326983230456482242756608 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 10633823966279326983230456482242756608` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/3260954434884075520`; generic mirror of
`r_2658455991569831745807614120560689152_le` above and latest exact
`r_5316911983139663491615228241121378304_le` above; decay recomputed honestly with
`norm_num` via `M10633823966279326983230456482242756608_rpow_ge`; honest conservative
`T = 24/3260954434884075520` for the `3260954434884075520` root lower). -/
theorem r_10633823966279326983230456482242756608_le :
    (12 : ℝ) * ((((((10633823966279326983230456482242756608 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 3260954434884075520 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((10633823966279326983230456482242756608 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((10633823966279326983230456482242756608 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M10633823966279326983230456482242756608_rpow_ge
  have hrw : ((((10633823966279326983230456482242756608 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((10633823966279326983230456482242756608 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((10633823966279326983230456482242756608 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (3260954434884075520 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((10633823966279326983230456482242756608 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (3260954434884075520 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((10633823966279326983230456482242756608 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((3260954434884075520 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((3260954434884075520 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 3260954434884075520 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 10633823966279326983230456482242756608`
(`‖G - S21267647932558653966460912964485513216‖ ≤ 24/3260954434884075520`; generic mirror of
`eta_tail_2658455991569831745807614120560689152_le` above and latest exact
`eta_tail_5316911983139663491615228241121378304_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_10633823966279326983230456482242756608_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 10633823966279326983230456482242756608), etaDirichletTerm s k)‖ ≤
      (24 / 3260954434884075520 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 10633823966279326983230456482242756608 (by norm_num)
  have h2M : 2 * 10633823966279326983230456482242756608 = 21267647932558653966460912964485513216 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_10633823966279326983230456482242756608_le
  linarith

/-- The `M = 10633823966279326983230456482242756608` constant honestly improves on the banked
`M = 5316911983139663491615228241121378304` constant
(`24/3260954434884075520 < 3/288230376151711744`). -/
theorem tail_10633823966279326983230456482242756608_lt_5316911983139663491615228241121378304 : (24 / 3260954434884075520 : ℝ) < (3 / 288230376151711744 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 21267647932558653966460912964485513216` tail
(`21267647932558653966460912964485513216^{1/2} = 4611686018427387904` exact; exact shape mirror of
`M5316911983139663491615228241121378304_rpow_eq` above and latest odd-floor
`M10633823966279326983230456482242756608_rpow_ge` above; honest via
`4611686018427387904^2 = 21267647932558653966460912964485513216` by `norm_num`;
`21267647932558653966460912964485513216 = 2^124` so the root is exact, unlike
`10633823966279326983230456482242756608`). -/
theorem M21267647932558653966460912964485513216_rpow_eq :
    ((((21267647932558653966460912964485513216 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (4611686018427387904 : ℝ) := by
  have hx2 : ((((((21267647932558653966460912964485513216 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((21267647932558653966460912964485513216 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((4611686018427387904 : ℝ) ^ (2 : ℕ)) = ((((21267647932558653966460912964485513216 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((21267647932558653966460912964485513216 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (4611686018427387904 : ℝ) := by norm_num
  have hle1 : ((((((21267647932558653966460912964485513216 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((4611686018427387904 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((4611686018427387904 : ℝ) ^ (2 : ℕ)) ≤
      ((((((21267647932558653966460912964485513216 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 21267647932558653966460912964485513216` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/4611686018427387904 = 3/576460752303423488`; exact shape mirror of
`r_5316911983139663491615228241121378304_le` above; decay recomputed honestly with
`norm_num` via the exact `M21267647932558653966460912964485513216_rpow_eq`; tightest honest
`T = 3/576460752303423488` for this root). -/
theorem r_21267647932558653966460912964485513216_le :
    (12 : ℝ) * ((((((21267647932558653966460912964485513216 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 576460752303423488 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((21267647932558653966460912964485513216 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M21267647932558653966460912964485513216_rpow_eq
  have hrw : ((((21267647932558653966460912964485513216 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((21267647932558653966460912964485513216 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((4611686018427387904 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 576460752303423488 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 21267647932558653966460912964485513216`
(`‖G - S42535295865117307932921825928971026432‖ ≤ 3/576460752303423488`; exact shape mirror of
`eta_tail_5316911983139663491615228241121378304_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_21267647932558653966460912964485513216_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 21267647932558653966460912964485513216), etaDirichletTerm s k)‖ ≤
      (3 / 576460752303423488 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 21267647932558653966460912964485513216 (by norm_num)
  have h2M : 2 * 21267647932558653966460912964485513216 = 42535295865117307932921825928971026432 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_21267647932558653966460912964485513216_le
  linarith

/-- The `M = 21267647932558653966460912964485513216` constant honestly improves on the banked
`M = 10633823966279326983230456482242756608` constant
(`3/576460752303423488 < 24/3260954434884075520`). -/
theorem tail_21267647932558653966460912964485513216_lt_10633823966279326983230456482242756608 : (3 / 576460752303423488 : ℝ) < (24 / 3260954434884075520 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 42535295865117307932921825928971026432` tail
(`6521908869768151040 ≤ 42535295865117307932921825928971026432^{1/2}`; generic mirror of
`M10633823966279326983230456482242756608_rpow_ge` above and latest exact
`M21267647932558653966460912964485513216_rpow_eq` above; honest floor via
`6521908869768151040 = 2 * 3260954434884075520` with `6521908869768151040^2 =
42535295305560481322605203540253081600 ≤ 42535295865117307932921825928971026432`
by `norm_num`; `42535295865117307932921825928971026432 = 2^125` so root
`4611686018427387904·√2 ≈ 6521908912666391106.xx` is NOT exact, unlike
`21267647932558653966460912964485513216`; conservative doubling below true floor;
lower gap `559556826610316622388717944832`). -/
theorem M42535295865117307932921825928971026432_rpow_ge :
    (6521908869768151040 : ℝ) ≤ ((((42535295865117307932921825928971026432 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((6521908869768151040 : ℝ) ^ (2 : ℕ)) ≤ ((((42535295865117307932921825928971026432 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((42535295865117307932921825928971026432 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((42535295865117307932921825928971026432 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 42535295865117307932921825928971026432` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/6521908869768151040`; generic mirror of
`r_10633823966279326983230456482242756608_le` above and latest exact
`r_21267647932558653966460912964485513216_le` above; decay recomputed honestly with
`norm_num` via `M42535295865117307932921825928971026432_rpow_ge`; honest conservative
`T = 24/6521908869768151040` for the `6521908869768151040` root lower). -/
theorem r_42535295865117307932921825928971026432_le :
    (12 : ℝ) * ((((((42535295865117307932921825928971026432 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 6521908869768151040 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((42535295865117307932921825928971026432 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((42535295865117307932921825928971026432 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M42535295865117307932921825928971026432_rpow_ge
  have hrw : ((((42535295865117307932921825928971026432 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((42535295865117307932921825928971026432 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((42535295865117307932921825928971026432 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (6521908869768151040 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((42535295865117307932921825928971026432 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (6521908869768151040 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((42535295865117307932921825928971026432 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((6521908869768151040 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((6521908869768151040 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 6521908869768151040 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 42535295865117307932921825928971026432`
(`‖G - S85070591730234615865843651857942052864‖ ≤ 24/6521908869768151040`; generic mirror of
`eta_tail_10633823966279326983230456482242756608_le` above and latest exact
`eta_tail_21267647932558653966460912964485513216_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_42535295865117307932921825928971026432_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 42535295865117307932921825928971026432), etaDirichletTerm s k)‖ ≤
      (24 / 6521908869768151040 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 42535295865117307932921825928971026432 (by norm_num)
  have h2M : 2 * 42535295865117307932921825928971026432 = 85070591730234615865843651857942052864 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_42535295865117307932921825928971026432_le
  linarith

/-- The `M = 42535295865117307932921825928971026432` constant honestly improves on the banked
`M = 21267647932558653966460912964485513216` constant
(`24/6521908869768151040 < 3/576460752303423488`). -/
theorem tail_42535295865117307932921825928971026432_lt_21267647932558653966460912964485513216 : (24 / 6521908869768151040 : ℝ) < (3 / 576460752303423488 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 85070591730234615865843651857942052864` tail
(`85070591730234615865843651857942052864^{1/2} = 9223372036854775808` exact; exact shape mirror of
`M21267647932558653966460912964485513216_rpow_eq` above and latest odd-floor
`M42535295865117307932921825928971026432_rpow_ge` above; honest via
`9223372036854775808^2 = 85070591730234615865843651857942052864` by `norm_num`;
`85070591730234615865843651857942052864 = 2^126` so the root is exact, unlike
`42535295865117307932921825928971026432`). -/
theorem M85070591730234615865843651857942052864_rpow_eq :
    ((((85070591730234615865843651857942052864 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (9223372036854775808 : ℝ) := by
  have hx2 : ((((((85070591730234615865843651857942052864 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((85070591730234615865843651857942052864 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((9223372036854775808 : ℝ) ^ (2 : ℕ)) = ((((85070591730234615865843651857942052864 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((85070591730234615865843651857942052864 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (9223372036854775808 : ℝ) := by norm_num
  have hle1 : ((((((85070591730234615865843651857942052864 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((9223372036854775808 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((9223372036854775808 : ℝ) ^ (2 : ℕ)) ≤
      ((((((85070591730234615865843651857942052864 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 85070591730234615865843651857942052864` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/9223372036854775808 = 3/1152921504606846976`; exact shape mirror of
`r_21267647932558653966460912964485513216_le` above; decay recomputed honestly with
`norm_num` via the exact `M85070591730234615865843651857942052864_rpow_eq`; tightest honest
`T = 3/1152921504606846976` for this root). -/
theorem r_85070591730234615865843651857942052864_le :
    (12 : ℝ) * ((((((85070591730234615865843651857942052864 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 1152921504606846976 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((85070591730234615865843651857942052864 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M85070591730234615865843651857942052864_rpow_eq
  have hrw : ((((85070591730234615865843651857942052864 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((85070591730234615865843651857942052864 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((9223372036854775808 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 1152921504606846976 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 85070591730234615865843651857942052864`
(`‖G - S170141183460469231731687303715884105728‖ ≤ 3/1152921504606846976`; exact shape mirror of
`eta_tail_21267647932558653966460912964485513216_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_85070591730234615865843651857942052864_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 85070591730234615865843651857942052864), etaDirichletTerm s k)‖ ≤
      (3 / 1152921504606846976 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 85070591730234615865843651857942052864 (by norm_num)
  have h2M : 2 * 85070591730234615865843651857942052864 = 170141183460469231731687303715884105728 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_85070591730234615865843651857942052864_le
  linarith

/-- The `M = 85070591730234615865843651857942052864` constant honestly improves on the banked
`M = 42535295865117307932921825928971026432` constant
(`3/1152921504606846976 < 24/6521908869768151040`). -/
theorem tail_85070591730234615865843651857942052864_lt_42535295865117307932921825928971026432 : (3 / 1152921504606846976 : ℝ) < (24 / 6521908869768151040 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 170141183460469231731687303715884105728` tail
(`13043817739556300800 ≤ 170141183460469231731687303715884105728^{1/2}`; generic mirror of
`M42535295865117307932921825928971026432_rpow_ge` above and latest exact
`M85070591730234615865843651857942052864_rpow_eq` above; honest floor via
`13043817739556300800^2 =
170141181222763644607829252980080640000 ≤ 170141183460469231731687303715884105728`
by `norm_num`; `170141183460469231731687303715884105728 = 2^127` so root
`9223372036854775808·√2 ≈ 13043817825332782212.xx` is NOT exact, unlike
`85070591730234615865843651857942052864`; conservative near-doubling of the
`6521908869768151040` floor below the true floor `13043817825332782212`;
lower gap `2237705587123858050735803465728`). -/
theorem M170141183460469231731687303715884105728_rpow_ge :
    (13043817739556300800 : ℝ) ≤ ((((170141183460469231731687303715884105728 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((13043817739556300800 : ℝ) ^ (2 : ℕ)) ≤ ((((170141183460469231731687303715884105728 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((170141183460469231731687303715884105728 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((170141183460469231731687303715884105728 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 170141183460469231731687303715884105728` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/13043817739556300800`; generic mirror of
`r_42535295865117307932921825928971026432_le` above and latest exact
`r_85070591730234615865843651857942052864_le` above; decay recomputed honestly with
`norm_num` via `M170141183460469231731687303715884105728_rpow_ge`; honest conservative
`T = 24/13043817739556300800` for the `13043817739556300800` root lower). -/
theorem r_170141183460469231731687303715884105728_le :
    (12 : ℝ) * ((((((170141183460469231731687303715884105728 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 13043817739556300800 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((170141183460469231731687303715884105728 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((170141183460469231731687303715884105728 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M170141183460469231731687303715884105728_rpow_ge
  have hrw : ((((170141183460469231731687303715884105728 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((170141183460469231731687303715884105728 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((170141183460469231731687303715884105728 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (13043817739556300800 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((170141183460469231731687303715884105728 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (13043817739556300800 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((170141183460469231731687303715884105728 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((13043817739556300800 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((13043817739556300800 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 13043817739556300800 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 170141183460469231731687303715884105728`
(`‖G - S340282366920938463463374607431768211456‖ ≤ 24/13043817739556300800`; generic mirror of
`eta_tail_42535295865117307932921825928971026432_le` above and latest exact
`eta_tail_85070591730234615865843651857942052864_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_170141183460469231731687303715884105728_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 170141183460469231731687303715884105728), etaDirichletTerm s k)‖ ≤
      (24 / 13043817739556300800 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 170141183460469231731687303715884105728 (by norm_num)
  have h2M : 2 * 170141183460469231731687303715884105728 = 340282366920938463463374607431768211456 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_170141183460469231731687303715884105728_le
  linarith

/-- The `M = 170141183460469231731687303715884105728` constant honestly improves on the banked
`M = 85070591730234615865843651857942052864` constant
(`24/13043817739556300800 < 3/1152921504606846976`). -/
theorem tail_170141183460469231731687303715884105728_lt_85070591730234615865843651857942052864 : (24 / 13043817739556300800 : ℝ) < (3 / 1152921504606846976 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 340282366920938463463374607431768211456` tail
(`340282366920938463463374607431768211456^{1/2} = 18446744073709551616` exact; exact shape mirror of
`M85070591730234615865843651857942052864_rpow_eq` above and latest odd-floor
`M170141183460469231731687303715884105728_rpow_ge` above; honest via
`18446744073709551616^2 = 340282366920938463463374607431768211456` by `norm_num`;
`340282366920938463463374607431768211456 = 2^128` so the root is exact, unlike
`170141183460469231731687303715884105728`). -/
theorem M340282366920938463463374607431768211456_rpow_eq :
    ((((340282366920938463463374607431768211456 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (18446744073709551616 : ℝ) := by
  have hx2 : ((((((340282366920938463463374607431768211456 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((340282366920938463463374607431768211456 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((18446744073709551616 : ℝ) ^ (2 : ℕ)) = ((((340282366920938463463374607431768211456 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((340282366920938463463374607431768211456 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (18446744073709551616 : ℝ) := by norm_num
  have hle1 : ((((((340282366920938463463374607431768211456 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((18446744073709551616 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((18446744073709551616 : ℝ) ^ (2 : ℕ)) ≤
      ((((((340282366920938463463374607431768211456 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 340282366920938463463374607431768211456` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/18446744073709551616 = 3/2305843009213693952`; exact shape mirror of
`r_85070591730234615865843651857942052864_le` above; decay recomputed honestly with
`norm_num` via the exact `M340282366920938463463374607431768211456_rpow_eq`; tightest honest
`T = 3/2305843009213693952` for this root). -/
theorem r_340282366920938463463374607431768211456_le :
    (12 : ℝ) * ((((((340282366920938463463374607431768211456 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 2305843009213693952 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((340282366920938463463374607431768211456 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M340282366920938463463374607431768211456_rpow_eq
  have hrw : ((((340282366920938463463374607431768211456 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((340282366920938463463374607431768211456 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((18446744073709551616 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 2305843009213693952 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 340282366920938463463374607431768211456`
(`‖G - S680564733841876926926749214863536422912‖ ≤ 3/2305843009213693952`; exact shape mirror of
`eta_tail_85070591730234615865843651857942052864_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_340282366920938463463374607431768211456_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 340282366920938463463374607431768211456), etaDirichletTerm s k)‖ ≤
      (3 / 2305843009213693952 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 340282366920938463463374607431768211456 (by norm_num)
  have h2M : 2 * 340282366920938463463374607431768211456 = 680564733841876926926749214863536422912 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_340282366920938463463374607431768211456_le
  linarith

/-- The `M = 340282366920938463463374607431768211456` constant honestly improves on the banked
`M = 170141183460469231731687303715884105728` constant
(`3/2305843009213693952 < 24/13043817739556300800`). -/
theorem tail_340282366920938463463374607431768211456_lt_170141183460469231731687303715884105728 : (3 / 2305843009213693952 : ℝ) < (24 / 13043817739556300800 : ℝ) := by
  norm_num

end Door3TailEtaUpper


namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 680564733841876926926749214863536422912` tail
(`26087635479112601600 ≤ 680564733841876926926749214863536422912^{1/2}`; generic mirror of
`M170141183460469231731687303715884105728_rpow_ge` above and latest exact
`M340282366920938463463374607431768211456_rpow_eq` above; honest floor via
`26087635479112601600^2 =
680564724891054578431317011920322560000 ≤ 680564733841876926926749214863536422912`
by `norm_num`; `680564733841876926926749214863536422912 = 2^129` so root
`18446744073709551616·√2 ≈ 26087635650665564424.xx` is NOT exact, unlike
`340282366920938463463374607431768211456`; conservative doubling of the
`13043817739556300800` floor below the true floor `26087635650665564424`;
lower gap `8950822348495432202943213862912`). -/
theorem M680564733841876926926749214863536422912_rpow_ge :
    (26087635479112601600 : ℝ) ≤ ((((680564733841876926926749214863536422912 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((26087635479112601600 : ℝ) ^ (2 : ℕ)) ≤ ((((680564733841876926926749214863536422912 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((680564733841876926926749214863536422912 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((680564733841876926926749214863536422912 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 680564733841876926926749214863536422912` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/26087635479112601600`; generic mirror of
`r_170141183460469231731687303715884105728_le` above and latest exact
`r_340282366920938463463374607431768211456_le` above; decay recomputed honestly with
`norm_num` via `M680564733841876926926749214863536422912_rpow_ge`; honest conservative
`T = 24/26087635479112601600` for the `26087635479112601600` root lower). -/
theorem r_680564733841876926926749214863536422912_le :
    (12 : ℝ) * ((((((680564733841876926926749214863536422912 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 26087635479112601600 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((680564733841876926926749214863536422912 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((680564733841876926926749214863536422912 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M680564733841876926926749214863536422912_rpow_ge
  have hrw : ((((680564733841876926926749214863536422912 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((680564733841876926926749214863536422912 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((680564733841876926926749214863536422912 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (26087635479112601600 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((680564733841876926926749214863536422912 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (26087635479112601600 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((680564733841876926926749214863536422912 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((26087635479112601600 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((26087635479112601600 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 26087635479112601600 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 680564733841876926926749214863536422912`
(`‖G - S1361129467683753853853498429727072845824‖ ≤ 24/26087635479112601600`; generic mirror of
`eta_tail_170141183460469231731687303715884105728_le` above and latest exact
`eta_tail_340282366920938463463374607431768211456_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_680564733841876926926749214863536422912_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 680564733841876926926749214863536422912), etaDirichletTerm s k)‖ ≤
      (24 / 26087635479112601600 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 680564733841876926926749214863536422912 (by norm_num)
  have h2M : 2 * 680564733841876926926749214863536422912 = 1361129467683753853853498429727072845824 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_680564733841876926926749214863536422912_le
  linarith

/-- The `M = 680564733841876926926749214863536422912` constant honestly improves on the banked
`M = 340282366920938463463374607431768211456` constant
(`24/26087635479112601600 < 3/2305843009213693952`). -/
theorem tail_680564733841876926926749214863536422912_lt_340282366920938463463374607431768211456 : (24 / 26087635479112601600 : ℝ) < (3 / 2305843009213693952 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 1361129467683753853853498429727072845824` tail
(`1361129467683753853853498429727072845824^{1/2} = 36893488147419103232` exact; exact shape mirror of
`M340282366920938463463374607431768211456_rpow_eq` above and latest odd-floor
`M680564733841876926926749214863536422912_rpow_ge` above; honest via
`36893488147419103232^2 = 1361129467683753853853498429727072845824` by `norm_num`;
`1361129467683753853853498429727072845824 = 2^130` so the root is exact, unlike
`680564733841876926926749214863536422912`). -/
theorem M1361129467683753853853498429727072845824_rpow_eq :
    ((((1361129467683753853853498429727072845824 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (36893488147419103232 : ℝ) := by
  have hx2 : ((((((1361129467683753853853498429727072845824 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((1361129467683753853853498429727072845824 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((36893488147419103232 : ℝ) ^ (2 : ℕ)) = ((((1361129467683753853853498429727072845824 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((1361129467683753853853498429727072845824 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (36893488147419103232 : ℝ) := by norm_num
  have hle1 : ((((((1361129467683753853853498429727072845824 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((36893488147419103232 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((36893488147419103232 : ℝ) ^ (2 : ℕ)) ≤
      ((((((1361129467683753853853498429727072845824 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 1361129467683753853853498429727072845824` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/36893488147419103232 = 3/4611686018427387904`; exact shape mirror of
`r_340282366920938463463374607431768211456_le` above; decay recomputed honestly with
`norm_num` via the exact `M1361129467683753853853498429727072845824_rpow_eq`; tightest honest
`T = 3/4611686018427387904` for this root). -/
theorem r_1361129467683753853853498429727072845824_le :
    (12 : ℝ) * ((((((1361129467683753853853498429727072845824 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 4611686018427387904 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((1361129467683753853853498429727072845824 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M1361129467683753853853498429727072845824_rpow_eq
  have hrw : ((((1361129467683753853853498429727072845824 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((1361129467683753853853498429727072845824 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((36893488147419103232 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 4611686018427387904 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 1361129467683753853853498429727072845824`
(`‖G - S2722258935367507707706996859454145691648‖ ≤ 3/4611686018427387904`; exact shape mirror of
`eta_tail_340282366920938463463374607431768211456_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_1361129467683753853853498429727072845824_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 1361129467683753853853498429727072845824), etaDirichletTerm s k)‖ ≤
      (3 / 4611686018427387904 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1361129467683753853853498429727072845824 (by norm_num)
  have h2M : 2 * 1361129467683753853853498429727072845824 = 2722258935367507707706996859454145691648 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_1361129467683753853853498429727072845824_le
  linarith

/-- The `M = 1361129467683753853853498429727072845824` constant honestly improves on the banked
`M = 680564733841876926926749214863536422912` constant
(`3/4611686018427387904 < 24/26087635479112601600`). -/
theorem tail_1361129467683753853853498429727072845824_lt_680564733841876926926749214863536422912 : (3 / 4611686018427387904 : ℝ) < (24 / 26087635479112601600 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 2722258935367507707706996859454145691648` tail
(`52175270958225203200 ≤ 2722258935367507707706996859454145691648^{1/2}`; generic mirror of
`M680564733841876926926749214863536422912_rpow_ge` above and latest exact
`M1361129467683753853853498429727072845824_rpow_eq` above; honest floor via
`52175270958225203200^2 =
2722258899564218313725268047681290240000 ≤ 2722258935367507707706996859454145691648`
by `norm_num`; `2722258935367507707706996859454145691648 = 2^131` so root
`36893488147419103232·√2 ≈ 52175271301331128849.xx` is NOT exact, unlike
`1361129467683753853853498429727072845824`; conservative doubling of the
`26087635479112601600` floor below the true floor `52175271301331128849`;
lower gap `35803289393981728811772855451648`). -/
theorem M2722258935367507707706996859454145691648_rpow_ge :
    (52175270958225203200 : ℝ) ≤ ((((2722258935367507707706996859454145691648 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((52175270958225203200 : ℝ) ^ (2 : ℕ)) ≤ ((((2722258935367507707706996859454145691648 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((2722258935367507707706996859454145691648 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((2722258935367507707706996859454145691648 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 2722258935367507707706996859454145691648` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/52175270958225203200`; generic mirror of
`r_680564733841876926926749214863536422912_le` above and latest exact
`r_1361129467683753853853498429727072845824_le` above; decay recomputed honestly with
`norm_num` via `M2722258935367507707706996859454145691648_rpow_ge`; honest conservative
`T = 24/52175270958225203200` for the `52175270958225203200` root lower). -/
theorem r_2722258935367507707706996859454145691648_le :
    (12 : ℝ) * ((((((2722258935367507707706996859454145691648 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 52175270958225203200 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((2722258935367507707706996859454145691648 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((2722258935367507707706996859454145691648 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M2722258935367507707706996859454145691648_rpow_ge
  have hrw : ((((2722258935367507707706996859454145691648 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((2722258935367507707706996859454145691648 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((2722258935367507707706996859454145691648 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (52175270958225203200 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((2722258935367507707706996859454145691648 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (52175270958225203200 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((2722258935367507707706996859454145691648 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((52175270958225203200 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((52175270958225203200 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 52175270958225203200 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 2722258935367507707706996859454145691648`
(`‖G - S5444517870735015415413993718908291383296‖ ≤ 24/52175270958225203200`; generic mirror of
`eta_tail_680564733841876926926749214863536422912_le` above and latest exact
`eta_tail_1361129467683753853853498429727072845824_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_2722258935367507707706996859454145691648_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 2722258935367507707706996859454145691648), etaDirichletTerm s k)‖ ≤
      (24 / 52175270958225203200 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 2722258935367507707706996859454145691648 (by norm_num)
  have h2M : 2 * 2722258935367507707706996859454145691648 = 5444517870735015415413993718908291383296 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_2722258935367507707706996859454145691648_le
  linarith

/-- The `M = 2722258935367507707706996859454145691648` constant honestly improves on the banked
`M = 1361129467683753853853498429727072845824` constant
(`24/52175270958225203200 < 3/4611686018427387904`). -/
theorem tail_2722258935367507707706996859454145691648_lt_1361129467683753853853498429727072845824 : (24 / 52175270958225203200 : ℝ) < (3 / 4611686018427387904 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 5444517870735015415413993718908291383296` tail
(`5444517870735015415413993718908291383296^{1/2} = 73786976294838206464` exact; exact shape mirror of
`M1361129467683753853853498429727072845824_rpow_eq` above and latest odd-floor
`M2722258935367507707706996859454145691648_rpow_ge` above; honest via
`73786976294838206464^2 = 5444517870735015415413993718908291383296` by `norm_num`;
`5444517870735015415413993718908291383296 = 2^132` so the root is exact, unlike
`2722258935367507707706996859454145691648`). -/
theorem M5444517870735015415413993718908291383296_rpow_eq :
    ((((5444517870735015415413993718908291383296 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (73786976294838206464 : ℝ) := by
  have hx2 : ((((((5444517870735015415413993718908291383296 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((5444517870735015415413993718908291383296 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((73786976294838206464 : ℝ) ^ (2 : ℕ)) = ((((5444517870735015415413993718908291383296 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((5444517870735015415413993718908291383296 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (73786976294838206464 : ℝ) := by norm_num
  have hle1 : ((((((5444517870735015415413993718908291383296 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((73786976294838206464 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((73786976294838206464 : ℝ) ^ (2 : ℕ)) ≤
      ((((((5444517870735015415413993718908291383296 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 5444517870735015415413993718908291383296` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/73786976294838206464 = 3/9223372036854775808`; exact shape mirror of
`r_1361129467683753853853498429727072845824_le` above; decay recomputed honestly with
`norm_num` via the exact `M5444517870735015415413993718908291383296_rpow_eq`; tightest honest
`T = 3/9223372036854775808` for this root). -/
theorem r_5444517870735015415413993718908291383296_le :
    (12 : ℝ) * ((((((5444517870735015415413993718908291383296 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 9223372036854775808 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((5444517870735015415413993718908291383296 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M5444517870735015415413993718908291383296_rpow_eq
  have hrw : ((((5444517870735015415413993718908291383296 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((5444517870735015415413993718908291383296 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((73786976294838206464 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 9223372036854775808 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 5444517870735015415413993718908291383296`
(`‖G - S10889035741470030830827987437816582766592‖ ≤ 3/9223372036854775808`; exact shape mirror of
`eta_tail_1361129467683753853853498429727072845824_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_5444517870735015415413993718908291383296_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 5444517870735015415413993718908291383296), etaDirichletTerm s k)‖ ≤
      (3 / 9223372036854775808 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 5444517870735015415413993718908291383296 (by norm_num)
  have h2M : 2 * 5444517870735015415413993718908291383296 = 10889035741470030830827987437816582766592 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_5444517870735015415413993718908291383296_le
  linarith

/-- The `M = 5444517870735015415413993718908291383296` constant honestly improves on the banked
`M = 2722258935367507707706996859454145691648` constant
(`3/9223372036854775808 < 24/52175270958225203200`). -/
theorem tail_5444517870735015415413993718908291383296_lt_2722258935367507707706996859454145691648 : (3 / 9223372036854775808 : ℝ) < (24 / 52175270958225203200 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 10889035741470030830827987437816582766592` tail
(`104350541916450406400 ≤ 10889035741470030830827987437816582766592^{1/2}`; generic mirror of
`M2722258935367507707706996859454145691648_rpow_ge` above and latest exact
`M5444517870735015415413993718908291383296_rpow_eq` above; honest floor via
`104350541916450406400^2 =
10889035598256873254901072190725160960000 ≤ 10889035741470030830827987437816582766592`
by `norm_num`; `10889035741470030830827987437816582766592 = 2^133` so root
`73786976294838206464·√2 ≈ 104350542649578 hum` is NOT exact, unlike
`5444517870735015415413993718908291383296`; conservative doubling of the
`52175270958225203200` floor below the true floor `10435054264957820883`;
lower gap `143213157575926915247091421806592`). -/
theorem M10889035741470030830827987437816582766592_rpow_ge :
    (104350541916450406400 : ℝ) ≤ ((((10889035741470030830827987437816582766592 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((104350541916450406400 : ℝ) ^ (2 : ℕ)) ≤ ((((10889035741470030830827987437816582766592 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((10889035741470030830827987437816582766592 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((10889035741470030830827987437816582766592 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 10889035741470030830827987437816582766592` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/104350541916450406400`; generic mirror of
`r_2722258935367507707706996859454145691648_le` above and latest exact
`r_5444517870735015415413993718908291383296_le` above; decay recomputed honestly with
`norm_num` via `M10889035741470030830827987437816582766592_rpow_ge`; honest conservative
`T = 24/104350541916450406400` for the `104350541916450406400` root lower). -/
theorem r_10889035741470030830827987437816582766592_le :
    (12 : ℝ) * ((((((10889035741470030830827987437816582766592 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 104350541916450406400 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((10889035741470030830827987437816582766592 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((10889035741470030830827987437816582766592 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M10889035741470030830827987437816582766592_rpow_ge
  have hrw : ((((10889035741470030830827987437816582766592 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((10889035741470030830827987437816582766592 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((10889035741470030830827987437816582766592 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (104350541916450406400 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((10889035741470030830827987437816582766592 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (104350541916450406400 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((10889035741470030830827987437816582766592 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((104350541916450406400 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((104350541916450406400 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 104350541916450406400 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 10889035741470030830827987437816582766592`
(`‖G - S21778071482940061661655974875633165533184‖ ≤ 24/104350541916450406400`; generic mirror of
`eta_tail_2722258935367507707706996859454145691648_le` above and latest exact
`eta_tail_5444517870735015415413993718908291383296_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_10889035741470030830827987437816582766592_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 10889035741470030830827987437816582766592), etaDirichletTerm s k)‖ ≤
      (24 / 104350541916450406400 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 10889035741470030830827987437816582766592 (by norm_num)
  have h2M : 2 * 10889035741470030830827987437816582766592 = 21778071482940061661655974875633165533184 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_10889035741470030830827987437816582766592_le
  linarith

/-- The `M = 10889035741470030830827987437816582766592` constant honestly improves on the banked
`M = 5444517870735015415413993718908291383296` constant
(`24/104350541916450406400 < 3/9223372036854775808`). -/
theorem tail_10889035741470030830827987437816582766592_lt_5444517870735015415413993718908291383296 : (24 / 104350541916450406400 : ℝ) < (3 / 9223372036854775808 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 21778071482940061661655974875633165533184` tail
(`21778071482940061661655974875633165533184^{1/2} = 147573952589676412928` exact; exact shape mirror of
`M5444517870735015415413993718908291383296_rpow_eq` above and latest odd-floor
`M10889035741470030830827987437816582766592_rpow_ge` above; honest via
`147573952589676412928^2 = 21778071482940061661655974875633165533184` by `norm_num`;
`21778071482940061661655974875633165533184 = 2^134` so the root is exact, unlike
`10889035741470030830827987437816582766592`). -/
theorem M21778071482940061661655974875633165533184_rpow_eq :
    ((((21778071482940061661655974875633165533184 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (147573952589676412928 : ℝ) := by
  have hx2 : ((((((21778071482940061661655974875633165533184 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((21778071482940061661655974875633165533184 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((147573952589676412928 : ℝ) ^ (2 : ℕ)) = ((((21778071482940061661655974875633165533184 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((21778071482940061661655974875633165533184 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (147573952589676412928 : ℝ) := by norm_num
  have hle1 : ((((((21778071482940061661655974875633165533184 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((147573952589676412928 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((147573952589676412928 : ℝ) ^ (2 : ℕ)) ≤
      ((((((21778071482940061661655974875633165533184 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 21778071482940061661655974875633165533184` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/147573952589676412928 = 3/18446744073709551616`; exact shape mirror of
`r_5444517870735015415413993718908291383296_le` above; decay recomputed honestly with
`norm_num` via the exact `M21778071482940061661655974875633165533184_rpow_eq`; tightest honest
`T = 3/18446744073709551616` for this root). -/
theorem r_21778071482940061661655974875633165533184_le :
    (12 : ℝ) * ((((((21778071482940061661655974875633165533184 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 18446744073709551616 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((21778071482940061661655974875633165533184 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M21778071482940061661655974875633165533184_rpow_eq
  have hrw : ((((21778071482940061661655974875633165533184 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((21778071482940061661655974875633165533184 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((147573952589676412928 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 18446744073709551616 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 21778071482940061661655974875633165533184`
(`‖G - S43556142965880123323311949751266331066368‖ ≤ 3/18446744073709551616`; exact shape mirror of
`eta_tail_5444517870735015415413993718908291383296_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_21778071482940061661655974875633165533184_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 21778071482940061661655974875633165533184), etaDirichletTerm s k)‖ ≤
      (3 / 18446744073709551616 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 21778071482940061661655974875633165533184 (by norm_num)
  have h2M : 2 * 21778071482940061661655974875633165533184 = 43556142965880123323311949751266331066368 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_21778071482940061661655974875633165533184_le
  linarith

/-- The `M = 21778071482940061661655974875633165533184` constant honestly improves on the banked
`M = 10889035741470030830827987437816582766592` constant
(`3/18446744073709551616 < 24/104350541916450406400`). -/
theorem tail_21778071482940061661655974875633165533184_lt_10889035741470030830827987437816582766592 : (3 / 18446744073709551616 : ℝ) < (24 / 104350541916450406400 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 43556142965880123323311949751266331066368` tail
(`208701083832900812800 ≤ 43556142965880123323311949751266331066368^{1/2}`; generic mirror of
`M10889035741470030830827987437816582766592_rpow_ge` above and latest exact
`M21778071482940061661655974875633165533184_rpow_eq` above; honest floor via
`208701083832900812800^2 = 43556142393027493019604288762900643840000 ≤
43556142965880123323311949751266331066368` by `norm_num`;
`43556142965880123323311949751266331066368 = 2^135` so root `147573952589676412928·√2 ≈
208701085205324515397` is NOT exact, unlike `21778071482940061661655974875633165533184`;
conservative doubling `2 * 104350541916450406400 = 208701083832900812800` below the true floor
`208701085205324515397`; lower gap `572852630303707660988365687226368`). -/
theorem M43556142965880123323311949751266331066368_rpow_ge :
    (208701083832900812800 : ℝ) ≤ ((((43556142965880123323311949751266331066368 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((208701083832900812800 : ℝ) ^ (2 : ℕ)) ≤ ((((43556142965880123323311949751266331066368 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((43556142965880123323311949751266331066368 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((43556142965880123323311949751266331066368 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 43556142965880123323311949751266331066368` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/208701083832900812800`; generic mirror of
`r_10889035741470030830827987437816582766592_le` above and latest exact
`r_21778071482940061661655974875633165533184_le` above; decay recomputed honestly with
`norm_num` via `M43556142965880123323311949751266331066368_rpow_ge`; honest conservative
`T = 24/208701083832900812800` for the `208701083832900812800` root lower). -/
theorem r_43556142965880123323311949751266331066368_le :
    (12 : ℝ) * ((((((43556142965880123323311949751266331066368 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 208701083832900812800 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((43556142965880123323311949751266331066368 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((43556142965880123323311949751266331066368 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M43556142965880123323311949751266331066368_rpow_ge
  have hrw : ((((43556142965880123323311949751266331066368 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((43556142965880123323311949751266331066368 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((43556142965880123323311949751266331066368 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (208701083832900812800 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((43556142965880123323311949751266331066368 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (208701083832900812800 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((43556142965880123323311949751266331066368 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((208701083832900812800 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((208701083832900812800 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 208701083832900812800 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 43556142965880123323311949751266331066368`
(`‖G - S87112285931760246646623899502532662132736‖ ≤ 24/208701083832900812800`; generic mirror of
`eta_tail_10889035741470030830827987437816582766592_le` above and latest exact
`eta_tail_21778071482940061661655974875633165533184_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_43556142965880123323311949751266331066368_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 43556142965880123323311949751266331066368), etaDirichletTerm s k)‖ ≤
      (24 / 208701083832900812800 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 43556142965880123323311949751266331066368 (by norm_num)
  have h2M : 2 * 43556142965880123323311949751266331066368 = 87112285931760246646623899502532662132736 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_43556142965880123323311949751266331066368_le
  linarith

/-- The `M = 43556142965880123323311949751266331066368` constant honestly improves on the banked
`M = 21778071482940061661655974875633165533184` constant
(`24/208701083832900812800 < 3/18446744073709551616`). -/
theorem tail_43556142965880123323311949751266331066368_lt_21778071482940061661655974875633165533184 : (24 / 208701083832900812800 : ℝ) < (3 / 18446744073709551616 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 87112285931760246646623899502532662132736` tail
(`87112285931760246646623899502532662132736^{1/2} = 295147905179352825856` exact; exact shape mirror of
`M21778071482940061661655974875633165533184_rpow_eq` above and latest odd-floor
`M43556142965880123323311949751266331066368_rpow_ge` above; honest via
`295147905179352825856^2 = 87112285931760246646623899502532662132736` by `norm_num`;
`87112285931760246646623899502532662132736 = 2^136` so the root is exact, unlike
`43556142965880123323311949751266331066368`). -/
theorem M87112285931760246646623899502532662132736_rpow_eq :
    ((((87112285931760246646623899502532662132736 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (295147905179352825856 : ℝ) := by
  have hx2 : ((((((87112285931760246646623899502532662132736 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((87112285931760246646623899502532662132736 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((295147905179352825856 : ℝ) ^ (2 : ℕ)) = ((((87112285931760246646623899502532662132736 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((87112285931760246646623899502532662132736 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (295147905179352825856 : ℝ) := by norm_num
  have hle1 : ((((((87112285931760246646623899502532662132736 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((295147905179352825856 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((295147905179352825856 : ℝ) ^ (2 : ℕ)) ≤
      ((((((87112285931760246646623899502532662132736 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 87112285931760246646623899502532662132736` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/295147905179352825856 = 3/36893488147419103232`; exact shape mirror of
`r_21778071482940061661655974875633165533184_le` above; decay recomputed honestly with
`norm_num` via the exact `M87112285931760246646623899502532662132736_rpow_eq`; tightest honest
`T = 3/36893488147419103232` for this root). -/
theorem r_87112285931760246646623899502532662132736_le :
    (12 : ℝ) * ((((((87112285931760246646623899502532662132736 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 36893488147419103232 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((87112285931760246646623899502532662132736 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M87112285931760246646623899502532662132736_rpow_eq
  have hrw : ((((87112285931760246646623899502532662132736 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((87112285931760246646623899502532662132736 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((295147905179352825856 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 36893488147419103232 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 87112285931760246646623899502532662132736`
(`‖G - S174224571863520493293247799005065324265472‖ ≤ 3/36893488147419103232`; exact shape mirror of
`eta_tail_21778071482940061661655974875633165533184_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_87112285931760246646623899502532662132736_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 87112285931760246646623899502532662132736), etaDirichletTerm s k)‖ ≤
      (3 / 36893488147419103232 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 87112285931760246646623899502532662132736 (by norm_num)
  have h2M : 2 * 87112285931760246646623899502532662132736 = 174224571863520493293247799005065324265472 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_87112285931760246646623899502532662132736_le
  linarith

/-- The `M = 87112285931760246646623899502532662132736` constant honestly improves on the banked
`M = 43556142965880123323311949751266331066368` constant
(`3/36893488147419103232 < 24/208701083832900812800`). -/
theorem tail_87112285931760246646623899502532662132736_lt_43556142965880123323311949751266331066368 : (3 / 36893488147419103232 : ℝ) < (24 / 208701083832900812800 : ℝ) := by
  norm_num

end Door3TailEtaUpper


namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 174224571863520493293247799005065324265472` tail
(`417402167665801625600 ≤ 174224571863520493293247799005065324265472^{1/2}`; generic mirror of
`M43556142965880123323311949751266331066368_rpow_ge` above and latest exact
`M87112285931760246646623899502532662132736_rpow_eq` above; honest floor via
`417402167665801625600^2 = 174224569572109972078417155051602575360000 ≤
174224571863520493293247799005065324265472` by `norm_num`;
`174224571863520493293247799005065324265472 = 2^137` so root `295147905179352825856·√2 ≈
417402170410649030795` is NOT exact, unlike `87112285931760246646623899502532662132736`;
conservative doubling `2 * 208701083832900812800 = 417402167665801625600` below the true floor
`417402170410649030795`; lower gap `2291410521214830643953462748905472`). -/
theorem M174224571863520493293247799005065324265472_rpow_ge :
    (417402167665801625600 : ℝ) ≤ ((((174224571863520493293247799005065324265472 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((417402167665801625600 : ℝ) ^ (2 : ℕ)) ≤ ((((174224571863520493293247799005065324265472 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((174224571863520493293247799005065324265472 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((174224571863520493293247799005065324265472 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 174224571863520493293247799005065324265472` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/417402167665801625600`; generic mirror of
`r_43556142965880123323311949751266331066368_le` above and latest exact
`r_87112285931760246646623899502532662132736_le` above; decay recomputed honestly with
`norm_num` via `M174224571863520493293247799005065324265472_rpow_ge`; honest conservative
`T = 24/417402167665801625600` for the `417402167665801625600` root lower). -/
theorem r_174224571863520493293247799005065324265472_le :
    (12 : ℝ) * ((((((174224571863520493293247799005065324265472 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 417402167665801625600 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((174224571863520493293247799005065324265472 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((174224571863520493293247799005065324265472 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M174224571863520493293247799005065324265472_rpow_ge
  have hrw : ((((174224571863520493293247799005065324265472 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((174224571863520493293247799005065324265472 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((174224571863520493293247799005065324265472 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (417402167665801625600 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((174224571863520493293247799005065324265472 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (417402167665801625600 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((174224571863520493293247799005065324265472 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((417402167665801625600 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((417402167665801625600 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 417402167665801625600 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 174224571863520493293247799005065324265472`
(`‖G - S348449143727040986586495598010130648530944‖ ≤ 24/417402167665801625600`; generic mirror of
`eta_tail_43556142965880123323311949751266331066368_le` above and latest exact
`eta_tail_87112285931760246646623899502532662132736_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_174224571863520493293247799005065324265472_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 174224571863520493293247799005065324265472), etaDirichletTerm s k)‖ ≤
      (24 / 417402167665801625600 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 174224571863520493293247799005065324265472 (by norm_num)
  have h2M : 2 * 174224571863520493293247799005065324265472 = 348449143727040986586495598010130648530944 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_174224571863520493293247799005065324265472_le
  linarith

/-- The `M = 174224571863520493293247799005065324265472` constant honestly improves on the banked
`M = 87112285931760246646623899502532662132736` constant
(`24/417402167665801625600 < 3/36893488147419103232`). -/
theorem tail_174224571863520493293247799005065324265472_lt_87112285931760246646623899502532662132736 : (24 / 417402167665801625600 : ℝ) < (3 / 36893488147419103232 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 348449143727040986586495598010130648530944` tail
(`348449143727040986586495598010130648530944^{1/2} = 590295810358705651712` exact; exact shape mirror of
`M87112285931760246646623899502532662132736_rpow_eq` above and latest odd-floor
`M174224571863520493293247799005065324265472_rpow_ge` above; honest via
`590295810358705651712^2 = 348449143727040986586495598010130648530944` by `norm_num`;
`348449143727040986586495598010130648530944 = 2^138` so the root is exact, unlike
`174224571863520493293247799005065324265472`). -/
theorem M348449143727040986586495598010130648530944_rpow_eq :
    ((((348449143727040986586495598010130648530944 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (590295810358705651712 : ℝ) := by
  have hx2 : ((((((348449143727040986586495598010130648530944 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((348449143727040986586495598010130648530944 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((590295810358705651712 : ℝ) ^ (2 : ℕ)) = ((((348449143727040986586495598010130648530944 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((348449143727040986586495598010130648530944 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (590295810358705651712 : ℝ) := by norm_num
  have hle1 : ((((((348449143727040986586495598010130648530944 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((590295810358705651712 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((590295810358705651712 : ℝ) ^ (2 : ℕ)) ≤
      ((((((348449143727040986586495598010130648530944 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 348449143727040986586495598010130648530944` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/590295810358705651712 = 3/73786976294838206464`; exact shape mirror of
`r_87112285931760246646623899502532662132736_le` above; decay recomputed honestly with
`norm_num` via the exact `M348449143727040986586495598010130648530944_rpow_eq`; tightest honest
`T = 3/73786976294838206464` for this root). -/
theorem r_348449143727040986586495598010130648530944_le :
    (12 : ℝ) * ((((((348449143727040986586495598010130648530944 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 73786976294838206464 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((348449143727040986586495598010130648530944 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M348449143727040986586495598010130648530944_rpow_eq
  have hrw : ((((348449143727040986586495598010130648530944 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((348449143727040986586495598010130648530944 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((590295810358705651712 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 73786976294838206464 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 348449143727040986586495598010130648530944`
(`‖G - S696898287454081973172991196020261297061888‖ ≤ 3/73786976294838206464`; exact shape mirror of
`eta_tail_87112285931760246646623899502532662132736_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_348449143727040986586495598010130648530944_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 348449143727040986586495598010130648530944), etaDirichletTerm s k)‖ ≤
      (3 / 73786976294838206464 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 348449143727040986586495598010130648530944 (by norm_num)
  have h2M : 2 * 348449143727040986586495598010130648530944 = 696898287454081973172991196020261297061888 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_348449143727040986586495598010130648530944_le
  linarith

/-- The `M = 348449143727040986586495598010130648530944` constant honestly improves on the banked
`M = 174224571863520493293247799005065324265472` constant
(`3/73786976294838206464 < 24/417402167665801625600`). -/
theorem tail_348449143727040986586495598010130648530944_lt_174224571863520493293247799005065324265472 : (3 / 73786976294838206464 : ℝ) < (24 / 417402167665801625600 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 696898287454081973172991196020261297061888` tail
(`834804335331603251200 ≤ 696898287454081973172991196020261297061888^{1/2}`; generic mirror of
`M174224571863520493293247799005065324265472_rpow_ge` above and latest exact
`M348449143727040986586495598010130648530944_rpow_eq` above; honest floor via
`834804335331603251200^2 = 696898278288439888313668620206410301440000 ≤
696898287454081973172991196020261297061888` by `norm_num`;
`696898287454081973172991196020261297061888 = 2^139` so root `590295810358705651712·√2 ≈
834804340821298061590` is NOT exact, unlike `348449143727040986586495598010130648530944`;
conservative doubling `2 * 417402167665801625600 = 834804335331603251200` below the true floor
`834804340821298061590`; lower gap `9165642084859322575813850995621888`). -/
theorem M696898287454081973172991196020261297061888_rpow_ge :
    (834804335331603251200 : ℝ) ≤ ((((696898287454081973172991196020261297061888 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((834804335331603251200 : ℝ) ^ (2 : ℕ)) ≤ ((((696898287454081973172991196020261297061888 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((696898287454081973172991196020261297061888 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((696898287454081973172991196020261297061888 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 696898287454081973172991196020261297061888` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/834804335331603251200`; generic mirror of
`r_174224571863520493293247799005065324265472_le` above and latest exact
`r_348449143727040986586495598010130648530944_le` above; decay recomputed honestly with
`norm_num` via `M696898287454081973172991196020261297061888_rpow_ge`; honest conservative
`T = 24/834804335331603251200` for the `834804335331603251200` root lower). -/
theorem r_696898287454081973172991196020261297061888_le :
    (12 : ℝ) * ((((((696898287454081973172991196020261297061888 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 834804335331603251200 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((696898287454081973172991196020261297061888 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((696898287454081973172991196020261297061888 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M696898287454081973172991196020261297061888_rpow_ge
  have hrw : ((((696898287454081973172991196020261297061888 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((696898287454081973172991196020261297061888 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((696898287454081973172991196020261297061888 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (834804335331603251200 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((696898287454081973172991196020261297061888 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (834804335331603251200 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((696898287454081973172991196020261297061888 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((834804335331603251200 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((834804335331603251200 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 834804335331603251200 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 696898287454081973172991196020261297061888`
(`‖G - S1393796574908163946345982392040522594123776‖ ≤ 24/834804335331603251200`; generic mirror of
`eta_tail_174224571863520493293247799005065324265472_le` above and latest exact
`eta_tail_348449143727040986586495598010130648530944_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_696898287454081973172991196020261297061888_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 696898287454081973172991196020261297061888), etaDirichletTerm s k)‖ ≤
      (24 / 834804335331603251200 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 696898287454081973172991196020261297061888 (by norm_num)
  have h2M : 2 * 696898287454081973172991196020261297061888 = 1393796574908163946345982392040522594123776 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_696898287454081973172991196020261297061888_le
  linarith

/-- The `M = 696898287454081973172991196020261297061888` constant honestly improves on the banked
`M = 348449143727040986586495598010130648530944` constant
(`24/834804335331603251200 < 3/73786976294838206464`). -/
theorem tail_696898287454081973172991196020261297061888_lt_348449143727040986586495598010130648530944 : (24 / 834804335331603251200 : ℝ) < (3 / 73786976294838206464 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 1393796574908163946345982392040522594123776` tail
(`1393796574908163946345982392040522594123776^{1/2} = 1180591620717411303424` exact; exact shape mirror of
`M348449143727040986586495598010130648530944_rpow_eq` above and latest odd-floor
`M696898287454081973172991196020261297061888_rpow_ge` above; honest via
`1180591620717411303424^2 = 1393796574908163946345982392040522594123776` by `norm_num`;
`1393796574908163946345982392040522594123776 = 2^140` so the root is exact, unlike
`696898287454081973172991196020261297061888`). -/
theorem M1393796574908163946345982392040522594123776_rpow_eq :
    ((((1393796574908163946345982392040522594123776 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (1180591620717411303424 : ℝ) := by
  have hx2 : ((((((1393796574908163946345982392040522594123776 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((1393796574908163946345982392040522594123776 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((1180591620717411303424 : ℝ) ^ (2 : ℕ)) = ((((1393796574908163946345982392040522594123776 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((1393796574908163946345982392040522594123776 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (1180591620717411303424 : ℝ) := by norm_num
  have hle1 : ((((((1393796574908163946345982392040522594123776 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((1180591620717411303424 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((1180591620717411303424 : ℝ) ^ (2 : ℕ)) ≤
      ((((((1393796574908163946345982392040522594123776 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 1393796574908163946345982392040522594123776` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/1180591620717411303424 = 3/147573952589676412928`; exact shape mirror of
`r_348449143727040986586495598010130648530944_le` above; decay recomputed honestly with
`norm_num` via the exact `M1393796574908163946345982392040522594123776_rpow_eq`; tightest honest
`T = 3/147573952589676412928` for this root). -/
theorem r_1393796574908163946345982392040522594123776_le :
    (12 : ℝ) * ((((((1393796574908163946345982392040522594123776 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 147573952589676412928 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((1393796574908163946345982392040522594123776 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M1393796574908163946345982392040522594123776_rpow_eq
  have hrw : ((((1393796574908163946345982392040522594123776 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((1393796574908163946345982392040522594123776 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((1180591620717411303424 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 147573952589676412928 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 1393796574908163946345982392040522594123776`
(`‖G - S2787593149816327892691964784081045188247552‖ ≤ 3/147573952589676412928`; exact shape mirror of
`eta_tail_348449143727040986586495598010130648530944_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_1393796574908163946345982392040522594123776_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 1393796574908163946345982392040522594123776), etaDirichletTerm s k)‖ ≤
      (3 / 147573952589676412928 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1393796574908163946345982392040522594123776 (by norm_num)
  have h2M : 2 * 1393796574908163946345982392040522594123776 = 2787593149816327892691964784081045188247552 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_1393796574908163946345982392040522594123776_le
  linarith

/-- The `M = 1393796574908163946345982392040522594123776` constant honestly improves on the banked
`M = 696898287454081973172991196020261297061888` constant
(`3/147573952589676412928 < 24/834804335331603251200`). -/
theorem tail_1393796574908163946345982392040522594123776_lt_696898287454081973172991196020261297061888 : (3 / 147573952589676412928 : ℝ) < (24 / 834804335331603251200 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 2787593149816327892691964784081045188247552` tail
(`1669608670663206502400 ≤ 2787593149816327892691964784081045188247552^{1/2}`; generic mirror of
`M696898287454081973172991196020261297061888_rpow_ge` above and latest exact
`M1393796574908163946345982392040522594123776_rpow_eq` above; honest floor via
`1669608670663206502400^2 = 2787593113153759553254674480825641205760000 ≤
2787593149816327892691964784081045188247552` by `norm_num`;
`2787593149816327892691964784081045188247552 = 2^141` so root `1180591620717411303424·√2 ≈
1669608681642596123180` is NOT exact, unlike `1393796574908163946345982392040522594123776`;
conservative doubling `2 * 834804335331603251200 = 1669608670663206502400` below the true floor
`1669608681642596123180`; lower gap `36662568339437290303255403982487552`). -/
theorem M2787593149816327892691964784081045188247552_rpow_ge :
    (1669608670663206502400 : ℝ) ≤ ((((2787593149816327892691964784081045188247552 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((1669608670663206502400 : ℝ) ^ (2 : ℕ)) ≤ ((((2787593149816327892691964784081045188247552 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((2787593149816327892691964784081045188247552 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((2787593149816327892691964784081045188247552 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 2787593149816327892691964784081045188247552` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/1669608670663206502400`; generic mirror of
`r_696898287454081973172991196020261297061888_le` above and latest exact
`r_1393796574908163946345982392040522594123776_le` above; decay recomputed honestly with
`norm_num` via `M2787593149816327892691964784081045188247552_rpow_ge`; honest conservative
`T = 24/1669608670663206502400` for the `1669608670663206502400` root lower). -/
theorem r_2787593149816327892691964784081045188247552_le :
    (12 : ℝ) * ((((((2787593149816327892691964784081045188247552 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 1669608670663206502400 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((2787593149816327892691964784081045188247552 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((2787593149816327892691964784081045188247552 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M2787593149816327892691964784081045188247552_rpow_ge
  have hrw : ((((2787593149816327892691964784081045188247552 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((2787593149816327892691964784081045188247552 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((2787593149816327892691964784081045188247552 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (1669608670663206502400 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((2787593149816327892691964784081045188247552 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (1669608670663206502400 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((2787593149816327892691964784081045188247552 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((1669608670663206502400 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((1669608670663206502400 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 1669608670663206502400 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 2787593149816327892691964784081045188247552`
(`‖G - S5575186299632655785383929568162090376495104‖ ≤ 24/1669608670663206502400`; generic mirror of
`eta_tail_696898287454081973172991196020261297061888_le` above and latest exact
`eta_tail_1393796574908163946345982392040522594123776_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_2787593149816327892691964784081045188247552_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 2787593149816327892691964784081045188247552), etaDirichletTerm s k)‖ ≤
      (24 / 1669608670663206502400 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 2787593149816327892691964784081045188247552 (by norm_num)
  have h2M : 2 * 2787593149816327892691964784081045188247552 = 5575186299632655785383929568162090376495104 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_2787593149816327892691964784081045188247552_le
  linarith

/-- The `M = 2787593149816327892691964784081045188247552` constant honestly improves on the banked
`M = 1393796574908163946345982392040522594123776` constant
(`24/1669608670663206502400 < 3/147573952589676412928`). -/
theorem tail_2787593149816327892691964784081045188247552_lt_1393796574908163946345982392040522594123776 : (24 / 1669608670663206502400 : ℝ) < (3 / 147573952589676412928 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 5575186299632655785383929568162090376495104` tail
(`5575186299632655785383929568162090376495104^{1/2} = 2361183241434822606848` exact; exact shape mirror of
`M1393796574908163946345982392040522594123776_rpow_eq` above and latest odd-floor
`M2787593149816327892691964784081045188247552_rpow_ge` above; honest via
`2361183241434822606848^2 = 5575186299632655785383929568162090376495104` by `norm_num`;
`5575186299632655785383929568162090376495104 = 2^142` so the root is exact, unlike
`2787593149816327892691964784081045188247552`). -/
theorem M5575186299632655785383929568162090376495104_rpow_eq :
    ((((5575186299632655785383929568162090376495104 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (2361183241434822606848 : ℝ) := by
  have hx2 : ((((((5575186299632655785383929568162090376495104 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((5575186299632655785383929568162090376495104 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((2361183241434822606848 : ℝ) ^ (2 : ℕ)) = ((((5575186299632655785383929568162090376495104 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((5575186299632655785383929568162090376495104 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (2361183241434822606848 : ℝ) := by norm_num
  have hle1 : ((((((5575186299632655785383929568162090376495104 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((2361183241434822606848 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((2361183241434822606848 : ℝ) ^ (2 : ℕ)) ≤
      ((((((5575186299632655785383929568162090376495104 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 5575186299632655785383929568162090376495104` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/2361183241434822606848 = 3/295147905179352825856`; exact shape mirror of
`r_1393796574908163946345982392040522594123776_le` above; decay recomputed honestly with
`norm_num` via the exact `M5575186299632655785383929568162090376495104_rpow_eq`; tightest honest
`T = 3/295147905179352825856` for this root). -/
theorem r_5575186299632655785383929568162090376495104_le :
    (12 : ℝ) * ((((((5575186299632655785383929568162090376495104 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 295147905179352825856 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((5575186299632655785383929568162090376495104 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M5575186299632655785383929568162090376495104_rpow_eq
  have hrw : ((((5575186299632655785383929568162090376495104 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((5575186299632655785383929568162090376495104 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((2361183241434822606848 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 295147905179352825856 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 5575186299632655785383929568162090376495104`
(`‖G - S11150372599265311570767859136324180752990208‖ ≤ 3/295147905179352825856`; exact shape mirror of
`eta_tail_1393796574908163946345982392040522594123776_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_5575186299632655785383929568162090376495104_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 5575186299632655785383929568162090376495104), etaDirichletTerm s k)‖ ≤
      (3 / 295147905179352825856 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 5575186299632655785383929568162090376495104 (by norm_num)
  have h2M : 2 * 5575186299632655785383929568162090376495104 = 11150372599265311570767859136324180752990208 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_5575186299632655785383929568162090376495104_le
  linarith

/-- The `M = 5575186299632655785383929568162090376495104` constant honestly improves on the banked
`M = 2787593149816327892691964784081045188247552` constant
(`3/295147905179352825856 < 24/1669608670663206502400`). -/
theorem tail_5575186299632655785383929568162090376495104_lt_2787593149816327892691964784081045188247552 : (3 / 295147905179352825856 : ℝ) < (24 / 1669608670663206502400 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 11150372599265311570767859136324180752990208` tail
(`3339217341326413004800 ≤ 11150372599265311570767859136324180752990208^{1/2}`; generic mirror of
`M2787593149816327892691964784081045188247552_rpow_ge` above and latest exact
`M5575186299632655785383929568162090376495104_rpow_eq` above; honest floor via
`3339217341326413004800^2 = 11150372452615038213018697923302564823040000 ≤
11150372599265311570767859136324180752990208` by `norm_num`;
`11150372599265311570767859136324180752990208 = 2^143` so root `2361183241434822606848·√2 ≈
3339217363285192246361` is NOT exact, unlike `5575186299632655785383929568162090376495104`;
conservative doubling `2 * 1669608670663206502400 = 3339217341326413004800` below the true floor
`3339217363285192246361`; lower gap `146650273357749161213021615929950208`). -/
theorem M11150372599265311570767859136324180752990208_rpow_ge :
    (3339217341326413004800 : ℝ) ≤ ((((11150372599265311570767859136324180752990208 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((3339217341326413004800 : ℝ) ^ (2 : ℕ)) ≤ ((((11150372599265311570767859136324180752990208 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((11150372599265311570767859136324180752990208 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((11150372599265311570767859136324180752990208 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 11150372599265311570767859136324180752990208` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/3339217341326413004800`; generic mirror of
`r_2787593149816327892691964784081045188247552_le` above and latest exact
`r_5575186299632655785383929568162090376495104_le` above; decay recomputed honestly with
`norm_num` via `M11150372599265311570767859136324180752990208_rpow_ge`; honest conservative
`T = 24/3339217341326413004800` for the `3339217341326413004800` root lower). -/
theorem r_11150372599265311570767859136324180752990208_le :
    (12 : ℝ) * ((((((11150372599265311570767859136324180752990208 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 3339217341326413004800 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((11150372599265311570767859136324180752990208 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((11150372599265311570767859136324180752990208 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M11150372599265311570767859136324180752990208_rpow_ge
  have hrw : ((((11150372599265311570767859136324180752990208 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((11150372599265311570767859136324180752990208 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((11150372599265311570767859136324180752990208 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (3339217341326413004800 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((11150372599265311570767859136324180752990208 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (3339217341326413004800 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((11150372599265311570767859136324180752990208 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((3339217341326413004800 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((3339217341326413004800 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 3339217341326413004800 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 11150372599265311570767859136324180752990208`
(`‖G - S22300745198530623141535718272648361505980416‖ ≤ 24/3339217341326413004800`; generic mirror of
`eta_tail_2787593149816327892691964784081045188247552_le` above and latest exact
`eta_tail_5575186299632655785383929568162090376495104_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_11150372599265311570767859136324180752990208_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 11150372599265311570767859136324180752990208), etaDirichletTerm s k)‖ ≤
      (24 / 3339217341326413004800 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 11150372599265311570767859136324180752990208 (by norm_num)
  have h2M : 2 * 11150372599265311570767859136324180752990208 = 22300745198530623141535718272648361505980416 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_11150372599265311570767859136324180752990208_le
  linarith

/-- The `M = 11150372599265311570767859136324180752990208` constant honestly improves on the banked
`M = 5575186299632655785383929568162090376495104` constant
(`24/3339217341326413004800 < 3/295147905179352825856`). -/
theorem tail_11150372599265311570767859136324180752990208_lt_5575186299632655785383929568162090376495104 : (24 / 3339217341326413004800 : ℝ) < (3 / 295147905179352825856 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 22300745198530623141535718272648361505980416` tail
(`22300745198530623141535718272648361505980416^{1/2} = 4722366482869645213696` exact; exact shape mirror of
`M5575186299632655785383929568162090376495104_rpow_eq` above and latest odd-floor
`M11150372599265311570767859136324180752990208_rpow_ge` above; honest via
`4722366482869645213696^2 = 22300745198530623141535718272648361505980416` by `norm_num`;
`22300745198530623141535718272648361505980416 = 2^144` so the root is exact, unlike
`11150372599265311570767859136324180752990208`). -/
theorem M22300745198530623141535718272648361505980416_rpow_eq :
    ((((22300745198530623141535718272648361505980416 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (4722366482869645213696 : ℝ) := by
  have hx2 : ((((((22300745198530623141535718272648361505980416 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((22300745198530623141535718272648361505980416 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((4722366482869645213696 : ℝ) ^ (2 : ℕ)) = ((((22300745198530623141535718272648361505980416 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((22300745198530623141535718272648361505980416 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (4722366482869645213696 : ℝ) := by norm_num
  have hle1 : ((((((22300745198530623141535718272648361505980416 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((4722366482869645213696 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((4722366482869645213696 : ℝ) ^ (2 : ℕ)) ≤
      ((((((22300745198530623141535718272648361505980416 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 22300745198530623141535718272648361505980416` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/4722366482869645213696 = 3/590295810358705651712`; exact shape mirror of
`r_5575186299632655785383929568162090376495104_le` above; decay recomputed honestly with
`norm_num` via the exact `M22300745198530623141535718272648361505980416_rpow_eq`; tightest honest
`T = 3/590295810358705651712` for this root). -/
theorem r_22300745198530623141535718272648361505980416_le :
    (12 : ℝ) * ((((((22300745198530623141535718272648361505980416 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 590295810358705651712 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((22300745198530623141535718272648361505980416 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M22300745198530623141535718272648361505980416_rpow_eq
  have hrw : ((((22300745198530623141535718272648361505980416 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((22300745198530623141535718272648361505980416 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((4722366482869645213696 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 590295810358705651712 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 22300745198530623141535718272648361505980416`
(`‖G - S44601490397061246283071436545296723011960832‖ ≤ 3/590295810358705651712`; exact shape mirror of
`eta_tail_5575186299632655785383929568162090376495104_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_22300745198530623141535718272648361505980416_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 22300745198530623141535718272648361505980416), etaDirichletTerm s k)‖ ≤
      (3 / 590295810358705651712 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 22300745198530623141535718272648361505980416 (by norm_num)
  have h2M : 2 * 22300745198530623141535718272648361505980416 = 44601490397061246283071436545296723011960832 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_22300745198530623141535718272648361505980416_le
  linarith

/-- The `M = 22300745198530623141535718272648361505980416` constant honestly improves on the banked
`M = 11150372599265311570767859136324180752990208` constant
(`3/590295810358705651712 < 24/3339217341326413004800`). -/
theorem tail_22300745198530623141535718272648361505980416_lt_11150372599265311570767859136324180752990208 : (3 / 590295810358705651712 : ℝ) < (24 / 3339217341326413004800 : ℝ) := by
  norm_num

end Door3TailEtaUpper
namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 44601490397061246283071436545296723011960832` tail
(`6678434682652826009600 ≤ 44601490397061246283071436545296723011960832^{1/2}`;
generic mirror of `M11150372599265311570767859136324180752990208_rpow_ge` above and latest exact
`M22300745198530623141535718272648361505980416_rpow_eq` above; honest floor via
`6678434682652826009600^2 = 44601489810460152852074791693210259292160000 ≤
44601490397061246283071436545296723011960832` by `norm_num`;
`44601490397061246283071436545296723011960832 = 2^145` so root `4722366482869645213696·√2 ≈
6678434726570384492722` is NOT exact, unlike `22300745198530623141535718272648361505980416`;
conservative doubling `2 * 3339217341326413004800 = 6678434682652826009600` below the true floor
`6678434726570384492722`; lower gap `586601093430996644852086463719800832`). -/
theorem M44601490397061246283071436545296723011960832_rpow_ge :
    (6678434682652826009600 : ℝ) ≤ ((((44601490397061246283071436545296723011960832 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((6678434682652826009600 : ℝ) ^ (2 : ℕ)) ≤ ((((44601490397061246283071436545296723011960832 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((44601490397061246283071436545296723011960832 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((44601490397061246283071436545296723011960832 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 44601490397061246283071436545296723011960832` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/6678434682652826009600`; generic mirror of
`r_11150372599265311570767859136324180752990208_le` above and latest exact
`r_22300745198530623141535718272648361505980416_le` above; decay recomputed honestly with
`norm_num` via `M44601490397061246283071436545296723011960832_rpow_ge`; honest conservative
`T = 24/6678434682652826009600` for the `6678434682652826009600` root lower). -/
theorem r_44601490397061246283071436545296723011960832_le :
    (12 : ℝ) * ((((((44601490397061246283071436545296723011960832 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 6678434682652826009600 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((44601490397061246283071436545296723011960832 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((44601490397061246283071436545296723011960832 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M44601490397061246283071436545296723011960832_rpow_ge
  have hrw : ((((44601490397061246283071436545296723011960832 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((44601490397061246283071436545296723011960832 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((44601490397061246283071436545296723011960832 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (6678434682652826009600 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((44601490397061246283071436545296723011960832 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (6678434682652826009600 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((44601490397061246283071436545296723011960832 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((6678434682652826009600 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((6678434682652826009600 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 6678434682652826009600 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 44601490397061246283071436545296723011960832`
(`‖G - S89202980794122492566142873090593446023921664‖ ≤ 24/6678434682652826009600`; generic mirror of
`eta_tail_11150372599265311570767859136324180752990208_le` above and latest exact
`eta_tail_22300745198530623141535718272648361505980416_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_44601490397061246283071436545296723011960832_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 44601490397061246283071436545296723011960832), etaDirichletTerm s k)‖ ≤
      (24 / 6678434682652826009600 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 44601490397061246283071436545296723011960832 (by norm_num)
  have h2M : 2 * 44601490397061246283071436545296723011960832 = 89202980794122492566142873090593446023921664 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_44601490397061246283071436545296723011960832_le
  linarith

/-- The `M = 44601490397061246283071436545296723011960832` constant honestly improves on the banked
`M = 22300745198530623141535718272648361505980416` constant
(`24/6678434682652826009600 < 3/590295810358705651712`). -/
theorem tail_44601490397061246283071436545296723011960832_lt_22300745198530623141535718272648361505980416 : (24 / 6678434682652826009600 : ℝ) < (3 / 590295810358705651712 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 89202980794122492566142873090593446023921664` tail
(`89202980794122492566142873090593446023921664^{1/2} = 9444732965739290427392` exact; exact shape mirror of
`M22300745198530623141535718272648361505980416_rpow_eq` above and latest odd-floor
`M44601490397061246283071436545296723011960832_rpow_ge` above; honest via
`9444732965739290427392^2 = 89202980794122492566142873090593446023921664` by `norm_num`;
`89202980794122492566142873090593446023921664 = 2^146` so the root is exact, unlike
`44601490397061246283071436545296723011960832`). -/
theorem M89202980794122492566142873090593446023921664_rpow_eq :
    ((((89202980794122492566142873090593446023921664 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (9444732965739290427392 : ℝ) := by
  have hx2 : ((((((89202980794122492566142873090593446023921664 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((89202980794122492566142873090593446023921664 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((9444732965739290427392 : ℝ) ^ (2 : ℕ)) = ((((89202980794122492566142873090593446023921664 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((89202980794122492566142873090593446023921664 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (9444732965739290427392 : ℝ) := by norm_num
  have hle1 : ((((((89202980794122492566142873090593446023921664 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((9444732965739290427392 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((9444732965739290427392 : ℝ) ^ (2 : ℕ)) ≤
      ((((((89202980794122492566142873090593446023921664 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 89202980794122492566142873090593446023921664` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/9444732965739290427392 = 3/1180591620717411303424`; exact shape mirror of
`r_22300745198530623141535718272648361505980416_le` above; decay recomputed honestly with
`norm_num` via the exact `M89202980794122492566142873090593446023921664_rpow_eq`; tightest honest
`T = 3/1180591620717411303424` for this root). -/
theorem r_89202980794122492566142873090593446023921664_le :
    (12 : ℝ) * ((((((89202980794122492566142873090593446023921664 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 1180591620717411303424 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((89202980794122492566142873090593446023921664 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M89202980794122492566142873090593446023921664_rpow_eq
  have hrw : ((((89202980794122492566142873090593446023921664 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((89202980794122492566142873090593446023921664 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((9444732965739290427392 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 1180591620717411303424 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 89202980794122492566142873090593446023921664`
(`‖G - S178405961588244985132285746181186892047843328‖ ≤ 3/1180591620717411303424`; exact shape mirror of
`eta_tail_22300745198530623141535718272648361505980416_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_89202980794122492566142873090593446023921664_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 89202980794122492566142873090593446023921664), etaDirichletTerm s k)‖ ≤
      (3 / 1180591620717411303424 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 89202980794122492566142873090593446023921664 (by norm_num)
  have h2M : 2 * 89202980794122492566142873090593446023921664 = 178405961588244985132285746181186892047843328 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_89202980794122492566142873090593446023921664_le
  linarith

/-- The `M = 89202980794122492566142873090593446023921664` constant honestly improves on the banked
`M = 44601490397061246283071436545296723011960832` constant
(`3/1180591620717411303424 < 24/6678434682652826009600`). -/
theorem tail_89202980794122492566142873090593446023921664_lt_44601490397061246283071436545296723011960832 : (3 / 1180591620717411303424 : ℝ) < (24 / 6678434682652826009600 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 178405961588244985132285746181186892047843328` tail
(`13356869365305652019200 ≤ 178405961588244985132285746181186892047843328^{1/2}`;
generic mirror of `M9444732965739290427392_rpow_ge` at `:4493` and latest exact
`M89202980794122492566142873090593446023921664_rpow_eq` at `:9911`; honest floor via
`13356869365305652019200^2 ≤ 178405961588244985132285746181186892047843328` by `norm_num`;
`178405961588244985132285746181186892047843328 = 2^147` so root `9444732965739290427392·√2 ≈ 13356869453140768985445`
is NOT exact; conservative doubling `2 * 6678434682652826009600 = 13356869365305652019200` below the true floor
`13356869453140768985445`; lower gap `2346404373723986579408345854879203328`). -/
theorem M178405961588244985132285746181186892047843328_rpow_ge :
    (13356869365305652019200 : ℝ) ≤ ((((178405961588244985132285746181186892047843328 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((13356869365305652019200 : ℝ) ^ (2 : ℕ)) ≤ ((((178405961588244985132285746181186892047843328 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((178405961588244985132285746181186892047843328 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((178405961588244985132285746181186892047843328 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 178405961588244985132285746181186892047843328` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/13356869365305652019200`; generic mirror of `r_9444732965739290427392_le`
at `:4509` and latest exact `r_89202980794122492566142873090593446023921664_le` at `:9937`; decay recomputed honestly
with `norm_num` via `M178405961588244985132285746181186892047843328_rpow_ge`; honest conservative
`T = 24/13356869365305652019200` for the `13356869365305652019200` root lower). -/
theorem r_178405961588244985132285746181186892047843328_le :
    (12 : ℝ) * ((((((178405961588244985132285746181186892047843328 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 13356869365305652019200 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((178405961588244985132285746181186892047843328 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((178405961588244985132285746181186892047843328 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M178405961588244985132285746181186892047843328_rpow_ge
  have hrw : ((((178405961588244985132285746181186892047843328 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((178405961588244985132285746181186892047843328 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((178405961588244985132285746181186892047843328 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (13356869365305652019200 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((178405961588244985132285746181186892047843328 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (13356869365305652019200 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((178405961588244985132285746181186892047843328 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((13356869365305652019200 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((13356869365305652019200 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 13356869365305652019200 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 178405961588244985132285746181186892047843328`
(`‖G - S356811923176489970264571492362373784095686656‖ ≤ 24/13356869365305652019200`; generic mirror of
`eta_tail_9444732965739290427392_le` at `:4536` and latest exact `eta_tail_89202980794122492566142873090593446023921664_le`
at `:9954` — numerals use only `Re = 1/2` and `‖s‖ ≤ 12`). -/
theorem eta_tail_178405961588244985132285746181186892047843328_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 178405961588244985132285746181186892047843328), etaDirichletTerm s k)‖ ≤
      (24 / 13356869365305652019200 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 178405961588244985132285746181186892047843328 (by norm_num)
  have h2M : 2 * 178405961588244985132285746181186892047843328 = 356811923176489970264571492362373784095686656 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_178405961588244985132285746181186892047843328_le
  linarith

/-- The `M = 178405961588244985132285746181186892047843328` constant honestly improves on the banked
`M = 89202980794122492566142873090593446023921664` constant
(`24/13356869365305652019200 < 3/1180591620717411303424`). -/
theorem tail_178405961588244985132285746181186892047843328_lt_89202980794122492566142873090593446023921664 : (24 / 13356869365305652019200 : ℝ) < (3 / 1180591620717411303424 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 356811923176489970264571492362373784095686656` tail
(`356811923176489970264571492362373784095686656^{1/2} = 18889465931478580854784` exact; exact shape mirror of
`M89202980794122492566142873090593446023921664_rpow_eq` at `:9911` and latest odd-floor
`M178405961588244985132285746181186892047843328_rpow_ge` above; honest via
`18889465931478580854784^2 = 356811923176489970264571492362373784095686656` by `norm_num`;
`356811923176489970264571492362373784095686656 = 2^148` so the root is exact, unlike
`178405961588244985132285746181186892047843328`). -/
theorem M356811923176489970264571492362373784095686656_rpow_eq :
    ((((356811923176489970264571492362373784095686656 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (18889465931478580854784 : ℝ) := by
  have hx2 : ((((((356811923176489970264571492362373784095686656 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((356811923176489970264571492362373784095686656 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((18889465931478580854784 : ℝ) ^ (2 : ℕ)) = ((((356811923176489970264571492362373784095686656 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((356811923176489970264571492362373784095686656 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (18889465931478580854784 : ℝ) := by norm_num
  have hle1 : ((((((356811923176489970264571492362373784095686656 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((18889465931478580854784 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((18889465931478580854784 : ℝ) ^ (2 : ℕ)) ≤
      ((((((356811923176489970264571492362373784095686656 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 356811923176489970264571492362373784095686656` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/18889465931478580854784 = 3/2361183241434822606848`; exact shape mirror of
`r_89202980794122492566142873090593446023921664_le` at `:9937`; decay recomputed honestly with `norm_num`
via the exact `M356811923176489970264571492362373784095686656_rpow_eq`; tightest honest
`T = 3/2361183241434822606848` for this root). -/
theorem r_356811923176489970264571492362373784095686656_le :
    (12 : ℝ) * ((((((356811923176489970264571492362373784095686656 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 2361183241434822606848 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((356811923176489970264571492362373784095686656 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M356811923176489970264571492362373784095686656_rpow_eq
  have hrw : ((((356811923176489970264571492362373784095686656 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((356811923176489970264571492362373784095686656 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((18889465931478580854784 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 2361183241434822606848 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 356811923176489970264571492362373784095686656`
(`‖G - S713623846352979940529142984724747568191373312‖ ≤ 3/2361183241434822606848`; exact shape mirror of
`eta_tail_89202980794122492566142873090593446023921664_le` at `:9954` — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_356811923176489970264571492362373784095686656_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 356811923176489970264571492362373784095686656), etaDirichletTerm s k)‖ ≤
      (3 / 2361183241434822606848 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 356811923176489970264571492362373784095686656 (by norm_num)
  have h2M : 2 * 356811923176489970264571492362373784095686656 = 713623846352979940529142984724747568191373312 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_356811923176489970264571492362373784095686656_le
  linarith

/-- The `M = 356811923176489970264571492362373784095686656` constant honestly improves on the banked
`M = 178405961588244985132285746181186892047843328` constant
(`3/2361183241434822606848 < 24/13356869365305652019200`). -/
theorem tail_356811923176489970264571492362373784095686656_lt_178405961588244985132285746181186892047843328 : (3 / 2361183241434822606848 : ℝ) < (24 / 13356869365305652019200 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 713623846352979940529142984724747568191373312` tail
(`26713738730611304038400 ≤ 713623846352979940529142984724747568191373312^{1/2}`;
generic mirror of `M178405961588244985132285746181186892047843328_rpow_ge` and latest exact
`M356811923176489970264571492362373784095686656_rpow_eq`; honest floor via
`26713738730611304038400^2 = 713623836967362445633196667091364148674560000 ≤
713623846352979940529142984724747568191373312` by `norm_num`;
`713623846352979940529142984724747568191373312 = 2^149` so root `18889465931478580854784·√2 ≈ 26713738906281537970891`
is NOT exact; conservative doubling `2 * 13356869365305652019200 = 26713738730611304038400` below the true floor
`26713738906281537970891`; lower gap `9385617494895946317633383419516813312`). -/
theorem M713623846352979940529142984724747568191373312_rpow_ge :
    (26713738730611304038400 : ℝ) ≤ ((((713623846352979940529142984724747568191373312 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((26713738730611304038400 : ℝ) ^ (2 : ℕ)) ≤ ((((713623846352979940529142984724747568191373312 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((713623846352979940529142984724747568191373312 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((713623846352979940529142984724747568191373312 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 713623846352979940529142984724747568191373312` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/26713738730611304038400`; generic mirror of `r_178405961588244985132285746181186892047843328_le`
and latest exact `r_356811923176489970264571492362373784095686656_le`; decay recomputed honestly
with `norm_num` via `M713623846352979940529142984724747568191373312_rpow_ge`; honest conservative
`T = 24/26713738730611304038400` for the `26713738730611304038400` root lower). -/
theorem r_713623846352979940529142984724747568191373312_le :
    (12 : ℝ) * ((((((713623846352979940529142984724747568191373312 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 26713738730611304038400 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((713623846352979940529142984724747568191373312 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((713623846352979940529142984724747568191373312 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M713623846352979940529142984724747568191373312_rpow_ge
  have hrw : ((((713623846352979940529142984724747568191373312 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((713623846352979940529142984724747568191373312 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((713623846352979940529142984724747568191373312 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (26713738730611304038400 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((713623846352979940529142984724747568191373312 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (26713738730611304038400 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((713623846352979940529142984724747568191373312 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((26713738730611304038400 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((26713738730611304038400 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 26713738730611304038400 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 713623846352979940529142984724747568191373312`
(`‖G - S1427247692705959881058285969449495136382746624‖ ≤ 24/26713738730611304038400`;
generic mirror of `eta_tail_178405961588244985132285746181186892047843328_le` and latest exact
`eta_tail_356811923176489970264571492362373784095686656_le` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_713623846352979940529142984724747568191373312_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 713623846352979940529142984724747568191373312), etaDirichletTerm s k)‖ ≤
      (24 / 26713738730611304038400 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 713623846352979940529142984724747568191373312 (by norm_num)
  have h2M : 2 * 713623846352979940529142984724747568191373312 = 1427247692705959881058285969449495136382746624 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_713623846352979940529142984724747568191373312_le
  linarith

/-- The `M = 713623846352979940529142984724747568191373312` constant honestly improves on the banked
`M = 356811923176489970264571492362373784095686656` constant
(`24/26713738730611304038400 < 3/2361183241434822606848`). -/
theorem tail_713623846352979940529142984724747568191373312_lt_356811923176489970264571492362373784095686656 : (24 / 26713738730611304038400 : ℝ) < (3 / 2361183241434822606848 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 1427247692705959881058285969449495136382746624` tail
(`1427247692705959881058285969449495136382746624^{1/2} = 37778931862957161709568` exact; exact shape mirror of
`M356811923176489970264571492362373784095686656_rpow_eq` and latest odd-floor
`M713623846352979940529142984724747568191373312_rpow_ge` above; honest via
`37778931862957161709568^2 = 1427247692705959881058285969449495136382746624` by `norm_num`;
`1427247692705959881058285969449495136382746624 = 2^150` so the root is exact, unlike
`713623846352979940529142984724747568191373312`). -/
theorem M1427247692705959881058285969449495136382746624_rpow_eq :
    ((((1427247692705959881058285969449495136382746624 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (37778931862957161709568 : ℝ) := by
  have hx2 : ((((((1427247692705959881058285969449495136382746624 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((1427247692705959881058285969449495136382746624 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((37778931862957161709568 : ℝ) ^ (2 : ℕ)) = ((((1427247692705959881058285969449495136382746624 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((1427247692705959881058285969449495136382746624 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (37778931862957161709568 : ℝ) := by norm_num
  have hle1 : ((((((1427247692705959881058285969449495136382746624 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((37778931862957161709568 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((37778931862957161709568 : ℝ) ^ (2 : ℕ)) ≤
      ((((((1427247692705959881058285969449495136382746624 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 1427247692705959881058285969449495136382746624` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/37778931862957161709568 = 3/4722366482869645213696`; exact shape mirror of
`r_356811923176489970264571492362373784095686656_le`; decay recomputed honestly with `norm_num`
via the exact `M1427247692705959881058285969449495136382746624_rpow_eq`; tightest honest
`T = 3/4722366482869645213696` for this root). -/
theorem r_1427247692705959881058285969449495136382746624_le :
    (12 : ℝ) * ((((((1427247692705959881058285969449495136382746624 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 4722366482869645213696 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((1427247692705959881058285969449495136382746624 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M1427247692705959881058285969449495136382746624_rpow_eq
  have hrw : ((((1427247692705959881058285969449495136382746624 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((1427247692705959881058285969449495136382746624 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((37778931862957161709568 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 4722366482869645213696 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 1427247692705959881058285969449495136382746624`
(`‖G - S2854495385411919762116571938898990272765493248‖ ≤ 3/4722366482869645213696`; exact shape mirror of
`eta_tail_356811923176489970264571492362373784095686656_le` — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_1427247692705959881058285969449495136382746624_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 1427247692705959881058285969449495136382746624), etaDirichletTerm s k)‖ ≤
      (3 / 4722366482869645213696 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1427247692705959881058285969449495136382746624 (by norm_num)
  have h2M : 2 * 1427247692705959881058285969449495136382746624 = 2854495385411919762116571938898990272765493248 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_1427247692705959881058285969449495136382746624_le
  linarith

/-- The `M = 1427247692705959881058285969449495136382746624` constant honestly improves on the banked
`M = 713623846352979940529142984724747568191373312` constant
(`3/4722366482869645213696 < 24/26713738730611304038400`). -/
theorem tail_1427247692705959881058285969449495136382746624_lt_713623846352979940529142984724747568191373312 : (3 / 4722366482869645213696 : ℝ) < (24 / 26713738730611304038400 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 2854495385411919762116571938898990272765493248` tail
(`53427477461222608076800 ≤ 2854495385411919762116571938898990272765493248^{1/2}`;
generic mirror of `M713623846352979940529142984724747568191373312_rpow_ge` and latest exact
`M1427247692705959881058285969449495136382746624_rpow_eq`; honest floor via
`53427477461222608076800^2 = 2854495347869449782532786668365456594698240000 ≤
2854495385411919762116571938898990272765493248` by `norm_num`;
`2854495385411919762116571938898990272765493248 = 2^151` so root `37778931862957161709568·√2 ≈ 53427477812563075941783`
is NOT exact; conservative doubling `2 * 26713738730611304038400 = 53427477461222608076800` below the true floor
`53427477812563075941783`; lower gap `37542469979583785270533533678067253248`). -/
theorem M2854495385411919762116571938898990272765493248_rpow_ge :
    (53427477461222608076800 : ℝ) ≤ ((((2854495385411919762116571938898990272765493248 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((53427477461222608076800 : ℝ) ^ (2 : ℕ)) ≤ ((((2854495385411919762116571938898990272765493248 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((2854495385411919762116571938898990272765493248 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((2854495385411919762116571938898990272765493248 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 2854495385411919762116571938898990272765493248` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/53427477461222608076800`; generic mirror of `r_713623846352979940529142984724747568191373312_le`
and latest exact `r_1427247692705959881058285969449495136382746624_le`; decay recomputed honestly
with `norm_num` via `M2854495385411919762116571938898990272765493248_rpow_ge`; honest conservative
`T = 24/53427477461222608076800` for the `53427477461222608076800` root lower). -/
theorem r_2854495385411919762116571938898990272765493248_le :
    (12 : ℝ) * ((((((2854495385411919762116571938898990272765493248 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 53427477461222608076800 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((2854495385411919762116571938898990272765493248 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((2854495385411919762116571938898990272765493248 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M2854495385411919762116571938898990272765493248_rpow_ge
  have hrw : ((((2854495385411919762116571938898990272765493248 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((2854495385411919762116571938898990272765493248 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((2854495385411919762116571938898990272765493248 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (53427477461222608076800 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((2854495385411919762116571938898990272765493248 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (53427477461222608076800 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((2854495385411919762116571938898990272765493248 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((53427477461222608076800 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((53427477461222608076800 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 53427477461222608076800 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 2854495385411919762116571938898990272765493248`
(`‖G - S5708990770823839524233143877797980545530986496‖ ≤ 24/53427477461222608076800`;
generic mirror of `eta_tail_713623846352979940529142984724747568191373312_le` and latest exact
`eta_tail_1427247692705959881058285969449495136382746624_le` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_2854495385411919762116571938898990272765493248_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 2854495385411919762116571938898990272765493248), etaDirichletTerm s k)‖ ≤
      (24 / 53427477461222608076800 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 2854495385411919762116571938898990272765493248 (by norm_num)
  have h2M : 2 * 2854495385411919762116571938898990272765493248 = 5708990770823839524233143877797980545530986496 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_2854495385411919762116571938898990272765493248_le
  linarith

/-- The `M = 2854495385411919762116571938898990272765493248` constant honestly improves on the banked
`M = 1427247692705959881058285969449495136382746624` constant
(`24/53427477461222608076800 < 3/4722366482869645213696`). -/
theorem tail_2854495385411919762116571938898990272765493248_lt_1427247692705959881058285969449495136382746624 : (24 / 53427477461222608076800 : ℝ) < (3 / 4722366482869645213696 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 5708990770823839524233143877797980545530986496` tail
(`5708990770823839524233143877797980545530986496^{1/2} = 75557863725914323419136` exact; exact shape mirror of
`M1427247692705959881058285969449495136382746624_rpow_eq` and latest odd-floor
`M2854495385411919762116571938898990272765493248_rpow_ge` above; honest via
`75557863725914323419136^2 = 5708990770823839524233143877797980545530986496` by `norm_num`;
`5708990770823839524233143877797980545530986496 = 2^152` so the root is exact, unlike
`2854495385411919762116571938898990272765493248`). -/
theorem M5708990770823839524233143877797980545530986496_rpow_eq :
    ((((5708990770823839524233143877797980545530986496 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (75557863725914323419136 : ℝ) := by
  have hx2 : ((((((5708990770823839524233143877797980545530986496 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((5708990770823839524233143877797980545530986496 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((75557863725914323419136 : ℝ) ^ (2 : ℕ)) = ((((5708990770823839524233143877797980545530986496 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((5708990770823839524233143877797980545530986496 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (75557863725914323419136 : ℝ) := by norm_num
  have hle1 : ((((((5708990770823839524233143877797980545530986496 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((75557863725914323419136 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((75557863725914323419136 : ℝ) ^ (2 : ℕ)) ≤
      ((((((5708990770823839524233143877797980545530986496 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 5708990770823839524233143877797980545530986496` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/75557863725914323419136 = 3/9444732965739290427392`; exact shape mirror of
`r_1427247692705959881058285969449495136382746624_le`; decay recomputed honestly with `norm_num`
via the exact `M5708990770823839524233143877797980545530986496_rpow_eq`; tightest honest
`T = 3/9444732965739290427392` for this root). -/
theorem r_5708990770823839524233143877797980545530986496_le :
    (12 : ℝ) * ((((((5708990770823839524233143877797980545530986496 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 9444732965739290427392 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((5708990770823839524233143877797980545530986496 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M5708990770823839524233143877797980545530986496_rpow_eq
  have hrw : ((((5708990770823839524233143877797980545530986496 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((5708990770823839524233143877797980545530986496 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((75557863725914323419136 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 9444732965739290427392 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 5708990770823839524233143877797980545530986496`
(`‖G - S11417981541647679048466287755595961091061972992‖ ≤ 3/9444732965739290427392`; exact shape mirror of
`eta_tail_1427247692705959881058285969449495136382746624_le` — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_5708990770823839524233143877797980545530986496_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 5708990770823839524233143877797980545530986496), etaDirichletTerm s k)‖ ≤
      (3 / 9444732965739290427392 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 5708990770823839524233143877797980545530986496 (by norm_num)
  have h2M : 2 * 5708990770823839524233143877797980545530986496 = 11417981541647679048466287755595961091061972992 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_5708990770823839524233143877797980545530986496_le
  linarith

/-- The `M = 5708990770823839524233143877797980545530986496` constant honestly improves on the banked
`M = 2854495385411919762116571938898990272765493248` constant
(`3/9444732965739290427392 < 24/53427477461222608076800`). -/
theorem tail_5708990770823839524233143877797980545530986496_lt_2854495385411919762116571938898990272765493248 : (3 / 9444732965739290427392 : ℝ) < (24 / 53427477461222608076800 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 11417981541647679048466287755595961091061972992` tail
(`106854954922445216153600 ≤ 11417981541647679048466287755595961091061972992^{1/2}`;
generic mirror of `M2854495385411919762116571938898990272765493248_rpow_ge` and latest exact
`M5708990770823839524233143877797980545530986496_rpow_eq` above; honest floor via
`106854954922445216153600^2 = 11417981391477799130131146673461826378792960000 ≤
11417981541647679048466287755595961091061972992` by `norm_num`;
`11417981541647679048466287755595961091061972992 = 2^153` so root `75557863725914323419136·√2 ≈
106854955625126151883567` is NOT exact; conservative doubling
`2 * 53427477461222608076800 = 106854954922445216153600` below the true floor
`106854955625126151883567`; lower gap `150169879918335141082134134712269012992`). -/
theorem M11417981541647679048466287755595961091061972992_rpow_ge :
    (106854954922445216153600 : ℝ) ≤ ((((11417981541647679048466287755595961091061972992 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((106854954922445216153600 : ℝ) ^ (2 : ℕ)) ≤ ((((11417981541647679048466287755595961091061972992 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((11417981541647679048466287755595961091061972992 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((11417981541647679048466287755595961091061972992 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 11417981541647679048466287755595961091061972992` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/106854954922445216153600`; generic mirror of
`r_2854495385411919762116571938898990272765493248_le` and latest exact
`r_5708990770823839524233143877797980545530986496_le`; decay recomputed honestly
with `norm_num` via `M11417981541647679048466287755595961091061972992_rpow_ge`; honest conservative
`T = 24/106854954922445216153600` for the `106854954922445216153600` root lower). -/
theorem r_11417981541647679048466287755595961091061972992_le :
    (12 : ℝ) * ((((((11417981541647679048466287755595961091061972992 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 106854954922445216153600 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((11417981541647679048466287755595961091061972992 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((11417981541647679048466287755595961091061972992 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M11417981541647679048466287755595961091061972992_rpow_ge
  have hrw : ((((11417981541647679048466287755595961091061972992 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((11417981541647679048466287755595961091061972992 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((11417981541647679048466287755595961091061972992 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (106854954922445216153600 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((11417981541647679048466287755595961091061972992 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (106854954922445216153600 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((11417981541647679048466287755595961091061972992 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((106854954922445216153600 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((106854954922445216153600 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 106854954922445216153600 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 11417981541647679048466287755595961091061972992`
(`‖G - S22835963083295358096932575511191922182123945984‖ ≤ 24/106854954922445216153600`;
generic mirror of `eta_tail_2854495385411919762116571938898990272765493248_le` and latest exact
`eta_tail_5708990770823839524233143877797980545530986496_le` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_11417981541647679048466287755595961091061972992_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 11417981541647679048466287755595961091061972992), etaDirichletTerm s k)‖ ≤
      (24 / 106854954922445216153600 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 11417981541647679048466287755595961091061972992 (by norm_num)
  have h2M : 2 * 11417981541647679048466287755595961091061972992 = 22835963083295358096932575511191922182123945984 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_11417981541647679048466287755595961091061972992_le
  linarith

/-- The `M = 11417981541647679048466287755595961091061972992` constant honestly improves on the banked
`M = 5708990770823839524233143877797980545530986496` constant
(`24/106854954922445216153600 < 3/9444732965739290427392`). -/
theorem tail_11417981541647679048466287755595961091061972992_lt_5708990770823839524233143877797980545530986496 : (24 / 106854954922445216153600 : ℝ) < (3 / 9444732965739290427392 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 22835963083295358096932575511191922182123945984` tail
(`22835963083295358096932575511191922182123945984^{1/2} = 151115727451828646838272` exact; exact shape mirror of
`M5708990770823839524233143877797980545530986496_rpow_eq` and latest odd-floor
`M11417981541647679048466287755595961091061972992_rpow_ge` above; honest via
`151115727451828646838272^2 = 22835963083295358096932575511191922182123945984` by `norm_num`;
`22835963083295358096932575511191922182123945984 = 2^154` so the root is exact, unlike
`11417981541647679048466287755595961091061972992`). -/
theorem M22835963083295358096932575511191922182123945984_rpow_eq :
    ((((22835963083295358096932575511191922182123945984 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (151115727451828646838272 : ℝ) := by
  have hx2 : ((((((22835963083295358096932575511191922182123945984 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((22835963083295358096932575511191922182123945984 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((151115727451828646838272 : ℝ) ^ (2 : ℕ)) = ((((22835963083295358096932575511191922182123945984 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((22835963083295358096932575511191922182123945984 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (151115727451828646838272 : ℝ) := by norm_num
  have hle1 : ((((((22835963083295358096932575511191922182123945984 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((151115727451828646838272 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((151115727451828646838272 : ℝ) ^ (2 : ℕ)) ≤
      ((((((22835963083295358096932575511191922182123945984 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 22835963083295358096932575511191922182123945984` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/151115727451828646838272 = 3/18889465931478580854784`; exact shape mirror of
`r_5708990770823839524233143877797980545530986496_le`; decay recomputed honestly with `norm_num`
via the exact `M22835963083295358096932575511191922182123945984_rpow_eq`; tightest honest
`T = 3/18889465931478580854784` for this root). -/
theorem r_22835963083295358096932575511191922182123945984_le :
    (12 : ℝ) * ((((((22835963083295358096932575511191922182123945984 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 18889465931478580854784 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((22835963083295358096932575511191922182123945984 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M22835963083295358096932575511191922182123945984_rpow_eq
  have hrw : ((((22835963083295358096932575511191922182123945984 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((22835963083295358096932575511191922182123945984 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((151115727451828646838272 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 18889465931478580854784 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 22835963083295358096932575511191922182123945984`
(`‖G - S45671926166590716193865151022383844364247891968‖ ≤ 3/18889465931478580854784`; exact shape mirror of
`eta_tail_5708990770823839524233143877797980545530986496_le` — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_22835963083295358096932575511191922182123945984_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 22835963083295358096932575511191922182123945984), etaDirichletTerm s k)‖ ≤
      (3 / 18889465931478580854784 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 22835963083295358096932575511191922182123945984 (by norm_num)
  have h2M : 2 * 22835963083295358096932575511191922182123945984 = 45671926166590716193865151022383844364247891968 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_22835963083295358096932575511191922182123945984_le
  linarith

/-- The `M = 22835963083295358096932575511191922182123945984` constant honestly improves on the banked
`M = 11417981541647679048466287755595961091061972992` constant
(`3/18889465931478580854784 < 24/106854954922445216153600`). -/
theorem tail_22835963083295358096932575511191922182123945984_lt_11417981541647679048466287755595961091061972992 : (3 / 18889465931478580854784 : ℝ) < (24 / 106854954922445216153600 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 45671926166590716193865151022383844364247891968` tail
(`213709909844890432307200 ≤ 45671926166590716193865151022383844364247891968^{1/2}`;
generic mirror of `M11417981541647679048466287755595961091061972992_rpow_ge` and latest exact
`M22835963083295358096932575511191922182123945984_rpow_eq` above; honest floor via
`213709909844890432307200^2 = 45671925565911196520524586693847305515171840000 ≤
45671926166590716193865151022383844364247891968` by `norm_num`;
`45671926166590716193865151022383844364247891968 = 2^155` so root `151115727451828646838272·√2 ≈
213709911250252303767135` is NOT exact; conservative doubling
`2 * 106854954922445216153600 = 213709909844890432307200` below the true floor
`213709911250252303767135`; lower gap `600679519673340564328536538849076051968`). -/
theorem M45671926166590716193865151022383844364247891968_rpow_ge :
    (213709909844890432307200 : ℝ) ≤ ((((45671926166590716193865151022383844364247891968 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((213709909844890432307200 : ℝ) ^ (2 : ℕ)) ≤ ((((45671926166590716193865151022383844364247891968 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((45671926166590716193865151022383844364247891968 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((45671926166590716193865151022383844364247891968 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 45671926166590716193865151022383844364247891968` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/213709909844890432307200`; generic mirror of
`r_11417981541647679048466287755595961091061972992_le` and latest exact
`r_22835963083295358096932575511191922182123945984_le`; decay recomputed honestly
with `norm_num` via `M45671926166590716193865151022383844364247891968_rpow_ge`; honest conservative
`T = 24/213709909844890432307200` for the `213709909844890432307200` root lower). -/
theorem r_45671926166590716193865151022383844364247891968_le :
    (12 : ℝ) * ((((((45671926166590716193865151022383844364247891968 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 213709909844890432307200 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((45671926166590716193865151022383844364247891968 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((45671926166590716193865151022383844364247891968 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M45671926166590716193865151022383844364247891968_rpow_ge
  have hrw : ((((45671926166590716193865151022383844364247891968 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((45671926166590716193865151022383844364247891968 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((45671926166590716193865151022383844364247891968 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (213709909844890432307200 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((45671926166590716193865151022383844364247891968 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (213709909844890432307200 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((45671926166590716193865151022383844364247891968 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((213709909844890432307200 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((213709909844890432307200 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 213709909844890432307200 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 45671926166590716193865151022383844364247891968`
(`‖G - S91343852333181432387730302044767688728495783936‖ ≤ 24/213709909844890432307200`;
generic mirror of `eta_tail_11417981541647679048466287755595961091061972992_le` and latest exact
`eta_tail_22835963083295358096932575511191922182123945984_le` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_45671926166590716193865151022383844364247891968_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 45671926166590716193865151022383844364247891968), etaDirichletTerm s k)‖ ≤
      (24 / 213709909844890432307200 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 45671926166590716193865151022383844364247891968 (by norm_num)
  have h2M : 2 * 45671926166590716193865151022383844364247891968 = 91343852333181432387730302044767688728495783936 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_45671926166590716193865151022383844364247891968_le
  linarith

/-- The `M = 45671926166590716193865151022383844364247891968` constant honestly improves on the banked
`M = 22835963083295358096932575511191922182123945984` constant
(`24/213709909844890432307200 < 3/18889465931478580854784`). -/
theorem tail_45671926166590716193865151022383844364247891968_lt_22835963083295358096932575511191922182123945984 : (24 / 213709909844890432307200 : ℝ) < (3 / 18889465931478580854784 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 91343852333181432387730302044767688728495783936` tail
(`91343852333181432387730302044767688728495783936^{1/2} = 302231454903657293676544` exact; exact shape mirror of
`M22835963083295358096932575511191922182123945984_rpow_eq` and latest odd-floor
`M45671926166590716193865151022383844364247891968_rpow_ge` above; honest via
`302231454903657293676544^2 = 91343852333181432387730302044767688728495783936` by `norm_num`;
`91343852333181432387730302044767688728495783936 = 2^156` so the root is exact, unlike
`45671926166590716193865151022383844364247891968`). -/
theorem M91343852333181432387730302044767688728495783936_rpow_eq :
    ((((91343852333181432387730302044767688728495783936 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (302231454903657293676544 : ℝ) := by
  have hx2 : ((((((91343852333181432387730302044767688728495783936 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((91343852333181432387730302044767688728495783936 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((302231454903657293676544 : ℝ) ^ (2 : ℕ)) = ((((91343852333181432387730302044767688728495783936 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((91343852333181432387730302044767688728495783936 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (302231454903657293676544 : ℝ) := by norm_num
  have hle1 : ((((((91343852333181432387730302044767688728495783936 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((302231454903657293676544 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((302231454903657293676544 : ℝ) ^ (2 : ℕ)) ≤
      ((((((91343852333181432387730302044767688728495783936 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 91343852333181432387730302044767688728495783936` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/302231454903657293676544 = 3/37778931862957161709568`; exact shape mirror of
`r_22835963083295358096932575511191922182123945984_le`; decay recomputed honestly with `norm_num`
via the exact `M91343852333181432387730302044767688728495783936_rpow_eq`; tightest honest
`T = 3/37778931862957161709568` for this root). -/
theorem r_91343852333181432387730302044767688728495783936_le :
    (12 : ℝ) * ((((((91343852333181432387730302044767688728495783936 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 37778931862957161709568 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((91343852333181432387730302044767688728495783936 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M91343852333181432387730302044767688728495783936_rpow_eq
  have hrw : ((((91343852333181432387730302044767688728495783936 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((91343852333181432387730302044767688728495783936 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((302231454903657293676544 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 37778931862957161709568 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 91343852333181432387730302044767688728495783936`
(`‖G - S182687704666362864775460604089535377456991567872‖ ≤ 3/37778931862957161709568`; exact shape mirror of
`eta_tail_22835963083295358096932575511191922182123945984_le` — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_91343852333181432387730302044767688728495783936_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 91343852333181432387730302044767688728495783936), etaDirichletTerm s k)‖ ≤
      (3 / 37778931862957161709568 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 91343852333181432387730302044767688728495783936 (by norm_num)
  have h2M : 2 * 91343852333181432387730302044767688728495783936 = 182687704666362864775460604089535377456991567872 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_91343852333181432387730302044767688728495783936_le
  linarith

/-- The `M = 91343852333181432387730302044767688728495783936` constant honestly improves on the banked
`M = 45671926166590716193865151022383844364247891968` constant
(`3/37778931862957161709568 < 24/213709909844890432307200`). -/
theorem tail_91343852333181432387730302044767688728495783936_lt_45671926166590716193865151022383844364247891968 : (3 / 37778931862957161709568 : ℝ) < (24 / 213709909844890432307200 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 182687704666362864775460604089535377456991567872` tail
(`427419819689780864614400 ≤ 182687704666362864775460604089535377456991567872^{1/2}`;
generic mirror of `M45671926166590716193865151022383844364247891968_rpow_ge` above and latest exact
`M91343852333181432387730302044767688728495783936_rpow_eq` above; honest floor via
`427419819689780864614400^2 ≤ 182687704666362864775460604089535377456991567872` by `norm_num`;
doubling pattern `427419819689780864614400 = 2 * 213709909844890432307200`;
`182687704666362864775460604089535377456991567872 = 2^157` so root `2^78·√2` is NOT exact,
unlike `91343852333181432387730302044767688728495783936`). -/
theorem M182687704666362864775460604089535377456991567872_rpow_ge :
    (427419819689780864614400 : ℝ) ≤ ((((182687704666362864775460604089535377456991567872 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((427419819689780864614400 : ℝ) ^ (2 : ℕ)) ≤ ((((182687704666362864775460604089535377456991567872 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((182687704666362864775460604089535377456991567872 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((182687704666362864775460604089535377456991567872 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 182687704666362864775460604089535377456991567872` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/427419819689780864614400`; generic mirror of
`r_45671926166590716193865151022383844364247891968_le` above and latest exact
`r_91343852333181432387730302044767688728495783936_le` above; decay recomputed honestly with
`norm_num` via `M182687704666362864775460604089535377456991567872_rpow_ge`; tightest honest
`T = 24/427419819689780864614400` for the `427419819689780864614400` root lower). -/
theorem r_182687704666362864775460604089535377456991567872_le :
    (12 : ℝ) * ((((((182687704666362864775460604089535377456991567872 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 427419819689780864614400 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((182687704666362864775460604089535377456991567872 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((182687704666362864775460604089535377456991567872 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M182687704666362864775460604089535377456991567872_rpow_ge
  have hrw : ((((182687704666362864775460604089535377456991567872 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((182687704666362864775460604089535377456991567872 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((182687704666362864775460604089535377456991567872 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (427419819689780864614400 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((182687704666362864775460604089535377456991567872 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (427419819689780864614400 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((182687704666362864775460604089535377456991567872 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((427419819689780864614400 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((427419819689780864614400 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 427419819689780864614400 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 182687704666362864775460604089535377456991567872`
(`‖G - S365375409332725729550921208179070754913983135744‖ ≤ 24/427419819689780864614400`; generic mirror
of `eta_tail_45671926166590716193865151022383844364247891968_le` above and latest exact
`eta_tail_91343852333181432387730302044767688728495783936_le` above — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_182687704666362864775460604089535377456991567872_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 182687704666362864775460604089535377456991567872), etaDirichletTerm s k)‖ ≤
      (24 / 427419819689780864614400 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 182687704666362864775460604089535377456991567872 (by norm_num)
  have h2M : 2 * 182687704666362864775460604089535377456991567872 = 365375409332725729550921208179070754913983135744 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_182687704666362864775460604089535377456991567872_le
  linarith

/-- The `M = 182687704666362864775460604089535377456991567872` constant honestly improves on the banked
`M = 91343852333181432387730302044767688728495783936` constant
(`24/427419819689780864614400 < 3/37778931862957161709568`). -/
theorem tail_182687704666362864775460604089535377456991567872_lt_91343852333181432387730302044767688728495783936 : (24 / 427419819689780864614400 : ℝ) < (3 / 37778931862957161709568 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 365375409332725729550921208179070754913983135744` tail
(`365375409332725729550921208179070754913983135744^{1/2} = 604462909807314587353088` exact; exact shape mirror of
`M91343852333181432387730302044767688728495783936_rpow_eq` above and latest odd-floor
`M182687704666362864775460604089535377456991567872_rpow_ge` above; honest via
`604462909807314587353088^2 = 365375409332725729550921208179070754913983135744` by `norm_num`;
`365375409332725729550921208179070754913983135744 = 2^158` so the root is exact, unlike
`182687704666362864775460604089535377456991567872`). -/
theorem M365375409332725729550921208179070754913983135744_rpow_eq :
    ((((365375409332725729550921208179070754913983135744 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (604462909807314587353088 : ℝ) := by
  have hx2 : ((((((365375409332725729550921208179070754913983135744 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((365375409332725729550921208179070754913983135744 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((604462909807314587353088 : ℝ) ^ (2 : ℕ)) = ((((365375409332725729550921208179070754913983135744 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((365375409332725729550921208179070754913983135744 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (604462909807314587353088 : ℝ) := by norm_num
  have hle1 : ((((((365375409332725729550921208179070754913983135744 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((604462909807314587353088 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((604462909807314587353088 : ℝ) ^ (2 : ℕ)) ≤
      ((((((365375409332725729550921208179070754913983135744 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 365375409332725729550921208179070754913983135744` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/604462909807314587353088 = 3/75557863725914323419136`; exact shape mirror of
`r_91343852333181432387730302044767688728495783936_le` above; decay recomputed honestly with `norm_num`
via the exact `M365375409332725729550921208179070754913983135744_rpow_eq`; tightest honest
`T = 3/75557863725914323419136` for this root). -/
theorem r_365375409332725729550921208179070754913983135744_le :
    (12 : ℝ) * ((((((365375409332725729550921208179070754913983135744 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 75557863725914323419136 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((365375409332725729550921208179070754913983135744 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M365375409332725729550921208179070754913983135744_rpow_eq
  have hrw : ((((365375409332725729550921208179070754913983135744 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((365375409332725729550921208179070754913983135744 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((604462909807314587353088 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 75557863725914323419136 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 365375409332725729550921208179070754913983135744`
(`‖G - S730750818665451459101842416358141509827966271488‖ ≤ 3/75557863725914323419136`; exact shape mirror of
`eta_tail_91343852333181432387730302044767688728495783936_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_365375409332725729550921208179070754913983135744_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 365375409332725729550921208179070754913983135744), etaDirichletTerm s k)‖ ≤
      (3 / 75557863725914323419136 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 365375409332725729550921208179070754913983135744 (by norm_num)
  have h2M : 2 * 365375409332725729550921208179070754913983135744 = 730750818665451459101842416358141509827966271488 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_365375409332725729550921208179070754913983135744_le
  linarith

/-- The `M = 365375409332725729550921208179070754913983135744` constant honestly improves on the banked
`M = 182687704666362864775460604089535377456991567872` constant
(`3/75557863725914323419136 < 24/427419819689780864614400`). -/
theorem tail_365375409332725729550921208179070754913983135744_lt_182687704666362864775460604089535377456991567872 : (3 / 75557863725914323419136 : ℝ) < (24 / 427419819689780864614400 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 730750818665451459101842416358141509827966271488` tail
(`854839639379561729228800 ≤ 730750818665451459101842416358141509827966271488^{1/2}`;
generic mirror of `M182687704666362864775460604089535377456991567872_rpow_ge` above and latest exact
`M365375409332725729550921208179070754913983135744_rpow_eq` above; honest floor via
`854839639379561729228800^2 = 730750809054579144328393387101556888242749440000 ≤
730750818665451459101842416358141509827966271488` by `norm_num`;
doubling pattern `854839639379561729228800 = 2 * 427419819689780864614400`;
`730750818665451459101842416358141509827966271488 = 2^159` so root `2^79·√2` is NOT exact,
unlike `365375409332725729550921208179070754913983135744`). -/
theorem M730750818665451459101842416358141509827966271488_rpow_ge :
    (854839639379561729228800 : ℝ) ≤ ((((730750818665451459101842416358141509827966271488 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((854839639379561729228800 : ℝ) ^ (2 : ℕ)) ≤ ((((730750818665451459101842416358141509827966271488 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((730750818665451459101842416358141509827966271488 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((730750818665451459101842416358141509827966271488 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 730750818665451459101842416358141509827966271488` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/854839639379561729228800`; generic mirror of
`r_182687704666362864775460604089535377456991567872_le` above and latest exact
`r_365375409332725729550921208179070754913983135744_le` above; decay recomputed honestly with
`norm_num` via `M730750818665451459101842416358141509827966271488_rpow_ge`; tightest honest
`T = 24/854839639379561729228800` for the `854839639379561729228800` root lower). -/
theorem r_730750818665451459101842416358141509827966271488_le :
    (12 : ℝ) * ((((((730750818665451459101842416358141509827966271488 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 854839639379561729228800 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((730750818665451459101842416358141509827966271488 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((730750818665451459101842416358141509827966271488 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M730750818665451459101842416358141509827966271488_rpow_ge
  have hrw : ((((730750818665451459101842416358141509827966271488 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((730750818665451459101842416358141509827966271488 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((730750818665451459101842416358141509827966271488 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (854839639379561729228800 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((730750818665451459101842416358141509827966271488 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (854839639379561729228800 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((730750818665451459101842416358141509827966271488 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((854839639379561729228800 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((854839639379561729228800 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 854839639379561729228800 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 730750818665451459101842416358141509827966271488`
(`‖G - S1461501637330902918203684832716283019655932542976‖ ≤ 24/854839639379561729228800`; generic mirror
of `eta_tail_182687704666362864775460604089535377456991567872_le` above and latest exact
`eta_tail_365375409332725729550921208179070754913983135744_le` above — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_730750818665451459101842416358141509827966271488_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 730750818665451459101842416358141509827966271488), etaDirichletTerm s k)‖ ≤
      (24 / 854839639379561729228800 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 730750818665451459101842416358141509827966271488 (by norm_num)
  have h2M : 2 * 730750818665451459101842416358141509827966271488 = 1461501637330902918203684832716283019655932542976 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_730750818665451459101842416358141509827966271488_le
  linarith

/-- The `M = 730750818665451459101842416358141509827966271488` constant honestly improves on the banked
`M = 365375409332725729550921208179070754913983135744` constant
(`24/854839639379561729228800 < 3/75557863725914323419136`). -/
theorem tail_730750818665451459101842416358141509827966271488_lt_365375409332725729550921208179070754913983135744 : (24 / 854839639379561729228800 : ℝ) < (3 / 75557863725914323419136 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 1461501637330902918203684832716283019655932542976` tail
(`1461501637330902918203684832716283019655932542976^{1/2} = 1208925819614629174706176` exact; exact shape mirror of
`M365375409332725729550921208179070754913983135744_rpow_eq` above and latest odd-floor
`M730750818665451459101842416358141509827966271488_rpow_ge` above; honest via
`1208925819614629174706176^2 = 1461501637330902918203684832716283019655932542976` by `norm_num`;
`1461501637330902918203684832716283019655932542976 = 2^160` so the root is exact, unlike
`730750818665451459101842416358141509827966271488`). -/
theorem M1461501637330902918203684832716283019655932542976_rpow_eq :
    ((((1461501637330902918203684832716283019655932542976 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (1208925819614629174706176 : ℝ) := by
  have hx2 : ((((((1461501637330902918203684832716283019655932542976 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((1461501637330902918203684832716283019655932542976 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((1208925819614629174706176 : ℝ) ^ (2 : ℕ)) = ((((1461501637330902918203684832716283019655932542976 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((1461501637330902918203684832716283019655932542976 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (1208925819614629174706176 : ℝ) := by norm_num
  have hle1 : ((((((1461501637330902918203684832716283019655932542976 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((1208925819614629174706176 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((1208925819614629174706176 : ℝ) ^ (2 : ℕ)) ≤
      ((((((1461501637330902918203684832716283019655932542976 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 1461501637330902918203684832716283019655932542976` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/1208925819614629174706176 = 3/151115727451828646838272`; exact shape mirror of
`r_365375409332725729550921208179070754913983135744_le` above; decay recomputed honestly with `norm_num`
via the exact `M1461501637330902918203684832716283019655932542976_rpow_eq`; tightest honest
`T = 3/151115727451828646838272` for this root). -/
theorem r_1461501637330902918203684832716283019655932542976_le :
    (12 : ℝ) * ((((((1461501637330902918203684832716283019655932542976 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 151115727451828646838272 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((1461501637330902918203684832716283019655932542976 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M1461501637330902918203684832716283019655932542976_rpow_eq
  have hrw : ((((1461501637330902918203684832716283019655932542976 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((1461501637330902918203684832716283019655932542976 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((1208925819614629174706176 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 151115727451828646838272 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 1461501637330902918203684832716283019655932542976`
(`‖G - S2923003274661805836407369665432566039311865085952‖ ≤ 3/151115727451828646838272`; exact shape mirror of
`eta_tail_365375409332725729550921208179070754913983135744_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_1461501637330902918203684832716283019655932542976_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 1461501637330902918203684832716283019655932542976), etaDirichletTerm s k)‖ ≤
      (3 / 151115727451828646838272 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1461501637330902918203684832716283019655932542976 (by norm_num)
  have h2M : 2 * 1461501637330902918203684832716283019655932542976 = 2923003274661805836407369665432566039311865085952 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_1461501637330902918203684832716283019655932542976_le
  linarith

/-- The `M = 1461501637330902918203684832716283019655932542976` constant honestly improves on the banked
`M = 730750818665451459101842416358141509827966271488` constant
(`3/151115727451828646838272 < 24/854839639379561729228800`). -/
theorem tail_1461501637330902918203684832716283019655932542976_lt_730750818665451459101842416358141509827966271488 : (3 / 151115727451828646838272 : ℝ) < (24 / 854839639379561729228800 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 2923003274661805836407369665432566039311865085952` tail
(`1709679278759123458457600 ≤ 2923003274661805836407369665432566039311865085952^{1/2}`;
generic mirror of `M730750818665451459101842416358141509827966271488_rpow_ge` above and latest exact
`M1461501637330902918203684832716283019655932542976_rpow_eq` above; honest floor via
`1709679278759123458457600^2 = 2923003236218316577313573548406227552970997760000 ≤
2923003274661805836407369665432566039311865085952` by `norm_num`;
doubling pattern `1709679278759123458457600 = 2 * 854839639379561729228800`;
`2923003274661805836407369665432566039311865085952 = 2^161` so root `2^80·√2` is NOT exact,
unlike `1461501637330902918203684832716283019655932542976`). -/
theorem M2923003274661805836407369665432566039311865085952_rpow_ge :
    (1709679278759123458457600 : ℝ) ≤ ((((2923003274661805836407369665432566039311865085952 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((1709679278759123458457600 : ℝ) ^ (2 : ℕ)) ≤ ((((2923003274661805836407369665432566039311865085952 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((2923003274661805836407369665432566039311865085952 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((2923003274661805836407369665432566039311865085952 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 2923003274661805836407369665432566039311865085952` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/1709679278759123458457600`; generic mirror of
`r_730750818665451459101842416358141509827966271488_le` above and latest exact
`r_1461501637330902918203684832716283019655932542976_le` above; decay recomputed honestly with
`norm_num` via `M2923003274661805836407369665432566039311865085952_rpow_ge`; tightest honest
`T = 24/1709679278759123458457600` for the `1709679278759123458457600` root lower). -/
theorem r_2923003274661805836407369665432566039311865085952_le :
    (12 : ℝ) * ((((((2923003274661805836407369665432566039311865085952 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 1709679278759123458457600 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((2923003274661805836407369665432566039311865085952 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((2923003274661805836407369665432566039311865085952 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M2923003274661805836407369665432566039311865085952_rpow_ge
  have hrw : ((((2923003274661805836407369665432566039311865085952 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((2923003274661805836407369665432566039311865085952 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((2923003274661805836407369665432566039311865085952 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (1709679278759123458457600 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((2923003274661805836407369665432566039311865085952 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (1709679278759123458457600 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((2923003274661805836407369665432566039311865085952 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((1709679278759123458457600 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((1709679278759123458457600 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 1709679278759123458457600 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 2923003274661805836407369665432566039311865085952`
(`‖G - S5846006549323611672814739330865132078623730171904‖ ≤ 24/1709679278759123458457600`; generic mirror
of `eta_tail_730750818665451459101842416358141509827966271488_le` above and latest exact
`eta_tail_1461501637330902918203684832716283019655932542976_le` above — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_2923003274661805836407369665432566039311865085952_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 2923003274661805836407369665432566039311865085952), etaDirichletTerm s k)‖ ≤
      (24 / 1709679278759123458457600 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 2923003274661805836407369665432566039311865085952 (by norm_num)
  have h2M : 2 * 2923003274661805836407369665432566039311865085952 = 5846006549323611672814739330865132078623730171904 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_2923003274661805836407369665432566039311865085952_le
  linarith

/-- The `M = 2923003274661805836407369665432566039311865085952` constant honestly improves on the banked
`M = 1461501637330902918203684832716283019655932542976` constant
(`24/1709679278759123458457600 < 3/151115727451828646838272`). -/
theorem tail_2923003274661805836407369665432566039311865085952_lt_1461501637330902918203684832716283019655932542976 : (24 / 1709679278759123458457600 : ℝ) < (3 / 151115727451828646838272 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 5846006549323611672814739330865132078623730171904` tail
(`5846006549323611672814739330865132078623730171904^{1/2} = 2417851639229258349412352` exact; exact shape mirror of
`M1461501637330902918203684832716283019655932542976_rpow_eq` above and latest odd-floor
`M2923003274661805836407369665432566039311865085952_rpow_ge` above; honest via
`2417851639229258349412352^2 = 5846006549323611672814739330865132078623730171904` by `norm_num`;
`5846006549323611672814739330865132078623730171904 = 2^162` so the root is exact, unlike
`2923003274661805836407369665432566039311865085952`). -/
theorem M5846006549323611672814739330865132078623730171904_rpow_eq :
    ((((5846006549323611672814739330865132078623730171904 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (2417851639229258349412352 : ℝ) := by
  have hx2 : ((((((5846006549323611672814739330865132078623730171904 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((5846006549323611672814739330865132078623730171904 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((2417851639229258349412352 : ℝ) ^ (2 : ℕ)) = ((((5846006549323611672814739330865132078623730171904 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((5846006549323611672814739330865132078623730171904 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (2417851639229258349412352 : ℝ) := by norm_num
  have hle1 : ((((((5846006549323611672814739330865132078623730171904 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((2417851639229258349412352 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((2417851639229258349412352 : ℝ) ^ (2 : ℕ)) ≤
      ((((((5846006549323611672814739330865132078623730171904 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 5846006549323611672814739330865132078623730171904` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/2417851639229258349412352 = 3/302231454903657293676544`; exact shape mirror of
`r_1461501637330902918203684832716283019655932542976_le` above; decay recomputed honestly with `norm_num`
via the exact `M5846006549323611672814739330865132078623730171904_rpow_eq`; tightest honest
`T = 3/302231454903657293676544` for this root). -/
theorem r_5846006549323611672814739330865132078623730171904_le :
    (12 : ℝ) * ((((((5846006549323611672814739330865132078623730171904 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 302231454903657293676544 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((5846006549323611672814739330865132078623730171904 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M5846006549323611672814739330865132078623730171904_rpow_eq
  have hrw : ((((5846006549323611672814739330865132078623730171904 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((5846006549323611672814739330865132078623730171904 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((2417851639229258349412352 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 302231454903657293676544 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 5846006549323611672814739330865132078623730171904`
(`‖G - S11692013098647223345629478661730264157247460343808‖ ≤ 3/302231454903657293676544`; exact shape mirror of
`eta_tail_1461501637330902918203684832716283019655932542976_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_5846006549323611672814739330865132078623730171904_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 5846006549323611672814739330865132078623730171904), etaDirichletTerm s k)‖ ≤
      (3 / 302231454903657293676544 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 5846006549323611672814739330865132078623730171904 (by norm_num)
  have h2M : 2 * 5846006549323611672814739330865132078623730171904 = 11692013098647223345629478661730264157247460343808 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_5846006549323611672814739330865132078623730171904_le
  linarith

/-- The `M = 5846006549323611672814739330865132078623730171904` constant honestly improves on the banked
`M = 2923003274661805836407369665432566039311865085952` constant
(`3/302231454903657293676544 < 24/1709679278759123458457600`). -/
theorem tail_5846006549323611672814739330865132078623730171904_lt_2923003274661805836407369665432566039311865085952 : (3 / 302231454903657293676544 : ℝ) < (24 / 1709679278759123458457600 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 11692013098647223345629478661730264157247460343808` tail
(`3419358557518246916915200 ≤ 11692013098647223345629478661730264157247460343808^{1/2}`;
generic mirror of `M2923003274661805836407369665432566039311865085952_rpow_ge` above and latest exact
`M5846006549323611672814739330865132078623730171904_rpow_eq` above; honest floor via
`3419358557518246916915200^2 = 11692012944873266309254294193624910211883991040000 ≤
11692013098647223345629478661730264157247460343808` by `norm_num`;
doubling pattern `3419358557518246916915200 = 2 * 1709679278759123458457600`;
`11692013098647223345629478661730264157247460343808 = 2^163` so root `2^81·√2` is NOT exact,
unlike `5846006549323611672814739330865132078623730171904`). -/
theorem M11692013098647223345629478661730264157247460343808_rpow_ge :
    (3419358557518246916915200 : ℝ) ≤ ((((11692013098647223345629478661730264157247460343808 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((3419358557518246916915200 : ℝ) ^ (2 : ℕ)) ≤ ((((11692013098647223345629478661730264157247460343808 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((11692013098647223345629478661730264157247460343808 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((11692013098647223345629478661730264157247460343808 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 11692013098647223345629478661730264157247460343808` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/3419358557518246916915200`; generic mirror of
`r_2923003274661805836407369665432566039311865085952_le` above and latest exact
`r_5846006549323611672814739330865132078623730171904_le` above; decay recomputed honestly with
`norm_num` via `M11692013098647223345629478661730264157247460343808_rpow_ge`; tightest honest
`T = 24/3419358557518246916915200` for the `3419358557518246916915200` root lower). -/
theorem r_11692013098647223345629478661730264157247460343808_le :
    (12 : ℝ) * ((((((11692013098647223345629478661730264157247460343808 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 3419358557518246916915200 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((11692013098647223345629478661730264157247460343808 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((11692013098647223345629478661730264157247460343808 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M11692013098647223345629478661730264157247460343808_rpow_ge
  have hrw : ((((11692013098647223345629478661730264157247460343808 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((11692013098647223345629478661730264157247460343808 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((11692013098647223345629478661730264157247460343808 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (3419358557518246916915200 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((11692013098647223345629478661730264157247460343808 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (3419358557518246916915200 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((11692013098647223345629478661730264157247460343808 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((3419358557518246916915200 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((3419358557518246916915200 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 3419358557518246916915200 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 11692013098647223345629478661730264157247460343808`
(`‖G - S23384026197294446691258957323460528314494920687616‖ ≤ 24/3419358557518246916915200`; generic mirror
of `eta_tail_2923003274661805836407369665432566039311865085952_le` above and latest exact
`eta_tail_5846006549323611672814739330865132078623730171904_le` above — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_11692013098647223345629478661730264157247460343808_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 11692013098647223345629478661730264157247460343808), etaDirichletTerm s k)‖ ≤
      (24 / 3419358557518246916915200 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 11692013098647223345629478661730264157247460343808 (by norm_num)
  have h2M : 2 * 11692013098647223345629478661730264157247460343808 = 23384026197294446691258957323460528314494920687616 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_11692013098647223345629478661730264157247460343808_le
  linarith

/-- The `M = 11692013098647223345629478661730264157247460343808` constant honestly improves on the banked
`M = 5846006549323611672814739330865132078623730171904` constant
(`24/3419358557518246916915200 < 3/302231454903657293676544`). -/
theorem tail_11692013098647223345629478661730264157247460343808_lt_5846006549323611672814739330865132078623730171904 : (24 / 3419358557518246916915200 : ℝ) < (3 / 302231454903657293676544 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 23384026197294446691258957323460528314494920687616` tail
(`23384026197294446691258957323460528314494920687616^{1/2} = 4835703278458516698824704` exact; exact shape mirror of
`M5846006549323611672814739330865132078623730171904_rpow_eq` above and latest odd-floor
`M11692013098647223345629478661730264157247460343808_rpow_ge` above; honest via
`4835703278458516698824704^2 = 23384026197294446691258957323460528314494920687616` by `norm_num`;
`23384026197294446691258957323460528314494920687616 = 2^164` so the root is exact, unlike
`11692013098647223345629478661730264157247460343808`). -/
theorem M23384026197294446691258957323460528314494920687616_rpow_eq :
    ((((23384026197294446691258957323460528314494920687616 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (4835703278458516698824704 : ℝ) := by
  have hx2 : ((((((23384026197294446691258957323460528314494920687616 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((23384026197294446691258957323460528314494920687616 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((4835703278458516698824704 : ℝ) ^ (2 : ℕ)) = ((((23384026197294446691258957323460528314494920687616 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((23384026197294446691258957323460528314494920687616 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (4835703278458516698824704 : ℝ) := by norm_num
  have hle1 : ((((((23384026197294446691258957323460528314494920687616 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((4835703278458516698824704 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((4835703278458516698824704 : ℝ) ^ (2 : ℕ)) ≤
      ((((((23384026197294446691258957323460528314494920687616 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 23384026197294446691258957323460528314494920687616` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/4835703278458516698824704 = 3/604462909807314587353088`; exact shape mirror of
`r_5846006549323611672814739330865132078623730171904_le` above; decay recomputed honestly with `norm_num`
via the exact `M23384026197294446691258957323460528314494920687616_rpow_eq`; tightest honest
`T = 3/604462909807314587353088` for this root). -/
theorem r_23384026197294446691258957323460528314494920687616_le :
    (12 : ℝ) * ((((((23384026197294446691258957323460528314494920687616 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 604462909807314587353088 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((23384026197294446691258957323460528314494920687616 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M23384026197294446691258957323460528314494920687616_rpow_eq
  have hrw : ((((23384026197294446691258957323460528314494920687616 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((23384026197294446691258957323460528314494920687616 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((4835703278458516698824704 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 604462909807314587353088 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 23384026197294446691258957323460528314494920687616`
(`‖G - S46768052394588893382517914646921056628989841375232‖ ≤ 3/604462909807314587353088`; exact shape mirror of
`eta_tail_5846006549323611672814739330865132078623730171904_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_23384026197294446691258957323460528314494920687616_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 23384026197294446691258957323460528314494920687616), etaDirichletTerm s k)‖ ≤
      (3 / 604462909807314587353088 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 23384026197294446691258957323460528314494920687616 (by norm_num)
  have h2M : 2 * 23384026197294446691258957323460528314494920687616 = 46768052394588893382517914646921056628989841375232 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_23384026197294446691258957323460528314494920687616_le
  linarith

/-- The `M = 23384026197294446691258957323460528314494920687616` constant honestly improves on the banked
`M = 11692013098647223345629478661730264157247460343808` constant
(`3/604462909807314587353088 < 24/3419358557518246916915200`). -/
theorem tail_23384026197294446691258957323460528314494920687616_lt_11692013098647223345629478661730264157247460343808 : (3 / 604462909807314587353088 : ℝ) < (24 / 3419358557518246916915200 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 46768052394588893382517914646921056628989841375232` tail
(`6838717115036493833830400 ≤ 46768052394588893382517914646921056628989841375232^{1/2}`;
generic mirror of `M11692013098647223345629478661730264157247460343808_rpow_ge` above and latest exact
`M23384026197294446691258957323460528314494920687616_rpow_eq` above; honest floor via
`6838717115036493833830400^2 = 46768051779493065237017176774499640847535964160000 ≤
46768052394588893382517914646921056628989841375232` by `norm_num`;
doubling pattern `6838717115036493833830400 = 2 * 3419358557518246916915200`;
`46768052394588893382517914646921056628989841375232 = 2^165` so root `2^82·√2` is NOT exact,
unlike `23384026197294446691258957323460528314494920687616`). -/
theorem M46768052394588893382517914646921056628989841375232_rpow_ge :
    (6838717115036493833830400 : ℝ) ≤ ((((46768052394588893382517914646921056628989841375232 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((6838717115036493833830400 : ℝ) ^ (2 : ℕ)) ≤ ((((46768052394588893382517914646921056628989841375232 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((46768052394588893382517914646921056628989841375232 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((46768052394588893382517914646921056628989841375232 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 46768052394588893382517914646921056628989841375232` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/6838717115036493833830400`; generic mirror of
`r_11692013098647223345629478661730264157247460343808_le` above and latest exact
`r_23384026197294446691258957323460528314494920687616_le` above; decay recomputed honestly with
`norm_num` via `M46768052394588893382517914646921056628989841375232_rpow_ge`; honest conservative
`T = 24/6838717115036493833830400` for the `6838717115036493833830400` root lower). -/
theorem r_46768052394588893382517914646921056628989841375232_le :
    (12 : ℝ) * ((((((46768052394588893382517914646921056628989841375232 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 6838717115036493833830400 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((46768052394588893382517914646921056628989841375232 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((46768052394588893382517914646921056628989841375232 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M46768052394588893382517914646921056628989841375232_rpow_ge
  have hrw : ((((46768052394588893382517914646921056628989841375232 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((46768052394588893382517914646921056628989841375232 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((46768052394588893382517914646921056628989841375232 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (6838717115036493833830400 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((46768052394588893382517914646921056628989841375232 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (6838717115036493833830400 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((46768052394588893382517914646921056628989841375232 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((6838717115036493833830400 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((6838717115036493833830400 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 6838717115036493833830400 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 46768052394588893382517914646921056628989841375232`
(`‖G - S93536104789177786765035829293842113257979682750464‖ ≤ 24/6838717115036493833830400`; generic mirror
of `eta_tail_11692013098647223345629478661730264157247460343808_le` above and latest exact
`eta_tail_23384026197294446691258957323460528314494920687616_le` above — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_46768052394588893382517914646921056628989841375232_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 46768052394588893382517914646921056628989841375232), etaDirichletTerm s k)‖ ≤
      (24 / 6838717115036493833830400 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 46768052394588893382517914646921056628989841375232 (by norm_num)
  have h2M : 2 * 46768052394588893382517914646921056628989841375232 = 93536104789177786765035829293842113257979682750464 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_46768052394588893382517914646921056628989841375232_le
  linarith

/-- The `M = 46768052394588893382517914646921056628989841375232` constant honestly improves on the banked
`M = 23384026197294446691258957323460528314494920687616` constant
(`24/6838717115036493833830400 < 3/604462909807314587353088`). -/
theorem tail_46768052394588893382517914646921056628989841375232_lt_23384026197294446691258957323460528314494920687616 : (24 / 6838717115036493833830400 : ℝ) < (3 / 604462909807314587353088 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 93536104789177786765035829293842113257979682750464` tail
(`93536104789177786765035829293842113257979682750464^{1/2} = 9671406556917033397649408` exact; exact shape mirror of
`M23384026197294446691258957323460528314494920687616_rpow_eq` above and latest odd-floor
`M46768052394588893382517914646921056628989841375232_rpow_ge` above; honest via
`9671406556917033397649408^2 = 93536104789177786765035829293842113257979682750464` by `norm_num`;
`93536104789177786765035829293842113257979682750464 = 2^166` so the root is exact, unlike
`46768052394588893382517914646921056628989841375232`). -/
theorem M93536104789177786765035829293842113257979682750464_rpow_eq :
    ((((93536104789177786765035829293842113257979682750464 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (9671406556917033397649408 : ℝ) := by
  have hx2 : ((((((93536104789177786765035829293842113257979682750464 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((93536104789177786765035829293842113257979682750464 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((9671406556917033397649408 : ℝ) ^ (2 : ℕ)) = ((((93536104789177786765035829293842113257979682750464 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((93536104789177786765035829293842113257979682750464 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (9671406556917033397649408 : ℝ) := by norm_num
  have hle1 : ((((((93536104789177786765035829293842113257979682750464 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((9671406556917033397649408 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((9671406556917033397649408 : ℝ) ^ (2 : ℕ)) ≤
      ((((((93536104789177786765035829293842113257979682750464 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 93536104789177786765035829293842113257979682750464` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/9671406556917033397649408 = 3/1208925819614629174706176`; exact shape mirror of
`r_23384026197294446691258957323460528314494920687616_le` above; decay recomputed honestly with `norm_num`
via the exact `M93536104789177786765035829293842113257979682750464_rpow_eq`; tightest honest
`T = 3/1208925819614629174706176` for this root). -/
theorem r_93536104789177786765035829293842113257979682750464_le :
    (12 : ℝ) * ((((((93536104789177786765035829293842113257979682750464 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 1208925819614629174706176 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((93536104789177786765035829293842113257979682750464 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M93536104789177786765035829293842113257979682750464_rpow_eq
  have hrw : ((((93536104789177786765035829293842113257979682750464 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((93536104789177786765035829293842113257979682750464 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((9671406556917033397649408 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 1208925819614629174706176 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 93536104789177786765035829293842113257979682750464`
(`‖G - S187072209578355573530071658587684226515959365500928‖ ≤ 3/1208925819614629174706176`; exact shape mirror of
`eta_tail_23384026197294446691258957323460528314494920687616_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_93536104789177786765035829293842113257979682750464_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 93536104789177786765035829293842113257979682750464), etaDirichletTerm s k)‖ ≤
      (3 / 1208925819614629174706176 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 93536104789177786765035829293842113257979682750464 (by norm_num)
  have h2M : 2 * 93536104789177786765035829293842113257979682750464 = 187072209578355573530071658587684226515959365500928 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_93536104789177786765035829293842113257979682750464_le
  linarith

/-- The `M = 93536104789177786765035829293842113257979682750464` constant honestly improves on the banked
`M = 46768052394588893382517914646921056628989841375232` constant
(`3/1208925819614629174706176 < 24/6838717115036493833830400`). -/
theorem tail_93536104789177786765035829293842113257979682750464_lt_46768052394588893382517914646921056628989841375232 : (3 / 1208925819614629174706176 : ℝ) < (24 / 6838717115036493833830400 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 187072209578355573530071658587684226515959365500928` tail
(`13677434230072987667660800 ≤ 187072209578355573530071658587684226515959365500928^{1/2}`;
generic mirror of `M46768052394588893382517914646921056628989841375232_rpow_ge` above and latest exact
`M93536104789177786765035829293842113257979682750464_rpow_eq` above; honest floor via
`13677434230072987667660800^2 = 187072207117972260948068707097998563390143856640000 ≤
187072209578355573530071658587684226515959365500928` by `norm_num`;
doubling pattern `13677434230072987667660800 = 2 * 6838717115036493833830400`;
`187072209578355573530071658587684226515959365500928 = 2^167` so root `2^83·√2` is NOT exact,
unlike `93536104789177786765035829293842113257979682750464`). -/
theorem M187072209578355573530071658587684226515959365500928_rpow_ge :
    (13677434230072987667660800 : ℝ) ≤ ((((187072209578355573530071658587684226515959365500928 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((13677434230072987667660800 : ℝ) ^ (2 : ℕ)) ≤ ((((187072209578355573530071658587684226515959365500928 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((187072209578355573530071658587684226515959365500928 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((187072209578355573530071658587684226515959365500928 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 187072209578355573530071658587684226515959365500928` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/13677434230072987667660800`; generic mirror of
`r_46768052394588893382517914646921056628989841375232_le` above and latest exact
`r_93536104789177786765035829293842113257979682750464_le` above; decay recomputed honestly with
`norm_num` via `M187072209578355573530071658587684226515959365500928_rpow_ge`; honest conservative
`T = 24/13677434230072987667660800` for the `13677434230072987667660800` root lower). -/
theorem r_187072209578355573530071658587684226515959365500928_le :
    (12 : ℝ) * ((((((187072209578355573530071658587684226515959365500928 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 13677434230072987667660800 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((187072209578355573530071658587684226515959365500928 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((187072209578355573530071658587684226515959365500928 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M187072209578355573530071658587684226515959365500928_rpow_ge
  have hrw : ((((187072209578355573530071658587684226515959365500928 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((187072209578355573530071658587684226515959365500928 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((187072209578355573530071658587684226515959365500928 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (13677434230072987667660800 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((187072209578355573530071658587684226515959365500928 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (13677434230072987667660800 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((187072209578355573530071658587684226515959365500928 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((13677434230072987667660800 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((13677434230072987667660800 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 13677434230072987667660800 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 187072209578355573530071658587684226515959365500928`
(`‖G - S374144419156711147060143317175368453031918731001856‖ ≤ 24/13677434230072987667660800`; generic mirror
of `eta_tail_46768052394588893382517914646921056628989841375232_le` above and latest exact
`eta_tail_93536104789177786765035829293842113257979682750464_le` above — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_187072209578355573530071658587684226515959365500928_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 187072209578355573530071658587684226515959365500928), etaDirichletTerm s k)‖ ≤
      (24 / 13677434230072987667660800 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 187072209578355573530071658587684226515959365500928 (by norm_num)
  have h2M : 2 * 187072209578355573530071658587684226515959365500928 = 374144419156711147060143317175368453031918731001856 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_187072209578355573530071658587684226515959365500928_le
  linarith

/-- The `M = 187072209578355573530071658587684226515959365500928` constant honestly improves on the banked
`M = 93536104789177786765035829293842113257979682750464` constant
(`24/13677434230072987667660800 < 3/1208925819614629174706176`). -/
theorem tail_187072209578355573530071658587684226515959365500928_lt_93536104789177786765035829293842113257979682750464 : (24 / 13677434230072987667660800 : ℝ) < (3 / 1208925819614629174706176 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 374144419156711147060143317175368453031918731001856` tail
(`374144419156711147060143317175368453031918731001856^{1/2} = 19342813113834066795298816` exact; exact shape mirror of
`M93536104789177786765035829293842113257979682750464_rpow_eq` above and latest odd-floor
`M187072209578355573530071658587684226515959365500928_rpow_ge` above; honest via
`19342813113834066795298816^2 = 374144419156711147060143317175368453031918731001856` by `norm_num`;
`374144419156711147060143317175368453031918731001856 = 2^168` so the root is exact, unlike
`187072209578355573530071658587684226515959365500928`). -/
theorem M374144419156711147060143317175368453031918731001856_rpow_eq :
    ((((374144419156711147060143317175368453031918731001856 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (19342813113834066795298816 : ℝ) := by
  have hx2 : ((((((374144419156711147060143317175368453031918731001856 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((374144419156711147060143317175368453031918731001856 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((19342813113834066795298816 : ℝ) ^ (2 : ℕ)) = ((((374144419156711147060143317175368453031918731001856 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((374144419156711147060143317175368453031918731001856 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (19342813113834066795298816 : ℝ) := by norm_num
  have hle1 : ((((((374144419156711147060143317175368453031918731001856 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((19342813113834066795298816 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((19342813113834066795298816 : ℝ) ^ (2 : ℕ)) ≤
      ((((((374144419156711147060143317175368453031918731001856 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 374144419156711147060143317175368453031918731001856` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/19342813113834066795298816 = 3/2417851639229258349412352`; exact shape mirror of
`r_93536104789177786765035829293842113257979682750464_le` above; decay recomputed honestly with `norm_num`
via the exact `M374144419156711147060143317175368453031918731001856_rpow_eq`; tightest honest
`T = 3/2417851639229258349412352` for this root). -/
theorem r_374144419156711147060143317175368453031918731001856_le :
    (12 : ℝ) * ((((((374144419156711147060143317175368453031918731001856 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 2417851639229258349412352 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((374144419156711147060143317175368453031918731001856 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M374144419156711147060143317175368453031918731001856_rpow_eq
  have hrw : ((((374144419156711147060143317175368453031918731001856 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((374144419156711147060143317175368453031918731001856 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((19342813113834066795298816 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 2417851639229258349412352 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 374144419156711147060143317175368453031918731001856`
(`‖G - S748288838313422294120286634350736906063837462003712‖ ≤ 3/2417851639229258349412352`; exact shape mirror of
`eta_tail_93536104789177786765035829293842113257979682750464_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_374144419156711147060143317175368453031918731001856_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 374144419156711147060143317175368453031918731001856), etaDirichletTerm s k)‖ ≤
      (3 / 2417851639229258349412352 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 374144419156711147060143317175368453031918731001856 (by norm_num)
  have h2M : 2 * 374144419156711147060143317175368453031918731001856 = 748288838313422294120286634350736906063837462003712 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_374144419156711147060143317175368453031918731001856_le
  linarith

/-- The `M = 374144419156711147060143317175368453031918731001856` constant honestly improves on the banked
`M = 187072209578355573530071658587684226515959365500928` constant
(`3/2417851639229258349412352 < 24/13677434230072987667660800`). -/
theorem tail_374144419156711147060143317175368453031918731001856_lt_187072209578355573530071658587684226515959365500928 : (3 / 2417851639229258349412352 : ℝ) < (24 / 13677434230072987667660800 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 748288838313422294120286634350736906063837462003712` tail
(`27354868460145975335321600 ≤ 748288838313422294120286634350736906063837462003712^{1/2}`;
generic mirror of `M187072209578355573530071658587684226515959365500928_rpow_ge` above and latest exact
`M374144419156711147060143317175368453031918731001856_rpow_eq` above; honest floor via
`27354868460145975335321600^2 = 748288828471889043792274828391994253560575426560000 ≤
748288838313422294120286634350736906063837462003712` by `norm_num`;
doubling pattern `27354868460145975335321600 = 2 * 13677434230072987667660800`;
`748288838313422294120286634350736906063837462003712 = 2^169` so root `2^84·√2` is NOT exact,
unlike `374144419156711147060143317175368453031918731001856`). -/
theorem M748288838313422294120286634350736906063837462003712_rpow_ge :
    (27354868460145975335321600 : ℝ) ≤ ((((748288838313422294120286634350736906063837462003712 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((27354868460145975335321600 : ℝ) ^ (2 : ℕ)) ≤ ((((748288838313422294120286634350736906063837462003712 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((748288838313422294120286634350736906063837462003712 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((748288838313422294120286634350736906063837462003712 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 748288838313422294120286634350736906063837462003712` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/27354868460145975335321600`; generic mirror of
`r_187072209578355573530071658587684226515959365500928_le` above and latest exact
`r_374144419156711147060143317175368453031918731001856_le` above; decay recomputed honestly with
`norm_num` via `M748288838313422294120286634350736906063837462003712_rpow_ge`; honest conservative
`T = 24/27354868460145975335321600` for the `27354868460145975335321600` root lower). -/
theorem r_748288838313422294120286634350736906063837462003712_le :
    (12 : ℝ) * ((((((748288838313422294120286634350736906063837462003712 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 27354868460145975335321600 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((748288838313422294120286634350736906063837462003712 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((748288838313422294120286634350736906063837462003712 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M748288838313422294120286634350736906063837462003712_rpow_ge
  have hrw : ((((748288838313422294120286634350736906063837462003712 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((748288838313422294120286634350736906063837462003712 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((748288838313422294120286634350736906063837462003712 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (27354868460145975335321600 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((748288838313422294120286634350736906063837462003712 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (27354868460145975335321600 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((748288838313422294120286634350736906063837462003712 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((27354868460145975335321600 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((27354868460145975335321600 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 27354868460145975335321600 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 748288838313422294120286634350736906063837462003712`
(`‖G - S1496577676626844588240573268701473812127674924007424‖ ≤ 24/27354868460145975335321600`; generic mirror
of `eta_tail_187072209578355573530071658587684226515959365500928_le` above and latest exact
`eta_tail_374144419156711147060143317175368453031918731001856_le` above — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_748288838313422294120286634350736906063837462003712_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 748288838313422294120286634350736906063837462003712), etaDirichletTerm s k)‖ ≤
      (24 / 27354868460145975335321600 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 748288838313422294120286634350736906063837462003712 (by norm_num)
  have h2M : 2 * 748288838313422294120286634350736906063837462003712 = 1496577676626844588240573268701473812127674924007424 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_748288838313422294120286634350736906063837462003712_le
  linarith

/-- The `M = 748288838313422294120286634350736906063837462003712` constant honestly improves on the banked
`M = 374144419156711147060143317175368453031918731001856` constant
(`24/27354868460145975335321600 < 3/2417851639229258349412352`). -/
theorem tail_748288838313422294120286634350736906063837462003712_lt_374144419156711147060143317175368453031918731001856 : (24 / 27354868460145975335321600 : ℝ) < (3 / 2417851639229258349412352 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 1496577676626844588240573268701473812127674924007424` tail
(`1496577676626844588240573268701473812127674924007424^{1/2} = 38685626227668133590597632` exact; exact shape mirror of
`M374144419156711147060143317175368453031918731001856_rpow_eq` above and latest odd-floor
`M748288838313422294120286634350736906063837462003712_rpow_ge` above; honest via
`38685626227668133590597632^2 = 1496577676626844588240573268701473812127674924007424` by `norm_num`;
`1496577676626844588240573268701473812127674924007424 = 2^170` so the root is exact, unlike
`748288838313422294120286634350736906063837462003712`). -/
theorem M1496577676626844588240573268701473812127674924007424_rpow_eq :
    ((((1496577676626844588240573268701473812127674924007424 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (38685626227668133590597632 : ℝ) := by
  have hx2 : ((((((1496577676626844588240573268701473812127674924007424 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((1496577676626844588240573268701473812127674924007424 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((38685626227668133590597632 : ℝ) ^ (2 : ℕ)) = ((((1496577676626844588240573268701473812127674924007424 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((1496577676626844588240573268701473812127674924007424 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (38685626227668133590597632 : ℝ) := by norm_num
  have hle1 : ((((((1496577676626844588240573268701473812127674924007424 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((38685626227668133590597632 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((38685626227668133590597632 : ℝ) ^ (2 : ℕ)) ≤
      ((((((1496577676626844588240573268701473812127674924007424 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 1496577676626844588240573268701473812127674924007424` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/38685626227668133590597632 = 3/4835703278458516698824704`; exact shape mirror of
`r_374144419156711147060143317175368453031918731001856_le` above; decay recomputed honestly with `norm_num`
via the exact `M1496577676626844588240573268701473812127674924007424_rpow_eq`; tightest honest
`T = 3/4835703278458516698824704` for this root). -/
theorem r_1496577676626844588240573268701473812127674924007424_le :
    (12 : ℝ) * ((((((1496577676626844588240573268701473812127674924007424 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 4835703278458516698824704 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((1496577676626844588240573268701473812127674924007424 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M1496577676626844588240573268701473812127674924007424_rpow_eq
  have hrw : ((((1496577676626844588240573268701473812127674924007424 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((1496577676626844588240573268701473812127674924007424 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((38685626227668133590597632 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 4835703278458516698824704 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 1496577676626844588240573268701473812127674924007424`
(`‖G - S2993155353253689176481146537402947624255349848014848‖ ≤ 3/4835703278458516698824704`; exact shape mirror of
`eta_tail_374144419156711147060143317175368453031918731001856_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_1496577676626844588240573268701473812127674924007424_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 1496577676626844588240573268701473812127674924007424), etaDirichletTerm s k)‖ ≤
      (3 / 4835703278458516698824704 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1496577676626844588240573268701473812127674924007424 (by norm_num)
  have h2M : 2 * 1496577676626844588240573268701473812127674924007424 = 2993155353253689176481146537402947624255349848014848 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_1496577676626844588240573268701473812127674924007424_le
  linarith

/-- The `M = 1496577676626844588240573268701473812127674924007424` constant honestly improves on the banked
`M = 748288838313422294120286634350736906063837462003712` constant
(`3/4835703278458516698824704 < 24/27354868460145975335321600`). -/
theorem tail_1496577676626844588240573268701473812127674924007424_lt_748288838313422294120286634350736906063837462003712 : (3 / 4835703278458516698824704 : ℝ) < (24 / 27354868460145975335321600 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 2993155353253689176481146537402947624255349848014848` tail
(`54709736920291950670643200 ≤ 2993155353253689176481146537402947624255349848014848^{1/2}`;
generic mirror of `M748288838313422294120286634350736906063837462003712_rpow_ge` above and latest exact
`M1496577676626844588240573268701473812127674924007424_rpow_eq` above; honest floor via
`54709736920291950670643200^2 = 2993155313887556175169099313567977014242301706240000 ≤
2993155353253689176481146537402947624255349848014848` by `norm_num`;
doubling pattern `54709736920291950670643200 = 2 * 27354868460145975335321600`;
`2993155353253689176481146537402947624255349848014848 = 2^171` so root `2^85·√2` is NOT exact,
unlike `1496577676626844588240573268701473812127674924007424`). -/
theorem M2993155353253689176481146537402947624255349848014848_rpow_ge :
    (54709736920291950670643200 : ℝ) ≤ ((((2993155353253689176481146537402947624255349848014848 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((54709736920291950670643200 : ℝ) ^ (2 : ℕ)) ≤ ((((2993155353253689176481146537402947624255349848014848 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((2993155353253689176481146537402947624255349848014848 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((2993155353253689176481146537402947624255349848014848 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 2993155353253689176481146537402947624255349848014848` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/54709736920291950670643200`; generic mirror of
`r_748288838313422294120286634350736906063837462003712_le` above and latest exact
`r_1496577676626844588240573268701473812127674924007424_le` above; decay recomputed honestly with
`norm_num` via `M2993155353253689176481146537402947624255349848014848_rpow_ge`; honest conservative
`T = 24/54709736920291950670643200` for the `54709736920291950670643200` root lower). -/
theorem r_2993155353253689176481146537402947624255349848014848_le :
    (12 : ℝ) * ((((((2993155353253689176481146537402947624255349848014848 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 54709736920291950670643200 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((2993155353253689176481146537402947624255349848014848 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((2993155353253689176481146537402947624255349848014848 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M2993155353253689176481146537402947624255349848014848_rpow_ge
  have hrw : ((((2993155353253689176481146537402947624255349848014848 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((2993155353253689176481146537402947624255349848014848 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((2993155353253689176481146537402947624255349848014848 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (54709736920291950670643200 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((2993155353253689176481146537402947624255349848014848 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (54709736920291950670643200 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((2993155353253689176481146537402947624255349848014848 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((54709736920291950670643200 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((54709736920291950670643200 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 54709736920291950670643200 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 2993155353253689176481146537402947624255349848014848`
(`‖G - S5986310706507378352962293074805895248510699696029696‖ ≤ 24/54709736920291950670643200`; generic mirror
of `eta_tail_748288838313422294120286634350736906063837462003712_le` above and latest exact
`eta_tail_1496577676626844588240573268701473812127674924007424_le` above — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_2993155353253689176481146537402947624255349848014848_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 2993155353253689176481146537402947624255349848014848), etaDirichletTerm s k)‖ ≤
      (24 / 54709736920291950670643200 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 2993155353253689176481146537402947624255349848014848 (by norm_num)
  have h2M : 2 * 2993155353253689176481146537402947624255349848014848 = 5986310706507378352962293074805895248510699696029696 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_2993155353253689176481146537402947624255349848014848_le
  linarith

/-- The `M = 2993155353253689176481146537402947624255349848014848` constant honestly improves on the banked
`M = 1496577676626844588240573268701473812127674924007424` constant
(`24/54709736920291950670643200 < 3/4835703278458516698824704`). -/
theorem tail_2993155353253689176481146537402947624255349848014848_lt_1496577676626844588240573268701473812127674924007424 : (24 / 54709736920291950670643200 : ℝ) < (3 / 4835703278458516698824704 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 5986310706507378352962293074805895248510699696029696` tail
(`5986310706507378352962293074805895248510699696029696^{1/2} = 77371252455336267181195264` exact; exact shape mirror of
`M1496577676626844588240573268701473812127674924007424_rpow_eq` above and latest odd-floor
`M2993155353253689176481146537402947624255349848014848_rpow_ge` above; honest via
`77371252455336267181195264^2 = 5986310706507378352962293074805895248510699696029696` by `norm_num`;
`5986310706507378352962293074805895248510699696029696 = 2^172` so the root is exact, unlike
`2993155353253689176481146537402947624255349848014848`). -/
theorem M5986310706507378352962293074805895248510699696029696_rpow_eq :
    ((((5986310706507378352962293074805895248510699696029696 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (77371252455336267181195264 : ℝ) := by
  have hx2 : ((((((5986310706507378352962293074805895248510699696029696 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((5986310706507378352962293074805895248510699696029696 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((77371252455336267181195264 : ℝ) ^ (2 : ℕ)) = ((((5986310706507378352962293074805895248510699696029696 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((5986310706507378352962293074805895248510699696029696 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (77371252455336267181195264 : ℝ) := by norm_num
  have hle1 : ((((((5986310706507378352962293074805895248510699696029696 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((77371252455336267181195264 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((77371252455336267181195264 : ℝ) ^ (2 : ℕ)) ≤
      ((((((5986310706507378352962293074805895248510699696029696 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 5986310706507378352962293074805895248510699696029696` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/77371252455336267181195264 = 3/9671406556917033397649408`; exact shape mirror of
`r_1496577676626844588240573268701473812127674924007424_le` above; decay recomputed honestly with `norm_num`
via the exact `M5986310706507378352962293074805895248510699696029696_rpow_eq`; tightest honest
`T = 3/9671406556917033397649408` for this root). -/
theorem r_5986310706507378352962293074805895248510699696029696_le :
    (12 : ℝ) * ((((((5986310706507378352962293074805895248510699696029696 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 9671406556917033397649408 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((5986310706507378352962293074805895248510699696029696 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M5986310706507378352962293074805895248510699696029696_rpow_eq
  have hrw : ((((5986310706507378352962293074805895248510699696029696 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((5986310706507378352962293074805895248510699696029696 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((77371252455336267181195264 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 9671406556917033397649408 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 5986310706507378352962293074805895248510699696029696`
(`‖G - S11972621413014756705924586149611790497021399392059392‖ ≤ 3/9671406556917033397649408`; exact shape mirror of
`eta_tail_1496577676626844588240573268701473812127674924007424_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_5986310706507378352962293074805895248510699696029696_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 5986310706507378352962293074805895248510699696029696), etaDirichletTerm s k)‖ ≤
      (3 / 9671406556917033397649408 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 5986310706507378352962293074805895248510699696029696 (by norm_num)
  have h2M : 2 * 5986310706507378352962293074805895248510699696029696 = 11972621413014756705924586149611790497021399392059392 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_5986310706507378352962293074805895248510699696029696_le
  linarith

/-- The `M = 5986310706507378352962293074805895248510699696029696` constant honestly improves on the banked
`M = 2993155353253689176481146537402947624255349848014848` constant
(`3/9671406556917033397649408 < 24/54709736920291950670643200`). -/
theorem tail_5986310706507378352962293074805895248510699696029696_lt_2993155353253689176481146537402947624255349848014848 : (3 / 9671406556917033397649408 : ℝ) < (24 / 54709736920291950670643200 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 11972621413014756705924586149611790497021399392059392` tail
(`109419473840583901341286400 ≤ 11972621413014756705924586149611790497021399392059392^{1/2}`;
generic mirror of `M2993155353253689176481146537402947624255349848014848_rpow_ge` above and latest exact
`M5986310706507378352962293074805895248510699696029696_rpow_eq` above; honest floor via
`109419473840583901341286400^2 = 11972621255550224700676397254271908056969206824960000 ≤
11972621413014756705924586149611790497021399392059392` by `norm_num`;
doubling pattern `109419473840583901341286400 = 2 * 54709736920291950670643200`;
`11972621413014756705924586149611790497021399392059392 = 2^173` so root `2^86·√2` is NOT exact,
unlike `5986310706507378352962293074805895248510699696029696`). -/
theorem M11972621413014756705924586149611790497021399392059392_rpow_ge :
    (109419473840583901341286400 : ℝ) ≤ ((((11972621413014756705924586149611790497021399392059392 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((109419473840583901341286400 : ℝ) ^ (2 : ℕ)) ≤ ((((11972621413014756705924586149611790497021399392059392 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((11972621413014756705924586149611790497021399392059392 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((11972621413014756705924586149611790497021399392059392 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 11972621413014756705924586149611790497021399392059392` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/109419473840583901341286400`; generic mirror of
`r_2993155353253689176481146537402947624255349848014848_le` above and latest exact
`r_5986310706507378352962293074805895248510699696029696_le` above; decay recomputed honestly with
`norm_num` via `M11972621413014756705924586149611790497021399392059392_rpow_ge`; honest conservative
`T = 24/109419473840583901341286400` for the `109419473840583901341286400` root lower). -/
theorem r_11972621413014756705924586149611790497021399392059392_le :
    (12 : ℝ) * ((((((11972621413014756705924586149611790497021399392059392 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 109419473840583901341286400 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((11972621413014756705924586149611790497021399392059392 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((11972621413014756705924586149611790497021399392059392 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M11972621413014756705924586149611790497021399392059392_rpow_ge
  have hrw : ((((11972621413014756705924586149611790497021399392059392 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((11972621413014756705924586149611790497021399392059392 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((11972621413014756705924586149611790497021399392059392 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (109419473840583901341286400 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((11972621413014756705924586149611790497021399392059392 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (109419473840583901341286400 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((11972621413014756705924586149611790497021399392059392 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((109419473840583901341286400 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((109419473840583901341286400 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 109419473840583901341286400 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 11972621413014756705924586149611790497021399392059392`
(`‖G - S23945242826029513411849172299223580994042798784118784‖ ≤ 24/109419473840583901341286400`; generic mirror
of `eta_tail_2993155353253689176481146537402947624255349848014848_le` above and latest exact
`eta_tail_5986310706507378352962293074805895248510699696029696_le` above — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_11972621413014756705924586149611790497021399392059392_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 11972621413014756705924586149611790497021399392059392), etaDirichletTerm s k)‖ ≤
      (24 / 109419473840583901341286400 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 11972621413014756705924586149611790497021399392059392 (by norm_num)
  have h2M : 2 * 11972621413014756705924586149611790497021399392059392 = 23945242826029513411849172299223580994042798784118784 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_11972621413014756705924586149611790497021399392059392_le
  linarith

/-- The `M = 11972621413014756705924586149611790497021399392059392` constant honestly improves on the banked
`M = 5986310706507378352962293074805895248510699696029696` constant
(`24/109419473840583901341286400 < 3/9671406556917033397649408`). -/
theorem tail_11972621413014756705924586149611790497021399392059392_lt_5986310706507378352962293074805895248510699696029696 : (24 / 109419473840583901341286400 : ℝ) < (3 / 9671406556917033397649408 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 23945242826029513411849172299223580994042798784118784` tail
(`23945242826029513411849172299223580994042798784118784^{1/2} = 154742504910672534362390528` exact; exact shape mirror of
`M5986310706507378352962293074805895248510699696029696_rpow_eq` above and latest odd-floor
`M11972621413014756705924586149611790497021399392059392_rpow_ge` above; honest via
`154742504910672534362390528^2 = 23945242826029513411849172299223580994042798784118784` by `norm_num`;
`23945242826029513411849172299223580994042798784118784 = 2^174` so the root is exact, unlike
`11972621413014756705924586149611790497021399392059392`). -/
theorem M23945242826029513411849172299223580994042798784118784_rpow_eq :
    ((((23945242826029513411849172299223580994042798784118784 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (154742504910672534362390528 : ℝ) := by
  have hx2 : ((((((23945242826029513411849172299223580994042798784118784 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((23945242826029513411849172299223580994042798784118784 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((154742504910672534362390528 : ℝ) ^ (2 : ℕ)) = ((((23945242826029513411849172299223580994042798784118784 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((23945242826029513411849172299223580994042798784118784 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (154742504910672534362390528 : ℝ) := by norm_num
  have hle1 : ((((((23945242826029513411849172299223580994042798784118784 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((154742504910672534362390528 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((154742504910672534362390528 : ℝ) ^ (2 : ℕ)) ≤
      ((((((23945242826029513411849172299223580994042798784118784 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 23945242826029513411849172299223580994042798784118784` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/154742504910672534362390528 = 3/19342813113834066795298816`; exact shape mirror of
`r_5986310706507378352962293074805895248510699696029696_le` above; decay recomputed honestly with `norm_num`
via the exact `M23945242826029513411849172299223580994042798784118784_rpow_eq`; tightest honest
`T = 3/19342813113834066795298816` for this root). -/
theorem r_23945242826029513411849172299223580994042798784118784_le :
    (12 : ℝ) * ((((((23945242826029513411849172299223580994042798784118784 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 19342813113834066795298816 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((23945242826029513411849172299223580994042798784118784 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M23945242826029513411849172299223580994042798784118784_rpow_eq
  have hrw : ((((23945242826029513411849172299223580994042798784118784 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((23945242826029513411849172299223580994042798784118784 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((154742504910672534362390528 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 19342813113834066795298816 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 23945242826029513411849172299223580994042798784118784`
(`‖G - S47890485652059026823698344598447161988085597568237568‖ ≤ 3/19342813113834066795298816`; exact shape mirror of
`eta_tail_5986310706507378352962293074805895248510699696029696_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_23945242826029513411849172299223580994042798784118784_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 23945242826029513411849172299223580994042798784118784), etaDirichletTerm s k)‖ ≤
      (3 / 19342813113834066795298816 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 23945242826029513411849172299223580994042798784118784 (by norm_num)
  have h2M : 2 * 23945242826029513411849172299223580994042798784118784 = 47890485652059026823698344598447161988085597568237568 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_23945242826029513411849172299223580994042798784118784_le
  linarith

/-- The `M = 23945242826029513411849172299223580994042798784118784` constant honestly improves on the banked
`M = 11972621413014756705924586149611790497021399392059392` constant
(`3/19342813113834066795298816 < 24/109419473840583901341286400`). -/
theorem tail_23945242826029513411849172299223580994042798784118784_lt_11972621413014756705924586149611790497021399392059392 : (3 / 19342813113834066795298816 : ℝ) < (24 / 109419473840583901341286400 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 47890485652059026823698344598447161988085597568237568` tail
(`218838947681167802682572800 ≤ 47890485652059026823698344598447161988085597568237568^{1/2}`;
generic mirror of `M11972621413014756705924586149611790497021399392059392_rpow_ge` above and latest exact
`M23945242826029513411849172299223580994042798784118784_rpow_eq` above; honest floor via
`218838947681167802682572800^2 = 47890485022200898802705589017087632227876827299840000 ≤
47890485652059026823698344598447161988085597568237568` by `norm_num`;
`47890485652059026823698344598447161988085597568237568 = 2^175` so root `154742504910672534362390528·√2 ≈
218838949120258359057546633` is NOT exact, unlike `23945242826029513411849172299223580994042798784118784`;
conservative doubling `2 * 109419473840583901341286400 = 218838947681167802682572800` below the true floor
`218838949120258359057546633`; lower gap `629858128020992755581359529760208770268397568`). -/
theorem M47890485652059026823698344598447161988085597568237568_rpow_ge :
    (218838947681167802682572800 : ℝ) ≤ ((((47890485652059026823698344598447161988085597568237568 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((218838947681167802682572800 : ℝ) ^ (2 : ℕ)) ≤ ((((47890485652059026823698344598447161988085597568237568 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((47890485652059026823698344598447161988085597568237568 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((47890485652059026823698344598447161988085597568237568 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 47890485652059026823698344598447161988085597568237568` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/218838947681167802682572800`; generic mirror of
`r_11972621413014756705924586149611790497021399392059392_le` above and latest exact
`r_23945242826029513411849172299223580994042798784118784_le` above; decay recomputed honestly with
`norm_num` via `M47890485652059026823698344598447161988085597568237568_rpow_ge`; honest conservative
`T = 24/218838947681167802682572800` for the `218838947681167802682572800` root lower). -/
theorem r_47890485652059026823698344598447161988085597568237568_le :
    (12 : ℝ) * ((((((47890485652059026823698344598447161988085597568237568 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 218838947681167802682572800 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((47890485652059026823698344598447161988085597568237568 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((47890485652059026823698344598447161988085597568237568 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M47890485652059026823698344598447161988085597568237568_rpow_ge
  have hrw : ((((47890485652059026823698344598447161988085597568237568 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((47890485652059026823698344598447161988085597568237568 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((47890485652059026823698344598447161988085597568237568 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (218838947681167802682572800 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((47890485652059026823698344598447161988085597568237568 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (218838947681167802682572800 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((47890485652059026823698344598447161988085597568237568 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((218838947681167802682572800 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((218838947681167802682572800 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 218838947681167802682572800 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 47890485652059026823698344598447161988085597568237568`
(`‖G - S95780971304118053647396689196894323976171195136475136‖ ≤ 24/218838947681167802682572800`; generic mirror of
`eta_tail_11972621413014756705924586149611790497021399392059392_le` above and latest exact
`eta_tail_23945242826029513411849172299223580994042798784118784_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_47890485652059026823698344598447161988085597568237568_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 47890485652059026823698344598447161988085597568237568), etaDirichletTerm s k)‖ ≤
      (24 / 218838947681167802682572800 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 47890485652059026823698344598447161988085597568237568 (by norm_num)
  have h2M : 2 * 47890485652059026823698344598447161988085597568237568 = 95780971304118053647396689196894323976171195136475136 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_47890485652059026823698344598447161988085597568237568_le
  linarith

/-- The `M = 47890485652059026823698344598447161988085597568237568` constant honestly improves on the banked
`M = 23945242826029513411849172299223580994042798784118784` constant
(`24/218838947681167802682572800 < 3/19342813113834066795298816`). -/
theorem tail_47890485652059026823698344598447161988085597568237568_lt_23945242826029513411849172299223580994042798784118784 : (24 / 218838947681167802682572800 : ℝ) < (3 / 19342813113834066795298816 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 95780971304118053647396689196894323976171195136475136` tail
(`95780971304118053647396689196894323976171195136475136^{1/2} = 309485009821345068724781056` exact; exact shape mirror of
`M23945242826029513411849172299223580994042798784118784_rpow_eq` above and latest odd-floor
`M47890485652059026823698344598447161988085597568237568_rpow_ge` above; honest via
`309485009821345068724781056^2 = 95780971304118053647396689196894323976171195136475136` by `norm_num`;
`95780971304118053647396689196894323976171195136475136 = 2^176` so the root is exact, unlike
`47890485652059026823698344598447161988085597568237568`). -/
theorem M95780971304118053647396689196894323976171195136475136_rpow_eq :
    ((((95780971304118053647396689196894323976171195136475136 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (309485009821345068724781056 : ℝ) := by
  have hx2 : ((((((95780971304118053647396689196894323976171195136475136 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((95780971304118053647396689196894323976171195136475136 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((309485009821345068724781056 : ℝ) ^ (2 : ℕ)) = ((((95780971304118053647396689196894323976171195136475136 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((95780971304118053647396689196894323976171195136475136 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (309485009821345068724781056 : ℝ) := by norm_num
  have hle1 : ((((((95780971304118053647396689196894323976171195136475136 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((309485009821345068724781056 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((309485009821345068724781056 : ℝ) ^ (2 : ℕ)) ≤
      ((((((95780971304118053647396689196894323976171195136475136 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 95780971304118053647396689196894323976171195136475136` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/309485009821345068724781056 = 3/38685626227668133590597632`; exact shape mirror of
`r_23945242826029513411849172299223580994042798784118784_le` above; decay recomputed honestly with
`norm_num` via the exact `M95780971304118053647396689196894323976171195136475136_rpow_eq`; tightest honest
`T = 3/38685626227668133590597632` for this root). -/
theorem r_95780971304118053647396689196894323976171195136475136_le :
    (12 : ℝ) * ((((((95780971304118053647396689196894323976171195136475136 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 38685626227668133590597632 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((95780971304118053647396689196894323976171195136475136 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M95780971304118053647396689196894323976171195136475136_rpow_eq
  have hrw : ((((95780971304118053647396689196894323976171195136475136 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((95780971304118053647396689196894323976171195136475136 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((309485009821345068724781056 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 38685626227668133590597632 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 95780971304118053647396689196894323976171195136475136`
(`‖G - S191561942608236107294793378393788647952342390272950272‖ ≤ 3/38685626227668133590597632`; exact shape mirror of
`eta_tail_23945242826029513411849172299223580994042798784118784_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_95780971304118053647396689196894323976171195136475136_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 95780971304118053647396689196894323976171195136475136), etaDirichletTerm s k)‖ ≤
      (3 / 38685626227668133590597632 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 95780971304118053647396689196894323976171195136475136 (by norm_num)
  have h2M : 2 * 95780971304118053647396689196894323976171195136475136 = 191561942608236107294793378393788647952342390272950272 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_95780971304118053647396689196894323976171195136475136_le
  linarith

/-- The `M = 95780971304118053647396689196894323976171195136475136` constant honestly improves on the banked
`M = 47890485652059026823698344598447161988085597568237568` constant
(`3/38685626227668133590597632 < 24/218838947681167802682572800`). -/
theorem tail_95780971304118053647396689196894323976171195136475136_lt_47890485652059026823698344598447161988085597568237568 : (3 / 38685626227668133590597632 : ℝ) < (24 / 218838947681167802682572800 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 191561942608236107294793378393788647952342390272950272` tail
(`437677895362335605365145600 ≤ 191561942608236107294793378393788647952342390272950272^{1/2}`;
generic mirror of `M47890485652059026823698344598447161988085597568237568_rpow_ge` above and latest exact
`M95780971304118053647396689196894323976171195136475136_rpow_eq` above; honest floor via
`437677895362335605365145600^2 = 191561940088803595210822356068350528911507309199360000 ≤
191561942608236107294793378393788647952342390272950272` by `norm_num`;
`191561942608236107294793378393788647952342390272950272 = 2^177` so root `309485009821345068724781056·√2 ≈
437677898240516718115093267` is NOT exact, unlike `95780971304118053647396689196894323976171195136475136`;
conservative doubling `2 * 218838947681167802682572800 = 437677895362335605365145600` below the true floor
`437677898240516718115093267`; lower gap `2878181112749947667`). -/
theorem M191561942608236107294793378393788647952342390272950272_rpow_ge :
    (437677895362335605365145600 : ℝ) ≤ ((((191561942608236107294793378393788647952342390272950272 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((437677895362335605365145600 : ℝ) ^ (2 : ℕ)) ≤ ((((191561942608236107294793378393788647952342390272950272 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((191561942608236107294793378393788647952342390272950272 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((191561942608236107294793378393788647952342390272950272 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 191561942608236107294793378393788647952342390272950272` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/437677895362335605365145600`; generic mirror of
`r_47890485652059026823698344598447161988085597568237568_le` above and latest exact
`r_95780971304118053647396689196894323976171195136475136_le` above; decay recomputed honestly with
`norm_num` via `M191561942608236107294793378393788647952342390272950272_rpow_ge`; honest conservative
`T = 24/437677895362335605365145600` for the `437677895362335605365145600` root lower). -/
theorem r_191561942608236107294793378393788647952342390272950272_le :
    (12 : ℝ) * ((((((191561942608236107294793378393788647952342390272950272 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 437677895362335605365145600 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((191561942608236107294793378393788647952342390272950272 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((191561942608236107294793378393788647952342390272950272 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M191561942608236107294793378393788647952342390272950272_rpow_ge
  have hrw : ((((191561942608236107294793378393788647952342390272950272 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((191561942608236107294793378393788647952342390272950272 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((191561942608236107294793378393788647952342390272950272 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (437677895362335605365145600 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((191561942608236107294793378393788647952342390272950272 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (437677895362335605365145600 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((191561942608236107294793378393788647952342390272950272 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((437677895362335605365145600 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((437677895362335605365145600 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 437677895362335605365145600 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 191561942608236107294793378393788647952342390272950272`
(`‖G - S383123885216472214589586756787577295904684780545900544‖ ≤ 24/437677895362335605365145600`; generic mirror of
`eta_tail_47890485652059026823698344598447161988085597568237568_le` above and latest exact
`eta_tail_95780971304118053647396689196894323976171195136475136_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_191561942608236107294793378393788647952342390272950272_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 191561942608236107294793378393788647952342390272950272), etaDirichletTerm s k)‖ ≤
      (24 / 437677895362335605365145600 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 191561942608236107294793378393788647952342390272950272 (by norm_num)
  have h2M : 2 * 191561942608236107294793378393788647952342390272950272 = 383123885216472214589586756787577295904684780545900544 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_191561942608236107294793378393788647952342390272950272_le
  linarith

/-- The `M = 191561942608236107294793378393788647952342390272950272` constant honestly improves on the banked
`M = 95780971304118053647396689196894323976171195136475136` constant
(`24/437677895362335605365145600 < 3/38685626227668133590597632`). -/
theorem tail_191561942608236107294793378393788647952342390272950272_lt_95780971304118053647396689196894323976171195136475136 : (24 / 437677895362335605365145600 : ℝ) < (3 / 38685626227668133590597632 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 383123885216472214589586756787577295904684780545900544` tail
(`383123885216472214589586756787577295904684780545900544^{1/2} = 618970019642690137449562112` exact; exact shape mirror of
`M95780971304118053647396689196894323976171195136475136_rpow_eq` above and latest odd-floor
`M191561942608236107294793378393788647952342390272950272_rpow_ge` above; honest via
`618970019642690137449562112^2 = 383123885216472214589586756787577295904684780545900544` by `norm_num`;
`383123885216472214589586756787577295904684780545900544 = 2^178` so the root is exact, unlike
`191561942608236107294793378393788647952342390272950272`). -/
theorem M383123885216472214589586756787577295904684780545900544_rpow_eq :
    ((((383123885216472214589586756787577295904684780545900544 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (618970019642690137449562112 : ℝ) := by
  have hx2 : ((((((383123885216472214589586756787577295904684780545900544 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((383123885216472214589586756787577295904684780545900544 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((618970019642690137449562112 : ℝ) ^ (2 : ℕ)) = ((((383123885216472214589586756787577295904684780545900544 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((383123885216472214589586756787577295904684780545900544 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (618970019642690137449562112 : ℝ) := by norm_num
  have hle1 : ((((((383123885216472214589586756787577295904684780545900544 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((618970019642690137449562112 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((618970019642690137449562112 : ℝ) ^ (2 : ℕ)) ≤
      ((((((383123885216472214589586756787577295904684780545900544 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 383123885216472214589586756787577295904684780545900544` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/618970019642690137449562112 = 3/77371252455336267181195264`; exact shape mirror of
`r_95780971304118053647396689196894323976171195136475136_le` above; decay recomputed honestly with
`norm_num` via the exact `M383123885216472214589586756787577295904684780545900544_rpow_eq`; tightest honest
`T = 3/77371252455336267181195264` for this root). -/
theorem r_383123885216472214589586756787577295904684780545900544_le :
    (12 : ℝ) * ((((((383123885216472214589586756787577295904684780545900544 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 77371252455336267181195264 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((383123885216472214589586756787577295904684780545900544 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M383123885216472214589586756787577295904684780545900544_rpow_eq
  have hrw : ((((383123885216472214589586756787577295904684780545900544 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((383123885216472214589586756787577295904684780545900544 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((618970019642690137449562112 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 77371252455336267181195264 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 383123885216472214589586756787577295904684780545900544`
(`‖G - S766247770432944429179173513575154591809369561091801088‖ ≤ 3/77371252455336267181195264`; exact shape mirror of
`eta_tail_95780971304118053647396689196894323976171195136475136_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_383123885216472214589586756787577295904684780545900544_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 383123885216472214589586756787577295904684780545900544), etaDirichletTerm s k)‖ ≤
      (3 / 77371252455336267181195264 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 383123885216472214589586756787577295904684780545900544 (by norm_num)
  have h2M : 2 * 383123885216472214589586756787577295904684780545900544 = 766247770432944429179173513575154591809369561091801088 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_383123885216472214589586756787577295904684780545900544_le
  linarith

/-- The `M = 383123885216472214589586756787577295904684780545900544` constant honestly improves on the banked
`M = 191561942608236107294793378393788647952342390272950272` constant
(`3/77371252455336267181195264 < 24/437677895362335605365145600`). -/
theorem tail_383123885216472214589586756787577295904684780545900544_lt_191561942608236107294793378393788647952342390272950272 : (3 / 77371252455336267181195264 : ℝ) < (24 / 437677895362335605365145600 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 766247770432944429179173513575154591809369561091801088` tail
(`875355790724671210730291200 ≤ 766247770432944429179173513575154591809369561091801088^{1/2}`;
generic mirror of `M191561942608236107294793378393788647952342390272950272_rpow_ge` above and latest exact
`M383123885216472214589586756787577295904684780545900544_rpow_eq` above; honest floor via
`875355790724671210730291200^2 = 766247760355214380843289424273402115646029236797440000 ≤
766247770432944429179173513575154591809369561091801088` by `norm_num`;
`766247770432944429179173513575154591809369561091801088 = 2^179` so root `618970019642690137449562112·√2 ≈
875355796481033436230186534` is NOT exact, unlike `383123885216472214589586756787577295904684780545900544`;
conservative doubling `2 * 437677895362335605365145600 = 875355790724671210730291200` below the true floor
`875355796481033436230186534`; lower gap `5756362225499895334`). -/
theorem M766247770432944429179173513575154591809369561091801088_rpow_ge :
    (875355790724671210730291200 : ℝ) ≤ ((((766247770432944429179173513575154591809369561091801088 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((875355790724671210730291200 : ℝ) ^ (2 : ℕ)) ≤ ((((766247770432944429179173513575154591809369561091801088 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((766247770432944429179173513575154591809369561091801088 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((766247770432944429179173513575154591809369561091801088 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 766247770432944429179173513575154591809369561091801088` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/875355790724671210730291200`; generic mirror of
`r_191561942608236107294793378393788647952342390272950272_le` above and latest exact
`r_383123885216472214589586756787577295904684780545900544_le` above; decay recomputed honestly with
`norm_num` via `M766247770432944429179173513575154591809369561091801088_rpow_ge`; honest conservative
`T = 24/875355790724671210730291200` for the `875355790724671210730291200` root lower). -/
theorem r_766247770432944429179173513575154591809369561091801088_le :
    (12 : ℝ) * ((((((766247770432944429179173513575154591809369561091801088 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 875355790724671210730291200 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((766247770432944429179173513575154591809369561091801088 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((766247770432944429179173513575154591809369561091801088 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M766247770432944429179173513575154591809369561091801088_rpow_ge
  have hrw : ((((766247770432944429179173513575154591809369561091801088 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((766247770432944429179173513575154591809369561091801088 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((766247770432944429179173513575154591809369561091801088 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (875355790724671210730291200 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((766247770432944429179173513575154591809369561091801088 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (875355790724671210730291200 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((766247770432944429179173513575154591809369561091801088 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((875355790724671210730291200 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((875355790724671210730291200 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 875355790724671210730291200 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 766247770432944429179173513575154591809369561091801088`
(`‖G - S1532495540865888858358347027150309183618739122183602176‖ ≤ 24/875355790724671210730291200`; generic mirror of
`eta_tail_191561942608236107294793378393788647952342390272950272_le` above and latest exact
`eta_tail_383123885216472214589586756787577295904684780545900544_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_766247770432944429179173513575154591809369561091801088_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 766247770432944429179173513575154591809369561091801088), etaDirichletTerm s k)‖ ≤
      (24 / 875355790724671210730291200 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 766247770432944429179173513575154591809369561091801088 (by norm_num)
  have h2M : 2 * 766247770432944429179173513575154591809369561091801088 = 1532495540865888858358347027150309183618739122183602176 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_766247770432944429179173513575154591809369561091801088_le
  linarith

/-- The `M = 766247770432944429179173513575154591809369561091801088` constant honestly improves on the banked
`M = 383123885216472214589586756787577295904684780545900544` constant
(`24/875355790724671210730291200 < 3/77371252455336267181195264`). -/
theorem tail_766247770432944429179173513575154591809369561091801088_lt_383123885216472214589586756787577295904684780545900544 : (24 / 875355790724671210730291200 : ℝ) < (3 / 77371252455336267181195264 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 1532495540865888858358347027150309183618739122183602176` tail
(`1532495540865888858358347027150309183618739122183602176^{1/2} = 1237940039285380274899124224` exact; exact shape mirror of
`M383123885216472214589586756787577295904684780545900544_rpow_eq` above and latest odd-floor
`M766247770432944429179173513575154591809369561091801088_rpow_ge` above; honest via
`1237940039285380274899124224^2 = 1532495540865888858358347027150309183618739122183602176` by `norm_num`;
`1532495540865888858358347027150309183618739122183602176 = 2^180` so the root is exact, unlike
`766247770432944429179173513575154591809369561091801088`). -/
theorem M1532495540865888858358347027150309183618739122183602176_rpow_eq :
    ((((1532495540865888858358347027150309183618739122183602176 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (1237940039285380274899124224 : ℝ) := by
  have hx2 : ((((((1532495540865888858358347027150309183618739122183602176 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((1532495540865888858358347027150309183618739122183602176 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((1237940039285380274899124224 : ℝ) ^ (2 : ℕ)) = ((((1532495540865888858358347027150309183618739122183602176 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((1532495540865888858358347027150309183618739122183602176 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (1237940039285380274899124224 : ℝ) := by norm_num
  have hle1 : ((((((1532495540865888858358347027150309183618739122183602176 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((1237940039285380274899124224 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((1237940039285380274899124224 : ℝ) ^ (2 : ℕ)) ≤
      ((((((1532495540865888858358347027150309183618739122183602176 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 1532495540865888858358347027150309183618739122183602176` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/1237940039285380274899124224 = 3/154742504910672534362390528`; exact shape mirror of
`r_383123885216472214589586756787577295904684780545900544_le` above; decay recomputed honestly with
`norm_num` via the exact `M1532495540865888858358347027150309183618739122183602176_rpow_eq`; tightest honest
`T = 3/154742504910672534362390528` for this root). -/
theorem r_1532495540865888858358347027150309183618739122183602176_le :
    (12 : ℝ) * ((((((1532495540865888858358347027150309183618739122183602176 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 154742504910672534362390528 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((1532495540865888858358347027150309183618739122183602176 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M1532495540865888858358347027150309183618739122183602176_rpow_eq
  have hrw : ((((1532495540865888858358347027150309183618739122183602176 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((1532495540865888858358347027150309183618739122183602176 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((1237940039285380274899124224 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 154742504910672534362390528 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 1532495540865888858358347027150309183618739122183602176`
(`‖G - S3064991081731777716716694054300618367237478244367204352‖ ≤ 3/154742504910672534362390528`; exact shape mirror of
`eta_tail_383123885216472214589586756787577295904684780545900544_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_1532495540865888858358347027150309183618739122183602176_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 1532495540865888858358347027150309183618739122183602176), etaDirichletTerm s k)‖ ≤
      (3 / 154742504910672534362390528 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1532495540865888858358347027150309183618739122183602176 (by norm_num)
  have h2M : 2 * 1532495540865888858358347027150309183618739122183602176 = 3064991081731777716716694054300618367237478244367204352 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_1532495540865888858358347027150309183618739122183602176_le
  linarith

/-- The `M = 1532495540865888858358347027150309183618739122183602176` constant honestly improves on the banked
`M = 766247770432944429179173513575154591809369561091801088` constant
(`3/154742504910672534362390528 < 24/875355790724671210730291200`). -/
theorem tail_1532495540865888858358347027150309183618739122183602176_lt_766247770432944429179173513575154591809369561091801088 : (3 / 154742504910672534362390528 : ℝ) < (24 / 875355790724671210730291200 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 3064991081731777716716694054300618367237478244367204352` tail
(`1750711581449342421460582400 ≤ 3064991081731777716716694054300618367237478244367204352^{1/2}`;
generic mirror of `M766247770432944429179173513575154591809369561091801088_rpow_ge` above and latest exact
`M1532495540865888858358347027150309183618739122183602176_rpow_eq` above; honest floor via
`1750711581449342421460582400^2 = 3064991041420857523373157697093608462584116947189760000 ≤
3064991081731777716716694054300618367237478244367204352` by `norm_num`;
`3064991081731777716716694054300618367237478244367204352 = 2^181` so root `1237940039285380274899124224·√2 ≈
1750711592962066872460373069` is NOT exact, unlike `1532495540865888858358347027150309183618739122183602176`;
conservative doubling `2 * 875355790724671210730291200 = 1750711581449342421460582400` below the true floor
`1750711592962066872460373069`; lower gap `11512724450999790669`). -/
theorem M3064991081731777716716694054300618367237478244367204352_rpow_ge :
    (1750711581449342421460582400 : ℝ) ≤ ((((3064991081731777716716694054300618367237478244367204352 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((1750711581449342421460582400 : ℝ) ^ (2 : ℕ)) ≤ ((((3064991081731777716716694054300618367237478244367204352 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((3064991081731777716716694054300618367237478244367204352 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((3064991081731777716716694054300618367237478244367204352 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 3064991081731777716716694054300618367237478244367204352` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/1750711581449342421460582400`; generic mirror of
`r_766247770432944429179173513575154591809369561091801088_le` above and latest exact
`r_1532495540865888858358347027150309183618739122183602176_le` above; decay recomputed honestly with
`norm_num` via `M3064991081731777716716694054300618367237478244367204352_rpow_ge`; honest conservative
`T = 24/1750711581449342421460582400` for the `1750711581449342421460582400` root lower). -/
theorem r_3064991081731777716716694054300618367237478244367204352_le :
    (12 : ℝ) * ((((((3064991081731777716716694054300618367237478244367204352 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 1750711581449342421460582400 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((3064991081731777716716694054300618367237478244367204352 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((3064991081731777716716694054300618367237478244367204352 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M3064991081731777716716694054300618367237478244367204352_rpow_ge
  have hrw : ((((3064991081731777716716694054300618367237478244367204352 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((3064991081731777716716694054300618367237478244367204352 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((3064991081731777716716694054300618367237478244367204352 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (1750711581449342421460582400 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((3064991081731777716716694054300618367237478244367204352 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (1750711581449342421460582400 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((3064991081731777716716694054300618367237478244367204352 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((1750711581449342421460582400 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((1750711581449342421460582400 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 1750711581449342421460582400 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 3064991081731777716716694054300618367237478244367204352`
(`‖G - S6129982163463555433433388108601236734474956488734408704‖ ≤ 24/1750711581449342421460582400`; generic mirror of
`eta_tail_766247770432944429179173513575154591809369561091801088_le` above and latest exact
`eta_tail_1532495540865888858358347027150309183618739122183602176_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_3064991081731777716716694054300618367237478244367204352_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 3064991081731777716716694054300618367237478244367204352), etaDirichletTerm s k)‖ ≤
      (24 / 1750711581449342421460582400 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 3064991081731777716716694054300618367237478244367204352 (by norm_num)
  have h2M : 2 * 3064991081731777716716694054300618367237478244367204352 = 6129982163463555433433388108601236734474956488734408704 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_3064991081731777716716694054300618367237478244367204352_le
  linarith

/-- The `M = 3064991081731777716716694054300618367237478244367204352` constant honestly improves on the banked
`M = 1532495540865888858358347027150309183618739122183602176` constant
(`24/1750711581449342421460582400 < 3/154742504910672534362390528`). -/
theorem tail_3064991081731777716716694054300618367237478244367204352_lt_1532495540865888858358347027150309183618739122183602176 : (24 / 1750711581449342421460582400 : ℝ) < (3 / 154742504910672534362390528 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 6129982163463555433433388108601236734474956488734408704` tail
(`6129982163463555433433388108601236734474956488734408704^{1/2} = 2475880078570760549798248448` exact; exact shape mirror of
`M1532495540865888858358347027150309183618739122183602176_rpow_eq` above and latest odd-floor
`M3064991081731777716716694054300618367237478244367204352_rpow_ge` above; honest via
`2475880078570760549798248448^2 = 6129982163463555433433388108601236734474956488734408704` by `norm_num`;
`6129982163463555433433388108601236734474956488734408704 = 2^182` so the root is exact, unlike
`3064991081731777716716694054300618367237478244367204352`). -/
theorem M6129982163463555433433388108601236734474956488734408704_rpow_eq :
    ((((6129982163463555433433388108601236734474956488734408704 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (2475880078570760549798248448 : ℝ) := by
  have hx2 : ((((((6129982163463555433433388108601236734474956488734408704 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((6129982163463555433433388108601236734474956488734408704 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((2475880078570760549798248448 : ℝ) ^ (2 : ℕ)) = ((((6129982163463555433433388108601236734474956488734408704 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((6129982163463555433433388108601236734474956488734408704 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (2475880078570760549798248448 : ℝ) := by norm_num
  have hle1 : ((((((6129982163463555433433388108601236734474956488734408704 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((2475880078570760549798248448 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((2475880078570760549798248448 : ℝ) ^ (2 : ℕ)) ≤
      ((((((6129982163463555433433388108601236734474956488734408704 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 6129982163463555433433388108601236734474956488734408704` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/2475880078570760549798248448 = 3/309485009821345068724781056`; exact shape mirror of
`r_1532495540865888858358347027150309183618739122183602176_le` above; decay recomputed honestly with
`norm_num` via the exact `M6129982163463555433433388108601236734474956488734408704_rpow_eq`; tightest honest
`T = 3/309485009821345068724781056` for this root). -/
theorem r_6129982163463555433433388108601236734474956488734408704_le :
    (12 : ℝ) * ((((((6129982163463555433433388108601236734474956488734408704 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 309485009821345068724781056 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((6129982163463555433433388108601236734474956488734408704 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M6129982163463555433433388108601236734474956488734408704_rpow_eq
  have hrw : ((((6129982163463555433433388108601236734474956488734408704 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((6129982163463555433433388108601236734474956488734408704 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((2475880078570760549798248448 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 309485009821345068724781056 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 6129982163463555433433388108601236734474956488734408704`
(`‖G - S12259964326927110866866776217202473468949912977468817408‖ ≤ 3/309485009821345068724781056`; exact shape mirror of
`eta_tail_1532495540865888858358347027150309183618739122183602176_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_6129982163463555433433388108601236734474956488734408704_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 6129982163463555433433388108601236734474956488734408704), etaDirichletTerm s k)‖ ≤
      (3 / 309485009821345068724781056 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 6129982163463555433433388108601236734474956488734408704 (by norm_num)
  have h2M : 2 * 6129982163463555433433388108601236734474956488734408704 = 12259964326927110866866776217202473468949912977468817408 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_6129982163463555433433388108601236734474956488734408704_le
  linarith

/-- The `M = 6129982163463555433433388108601236734474956488734408704` constant honestly improves on the banked
`M = 3064991081731777716716694054300618367237478244367204352` constant
(`3/309485009821345068724781056 < 24/1750711581449342421460582400`). -/
theorem tail_6129982163463555433433388108601236734474956488734408704_lt_3064991081731777716716694054300618367237478244367204352 : (3 / 309485009821345068724781056 : ℝ) < (24 / 1750711581449342421460582400 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 12259964326927110866866776217202473468949912977468817408` tail
(`3501423162898684842921164800 ≤ 12259964326927110866866776217202473468949912977468817408^{1/2}`;
generic mirror of `M3064991081731777716716694054300618367237478244367204352_rpow_ge` above and latest exact
`M6129982163463555433433388108601236734474956488734408704_rpow_eq` above; honest floor via
`3501423162898684842921164800^2 = 12259964165683430093492630788374433850336467788759040000 ≤
12259964326927110866866776217202473468949912977468817408` by `norm_num`;
`12259964326927110866866776217202473468949912977468817408 = 2^183` so root `2475880078570760549798248448·√2 ≈
3501423185924133744920746139` is NOT exact, unlike `6129982163463555433433388108601236734474956488734408704`;
conservative doubling `2 * 1750711581449342421460582400 = 3501423162898684842921164800` below the true floor
`3501423185924133744920746139`; lower gap `161243680773374145428828039618613445188709777408`). -/
theorem M12259964326927110866866776217202473468949912977468817408_rpow_ge :
    (3501423162898684842921164800 : ℝ) ≤ ((((12259964326927110866866776217202473468949912977468817408 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((3501423162898684842921164800 : ℝ) ^ (2 : ℕ)) ≤ ((((12259964326927110866866776217202473468949912977468817408 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((12259964326927110866866776217202473468949912977468817408 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((12259964326927110866866776217202473468949912977468817408 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 12259964326927110866866776217202473468949912977468817408` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/3501423162898684842921164800`; generic mirror of
`r_3064991081731777716716694054300618367237478244367204352_le` above and latest exact
`r_6129982163463555433433388108601236734474956488734408704_le` above; decay recomputed honestly with
`norm_num` via `M12259964326927110866866776217202473468949912977468817408_rpow_ge`; honest conservative
`T = 24/3501423162898684842921164800` for the `3501423162898684842921164800` root lower). -/
theorem r_12259964326927110866866776217202473468949912977468817408_le :
    (12 : ℝ) * ((((((12259964326927110866866776217202473468949912977468817408 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 3501423162898684842921164800 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((12259964326927110866866776217202473468949912977468817408 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((12259964326927110866866776217202473468949912977468817408 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M12259964326927110866866776217202473468949912977468817408_rpow_ge
  have hrw : ((((12259964326927110866866776217202473468949912977468817408 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((12259964326927110866866776217202473468949912977468817408 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((12259964326927110866866776217202473468949912977468817408 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (3501423162898684842921164800 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((12259964326927110866866776217202473468949912977468817408 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (3501423162898684842921164800 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((12259964326927110866866776217202473468949912977468817408 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((3501423162898684842921164800 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((3501423162898684842921164800 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 3501423162898684842921164800 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 12259964326927110866866776217202473468949912977468817408`
(`‖G - S24519928653854221733733552434404946937899825954937634816‖ ≤ 24/3501423162898684842921164800`; generic mirror of
`eta_tail_3064991081731777716716694054300618367237478244367204352_le` above and latest exact
`eta_tail_6129982163463555433433388108601236734474956488734408704_le` above — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_12259964326927110866866776217202473468949912977468817408_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 12259964326927110866866776217202473468949912977468817408), etaDirichletTerm s k)‖ ≤
      (24 / 3501423162898684842921164800 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 12259964326927110866866776217202473468949912977468817408 (by norm_num)
  have h2M : 2 * 12259964326927110866866776217202473468949912977468817408 = 24519928653854221733733552434404946937899825954937634816 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_12259964326927110866866776217202473468949912977468817408_le
  linarith

/-- The `M = 12259964326927110866866776217202473468949912977468817408` constant honestly improves on the banked
`M = 6129982163463555433433388108601236734474956488734408704` constant
(`24/3501423162898684842921164800 < 3/309485009821345068724781056`). -/
theorem tail_12259964326927110866866776217202473468949912977468817408_lt_6129982163463555433433388108601236734474956488734408704 : (24 / 3501423162898684842921164800 : ℝ) < (3 / 309485009821345068724781056 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 24519928653854221733733552434404946937899825954937634816` tail
(`24519928653854221733733552434404946937899825954937634816^{1/2} = 4951760157141521099596496896` exact; exact shape mirror of
`M6129982163463555433433388108601236734474956488734408704_rpow_eq` above and latest odd-floor
`M12259964326927110866866776217202473468949912977468817408_rpow_ge` above; honest via
`4951760157141521099596496896^2 = 24519928653854221733733552434404946937899825954937634816` by `norm_num`;
`24519928653854221733733552434404946937899825954937634816 = 2^184` so the root is exact, unlike
`12259964326927110866866776217202473468949912977468817408`). -/
theorem M24519928653854221733733552434404946937899825954937634816_rpow_eq :
    ((((24519928653854221733733552434404946937899825954937634816 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (4951760157141521099596496896 : ℝ) := by
  have hx2 : ((((((24519928653854221733733552434404946937899825954937634816 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((24519928653854221733733552434404946937899825954937634816 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((4951760157141521099596496896 : ℝ) ^ (2 : ℕ)) = ((((24519928653854221733733552434404946937899825954937634816 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((24519928653854221733733552434404946937899825954937634816 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (4951760157141521099596496896 : ℝ) := by norm_num
  have hle1 : ((((((24519928653854221733733552434404946937899825954937634816 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((4951760157141521099596496896 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((4951760157141521099596496896 : ℝ) ^ (2 : ℕ)) ≤
      ((((((24519928653854221733733552434404946937899825954937634816 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 24519928653854221733733552434404946937899825954937634816` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/4951760157141521099596496896 = 3/618970019642690137449562112`; exact shape mirror of
`r_6129982163463555433433388108601236734474956488734408704_le` above; decay recomputed honestly with `norm_num`
via the exact `M24519928653854221733733552434404946937899825954937634816_rpow_eq`; tightest honest
`T = 3/618970019642690137449562112` for this root). -/
theorem r_24519928653854221733733552434404946937899825954937634816_le :
    (12 : ℝ) * ((((((24519928653854221733733552434404946937899825954937634816 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 618970019642690137449562112 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((24519928653854221733733552434404946937899825954937634816 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M24519928653854221733733552434404946937899825954937634816_rpow_eq
  have hrw : ((((24519928653854221733733552434404946937899825954937634816 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((24519928653854221733733552434404946937899825954937634816 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((4951760157141521099596496896 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 618970019642690137449562112 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 24519928653854221733733552434404946937899825954937634816`
(`‖G - S49039857307708443467467104868809893875799651909875269632‖ ≤ 3/618970019642690137449562112`; exact shape mirror of
`eta_tail_6129982163463555433433388108601236734474956488734408704_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_24519928653854221733733552434404946937899825954937634816_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 24519928653854221733733552434404946937899825954937634816), etaDirichletTerm s k)‖ ≤
      (3 / 618970019642690137449562112 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 24519928653854221733733552434404946937899825954937634816 (by norm_num)
  have h2M : 2 * 24519928653854221733733552434404946937899825954937634816 = 49039857307708443467467104868809893875799651909875269632 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_24519928653854221733733552434404946937899825954937634816_le
  linarith

/-- The `M = 24519928653854221733733552434404946937899825954937634816` constant honestly improves on the banked
`M = 12259964326927110866866776217202473468949912977468817408` constant
(`3/618970019642690137449562112 < 24/3501423162898684842921164800`). -/
theorem tail_24519928653854221733733552434404946937899825954937634816_lt_12259964326927110866866776217202473468949912977468817408 : (3 / 618970019642690137449562112 : ℝ) < (24 / 3501423162898684842921164800 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 49039857307708443467467104868809893875799651909875269632` tail
(`7002846325797369685842329600 ≤ 49039857307708443467467104868809893875799651909875269632^{1/2}`;
generic mirror of `M12259964326927110866866776217202473468949912977468817408_rpow_ge` above and latest exact
`M24519928653854221733733552434404946937899825954937634816_rpow_eq` above; honest floor via
`7002846325797369685842329600^2 = 49039856662733720373970523153497735401345871155036160000 ≤
49039857307708443467467104868809893875799651909875269632` by `norm_num`;
`49039857307708443467467104868809893875799651909875269632 = 2^185` so root `4951760157141521099596496896·√2 ≈
7002846371848267489841492278` is NOT exact, unlike `24519928653854221733733552434404946937899825954937634816`;
conservative doubling `2 * 3501423162898684842921164800 = 7002846325797369685842329600` below the true floor
`7002846371848267489841492278`; lower gap `644974723093496581715312158474453780754839109632`). -/
theorem M49039857307708443467467104868809893875799651909875269632_rpow_ge :
    (7002846325797369685842329600 : ℝ) ≤ ((((49039857307708443467467104868809893875799651909875269632 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((7002846325797369685842329600 : ℝ) ^ (2 : ℕ)) ≤ ((((49039857307708443467467104868809893875799651909875269632 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((49039857307708443467467104868809893875799651909875269632 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((49039857307708443467467104868809893875799651909875269632 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 49039857307708443467467104868809893875799651909875269632` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/7002846325797369685842329600`; generic mirror of
`r_12259964326927110866866776217202473468949912977468817408_le` above and latest exact
`r_24519928653854221733733552434404946937899825954937634816_le` above; decay recomputed honestly with
`norm_num` via `M49039857307708443467467104868809893875799651909875269632_rpow_ge`; honest conservative
`T = 24/7002846325797369685842329600` for the `7002846325797369685842329600` root lower). -/
theorem r_49039857307708443467467104868809893875799651909875269632_le :
    (12 : ℝ) * ((((((49039857307708443467467104868809893875799651909875269632 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 7002846325797369685842329600 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((49039857307708443467467104868809893875799651909875269632 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((49039857307708443467467104868809893875799651909875269632 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M49039857307708443467467104868809893875799651909875269632_rpow_ge
  have hrw : ((((49039857307708443467467104868809893875799651909875269632 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((49039857307708443467467104868809893875799651909875269632 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((49039857307708443467467104868809893875799651909875269632 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (7002846325797369685842329600 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((49039857307708443467467104868809893875799651909875269632 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (7002846325797369685842329600 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((49039857307708443467467104868809893875799651909875269632 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((7002846325797369685842329600 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((7002846325797369685842329600 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 7002846325797369685842329600 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 49039857307708443467467104868809893875799651909875269632`
(`‖G - S98079714615416886934934209737619787751599303819750539264‖ ≤ 24/7002846325797369685842329600`; generic mirror of
`eta_tail_12259964326927110866866776217202473468949912977468817408_le` above and latest exact
`eta_tail_24519928653854221733733552434404946937899825954937634816_le` above — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_49039857307708443467467104868809893875799651909875269632_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 49039857307708443467467104868809893875799651909875269632), etaDirichletTerm s k)‖ ≤
      (24 / 7002846325797369685842329600 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 49039857307708443467467104868809893875799651909875269632 (by norm_num)
  have h2M : 2 * 49039857307708443467467104868809893875799651909875269632 = 98079714615416886934934209737619787751599303819750539264 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_49039857307708443467467104868809893875799651909875269632_le
  linarith

/-- The `M = 49039857307708443467467104868809893875799651909875269632` constant honestly improves on the banked
`M = 24519928653854221733733552434404946937899825954937634816` constant
(`24/7002846325797369685842329600 < 3/618970019642690137449562112`). -/
theorem tail_49039857307708443467467104868809893875799651909875269632_lt_24519928653854221733733552434404946937899825954937634816 : (24 / 7002846325797369685842329600 : ℝ) < (3 / 618970019642690137449562112 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 98079714615416886934934209737619787751599303819750539264` tail
(`98079714615416886934934209737619787751599303819750539264^{1/2} = 9903520314283042199192993792` exact; exact shape mirror of
`M24519928653854221733733552434404946937899825954937634816_rpow_eq` above and latest odd-floor
`M49039857307708443467467104868809893875799651909875269632_rpow_ge` above; honest via
`9903520314283042199192993792^2 = 98079714615416886934934209737619787751599303819750539264` by `norm_num`;
`98079714615416886934934209737619787751599303819750539264 = 2^186` so the root is exact, unlike
`49039857307708443467467104868809893875799651909875269632`). -/
theorem M98079714615416886934934209737619787751599303819750539264_rpow_eq :
    ((((98079714615416886934934209737619787751599303819750539264 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (9903520314283042199192993792 : ℝ) := by
  have hx2 : ((((((98079714615416886934934209737619787751599303819750539264 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((98079714615416886934934209737619787751599303819750539264 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((9903520314283042199192993792 : ℝ) ^ (2 : ℕ)) = ((((98079714615416886934934209737619787751599303819750539264 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((98079714615416886934934209737619787751599303819750539264 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (9903520314283042199192993792 : ℝ) := by norm_num
  have hle1 : ((((((98079714615416886934934209737619787751599303819750539264 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((9903520314283042199192993792 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((9903520314283042199192993792 : ℝ) ^ (2 : ℕ)) ≤
      ((((((98079714615416886934934209737619787751599303819750539264 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 98079714615416886934934209737619787751599303819750539264` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/9903520314283042199192993792 = 3/1237940039285380274899124224`; exact shape mirror of
`r_24519928653854221733733552434404946937899825954937634816_le` above; decay recomputed honestly with `norm_num`
via the exact `M98079714615416886934934209737619787751599303819750539264_rpow_eq`; tightest honest
`T = 3/1237940039285380274899124224` for this root). -/
theorem r_98079714615416886934934209737619787751599303819750539264_le :
    (12 : ℝ) * ((((((98079714615416886934934209737619787751599303819750539264 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 1237940039285380274899124224 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((98079714615416886934934209737619787751599303819750539264 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M98079714615416886934934209737619787751599303819750539264_rpow_eq
  have hrw : ((((98079714615416886934934209737619787751599303819750539264 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((98079714615416886934934209737619787751599303819750539264 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((9903520314283042199192993792 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 1237940039285380274899124224 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 98079714615416886934934209737619787751599303819750539264`
(`‖G - S196159429230833773869868419475239575503198607639501078528‖ ≤ 3/1237940039285380274899124224`; exact shape mirror of
`eta_tail_24519928653854221733733552434404946937899825954937634816_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_98079714615416886934934209737619787751599303819750539264_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 98079714615416886934934209737619787751599303819750539264), etaDirichletTerm s k)‖ ≤
      (3 / 1237940039285380274899124224 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 98079714615416886934934209737619787751599303819750539264 (by norm_num)
  have h2M : 2 * 98079714615416886934934209737619787751599303819750539264 = 196159429230833773869868419475239575503198607639501078528 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_98079714615416886934934209737619787751599303819750539264_le
  linarith

/-- The `M = 98079714615416886934934209737619787751599303819750539264` constant honestly improves on the banked
`M = 49039857307708443467467104868809893875799651909875269632` constant
(`3/1237940039285380274899124224 < 24/7002846325797369685842329600`). -/
theorem tail_98079714615416886934934209737619787751599303819750539264_lt_49039857307708443467467104868809893875799651909875269632 : (3 / 1237940039285380274899124224 : ℝ) < (24 / 7002846325797369685842329600 : ℝ) := by
  norm_num

end Door3TailEtaUpper


namespace Door3TailEtaUpper

/-- Rpow lower for the generic `M = 196159429230833773869868419475239575503198607639501078528` tail
(`14005692651594739371684659200 ≤ 196159429230833773869868419475239575503198607639501078528^{1/2}`;
generic mirror of `M49039857307708443467467104868809893875799651909875269632_rpow_ge` above and latest exact
`M98079714615416886934934209737619787751599303819750539264_rpow_eq` above; honest floor via
`14005692651594739371684659200^2 = 196159426650934881495882092613990941605383484620144640000 ≤
196159429230833773869868419475239575503198607639501078528` by `norm_num`;
`196159429230833773869868419475239575503198607639501078528 = 2^187` so root `9903520314283042199192993792·√2 ≈
14005692743696534979682984556` is NOT exact, unlike `98079714615416886934934209737619787751599303819750539264`;
conservative doubling `2 * 7002846325797369685842329600 = 14005692651594739371684659200` below the true floor
`14005692743696534979682984556`; lower gap `2579898892373986326861248633897815123019356438528`). -/
theorem M196159429230833773869868419475239575503198607639501078528_rpow_ge :
    (14005692651594739371684659200 : ℝ) ≤ ((((196159429230833773869868419475239575503198607639501078528 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((14005692651594739371684659200 : ℝ) ^ (2 : ℕ)) ≤ ((((196159429230833773869868419475239575503198607639501078528 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((196159429230833773869868419475239575503198607639501078528 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((196159429230833773869868419475239575503198607639501078528 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Generic `M = 196159429230833773869868419475239575503198607639501078528` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/14005692651594739371684659200`; generic mirror of
`r_49039857307708443467467104868809893875799651909875269632_le` above and latest exact
`r_98079714615416886934934209737619787751599303819750539264_le` above; decay recomputed honestly with
`norm_num` via `M196159429230833773869868419475239575503198607639501078528_rpow_ge`; honest conservative
`T = 24/14005692651594739371684659200` for the `14005692651594739371684659200` root lower). -/
theorem r_196159429230833773869868419475239575503198607639501078528_le :
    (12 : ℝ) * ((((((196159429230833773869868419475239575503198607639501078528 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (24 / 14005692651594739371684659200 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((196159429230833773869868419475239575503198607639501078528 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((196159429230833773869868419475239575503198607639501078528 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := M196159429230833773869868419475239575503198607639501078528_rpow_ge
  have hrw : ((((196159429230833773869868419475239575503198607639501078528 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((196159429230833773869868419475239575503198607639501078528 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((196159429230833773869868419475239575503198607639501078528 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (14005692651594739371684659200 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((196159429230833773869868419475239575503198607639501078528 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (14005692651594739371684659200 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((196159429230833773869868419475239575503198607639501078528 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((14005692651594739371684659200 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((14005692651594739371684659200 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (24 / 14005692651594739371684659200 : ℝ) := by
    norm_num
  linarith

/-- Generic paired tail at `M = 196159429230833773869868419475239575503198607639501078528`
(`‖G - S392318858461667547739736838950479151006397215279002157056‖ ≤ 24/14005692651594739371684659200`; generic mirror of
`eta_tail_49039857307708443467467104868809893875799651909875269632_le` above and latest exact
`eta_tail_98079714615416886934934209737619787751599303819750539264_le` above — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem eta_tail_196159429230833773869868419475239575503198607639501078528_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 196159429230833773869868419475239575503198607639501078528), etaDirichletTerm s k)‖ ≤
      (24 / 14005692651594739371684659200 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 196159429230833773869868419475239575503198607639501078528 (by norm_num)
  have h2M : 2 * 196159429230833773869868419475239575503198607639501078528 = 392318858461667547739736838950479151006397215279002157056 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_196159429230833773869868419475239575503198607639501078528_le
  linarith

/-- The `M = 196159429230833773869868419475239575503198607639501078528` constant honestly improves on the banked
`M = 98079714615416886934934209737619787751599303819750539264` constant
(`24/14005692651594739371684659200 < 3/1237940039285380274899124224`). -/
theorem tail_196159429230833773869868419475239575503198607639501078528_lt_98079714615416886934934209737619787751599303819750539264 : (24 / 14005692651594739371684659200 : ℝ) < (3 / 1237940039285380274899124224 : ℝ) := by
  norm_num

end Door3TailEtaUpper

namespace Door3TailEtaUpper

/-- Rpow value for the generic `M = 392318858461667547739736838950479151006397215279002157056` tail
(`392318858461667547739736838950479151006397215279002157056^{1/2} = 19807040628566084398385987584` exact; exact shape mirror of
`M98079714615416886934934209737619787751599303819750539264_rpow_eq` above and latest odd-floor
`M196159429230833773869868419475239575503198607639501078528_rpow_ge` above; honest via
`19807040628566084398385987584^2 = 392318858461667547739736838950479151006397215279002157056` by `norm_num`;
`392318858461667547739736838950479151006397215279002157056 = 2^188` so the root is exact, unlike
`196159429230833773869868419475239575503198607639501078528`). -/
theorem M392318858461667547739736838950479151006397215279002157056_rpow_eq :
    ((((392318858461667547739736838950479151006397215279002157056 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) = (19807040628566084398385987584 : ℝ) := by
  have hx2 : ((((((392318858461667547739736838950479151006397215279002157056 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) =
      ((((392318858461667547739736838950479151006397215279002157056 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hy2 : ((19807040628566084398385987584 : ℝ) ^ (2 : ℕ)) = ((((392318858461667547739736838950479151006397215279002157056 : ℕ)) : ℝ)) := by norm_num
  have hx_nn : (0 : ℝ) ≤ ((((392318858461667547739736838950479151006397215279002157056 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hy_nn : (0 : ℝ) ≤ (19807040628566084398385987584 : ℝ) := by norm_num
  have hle1 : ((((((392318858461667547739736838950479151006397215279002157056 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) ≤
      ((19807040628566084398385987584 : ℝ) ^ (2 : ℕ)) :=
    le_of_eq (by rw [hx2, hy2])
  have hle2 : ((19807040628566084398385987584 : ℝ) ^ (2 : ℕ)) ≤
      ((((((392318858461667547739736838950479151006397215279002157056 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) :=
    le_of_eq (by rw [hy2, hx2])
  exact le_antisymm
    (le_of_pow_le_pow_left₀ (by norm_num) hy_nn hle1)
    (le_of_pow_le_pow_left₀ (by norm_num) hx_nn hle2)

/-- Generic `M = 392318858461667547739736838950479151006397215279002157056` tail-decay bound at `Re = 1/2`
(`12·(M^{-1/2})/(1/2) = 24/19807040628566084398385987584 = 3/2475880078570760549798248448`; exact shape mirror of
`r_98079714615416886934934209737619787751599303819750539264_le` above; decay recomputed honestly with `norm_num`
via the exact `M392318858461667547739736838950479151006397215279002157056_rpow_eq`; tightest honest
`T = 3/2475880078570760549798248448` for this root). -/
theorem r_392318858461667547739736838950479151006397215279002157056_le :
    (12 : ℝ) * ((((((392318858461667547739736838950479151006397215279002157056 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤
      (3 / 2475880078570760549798248448 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((392318858461667547739736838950479151006397215279002157056 : ℕ)) : ℝ)) := by norm_num
  have hA_eq := M392318858461667547739736838950479151006397215279002157056_rpow_eq
  have hrw : ((((392318858461667547739736838950479151006397215279002157056 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((392318858461667547739736838950479151006397215279002157056 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw, hA_eq]
  have hnum : (12 : ℝ) * (((19807040628566084398385987584 : ℝ))⁻¹ / (1 / 2 : ℝ)) ≤ (3 / 2475880078570760549798248448 : ℝ) := by
    norm_num
  exact hnum

/-- Generic paired tail at `M = 392318858461667547739736838950479151006397215279002157056`
(`‖G - S784637716923335095479473677900958302012794430558004314112‖ ≤ 3/2475880078570760549798248448`; exact shape mirror of
`eta_tail_98079714615416886934934209737619787751599303819750539264_le` above — numerals use only `Re = 1/2`
and `‖s‖ ≤ 12`). -/
theorem eta_tail_392318858461667547739736838950479151006397215279002157056_le {s : ℂ} (hre : s.re = (1 / 2 : ℝ))
    (hC : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range (2 * 392318858461667547739736838950479151006397215279002157056), etaDirichletTerm s k)‖ ≤
      (3 / 2475880078570760549798248448 : ℝ) := by
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 392318858461667547739736838950479151006397215279002157056 (by norm_num)
  have h2M : 2 * 392318858461667547739736838950479151006397215279002157056 = 784637716923335095479473677900958302012794430558004314112 := by norm_num
  rw [h2M] at hgen
  rw [hre] at hgen
  have hr := r_392318858461667547739736838950479151006397215279002157056_le
  linarith

/-- The `M = 392318858461667547739736838950479151006397215279002157056` constant honestly improves on the banked
`M = 196159429230833773869868419475239575503198607639501078528` constant
(`3/2475880078570760549798248448 < 24/14005692651594739371684659200`). -/
theorem tail_392318858461667547739736838950479151006397215279002157056_lt_196159429230833773869868419475239575503198607639501078528 : (3 / 2475880078570760549798248448 : ℝ) < (24 / 14005692651594739371684659200 : ℝ) := by
  norm_num

end Door3TailEtaUpper

