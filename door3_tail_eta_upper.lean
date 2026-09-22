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
