import zeta_rigorous

open Filter Topology Real Complex

noncomputable section

namespace Door3ZetaPairTightening

/- A degree-eight cosine majorant, obtained by one more Taylor bootstrap over
the already proved septic sine lower bound. -/
theorem cos_le_sextic {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 := by
  have key : ∀ t : ℝ,
      HasDerivAt
        (fun u : ℝ => 1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320 - Real.cos u)
        (-t + t ^ 3 / 6 - t ^ 5 / 120 + t ^ 7 / 5040 + Real.sin t) t := by
    intro t
    have h2 : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t := by
      have h := (hasDerivAt_pow 2 t).div_const (2 : ℝ)
      have e : ((2 : ℕ) : ℝ) * t ^ (2 - 1) / 2 = t := by
        rw [show (2 - 1 : ℕ) = 1 by decide, pow_one]
        ring
      rwa [e] at h
    have h4 : HasDerivAt (fun u : ℝ => u ^ 4 / 24) (t ^ 3 / 6) t := by
      have h := (hasDerivAt_pow 4 t).div_const (24 : ℝ)
      have e : ((4 : ℕ) : ℝ) * t ^ (4 - 1) / 24 = t ^ 3 / 6 := by
        rw [show (4 - 1 : ℕ) = 3 by decide]
        push_cast
        ring
      rwa [e] at h
    have h6 : HasDerivAt (fun u : ℝ => u ^ 6 / 720) (t ^ 5 / 120) t := by
      have h := (hasDerivAt_pow 6 t).div_const (720 : ℝ)
      have e : ((6 : ℕ) : ℝ) * t ^ (6 - 1) / 720 = t ^ 5 / 120 := by
        rw [show (6 - 1 : ℕ) = 5 by decide]
        push_cast
        ring
      rwa [e] at h
    have h8 : HasDerivAt (fun u : ℝ => u ^ 8 / 40320) (t ^ 7 / 5040) t := by
      have h := (hasDerivAt_pow 8 t).div_const (40320 : ℝ)
      have e : ((8 : ℕ) : ℝ) * t ^ (8 - 1) / 40320 = t ^ 7 / 5040 := by
        rw [show (8 - 1 : ℕ) = 7 by decide]
        push_cast
        ring
      rwa [e] at h
    have hcos : HasDerivAt (fun u : ℝ => Real.cos u) (-Real.sin t) t :=
      Real.hasDerivAt_cos t
    have hbase :
        HasDerivAt
          (fun u : ℝ => 1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320 - Real.cos u)
          (0 - t + t ^ 3 / 6 - t ^ 5 / 120 + t ^ 7 / 5040 - -Real.sin t) t :=
      (((hasDerivAt_const t (1 : ℝ)).sub h2).add h4).sub h6 |>.add h8 |>.sub hcos
    have e : (0 : ℝ) - t + t ^ 3 / 6 - t ^ 5 / 120 + t ^ 7 / 5040 - -Real.sin t =
        -t + t ^ 3 / 6 - t ^ 5 / 120 + t ^ 7 / 5040 + Real.sin t := by ring
    rwa [e] at hbase
  have hcont : ContinuousOn
      (fun u : ℝ => 1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320 - Real.cos u)
      (Set.Ici 0) := by fun_prop
  have hdiff : DifferentiableOn ℝ
      (fun u : ℝ => 1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320 - Real.cos u)
      (interior (Set.Ici 0)) :=
    fun t _ => (key t).differentiableAt.differentiableWithinAt
  have hnn : ∀ t ∈ interior (Set.Ici (0 : ℝ)),
      0 ≤ deriv
        (fun u : ℝ => 1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320 - Real.cos u) t := by
    intro t ht
    rw [interior_Ici] at ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt (Set.mem_Ioi.mp ht)
    rw [(key t).deriv]
    have hs := CG_sin_ge_septic ht0
    linarith
  have hmono := monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont hdiff hnn
  have h0x := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  have hf0 :
      (fun u : ℝ => 1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320 - Real.cos u) 0 = 0 := by
    norm_num [Real.cos_zero]
  rw [hf0] at h0x
  linarith

theorem poly8_antitone_on :
    AntitoneOn (fun u : ℝ => 1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320)
      (Set.Icc (1.4971 : ℝ) 1.517) := by
  let f : ℝ → ℝ := fun u => 1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320
  have hcont : ContinuousOn f (Set.Icc (1.4971 : ℝ) 1.517) := by
    dsimp [f]
    fun_prop
  have hdiff : DifferentiableOn ℝ f (interior (Set.Icc (1.4971 : ℝ) 1.517)) := by
    intro t ht
    dsimp [f]
    fun_prop
  have hnn : ∀ t ∈ interior (Set.Icc (1.4971 : ℝ) 1.517), deriv f t ≤ 0 := by
    intro t ht
    rw [interior_Icc] at ht
    have ht0 : (0 : ℝ) ≤ t := by linarith [ht.1]
    have h2 : t ^ 2 ≤ (1.517 : ℝ) ^ 2 := pow_le_pow_left₀ ht0 (le_of_lt ht.2) 2
    have h6 : t ^ 6 ≤ (1.517 : ℝ) ^ 6 := pow_le_pow_left₀ ht0 (le_of_lt ht.2) 6
    have hbr : (0 : ℝ) ≤ 1 - t ^ 2 / 6 + t ^ 4 / 120 - t ^ 6 / 5040 := by
      nlinarith [sq_nonneg (t ^ 2)]
    have hmul : 0 ≤ t * (1 - t ^ 2 / 6 + t ^ 4 / 120 - t ^ 6 / 5040) :=
      mul_nonneg ht0 hbr
    dsimp [f]
    have h2 : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t := by
      have h := (hasDerivAt_pow 2 t).div_const (2 : ℝ)
      have e : ((2 : ℕ) : ℝ) * t ^ (2 - 1) / 2 = t := by
        rw [show (2 - 1 : ℕ) = 1 by decide, pow_one]
        ring
      rwa [e] at h
    have h4 : HasDerivAt (fun u : ℝ => u ^ 4 / 24) (t ^ 3 / 6) t := by
      have h := (hasDerivAt_pow 4 t).div_const (24 : ℝ)
      have e : ((4 : ℕ) : ℝ) * t ^ (4 - 1) / 24 = t ^ 3 / 6 := by
        rw [show (4 - 1 : ℕ) = 3 by decide]
        push_cast
        ring
      rwa [e] at h
    have h6 : HasDerivAt (fun u : ℝ => u ^ 6 / 720) (t ^ 5 / 120) t := by
      have h := (hasDerivAt_pow 6 t).div_const (720 : ℝ)
      have e : ((6 : ℕ) : ℝ) * t ^ (6 - 1) / 720 = t ^ 5 / 120 := by
        rw [show (6 - 1 : ℕ) = 5 by decide]
        push_cast
        ring
      rwa [e] at h
    have h8 : HasDerivAt (fun u : ℝ => u ^ 8 / 40320) (t ^ 7 / 5040) t := by
      have h := (hasDerivAt_pow 8 t).div_const (40320 : ℝ)
      have e : ((8 : ℕ) : ℝ) * t ^ (8 - 1) / 40320 = t ^ 7 / 5040 := by
        rw [show (8 - 1 : ℕ) = 7 by decide]
        push_cast
        ring
      rwa [e] at h
    have hbase :
        HasDerivAt (fun u : ℝ => 1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320)
          (0 - t + t ^ 3 / 6 - t ^ 5 / 120 + t ^ 7 / 5040) t :=
      (((hasDerivAt_const t (1 : ℝ)).sub h2).add h4).sub h6 |>.add h8
    have hd : deriv (fun u : ℝ => 1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320) t =
        -t + t ^ 3 / 6 - t ^ 5 / 120 + t ^ 7 / 5040 := by
      have h := hbase.deriv
      convert h using 1 <;> ring
    rw [hd]
    nlinarith [hmul]
  exact antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont hdiff hnn

theorem cos20_upper : Real.cos (D3_phase 20) ≤ (0.074 : ℝ) := by
  have hmem := DZ3v_delta20_mem
  have c1 : Real.cos (D3_phase 20 - 2 * Real.pi) = Real.cos (D3_phase 20) :=
    Real.cos_sub_two_pi _
  have e2 : D3_phase 20 - 4 * Real.pi = (D3_phase 20 - 2 * Real.pi) - 2 * Real.pi := by ring
  have c2 : Real.cos (D3_phase 20 - 4 * Real.pi) = Real.cos (D3_phase 20 - 2 * Real.pi) := by
    rw [e2]; exact Real.cos_sub_two_pi _
  have e3 : D3_phase 20 - 6 * Real.pi = (D3_phase 20 - 4 * Real.pi) - 2 * Real.pi := by ring
  have c3 : Real.cos (D3_phase 20 - 6 * Real.pi) = Real.cos (D3_phase 20 - 4 * Real.pi) := by
    rw [e3]; exact Real.cos_sub_two_pi _
  have e4 : D3_phase 20 - 8 * Real.pi = (D3_phase 20 - 6 * Real.pi) - 2 * Real.pi := by ring
  have c4 : Real.cos (D3_phase 20 - 8 * Real.pi) = Real.cos (D3_phase 20 - 6 * Real.pi) := by
    rw [e4]; exact Real.cos_sub_two_pi _
  have hred : Real.cos (D3_phase 20 - 8 * Real.pi) = Real.cos (D3_phase 20) := by
    rw [c4, c3, c2, c1]
  rw [← hred]
  have hu_nn : (0 : ℝ) ≤ D3_phase 20 - 8 * Real.pi := by linarith [hmem.1]
  have hu_lo : (1.4971 : ℝ) ≤ D3_phase 20 - 8 * Real.pi := hmem.1
  have hu_hi : D3_phase 20 - 8 * Real.pi ≤ (1.517 : ℝ) := hmem.2
  have hQ := cos_le_sextic hu_nn
  have hpoly := poly8_antitone_on
  have hpoly_le :
      1 - (D3_phase 20 - 8 * Real.pi)^2 / 2 + (D3_phase 20 - 8 * Real.pi)^4 / 24
        - (D3_phase 20 - 8 * Real.pi)^6 / 720 + (D3_phase 20 - 8 * Real.pi)^8 / 40320
      ≤ 1 - (1.4971 : ℝ)^2 / 2 + (1.4971 : ℝ)^4 / 24
        - (1.4971 : ℝ)^6 / 720 + (1.4971 : ℝ)^8 / 40320 := by
    exact hpoly ⟨le_rfl, by norm_num⟩ ⟨hu_lo, hu_hi⟩ hu_lo
  have hnum : (1 : ℝ) - (1.4971 : ℝ)^2 / 2 + (1.4971 : ℝ)^4 / 24
      - (1.4971 : ℝ)^6 / 720 + (1.4971 : ℝ)^8 / 40320 ≤ 0.074 := by norm_num
  linarith

theorem cos21_lower : (-0.343 : ℝ) ≤ Real.cos (D3_phase 21) := by
  have hmem := DZ3v_delta21_mem
  have c1 : Real.cos (D3_phase 21 - 2 * Real.pi) = Real.cos (D3_phase 21) :=
    Real.cos_sub_two_pi _
  have e2 : D3_phase 21 - 4 * Real.pi = (D3_phase 21 - 2 * Real.pi) - 2 * Real.pi := by ring
  have c2 : Real.cos (D3_phase 21 - 4 * Real.pi) = Real.cos (D3_phase 21 - 2 * Real.pi) := by
    rw [e2]; exact Real.cos_sub_two_pi _
  have e3 : D3_phase 21 - 6 * Real.pi = (D3_phase 21 - 4 * Real.pi) - 2 * Real.pi := by ring
  have c3 : Real.cos (D3_phase 21 - 6 * Real.pi) = Real.cos (D3_phase 21 - 4 * Real.pi) := by
    rw [e3]; exact Real.cos_sub_two_pi _
  have e4 : D3_phase 21 - 8 * Real.pi = (D3_phase 21 - 6 * Real.pi) - 2 * Real.pi := by ring
  have c4 : Real.cos (D3_phase 21 - 8 * Real.pi) = Real.cos (D3_phase 21 - 6 * Real.pi) := by
    rw [e4]; exact Real.cos_sub_two_pi _
  have hred : Real.cos (D3_phase 21 - 8 * Real.pi) = Real.cos (D3_phase 21) := by
    rw [c4, c3, c2, c1]
  rw [← hred]
  have hu_nn : (0 : ℝ) ≤ D3_phase 21 - 8 * Real.pi := by linarith [hmem.1]
  have hu_lo : (1.9138 : ℝ) ≤ D3_phase 21 - 8 * Real.pi := hmem.1
  have hu_hi : D3_phase 21 - 8 * Real.pi ≤ (1.9147 : ℝ) := hmem.2
  have hS := DZ3u_cos_sextic_lower hu_nn
  have h2hi : (D3_phase 21 - 8 * Real.pi)^2 ≤ (1.9147 : ℝ)^2 :=
    pow_le_pow_left₀ hu_nn hu_hi 2
  have h4lo : (1.9138 : ℝ)^4 ≤ (D3_phase 21 - 8 * Real.pi)^4 :=
    pow_le_pow_left₀ (by norm_num) hu_lo 4
  have h6hi : (D3_phase 21 - 8 * Real.pi)^6 ≤ (1.9147 : ℝ)^6 :=
    pow_le_pow_left₀ hu_nn hu_hi 6
  have hnum : (-0.343 : ℝ) ≤ 1 - (1.9147 : ℝ)^2 / 2
      + (1.9138 : ℝ)^4 / 24 - (1.9147 : ℝ)^6 / 720 := by norm_num
  have hle : 1 - (1.9147 : ℝ)^2 / 2 + (1.9138 : ℝ)^4 / 24 - (1.9147 : ℝ)^6 / 720
      ≤ 1 - (D3_phase 21 - 8 * Real.pi)^2 / 2
        + (D3_phase 21 - 8 * Real.pi)^4 / 24 - (D3_phase 21 - 8 * Real.pi)^6 / 720 := by
    linarith [h2hi, h4lo, h6hi]
  linarith

theorem amp20_le_inv62134 : D3_amp 20 ≤ 1 / 6.2134 := by
  unfold D3_amp
  have hcast : ((((20 : ℕ) : ℝ) + 1 : ℝ)) = 21 := by norm_num
  rw [hcast]
  have hpow : (((6.2134 : ℝ)) ^ ((5 : ℕ))) ≤
      ((((21 : ℝ) ^ ((3 / 5 : ℝ)))) ^ ((5 : ℕ)) : ℝ) := by
    have e : ((((21 : ℝ) ^ ((3 / 5 : ℝ)))) ^ ((5 : ℕ)) : ℝ) = (21 : ℝ) ^ ((3 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 21)]
      rw [show (3 / 5 : ℝ) * (((5 : ℕ)) : ℝ) = (3 : ℝ) by norm_num]
      rw [show (3 : ℝ) = (((3 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 21 3
    rw [e]
    norm_num
  have hstep : ((6.2134 : ℝ)) ≤ (21 : ℝ) ^ ((3 / 5 : ℝ)) :=
    le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _).le hpow
  calc
    (21 : ℝ) ^ (-(0.605 : ℝ)) ≤ (6.2134 : ℝ)⁻¹ := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 21)]
      exact (inv_le_inv₀ (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)).mpr
        (le_trans hstep (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)))
    _ = 1 / 6.2134 := by rw [one_div]

theorem pair10_re_le :
    (etaPairTerm (1 - zetaCellS0) 10).re ≤ (0.0673 : ℝ) := by
  rw [DZ3v_pair10_re_eq]
  have hA20 := DZ3w_amp20_le_inv62
  have hA21 := DZ3w_amp21_le_inv638
  have hc20 := cos20_upper
  have hc21 := cos21_lower
  have hA20' := amp20_le_inv62134
  have h1 : D3_amp 20 * Real.cos (D3_phase 20) ≤ (1 / 6.2134 : ℝ) * 0.074 := by
    have e : D3_amp 20 * Real.cos (D3_phase 20)
        = D3_amp 20 * 0.074 - D3_amp 20 * (0.074 - Real.cos (D3_phase 20)) := by ring
    have hnn : (0 : ℝ) ≤ D3_amp 20 * (0.074 - Real.cos (D3_phase 20)) :=
      mul_nonneg (D3_amp_nonneg 20) (by linarith)
    have hle : D3_amp 20 * 0.074 ≤ (1 / 6.2134 : ℝ) * 0.074 :=
      mul_le_mul_of_nonneg_right hA20' (by norm_num)
    linarith
  have h2 : -(D3_amp 21 * Real.cos (D3_phase 21)) ≤ (1 / 6.38 : ℝ) * 0.343 := by
    have e : -(D3_amp 21 * Real.cos (D3_phase 21))
        = D3_amp 21 * 0.343 - D3_amp 21 * (0.343 + Real.cos (D3_phase 21)) := by ring
    have hnn : (0 : ℝ) ≤ D3_amp 21 * (0.343 + Real.cos (D3_phase 21)) :=
      mul_nonneg (D3_amp_nonneg 21) (by linarith)
    have hle : D3_amp 21 * 0.343 ≤ (1 / 6.38 : ℝ) * 0.343 :=
      mul_le_mul_of_nonneg_right hA21 (by norm_num)
    linarith
  have hnum : (1 / 6.2134 : ℝ) * 0.074 + (1 / 6.38 : ℝ) * 0.343 ≤ 0.0673 := by norm_num
  linarith

#print axioms Door3ZetaPairTightening.cos_le_sextic
#print axioms Door3ZetaPairTightening.cos20_upper
#print axioms Door3ZetaPairTightening.cos21_lower
#print axioms Door3ZetaPairTightening.pair10_re_le

end Door3ZetaPairTightening
