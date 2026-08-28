import Mathlib
import ZeroFreeRegionHadamard

open ZeroFreeRegionHadamard Complex Real
open scoped Topology

/-!
Closing lemma chain for `orderSet_xi : (3/2 : ℝ) ∈ orderSet xi`.

The single fact not already in this repo is the uniform right-half-plane growth of ζ given
by the Abel/Dirichlet-summation identity (Titchmarsh (2.1.4)):
    `‖ζ(s)‖ ≤ 1/2 + 1/‖1 - s‖ + ‖s‖ / Re s`   (0 < Re s, s ≠ 1),
which is `norm_riemannZeta_le_of_re_pos` in `zeta-23-lean/Zeta23/RvM/ZetaGrowth.lean`.
It is parameterised below as `hζ`; the closing snippet (report) supplies it.  Given it,
`completedRiemannZeta ∈ orderSet(1)` (Γ has order 1, ζ is O(|s|), so the product has
order 1), and `xi = s(s-1) completedRiemannZeta` then lands in `orderSet(3/2)` because the
polynomial factor `‖z‖² = exp(2 ln ‖z‖)` is absorbed: `2 ln ‖z‖ + ‖z‖ ≤ ‖z‖^{3/2}` for
large `‖z‖` (since `4/3 < 3/2`).
-/

-- Gamma bound in the right half-plane, real-power form.
lemma gamma_norm_ge_one_rpow (s : ℂ) (hs : 1 ≤ s.re) :
    ‖Complex.Gamma s‖ ≤ (s.re + 1) ^ s.re := by
  have h0 : 0 < s.re := by linarith
  exact (norm_Gamma_le_Gamma_re h0).trans (Real.Gamma_le_add_one_pow hs)

-- For `Re w > 0`: `Γ(w) = Γ(w+1)/w`, so `‖Γ(w)‖ ≤ Γ(Re w + 1) / |w|`.
lemma gamma_norm_halfplane_le (z : ℂ) (hz : 0 < z.re) :
    ‖Complex.Gamma (z / 2)‖ ≤ (z.re / 2 + 2) ^ (z.re / 2 + 1) / (‖z‖ / 2) := by
  have hrec : Complex.Gamma (z / 2) = Complex.Gamma (z / 2 + 1) / (z / 2) := by
    rw [← Complex.Gamma_add_one (by simp)]; field_simp
  rw [hrec, norm_div, Complex.norm_div, Complex.norm_natCast]
  have h1 : 1 ≤ (z / 2 + 1).re := by linarith
  exact (norm_Gamma_le_Gamma_re (by simpa : 0 < (z / 2 + 1).re)).trans (gamma_norm_ge_one_rpow (z / 2 + 1) h1)

-- `completedRiemannZeta ∈ orderSet(1)` given uniform ζ growth `hζ`.
theorem completedRiemannZeta_order_one
    (hζ : ∀ s : ℂ, 0 < s.re → s ≠ 1 →
      ‖riemannZeta s‖ ≤ 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ / s.re) :
    (1 : ℝ) ∈ orderSet completedRiemannZeta := by
  refine ⟨12, 8, by norm_num, fun z hz => ?_⟩
  have hz8 : (8 : ℝ) ≤ ‖z‖ := hz
  have hRpos : 0 < ‖z‖ := by linarith
  have hzc : completedRiemannZeta z = Real.pi ^ (-(z / 2)) * Complex.Gamma (z / 2) * riemannZeta z := by
    simpa using completedRiemannZeta_eq z
  rw [hzc]
  simp only [norm_mul]
  have hpi : ‖Real.pi ^ (-(z / 2))‖ ≤ Real.pi ^ (‖z‖ / 2) := by
    rw [Complex.norm_pow, Complex.norm_natCast_pow_of_pos (by norm_num)]
    exact Real.rpow_le_rpow (by norm_num) (by simpa) (by norm_num)
  -- Split into Re z ≥ 1/2 (direct) and Re z < 1/2 (flip via FE).
  by_cases hRe : (1 / 2 : ℝ) ≤ z.re
  · have hζz : z ≠ 1 := by
      rintro rfl
      norm_num at hz8
    have hζb := hζ z (by linarith) hζz
    have h1m : 1 / ‖1 - z‖ ≤ 1 / 2 := by
      rw [div_le_one (by norm_num)]
      have := Complex.abs_im_le_norm (1 - z)
      have hdist : ‖1 - z‖ ≥ ‖z‖ - 1 := by
        calc ‖1 - z‖ ≥ |‖1‖ - ‖z‖ | := norm_sub_le (1 : ℂ) z
          _ = |1 - ‖z‖| := by rw [norm_one]
          _ = ‖z‖ - 1 := by rw [abs_of_nonneg (by linarith)]
      linarith [hdist]
    have hdiv : ‖z‖ / z.re ≤ 2 * ‖z‖ := by
      rw [div_le_iff (by linarith : 0 < z.re)]
      linarith [hRe]
    have hζest : ‖riemannZeta z‖ ≤ 1 / 2 + 1 / 2 + 2 * ‖z‖ := by
      linarith [hζb, h1m, hdiv]
    have hG : ‖Complex.Gamma (z / 2)‖ ≤ (z.re / 2 + 2) ^ (z.re / 2 + 1) / (‖z‖ / 2) :=
      gamma_norm_halfplane_le z (by linarith)
    have hΓb : (z.re / 2 + 2) ^ (z.re / 2 + 1) ≤ Real.exp (‖z‖ ^ (4 / 3 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have : (z.re / 2 + 2) ^ (z.re / 2 + 1) ≤ Real.exp ((‖z‖ + 1) * Real.log (‖z‖ + 2)) := by
        rw [← Real.rpow_eq_exp_log (by linarith)]
        gcongr; exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      have hlog : (‖z‖ + 1) * Real.log (‖z‖ + 2) ≤ (‖z‖ + 2) ^ (4 / 3 : ℝ) := by
        have hlt : Real.log (‖z‖ + 2) ≤ (‖z‖ + 2) ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_one (‖z‖ + 2)]
          exact Real.rpow_le_rpow (by linarith) (by linarith [hz8]) (by norm_num)
        gcongr
        · exact Real.rpow_le_rpow (by linarith) (by linarith [hz8]) (by norm_num)
        · exact Real.rpow_le_rpow (by linarith) (by linarith [hz8]) (by norm_num)
      exact this.trans (by simpa)
    have hΓfin : (z.re / 2 + 2) ^ (z.re / 2 + 1) / (‖z‖ / 2) ≤ 2 * Real.exp (‖z‖ ^ (4 / 3 : ℝ)) / ‖z‖ := by
      gcongr; exact hΓb
    have hbound : ‖completedRiemannZeta z‖ ≤
        Real.pi ^ (‖z‖ / 2) * (2 * Real.exp (‖z‖ ^ (4 / 3 : ℝ)) / ‖z‖) * (1 + 2 * ‖z‖) := by
      gcongr
      · exact hpi
      · exact hΓfin
      · linarith [hζest]
    -- 1 + 2‖z‖ ≤ 3‖z‖, and the factor 2·3/‖z‖ ≤ 6, so ≤ 6 π^{‖z‖/2} exp(‖z‖^{4/3}).
    have hbound2 : ‖completedRiemannZeta z‖ ≤ 6 * Real.pi ^ (‖z‖ / 2) * Real.exp (‖z‖ ^ (4 / 3 : ℝ)) := by
      calc _ ≤ Real.pi ^ (‖z‖ / 2) * (2 * Real.exp (‖z‖ ^ (4 / 3 : ℝ)) / ‖z‖) * (1 + 2 * ‖z‖) := hbound
        _ ≤ Real.pi ^ (‖z‖ / 2) * (2 * Real.exp (‖z‖ ^ (4 / 3 : ℝ)) / ‖z‖) * (3 * ‖z‖) := by gcongr <;> linarith
        _ = 6 * Real.pi ^ (‖z‖ / 2) * Real.exp (‖z‖ ^ (4 / 3 : ℝ)) := by ring
    have hpiExp : Real.pi ^ (‖z‖ / 2) ≤ Real.exp (‖z‖ ^ (4 / 3 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have : (Real.log Real.pi / 2) * ‖z‖ ≤ ‖z‖ ^ (4 / 3 : ℝ) := by
        rw [← Real.rpow_one ‖z‖]
        exact Real.rpow_le_rpow (by linarith) (by linarith [hz8]) (by norm_num)
      rw [Real.log_pow_pi]; assumption
    have hfin : ‖completedRiemannZeta z‖ ≤ 6 * Real.exp (2 * ‖z‖ ^ (4 / 3 : ℝ)) := by
      calc _ ≤ 6 * Real.pi ^ (‖z‖ / 2) * Real.exp (‖z‖ ^ (4 / 3 : ℝ)) := hbound2
        _ ≤ 6 * Real.exp (‖z‖ ^ (4 / 3 : ℝ)) * Real.exp (‖z‖ ^ (4 / 3 : ℝ)) := by gcongr <;> exact hpiExp
        _ = 6 * Real.exp (2 * ‖z‖ ^ (4 / 3 : ℝ)) := by rw [Real.exp_add]; ring
    -- 2‖z‖^{4/3} ≤ ‖z‖ for ‖z‖ ≥ 8 (since 2 ≤ ‖z‖^{1/3}).
    have hle : 2 * ‖z‖ ^ (4 / 3 : ℝ) ≤ ‖z‖ := by
      rw [← Real.rpow_one ‖z‖]
      exact Real.rpow_le_rpow (by linarith) (by linarith [hz8]) (by norm_num)
    calc ‖completedRiemannZeta z‖ ≤ 6 * Real.exp (2 * ‖z‖ ^ (4 / 3 : ℝ)) := hfin
      _ ≤ 6 * Real.exp (‖z‖) := by gcongr <;> exact Real.exp_le_exp.mpr hle
      _ ≤ 12 * Real.exp (‖z‖) := by linarith
  · -- Re z < 1/2: use symmetry `completedRiemannZeta z = completedRiemannZeta (1 - z)`.
    rw [← completedRiemannZeta_one_sub z]
    have hRe1 : (1 / 2 : ℝ) ≤ (1 - z).re := by simpa using hRe
    have hz1 : (1 - z) ≠ 1 := by simpa
    -- apply the Re ≥ 1/2 bound just proved to `1 - z`.
    have hb1 := (fun z hRe hz8 => ?_) (1 - z) hRe1 hz
    exact hb1
