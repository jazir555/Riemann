import ZeroFreeRegionProof
import ZeroFreeRegionHadamard
import KadiriOrderInfra

open Complex Real Topology
open scoped BigOperators
open ZeroFreeRegionHadamard
open ArithmeticFunction hiding log
open scoped LSeries.notation

noncomputable section

/-!
Corrected `kadiriLamzouriZetaZeroFreeEdge`.

ROOT CAUSE (fixed here): the original code set
  `analytic s' = LSeries ↗Λ s' + (1/(s'-s) + 1/s)`  with `Z = {s}`,
so the borderline `1/(s'-s)` term lived inside `analytic` and broke the
3-4-1 analytic bound (`h_analytic`).

CORRECTION: take `analytic` to be the gamma/digamma part from the Hadamard
factorisation (via `logDeriv_completedZeta`) MINUS the tail of the *full*
ξ-zero enumeration `a` (from `xi_zero_enumeration`); move the borderline
`1/(s'-s)` term into the zero-sum over that full enumeration.  Under the
contradiction `ζ(s) = 0` we have `s = a k`, so the finite truncation
`Z = {a n | n < k+1}` contains `s` and `h_decomp` follows by splitting the
infinite zero-sum.  The analytic part is then bounded by the digamma
3-4-1 estimate (`digamma_le_log`), giving `A₀ = 3`, `A₁ = 5/2`.
-/

-- The gamma/digamma part of the Hadamard decomposition.
def gammaPart (g : ℂ → ℂ) (s' : ℂ) : ℂ :=
  -deriv g s' + 1 / s' + 1 / (s' - 1) + logDeriv (fun x : ℂ => x.Gammaℝ) s'

-- `logDeriv Gammaℝ(s) = -(log π)/2 + (1/2)·digamma(s/2)`.
theorem logDeriv_Gammaℝ_eq (s : ℂ) (hs : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) :
    logDeriv (fun x : ℂ => x.Gammaℝ) s =
      -(Real.log Real.pi) / 2 + (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
  rw [Gammaℝ_def]
  have hπ : π ^ (-s / 2) ≠ 0 := by exact cpow_ne_zero (Real.pi_ne_zero : π ≠ 0) _
  have hΓ : Gamma (s / 2) ≠ 0 := by
    intro h
    have := Complex.Gamma_eq_zero_iff.mp h
    simpa [hs] using this
  rw [logDeriv_mul s hπ hΓ]
  rw [logDeriv_cpow (fun _ => (Real.pi_ne_zero : π ≠ 0)) _ (by norm_num)]
  · rw [logDeriv_apply, hasDerivAt_id s, one_mul, mul_div_cancel_left₀
        (show (2 : ℂ) ≠ 0 from by norm_num),
        logDeriv_apply, Complex.digamma_def]
    ring
  · simpa

-- 3-4-1 of `1/(s-1)` is `≤ 3/(σ-1) + 3`.
theorem oneOverSsub1_threeFourOne (σ t : ℝ) (hσ : 1 < σ) (ht : 1 ≤ |t|) :
    3 * ((1 : ℂ) / (↑σ - 1)).re
  + 4 * ((1 : ℂ) / (↑σ - 1 + ↑t * I)).re
  + ((1 : ℂ) / (↑σ - 1 + 2 * ↑t * I)).re
    ≤ 3 / (σ - 1) + 3 := by
  have h1 : ((↑σ - 1 : ℂ)⁻¹).re = 1 / (σ - 1) := by
    rw [Complex.inv_re]; simp [Complex.normSq_apply]; ring_nf
  have h2 : ((↑σ - 1 + ↑t * I : ℂ)⁻¹).re = (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) := by
    rw [Complex.inv_re]; simp [Complex.normSq_apply]; ring_nf
  have h3 : ((↑σ - 1 + 2 * ↑t * I : ℂ)⁻¹).re = (σ - 1) / ((σ - 1) ^ 2 + 4 * t ^ 2) := by
    rw [Complex.inv_re]; simp [Complex.normSq_apply]; ring_nf
  rw [h1, h2, h3]
  have htt : t ^ 2 ≥ 1 := by rw [← Real.sq_le_sq]; linarith
  have hA : (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) ≤ 1 / t := by
    apply div_le_div_of_nonneg_left (by linarith) (by linarith)
    have := le_mul_of_one_le_right (by linarith : (0 : ℝ) ≤ (σ - 1)) htt
    linarith
  have hB : (σ - 1) / ((σ - 1) ^ 2 + 4 * t ^ 2) ≤ 1 / (2 * t) := by
    apply div_le_div_of_nonneg_left (by linarith) (by linarith)
    have := le_mul_of_one_le_right (by linarith : (0 : ℝ) ≤ (σ - 1)) (by nlinarith [htt] : t ≤ 2 * t)
    linarith
  have hC : 1 / t ≤ 1 := by rw [← one_div, div_le_div (by norm_num) (by norm_num)]; linarith
  have hD : 1 / (2 * t) ≤ 1 / 2 := by linarith
  linarith

-- 3-4-1 of `1/s` is `≤ 8`.
theorem oneOverS_threeFourOne (σ t : ℝ) (hσ : 1 < σ) (ht : 1 ≤ |t|) :
    3 * ((1 : ℂ) / (↑σ : ℂ)).re
  + 4 * ((1 : ℂ) / (↑σ + ↑t * I)).re
  + ((1 : ℂ) / (↑σ + 2 * ↑t * I)).re
    ≤ 8 := by
  have hr : ((↑σ : ℂ)⁻¹).re = 1 / σ := by rw [Complex.inv_re]; simp [Complex.normSq_apply]; ring_nf
  have h1 : ((↑σ + ↑t * I : ℂ)⁻¹).re = σ / (σ ^ 2 + t ^ 2) := by
    rw [Complex.inv_re]; simp [Complex.normSq_apply]; ring_nf
  have h2 : ((↑σ + 2 * ↑t * I : ℂ)⁻¹).re = σ / (σ ^ 2 + 4 * t ^ 2) := by
    rw [Complex.inv_re]; simp [Complex.normSq_apply]; ring_nf
  rw [hr, h1, h2]
  have hσ1 : 1 / σ ≤ 1 := by rw [← one_div, div_le_div (by norm_num) (by norm_num)]; linarith
  have htt : t ^ 2 ≥ 1 := by rw [← Real.sq_le_sq]; linarith
  have hA : σ / (σ ^ 2 + t ^ 2) ≤ 1 / t := by
    apply div_le_div_of_nonneg_left (by linarith) (by linarith)
    have := le_mul_of_one_le_right (by linarith : (0 : ℝ) ≤ σ) htt
    linarith
  have hB : σ / (σ ^ 2 + 4 * t ^ 2) ≤ 1 / (2 * t) := by
    apply div_le_div_of_nonneg_left (by linarith) (by linarith)
    have := le_mul_of_one_le_right (by linarith : (0 : ℝ) ≤ σ) (by nlinarith [htt] : t ≤ 2 * t)
    linarith
  have hC : 1 / t ≤ 1 := by rw [← one_div, div_le_div (by norm_num) (by norm_num)]; linarith
  have hD : 1 / (2 * t) ≤ 1 / 2 := by linarith
  linarith

-- 3-4-1 of `(1/2)·digamma(s/2)` is `≤ (5/2)·log(|t|+2) + 20`.
theorem digammaHalf_threeFourOne (σ t : ℝ) (hσ : 1 < σ) (ht : 1 ≤ |t|) :
    let f := fun (z : ℂ) => (1 / 2 : ℂ) * Complex.digamma (z / 2)
    3 * (f (↑σ)).re + 4 * (f (↑σ + ↑t * I)).re + (f (↑σ + 2 * ↑t * I)).re
      ≤ (5 / 2 : ℝ) * Real.log (|t| + 2) + 20 := by
  intro f
  let z1 : ℂ := ↑σ
  let z2 : ℂ := ↑σ + ↑t * I
  let z3 : ℂ := ↑σ + 2 * ↑t * I
  have hz1 : (z1 / 2).re = σ / 2 := by simp
  have hz2 : (z2 / 2).re = σ / 2 := by simp
  have hz3 : (z3 / 2).re = σ / 2 := by simp
  have hnz1 : (z1 / 2).re > 0 := by simpa [hz1] using hσ
  have hnz2 : (z2 / 2).re > 0 := by simpa [hz2] using hσ
  have hnz3 : (z3 / 2).re > 0 := by simpa [hz3] using hσ
  have him2 : |(z2 / 2).im| = |t| / 2 := by
    rw [← Complex.abs_of_real, Complex.abs_div, Complex.abs_of_real, Complex.abs_mul, Complex.abs_I]
    norm_num; ring
  have him3 : |(z3 / 2).im| = |t| := by
    rw [← Complex.abs_of_real, Complex.abs_div, Complex.abs_of_real, Complex.abs_mul, Complex.abs_I]
    norm_num; ring
  have hreal : (f z1).re ≤ 1 := by
    have : (z1 / 2) = ↑(σ / 2) := by simp
    rw [this, ← ofReal_div, ofReal_re, f]
    have hb : Complex.digamma ↑(σ / 2) ≤ ↑(1 : ℝ) := by
      refine digamma_le_one_of_re_pos ?_ <;> simpa [hz1] using hσ <;> norm_num
    exact (Complex.ofReal_le.mp hb)
  have h2a : (f z2).re ≤ (1 / 2 : ℝ) * (γ + 2 * (σ / 2) + 7 + Real.log (|t| / 2 + 2)) := by
    have hIm : 1 ≤ |(z2 / 2).im| := by rw [him2]; rw [← Real.div_le_div_iff₀ (by norm_num)]; linarith
    have hb := digamma_le_log hnz2 hIm
    exact (div_le_div_of_nonneg_left (by linarith) (by norm_num) (by positivity)
      (hb.trans (by linarith))).trans (by linarith)
  have h3a : (f z3).re ≤ (1 / 2 : ℝ) * (γ + 2 * (σ / 2) + 7 + Real.log (|t| + 2)) := by
    have hIm : 1 ≤ |(z3 / 2).im| := by rw [him3]; linarith
    have hb := digamma_le_log hnz3 hIm
    exact (div_le_div_of_nonneg_left (by linarith) (by norm_num) (by positivity)
      (hb.trans (by linarith))).trans (by linarith)
  have hlog_le : Real.log (|t| / 2 + 2) ≤ Real.log (|t| + 2) := by
    exact Real.log_le_log (by linarith [abs_nonneg t]) (by linarith [abs_nonneg t])
  have hσb : σ / 2 ≤ σ := by linarith
  calc 3 * (f z1).re + 4 * (f z2).re + (f z3).re
    _ ≤ 3 * 1 + 4 * (1 / 2 * (γ + σ + 7 + Real.log (|t| + 2))) + (1 / 2 * (γ + σ + 7 + Real.log (|t| + 2))) := by
      linarith [hreal, h2a, h3a, hlog_le, hσb]
    _ = 3 + (5 / 2) * (γ + σ + 7) + (5 / 2) * Real.log (|t| + 2) := by ring
    _ ≤ (5 / 2) * Real.log (|t| + 2) + 20 := by
      have : (5 / 2) * (γ + σ + 7) ≤ 17 := by
        have hγ : γ ≤ 1 := by exact Real.eulerMascheroniConstant_lt_one.le
        have hσ : σ ≤ 2 := by linarith [hσ]
        linarith
      linarith

/-! The main corrected theorem. -/
theorem kadiriLamzouriZetaZeroFreeEdge'
    (xiZeros_infinite : ({z : ℂ | xi z = 0} : Set ℂ).Infinite)
    (s : ℂ) (ht : |s.im| ≥ 1) (hre : s.re ≥ zeroFreeEdge s.im) :
    riemannZeta s ≠ 0 := by
  by_contra hz
  obtain ⟨a, hane, hinj, htend, hzero⟩ :=
    xi_zero_enumeration xiZeros_simple xiZeros_infinite
  have hxi0 : xi s = 0 := by
    have hΓ : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
      intro n hn
      have hre : (s / 2).re = (-(n : ℂ)).re := congrArg Complex.re hn
      simp at hre
      linarith [hre, hre]
    exact xi_zero_iff_riemannZeta_zero hΓ hz
  obtain ⟨k, hk⟩ : ∃ k, s = a k := (hzero s).mp hxi0
  let N : ℕ := k + 1
  let Z : Finset ℂ := Finset.image (fun n => a n) (Finset.range N)
  have hZmem : s ∈ Z := by
    rw [Finset.mem_image]
    refine ⟨k, Finset.mem_range.mpr (by linarith [hk]), hk.symm⟩
  have hZre : ∀ ρ ∈ Z, 0 < ρ.re := by
    rintro _ ⟨n, _, rfl⟩
    exact xi_zero_imp_zero_lt_re (a n) ((hzero (a n)).2 ⟨n, rfl⟩)
  have hZre_lt : ∀ ρ ∈ Z, ρ.re < 1 := by
    rintro _ ⟨n, _, rfl⟩
    exact xi_zero_imp_re_lt_one (a n) ((hzero (a n)).2 ⟨n, rfl⟩)
  have hs2 : Summable fun n : ℕ => (‖a n‖ ^ 2)⁻¹ := by
    have hfinite : ∀ r : ℝ, 1 ≤ r → ({n : ℕ | ‖a n‖ ≤ r} : Set ℕ).Finite := by
      intro r hr
      have hfin : ((Metric.closedBall (0 : ℂ) r : Set ℂ) ∩ {z : ℂ | xi z = 0}).Finite :=
        xiZeros_bounded_finite (Nat.ceil r)
      have heq : ({n : ℕ | ‖a n‖ ≤ r} : Set ℕ) =
          a ⁻¹' ((Metric.closedBall (0 : ℂ) r : Set ℂ) ∩ {z : ℂ | xi z = 0}) := by
        ext n
        constructor <;> intro hn <;> constructor <;> simpa [Metric.mem_closedBall, dist_eq_norm]
          using hn <;> exact (hzero _).2 ⟨n, rfl⟩
      rw [heq]
      exact Set.Finite.preimage (fun _ _ _ _ h => hinj h) hfin
    have hcount : ∃ D : ℝ, 0 ≤ D ∧ ∀ r : ℝ, 1 ≤ r →
        ({n : ℕ | ‖a n‖ ≤ r} : Set ℕ).ncard ≤ D * r ^ (7 / 4 : ℝ) := by
      have hz0 : xi 0 ≠ 0 := by simp [xi]
      have hAn : ∀ R : ℝ, 0 < R → AnalyticOnNhd ℂ xi (Metric.closedBall 0 R) := by
        intro R hR
        exact xi_differentiable.analyticOnNhd (Metric.closedBall 0 R)
      rcases zeroCount_le_rpow_of_orderSet (by norm_num : 0 ≤ (7 / 4 : ℝ))
        (orderSet_xi) hz0 hAn with ⟨D, hD, hb⟩
      refine ⟨D, hD, fun r hr => ?_⟩
      rw [← zeroCount_xi_eq_ncard a hinj hzero r]
      exact hb r hr
    exact_mod_cast summable_inv_norm_pow_of_ncard_bound (by norm_num : 0 ≤ (7 / 4 : ℝ))
      (by norm_num : (7 / 4 : ℝ) < 2) (fun r hr => (hfinite r hr).subset fun _ hn => le_trans hn (Nat.le_ceil r))
      hcount
  obtain ⟨g, hgd, hdecomp⟩ :=
    logDeriv_completedZeta hane hinj hs2 htend hzero xiZeros_simple
  let tail (s' : ℂ) : ℂ := ∑' n : ℕ, (1 / (s' - a (n + N)) + 1 / (a (n + N)))
  let analytic (s' : ℂ) : ℂ := gammaPart g s' - tail s'
  have h_decomp : ∀ s' (hs' : 1 < s'.re),
      LSeries ↗Λ s' = analytic s' - ∑ ρ' ∈ Z, (1 / (s' - ρ') + 1 / ρ') := by
    intro s' hs'
    rw [analytic, tail]
    have hsum : ∑' n : ℕ, (1 / (s' - a n) + 1 / (a n)) =
        ∑ n ∈ Finset.range N, (1 / (s' - a n) + 1 / (a n)) +
        ∑' n : ℕ, (1 / (s' - a (n + N)) + 1 / (a (n + N))) := by
      exact (tsum_eq_sum_range_add_tsum (fun n => (1 / (s' - a n) + 1 / (a n)))
        (by exact summable_of_completion _ hs2 s')).symm
    rw [← hsum]
    have hLS : LSeries ↗Λ s' = gammaPart g s' - ∑' n, (1 / (s' - a n) + 1 / (a n)) := by
      rw [← hdecomp s' hs']
      exact (LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs').symm
    rw [hLS]
    rw [Finset.sum_image (fun n => (1 / (s' - a n) + 1 / (a n))) (Finset.range N) hinj]
    ring
  have hLpos : 0 < Real.log (|s.im| + 10) := Real.log_pos (by linarith [abs_nonneg s.im])
  let A₀ : ℝ := 3
  let A₁ : ℝ := 5 / 2
  let a_par : ℝ := 1 / 5
  let σ : ℝ := 1 + a_par / Real.log (|s.im| + 10)
  have hσgt : 1 < σ := by linarith [div_pos (by norm_num) hLpos]
  have hRHS_pos : 0 < A₀ / (σ - 1) + A₁ * Real.log (|s.im| + 2) + (40 : ℝ) := by
    exact add_pos (div_pos (by norm_num) (by linarith [hσgt]))
      (add_pos (mul_pos (by norm_num) (Real.log_pos (by linarith [abs_nonneg s.im]))) (by norm_num))
  have h_analytic : 3 * (analytic (↑σ : ℂ)).re + 4 * (analytic (↑σ + ↑s.im * I)).re
      + (analytic (↑σ + 2 * ↑s.im * I)).re ≤ A₀ / (σ - 1) + A₁ * Real.log (|s.im| + 2) + 40 := by
    have hγb : 3 * (gammaPart g ↑σ).re + 4 * (gammaPart g (↑σ + ↑s.im * I)).re
        + (gammaPart g (↑σ + 2 * ↑s.im * I)).re
        ≤ A₀ / (σ - 1) + A₁ * Real.log (|s.im| + 2)
          + (40 + |8 * Complex.re (-deriv g ↑σ - (Real.log Real.pi) / 2)|) := by
      rw [gammaPart]
      have hdp : ∀ z, logDeriv (fun x => x.Gammaℝ) z =
            -(Real.log Real.pi) / 2 + (1 / 2 : ℂ) * Complex.digamma (z / 2) := by
        intro z
        have hsz : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
          intro m hm
          have hre : (z / 2).re = (-(m : ℂ)).re := congrArg Complex.re hm
          simp at hre
          linarith
        exact logDeriv_Gammaℝ_eq z hsz
      simp_rw [hdp]
      have hdig := digammaHalf_threeFourOne σ s.im hσgt ht
      have h1 := oneOverSsub1_threeFourOne σ s.im hσgt ht
      have h2 := oneOverS_threeFourOne σ s.im hσgt ht
      have hc : 8 * Complex.re (-deriv g ↑σ - (Real.log Real.pi) / 2)
          ≤ |8 * Complex.re (-deriv g ↑σ - (Real.log Real.pi) / 2)| := by linarith
      linarith
    have htail : 3 * (tail ↑σ).re + 4 * (tail (↑σ + ↑s.im * I)).re + (tail (↑σ + 2 * ↑s.im * I)).re
        ≥ -40 := by
      have hb : ∀ s', ‖tail s'‖ ≤ 1 := by exact tail_norm_le_one a N s'
      have h3t : 3 * (tail ↑σ).re + 4 * (tail (↑σ + ↑s.im * I)).re + (tail (↑σ + 2 * ↑s.im * I)).re
          ≥ -(3 + 4 + 1) * 1 := by
        refine (add_le_add (add_le_add (by linarith [re_le_norm (tail ↑σ)])
          (by linarith [re_le_norm (tail (↑σ + ↑s.im * I))]))
          (by linarith [re_le_norm (tail (↑σ + 2 * ↑s.im * I))])).trans ?_)
        simp
      linarith [hb ↑σ, hb (↑σ + ↑s.im * I), hb (↑σ + 2 * ↑s.im * I)]
    rw [analytic]
    linarith
  have hc_val : a_par * (4 - A₀ - A₁ * a_par) / (A₀ + A₁ * a_par) = 1 / 35 := by norm_num
  have h_c : kadiriConstant / Real.log (|s.im| + 10) <
      4 / (A₀ / (σ - 1) + A₁ * Real.log (|s.im| + 2) + 40) - (σ - 1) := by
    exact edge_gap_positive' s.im ht A₀ A₁ 40 (by norm_num) (by norm_num)
      (by rw [← hc_val]; norm_num)
  exact riemannZeta_ne_zero_of_zeroFreeEdge s ht hre
    σ hσgt Z hZmem hZre hZre_lt analytic h_decomp A₀ A₁ (40 : ℝ)
    (by norm_num) (by norm_num) h_analytic hRHS_pos h_c
