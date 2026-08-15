import ZeroFreeRegionHadamard

open Complex Finset Real HurwitzZeta ZeroFreeRegionHadamard
open scoped Topology Filter
open Filter Metric

set_option maxHeartbeats 800000 in
theorem logDeriv_xi_of_factorization {a : ℕ → ℂ} {g : ℂ → ℂ} {z : ℂ}
    (hane : ∀ n, a n ≠ 0) (hs2 : Summable fun n : ℕ => (‖a n‖ ^ 2)⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop)
    (hgd : Differentiable ℂ g)
    (hxi : ∀ w, xi w = Complex.exp (g w) * canonicalProductNat 1 a w)
    (hzane : ∀ n, z ≠ a n) :
    logDeriv xi z = deriv g z + ∑' n, (1 / (z - a n) + 1 / a n) := by
  let P : ℂ → ℂ := canonicalProductNat 1 a
  have hP0 : P z ≠ 0 := by
    dsimp [P]
    exact canonicalProductNat_ne_zero hane 1 hzane hs2 htend
  have hlogP : logDeriv P z = ∑' n, (1 / (z - a n) + 1 / a n) := by
    dsimp [P]
    exact logDeriv_canonicalProductNat_genus_one hane hs2 htend hzane
  have hlogexp : logDeriv (fun w : ℂ => Complex.exp (g w)) z = deriv g z := by
    rw [logDeriv_apply]
    have h₁ : DifferentiableAt ℂ Complex.exp (g z) := Complex.differentiableAt_exp (x := g z)
    have h₂ : DifferentiableAt ℂ g z := hgd.differentiableAt
    have hc := deriv_comp z h₁ h₂
    rw [show (fun w : ℂ => Complex.exp (g w)) = Complex.exp ∘ g from rfl, hc]
    rw [show deriv Complex.exp (g z) = Complex.exp (g z) from (Complex.hasDerivAt_exp (g z)).deriv]
    ring
    exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)
  have hlogmul : logDeriv (fun w : ℂ => Complex.exp (g w) * P w) z =
      logDeriv (fun w : ℂ => Complex.exp (g w)) z + logDeriv P z := by
    exact logDeriv_mul z (Complex.exp_ne_zero (g z)) hP0
      (DifferentiableAt.comp z (Complex.differentiableAt_exp (x := g z)) hgd.differentiableAt)
      (differentiable_canonicalProductNat hane 1 hs2 htend).differentiableAt
  have hfun : xi = fun w : ℂ => Complex.exp (g w) * P w := by
    funext w
    exact hxi w
  rw [hfun, hlogmul, hlogexp, hlogP]

set_option maxHeartbeats 800000 in
theorem neg_logDeriv_riemannZeta_eq_xi {s : ℂ} (hs : s ≠ 0) (hs1 : s ≠ 1)
    (hΓ : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) (hζ0 : riemannZeta s ≠ 0) :
    - deriv riemannZeta s / riemannZeta s =
      - logDeriv xi s + 1 / s + 1 / (s - 1) + logDeriv (fun x : ℂ => x.Gammaℝ) s := by
  let Λ : ℂ → ℂ := completedRiemannZeta
  let G : ℂ → ℂ := fun x : ℂ => x.Gammaℝ
  have hG0 : G s ≠ 0 := by
    dsimp [G]
    rw [Complex.Gammaℝ_def]
    apply mul_ne_zero
    · rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero)]
      exact Complex.exp_ne_zero _
    · exact Complex.Gamma_ne_zero hΓ
  have hΛ0 : Λ s ≠ 0 := by
    dsimp [Λ]
    intro hΛ
    have hdef := riemannZeta_def_of_ne_zero hs
    rw [hΛ] at hdef
    exact hζ0 (by rw [hdef]; simp)
  have hΛd : DifferentiableAt ℂ Λ s := by
    dsimp [Λ]
    exact differentiableAt_completedZeta hs hs1
  have hGd : DifferentiableAt ℂ G s := by
    dsimp [G]
    apply DifferentiableAt.mul
    · have hh : HasDerivAt (fun x : ℂ => -x / 2) (-1 / 2) s := by
        rw [show (fun x : ℂ => -x / 2) = fun x : ℂ => (-1 / 2) * x from by
          funext x
          ring]
        exact hasDerivAt_const_mul (-1 / 2)
      have hc : HasDerivAt (fun x : ℂ => (π : ℂ) ^ (-x / 2)) _ s :=
        HasDerivAt.cpow (hasDerivAt_const s (π : ℂ)) hh
          (Complex.ofReal_mem_slitPlane.mpr Real.pi_pos)
      exact hc.differentiableAt
    · have hhalf : DifferentiableAt ℂ (fun x : ℂ => x / 2) s := by fun_prop
      exact DifferentiableAt.comp s (Complex.differentiableAt_Gamma (s / 2) (by
        intro m hm
        exact hΓ m (by simpa using hm))) hhalf
  have hζeq : riemannZeta =ᶠ[𝓝 s] (fun x : ℂ => Λ x / G x) := by
    filter_upwards [(isOpen_ne (x := (0 : ℂ))).mem_nhds hs] with x hx
    simpa [Λ, G] using riemannZeta_def_of_ne_zero hx
  have hlogζ : logDeriv riemannZeta s = logDeriv Λ s - logDeriv G s := by
    have hcongr : logDeriv riemannZeta s = logDeriv (fun x : ℂ => Λ x / G x) s := by
      rw [logDeriv_apply]
      rw [hζeq.deriv_eq, hζeq.eq_of_nhds, logDeriv_apply]
    rw [hcongr]
    have hloginv : logDeriv (fun x : ℂ => (G x)⁻¹) s = -logDeriv G s := by
      rw [logDeriv_apply]
      rw [show deriv (fun x : ℂ => (G x)⁻¹) s = -deriv G s / G s ^ 2 by
        exact (HasDerivAt.inv (hGd.hasDerivAt) hG0).deriv]
      rw [logDeriv_apply]
      field_simp [hG0]
    have hm : logDeriv (fun x : ℂ => Λ x / G x) s = logDeriv Λ s - logDeriv G s := by
      rw [show (fun x : ℂ => Λ x / G x) = fun x : ℂ => Λ x * G⁻¹ x from by
        funext x
        rw [div_eq_mul_inv]
        rfl]
      rw [logDeriv_mul s hΛ0 (inv_ne_zero (a := G s) hG0) hΛd (DifferentiableAt.inv hGd hG0)]
      rw [show logDeriv G⁻¹ s = logDeriv (fun x : ℂ => (G x)⁻¹) s from rfl, hloginv]
      ring
    exact hm
  have hxiΛ : xi =ᶠ[𝓝 s] (fun x : ℂ => x * (x - 1) * Λ x) := by
    filter_upwards [(isOpen_ne (x := (0 : ℂ))).mem_nhds hs,
      (isOpen_ne (x := (1 : ℂ))).mem_nhds hs1] with x hx0 hx1
    simpa [Λ] using xi_eq_mul_completedRiemannZeta hx0 hx1
  have hlogxi : logDeriv xi s = 1 / s + 1 / (s - 1) + logDeriv Λ s := by
    have hlogcongr : logDeriv xi s = logDeriv (fun x : ℂ => x * (x - 1) * Λ x) s := by
      rw [logDeriv_apply]
      rw [hxiΛ.deriv_eq, hxiΛ.eq_of_nhds, logDeriv_apply]
    rw [hlogcongr]
    have h1 : logDeriv (fun x : ℂ => x) s = 1 / s := by
      rw [logDeriv_apply]
      simp
    have h2 : logDeriv (fun x : ℂ => x - 1) s = 1 / (s - 1) := by
      rw [logDeriv_apply]
      have hd : deriv (fun x : ℂ => x - 1) s = 1 := by
        simpa using ((hasDerivAt_id s).sub (hasDerivAt_const s (1 : ℂ))).deriv
      rw [hd]
    have hlogid : logDeriv (fun x : ℂ => x * (x - 1)) s = 1 / s + 1 / (s - 1) := by
      rw [← h1, ← h2]
      exact logDeriv_mul s (by simpa using hs) (sub_ne_zero.mpr hs1) (by fun_prop) (by fun_prop)
    have hm : logDeriv (fun x : ℂ => x * (x - 1) * Λ x) s =
        logDeriv (fun x : ℂ => x * (x - 1)) s + logDeriv Λ s := by
      exact logDeriv_mul s (mul_ne_zero hs (sub_ne_zero.mpr hs1)) hΛ0 (by fun_prop) hΛd
    rw [hm, hlogid]
  rw [show - deriv riemannZeta s / riemannZeta s = - logDeriv riemannZeta s from by
    rw [logDeriv_apply]
    ring]
  rw [hlogζ, hlogxi]
  ring

set_option maxHeartbeats 800000 in
theorem logDeriv_completedZeta {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0)
    (hinj : Function.Injective a) (hs2 : Summable fun n : ℕ => (‖a n‖ ^ 2)⁻¹)
    (htend : Tendsto (fun n : ℕ => ‖a n‖) atTop atTop)
    (hzero : ∀ z, xi z = 0 ↔ ∃ n, z = a n)
    (hord : ∀ z, meromorphicOrderAt xi z ≤ 1) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ s, 1 < s.re ->
        - deriv riemannZeta s / riemannZeta s =
          (- deriv g s + 1 / s + 1 / (s - 1) + logDeriv (fun x : ℂ => x.Gammaℝ) s) -
            ∑' n, (1 / (s - a n) + 1 / a n) := by
  rcases hadamard_factorization_genus_one (f := xi) xi_differentiable hane hzero hord hinj hs2 htend with
    ⟨g, hgd, hxi⟩
  refine ⟨g, hgd, ?_⟩
  intro s hsre
  have h1 : 1 ≤ s.re := le_of_lt hsre
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re h1
  have hs : s ≠ 0 := by
    intro h
    rw [h] at hsre
    norm_num at hsre
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hsre
    norm_num at hsre
  have hΓ : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
    intro n hn
    have hre : (s / 2).re = (-(n : ℂ)).re := congrArg Complex.re hn
    simp at hre
    linarith
  have hxi0 : xi s ≠ 0 := by
    intro h
    exact hζ0 ((xi_zero_iff_riemannZeta_zero hΓ).mp h)
  have hzane : ∀ n : ℕ, s ≠ a n := by
    intro n hn
    exact hxi0 ((hzero s).2 ⟨n, hn⟩)
  have hlog := logDeriv_xi_of_factorization (a := a) (g := g) hane hs2 htend hgd hxi hzane
  have hbridge := neg_logDeriv_riemannZeta_eq_xi hs hs1 hΓ hζ0
  rw [hbridge, hlog]
  ring