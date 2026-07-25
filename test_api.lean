import Mathlib

-- Step by step test for hform
theorem test_hform (t : ℝ) :
    completedRiemannZeta₀ ((1 / 2 : ℂ) + I * t) =
      FourierTransform.fourier
        (fun u => Real.exp (-(1/4:ℝ) * u) • (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (-u)))
        (t / (4 * Real.pi)) / 2 := by
  simp only [completedRiemannZeta₀, HurwitzZeta.completedHurwitzZetaEven₀, WeakFEPair.Λ₀]
  rw [mellin_eq_fourier]
  sorry -- check what goal looks like here

-- Step by step test for cocompact
theorem test_cocompact : (Filter.cocompact ℝ : Filter ℝ) ≤ Filter.atTop := by
  have := cocompact_eq_atBot_atTop (α := ℝ)
  rw [this]
  exact inf_le_right

-- Step by step for hfreq
theorem test_hfreq : Filter.Tendsto (fun t : ℝ => t / (4 * Real.pi)) Filter.atTop Filter.atTop := by
  have h1 : Filter.Tendsto (id : ℝ → ℝ) Filter.atTop Filter.atTop := Filter.tendsto_id
  have h2 : Tendsto (fun _ : ℝ => (4 * Real.pi : ℝ)) Filter.atTop (nhds (4 * Real.pi)) :=
    tendsto_const_nhds
  have := Filter.Tendsto.div h1 h2 (by norm_num : (4 * Real.pi : ℝ) ≠ 0)
  simp [div_eq_mul_inv] at this
  exact this
