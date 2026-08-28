import ZeroFreeRegionHadamard
import Zeta23.Assembly
import Zeta23.RvM.Statement
import Zeta23.Statement.SeamClosed
import Zeta23.GammaFacts.Complete

open ZeroFreeRegionHadamard Complex Real Topology Set Function Filter
open scoped BigOperators

noncomputable section

/-- A zero of `xi` is exactly a nontrivial zero of `ζ` (a zero in the open critical strip
  `0 < Re z < 1`). -/
theorem xiZero_eq_nontrivialZero {z : ℂ} : xi z = 0 ↔ Zeta23.IsNontrivialZero z := by
  constructor
  · intro hxi
    have hζ := xi_zero_imp_riemannZeta_zero hxi
    have hre0 : 0 < z.re := xi_zero_imp_zero_lt_re hxi
    have hre1 : z.re < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h) hζ
    exact ⟨hζ, hre0, hre1⟩
  · intro hζ
    have hΓ : ∀ n : ℕ, z / 2 ≠ -(n : ℂ) := by
      intro n hn
      have hre : (z / 2).re = (-(n : ℂ)).re := congrArg Complex.re hn
      simp at hre
      linarith [hζ.2.1]
    exact (xi_zero_iff_riemannZeta_zero hΓ).mpr hζ.1

/-- The zero set of `xi` is exactly the carrier of `Zeta23.zetaZeroConfig`
  (the set of nontrivial zeros of `ζ`). -/
theorem xiZeros_eq_zetaZeroConfig_carrier :
    {z : ℂ | xi z = 0} = Zeta23.zetaZeroConfig.carrier := by
  ext z
  simp [xiZero_eq_nontrivialZero, Zeta23.zetaZeroConfig_carrier, Zeta23.IsNontrivialZero]

/-- The number of nontrivial zeros of `ζ` with ordinate in `(T, 2T]` tends to `+∞` as `T → ∞`,
  by the Riemann–von Mangoldt formula (`Zeta23.Assembly.tendsto_N_atTop`,
  instantiated with `Zeta23.riemannVonMangoldt_zeta`). -/
theorem xiZeroCount_tendsto_atTop :
    Tendsto (fun T : ℝ => (Zeta23.zetaZeroConfig.N T (2 * T) : ℝ)) atTop atTop := by
  exact Zeta23.Assembly.tendsto_N_atTop Zeta23.zetaZeroConfig
    (Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts)

/-- `ξ` has infinitely many zeros.

  The zeros of `ξ` are exactly the nontrivial zeros of `ζ`
  (`xiZeros_eq_zetaZeroConfig_carrier`).  If they were finite, then for all sufficiently large `T`
  the window `{ρ : 0 < Im ρ ≤ 2T}` would contain none of them, so the Riemann–von Mangoldt count
  `N(T,2T)` would be `0` for all large `T` — contradicting `xiZeroCount_tendsto_atTop`
  (`N(T,2T) → ∞`). -/
theorem xiZeros_infinite : ({z : ℂ | xi z = 0} : Set ℂ).Infinite := by
  by_contra hfin
  rw [xiZeros_eq_zetaZeroConfig_carrier] at hfin
  set S := Zeta23.zetaZeroConfig.carrier
  have hSfin : S.Finite := ⟨hfin⟩
  have hT0 : ∃ T0 : ℝ, ∀ ρ ∈ S, ρ.im ≤ T0 := by
    by_cases hne : S.Nonempty
    · have hBdd : BddAbove {ρ.im | ρ ∈ S} :=
        Set.Finite.bddAbove (Set.Finite.image (fun ρ => ρ.im) hSfin)
      exact ⟨Sup {ρ.im | ρ ∈ S},
        fun ρ hρ => le_csSup hBdd (Set.mem_image.mpr ⟨ρ, hρ, rfl⟩)⟩
    · exact ⟨0, fun ρ hρ => (hne (Set.nonempty_of_mem hρ)).elim⟩
  choose T0 hb using hT0
  have hwin : ∀ T : ℝ, T0 ≤ T → Zeta23.zetaZeroConfig.window T (2 * T) = ∅ := by
    intro T hT
    ext ρ
    constructor
    · intro hρw
      have hc : ρ ∈ S := Zeta23.zetaZeroConfig.window_subset_carrier T (2 * T) hρw
      have hmem : Zeta23.IsNontrivialZero ρ ∧ T < ρ.im ∧ ρ.im ≤ 2 * T := by
        simpa [Zeta23.ZeroConfig.window] using hρw
      linarith [hmem.2.1, hb ρ hc, le_abs_self ρ.im, hT]
    · intro h
      contradiction
  have hN0 : ∀ T : ℝ, T0 ≤ T → Zeta23.zetaZeroConfig.N T (2 * T) = 0 := by
    intro T hT
    rw [Zeta23.ZeroConfig.N, hwin T hT]
    rw [finsum_mem_eq_finite_toFinset_sum (Set.finite_empty),
      Set.toFinset_empty, Finset.sum_empty]
  have hpos : ∀ᶠ T in atTop, (1 : ℝ) ≤ (Zeta23.zetaZeroConfig.N T (2 * T) : ℝ) :=
    xiZeroCount_tendsto_atTop 1
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hpos
  let T := max T0 T₁
  have hT0 : T0 ≤ T := le_max_left T0 T₁
  have hTT₁ : T₁ ≤ T := le_max_right T0 T₁
  have h1 : (1 : ℝ) ≤ (Zeta23.zetaZeroConfig.N T (2 * T) : ℝ) := hT₁ T hTT₁
  rw [hN0 T hT0] at h1
  norm_num at h1

end
