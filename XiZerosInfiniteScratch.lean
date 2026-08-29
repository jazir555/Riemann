import ZeroFreeRegionHadamard

open ZeroFreeRegionHadamard Complex Real Topology Set Function Filter
open scoped BigOperators

noncomputable section

/-!
Root-only scratch for the ξ-zero facts.

NOTE: the genuine, repo-backed proofs live elsewhere:
* `orderSet_xi` is proved in `KadiriOrderInfra.lean`.
* `xiZeros_infinite` (ξ has infinitely many zeros) is proved in `KadiriZeroFree.lean`.

This file therefore only reproduces the elementary equivalence
`xi z = 0 ↔ z` is a nontrivial zero of `ζ`, which needs only
`ZeroFreeRegionHadamard`. The heavy `Zeta23`-based route was abandoned
(building `Zeta23` is too expensive for the standalone toolchain).
-/

/-- A zero of `xi` is exactly a nontrivial zero of `ζ` (a zero in the open
  critical strip `0 < Re z < 1`). -/
theorem xiZero_eq_nontrivialZero {z : ℂ} :
    xi z = 0 ↔ (riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1) := by
  constructor
  · intro hxi
    have hζ := xi_zero_imp_riemannZeta_zero hxi
    have hre0 : 0 < z.re := xi_zero_imp_zero_lt_re hxi
    have hre1 : z.re < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h) hζ
    exact ⟨hζ, hre0, hre1⟩
  · rintro ⟨hζ, hre0, hre1⟩
    have hΓ : ∀ n : ℕ, z / 2 ≠ -(n : ℂ) := by
      intro n hn
      have hre : (z / 2).re = (-(n : ℂ)).re := congrArg Complex.re hn
      simp at hre
      linarith [hre0]
    exact (xi_zero_iff_riemannZeta_zero hΓ).mpr hζ

end
