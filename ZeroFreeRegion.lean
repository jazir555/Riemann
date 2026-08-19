import ZeroFreeRegionProof

open Complex Real Topology Filter
open scoped BigOperators

noncomputable section

/-- Basic trigonometric inequality:
    3 + 4 cos θ + cos 2θ = 2(1 + cos θ)^2 ≥ 0. -/
theorem trig_inequality (θ : ℝ) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  have h2 : Real.cos (2 * θ) = 2 * (Real.cos θ) ^ 2 - 1 :=
    Real.cos_two_mul θ
  rw [h2]
  have hsq :
      3 + 4 * Real.cos θ + (2 * (Real.cos θ) ^ 2 - 1) =
        2 * (Real.cos θ + 1) ^ 2 := by
    ring
  rw [hsq]
  exact mul_nonneg (by norm_num) (sq_nonneg _)

-- kadiriConstant and zeroFreeEdge are now imported from ZeroFreeRegionProof

/-- Correct conditional zero-free statement.

The first argument is exactly the Kadiri–Lamzouri zero-free region:
for |Im(s)| ≥ 1 and Re(s) ≥ zeroFreeEdge(Im(s)), ζ(s) ≠ 0.

Given that input, this proves nonvanishing in the two edge regions:
1. directly near Re(s) = 1;
2. near Re(s) = 0 by applying the functional equation to 1 - s.

The middle gap is intentionally excluded, because ζ has nontrivial zeros there.
-/
theorem riemannZeta_ne_zero_near_edges
    (kadiri_lamzouri_zero_free_edge :
      ∀ s : ℂ,
        |s.im| ≥ 1 →
        s.re ≥ zeroFreeEdge s.im →
        riemannZeta s ≠ 0)
    (s : ℂ)
    (hs0 : 0 < s.re)
    (hs1 : s.re < 1)
    (ht : |s.im| ≥ 10)
    (hedge :
      s.re ≥ zeroFreeEdge s.im ∨
      s.re ≤ kadiriConstant / Real.log (|s.im| + 10)) :
    riemannZeta s ≠ 0 := by
  rcases hedge with h | hsmall
  · -- Right edge: direct application of the assumed zero-free region.
    exact kadiri_lamzouri_zero_free_edge s (by linarith) h
  · -- Left edge: use the functional equation to move to 1 - s.
    have hs1' : s ≠ 1 := by
      intro h
      have : (1 : ℝ) < 1 := by
        simpa [h, Complex.one_re] using hs1
      linarith

    have hs_not_neg : ∀ n : ℕ, s ≠ -n := by
      intro n hn
      have hre : s.re = -(n : ℝ) := by
        have := congr_arg Complex.re hn
        simp at this
        exact this
      have hn : (0 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.zero_le n
      linarith

    intro hz

    -- Functional equation:
    -- ζ(1 - s) = factor * ζ(s)
    have hfe := riemannZeta_one_sub hs_not_neg hs1'

    have h1s_zero : riemannZeta (1 - s) = 0 := by
      rw [hfe, hz]
      simp

    have h1s_ht : |(1 - s).im| ≥ 1 := by
      have : |s.im| ≥ 1 := by linarith
      simpa [Complex.sub_im, abs_neg] using this

    have h1s_edge : (1 - s).re ≥ zeroFreeEdge (1 - s).im := by
      unfold zeroFreeEdge
      simp [Complex.sub_re, Complex.sub_im, abs_neg]
      linarith

    exact kadiri_lamzouri_zero_free_edge (1 - s) h1s_ht h1s_edge h1s_zero

/-- Equivalent formulation: outside the middle gap, the conditional zero-free
result applies. The hypothesis `hgap` is essential. Without it, the statement
is false because of the nontrivial zeros. -/
theorem riemannZeta_ne_zero_outside_middle_gap
    (kadiri_lamzouri_zero_free_edge :
      ∀ s : ℂ,
        |s.im| ≥ 1 →
        s.re ≥ zeroFreeEdge s.im →
        riemannZeta s ≠ 0)
    (s : ℂ)
    (hs0 : 0 < s.re)
    (hs1 : s.re < 1)
    (ht : |s.im| ≥ 10)
    (hgap :
      ¬ (kadiriConstant / Real.log (|s.im| + 10) < s.re ∧
         s.re < zeroFreeEdge s.im)) :
    riemannZeta s ≠ 0 := by
  by_cases hfree : s.re ≥ zeroFreeEdge s.im
  · exact kadiri_lamzouri_zero_free_edge s (by linarith) hfree
  · push_neg at hfree
    have hsmall : s.re ≤ kadiriConstant / Real.log (|s.im| + 10) := by
      by_contra h
      push_neg at h
      exact hgap ⟨h, hfree⟩
    exact
      riemannZeta_ne_zero_near_edges
        kadiri_lamzouri_zero_free_edge s hs0 hs1 ht (Or.inr hsmall)

end
