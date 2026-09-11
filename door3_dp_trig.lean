import Mathlib
/-!
# Door 3, stage 1: rigorous sine / cosine polynomial enclosures.

Status: stage 1 is delivered in this file. The banked Mathlib facts used are
`Real.one_sub_sq_div_two_le_cos`, `Real.sin_ge_sub_cube`, `Real.sin_bound`,
`Real.sin_sub_int_mul_two_pi`, and `Real.cos_sub_int_mul_two_pi`.

What is proved here (all with full proofs, explicit binders):
* `dp_cos_quad_floor`: quadratic cosine floor for every real `x`.
* `dp_sin_cubic_floor`: cubic sine floor for `0 <= x`.
* `dp_sin_cubic_ceil100`: weak cubic-plus-quintic sine ceiling with constant
  `1 / 100` for `|x| <= 1`, from banked `Real.sin_bound`.
* `dp_arg_reduce_mem`: for `|x| <= 40` there is an integer `k` with the shifted
  argument `x - k * (2 * pi)` inside `[-pi, pi]` (proved for every real `x`).
* `dp_sin_reduce` / `dp_cos_reduce`: sine / cosine invariance under the shift.
* `dp_sin_enclose_of_reduced`: for `|x| <= 40`, with reduced argument `r`
  satisfying `|r| <= 1`, an explicit two-sided enclosure of `Real.sin x`
  around `r - r ^ 3 / 6` of width at most `1 / 50`, in two sign cases.

Residual for stage 2 (exact statement, left for the sibling task):
* R1, sharp sine ceiling: for every `x` with `0 <= x` and `x <= 1`,
  `Real.sin x <= x - x ^ 3 / 6 + x ^ 5 / 120`.
  Suggested route: fourth-order Taylor with Lagrange remainder, i.e. there is
  a point `xi` between `0` and `x` with
  `Real.sin x = (x - x ^ 3 / 6) + Real.cos xi * x ^ 5 / 120`,
  then use `Real.cos xi <= 1`. The weak form with `|x| ^ 5 / 100` proved here
  already gives width `<= 1 / 50` when `|r| <= 1`, so stage 2 can proceed.
* R2, large reduced arguments: for `1 < |r|` and `|r| <= pi`, constant or
  cosine-side polynomial enclosures per octant (at most 8 cases) with
  `norm_num`-checked rational endpoints.
* R3, term discs: combine these enclosures with the banked `Real.log`
  numeral bounds (for example the `log 2` upper bounds used by the cell
  suppliers) to certify each Taylor disc.
-/

/-- Quadratic cosine floor for every real `x` (one rewrite of the banked lemma). -/
theorem dp_cos_quad_floor (x : ℝ) : 1 - x ^ 2 / 2 ≤ Real.cos x :=
  Real.one_sub_sq_div_two_le_cos

/-- Cubic sine floor for `0 <= x` (wrapper around the banked lemma). -/
theorem dp_sin_cubic_floor (x : ℝ) (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x :=
  Real.sin_ge_sub_cube hx

/-- Weak sine ceiling for `|x| <= 1` with constant `1 / 100` (from banked `Real.sin_bound`).
This is the banked stand-in for residual R1, which tightens `1 / 100` to `1 / 120`. -/
theorem dp_sin_cubic_ceil100 (x : ℝ) (hx : |x| ≤ 1) :
    Real.sin x ≤ x - x ^ 3 / 6 + |x| ^ 5 / 100 := by
  have hB := Real.sin_bound hx
  have hself : Real.sin x - (x - x ^ 3 / 6) ≤ |Real.sin x - (x - x ^ 3 / 6)| :=
    le_abs_self _
  have hle : Real.sin x - (x - x ^ 3 / 6) ≤ |x| ^ 5 / 100 := le_trans hself hB
  linarith

/-- Argument reduction: for `|x| <= 40` some integer shift lands in `[-pi, pi]`.
The proof is general (the `40` bound is not needed). -/
theorem dp_arg_reduce_mem (x : ℝ) (hx : |x| ≤ 40) :
    ∃ k : ℤ, |x - (k : ℝ) * (2 * Real.pi)| ≤ Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hT : 0 < 2 * Real.pi := by linarith
  have hTne : 2 * Real.pi ≠ 0 := ne_of_gt hT
  have h1 : ((Int.floor (x / (2 * Real.pi) + 1 / 2) : ℤ) : ℝ)
      ≤ x / (2 * Real.pi) + 1 / 2 := Int.floor_le _
  have h2 : x / (2 * Real.pi) + 1 / 2
      < ((Int.floor (x / (2 * Real.pi) + 1 / 2) : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  refine ⟨Int.floor (x / (2 * Real.pi) + 1 / 2), ?_⟩
  have hxeq : x / (2 * Real.pi) * (2 * Real.pi) = x := div_mul_cancel₀ x hTne
  have hdecomp : x - ((Int.floor (x / (2 * Real.pi) + 1 / 2) : ℤ) : ℝ) * (2 * Real.pi)
      = (x / (2 * Real.pi) - ((Int.floor (x / (2 * Real.pi) + 1 / 2) : ℤ) : ℝ))
        * (2 * Real.pi) := by
    rw [sub_mul, hxeq]
  have habs : |x / (2 * Real.pi) - ((Int.floor (x / (2 * Real.pi) + 1 / 2) : ℤ) : ℝ)|
      ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have habs2 : |x - ((Int.floor (x / (2 * Real.pi) + 1 / 2) : ℤ) : ℝ) * (2 * Real.pi)|
      = |x / (2 * Real.pi) - ((Int.floor (x / (2 * Real.pi) + 1 / 2) : ℤ) : ℝ)|
        * (2 * Real.pi) := by
    rw [hdecomp, abs_mul, abs_of_pos hT]
  have hmul : |x / (2 * Real.pi) - ((Int.floor (x / (2 * Real.pi) + 1 / 2) : ℤ) : ℝ)|
        * (2 * Real.pi)
      ≤ 1 / 2 * (2 * Real.pi) :=
    mul_le_mul_of_nonneg_right habs (le_of_lt hT)
  have hhalf : 1 / 2 * (2 * Real.pi) = Real.pi := by ring
  rw [habs2]
  rw [hhalf] at hmul
  exact hmul

/-- Sine is invariant under integer shifts by `2 * pi`. -/
theorem dp_sin_reduce (x : ℝ) (k : ℤ) :
    Real.sin (x - (k : ℝ) * (2 * Real.pi)) = Real.sin x :=
  Real.sin_sub_int_mul_two_pi x k

/-- Cosine is invariant under integer shifts by `2 * pi`. -/
theorem dp_cos_reduce (x : ℝ) (k : ℤ) :
    Real.cos (x - (k : ℝ) * (2 * Real.pi)) = Real.cos x :=
  Real.cos_sub_int_mul_two_pi x k

/-- Combined enclosure: for `|x| <= 40`, with reduced argument `r` satisfying
`|r| <= 1`, sine equals `sin r` and lies in the explicit interval
`[r - r ^ 3 / 6 - |r| ^ 5 / 100, r - r ^ 3 / 6 + |r| ^ 5 / 100]`
of width at most `1 / 50`. The proof splits on the sign of `r` (two cases),
using the floor on the nonneg side and oddness on the negative side. -/
theorem dp_sin_enclose_of_reduced (x : ℝ) (hx : |x| ≤ 40) (k : ℤ) (r : ℝ)
    (hrdef : r = x - (k : ℝ) * (2 * Real.pi)) (hred : |r| ≤ 1) :
    ∃ lo hi : ℝ, lo = r - r ^ 3 / 6 - |r| ^ 5 / 100 ∧
      hi = r - r ^ 3 / 6 + |r| ^ 5 / 100 ∧
      lo ≤ Real.sin x ∧ Real.sin x ≤ hi ∧ hi - lo ≤ 1 / 50 ∧
      Real.sin x = Real.sin r := by
  have hB : Real.sin r ≤ r - r ^ 3 / 6 + |r| ^ 5 / 100 :=
    dp_sin_cubic_ceil100 r hred
  have hpow : |r| ^ 5 ≤ 1 := pow_le_one₀ (abs_nonneg _) hred
  have hnn : (0 : ℝ) ≤ |r| ^ 5 / 100 :=
    div_nonneg (pow_nonneg (abs_nonneg _) _) (by norm_num)
  have hwidth : (r - r ^ 3 / 6 + |r| ^ 5 / 100) - (r - r ^ 3 / 6 - |r| ^ 5 / 100)
      ≤ 1 / 50 := by
    linarith
  have hsin_eq : Real.sin x = Real.sin r := by
    rw [hrdef]
    exact (dp_sin_reduce x k).symm
  rcases le_total 0 r with hr0 | hrneg
  · have hfloor := dp_sin_cubic_floor r hr0
    have hlo : r - r ^ 3 / 6 - |r| ^ 5 / 100 ≤ Real.sin r := by linarith
    refine ⟨r - r ^ 3 / 6 - |r| ^ 5 / 100, r - r ^ 3 / 6 + |r| ^ 5 / 100,
      rfl, rfl, ?_, ?_, ?_, hsin_eq⟩
    · rw [hsin_eq]
      exact hlo
    · rw [hsin_eq]
      exact hB
    · exact hwidth
  · have hs0 : 0 ≤ -r := by linarith
    have hs1 : |-r| ≤ 1 := by
      rw [abs_neg]
      exact hred
    have hfloor := dp_sin_cubic_floor (-r) hs0
    have hBs : Real.sin (-r) ≤ -r - (-r) ^ 3 / 6 + |-r| ^ 5 / 100 :=
      dp_sin_cubic_ceil100 (-r) hs1
    have hsin_r : Real.sin r = -Real.sin (-r) := by
      have h := Real.sin_neg (-r)
      rwa [neg_neg] at h
    have habs_eq : |-r| = |r| := abs_neg r
    have hcub : -r - (-r) ^ 3 / 6 = -(r - r ^ 3 / 6) := by ring
    rw [habs_eq] at hBs
    rw [hcub] at hfloor hBs
    have hlo : r - r ^ 3 / 6 - |r| ^ 5 / 100 ≤ Real.sin r := by
      rw [hsin_r]
      linarith
    have hhi : Real.sin r ≤ r - r ^ 3 / 6 + |r| ^ 5 / 100 := by
      rw [hsin_r]
      linarith
    refine ⟨r - r ^ 3 / 6 - |r| ^ 5 / 100, r - r ^ 3 / 6 + |r| ^ 5 / 100,
      rfl, rfl, ?_, ?_, ?_, hsin_eq⟩
    · rw [hsin_eq]
      exact hlo
    · rw [hsin_eq]
      exact hhi
    · exact hwidth
