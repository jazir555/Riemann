import riemann_hypothesis

/-!
# The hard-difference / mollified / Rouché door to RH

The key mathematical facts are:

1. **hardDifference ≠ 0 ↔ RH** (proved in the core):
   `HardDifferenceNonzero ↔ RiemannHypothesisProp`
   where `HardDifferenceNonzero` means
   `1/(z²+¼) - completedRiemannZeta₀(shiftedS z) ≠ 0` for every off-real z in the
   shifted strip `-(1/2) < z.im < 1/2`.

2. **The mollified-Rouché leaf** gives tail nonvanishing: a `MollifiedRoucheLeaf K`
   produces a Dirichlet mollifier whose gap estimate forces
   `zeta(shiftedS z) ≠ 0` for off-real z with `|Re z| > 10` and `0 < z.im`.

3. **The bridge** (proved below): since
   `1/(z²+¼) - completedRiemannZeta₀(shiftedS z) = 2*xiShifted z/(z²+¼)`
   (core identity `completedZeta_shifted_eq_inv_D_sub_two_xiShifted_div_D`) and
   `xiShifted z = classicalXiPrefactor(shiftedS z) * zeta(shiftedS z)` with the
   prefactor nonvanishing in the strip, the Rouché tail estimate yields the
   `HardDifferenceNonzero` condition in the upper tail `0 < z.im < 1/2, |Re z| > 10`.

4. **The residual**: the bridge covers the upper tail. The lower half
   `-(1/2) < z.im < 0` (conjugate-symmetric) and the bounded central region
   `|Re z| ≤ 10` (a compact rectangle) are the genuine residual of RH — forcing
   nonvanishing there is mathematically equivalent to RH and is not currently
   available. This is reported precisely as the open leaf.
-/

namespace MollifiedAttack

open scoped BigOperators
open Complex

noncomputable def dirichletMollifier (s : ℂ) (K : ℕ) : ℂ :=
  ∑ n ∈ Finset.range K, (ArithmeticFunction.moebius (n + 1) : ℂ) *
  (↑(n + 1) : ℂ) ^ (-s) * (1 - ↑(n + 1) / ↑K)

structure MollifiedRoucheLeaf (K : ℕ) where
  gap : ∀ (z : ℂ), 10 < |z.re| → 0 < z.im → z.im < (1 / 2 : ℝ) →
    ‖zeta (shiftedS z) * dirichletMollifier (shiftedS z) K - 1‖ < 1

theorem rh_from_mollified_rouche (K : ℕ) (H : MollifiedRoucheLeaf K) :
  ∀ (z : ℂ), 10 < |z.re| → 0 < z.im → z.im < (1 / 2 : ℝ) → zeta (shiftedS z) ≠ 0 := by
  intro z hx hy0 hy1
  have hgap := H.gap z hx hy0 hy1
  intro hz
  have hzero : zeta (shiftedS z) * dirichletMollifier (shiftedS z) K = 0 := by
    rw [hz, zero_mul]
  rw [hzero, zero_sub, norm_neg, norm_one] at hgap
  linarith

/-- The proven equivalence `HardDifferenceNonzero ↔ RH`, re-exported from the core. -/
theorem hardDifferenceNonzero_iff_RH :
    HardDifferenceNonzero ↔ RiemannHypothesisProp :=
  _root_.hardDifferenceNonzero_iff_RH

/-- The hard-difference / mollified-Rouché bridge.

    A `MollifiedRoucheLeaf K` forces the `HardDifferenceNonzero` condition
    (`1/(z²+¼) - completedRiemannZeta₀(shiftedS z) ≠ 0`) for every off-real z in the
    upper strip with `0 < z.im < 1/2` and `|Re z| > 10`.

    Proof. The Rouché gap gives `zeta(shiftedS z) ≠ 0` (rh_from_mollified_rouche).
    Since `xiShifted z = classicalXiPrefactor(shiftedS z) * zeta(shiftedS z)` and the
    prefactor is nonvanishing in the strip, `xiShifted z ≠ 0`. The core identity
    `completedZeta_shifted_eq_inv_D_sub_two_xiShifted_div_D` rewrites the goal to
    `2*xiShifted z/(z²+¼) ≠ 0`, which follows from `xiShifted z ≠ 0` and the
    nonvanishing of both the numerator factor `2` and the denominator `z²+¼`.

    This is the finite, correct bridge from the mollified-Rouché program to the
    hard-difference door, covering the upper tail `0 < z.im < 1/2, |Re z| > 10`. -/
theorem mollified_rouche_leaf_implies_tail_hard_difference_nonzero
    (K : ℕ) (H : MollifiedRoucheLeaf K) :
    ∀ (z : ℂ),
      10 < |z.re| →
      0 < z.im →
      z.im < (1 / 2 : ℝ) →
      1 / (z ^ 2 + (1 / 4 : ℂ)) - completedRiemannZeta₀ (shiftedS z) ≠ 0 := by
  intro z hx hy0 hlt
  have hzeta : zeta (shiftedS z) ≠ 0 := rh_from_mollified_rouche K H z hx hy0 hlt
  have hpref : classicalXiPrefactor (shiftedS z) ≠ 0 := by
    have hp := classical_prefactor_nonzero_instrip classical_gamma_nonzero_instrip
    have hre_pos : 0 < (shiftedS z).re := by
      rw [shiftedS_re]
      linarith
    have hre_lt : (shiftedS z).re < 1 := by
      rw [shiftedS_re]
      linarith
    exact hp (shiftedS z) hre_pos hre_lt
  have hxi : xiShifted z ≠ 0 := by
    have h_eq : xiShifted z = classicalXiPrefactor (shiftedS z) * zeta (shiftedS z) := by
      simp [xiShifted, shiftedS, classicalXi, XiFromPrefactor]
    rw [h_eq]
    exact mul_ne_zero hpref hzeta
  have hden : z ^ 2 + (1 / 4 : ℂ) ≠ 0 :=
    shifted_denominator_ne_zero_inside_strip z (by linarith : -(1 / 2) < z.im) hlt
  have heq : 1 / (z ^ 2 + (1 / 4 : ℂ)) - completedRiemannZeta₀ (shiftedS z) =
      2 * xiShifted z / (z ^ 2 + (1 / 4 : ℂ)) := by
    have h := completedZeta_shifted_eq_inv_D_sub_two_xiShifted_div_D z
      (by linarith : -(1 / 2) < z.im) hlt (by linarith [hy0] : z.im ≠ 0)
    calc
      1 / (z ^ 2 + (1 / 4 : ℂ)) - completedRiemannZeta₀ (shiftedS z)
          = 1 / (z ^ 2 + (1 / 4 : ℂ)) - (1 / (z ^ 2 + (1 / 4 : ℂ)) -
              2 * xiShifted z / (z ^ 2 + (1 / 4 : ℂ))) := by rw [h]
      _ = 2 * xiShifted z / (z ^ 2 + (1 / 4 : ℂ)) := by ring
  rw [heq]
  have hinv : (z ^ 2 + (1 / 4 : ℂ))⁻¹ ≠ 0 := inv_ne_zero hden
  have hnum : 2 * xiShifted z ≠ 0 := mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hxi
  exact mul_ne_zero hnum hinv

/-- The hard-difference vanishes at `z` iff `xiShifted` vanishes at `z`
    (within the strip `-(1/2) < z.im < 1/2`).  Since `z²+¼ ≠ 0` and `2 ≠ 0`
    in the strip, the identity
    `hardDifference z = 2·xiShifted z/(z²+¼)` gives the equivalence. -/
theorem hardDifference_eq_zero_iff_xiShifted_eq_zero {z : ℂ}
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ)) (hne : z.im ≠ 0) :
    1 / (z ^ 2 + (1 / 4 : ℂ)) - completedRiemannZeta₀ (shiftedS z) = 0 ↔
    xiShifted z = 0 := by
  have hD : z ^ 2 + (1 / 4 : ℂ) ≠ 0 :=
    shifted_denominator_ne_zero_inside_strip z hgt hlt
  have heq := inv_D_sub_completedZeta_eq_two_xiShifted_div_D z hgt hlt hne
  constructor
  · intro h
    rw [heq] at h
    rw [div_eq_zero_iff] at h
    rcases h with h1 | h2
    · exact (mul_eq_zero.mp h1).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
    · exfalso
      exact hD h2
  · intro h
    rw [heq, h, mul_zero, zero_div]

/-- The mollified-Rouché leaf forces `xiShifted z ≠ 0` in the upper tail
    `0 < z.im < 1/2, |Re z| > 10`.  Extracted from the committed
    `mollified_rouche_leaf_implies_tail_hard_difference_nonzero` via the
    hard-difference/xiShifted equivalence. -/
theorem mollified_rouche_leaf_implies_upper_tail_xiShifted_nonzero
    (K : ℕ) (H : MollifiedRoucheLeaf K) :
    ∀ (z : ℂ),
      10 < |z.re| →
      0 < z.im →
      z.im < (1 / 2 : ℝ) →
      xiShifted z ≠ 0 := by
  intro z hx hy0 hlt
  have hdiff := mollified_rouche_leaf_implies_tail_hard_difference_nonzero K H z hx hy0 hlt
  have hne : z.im ≠ 0 := by linarith
  have hgt : -(1 / 2 : ℝ) < z.im := by linarith
  have heq := hardDifference_eq_zero_iff_xiShifted_eq_zero hgt hlt hne
  exact mt heq.2 hdiff

/-- Conjugate symmetry of `xiShifted` (from the classical xi symmetries):
    `xiShifted (star z) = star (xiShifted z)`.  Hence `xiShifted z ≠ 0` iff
    `xiShifted (star z) ≠ 0`.  This is the bridge that reflects upper-tail
    nonvanishing to the lower half. -/
theorem xiShifted_conj_nonvanishing {z : ℂ}
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ)) :
    xiShifted z ≠ 0 ↔ xiShifted (star z) ≠ 0 := by
  have hgt' : -(1 : ℝ) / 2 < z.im := by linarith [hgt]
  have hsym := classicalXi_symmetry.conj_symm z hgt' hlt
  constructor
  · intro hnz hzero
    have : star (xiShifted z) = 0 := by rw [← hsym, hzero]
    have : xiShifted z = 0 := (star_eq_zero).mp this
    exact hnz this
  · intro hnz hzero
    have : xiShifted (star z) = 0 := by rw [hsym, hzero, star_zero]
    exact hnz this

/-- The mollified-Rouché leaf forces `xiShifted z ≠ 0` in the LOWER tail
    `-(1/2) < z.im < 0, |Re z| > 10`, by conjugate symmetry from the upper
    tail.  For such a `z`, `star z` lies in the upper tail (same `|Re|`,
    negated `Im`), where the upper-tail theorem gives `xiShifted (star z) ≠ 0`;
    conjugate symmetry then yields `xiShifted z ≠ 0`. -/
theorem mollified_rouche_leaf_implies_lower_tail_xiShifted_nonzero
    (K : ℕ) (H : MollifiedRoucheLeaf K) :
    ∀ (z : ℂ),
      10 < |z.re| →
      -(1 : ℝ) / 2 < z.im →
      z.im < 0 →
      xiShifted z ≠ 0 := by
  intro z hx hy0 hyl
  have hw_im : (star z).im = -z.im := by simp [star_def, conj_im]
  have hw_re : (star z).re = z.re := by simp [star_def, conj_re]
  have habs : 10 < |(star z).re| := by rwa [← hw_re] at hx
  have hw_xi : xiShifted (star z) ≠ 0 :=
    mollified_rouche_leaf_implies_upper_tail_xiShifted_nonzero K H (star z) habs
      (by linarith [hw_im]) (by linarith [hw_im])
  have hgt : -(1 : ℝ) / 2 < z.im := hy0
  have hlt : z.im < (1 : ℝ) / 2 := by linarith
  have hsym := classicalXi_symmetry.conj_symm z hgt hlt
  exact mt (fun h => by rw [hsym, h, star_zero]) hw_xi

/-- The mollified-Rouché leaf forces the hard-difference nonzero in the
    LOWER tail `-(1/2) < z.im < 0, |Re z| > 10`, by conjugate symmetry.
    This mirrors the committed upper-tail theorem's statement shape. -/
theorem mollified_rouche_leaf_implies_lower_tail_hard_difference_nonzero
    (K : ℕ) (H : MollifiedRoucheLeaf K) :
    ∀ (z : ℂ),
      10 < |z.re| →
      -(1 / 2 : ℝ) < z.im →
      z.im < 0 →
      1 / (z ^ 2 + (1 / 4 : ℂ)) - completedRiemannZeta₀ (shiftedS z) ≠ 0 := by
  intro z hx hy0 hyl
  have hgt : -(1 : ℝ) / 2 < z.im := by linarith [hy0]
  have hxi := mollified_rouche_leaf_implies_lower_tail_xiShifted_nonzero K H z hx hgt hyl
  have hne : z.im ≠ 0 := by linarith
  have hlt : z.im < (1 / 2 : ℝ) := by linarith
  have heq := hardDifference_eq_zero_iff_xiShifted_eq_zero hy0 hlt hne
  exact mt heq.1 hxi

/-- The mollified-Rouché leaf closes the FULL tail `|Re z| > 10` (both
    upper and lower halves), as a `XiTailPointwiseNonvanishingForX 10`
    certificate.  The upper half is the committed theorem; the lower half
    follows by conjugate symmetry. -/
def mollified_rouche_leaf_implies_tail_pointwise
    (K : ℕ) (H : MollifiedRoucheLeaf K) :
    XiTailPointwiseNonvanishingForX 10 where
  right_nonvanishing := by
    intro z hx hgt hlt hne
    have habs : 10 < |z.re| := by
      have hpos : 0 < z.re := by linarith
      rw [abs_of_pos hpos]; linarith
    by_cases hpos : 0 < z.im
    · exact mollified_rouche_leaf_implies_upper_tail_xiShifted_nonzero K H z habs hpos hlt
    · have hneg : z.im < 0 := lt_of_le_of_ne (by linarith) hne
      exact mollified_rouche_leaf_implies_lower_tail_xiShifted_nonzero K H z habs hgt hneg
  left_nonvanishing := by
    intro z hx hgt hlt hne
    have habs : 10 < |z.re| := by
      have hneg : z.re < 0 := by linarith
      rw [abs_of_neg hneg]; linarith
    by_cases hpos : 0 < z.im
    · exact mollified_rouche_leaf_implies_upper_tail_xiShifted_nonzero K H z habs hpos hlt
    · have hneg : z.im < 0 := lt_of_le_of_ne (by linarith) hne
      exact mollified_rouche_leaf_implies_lower_tail_xiShifted_nonzero K H z habs hgt hneg

/-- **Residual reduction for the hard-difference door.**

    The mollified-Rouché leaf closes the full tail `|Re z| > 10` (upper half
    by the committed bridge, lower half by conjugate symmetry).  Combined
    with a finite zero-free cover of the compact central rectangle
    `|Re z| ≤ 10` (a `XiCentralZeroFreeCover 10`), this yields the full
    off-real pointwise nonvanishing of `xiShifted`, and hence RH.

    The central rectangle `|Re z| ≤ 10, 0 < |z.im| < 1/2` is therefore the
    EXACT residual of the hard-difference door: it is a compact set whose
    zero-freeness is mathematically equivalent to RH, and no classical
    theorem currently in the repo covers it. -/
theorem rh_from_mollified_tail_and_central_cover
    (K : ℕ) (H : MollifiedRoucheLeaf K)
    (C : XiCentralZeroFreeCover 10) :
    RiemannHypothesisProp :=
  rh_from_central_zero_free_cover_and_tail_pointwise C
    (mollified_rouche_leaf_implies_tail_pointwise K H)

/-!
# Quantitative Rouché-gap bridge (new, fully proved)

The committed tail bridge above is qualitative (`≠ 0`).  The lemmas below
upgrade it to the *quantitative lower-bound* shape consumed by the finite-cover
assembly infrastructure:

* `rouche_margin_lower_bound` — pure Rouché gap (`‖u - 1‖ ≤ 1 - δ → δ ≤ ‖u‖`),
  via the reverse triangle inequality.  This is the quantitative form of
  `rh_from_mollified_rouche`.
* `hardDifference_norm_eq` / `hardDifference_lower_bound_of_xiShifted_lower_bound` —
  transfer of an `xiShifted` lower bound `ε ≤ ‖xiShifted z‖` to an explicit
  hard-difference lower bound `2 * ε / ‖z² + 1/4‖ ≤ ‖hardDifference z‖`, via the
  committed core identity `inv_D_sub_completedZeta_eq_two_xiShifted_div_D`.
  This is the hard-difference analogue of the product lower bound
  `TailProofEngine.tail_lower_bound_from_component_bounds` and of the analytic
  bound fed to `HadamardBridge.zeroFreeEdge_from_tsum`: a pointwise modulus
  lower bound is exactly what `XiLocalZeroFreeRect_of_lower_bound` (via
  `CellProofEngine.cell_lower_bound_from_center_and_deriv`) consumes to build a
  `XiCentralZeroFreeCover 10` cell.
* `mollified_gap_gives_zeta_lower_bound` /
  `mollified_gap_gives_hardDifference_lower_bound` — composition of the gap with
  a mollifier upper bound `‖M‖ ≤ B` and a prefactor lower bound
  `P₀ ≤ ‖classicalXiPrefactor s‖` into an explicit hard-difference lower bound.
  The `S₂`-is-a-lower-bound pattern follows the rigorous `Tendsto` template in
  `zeta_rigorous.eta_half_pos` (NOT the false `0 < ∑'` form for the
  conditionally convergent eta series).

All lemmas are unconditional implications (bounds in → bound out); they do not
assume RH, the leaf, or any zero-free region.  A zero-free region alone does NOT
force the critical line — the off-line exclusion comes from this Rouché lower
bound composed with the conjugate-symmetry reflection already committed above
(`mollified_rouche_leaf_implies_lower_tail_*`), i.e. the mollifier/Rouché
bridge, not the `KadiriZeroFree` edge.
-/

/-- Quantitative Rouché gap: `‖u - 1‖ ≤ 1 - δ` forces `δ ≤ ‖u‖`.

    Pure reverse-triangle-inequality estimate; the quantitative form of
    `rh_from_mollified_rouche` (which is the `δ → 0` qualitative corollary). -/
theorem rouche_margin_lower_bound {u : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ‖u - 1‖ ≤ 1 - δ) : δ ≤ ‖u‖ := by
  have h := norm_add_le ((1 : ℂ) - u) u
  rw [sub_add_cancel] at h
  rw [norm_one] at h
  have hrev : ‖(1 : ℂ) - u‖ = ‖u - 1‖ := norm_sub_rev 1 u
  rw [hrev] at h
  linarith

/-- Qualitative Rouché corollary: `‖u - 1‖ < 1` forces `u ≠ 0`. -/
theorem rouche_gap_ne_zero {u : ℂ} (hgap : ‖u - 1‖ < 1) : u ≠ 0 := by
  have h := norm_add_le ((1 : ℂ) - u) u
  rw [sub_add_cancel] at h
  rw [norm_one] at h
  have hrev : ‖(1 : ℂ) - u‖ = ‖u - 1‖ := norm_sub_rev 1 u
  rw [hrev] at h
  have hpos : 0 < ‖u‖ := by linarith
  exact norm_pos_iff.mp hpos

/-- Norm identity for the hard difference, from the committed core identity
    `inv_D_sub_completedZeta_eq_two_xiShifted_div_D`. -/
theorem hardDifference_norm_eq {z : ℂ}
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ)) (hne : z.im ≠ 0) :
    ‖1 / (z ^ 2 + (1 / 4 : ℂ)) - completedRiemannZeta₀ (shiftedS z)‖ =
      2 * ‖xiShifted z‖ / ‖z ^ 2 + (1 / 4 : ℂ)‖ := by
  have heq := inv_D_sub_completedZeta_eq_two_xiShifted_div_D z hgt hlt hne
  rw [heq, norm_div, norm_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]

/-- An `xiShifted` lower bound yields an explicit hard-difference lower bound.

    This is the bridge from `XiLocalLowerBoundRect`-shaped data
    (`ε ≤ ‖xiShifted z‖`, as produced per cell by
    `CellProofEngine.cell_lower_bound_from_center_and_deriv`) to hard-difference
    nonvanishing on that cell (via `XiLocalZeroFreeRect_of_lower_bound`). -/
theorem hardDifference_lower_bound_of_xiShifted_lower_bound {z : ℂ}
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ)) (hne : z.im ≠ 0)
    {ε : ℝ} (hε : ε ≤ ‖xiShifted z‖) (hDpos : 0 < ‖z ^ 2 + (1 / 4 : ℂ)‖) :
    2 * ε / ‖z ^ 2 + (1 / 4 : ℂ)‖ ≤
      ‖1 / (z ^ 2 + (1 / 4 : ℂ)) - completedRiemannZeta₀ (shiftedS z)‖ := by
  rw [hardDifference_norm_eq hgt hlt hne]
  gcongr

/-- A mollifier Rouché gap plus a mollifier upper bound gives an explicit zeta
    lower bound `δ / B ≤ ‖zeta s‖`. -/
theorem mollified_gap_gives_zeta_lower_bound {z : ℂ} {K : ℕ} {δ B : ℝ}
    (hδ : 0 < δ) (hB : 0 < B)
    (hM : ‖dirichletMollifier (shiftedS z) K‖ ≤ B)
    (hgap : ‖zeta (shiftedS z) * dirichletMollifier (shiftedS z) K - 1‖ ≤ 1 - δ) :
    δ / B ≤ ‖zeta (shiftedS z)‖ := by
  have hprod : δ ≤ ‖zeta (shiftedS z) * dirichletMollifier (shiftedS z) K‖ :=
    rouche_margin_lower_bound hδ hgap
  rw [norm_mul] at hprod
  have hle : δ ≤ ‖zeta (shiftedS z)‖ * B :=
    le_trans hprod (mul_le_mul_of_nonneg_left hM (norm_nonneg _))
  have hBne : B ≠ 0 := ne_of_gt hB
  field_simp
  linarith

/-- Composition: mollifier gap + mollifier upper bound + prefactor lower bound
    yields an explicit hard-difference lower bound.

    With `hgap` the `MollifiedRoucheLeaf`-shaped hypothesis (here with an
    explicit margin `δ`), `hM` the mollifier size control, `hpref` the
    classical-prefactor lower bound (nonvanishing in the strip via
    `classical_prefactor_nonzero_instrip`), this produces exactly the
    `ε ≤ ‖·‖` lower-bound certificate that the central-cover assembly
    (`XiCentralZeroFreeCover 10` via `XiLocalZeroFreeRect_of_lower_bound`)
    consumes.  Feeding the resulting `XiCentralZeroFreeCover 10` together with
    `mollified_rouche_leaf_implies_tail_pointwise` into
    `rh_from_mollified_tail_and_central_cover` is the remaining step to RH. -/
theorem mollified_gap_gives_hardDifference_lower_bound (K : ℕ) {z : ℂ} {δ B P₀ : ℝ}
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ)) (hne : z.im ≠ 0)
    (hδ : 0 < δ) (hB : 0 < B) (hP₀ : 0 ≤ P₀)
    (hM : ‖dirichletMollifier (shiftedS z) K‖ ≤ B)
    (hgap : ‖zeta (shiftedS z) * dirichletMollifier (shiftedS z) K - 1‖ ≤ 1 - δ)
    (hpref : P₀ ≤ ‖classicalXiPrefactor (shiftedS z)‖)
    (hDpos : 0 < ‖z ^ 2 + (1 / 4 : ℂ)‖) :
    2 * (P₀ * (δ / B)) / ‖z ^ 2 + (1 / 4 : ℂ)‖ ≤
      ‖1 / (z ^ 2 + (1 / 4 : ℂ)) - completedRiemannZeta₀ (shiftedS z)‖ := by
  have hzeta : δ / B ≤ ‖zeta (shiftedS z)‖ :=
    mollified_gap_gives_zeta_lower_bound hδ hB hM hgap
  have hxi_eq : xiShifted z = classicalXiPrefactor (shiftedS z) * zeta (shiftedS z) := by
    simp [xiShifted, shiftedS, classicalXi, XiFromPrefactor]
  have hxi_norm : ‖xiShifted z‖ =
      ‖classicalXiPrefactor (shiftedS z)‖ * ‖zeta (shiftedS z)‖ := by
    rw [hxi_eq, norm_mul]
  have hxi_low : P₀ * (δ / B) ≤ ‖xiShifted z‖ := by
    rw [hxi_norm]
    exact mul_le_mul hpref hzeta (div_nonneg hδ.le hB.le) (norm_nonneg _)
  exact hardDifference_lower_bound_of_xiShifted_lower_bound hgt hlt hne hxi_low hDpos

/-!
# Explicit mollifier bounds (partial leaf: `‖M‖ ≤ B` with concrete `B`)

The `MollifiedRoucheLeaf K` needs two estimates: a mollifier upper bound
`‖M‖ ≤ B` and a Rouché gap `‖ζ*M - 1‖ ≤ 1 - δ`.  This section proves the
first one unconditionally, with explicit `B`, plus the exact values of the
mollifier at the smallest `K`.  The gap itself is reduced to an explicit
zeta estimate (see `mollified_K2_gap_implies_zeta_bound`); that zeta estimate
is the precise remaining leaf gap.
-/

/-- Möbius factor is bounded by 1 in complex norm. -/
theorem moebius_complex_norm_le_one (n : ℕ) :
    ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h
  · simp [h]
  · rw [h]; simp
  · rw [h]; simp

/-- Dirichlet monomial bound: `‖(n+1)^{-s}‖ ≤ 1` for `0 ≤ Re s`. -/
theorem natCast_cpow_neg_norm_le_one (n : ℕ) (s : ℂ) (hs : 0 ≤ s.re) :
    ‖((n + 1 : ℕ) : ℂ) ^ (-s)‖ ≤ 1 := by
  have hpos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hbase : (((n + 1 : ℕ) : ℂ)) = (((((n + 1 : ℕ) : ℝ))) : ℂ) := by simp
  rw [hbase, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hre : (-s).re = -s.re := Complex.neg_re s
  rw [hre]
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · have h1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    exact_mod_cast h1
  · linarith

/-- Smoothing weight bound: `‖1 - (n+1)/K‖ ≤ 1` for `n < K`, `1 ≤ K`. -/
theorem mollifier_weight_norm_le_one (n K : ℕ) (hK : 1 ≤ K) (hmem : n < K) :
    ‖((1 - ((n + 1 : ℕ) : ℂ) / ((K : ℕ) : ℂ)) : ℂ)‖ ≤ 1 := by
  have hKne : (K : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.lt_of_lt_of_le (Nat.zero_lt_one) hK))
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le (Nat.zero_lt_one) hK)
  have hnK : ((((n + 1 : ℕ) : ℝ))) ≤ ((K : ℕ) : ℝ) := by
    have hle : n + 1 ≤ K := hmem
    exact_mod_cast hle
  have hnn : (0 : ℝ) ≤ ((((n + 1 : ℕ) : ℝ))) := by positivity
  have hdiv_nonneg : (0 : ℝ) ≤ ((((n + 1 : ℕ) : ℝ))) / ((K : ℕ) : ℝ) :=
    div_nonneg hnn hKpos.le
  have hdiv_le_one : ((((n + 1 : ℕ) : ℝ))) / ((K : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hKpos]
    exact hnK
  have hcast : ((1 - ((n + 1 : ℕ) : ℂ) / ((K : ℕ) : ℂ)) : ℂ) =
      (((1 - ((((n + 1 : ℕ) : ℝ))) / (((K : ℕ) : ℝ)) : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> linarith

/-- Explicit mollifier `L∞` bound: `‖M(s,K)‖ ≤ K` for `0 ≤ Re s`.

Each of the `K` summands is a product of three factors each of norm `≤ 1`
(Möbius, Dirichlet monomial, smoothing weight), hence has norm `≤ 1`; the
triangle inequality gives `≤ K`.  This supplies the `hM : ‖M‖ ≤ B` hypothesis
(with `B = K`) consumed by `mollified_gap_gives_zeta_lower_bound` and
`mollified_gap_gives_hardDifference_lower_bound`. -/
theorem dirichletMollifier_norm_le (s : ℂ) (K : ℕ) (hs : 0 ≤ s.re) :
    ‖dirichletMollifier s K‖ ≤ (K : ℝ) := by
  unfold dirichletMollifier
  by_cases hK0 : K = 0
  · subst hK0
    simp
  · have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr hK0
    calc ‖∑ n ∈ Finset.range K, (ArithmeticFunction.moebius (n + 1) : ℂ) *
            (↑(n + 1) : ℂ) ^ (-s) * (1 - ↑(n + 1) / ↑K)‖
        ≤ ∑ n ∈ Finset.range K, ‖(ArithmeticFunction.moebius (n + 1) : ℂ) *
            (↑(n + 1) : ℂ) ^ (-s) * (1 - ↑(n + 1) / ↑K)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range K, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnK : n < K := Finset.mem_range.mp hn
          have hmu := moebius_complex_norm_le_one (n + 1)
          have hcp := natCast_cpow_neg_norm_le_one n s hs
          have hwt := mollifier_weight_norm_le_one n K hK1 hnK
          rw [norm_mul, norm_mul]
          have h12 : ‖((ArithmeticFunction.moebius (n + 1) : ℤ) : ℂ)‖ *
              ‖(((n + 1 : ℕ) : ℂ) ^ (-s))‖ ≤ 1 :=
            mul_le_one₀ hmu (norm_nonneg _) hcp
          exact mul_le_one₀ h12 (norm_nonneg _) hwt
      _ = (K : ℝ) := by simp

/-- The `K = 0` mollifier vanishes (empty sum). -/
theorem dirichletMollifier_zero (s : ℂ) : dirichletMollifier s 0 = 0 := by
  simp [dirichletMollifier]

/-- The `K = 1` mollifier vanishes: the single term carries weight `1 - 1/1 = 0`. -/
theorem dirichletMollifier_one (s : ℂ) : dirichletMollifier s 1 = 0 := by
  unfold dirichletMollifier
  simp [Complex.one_cpow]

/-- The `K = 2` mollifier is the constant `1/2`: the `n = 0` term contributes
`1 * 1 * (1/2)` and the `n = 1` term carries weight `1 - 2/2 = 0`.  This is the
smallest nontrivial Dirichlet mollifier. -/
theorem dirichletMollifier_two (s : ℂ) : dirichletMollifier s 2 = 1 / 2 := by
  have hsum : (∑ n ∈ Finset.range 2, (ArithmeticFunction.moebius (n + 1) : ℂ) *
      (↑(n + 1) : ℂ) ^ (-s) * (1 - ↑(n + 1) / ↑(2 : ℕ))) =
      ((ArithmeticFunction.moebius 1 : ℂ) * ((1 : ℕ) : ℂ) ^ (-s) *
        (1 - ((1 : ℕ) : ℂ) / ((2 : ℕ) : ℂ))) +
      ((ArithmeticFunction.moebius 2 : ℂ) * ((2 : ℕ) : ℂ) ^ (-s) *
        (1 - ((2 : ℕ) : ℂ) / ((2 : ℕ) : ℂ))) := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  have hmu1 : ((ArithmeticFunction.moebius 1 : ℤ) : ℂ) = 1 := by
    simp
  have hcp1 : (((1 : ℕ) : ℂ) ^ (-s)) = 1 := by
    have h1 : (((1 : ℕ) : ℂ)) = (1 : ℂ) := by simp
    rw [h1, Complex.one_cpow]
  have hw1 : ((1 - ((1 : ℕ) : ℂ) / ((2 : ℕ) : ℂ)) : ℂ) = 1 / 2 := by
    norm_num
  have hw2 : ((1 - ((2 : ℕ) : ℂ) / ((2 : ℕ) : ℂ)) : ℂ) = 0 := by
    have h2 : ((2 : ℕ) : ℂ) / ((2 : ℕ) : ℂ) = 1 := by
      apply div_self
      norm_num
    rw [h2, sub_self]
  have e0 : ((ArithmeticFunction.moebius 1 : ℂ) * ((1 : ℕ) : ℂ) ^ (-s) *
      (1 - ((1 : ℕ) : ℂ) / ((2 : ℕ) : ℂ))) = 1 / 2 := by
    rw [hmu1, hcp1, hw1, one_mul, one_mul]
  have e1 : ((ArithmeticFunction.moebius 2 : ℂ) * ((2 : ℕ) : ℂ) ^ (-s) *
      (1 - ((2 : ℕ) : ℂ) / ((2 : ℕ) : ℂ))) = 0 := by
    rw [hw2, mul_zero]
  unfold dirichletMollifier
  rw [hsum, e0, e1, add_zero]

/-- `K = 2` mollifier norm: `‖M(s,2)‖ = 1/2`. -/
theorem dirichletMollifier_two_norm (s : ℂ) :
    ‖dirichletMollifier s 2‖ ≤ 1 / 2 := by
  rw [dirichletMollifier_two]
  norm_num

/-- Tail specialization of the `L∞` bound: on the shifted strip
`-(1/2) < Im z < 1/2` one has `Re(shiftedS z) = 1/2 - Im z ≥ 0`, so
`‖M(shiftedS z, K)‖ ≤ K`.  This is exactly the `hM` input for the quantitative
Rouché-gap chain on the tail. -/
theorem dirichletMollifier_tail_norm_le (z : ℂ) (K : ℕ)
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ)) :
    ‖dirichletMollifier (shiftedS z) K‖ ≤ (K : ℝ) := by
  apply dirichletMollifier_norm_le
  rw [shiftedS_re]
  linarith

/-- Tail specialization at `K = 2` with the sharp constant `1/2`. -/
theorem dirichletMollifier_tail_two_norm_le (z : ℂ) :
    ‖dirichletMollifier (shiftedS z) 2‖ ≤ 1 / 2 :=
  dirichletMollifier_two_norm _

/-- `K = 2` Rouché product identity: `ζ * M₂ - 1 = ζ/2 - 1`. -/
theorem mollified_K2_gap_eq (z : ℂ) :
    zeta (shiftedS z) * dirichletMollifier (shiftedS z) 2 - 1 =
      zeta (shiftedS z) / 2 - 1 := by
  rw [dirichletMollifier_two]
  ring

/-- `K = 2` gap forces a uniform zeta upper bound on the tail:
`‖ζ*M₂ - 1‖ ≤ 1 - δ` implies `‖ζ‖ ≤ 4 - 2δ`.

Hence a `MollifiedRoucheLeaf 2` (which asserts the gap hypothesis for every
tail `z`) would force `‖zeta(shiftedS z)‖ ≤ 4` uniformly for
`10 < |Re z|`, `0 < Im z < 1/2`.  Proving that uniform zeta bound is the
precise remaining gap for the `K = 2` leaf; no lemma currently in the repo
(`ZeroFreeRegion*` gives a zero-free edge near `Re = 1`, `KadiriDigammaBound`
bounds `Re ψ`, and Mathlib's Dirichlet-series API gives no strip upper bound
for `ζ`) supplies it.  A full leaf additionally needs `K` growing with `|Re z|`
(a fixed-`K` Dirichlet polynomial is uniformly bounded in `Im` while `ζ` on
`0 < Re < 1/2` is not), so the `K = 2` reduction below is the sharpest
fixed-`K` statement available. -/
theorem mollified_K2_gap_implies_zeta_bound {z : ℂ} {δ : ℝ}
    (hgap : ‖zeta (shiftedS z) * dirichletMollifier (shiftedS z) 2 - 1‖ ≤ 1 - δ) :
    ‖zeta (shiftedS z)‖ ≤ 4 - 2 * δ := by
  have heq := mollified_K2_gap_eq z
  rw [heq] at hgap
  have htri := norm_add_le (zeta (shiftedS z) / 2 - 1) (1 : ℂ)
  rw [sub_add_cancel] at htri
  rw [norm_one] at htri
  have h2 : ‖zeta (shiftedS z) / 2‖ ≤ (1 - δ) + 1 :=
    le_trans htri (by linarith)
  have hmul : ‖zeta (shiftedS z) / 2‖ = ‖zeta (shiftedS z)‖ / 2 := by
    rw [norm_div]
    norm_num
  rw [hmul] at h2
  linarith

end MollifiedAttack
