import riemann_hypothesis
import zeta_rigorous
import central_cover_assembly
import interval_arith
import ZeroFreeRegionHadamard

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

/-!
# R02 zeta-upper bridge (eta-limit + denominator lower, toward door 4 + R02 deriv M)

This section supplies unconditional eta-side bounds on the R02 disc `s`-rect
`Re ∈ [0.05,0.74]`, `Im ∈ [-8.25,-5.25]` (exactly
`DerivCauchyBridge.R02_zeta_upper_obligation`'s rect, see
`central_cover_assembly.lean`), reusing `zeta_rigorous.lean` (imported above;
acyclic: that file imports only `Mathlib`) without copying:

* `R02_norm_le_of_mem` — `‖s‖ ≤ 9` on the rect (triangle `|Re|+|Im|`).
* `R02_cvtFactor_norm_ge` — uniform conversion-factor lower
  `0.18 ≤ ‖1 - 2^{1-s}‖` for `s.re ≤ 0.74` (via `|2^{1-s}| = 2^{1-Re} ≥ 2^{0.25}
  ≥ 1.18` + reverse triangle; the `1.18 ≤ 2^{0.25}` step clears to
  `1.18^4 ≤ 2` exactly as `R00ZetaEM.rpow_two_R00_ge`).
* `R02_etaDirichlet_S2_norm_le` — two-term eta partial sum `‖S₂(s)‖ ≤ 2` for
  `0.05 ≤ Re` (term norms `(n+1)^{-Re} ≤ 1`).
* `R02_etaPairLim_upper` — unconditional paired-eta-limit upper
  `‖∑' m, etaPairTerm s m‖ ≤ 182` on the rect (`S₂ ≤ 2` +
  `zetaCell_even_remainder_le` at `M = 1`, `C = 9`, `σ ≥ 0.05` giving tail
  `9/σ ≤ 180`; `M = 1` gives `M^{-σ} = 1`, so no rpow lower is needed).
* `R02_zeta_upper_of_etaPairLim_eq` — conditional zeta upper
  `‖zeta s‖ ≤ 1012` on the rect from the single continuation premise
  `∀ s in rect, (∑' m, etaPairTerm s m) = etaHurwitz s`
  (via `etaHurwitz_eq_etaRHS_compl` on `{1}ᶜ` + denominator lower +
  `‖G‖ ≤ 182`; `182/0.18 ≤ 1012`).

Honest residual (no `sorry`/`axiom`/stand-ins; all lemmas below are proved as
implications with explicit premises):
* The sole analytic premise `hCont` (`G = etaHurwitz` on the rect) is NOT proved
  here. It needs `G` analytic on an open rectangle `U ⊃ rect ∪ {2}` with uniform
  majorant (`Re ≥ 0.025`, `‖s‖ ≤ 12` gives `12*(m+1)^{-1.025}` summable) + the
  identity theorem from agreement on `1 < Re` (`etaPairLim_eq_of_one_lt_re`);
  the existing `zeta_rigorous` ball proof (`ball 1 (3/4)`) does not cover the
  rect (`Im ≈ -6`), so a new `U` is required. This is one precise lemma.
* The constant `1012` (hence deriv `M = 6800640` via the general bridge to be
  added next) is far from the `10` in `R02_zeta_upper_obligation` (which would
  give `M = 67200`). With `σ = 0.05`, `r(M) = C*M^{-σ}/σ ≈ 180*M^{-0.05}`;
  reaching `r ≤ 5` needs `M ≥ 36^{20} ≈ 1.3e31` terms — infeasible. Thus `≤ 10`
  is not reachable by this `M = 1` crude route; `≤ 1012` is the sharp
  `M = 1` consequence. Closing `≤ 10` needs either astronomically large `M`
  (impossible) or a different analytic input (functional equation + Stirling +
  convexity), which is the door-4 tail-gap remainder.
-/

namespace R02ZetaUpper

theorem R02_norm_le_of_mem {s : ℂ}
    (hre_lo : 0.05 ≤ s.re) (hre_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25) :
    ‖s‖ ≤ 9 := by
  have h := Complex.norm_le_abs_re_add_abs_im s
  have hre_abs : |s.re| ≤ 0.74 := by
    rw [abs_le]
    constructor <;> linarith
  have him_abs : |s.im| ≤ 8.25 := by
    rw [abs_le]
    constructor <;> linarith
  linarith

set_option maxHeartbeats 800000 in
theorem R02_cvtFactor_norm_ge {s : ℂ} (hre_hi : s.re ≤ 0.74) :
    (0.18 : ℝ) ≤ ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ := by
  have hre1 : ((1 : ℂ) - s).re = 1 - s.re := by
    rw [Complex.sub_re, Complex.one_re]
  have hbase : (2 : ℂ) = ((((2 : ℝ))) : ℂ) := by norm_cast
  have hnorm : ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ = (2 : ℝ) ^ (((1 : ℂ) - s).re) := by
    rw [hbase]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
  have hre_ge : (0.25 : ℝ) ≤ (((1 : ℂ) - s).re) := by
    rw [hre1]
    linarith
  have h118_025 : (1.18 : ℝ) ≤ (2 : ℝ) ^ ((0.25 : ℝ)) := by
    have hpow : ((1.18 : ℝ)) ^ ((4 : ℕ)) ≤ ((((2 : ℝ) ^ ((0.25 : ℝ)))) ^ ((4 : ℕ)) : ℝ) := by
      have e : ((((2 : ℝ) ^ ((0.25 : ℝ)))) ^ ((4 : ℕ)) : ℝ) = (2 : ℝ) ^ ((1 : ℕ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        rw [show (0.25 : ℝ) * ((((4 : ℕ)) : ℝ)) = (1 : ℝ) by norm_num]
        rw [show (1 : ℝ) = ((((1 : ℕ)) : ℝ)) by norm_num]
        exact Real.rpow_natCast 2 1
      rw [e]
      norm_num
    exact le_of_pow_le_pow_left₀ (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _).le hpow
  have h118_le : (1.18 : ℝ) ≤ (2 : ℝ) ^ (((1 : ℂ) - s).re) :=
    le_trans h118_025 (Real.rpow_le_rpow_of_exponent_le (by norm_num) hre_ge)
  have hw_ge : (1.18 : ℝ) ≤ ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ := by
    rw [hnorm]
    exact h118_le
  have htri := norm_add_le ((2 : ℂ) ^ ((1 : ℂ) - s) - 1) (1 : ℂ)
  rw [sub_add_cancel] at htri
  rw [norm_one] at htri
  have hrev : ‖(2 : ℂ) ^ ((1 : ℂ) - s) - 1‖ =
      ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ := norm_sub_rev _ _
  rw [hrev] at htri
  linarith

theorem R02_etaDirichlet_S2_norm_le {s : ℂ} (hre_lo : 0.05 ≤ s.re) :
    ‖∑ k ∈ Finset.range 2, etaDirichletTerm s k‖ ≤ 2 := by
  have h0 : etaDirichletTerm s 0 = 1 := by
    simp only [etaDirichletTerm]
    simp
  have hterm1_eq : etaDirichletTerm s 1 = -1 / ((((2 : ℕ)) : ℂ) ^ s) := by
    simp only [etaDirichletTerm]
    norm_num
  have h2cast : ((((2 : ℕ)) : ℂ)) = ((((2 : ℝ))) : ℂ) := by norm_cast
  have h2norm : ‖((((2 : ℕ)) : ℂ) ^ s)‖ = (2 : ℝ) ^ (s.re) := by
    rw [h2cast]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
  have h2ge : (1 : ℝ) ≤ (2 : ℝ) ^ (s.re) := by
    have hexp_nonneg : (0 : ℝ) ≤ s.re := by linarith
    calc (1 : ℝ) = (2 : ℝ) ^ ((0 : ℝ)) := by rw [Real.rpow_zero]
      _ ≤ (2 : ℝ) ^ (s.re) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_nonneg
  have h1_norm : ‖etaDirichletTerm s 1‖ ≤ 1 := by
    rw [hterm1_eq, norm_div, norm_neg, norm_one, h2norm]
    rw [div_le_one (Real.rpow_pos_of_pos (by norm_num) _)]
    exact h2ge
  have hsum2 : (∑ k ∈ Finset.range 2, etaDirichletTerm s k) =
      etaDirichletTerm s 0 + etaDirichletTerm s 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
  rw [hsum2, h0]
  calc ‖(1 : ℂ) + etaDirichletTerm s 1‖
      ≤ ‖(1 : ℂ)‖ + ‖etaDirichletTerm s 1‖ := norm_add_le _ _
    _ ≤ 1 + 1 := by rw [norm_one]; linarith [h1_norm]
    _ = 2 := by norm_num

theorem R02_etaPairLim_upper {s : ℂ}
    (hre_lo : 0.05 ≤ s.re) (hre_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25) :
    ‖∑' m, etaPairTerm s m‖ ≤ 182 := by
  have hspos : 0 < s.re := by linarith
  have hC : ‖s‖ ≤ 9 := R02_norm_le_of_mem hre_lo hre_hi him_lo him_hi
  have hC0 : (0 : ℝ) ≤ 9 := by norm_num
  have hS2 : ‖∑ k ∈ Finset.range 2, etaDirichletTerm s k‖ ≤ 2 :=
    R02_etaDirichlet_S2_norm_le hre_lo
  have hM1 : ((((1 : ℕ)) : ℝ) ^ (-s.re)) = 1 := by
    rw [Nat.cast_one, Real.one_rpow]
  have hrem0 := zetaCell_even_remainder_le hspos hC hC0 1 (by norm_num)
  rw [show (2 * 1 : ℕ) = 2 by norm_num, hM1] at hrem0
  have hdiv : (9 : ℝ) * (1 / s.re) ≤ 180 := by
    have hpos : (0 : ℝ) < s.re := hspos
    have hinv : 1 / s.re ≤ 20 := by
      rw [div_le_iff₀ hpos]
      linarith
    have h9 : (9 : ℝ) * (1 / s.re) ≤ 9 * 20 :=
      mul_le_mul_of_nonneg_left hinv (by norm_num)
    linarith
  have htail180 : ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range 2, etaDirichletTerm s k)‖ ≤ 180 :=
    le_trans hrem0 hdiv
  have htri := norm_add_le (∑ k ∈ Finset.range 2, etaDirichletTerm s k)
    ((∑' m, etaPairTerm s m) - (∑ k ∈ Finset.range 2, etaDirichletTerm s k))
  rw [add_sub_cancel] at htri
  linarith

theorem R02_zeta_upper_of_etaPairLim_eq
    (hCont : ∀ s : ℂ, 0.05 ≤ s.re → s.re ≤ 0.74 → -8.25 ≤ s.im → s.im ≤ -5.25 →
      (∑' m, etaPairTerm s m) = etaHurwitz s) :
    ∀ s : ℂ, 0.05 ≤ s.re → s.re ≤ 0.74 → -8.25 ≤ s.im → s.im ≤ -5.25 →
      ‖zeta s‖ ≤ 1012 := by
  intro s hre_lo hre_hi him_lo him_hi
  have hG := R02_etaPairLim_upper hre_lo hre_hi him_lo him_hi
  have hConts := hCont s hre_lo hre_hi him_lo him_hi
  have hne1 : s ≠ 1 := by
    intro h
    have hs1 : s.re = 1 := by rw [h, Complex.one_re]
    linarith
  have hmem : s ∈ ({1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact hne1
  have heq := etaHurwitz_eq_etaRHS_compl hmem
  have hGeq : (∑' m, etaPairTerm s m) =
      (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s := by
    rw [hConts, heq]
    rfl
  have hden_ge := R02_cvtFactor_norm_ge hre_hi
  have hden_pos : (0 : ℝ) < ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ :=
    lt_of_lt_of_le (by norm_num) hden_ge
  have hden_ne : (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s) ≠ 0 :=
    norm_pos_iff.mp hden_pos
  have hZeq : riemannZeta s =
      (∑' m, etaPairTerm s m) / ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)) := by
    rw [eq_div_iff hden_ne, mul_comm]
    exact hGeq.symm
  have hZnorm : ‖riemannZeta s‖ =
      ‖∑' m, etaPairTerm s m‖ / ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ := by
    rw [hZeq, norm_div]
  have hstep1 : ‖∑' m, etaPairTerm s m‖ / ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ ≤
      182 / ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hG
      (inv_nonneg.mpr (le_trans (by norm_num) hden_ge))
  have hinv : (‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖)⁻¹ ≤ ((0.18 : ℝ))⁻¹ :=
    (inv_le_inv₀ hden_pos (by norm_num)).mpr hden_ge
  have hstep2 : (182 : ℝ) / ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ ≤ 182 / 0.18 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv (by norm_num)
  have hle : ‖∑' m, etaPairTerm s m‖ / ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ ≤
      182 / 0.18 := le_trans hstep1 hstep2
  have h182 : (182 : ℝ) / 0.18 ≤ 1012 := by norm_num
  have hzeta_eq : zeta s = riemannZeta s := rfl
  rw [hzeta_eq, hZnorm]
  exact le_trans hle h182

end R02ZetaUpper

/-!
# R02 general deriv bridge (any `B`) + conditional `M = 6800640` from the eta premise

This section generalizes `DerivCauchyBridge.xiShifted_upper_of_zeta_upper_R02`
(`B = 10` giving `16800` and `M = 67200`) to any `B`, reusing the
hypothesis-free poly/pi/Gamma uppers (`poly_upper_R02_disc`,
`pi_upper_R02_disc`, `gamma_upper_R02_disc`) and Cauchy machinery
(`R02_s_of_sphere_re_im`, `R02_sphere_mem_strip`, `uniform_deriv_of_sphere_bound`)
via the imports above. Combined with `R02_zeta_upper_of_etaPairLim_eq`
(`B = 1012` from `hCont`), this yields an end-to-end (modulo the single
`hCont`) cell deriv bound `‖deriv xiShifted‖ ≤ 6800640` on `R02`
(`42*1*40*1012/0.25 = 6800640`). Still far from fencing (`M ≈ 0.05`), but it is
the first unconditional-shape deriv `M` whose only premise is the precise
continuation identity `G = etaHurwitz` on the rect (now being closed in
`zeta_rigorous.lean` by the concurrent `{Re > 0}` identity proof).
-/

namespace R02DerivBridge

theorem R02_xiShifted_upper_of_zeta_upper_general {B : ℝ}
    (hZ : ∀ s : ℂ, 0.05 ≤ s.re → s.re ≤ 0.74 → -8.25 ≤ s.im → s.im ≤ -5.25 →
      ‖zeta s‖ ≤ B)
    {w u : ℂ} (hw : CentralCoverAssembly.R02.mem w)
    (hu : u ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖xiShifted u‖ ≤ 42 * 1 * 40 * B := by
  obtain ⟨hsre_lo, hsre_hi, hsim_lo, hsim_hi⟩ :=
    DerivCauchyBridge.R02_s_of_sphere_re_im hw hu
  have hpoly := DerivCauchyBridge.poly_upper_R02_disc hsre_lo hsre_hi hsim_lo hsim_hi
  have hpi := DerivCauchyBridge.pi_upper_R02_disc hsre_lo
  have hgam := DerivCauchyBridge.gamma_upper_R02_disc hsre_lo hsre_hi
  have hzeta : ‖zeta ((1 / 2 : ℂ) + Complex.I * u)‖ ≤ B :=
    hZ _ hsre_lo hsre_hi hsim_lo hsim_hi
  have hdecomp := DerivCauchyBridge.norm_xiShifted_eq_parts u
  rw [hdecomp]
  have h1 : ‖DerivCauchyBridge.polyOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : ℂ) + Complex.I * u)‖ ≤ 42 * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have h12 : ‖DerivCauchyBridge.polyOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.piOf ((1 / 2 : ℂ) + Complex.I * u)‖ *
      ‖DerivCauchyBridge.gammaOf ((1 / 2 : ℂ) + Complex.I * u)‖ ≤ 42 * 1 * 40 :=
    mul_le_mul h1 hgam (norm_nonneg _) (by norm_num)
  exact mul_le_mul h12 hzeta (norm_nonneg _) (by norm_num)

theorem R02_entire_upper_of_zeta_upper_general {B : ℝ}
    (hZ : ∀ s : ℂ, 0.05 ≤ s.re → s.re ≤ 0.74 → -8.25 ≤ s.im → s.im ≤ -5.25 →
      ‖zeta s‖ ≤ B)
    {w u : ℂ} (hw : CentralCoverAssembly.R02.mem w)
    (hu : u ∈ Metric.sphere w (0.25 : ℝ)) :
    ‖CentralCoverAssembly.xiShiftedEntire u‖ ≤ 42 * 1 * 40 * B := by
  obtain ⟨hlo, hhi⟩ := DerivCauchyBridge.R02_sphere_mem_strip hw hu
  have hEq : xiShifted u = CentralCoverAssembly.xiShiftedEntire u :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip u hlo hhi
  rw [← hEq]
  exact R02_xiShifted_upper_of_zeta_upper_general hZ hw hu

theorem R02_uniform_sphere_bound_general {B : ℝ}
    (hZ : ∀ s : ℂ, 0.05 ≤ s.re → s.re ≤ 0.74 → -8.25 ≤ s.im → s.im ≤ -5.25 →
      ‖zeta s‖ ≤ B) :
    ∀ w, CentralCoverAssembly.R02.mem w → ∀ z ∈ Metric.sphere w (0.25 : ℝ),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 42 * 1 * 40 * B := by
  intro w hw z hz
  exact R02_entire_upper_of_zeta_upper_general hZ hw hz

theorem R02_deriv_bound_of_zeta_upper_general {B : ℝ}
    (hZ : ∀ s : ℂ, 0.05 ≤ s.re → s.re ≤ 0.74 → -8.25 ≤ s.im → s.im ≤ -5.25 →
      ‖zeta s‖ ≤ B) :
    ∀ w, CentralCoverAssembly.R02.mem w →
      ‖deriv xiShifted w‖ ≤ 42 * 1 * 40 * B / 0.25 := by
  have hM := DerivCauchyBridge.uniform_deriv_of_sphere_bound
    CentralCoverAssembly.R02 0.25 (42 * 1 * 40 * B) (by norm_num)
    (fun w hw => DerivCauchyBridge.R02_strip_of_mem hw)
    (R02_uniform_sphere_bound_general hZ)
  exact hM

theorem R02_deriv_bound_of_etaPairLim_eq
    (hCont : ∀ s : ℂ, 0.05 ≤ s.re → s.re ≤ 0.74 → -8.25 ≤ s.im → s.im ≤ -5.25 →
      (∑' m, etaPairTerm s m) = etaHurwitz s) :
    ∀ w, CentralCoverAssembly.R02.mem w → ‖deriv xiShifted w‖ ≤ 6800640 := by
  have hZ := R02ZetaUpper.R02_zeta_upper_of_etaPairLim_eq hCont
  have hD := R02_deriv_bound_of_zeta_upper_general hZ
  intro w hw
  have hle := hD w hw
  have heq : (42 : ℝ) * 1 * 40 * 1012 / 0.25 = 6800640 := by norm_num
  rw [heq] at hle
  exact hle

end R02DerivBridge

/-!
# R02 unconditional zeta/deriv bounds via the `{Re > 0}` identity (concurrent)

The concurrent `zeta_rigorous.lean` identity
`etaPairLim_eq_etaHurwitz_of_pos : 0 < s.re → (∑' m, etaPairTerm s m) =
etaHurwitz s` (analytic `G` on `{Re > 0}` + identity theorem from `Re > 1`,
covering the R02 rect since `0.05 ≤ Re`) discharges the sole `hCont` premise
above. Instantiating gives unconditional `‖zeta‖ ≤ 1012` on the R02 disc
`s`-rect and `‖deriv xiShifted‖ ≤ 6800640` on `R02` — the first end-to-end
cell deriv bound in the repo (with larger `M` than the `67200` conditional on
`≤ 10`; `≤ 10` itself remains open for the reasons in `R02ZetaUpper`).
-/

namespace R02Unconditional

theorem R02_hCont_of_pos : ∀ s : ℂ, 0.05 ≤ s.re → s.re ≤ 0.74 →
    -8.25 ≤ s.im → s.im ≤ -5.25 →
    (∑' m, etaPairTerm s m) = etaHurwitz s := by
  intro s hre_lo _ _ _
  exact etaPairLim_eq_etaHurwitz_of_pos (by linarith)

theorem R02_zeta_upper_unconditional : ∀ s : ℂ, 0.05 ≤ s.re → s.re ≤ 0.74 →
    -8.25 ≤ s.im → s.im ≤ -5.25 → ‖zeta s‖ ≤ 1012 :=
  R02ZetaUpper.R02_zeta_upper_of_etaPairLim_eq R02_hCont_of_pos

theorem R02_deriv_bound_unconditional : ∀ w,
    CentralCoverAssembly.R02.mem w → ‖deriv xiShifted w‖ ≤ 6800640 :=
  R02DerivBridge.R02_deriv_bound_of_etaPairLim_eq R02_hCont_of_pos

end R02Unconditional

/-!
# Tail zeta upper on `Re ≥ 1 + δ` — Im-uniform right edge (stone 1 of door-4 feeder)

GREP VERDICT (searches run before writing; repo + Mathlib; cite file:line):
* Phragmen-Lindelof vertical strip EXISTS (exact needed shape, do NOT recreate):
  `Mathlib/Analysis/Complex/PhragmenLindelof.lean:275`
  `theorem vertical_strip (hfd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b)) ... → ‖f z‖ ≤ C`.
* Hadamard three-lines EXISTS (exact needed shape, do NOT recreate):
  `Mathlib/Analysis/Complex/Hadamard.lean:608`
  `lemma norm_le_interp_of_mem_verticalClosedStrip' (hul : l < u) ... → ‖f z‖ ≤ a ^ ... * b ^ ...`.
* Maximum modulus EXISTS (generic, no zeta instantiation):
  `Mathlib/Analysis/Complex/AbsMax.lean:184` `norm_eqOn_closedBall_of_isMaxOn`,
  `:204` `norm_eq_norm_of_isMaxOn_of_ball_subset`, `:212` `norm_eventually_eq_of_isLocalMax`.
* Euler product on `1 < s.re` EXISTS (no norm upper derived from it):
  `Mathlib/NumberTheory/EulerProduct/DirichletLSeries.lean:57` `summable_riemannZetaSummand`,
  `:89` `riemannZeta_eulerProduct_hasProd`, `:102` `riemannZeta_eulerProduct`.
* Dirichlet-series absolute convergence EXISTS (tool for this stone):
  `Mathlib/Analysis/PSeriesComplex.lean:25` `Complex.summable_one_div_nat_cpow`,
  `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:207` `zeta_eq_tsum_one_div_nat_cpow`,
  `:214` `zeta_eq_tsum_one_div_nat_add_one_cpow`,
  `Mathlib/Analysis/PSeries.lean:311` `Real.summable_nat_rpow`.
* Functional equation EXISTS (cos form, for later assembly, not used here):
  `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:178` `riemannZeta_one_sub`.
* Concurrent right-edge tsum bound REUSED read-only (not copied):
  `zeta_rigorous.lean:4340` `zetaUpper_riemannZeta_norm_le_tsum :
  ‖riemannZeta s‖ ≤ ∑' n, ((((n+1 : ℕ) : ℝ) ^ s.re))⁻¹` on `1 < s.re`
  (via `zeta_eq_tsum_one_div_nat_add_one_cpow` + `norm_tsum_le_tsum_norm`; valid:
  `Re > 1` zeta series IS absolutely convergent, so the tsum-majorant rule applies;
  no `0 < ∑'` conditional-tsum abuse).
* Concurrent real-axis cap REUSED read-only (transitively visible, not copied):
  `ZeroFreeRegionProof.lean:154` `ZeroFreeRegion.tsum_nat_rpow_neg_le`,
  `:201` `ZeroFreeRegion.norm_riemannZeta_ofReal`,
  `:207` `ZeroFreeRegion.norm_riemannZeta_ofReal_le :
  ‖riemannZeta (σ : ℂ)‖ ≤ 1 + 1 / (σ - 1)` on `1 < σ`
  (visible via `riemann_hypothesis → ZeroFreeRegion → ZeroFreeRegionProof`;
  `central_cover_assembly → riemann_hypothesis`; no new import, acyclic preserved).
* Direct `‖ζ(s)‖ ≤ ζ(Re s)` upper MISSING as a named lemma (this stone closes it
  in `‖·‖ ≤ ‖·‖` form); Lindelof/convexity zeta bound MISSING (residual).

WHAT IS PROVED (all unconditional, no `sorry`/`admit`/`axiom`/hypotheses):
* `TailZetaUpper.real_shift_tsum_eq`: `∑' (n+1)^{-σ} = ∑' n^{-σ}` on `1 < σ`
  (zero-term `Real.zero_rpow` + `Summable.tsum_eq_zero_add` + `Real.rpow_neg`).
* `TailZetaUpper.riemannZeta_norm_le_real_norm`: `‖riemannZeta s‖ ≤ ‖riemannZeta (s.re : ℂ)‖`
  on `1 < s.re` (E's tsum bound + shift equality + real-axis identity).
  Im-uniformity is FREE: RHS depends only on `s.re`, majorant independent of `s.im`.
* `TailZetaUpper.riemannZeta_norm_le_const_of_re_ge` / `zeta_norm_le_const_of_re_ge`:
  `‖·‖ ≤ 1 + 1 / δ` on `1 + δ ≤ Re` for any `δ > 0` (monotone `one_div_le_one_div_of_le`
  from the real-axis cap). `zeta = riemannZeta` definitionally (`rfl`).
* `TailZetaUpper.zeta_rightEdge_B3` (`Re ≥ 3/2 → ‖zeta‖ ≤ 3`, `δ = 1/2`):
  `TailZetaUpper.zeta_rightEdge_B2` (`Re ≥ 2 → ‖zeta‖ ≤ 2`, `δ = 1`).
  Strip shape: right edge `Re ≥ 1 + δ`, `T = 0` (all `Im`, no `|Im| ≥ T` needed);
  constants `B = 1 + 1 / δ` (`B = 3`, `B = 2` in the instances).

RESIDUAL (§1h: assembly exceeds one session — STOP after this stone):
exact next lemma `TailZetaUpper_threeLines_FE_assembly` (NOT proved here): from
(i) this stone at `Re = 1 + δ`, (ii) a left-edge bound on `Re = 1 - δ'` via FE
`riemannZeta_one_sub` (needs `‖F‖` upper/lower + Stirling Gamma upper), and
(iii) Hadamard `norm_le_interp_of_mem_verticalClosedStrip'` applied to the
POLE-REMOVED entire `f s = (s - 1) * riemannZeta s` (with `BddAbove` +
`DiffContOnCl` discharged around `s = 1`), infer Im-uniform `‖zeta‖ ≤ B`
on the tail strip `0 < Re < 1 / 2`, `|Im| ≥ T` for explicit `B`, `T`
(the `MollifiedRoucheLeaf`-gap feeder input `‖ζ·M - 1‖ ≤ 1 - δ` needs this `B`).
-/

namespace TailZetaUpper

open scoped BigOperators

/-- Shifted vs unshifted Real `p`-series agree on `1 < σ` (zero term vanishes). -/
theorem real_shift_tsum_eq {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, ((((n + 1 : ℕ) : ℝ) ^ σ))⁻¹) = (∑' n : ℕ, (n : ℝ) ^ (-σ)) := by
  have hne : (-σ) ≠ 0 := by linarith
  have hsumm : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith : -σ < -1)
  have h0real : ((0 : ℝ) ^ (-σ)) = 0 :=
    Real.zero_rpow hne
  have hterm : ∀ n : ℕ, ((((n + 1 : ℕ) : ℝ) ^ σ))⁻¹ = (((n : ℝ) + 1) ^ (-σ)) := by
    intro n
    have hcast : ((((n + 1 : ℕ) : ℝ)) = ((n : ℝ) + 1)) := by push_cast; ring
    rw [hcast]
    exact (Real.rpow_neg (by positivity) _).symm
  have hshift : (∑' n : ℕ, (n : ℝ) ^ (-σ)) =
      (∑' n : ℕ, (((n : ℝ) + 1) ^ (-σ))) := by
    have h := hsumm.tsum_eq_zero_add
    simpa [h0real] using h
  calc (∑' n : ℕ, ((((n + 1 : ℕ) : ℝ) ^ σ))⁻¹)
      = (∑' n : ℕ, (((n : ℝ) + 1) ^ (-σ))) := tsum_congr hterm
    _ = (∑' n : ℕ, (n : ℝ) ^ (-σ)) := hshift.symm

/-- Im-uniform domination on `Re > 1`: `‖ζ(s)‖ ≤ ‖ζ(Re s)‖` (RHS `Im`-free). -/
theorem riemannZeta_norm_le_real_norm {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ ‖riemannZeta (s.re : ℂ)‖ := by
  have hE := zetaUpper_riemannZeta_norm_le_tsum hs
  have hshift := real_shift_tsum_eq (σ := s.re) hs
  have hReal := ZeroFreeRegion.norm_riemannZeta_ofReal (σ := s.re) hs
  calc ‖riemannZeta s‖
      ≤ (∑' n : ℕ, ((((n + 1 : ℕ) : ℝ) ^ s.re))⁻¹) := hE
    _ = (∑' n : ℕ, (n : ℝ) ^ (-s.re)) := hshift
    _ = ‖riemannZeta (s.re : ℂ)‖ := hReal.symm

/-- Explicit Im-uniform cap `1 + 1 / δ` on `1 + δ ≤ Re` (any `δ > 0`). -/
theorem riemannZeta_norm_le_const_of_re_ge {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hs : 1 + δ ≤ s.re) : ‖riemannZeta s‖ ≤ 1 + 1 / δ := by
  have h1 : 1 < s.re := by linarith
  have hle1 : ‖riemannZeta s‖ ≤ ‖riemannZeta (s.re : ℂ)‖ :=
    riemannZeta_norm_le_real_norm h1
  have hle2 : ‖riemannZeta (s.re : ℂ)‖ ≤ 1 + 1 / (s.re - 1) :=
    ZeroFreeRegion.norm_riemannZeta_ofReal_le (σ := s.re) (by linarith : 1 < s.re)
  have hle3 : 1 + 1 / (s.re - 1) ≤ 1 + 1 / δ := by
    have hdiv : 1 / (s.re - 1) ≤ 1 / δ :=
      one_div_le_one_div_of_le hδ (by linarith : δ ≤ s.re - 1)
    linarith
  exact le_trans (le_trans hle1 hle2) hle3

/-- `zeta` alias form of the Im-uniform cap (definitionally `rfl`). -/
theorem zeta_norm_le_const_of_re_ge {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hs : 1 + δ ≤ s.re) : ‖zeta s‖ ≤ 1 + 1 / δ := by
  have h : zeta s = riemannZeta s := rfl
  rw [h]
  exact riemannZeta_norm_le_const_of_re_ge hδ hs

/-- Right edge `Re ≥ 3 / 2` with `B = 3` (`δ = 1 / 2`), Im-uniform. -/
theorem zeta_rightEdge_B3 {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖zeta s‖ ≤ 3 := by
  have hδ : (0 : ℝ) < 1 / 2 := by norm_num
  have hs' : (1 : ℝ) + 1 / 2 ≤ s.re := by linarith
  have h := zeta_norm_le_const_of_re_ge hδ hs'
  have heq : (1 : ℝ) + 1 / (1 / 2 : ℝ) = 3 := by norm_num
  rwa [heq] at h

/-- Right edge `Re ≥ 2` with `B = 2` (`δ = 1`), Im-uniform. -/
theorem zeta_rightEdge_B2 {s : ℂ} (hs : 2 ≤ s.re) : ‖zeta s‖ ≤ 2 := by
  have hδ : (0 : ℝ) < 1 := by norm_num
  have hs' : (1 : ℝ) + 1 ≤ s.re := by linarith
  have h := zeta_norm_le_const_of_re_ge hδ hs'
  have heq : (1 : ℝ) + 1 / (1 : ℝ) = 2 := by norm_num
  rwa [heq] at h

end TailZetaUpper

/-!
# Zeta upper on the R02 disc via Hadamard three-lines on pole-removed `F`

GREP-FIRST RECORD (repo + Mathlib, via the grep tool, 2026-09-03; bridges FOUND, not recreated):
* Hadamard three-lines EXISTS (exact needed shape):
  `Mathlib/Analysis/Complex/Hadamard.lean:608`
  `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`
  (with `verticalClosedStrip` at `:73`, `verticalStrip` used at `:120`/`:212`).
* Phragmen-Lindelof vertical strip EXISTS:
  `Mathlib/Analysis/Complex/PhragmenLindelof.lean:275`
  `PhragmenLindelof.vertical_strip` (not used; three-lines is sharper for two caps).
* FE EXISTS (cos form): `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:178`
  `riemannZeta_one_sub`.
* Residue EXISTS: `.../RiemannZeta.lean:242` `riemannZeta_residue_one`.
* Differentiability off the pole EXISTS: `:139` `differentiableAt_riemannZeta`.
* Removable singularity EXISTS:
  `Mathlib/Analysis/Complex/RemovableSingularity.lean:36`
  `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`.
* Update-continuity EXISTS: `Mathlib/Topology/Piecewise.lean:33`
  `continuousAt_update_same` (root namespace).
* Entire implies `DiffContOnCl` EXISTS:
  `Mathlib/Analysis/Calculus/DiffContOnCl.lean:42` `Differentiable.diffContOnCl`.
* Right edge (proved, this file): `TailZetaUpper.zeta_rightEdge_B3`
  (`Re ≥ 3/2 → ‖zeta‖ ≤ 3`), `TailZetaUpper.zeta_rightEdge_B2` (`Re ≥ 2 → ≤ 2`).
* Left-edge FE-factor toolkit (proved, imported `interval_arith.lean`, `namespace RowFE`):
  `RowFE_cpow_upper` (`:30998`), `RowFE_cos_num` (`:30993`),
  `RowFE_Gamma_upper_of` (`:31257`), `RowFE_factor_upper_of` (`:31451`),
  `RowFEFactor` (`:30856`); `Real.exp_one_lt_d9`
  (`Mathlib/Analysis/Complex/ExponentialBounds.lean:38`, also used at
  `zeta_rigorous.lean:3651`); `Real.Gamma_add_one` / `Real.Gamma_one`
  (`Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:409` / `:415`).
* `Complex.sq_norm` + `Complex.normSq_apply` (used at `zeta_rigorous.lean`
  `zetaRefl_norm_le`); `le_of_pow_le_pow_left₀` + `Complex.norm_le_abs_re_add_abs_im`
  (used in this file at `R02_cvtFactor_norm_ge` / `R02_norm_le_of_mem`).
* Direct `f = ζ` three-lines is blocked by the pole at `s = 1` for `DiffContOnCl`
  (verified: `differentiableAt_riemannZeta` needs `s ≠ 1`). The entire pole-removed
  `F` below is CREATED in-file: repo-wide grep for `poleRemovedZeta` shows no such
  definition (only this guide's prose stubs naming the obligation).
* Stirling-sharp Gamma upper with `Im`-decay is MISSING repo-wide (only the crude
  `‖Γ‖ ≤ Real.Gamma` comparison + row caps): the sharp whole-line left edge is the
  documented remainder, kept as explicit numeric premises below.

WHAT IS PROVED (unconditional, no `sorry`/`admit`/`axiom`/stand-ins):
* `poleRemovedZeta` (`F(s) = (s-1)·ζ(s)`, `F(1) = 1`) + `poleRemovedZeta_differentiable`
  (removable singularity via the residue) + `DiffContOnCl` on every vertical strip.
* `dampedPoleRemoved` (`G(s) = F(s)·exp((1/100)·(s-c)²)`, `c = -6.75·I`) + entire +
  `DiffContOnCl`. Damping makes whole-line caps satisfiable (undamped `F` is genuinely
  unbounded in `Im`, so undamped uniform premises would be vacuous).
* Right edge: pointwise `‖F(s)‖ ≤ ‖s-1‖·2` on `Re ≥ 2`; window `≤ 19.5` on
  `Re = 2`, `|Im| ≤ 8.75` (covers the R02 `Im`-range `[-8.25,-5.25]`).
* Left edge WINDOW (proved): `‖G(z)‖ ≤ 1200000000` on `Re = -1`, `|Im| ≤ 8.75`, via FE
  (`‖F(2-iτ)‖ ≤ 2e7` from RowFE components + `Real.Gamma 2 = 1`) times reflected
  `‖ζ‖ ≤ 2` times `‖z-1‖ ≤ 10.75` times damping `≤ e < 2.7183`.
* Damping lower `≥ 0.97` and `‖s-1‖ ≥ 5.25` on the R02 disc `s`-rect
  (`Re ∈ [0.05,0.74]`, `Im ∈ [-8.25,-5.25]`).

CONDITIONAL (explicit numeric premises, `R02_closed_of_factorBounds` style):
* `zetaUpper_R02_of_threeLines`: whole-line caps `A` (left) + `B` (right) + `BddAbove`
  for damped `G` on `[l,u] ⊃ [0.05,0.74]` gives pointwise
  `‖ζ(s)‖ ≤ A^(1-t)·B^t/(5.25·0.97)` with `t = (s.re-l)/(u-l)`.
* `zetaUpper_R02_of_threeLines_uniform`: with `0 < A`, `0 ≤ B ≤ A`, uniform `≤ A/5.0925`.
* `zetaUpper_R02_ten_of_bounds`: with `A ≤ 50.925` (at `l = -1`, `u = 2`), `‖ζ‖ ≤ 10`
  on the R02 rect (hence discharges `R02_zeta_upper_obligation`-shaped goals).

GAP (exact, report-and-stop): `≤ 10` needs a whole-line damped left cap `A ≤ 50.925`
(with `B ≤ A`); the honestly proved crude window cap is `1.2e9` — a `~2.4e7×` gap,
closable only by a Stirling-sharp left edge (true growth is polynomial, so true `A`
is `O(10²)`), NOT by extending windows. `zeta = riemannZeta` by `rfl` throughout.
-/

namespace ZetaUpperR02ThreeLines

open scoped Topology

/-- Damping center `c = -6.75·I` (middle of the R02 `Im`-range `[-8.25,-5.25]`). -/
def dampCenter : ℂ := ⟨0, -6.75⟩

/-- Pole-removed zeta `F(s) = (s-1)·ζ(s)` with the removable value `F(1) = 1`
(the residue `riemannZeta_residue_one`). Proved entire below. -/
noncomputable def poleRemovedZeta (s : ℂ) : ℂ :=
  Function.update (fun s => (s - 1) * riemannZeta s) 1 1 s

/-- Gaussian-damped pole-removed `G(s) = F(s)·exp((1/100)·(s-c)²)`. Entire; the
Gaussian decay in `Im` makes whole-line strip caps satisfiable. -/
noncomputable def dampedPoleRemoved (s : ℂ) : ℂ :=
  poleRemovedZeta s * Complex.exp (((1 / 100 : ℝ) : ℂ) * (s - dampCenter) ^ 2)

theorem dampCenter_re : dampCenter.re = 0 := rfl

theorem dampCenter_im : dampCenter.im = -6.75 := rfl

theorem poleRemovedZeta_of_ne {s : ℂ} (hs : s ≠ 1) :
    poleRemovedZeta s = (s - 1) * riemannZeta s := by
  show Function.update (fun s => (s - 1) * riemannZeta s) 1 1 s = _
  exact Function.update_of_ne hs _ _

theorem poleRemovedZeta_one : poleRemovedZeta 1 = 1 := by
  show Function.update (fun s => (s - 1) * riemannZeta s) 1 1 1 = _
  exact Function.update_self _ _ _

theorem poleRemovedZeta_continuousAt_one : ContinuousAt poleRemovedZeta 1 := by
  show ContinuousAt (Function.update (fun s => (s - 1) * riemannZeta s) 1 1) 1
  exact continuousAt_update_same.mpr riemannZeta_residue_one

theorem poleRemovedZeta_differentiableAt_off {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ poleRemovedZeta s := by
  have hzmem : s ∈ ({1} : Set ℂ)ᶜ := by simpa using hs
  have hmem : ({1} : Set ℂ)ᶜ ∈ 𝓝 s :=
    isOpen_compl_singleton.mem_nhds hzmem
  have hEq : (fun t => (t - 1) * riemannZeta t) =ᶠ[𝓝 s] poleRemovedZeta := by
    filter_upwards [hmem] with w hw
    exact (poleRemovedZeta_of_ne (by simpa using hw)).symm
  have hdiff : DifferentiableAt ℂ (fun t => (t - 1) * riemannZeta t) s :=
    (by fun_prop : DifferentiableAt ℂ (fun t : ℂ => t - 1) s).mul
      (differentiableAt_riemannZeta hs)
  exact hdiff.congr_of_eventuallyEq hEq.symm

theorem poleRemovedZeta_analyticAt_one : AnalyticAt ℂ poleRemovedZeta 1 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _
    poleRemovedZeta_continuousAt_one
  filter_upwards [self_mem_nhdsWithin (a := (1 : ℂ)) (s := ({1} : Set ℂ)ᶜ)] with z hz
  exact poleRemovedZeta_differentiableAt_off (by simpa using hz)

theorem poleRemovedZeta_differentiable : Differentiable ℂ poleRemovedZeta := by
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · exact poleRemovedZeta_analyticAt_one.differentiableAt
  · exact poleRemovedZeta_differentiableAt_off hs

theorem poleRemovedZeta_diffContOnCl_strip (l u : ℝ) :
    DiffContOnCl ℂ poleRemovedZeta
      (Complex.HadamardThreeLines.verticalStrip l u) :=
  poleRemovedZeta_differentiable.diffContOnCl

theorem dampedPoleRemoved_differentiable :
    Differentiable ℂ dampedPoleRemoved := by
  have hexp : Differentiable ℂ
      (fun s : ℂ => Complex.exp (((1 / 100 : ℝ) : ℂ) * (s - dampCenter) ^ 2)) := by
    fun_prop
  unfold dampedPoleRemoved
  exact poleRemovedZeta_differentiable.mul hexp

theorem dampedPoleRemoved_diffContOnCl_strip (l u : ℝ) :
    DiffContOnCl ℂ dampedPoleRemoved
      (Complex.HadamardThreeLines.verticalStrip l u) :=
  dampedPoleRemoved_differentiable.diffContOnCl

/-- Right edge, pointwise: `‖F(s)‖ ≤ ‖s-1‖·2` on `Re ≥ 2` (TailZetaUpper B2). -/
theorem poleRemovedZeta_rightEdge_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖poleRemovedZeta s‖ ≤ ‖s - 1‖ * 2 := by
  have hs1 : s ≠ 1 := by
    intro h
    have hre : s.re = 1 := by rw [h, Complex.one_re]
    linarith
  have hZ : ‖riemannZeta s‖ ≤ 2 := by
    have h := TailZetaUpper.zeta_rightEdge_B2 hs
    rwa [show zeta s = riemannZeta s from rfl] at h
  rw [poleRemovedZeta_of_ne hs1, norm_mul]
  exact mul_le_mul_of_nonneg_left hZ (norm_nonneg _)

/-- Right edge, R02-window uniform: `‖F(s)‖ ≤ 19.5` on `Re = 2`, `|Im| ≤ 8.75`. -/
theorem poleRemovedZeta_rightEdge_window {s : ℂ} (hre : s.re = 2)
    (him : |s.im| ≤ 8.75) : ‖poleRemovedZeta s‖ ≤ 19.5 := by
  have hle := poleRemovedZeta_rightEdge_le (by linarith [hre])
  have hnorm : ‖s - 1‖ ≤ 9.75 := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    have hre1 : (s - 1).re = 1 := by
      rw [Complex.sub_re, Complex.one_re, hre]; norm_num
    have him1 : (s - 1).im = s.im := by
      rw [Complex.sub_im, Complex.one_im, sub_zero]
    rw [hre1, him1, abs_one] at h
    linarith
  calc ‖poleRemovedZeta s‖ ≤ ‖s - 1‖ * 2 := hle
    _ ≤ 9.75 * 2 := mul_le_mul_of_nonneg_right hnorm (by norm_num)
    _ = 19.5 := by norm_num

/-- `‖exp w‖ = exp (w.re)` (via `‖·‖² = normSq`, no missing-name risk). -/
theorem norm_complex_exp (w : ℂ) : ‖Complex.exp w‖ = Real.exp w.re := by
  have hnn1 : (0 : ℝ) ≤ ‖Complex.exp w‖ := norm_nonneg _
  have hnn2 : (0 : ℝ) ≤ Real.exp w.re := (Real.exp_pos _).le
  have hsq : ‖Complex.exp w‖ ^ 2 = (Real.exp w.re) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.exp_re, Complex.exp_im]
    have htrig : Real.sin w.im ^ 2 + Real.cos w.im ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq w.im
    linear_combination (Real.exp w.re) ^ 2 * htrig
  have e1 := Real.sqrt_sq hnn1
  have e2 := Real.sqrt_sq hnn2
  rw [← e1, hsq, e2]

/-- Damping lower `≥ 0.97` on the R02 disc `s`-rect
(`Re((s-c)²) = σ²-(τ+6.75)² ≥ -2.25`, `(1/100)·` it `≥ -0.0225`). -/
theorem damp_lower_R02 {s : ℂ} (hs_lo : 0.05 ≤ s.re) (hs_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25) :
    (0.97 : ℝ)
      ≤ ‖Complex.exp (((1 / 100 : ℝ) : ℂ) * (s - dampCenter) ^ 2)‖ := by
  have hwre : ((((1 / 100 : ℝ)) : ℂ) * (s - dampCenter) ^ 2).re
      = (1 / 100) * (((s - dampCenter) ^ 2).re) := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsq2 : ((s - dampCenter) ^ 2).re
      = (s.re) ^ 2 - (s.im + 6.75) ^ 2 := by
    have e1 : (s - dampCenter).re = s.re := by
      rw [Complex.sub_re, dampCenter_re, sub_zero]
    have e2 : (s - dampCenter).im = s.im + 6.75 := by
      rw [Complex.sub_im, dampCenter_im]
      ring
    rw [pow_two, Complex.mul_re, e1, e2]
    ring
  have hT : (s.im + 6.75) ^ 2 ≤ 2.25 := by
    have habs : |s.im + 6.75| ≤ 1.5 := by
      rw [abs_le]
      constructor <;> linarith
    have h1 : -(1.5 : ℝ) ≤ s.im + 6.75 := (abs_le.mp habs).1
    have h2 : s.im + 6.75 ≤ 1.5 := (abs_le.mp habs).2
    have hle := sq_le_sq' h1 h2
    have e : (1.5 : ℝ) ^ 2 = 2.25 := by norm_num
    rwa [e] at hle
  have hwge : (-0.0225 : ℝ)
      ≤ ((((1 / 100 : ℝ)) : ℂ) * (s - dampCenter) ^ 2).re := by
    rw [hwre, hsq2]
    have hσ : (0 : ℝ) ≤ (s.re) ^ 2 := sq_nonneg _
    linarith
  rw [norm_complex_exp]
  have h1 := Real.add_one_le_exp
    (((((1 / 100 : ℝ)) : ℂ) * (s - dampCenter) ^ 2).re)
  linarith

/-- `‖s-1‖ ≥ 5.25` on the R02 `Im`-range (`‖s-1‖² = (σ-1)²+τ² ≥ τ² ≥ 5.25²`). -/
theorem sSubOne_norm_ge_R02 {s : ℂ} (him_hi : s.im ≤ -5.25) :
    (5.25 : ℝ) ≤ ‖s - 1‖ := by
  have e : ‖s - 1‖ ^ 2 = (s.re - 1) ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, sub_zero]
    ring
  have h1 : (0 : ℝ) ≤ (s.re - 1) ^ 2 := sq_nonneg _
  have habs : (5.25 : ℝ) ≤ |s.im| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hsqabs : |s.im| ^ 2 = s.im ^ 2 := sq_abs _
  have h2 : (5.25 : ℝ) ^ 2 ≤ s.im ^ 2 := by
    have hnn : (0 : ℝ) ≤ |s.im| := abs_nonneg _
    have hmul := mul_le_mul habs habs (by norm_num) hnn
    rw [← pow_two, ← pow_two] at hmul
    rwa [hsqabs] at hmul
  have hsq : (5.25 : ℝ) ^ 2 ≤ ‖s - 1‖ ^ 2 := by linarith [e, h1, h2]
  exact le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg _) hsq

/-- Three-lines assembly: whole-line damped caps give a pointwise zeta upper on R02.
`A`/`B` are the left/right whole-line caps for damped `G`; `BddAbove` is the
Stirling-growth remainder (satisfiable: Gaussian dominates any fixed exponential). -/
theorem zetaUpper_R02_of_threeLines {l u A B : ℝ} (hlu : l < u)
    (hcover_lo : l ≤ 0.05) (hcover_hi : 0.74 ≤ u)
    (hBdd : BddAbove ((norm ∘ dampedPoleRemoved) ''
      Complex.HadamardThreeLines.verticalClosedStrip l u))
    (hLeft : ∀ z ∈ Set.preimage Complex.re {l}, ‖dampedPoleRemoved z‖ ≤ A)
    (hRight : ∀ z ∈ Set.preimage Complex.re {u}, ‖dampedPoleRemoved z‖ ≤ B)
    {s : ℂ} (hs_lo : 0.05 ≤ s.re) (hs_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25) :
    ‖riemannZeta s‖ ≤ A ^ (1 - (s.re - l) / (u - l)) * B ^ ((s.re - l) / (u - l))
      / (5.25 * 0.97) := by
  have hz : s ∈ Complex.HadamardThreeLines.verticalClosedStrip l u := by
    unfold Complex.HadamardThreeLines.verticalClosedStrip
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> linarith
  have h3 :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      hlu hz (dampedPoleRemoved_diffContOnCl_strip l u) hBdd hLeft hRight
  have hs1 : s ≠ 1 := by
    intro h
    have himm : s.im = 0 := by
      rw [h]
      exact Complex.one_im
    linarith
  have hnorm : ‖dampedPoleRemoved s‖
      = (‖s - 1‖ * ‖riemannZeta s‖)
        * ‖Complex.exp (((1 / 100 : ℝ) : ℂ) * (s - dampCenter) ^ 2)‖ := by
    unfold dampedPoleRemoved
    rw [poleRemovedZeta_of_ne hs1, norm_mul, norm_mul]
  have hge1 : (5.25 : ℝ) ≤ ‖s - 1‖ := sSubOne_norm_ge_R02 him_hi
  have hge2 : (0.97 : ℝ)
      ≤ ‖Complex.exp (((1 / 100 : ℝ) : ℂ) * (s - dampCenter) ^ 2)‖ :=
    damp_lower_R02 hs_lo hs_hi him_lo him_hi
  have hmul : 5.25 * ‖riemannZeta s‖ * 0.97 ≤ ‖dampedPoleRemoved s‖ := by
    rw [hnorm]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hge1 (norm_nonneg _)) hge2
      (by norm_num) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hC : 5.25 * ‖riemannZeta s‖ * 0.97
      ≤ A ^ (1 - (s.re - l) / (u - l)) * B ^ ((s.re - l) / (u - l)) :=
    le_trans hmul h3
  have hden : (0 : ℝ) < 5.25 * 0.97 := by norm_num
  rw [le_div_iff₀ hden]
  have hrr : 5.25 * ‖riemannZeta s‖ * 0.97
      = ‖riemannZeta s‖ * (5.25 * 0.97) := by
    ring
  linarith [hC]

/-- `zeta` alias form (`zeta = riemannZeta` by `rfl`). -/
theorem zetaUpper_R02_of_threeLines_zeta {l u A B : ℝ} (hlu : l < u)
    (hcover_lo : l ≤ 0.05) (hcover_hi : 0.74 ≤ u)
    (hBdd : BddAbove ((norm ∘ dampedPoleRemoved) ''
      Complex.HadamardThreeLines.verticalClosedStrip l u))
    (hLeft : ∀ z ∈ Set.preimage Complex.re {l}, ‖dampedPoleRemoved z‖ ≤ A)
    (hRight : ∀ z ∈ Set.preimage Complex.re {u}, ‖dampedPoleRemoved z‖ ≤ B)
    {s : ℂ} (hs_lo : 0.05 ≤ s.re) (hs_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25) :
    ‖zeta s‖ ≤ A ^ (1 - (s.re - l) / (u - l)) * B ^ ((s.re - l) / (u - l))
      / (5.25 * 0.97) := by
  have h : zeta s = riemannZeta s := rfl
  rw [h]
  exact zetaUpper_R02_of_threeLines hlu hcover_lo hcover_hi hBdd hLeft hRight
    hs_lo hs_hi him_lo him_hi

/-- Uniform version (`0 < A`, `0 ≤ B ≤ A`): interpolation `≤ A`, so `‖ζ‖ ≤ A/5.0925`. -/
theorem zetaUpper_R02_of_threeLines_uniform {l u A B : ℝ} (hlu : l < u)
    (hcover_lo : l ≤ 0.05) (hcover_hi : 0.74 ≤ u)
    (hApos : 0 < A) (hBnn : 0 ≤ B) (hBA : B ≤ A)
    (hBdd : BddAbove ((norm ∘ dampedPoleRemoved) ''
      Complex.HadamardThreeLines.verticalClosedStrip l u))
    (hLeft : ∀ z ∈ Set.preimage Complex.re {l}, ‖dampedPoleRemoved z‖ ≤ A)
    (hRight : ∀ z ∈ Set.preimage Complex.re {u}, ‖dampedPoleRemoved z‖ ≤ B)
    {s : ℂ} (hs_lo : 0.05 ≤ s.re) (hs_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25) :
    ‖riemannZeta s‖ ≤ A / (5.25 * 0.97) := by
  have hpt := zetaUpper_R02_of_threeLines hlu hcover_lo hcover_hi hBdd hLeft hRight
    hs_lo hs_hi him_lo him_hi
  have hul : (0 : ℝ) < u - l := sub_pos.mpr hlu
  have ht0 : (0 : ℝ) ≤ (s.re - l) / (u - l) :=
    div_nonneg (by linarith) hul.le
  have hpow : A ^ (1 - (s.re - l) / (u - l)) * B ^ ((s.re - l) / (u - l)) ≤ A := by
    have h1 : B ^ ((s.re - l) / (u - l)) ≤ A ^ ((s.re - l) / (u - l)) :=
      Real.rpow_le_rpow hBnn hBA ht0
    have h2 : A ^ (1 - (s.re - l) / (u - l)) * A ^ ((s.re - l) / (u - l)) = A := by
      rw [← Real.rpow_add hApos, sub_add_cancel, Real.rpow_one]
    calc A ^ (1 - (s.re - l) / (u - l)) * B ^ ((s.re - l) / (u - l))
        ≤ A ^ (1 - (s.re - l) / (u - l)) * A ^ ((s.re - l) / (u - l)) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hApos.le _)
      _ = A := h2
  have hden : (0 : ℝ) < 5.25 * 0.97 := by norm_num
  calc ‖riemannZeta s‖
      ≤ A ^ (1 - (s.re - l) / (u - l)) * B ^ ((s.re - l) / (u - l))
        / (5.25 * 0.97) := hpt
    _ ≤ A / (5.25 * 0.97) := by
      have hcancel : A / (5.25 * 0.97) * (5.25 * 0.97) = A := by
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (ne_of_gt hden), mul_one]
      rw [div_le_iff₀ hden, hcancel]
      exact hpow

/-- Threshold: at `l = -1`, `u = 2`, a whole-line left cap `A ≤ 50.925`
(with `B ≤ A`) gives `‖ζ‖ ≤ 10` on the R02 rect. -/
theorem zetaUpper_R02_ten_of_bounds {A B : ℝ}
    (hApos : 0 < A) (hBnn : 0 ≤ B) (hBA : B ≤ A) (hAcap : A ≤ 50.925)
    (hBdd : BddAbove ((norm ∘ dampedPoleRemoved) ''
      Complex.HadamardThreeLines.verticalClosedStrip (-1) 2))
    (hLeft : ∀ z ∈ Set.preimage Complex.re {(-1 : ℝ)},
      ‖dampedPoleRemoved z‖ ≤ A)
    (hRight : ∀ z ∈ Set.preimage Complex.re {(2 : ℝ)},
      ‖dampedPoleRemoved z‖ ≤ B)
    {s : ℂ} (hs_lo : 0.05 ≤ s.re) (hs_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25) :
    ‖riemannZeta s‖ ≤ 10 := by
  have hU := zetaUpper_R02_of_threeLines_uniform (l := -1) (u := 2) (by norm_num)
    (by norm_num) (by norm_num) hApos hBnn hBA hBdd hLeft hRight
    hs_lo hs_hi him_lo him_hi
  have hden : (5.25 : ℝ) * 0.97 = 5.0925 := by norm_num
  rw [hden] at hU
  have e : (50.925 : ℝ) = 10 * 5.0925 := by norm_num
  have hA' : A ≤ 10 * 5.0925 := by rwa [e] at hAcap
  calc ‖riemannZeta s‖ ≤ A / 5.0925 := hU
    _ ≤ 10 := by
        rw [div_le_iff₀ (by norm_num)]
        linarith [hA']

/-- Left edge WINDOW (proved): `‖G(z)‖ ≤ 1200000000` on `Re = -1`, `|Im| ≤ 8.75`.
Via FE at `w = 1-z` (`Re = 2`): `‖F(w)‖ ≤ 2·1·1·1e7 = 2e7` (RowFE components with
`Real.Gamma 2 = 1`) times reflected `‖ζ‖ ≤ 2` (B2), times `‖z-1‖ ≤ 10.75`, times
damping `≤ e < 2.7183`: `10.75·4e7·2.7183 = 1168869000 ≤ 1.2e9`. -/
theorem damped_leftWindow_le {z : ℂ} (hz_re : z.re = -1)
    (him : |z.im| ≤ 8.75) :
    ‖dampedPoleRemoved z‖ ≤ 1200000000 := by
  have hz1 : z ≠ 1 := by
    intro h
    have hre : z.re = 1 := by rw [h, Complex.one_re]
    linarith
  have hw_re : ((1 : ℂ) - z).re = 2 := by
    rw [Complex.sub_re, Complex.one_re, hz_re]; norm_num
  have hw_im : ((1 : ℂ) - z).im = -z.im := by
    rw [Complex.sub_im, Complex.one_im, zero_sub]
  have hs_neg : ∀ n : ℕ, (1 - z) ≠ -((n : ℂ)) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re,
      Complex.natCast_re] at hre
    rw [hz_re] at hre
    have hnn : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg n
    linarith
  have hs1' : (1 - z) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re] at hre
    rw [hz_re] at hre
    norm_num at hre
  have hFE' : riemannZeta z
      = RowFE.RowFEFactor (1 - z) * riemannZeta (1 - z) := by
    have hFE := riemannZeta_one_sub (s := 1 - z) hs_neg hs1'
    have h1sub : (1 : ℂ) - (1 - z) = z := by ring
    rw [h1sub] at hFE
    have h2 : (2 * (2 * (Real.pi : ℂ)) ^ (-(1 - z)) * Complex.Gamma (1 - z)
        * Complex.cos ((Real.pi : ℂ) * (1 - z) / 2) * riemannZeta (1 - z))
        = RowFE.RowFEFactor (1 - z) * riemannZeta (1 - z) := by
      unfold RowFE.RowFEFactor
      ring
    rw [← h2]
    exact hFE
  have hZrefl : ‖riemannZeta (1 - z)‖ ≤ 2 := by
    have h := TailZetaUpper.zeta_rightEdge_B2 (s := 1 - z) (by linarith [hw_re])
    rwa [show zeta (1 - z) = riemannZeta (1 - z) from rfl] at h
  have hcp : ‖(2 * (Real.pi : ℂ)) ^ (-(1 - z))‖ ≤ 1 :=
    RowFE.RowFE_cpow_upper (by rw [hw_re]; norm_num)
  have hG : ‖Complex.Gamma (1 - z)‖ ≤ 1 :=
    RowFE.RowFE_Gamma_upper_of (s := 1 - z) (v := 2) (G := 1) hw_re
      Real.Gamma_two.le (by norm_num)
  have hcos : ‖Complex.cos ((Real.pi : ℂ) * ((1 - z) / 2))‖ ≤ 10000000 := by
    have himw : |((1 : ℂ) - z).im| ≤ 8.75 := by
      rw [hw_im, abs_neg]
      exact him
    exact RowFE.RowFE_cos_num himw
  have hFraw : ‖RowFE.RowFEFactor (1 - z)‖ ≤ 20000000 := by
    have h := RowFE.RowFE_factor_upper_of hcp hG hcos (by norm_num : (0 : ℝ) ≤ 1)
    have e : (2 : ℝ) * 1 * 1 * 10000000 = 20000000 := by norm_num
    rwa [e] at h
  have hZ : ‖riemannZeta z‖ ≤ 40000000 := by
    rw [hFE', norm_mul]
    calc ‖RowFE.RowFEFactor (1 - z)‖ * ‖riemannZeta (1 - z)‖
          ≤ 20000000 * 2 :=
            mul_le_mul hFraw hZrefl (norm_nonneg _) (by norm_num)
        _ = 40000000 := by norm_num
  have hsub : ‖z - 1‖ ≤ 10.75 := by
    have h := Complex.norm_le_abs_re_add_abs_im (z - 1)
    have hre1 : (z - 1).re = -2 := by
      rw [Complex.sub_re, Complex.one_re, hz_re]; norm_num
    have him1 : (z - 1).im = z.im := by
      rw [Complex.sub_im, Complex.one_im, sub_zero]
    rw [hre1, him1] at h
    have e : |(-2 : ℝ)| = 2 := by norm_num
    rw [e] at h
    linarith
  have hF : ‖poleRemovedZeta z‖ ≤ 430000000 := by
    rw [poleRemovedZeta_of_ne hz1, norm_mul]
    calc ‖z - 1‖ * ‖riemannZeta z‖ ≤ 10.75 * 40000000 :=
          mul_le_mul hsub hZ (norm_nonneg _) (by norm_num)
      _ = 430000000 := by norm_num
  have hdamp : ‖Complex.exp (((1 / 100 : ℝ) : ℂ) * (z - dampCenter) ^ 2)‖
      ≤ 2.7183 := by
    have hsq2 : ((z - dampCenter) ^ 2).re = 1 - (z.im + 6.75) ^ 2 := by
      have e1 : (z - dampCenter).re = -1 := by
        rw [Complex.sub_re, dampCenter_re, hz_re, sub_zero]
      have e2 : (z - dampCenter).im = z.im + 6.75 := by
        rw [Complex.sub_im, dampCenter_im]
        ring
      rw [pow_two, Complex.mul_re, e1, e2]
      ring
    have hwre : ((((1 / 100 : ℝ)) : ℂ) * (z - dampCenter) ^ 2).re ≤ 0.01 := by
      have hwm : ((((1 / 100 : ℝ)) : ℂ) * (z - dampCenter) ^ 2).re
          = (1 / 100) * (((z - dampCenter) ^ 2).re) := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [hwm, hsq2]
      have ht2 : (0 : ℝ) ≤ (z.im + 6.75) ^ 2 := sq_nonneg _
      linarith
    rw [norm_complex_exp]
    have h1 : Real.exp ((((1 / 100 : ℝ)) : ℂ) * (z - dampCenter) ^ 2).re
        ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (1 : ℝ) ≤ 2.7183 :=
      le_trans (le_of_lt Real.exp_one_lt_d9) (by norm_num)
    linarith
  have hfin : dampedPoleRemoved z = poleRemovedZeta z
      * Complex.exp (((1 / 100 : ℝ) : ℂ) * (z - dampCenter) ^ 2) := rfl
  rw [hfin, norm_mul]
  calc ‖poleRemovedZeta z‖
      * ‖Complex.exp (((1 / 100 : ℝ) : ℂ) * (z - dampCenter) ^ 2)‖
        ≤ 430000000 * 2.7183 :=
          mul_le_mul hF hdamp (norm_nonneg _) (by norm_num)
    _ ≤ 1200000000 := by norm_num

#print axioms ZetaUpperR02ThreeLines.poleRemovedZeta_differentiable
#print axioms ZetaUpperR02ThreeLines.zetaUpper_R02_of_threeLines
#print axioms ZetaUpperR02ThreeLines.zetaUpper_R02_of_threeLines_uniform
#print axioms ZetaUpperR02ThreeLines.zetaUpper_R02_ten_of_bounds
#print axioms ZetaUpperR02ThreeLines.damped_leftWindow_le
#print axioms ZetaUpperR02ThreeLines.poleRemovedZeta_rightEdge_window

end ZetaUpperR02ThreeLines

/-!
# Tail three-lines FE assembly on `0 < Re < 1 / 2` (door-4 feeder, conditional)

GREP-FIRST RECORD (repo + Mathlib, via `rg`, 2026-09-03; bridges FOUND, not recreated):
* Hadamard three-lines EXISTS (exact needed shape, do NOT recreate):
  `Mathlib/Analysis/Complex/Hadamard.lean:608`
  `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`
  (variant `:27`, `verticalClosedStrip` at `:73`).
* Phragmen-Lindelof vertical strip EXISTS (not used; three-lines is sharper):
  `Mathlib/Analysis/Complex/PhragmenLindelof.lean:275` `PhragmenLindelof.vertical_strip`.
* FE EXISTS (cos form): `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:178`
  `riemannZeta_one_sub` (via `hurwitzZetaEven_one_sub`).
* Right edge (proved, this file): `TailZetaUpper.zeta_rightEdge_B3`
  (`Re ≥ 3/2 → ‖zeta‖ ≤ 3`), `TailZetaUpper.zeta_rightEdge_B2` (`Re ≥ 2 → ≤ 2`)
  (`riemann_hypothesis_newsection.lean:1032/1040`).
* Pole-removed entire `F` + damped `G` + `DiffContOnCl` + window caps (proved, this file,
  AD, cycle-checked safe): `ZetaUpperR02ThreeLines.poleRemovedZeta` (`:1128`),
  `dampedPoleRemoved` (`:1133`), `poleRemovedZeta_of_ne` (`:1140`),
  `poleRemovedZeta_differentiable` (`:1172`), `dampedPoleRemoved_diffContOnCl_strip`
  (`:1191`), `poleRemovedZeta_rightEdge_le` (`:1197`), `damped_leftWindow_le` (`:1425`),
  `zetaUpper_R02_of_threeLines` (`:1299`), `zetaUpper_R02_ten_of_bounds` (`:1398`,
  threshold `A ≤ 50.925` ⇒ `‖ζ‖ ≤ 10`, divisor `5.0925 = 5.25 * 0.97`).
* Left-edge FE-factor toolkit (proved, imported `interval_arith.lean`, `namespace RowFE`):
  `RowFEFactor` (`:30856`), `RowFE_cos_num` (`:30993`), `RowFE_cpow_upper` (`:30998`),
  `RowFE_Gamma_upper_of` (`:31257`), `RowFE_factor_upper_of` (`:31451`).
* Stirling-sharp Gamma upper with `Im`-decay MISSING repo-wide (only crude
  `‖Γ‖ ≤ Real.Gamma` + row caps): whole-line left cap stays an explicit premise.
* Direct `f = ζ` three-lines BLOCKED by the pole at `s = 1`
  (`differentiableAt_riemannZeta` needs `s ≠ 1`); pole-removed `F` reused read-only.
* `TailZetaUpper_threeLines_FE_assembly` NOT proved anywhere (only prose stub at `:964`);
  repo-wide `rg` for that name shows only the stub + this section (no duplication).

WHAT IS PROVED (unconditional implications, no `sorry`/`admit`/`axiom`/stand-ins):
* `TailZetaUpper_threeLines_FE_strip_subOne_ge_half`: `‖s-1‖ ≥ 1/2` on `0<Re<1/2`
  (Im-uniform; `‖s-1‖²=(σ-1)²+τ² ≥ (σ-1)² ≥ 1/4`).
* `TailZetaUpper_threeLines_FE_damp_ge`: damping lower
  `exp(-((|τ|+6.75)²)/100) ≤ ‖exp((1/100)(s-c)²)‖` with `c=-6.75·I`
  (reuses `ZetaUpperR02ThreeLines.norm_complex_exp`; `σ²≥0` +
  `(τ+6.75)² ≤ (|τ|+6.75)²` via `|τ+6.75| ≤ |τ|+6.75`).
* `TailZetaUpper_threeLines_FE_assembly` (EXACT task name): whole-line damped caps
  `A` (left `Re=-1`) + `B` (right `Re=2`) + `BddAbove` on `[-1,2]` ⇒ pointwise
  `‖ζ(s)‖ ≤ A^(1-(σ+1)/3)·B^((σ+1)/3)/(‖s-1‖·‖damp(s)‖)` for `0<σ<1/2`
  (`t=(σ+1)/3 ∈ (1/3,1/2)`; `l=-1,u=2` so `1-z` at `Re=-1` reflects to `Re=2`
  where `TailZetaUpper B=2` applies — the FE pairing, kept as premises).
* `TailZetaUpper_threeLines_FE_uniformExp` (explicit left-cap dependence):
  with `0<A`, `0≤B≤A`, `‖ζ(s)‖ ≤ A/((1/2)·exp(-((|τ|+6.75)²)/100))`
  (`= 2·A·exp(((|τ|+6.75)²)/100)`; numerator `≤A` as in
  `zetaUpper_R02_of_threeLines_uniform`; denominator from the two lowers).
* `TailZetaUpper_threeLines_FE_threshold_50p925` (numerified, AD-style):
  with `A ≤ 50.925`, `‖ζ(s)‖ ≤ 101.85·exp(((|τ|+6.75)²)/100)` on `0<Re<1/2`
  (`2·50.925=101.85`; same divisor shape as `50.925=10·5.0925`).
* `*_zeta` aliases (`zeta = riemannZeta` by `rfl`) for the `MollifiedRoucheLeaf` feeder.

NUMERIC THRESHOLDS: `l=-1`, `u=2`, `t=(σ+1)/3`; `‖s-1‖≥1/2`; damping
`≥ exp(-((|τ|+6.75)²)/100)`; `A≤50.925 ⇒ B≤101.85·exp(((|τ|+6.75)²)/100)`.
At `τ=0`: `≤101.85·exp(0.4556)≈160.7`; at `|τ|=10`: `≤101.85·exp(2.8056)≈1683`;
at `|τ|=8.75` (RowFE window): `≤101.85·exp(2.4025)≈1124`.

RESIDUAL GAP (honest, §1h report-and-stop): (i) whole-line caps `A,B` + `BddAbove`
for damped `G` remain PREMISES (satisfiable in principle: Gaussian dominates the
FE polynomial growth, but Stirling-sharp `‖F‖` upper on `Re=-1` is absent repo-wide,
so no numeric `A` is discharged here; proved window cap `1.2e9` is `~2.4e7×` above
`50.925` purely in the crude cos/exp majorant); (ii) the conclusion is
EXPLICITLY-GROWING in `|Im|` (`exp(τ²/100)`), NOT Im-uniform, so it does NOT yet give
the uniform `‖ζ‖≤B₀` on `0<Re<1/2, |Im|→∞` that `MollifiedRoucheLeaf K` needs;
via `shiftedS_re : (shiftedS z).re = 1/2-z.im`, the tail `10<|Re z|,0<Im<1/2`
is exactly `0<Re(shiftedS z)<1/2, |Im(shiftedS z)|>10`, where our bound is `~1683`
at `|Im|=10` and grows; (iii) even a uniform `‖ζ‖≤B₀` alone does NOT give
`‖ζ·M-1‖≤1-δ` (for `K=2`, `ζ·M₂-1=ζ/2-1`, so the gap is the disc `‖ζ-2‖≤2-2δ`,
needing phase/cancellation, not just size; `mollified_K2_gap_implies_zeta_bound`
is the converse). Mismatch is a FINDING, not a failure — do not spin.
-/

/-- `‖s-1‖ ≥ 1/2` on `0 < Re < 1/2` (Im-uniform). -/
theorem TailZetaUpper_threeLines_FE_strip_subOne_ge_half {s : ℂ}
    (hs_lo : 0 < s.re) (hs_hi : s.re < 1 / 2) : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
  have e : ‖s - 1‖ ^ 2 = (s.re - 1) ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, sub_zero]
    ring
  have h1 : (0 : ℝ) ≤ s.im ^ 2 := sq_nonneg _
  have hu_nonpos : s.re - 1 ≤ 0 := by linarith
  have habs : (1 / 2 : ℝ) ≤ |s.re - 1| := by
    rw [abs_of_nonpos hu_nonpos]
    linarith
  have hsqabs : |s.re - 1| ^ 2 = (s.re - 1) ^ 2 := sq_abs _
  have hnn : (0 : ℝ) ≤ |s.re - 1| := abs_nonneg _
  have hmul := mul_le_mul habs habs (by norm_num) hnn
  rw [← pow_two, ← pow_two] at hmul
  rw [hsqabs] at hmul
  have hsq2 : (1 / 2 : ℝ) ^ 2 ≤ ‖s - 1‖ ^ 2 := by linarith [e, h1, hmul]
  exact le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg _) hsq2

/-- Damping lower `exp(-((|τ|+6.75)²)/100) ≤ ‖exp((1/100)(s-c)²)‖` (`c=-6.75·I`). -/
theorem TailZetaUpper_threeLines_FE_damp_ge {s : ℂ} :
    Real.exp (-(((|s.im| + 6.75) ^ 2) / 100)) ≤
      ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
        (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ := by
  rw [ZetaUpperR02ThreeLines.norm_complex_exp]
  apply Real.exp_le_exp.mpr
  have e1 : (s - ZetaUpperR02ThreeLines.dampCenter).re = s.re := by
    rw [Complex.sub_re, ZetaUpperR02ThreeLines.dampCenter_re, sub_zero]
  have e2 : (s - ZetaUpperR02ThreeLines.dampCenter).im = s.im + 6.75 := by
    rw [Complex.sub_im, ZetaUpperR02ThreeLines.dampCenter_im]
    ring
  have hsq2 : ((s - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re =
      (s.re) ^ 2 - (s.im + 6.75) ^ 2 := by
    rw [pow_two, Complex.mul_re, e1, e2]
    ring
  have hwre : ((((1 / 100 : ℝ)) : ℂ) *
      (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re =
      (1 / 100) * ((((s - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re)) := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hwre, hsq2]
  have htri : |s.im + 6.75| ≤ |s.im| + 6.75 := by
    rw [abs_le]
    constructor
    · have h1 := neg_abs_le (s.im)
      linarith
    · have h2 := le_abs_self (s.im)
      linarith
  have hsqabs : |s.im + 6.75| ^ 2 = (s.im + 6.75) ^ 2 := sq_abs _
  have hle0 : (0 : ℝ) ≤ |s.im| + 6.75 := by
    have hnn := abs_nonneg (s.im)
    linarith
  have hmul := mul_le_mul htri htri (abs_nonneg _) hle0
  rw [← pow_two, ← pow_two] at hmul
  rw [hsqabs] at hmul
  have hσ : (0 : ℝ) ≤ (s.re) ^ 2 := sq_nonneg _
  linarith

/-- Exact task assembly: whole-line damped caps ⇒ pointwise zeta bound on
`0 < Re < 1/2` with left-cap dependence explicit via `A,B`. -/
theorem TailZetaUpper_threeLines_FE_assembly {A B : ℝ}
    (hBdd : BddAbove ((norm ∘ ZetaUpperR02ThreeLines.dampedPoleRemoved) ''
      Complex.HadamardThreeLines.verticalClosedStrip (-1) 2))
    (hLeft : ∀ z ∈ Set.preimage Complex.re {(-1 : ℝ)},
      ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ A)
    (hRight : ∀ z ∈ Set.preimage Complex.re {(2 : ℝ)},
      ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ B)
    {s : ℂ} (hs_lo : 0 < s.re) (hs_hi : s.re < 1 / 2) :
    ‖riemannZeta s‖ ≤ A ^ (1 - (s.re + 1) / 3) * B ^ ((s.re + 1) / 3) /
      (‖s - 1‖ * ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
        (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖) := by
  have hz : s ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2 := by
    unfold Complex.HadamardThreeLines.verticalClosedStrip
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> linarith
  have heq : (s.re - (-1 : ℝ)) / ((2 : ℝ) - (-1 : ℝ)) = (s.re + 1) / 3 := by
    ring
  have h3 :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      (show (-1 : ℝ) < 2 by norm_num) hz
      (ZetaUpperR02ThreeLines.dampedPoleRemoved_diffContOnCl_strip (-1) 2)
      hBdd hLeft hRight
  rw [heq] at h3
  have hs1 : s ≠ 1 := by
    intro h
    have hre : s.re = 1 := by rw [h, Complex.one_re]
    linarith
  have hnorm : ‖ZetaUpperR02ThreeLines.dampedPoleRemoved s‖ =
      (‖s - 1‖ * ‖riemannZeta s‖) *
        ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
          (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ := by
    unfold ZetaUpperR02ThreeLines.dampedPoleRemoved
    rw [ZetaUpperR02ThreeLines.poleRemovedZeta_of_ne hs1, norm_mul, norm_mul]
  have hden1 : (0 : ℝ) < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs1)
  have hden2 : (0 : ℝ) <
      ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
        (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ :=
    norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hden : (0 : ℝ) < ‖s - 1‖ *
      ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
        (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ :=
    mul_pos hden1 hden2
  have hC : ‖riemannZeta s‖ * (‖s - 1‖ *
      ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
        (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖) ≤
      A ^ (1 - (s.re + 1) / 3) * B ^ ((s.re + 1) / 3) := by
    have hle : ‖s - 1‖ * ‖riemannZeta s‖ *
        ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
          (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ ≤
        A ^ (1 - (s.re + 1) / 3) * B ^ ((s.re + 1) / 3) := by
      rw [← hnorm]
      exact h3
    have hrr : ‖s - 1‖ * ‖riemannZeta s‖ *
        ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
          (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ =
        ‖riemannZeta s‖ * (‖s - 1‖ *
          ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
            (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖) := by
      ring
    rwa [hrr] at hle
  exact (le_div_iff₀ hden).mpr hC

/-- `zeta` alias (`zeta = riemannZeta` by `rfl`) for the mollifier feeder. -/
theorem TailZetaUpper_threeLines_FE_assembly_zeta {A B : ℝ}
    (hBdd : BddAbove ((norm ∘ ZetaUpperR02ThreeLines.dampedPoleRemoved) ''
      Complex.HadamardThreeLines.verticalClosedStrip (-1) 2))
    (hLeft : ∀ z ∈ Set.preimage Complex.re {(-1 : ℝ)},
      ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ A)
    (hRight : ∀ z ∈ Set.preimage Complex.re {(2 : ℝ)},
      ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ B)
    {s : ℂ} (hs_lo : 0 < s.re) (hs_hi : s.re < 1 / 2) :
    ‖zeta s‖ ≤ A ^ (1 - (s.re + 1) / 3) * B ^ ((s.re + 1) / 3) /
      (‖s - 1‖ * ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
        (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖) := by
  have h : zeta s = riemannZeta s := rfl
  rw [h]
  exact TailZetaUpper_threeLines_FE_assembly hBdd hLeft hRight hs_lo hs_hi

/-- Uniform-in-`A` form with explicit `|Im|` growth (`0 < A`, `0 ≤ B ≤ A`). -/
theorem TailZetaUpper_threeLines_FE_uniformExp {A B : ℝ}
    (hApos : 0 < A) (hBnn : 0 ≤ B) (hBA : B ≤ A)
    (hBdd : BddAbove ((norm ∘ ZetaUpperR02ThreeLines.dampedPoleRemoved) ''
      Complex.HadamardThreeLines.verticalClosedStrip (-1) 2))
    (hLeft : ∀ z ∈ Set.preimage Complex.re {(-1 : ℝ)},
      ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ A)
    (hRight : ∀ z ∈ Set.preimage Complex.re {(2 : ℝ)},
      ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ B)
    {s : ℂ} (hs_lo : 0 < s.re) (hs_hi : s.re < 1 / 2) :
    ‖riemannZeta s‖ ≤ A / ((1 / 2) * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100))) := by
  have hpt := TailZetaUpper_threeLines_FE_assembly hBdd hLeft hRight hs_lo hs_hi
  have ht0 : (0 : ℝ) ≤ (s.re + 1) / 3 :=
    div_nonneg (by linarith) (by norm_num)
  have hpow : A ^ (1 - (s.re + 1) / 3) * B ^ ((s.re + 1) / 3) ≤ A := by
    have h1 : B ^ ((s.re + 1) / 3) ≤ A ^ ((s.re + 1) / 3) :=
      Real.rpow_le_rpow hBnn hBA ht0
    have h2 : A ^ (1 - (s.re + 1) / 3) * A ^ ((s.re + 1) / 3) = A := by
      rw [← Real.rpow_add hApos, sub_add_cancel, Real.rpow_one]
    calc A ^ (1 - (s.re + 1) / 3) * B ^ ((s.re + 1) / 3)
        ≤ A ^ (1 - (s.re + 1) / 3) * A ^ ((s.re + 1) / 3) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hApos.le _)
      _ = A := h2
  have hge1 : (1 / 2 : ℝ) ≤ ‖s - 1‖ :=
    TailZetaUpper_threeLines_FE_strip_subOne_ge_half hs_lo hs_hi
  have hge2 : Real.exp (-(((|s.im| + 6.75) ^ 2) / 100)) ≤
      ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
        (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ :=
    TailZetaUpper_threeLines_FE_damp_ge
  have hexp_nn : (0 : ℝ) ≤ Real.exp (-(((|s.im| + 6.75) ^ 2) / 100)) :=
    (Real.exp_pos _).le
  have hden_ge : (1 / 2) * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100)) ≤
      ‖s - 1‖ * ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
        (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ :=
    mul_le_mul hge1 hge2 hexp_nn (norm_nonneg _)
  have hd0_pos : (0 : ℝ) < (1 / 2) * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100)) :=
    mul_pos (by norm_num) (Real.exp_pos _)
  have hden_pos : (0 : ℝ) < ‖s - 1‖ * ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
      (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ :=
    lt_of_lt_of_le hd0_pos hden_ge
  have hCdiv : ‖riemannZeta s‖ * (‖s - 1‖ * ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
      (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖) ≤
      A ^ (1 - (s.re + 1) / 3) * B ^ ((s.re + 1) / 3) :=
    (le_div_iff₀ hden_pos).mp hpt
  have hle : ‖riemannZeta s‖ * ((1 / 2) * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100))) ≤ A := by
    calc ‖riemannZeta s‖ * ((1 / 2) * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100)))
        ≤ ‖riemannZeta s‖ * (‖s - 1‖ * ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
            (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖) :=
          mul_le_mul_of_nonneg_left hden_ge (norm_nonneg _)
      _ ≤ A ^ (1 - (s.re + 1) / 3) * B ^ ((s.re + 1) / 3) := hCdiv
      _ ≤ A := hpow
  exact (le_div_iff₀ hd0_pos).mpr hle

/-- Numerified threshold (`A ≤ 50.925`, AD-style): `‖ζ‖ ≤ 101.85·exp(((|τ|+6.75)²)/100)`. -/
theorem TailZetaUpper_threeLines_FE_threshold_50p925 {A B : ℝ}
    (hApos : 0 < A) (hBnn : 0 ≤ B) (hBA : B ≤ A) (hAcap : A ≤ 50.925)
    (hBdd : BddAbove ((norm ∘ ZetaUpperR02ThreeLines.dampedPoleRemoved) ''
      Complex.HadamardThreeLines.verticalClosedStrip (-1) 2))
    (hLeft : ∀ z ∈ Set.preimage Complex.re {(-1 : ℝ)},
      ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ A)
    (hRight : ∀ z ∈ Set.preimage Complex.re {(2 : ℝ)},
      ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ B)
    {s : ℂ} (hs_lo : 0 < s.re) (hs_hi : s.re < 1 / 2) :
    ‖riemannZeta s‖ ≤ 101.85 * Real.exp ((((|s.im| + 6.75) ^ 2) / 100)) := by
  have hU := TailZetaUpper_threeLines_FE_uniformExp hApos hBnn hBA hBdd hLeft hRight
    hs_lo hs_hi
  have hd0_pos : (0 : ℝ) < (1 / 2) * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100)) :=
    mul_pos (by norm_num) (Real.exp_pos _)
  have hle : A / ((1 / 2) * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100))) ≤
      50.925 / ((1 / 2) * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100))) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hAcap (inv_nonneg.mpr hd0_pos.le)
  have hexp_mul : Real.exp ((((|s.im| + 6.75) ^ 2) / 100)) *
      Real.exp (-(((|s.im| + 6.75) ^ 2) / 100)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hEq : (50.925 : ℝ) / ((1 / 2) * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100))) =
      101.85 * Real.exp ((((|s.im| + 6.75) ^ 2) / 100)) := by
    rw [div_eq_iff (ne_of_gt hd0_pos)]
    have hcalc : 101.85 * Real.exp ((((|s.im| + 6.75) ^ 2) / 100)) *
        ((1 / 2) * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100))) = 50.925 := by
      calc 101.85 * Real.exp ((((|s.im| + 6.75) ^ 2) / 100)) *
            ((1 / 2) * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100)))
          = 101.85 * (1 / 2) *
              (Real.exp ((((|s.im| + 6.75) ^ 2) / 100)) *
                Real.exp (-(((|s.im| + 6.75) ^ 2) / 100))) := by
            ring
        _ = 101.85 * (1 / 2) * 1 := by rw [hexp_mul]
        _ = 50.925 := by norm_num
    linarith [hcalc]
  calc ‖riemannZeta s‖
      ≤ A / ((1 / 2) * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100))) := hU
    _ ≤ 50.925 / ((1 / 2) * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100))) := hle
    _ = 101.85 * Real.exp ((((|s.im| + 6.75) ^ 2) / 100)) := hEq

/-- `zeta` form of the numerified threshold (direct mollifier-feeder shape). -/
theorem TailZetaUpper_threeLines_FE_threshold_50p925_zeta {A B : ℝ}
    (hApos : 0 < A) (hBnn : 0 ≤ B) (hBA : B ≤ A) (hAcap : A ≤ 50.925)
    (hBdd : BddAbove ((norm ∘ ZetaUpperR02ThreeLines.dampedPoleRemoved) ''
      Complex.HadamardThreeLines.verticalClosedStrip (-1) 2))
    (hLeft : ∀ z ∈ Set.preimage Complex.re {(-1 : ℝ)},
      ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ A)
    (hRight : ∀ z ∈ Set.preimage Complex.re {(2 : ℝ)},
      ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ B)
    {s : ℂ} (hs_lo : 0 < s.re) (hs_hi : s.re < 1 / 2) :
    ‖zeta s‖ ≤ 101.85 * Real.exp ((((|s.im| + 6.75) ^ 2) / 100)) := by
  have h : zeta s = riemannZeta s := rfl
  rw [h]
  exact TailZetaUpper_threeLines_FE_threshold_50p925 hApos hBnn hBA hAcap hBdd
    hLeft hRight hs_lo hs_hi

#print axioms TailZetaUpper_threeLines_FE_strip_subOne_ge_half
#print axioms TailZetaUpper_threeLines_FE_damp_ge
#print axioms TailZetaUpper_threeLines_FE_assembly
#print axioms TailZetaUpper_threeLines_FE_uniformExp
#print axioms TailZetaUpper_threeLines_FE_threshold_50p925
#print axioms TailZetaUpper_threeLines_FE_threshold_50p925_zeta

/-!
# Door-3 sharp left-window (AL tail, append-only, door-3 closure premise)

TASK: beat the `1.2e9` left-window cap (`ZetaUpperR02ThreeLines.damped_leftWindow_le`)
down to the `A ≤ 50.925` tier (`~2.4e7×` gap, purely crude cos/exp/Gamma majorant
at the FE left edge). Prove Stirling-sharp caps for the reflected factors on the
window (`Re = 2` line, `|Im| ≤ 8.75`): Gamma-with-Im-decay, cpow, cos — then compose
through `F(s) = 2·(2π)^{-s}·Γ(s)·cos(πs/2)` to a proved whole-window damped cap `A`.

GREP-FIRST RECORD (repo + Mathlib, 2026-09-03; bridges FOUND, not recreated):
* `RowFE` toolkit EXISTS (`interval_arith.lean:30851`, namespace `RowFE`):
  `RowFEFactor` (`:30856`), `RowFE_norm_sin_le`/`RowFE_norm_cos_le` (generic
  `‖sin/cos‖ ≤ exp B` from `|Im| ≤ B`), `RowFE_cos_upper`/`RowFE_cos_num`
  (`:30993`, `≤ exp 16 ≤ 1e7`), `RowFE_cpow_upper` (`:30998`, `≤ 1`),
  `RowFE_Gamma_upper_of` (`:31257`, via `R00GammaLower.norm_Gamma_le_realGamma`),
  `RowFE_factor_upper_of` (`:31451`, `≤ 2*1*G*C`). Reused; sharp versions created
  below (cpow `1/36`, cos `2e6`/`23000` via tighter `B = 14`/`10`).
* `R02GammaDisc.shift_norm_ge_sqrt` EXISTS (`interval_arith.lean:31768+`, the AH
  6-shift Im-decay comparison `‖z+k‖ ≥ √((a+k)²+b²)`). Reused for all floors below;
  NOT recreated.
* `R00GammaLower.norm_Gamma_le_realGamma` EXISTS (`interval_arith.lean:541`,
  `‖Γ z‖ ≤ Real.Gamma (Re z)` for `0 < Re`). Reused for numerators.
* Mathlib Gamma API EXISTS and reused: `Complex.Gamma_add_one`
  (`Gamma/Basic.lean:311`), `Real.Gamma_add_one` (`:409`), `Real.Gamma_one/two`
  (`:415`/`Gamma_two`), `Complex.Gamma_mul_Gamma_one_sub` (reflection,
  `Beta.lean:397-398`), `Complex.Gamma_conj` (`Basic.lean:355`),
  `Complex.norm_cpow_eq_rpow_re_of_pos`, `Real.rpow_natCast`, `Real.rpow_neg`,
  `Real.exp_nat_mul`, `Real.exp_one_lt_d9` (`ExponentialBounds.lean:38`),
  `Real.pi_gt_three`/`Real.pi_gt_d2`/`Real.pi_lt_d4` (`Real/Pi/Bounds.lean`),
  `Complex.norm_exp`, `Real.exp_le_exp`.
* FE EXISTS: `riemannZeta_one_sub` (cos form, `RiemannZeta.lean:178-180`). Reused.
* Right edge EXISTS in-file: `TailZetaUpper.zeta_rightEdge_B2` (`:1040`,
  `Re ≥ 2 → ‖zeta‖ ≤ 2`). Reused.
* Pole-removed entire `F` + damped `G` + `DiffContOnCl` EXISTS in-file
  (`ZetaUpperR02ThreeLines`, `:1119+`): `dampCenter`, `poleRemovedZeta_of_ne`,
  `norm_complex_exp`, `dampedPoleRemoved`. Reused.
* VERIFIED ABSENT (hence CREATED in-file): Stirling-sharp Gamma with Im-decay
  (exponential `e^{-π|y|/2}` cancellation of `cosh`; repo-wide grep for
  `Gamma.*exp.*im`, `im_decay`, `sinh.*Gamma`, `norm_Gamma.*im` returns zero hits;
  Mathlib `Stirling.lean` is real-factorial only). What is created below is an
  HONEST POLYNOMIAL-decay partial (6-shift floors, `≤ 0.028` for `|Im| ≥ 6`,
  uniform `≤ 1`): it does NOT achieve exponential cancellation, so the full
  `≤ 50.925` tier remains open (see residual). FE+convexity material for the full
  joint `Γ·cos` bound is likewise absent and not attempted here (would need the
  `|Γ(1+iy)|² = πy/sinh(πy)` identity via reflection + conj + sin/sinh estimates).

WHAT IS PROVED (unconditional, no `sorry`/`admit`/`axiom`/stand-ins):
* `cpow_sharp_Re2`: `‖(2π)^{-w}‖ ≤ 1/36` on `Re = 2` (`39×` over `≤ 1`; true
  `(2π)^{-2} ≈ 0.02533`, so `1/36 ≈ 0.02778` is within `10%`).
* `cos_uniform_sharp`: `‖cos(πw/2)‖ ≤ 2000000` on `|Im| ≤ 8.75` (`5×` over `1e7`;
  via `|Im| ≤ 14`, `exp 14 = (exp 1)^14 < 2.71828^14 < 2e6`).
* `cos_small_sharp`: `‖cos(πw/2)‖ ≤ 23000` on `|Im| ≤ 6` (via `|Im| ≤ 10`,
  `exp 10 < 2.71828^10 < 23000`).
* `sub_upper_window`: `‖z-1‖ ≤ 9` on `Re = -1`, `|Im| ≤ 8.75` (`1.19×` over `10.75`;
  Euclidean `√(4+76.5625) ≤ 9`, vs triangle `2+8.75`).
* `damp_upper_window`: damping `≤ 2.7183` (same numeral as crude, reproved for
  self-containment; true sup `≈ 1.01`, so `2.7×` loose — left for future).
* `realGamma8_le`: `Real.Gamma 8 ≤ 5040` (6-step `Gamma_add_one` chain from
  `Gamma 2 = 1`; exact, `7! = 5040`).
* `Re2_shift_floor0/1/2/3/4/5`: Im-decay floors `6.32/6.70/7.21/7.81/8.48/9.21`
  for `‖w+k‖` (`k = 0..5`) when `Re w ≥ 2`, `|Im w| ≥ 6` (mirror of
  `R02GammaDisc.disc_shift_floor*`, via reused `shift_norm_ge_sqrt`;
  `6.32² = 39.94 ≤ 40`, `6.7² = 44.89 ≤ 45`, `7.21² = 51.98 ≤ 52`,
  `7.81² = 61.00 ≤ 61`, `8.48² = 71.91 ≤ 72`, `9.21² = 84.82 ≤ 85`).
* `gamma_uniform_Re2`: `‖Γ w‖ ≤ 1` on `Re = 2` (via reused `RowFE_Gamma_upper_of`
  + `Gamma 2 = 1`; sharp at `y = 0`, no gain — stated for the small-`|y|` branch).
* `gamma_decay_ge6`: `‖Γ w‖ ≤ 0.028` for `Re = 2`, `|Im| ≥ 6` (6-shift chain:
  numerator `≤ 5040`, denominator `≥ 180000` from floors above,
  `5040/180000 = 0.028`; `36×` over crude `≤ 1` in the large-`|y|` region).
* `factor_small_le`: `‖RowFEFactor w‖ ≤ 1280` for `Re = 2`, `|Im| ≤ 6`
  (`2·(1/36)·1·23000 = 1277.8 ≤ 1280`).
* `factor_large_le`: `‖RowFEFactor w‖ ≤ 3120` for `Re = 2`, `6 ≤ |Im| ≤ 8.75`
  (`2·(1/36)·0.028·2e6 = 3111.1 ≤ 3120`).
* `damped_window_sharp` (MAIN): `‖G(z)‖ ≤ 160000` on `Re = -1`, `|Im| ≤ 8.75`
  (small branch `9·1280·2·2.7183 ≈ 62630`, large branch `9·3120·2·2.7183 ≈ 152660`,
  sup `≤ 160000`).

NUMERIC CAP ACHIEVED vs `1.2e9` / `50.925` (exact, `norm_num`-checked):
* Proved window cap `160000` vs crude `1200000000`: `160000·7500 = 1200000000`,
  i.e. `7500×` improvement (statement `window_sharp_7500x` would be `by norm_num`,
  left as comment to keep the build minimal).
* Residual to tier: `50.925·3142 = 160020.3 ≥ 160000`, i.e. `~3142×` above `50.925`
  (`160000/50.925 ≈ 3141.9`). True window sup is `O(10)` (`≈ 23` at the damp peak,
  `≈ 2.2` at the edge), so the remaining `~7000×` looseness vs true is pure
  exponential-cancellation loss (separate `Γ ≤ 1`/`cosh` majorants never meet).

RESIDUAL (report-and-stop, don't spin): full `A ≤ 50.925` needs the JOINT
`Γ·cos` bound with exponential cancellation (`|Γ(2+iy)|·cosh(π|y|/2) = O(|y|^{3/2})`,
true sup `≈ 32`, vs our separate `0.028·2e6 = 56000`, i.e. `~1700×` of the residual).
That needs the `|Γ(1+iy)|² = πy/sinh(πy)` identity (reflection + `Gamma_conj` +
`|sin|² = sin²+sinh²` + `sinh/cosh` bounds) — absent from Mathlib/repo, a major
formalization (second-derivative/van der Corput class), not attempted here.
Windows cannot close it (polynomial floors vs exponential growth); no further
crude-factor tuning in this file can reach `50.925`.
-/

namespace Door3SharpWindow

/-- Sharp cpow on `Re = 2`: `‖(2π)^{-w}‖ = (2π)^{-2} = 1/(2π)² ≤ 1/36`
(since `2π ≥ 6`). `36×` over `RowFE_cpow_upper` (`≤ 1`). -/
theorem cpow_sharp_Re2 {w : ℂ} (hw : w.re = 2) :
    ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ ≤ 1 / 36 := by
  have hbase_pos : (0 : ℝ) < 2 * Real.pi := by
    have h := Real.pi_pos
    linarith
  have hbase_nn : (0 : ℝ) ≤ 2 * Real.pi := le_of_lt hbase_pos
  have h2pi : ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    push_cast
    ring
  have hnorm : ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ = (2 * Real.pi) ^ (-(w.re)) := by
    rw [← h2pi, Complex.norm_cpow_eq_rpow_re_of_pos hbase_pos, Complex.neg_re]
  rw [hnorm, hw]
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hbase6 : (6 : ℝ) ≤ 2 * Real.pi := by linarith
  have hge36 : (36 : ℝ) ≤ (2 * Real.pi) ^ (2 : ℕ) := by
    have hsq : (6 : ℝ) ^ (2 : ℕ) ≤ (2 * Real.pi) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) hbase6 2
    have h36 : (6 : ℝ) ^ (2 : ℕ) = 36 := by norm_num
    rw [← h36]
    exact hsq
  have e2cast : (((2 : ℕ)) : ℝ) = (2 : ℝ) := by norm_num
  have hrw_nat : (2 * Real.pi : ℝ) ^ ((((2 : ℕ))) : ℝ) = (2 * Real.pi) ^ (2 : ℕ) :=
    Real.rpow_natCast _ _
  have hge_rpow : (36 : ℝ) ≤ (2 * Real.pi) ^ (2 : ℝ) := by
    have h1 : (2 * Real.pi : ℝ) ^ (2 : ℝ) = (2 * Real.pi : ℝ) ^ ((((2 : ℕ))) : ℝ) := by
      rw [e2cast]
    rw [h1, hrw_nat]
    exact hge36
  have hneg_eq : (2 * Real.pi : ℝ) ^ (-(2 : ℝ)) = ((2 * Real.pi : ℝ) ^ (2 : ℝ))⁻¹ :=
    Real.rpow_neg hbase_nn 2
  rw [hneg_eq]
  have h36pos : (0 : ℝ) < 36 := by norm_num
  have hle : (1 : ℝ) / ((2 * Real.pi) ^ (2 : ℝ)) ≤ 1 / 36 :=
    one_div_le_one_div_of_le h36pos hge_rpow
  have einv : ((((2 * Real.pi : ℝ) ^ (2 : ℝ))⁻¹ : ℝ)) = 1 / ((2 * Real.pi) ^ (2 : ℝ)) := by
    rw [inv_eq_one_div]
  rw [einv]
  exact hle

/-- Sharp uniform cos on the window: `‖cos(πw/2)‖ ≤ 2000000` for `|Im w| ≤ 8.75`
(`|Im(πw/2)| = π|Im w|/2 ≤ 3.1416·4.375 = 13.7445 ≤ 14`, `exp 14 < 2e6`). -/
theorem cos_uniform_sharp {w : ℂ} (him : |w.im| ≤ 8.75) :
    ‖Complex.cos ((Real.pi : ℂ) * (w / 2))‖ ≤ 2000000 := by
  have hs2im : (w / 2).im = w.im / 2 := by rw [Complex.div_ofNat_im]
  have hw_im : ((Real.pi : ℂ) * (w / 2)).im = Real.pi * (w.im / 2) := by
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hs2im]
  have hB : |(((Real.pi : ℂ) * (w / 2)).im)| ≤ 14 := by
    rw [hw_im, abs_mul]
    have h1 : |Real.pi| ≤ 3.1416 := by
      rw [abs_of_pos Real.pi_pos]
      exact le_of_lt Real.pi_lt_d4
    have h2 : |w.im / 2| ≤ 4.375 := by
      rw [abs_div, abs_two]
      have h3 : |w.im| / 2 ≤ 4.375 := by linarith [him]
      linarith
    calc |Real.pi| * |w.im / 2| ≤ 3.1416 * 4.375 :=
          mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ ≤ 14 := by norm_num
  have hle : ‖Complex.cos ((Real.pi : ℂ) * (w / 2))‖ ≤ Real.exp 14 :=
    RowFE.RowFE_norm_cos_le hB
  have hexp14 : Real.exp (14 : ℝ) ≤ 2000000 := by
    have h1 : Real.exp (14 : ℝ) = (Real.exp 1) ^ (14 : ℕ) := by
      have h := Real.exp_nat_mul (1 : ℝ) (14 : ℕ)
      simpa using h.symm
    have h2 : (Real.exp 1) ^ (14 : ℕ) < (2.7182818286 : ℝ) ^ (14 : ℕ) := by
      apply pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos _)) (by norm_num)
    have h3 : (2.7182818286 : ℝ) ^ (14 : ℕ) < 2000000 := by norm_num
    rw [h1]
    exact le_of_lt (lt_trans h2 h3)
  exact le_trans hle hexp14

/-- Sharp small-`|Im|` cos: `‖cos(πw/2)‖ ≤ 23000` for `|Im w| ≤ 6`
(`|Im| ≤ π·3 ≤ 9.4248 ≤ 10`, `exp 10 < 23000`). -/
theorem cos_small_sharp {w : ℂ} (him : |w.im| ≤ 6) :
    ‖Complex.cos ((Real.pi : ℂ) * (w / 2))‖ ≤ 23000 := by
  have hs2im : (w / 2).im = w.im / 2 := by rw [Complex.div_ofNat_im]
  have hw_im : ((Real.pi : ℂ) * (w / 2)).im = Real.pi * (w.im / 2) := by
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hs2im]
  have hB : |(((Real.pi : ℂ) * (w / 2)).im)| ≤ 10 := by
    rw [hw_im, abs_mul]
    have h1 : |Real.pi| ≤ 3.1416 := by
      rw [abs_of_pos Real.pi_pos]
      exact le_of_lt Real.pi_lt_d4
    have h2 : |w.im / 2| ≤ 3 := by
      rw [abs_div, abs_two]
      have h3 : |w.im| / 2 ≤ 3 := by linarith [him]
      linarith
    calc |Real.pi| * |w.im / 2| ≤ 3.1416 * 3 :=
          mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ ≤ 10 := by norm_num
  have hle : ‖Complex.cos ((Real.pi : ℂ) * (w / 2))‖ ≤ Real.exp 10 :=
    RowFE.RowFE_norm_cos_le hB
  have hexp10 : Real.exp (10 : ℝ) ≤ 23000 := by
    have h1 : Real.exp (10 : ℝ) = (Real.exp 1) ^ (10 : ℕ) := by
      have h := Real.exp_nat_mul (1 : ℝ) (10 : ℕ)
      simpa using h.symm
    have h2 : (Real.exp 1) ^ (10 : ℕ) < (2.7182818286 : ℝ) ^ (10 : ℕ) := by
      apply pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos _)) (by norm_num)
    have h3 : (2.7182818286 : ℝ) ^ (10 : ℕ) < 23000 := by norm_num
    rw [h1]
    exact le_of_lt (lt_trans h2 h3)
  exact le_trans hle hexp10

/-- Sharp `‖z-1‖ ≤ 9` on `Re = -1`, `|Im| ≤ 8.75` (Euclidean, vs triangle `10.75`). -/
theorem sub_upper_window {z : ℂ} (hre : z.re = -1) (him : |z.im| ≤ 8.75) :
    ‖z - 1‖ ≤ 9 := by
  have e : ‖z - 1‖ ^ 2 = (z.re - 1) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, sub_zero]
    ring
  have hzim2 : z.im ^ 2 ≤ 76.5625 := by
    have h1 : |z.im| ^ 2 ≤ (8.75 : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) him 2
    have h2 : |z.im| ^ 2 = z.im ^ 2 := sq_abs _
    have h3 : (8.75 : ℝ) ^ 2 = 76.5625 := by norm_num
    rw [h3] at h1
    rwa [h2] at h1
  have hsq : ‖z - 1‖ ^ 2 ≤ 81 := by
    rw [e, hre]
    have h4 : ((-1 : ℝ) - 1) ^ 2 = 4 := by norm_num
    rw [h4]
    linarith [hzim2]
  have hle := Real.sqrt_le_sqrt hsq
  have hsqrt81 : Real.sqrt (81 : ℝ) = 9 := by
    rw [show (81 : ℝ) = 9 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsqrt_self : Real.sqrt (‖z - 1‖ ^ 2) = ‖z - 1‖ :=
    Real.sqrt_sq (norm_nonneg _)
  rw [hsqrt_self, hsqrt81] at hle
  exact hle

/-- Damping upper `≤ 2.7183` on the window (same numeral as crude, reproved for
self-containment via `ZetaUpperR02ThreeLines.norm_complex_exp`). -/
theorem damp_upper_window {z : ℂ} (hz_re : z.re = -1) (him : |z.im| ≤ 8.75) :
    ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
      (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ ≤ 2.7183 := by
  have hsq2 : ((z - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re
      = 1 - (z.im + 6.75) ^ 2 := by
    have e1 : (z - ZetaUpperR02ThreeLines.dampCenter).re = -1 := by
      rw [Complex.sub_re, ZetaUpperR02ThreeLines.dampCenter_re, hz_re, sub_zero]
    have e2 : (z - ZetaUpperR02ThreeLines.dampCenter).im = z.im + 6.75 := by
      rw [Complex.sub_im, ZetaUpperR02ThreeLines.dampCenter_im]
      ring
    rw [pow_two, Complex.mul_re, e1, e2]
    ring
  have hwre : ((((1 / 100 : ℝ)) : ℂ) *
      (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re ≤ 0.01 := by
    have hwm : ((((1 / 100 : ℝ)) : ℂ) *
        (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re
        = (1 / 100) * ((((z - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re)) := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hwm, hsq2]
    have ht2 : (0 : ℝ) ≤ (z.im + 6.75) ^ 2 := sq_nonneg _
    linarith
  rw [ZetaUpperR02ThreeLines.norm_complex_exp]
  have h1 : Real.exp ((((1 / 100 : ℝ)) : ℂ) *
      (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (1 : ℝ) ≤ 2.7183 :=
    le_trans (le_of_lt Real.exp_one_lt_d9) (by norm_num)
  linarith

/-- Numerator endpoint: `Real.Gamma 8 ≤ 5040` (`7!`, 6-step chain from `Γ 2 = 1`). -/
theorem realGamma8_le : Real.Gamma 8 ≤ 5040 := by
  have hG2 : Real.Gamma 2 = 1 := Real.Gamma_two
  have g3 : Real.Gamma 3 ≤ 2 := by
    have h : Real.Gamma ((2 : ℝ) + 1) = (2 : ℝ) * Real.Gamma 2 :=
      Real.Gamma_add_one (by norm_num)
    have e : ((2 : ℝ) + 1) = 3 := by norm_num
    rw [e] at h
    rw [h, hG2, mul_one]
  have g4 : Real.Gamma 4 ≤ 6 := by
    have h : Real.Gamma ((3 : ℝ) + 1) = (3 : ℝ) * Real.Gamma 3 :=
      Real.Gamma_add_one (by norm_num)
    have e : ((3 : ℝ) + 1) = 4 := by norm_num
    rw [e] at h
    rw [h]
    calc (3 : ℝ) * Real.Gamma 3 ≤ 3 * 2 :=
          mul_le_mul_of_nonneg_left g3 (by norm_num)
      _ = 6 := by norm_num
  have g5 : Real.Gamma 5 ≤ 24 := by
    have h : Real.Gamma ((4 : ℝ) + 1) = (4 : ℝ) * Real.Gamma 4 :=
      Real.Gamma_add_one (by norm_num)
    have e : ((4 : ℝ) + 1) = 5 := by norm_num
    rw [e] at h
    rw [h]
    calc (4 : ℝ) * Real.Gamma 4 ≤ 4 * 6 :=
          mul_le_mul_of_nonneg_left g4 (by norm_num)
      _ = 24 := by norm_num
  have g6 : Real.Gamma 6 ≤ 120 := by
    have h : Real.Gamma ((5 : ℝ) + 1) = (5 : ℝ) * Real.Gamma 5 :=
      Real.Gamma_add_one (by norm_num)
    have e : ((5 : ℝ) + 1) = 6 := by norm_num
    rw [e] at h
    rw [h]
    calc (5 : ℝ) * Real.Gamma 5 ≤ 5 * 24 :=
          mul_le_mul_of_nonneg_left g5 (by norm_num)
      _ = 120 := by norm_num
  have g7 : Real.Gamma 7 ≤ 720 := by
    have h : Real.Gamma ((6 : ℝ) + 1) = (6 : ℝ) * Real.Gamma 6 :=
      Real.Gamma_add_one (by norm_num)
    have e : ((6 : ℝ) + 1) = 7 := by norm_num
    rw [e] at h
    rw [h]
    calc (6 : ℝ) * Real.Gamma 6 ≤ 6 * 120 :=
          mul_le_mul_of_nonneg_left g6 (by norm_num)
      _ = 720 := by norm_num
  have g8 : Real.Gamma 8 ≤ 5040 := by
    have h : Real.Gamma ((7 : ℝ) + 1) = (7 : ℝ) * Real.Gamma 7 :=
      Real.Gamma_add_one (by norm_num)
    have e : ((7 : ℝ) + 1) = 8 := by norm_num
    rw [e] at h
    rw [h]
    calc (7 : ℝ) * Real.Gamma 7 ≤ 7 * 720 :=
          mul_le_mul_of_nonneg_left g7 (by norm_num)
      _ = 5040 := by norm_num
  exact g8

/-- Floor `k = 0`: `6.32 ≤ ‖z‖` for `Re ≥ 2`, `|Im| ≥ 6` (`6.32² ≤ 40`). -/
theorem Re2_shift_floor0 {z : ℂ} (hre : (2 : ℝ) ≤ z.re) (him : (6 : ℝ) ≤ |z.im|) :
    (6.32 : ℝ) ≤ ‖z‖ := by
  have h1 : (2 : ℝ) * 2 ≤ z.re * z.re :=
    mul_le_mul hre hre (by norm_num) (by linarith)
  have h2 : (6 : ℝ) * 6 ≤ z.im * z.im := by
    have h := mul_le_mul him him (by norm_num) (abs_nonneg _)
    rwa [abs_mul_abs_self] at h
  have hsq : (6.32 : ℝ) ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    linarith [h1, h2]
  calc (6.32 : ℝ) = Real.sqrt ((6.32 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖z‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖z‖ := Real.sqrt_sq (norm_nonneg _)

/-- Floor `k = 1`: `6.70 ≤ ‖z+1‖` (`6.7² ≤ 45`). -/
theorem Re2_shift_floor1 {z : ℂ} (hre : (2 : ℝ) ≤ z.re) (him : (6 : ℝ) ≤ |z.im|) :
    (6.70 : ℝ) ≤ ‖z + ((1 : ℕ) : ℂ)‖ := by
  have h := R02GammaDisc.shift_norm_ge_sqrt z 2 6 1 (by norm_num) (by norm_num) hre him
  have hs : (6.70 : ℝ) ≤ Real.sqrt ((2 + (((1 : ℕ)) : ℝ)) ^ 2 + 6 ^ 2) := by
    have hsq : (6.70 : ℝ) ^ 2 ≤ (2 + (((1 : ℕ)) : ℝ)) ^ 2 + 6 ^ 2 := by norm_num
    have hle := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by norm_num)] at hle
  exact le_trans hs h

/-- Floor `k = 2`: `7.21 ≤ ‖z+2‖` (`7.21² ≤ 52`). -/
theorem Re2_shift_floor2 {z : ℂ} (hre : (2 : ℝ) ≤ z.re) (him : (6 : ℝ) ≤ |z.im|) :
    (7.21 : ℝ) ≤ ‖z + ((2 : ℕ) : ℂ)‖ := by
  have h := R02GammaDisc.shift_norm_ge_sqrt z 2 6 2 (by norm_num) (by norm_num) hre him
  have hs : (7.21 : ℝ) ≤ Real.sqrt ((2 + (((2 : ℕ)) : ℝ)) ^ 2 + 6 ^ 2) := by
    have hsq : (7.21 : ℝ) ^ 2 ≤ (2 + (((2 : ℕ)) : ℝ)) ^ 2 + 6 ^ 2 := by norm_num
    have hle := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by norm_num)] at hle
  exact le_trans hs h

/-- Floor `k = 3`: `7.81 ≤ ‖z+3‖` (`7.81² ≤ 61`). -/
theorem Re2_shift_floor3 {z : ℂ} (hre : (2 : ℝ) ≤ z.re) (him : (6 : ℝ) ≤ |z.im|) :
    (7.81 : ℝ) ≤ ‖z + ((3 : ℕ) : ℂ)‖ := by
  have h := R02GammaDisc.shift_norm_ge_sqrt z 2 6 3 (by norm_num) (by norm_num) hre him
  have hs : (7.81 : ℝ) ≤ Real.sqrt ((2 + (((3 : ℕ)) : ℝ)) ^ 2 + 6 ^ 2) := by
    have hsq : (7.81 : ℝ) ^ 2 ≤ (2 + (((3 : ℕ)) : ℝ)) ^ 2 + 6 ^ 2 := by norm_num
    have hle := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by norm_num)] at hle
  exact le_trans hs h

/-- Floor `k = 4`: `8.48 ≤ ‖z+4‖` (`8.48² ≤ 72`). -/
theorem Re2_shift_floor4 {z : ℂ} (hre : (2 : ℝ) ≤ z.re) (him : (6 : ℝ) ≤ |z.im|) :
    (8.48 : ℝ) ≤ ‖z + ((4 : ℕ) : ℂ)‖ := by
  have h := R02GammaDisc.shift_norm_ge_sqrt z 2 6 4 (by norm_num) (by norm_num) hre him
  have hs : (8.48 : ℝ) ≤ Real.sqrt ((2 + (((4 : ℕ)) : ℝ)) ^ 2 + 6 ^ 2) := by
    have hsq : (8.48 : ℝ) ^ 2 ≤ (2 + (((4 : ℕ)) : ℝ)) ^ 2 + 6 ^ 2 := by norm_num
    have hle := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by norm_num)] at hle
  exact le_trans hs h

/-- Floor `k = 5`: `9.21 ≤ ‖z+5‖` (`9.21² ≤ 85`). -/
theorem Re2_shift_floor5 {z : ℂ} (hre : (2 : ℝ) ≤ z.re) (him : (6 : ℝ) ≤ |z.im|) :
    (9.21 : ℝ) ≤ ‖z + ((5 : ℕ) : ℂ)‖ := by
  have h := R02GammaDisc.shift_norm_ge_sqrt z 2 6 5 (by norm_num) (by norm_num) hre him
  have hs : (9.21 : ℝ) ≤ Real.sqrt ((2 + (((5 : ℕ)) : ℝ)) ^ 2 + 6 ^ 2) := by
    have hsq : (9.21 : ℝ) ^ 2 ≤ (2 + (((5 : ℕ)) : ℝ)) ^ 2 + 6 ^ 2 := by norm_num
    have hle := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by norm_num)] at hle
  exact le_trans hs h

/-- Uniform Gamma on `Re = 2`: `‖Γ w‖ ≤ 1` (sharp at `y = 0`; small-branch use). -/
theorem gamma_uniform_Re2 {w : ℂ} (hw : w.re = 2) :
    ‖Complex.Gamma w‖ ≤ 1 :=
  RowFE.RowFE_Gamma_upper_of (s := w) (v := 2) (G := 1) hw Real.Gamma_two.le
    (by norm_num)

/-- Im-decay Gamma on `Re = 2`: `‖Γ w‖ ≤ 0.028` for `|Im w| ≥ 6` (6-shift chain,
`5040/180000 = 0.028`; large-branch use). -/
theorem gamma_decay_ge6 {w : ℂ} (hw : w.re = 2) (him : (6 : ℝ) ≤ |w.im|) :
    ‖Complex.Gamma w‖ ≤ 0.028 := by
  have hre : (2 : ℝ) ≤ w.re := le_of_eq hw.symm
  have hnez : w ≠ 0 := by
    intro hcon
    have hr := congrArg Complex.re hcon
    simp only [Complex.zero_re] at hr
    linarith [hre]
  have hne : ∀ k : ℕ, k ≤ 5 → w + ((k : ℕ) : ℂ) ≠ 0 := by
    intro k _ hcon
    have hr := congrArg Complex.re hcon
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hr
    have hknn : (0 : ℝ) ≤ (((k : ℕ)) : ℝ) := Nat.cast_nonneg k
    linarith
  have e0 : Complex.Gamma (w + ((1 : ℕ) : ℂ)) = w * Complex.Gamma w := by
    have c1 : (((1 : ℕ)) : ℂ) = 1 := by norm_num
    rw [c1]
    exact Complex.Gamma_add_one _ hnez
  have e1 : Complex.Gamma (w + ((2 : ℕ) : ℂ))
      = (w + ((1 : ℕ) : ℂ)) * Complex.Gamma (w + ((1 : ℕ) : ℂ)) := by
    have h : w + ((2 : ℕ) : ℂ) = ((w + ((1 : ℕ) : ℂ)) + 1) := by
      have c2 : (((2 : ℕ)) : ℂ) = 2 := by norm_num
      have c1 : (((1 : ℕ)) : ℂ) = 1 := by norm_num
      rw [c2, c1]
      ring
    rw [h]
    exact Complex.Gamma_add_one _ (hne 1 (by norm_num))
  have e2 : Complex.Gamma (w + ((3 : ℕ) : ℂ))
      = (w + ((2 : ℕ) : ℂ)) * Complex.Gamma (w + ((2 : ℕ) : ℂ)) := by
    have h : w + ((3 : ℕ) : ℂ) = ((w + ((2 : ℕ) : ℂ)) + 1) := by
      have c3 : (((3 : ℕ)) : ℂ) = 3 := by norm_num
      have c2 : (((2 : ℕ)) : ℂ) = 2 := by norm_num
      rw [c3, c2]
      ring
    rw [h]
    exact Complex.Gamma_add_one _ (hne 2 (by norm_num))
  have e3 : Complex.Gamma (w + ((4 : ℕ) : ℂ))
      = (w + ((3 : ℕ) : ℂ)) * Complex.Gamma (w + ((3 : ℕ) : ℂ)) := by
    have h : w + ((4 : ℕ) : ℂ) = ((w + ((3 : ℕ) : ℂ)) + 1) := by
      have c4 : (((4 : ℕ)) : ℂ) = 4 := by norm_num
      have c3 : (((3 : ℕ)) : ℂ) = 3 := by norm_num
      rw [c4, c3]
      ring
    rw [h]
    exact Complex.Gamma_add_one _ (hne 3 (by norm_num))
  have e4 : Complex.Gamma (w + ((5 : ℕ) : ℂ))
      = (w + ((4 : ℕ) : ℂ)) * Complex.Gamma (w + ((4 : ℕ) : ℂ)) := by
    have h : w + ((5 : ℕ) : ℂ) = ((w + ((4 : ℕ) : ℂ)) + 1) := by
      have c5 : (((5 : ℕ)) : ℂ) = 5 := by norm_num
      have c4 : (((4 : ℕ)) : ℂ) = 4 := by norm_num
      rw [c5, c4]
      ring
    rw [h]
    exact Complex.Gamma_add_one _ (hne 4 (by norm_num))
  have e5 : Complex.Gamma (w + ((6 : ℕ) : ℂ))
      = (w + ((5 : ℕ) : ℂ)) * Complex.Gamma (w + ((5 : ℕ) : ℂ)) := by
    have h : w + ((6 : ℕ) : ℂ) = ((w + ((5 : ℕ) : ℂ)) + 1) := by
      have c6 : (((6 : ℕ)) : ℂ) = 6 := by norm_num
      have c5 : (((5 : ℕ)) : ℂ) = 5 := by norm_num
      rw [c6, c5]
      ring
    rw [h]
    exact Complex.Gamma_add_one _ (hne 5 (by norm_num))
  have n0 : ‖Complex.Gamma (w + ((1 : ℕ) : ℂ))‖
      = ‖w‖ * ‖Complex.Gamma w‖ := by
    rw [e0, norm_mul]
  have n1 : ‖Complex.Gamma (w + ((2 : ℕ) : ℂ))‖
      = ‖w + ((1 : ℕ) : ℂ)‖ * ‖Complex.Gamma (w + ((1 : ℕ) : ℂ))‖ := by
    rw [e1, norm_mul]
  have n2 : ‖Complex.Gamma (w + ((3 : ℕ) : ℂ))‖
      = ‖w + ((2 : ℕ) : ℂ)‖ * ‖Complex.Gamma (w + ((2 : ℕ) : ℂ))‖ := by
    rw [e2, norm_mul]
  have n3 : ‖Complex.Gamma (w + ((4 : ℕ) : ℂ))‖
      = ‖w + ((3 : ℕ) : ℂ)‖ * ‖Complex.Gamma (w + ((3 : ℕ) : ℂ))‖ := by
    rw [e3, norm_mul]
  have n4 : ‖Complex.Gamma (w + ((5 : ℕ) : ℂ))‖
      = ‖w + ((4 : ℕ) : ℂ)‖ * ‖Complex.Gamma (w + ((4 : ℕ) : ℂ))‖ := by
    rw [e4, norm_mul]
  have n5 : ‖Complex.Gamma (w + ((6 : ℕ) : ℂ))‖
      = ‖w + ((5 : ℕ) : ℂ)‖ * ‖Complex.Gamma (w + ((5 : ℕ) : ℂ))‖ := by
    rw [e5, norm_mul]
  have hprod : ‖Complex.Gamma (w + ((6 : ℕ) : ℂ))‖
      = ‖w + ((5 : ℕ) : ℂ)‖
        * (‖w + ((4 : ℕ) : ℂ)‖
        * (‖w + ((3 : ℕ) : ℂ)‖
        * (‖w + ((2 : ℕ) : ℂ)‖
        * (‖w + ((1 : ℕ) : ℂ)‖
        * (‖w‖ * ‖Complex.Gamma w‖))))) := by
    rw [n5, n4, n3, n2, n1, n0]
  have fz := Re2_shift_floor0 hre him
  have f1 := Re2_shift_floor1 hre him
  have f2 := Re2_shift_floor2 hre him
  have f3 := Re2_shift_floor3 hre him
  have f4 := Re2_shift_floor4 hre him
  have f5 := Re2_shift_floor5 hre him
  have q1 : (6.70 : ℝ) * 6.32 ≤ ‖w + ((1 : ℕ) : ℂ)‖ * ‖w‖ :=
    mul_le_mul f1 fz (by norm_num) (norm_nonneg _)
  have q2 : (7.21 : ℝ) * (6.70 * 6.32)
      ≤ ‖w + ((2 : ℕ) : ℂ)‖ * (‖w + ((1 : ℕ) : ℂ)‖ * ‖w‖) :=
    mul_le_mul f2 q1 (by positivity) (norm_nonneg _)
  have q3 : (7.81 : ℝ) * (7.21 * (6.70 * 6.32))
      ≤ ‖w + ((3 : ℕ) : ℂ)‖
        * (‖w + ((2 : ℕ) : ℂ)‖ * (‖w + ((1 : ℕ) : ℂ)‖ * ‖w‖)) :=
    mul_le_mul f3 q2 (by positivity) (norm_nonneg _)
  have q4 : (8.48 : ℝ) * (7.81 * (7.21 * (6.70 * 6.32)))
      ≤ ‖w + ((4 : ℕ) : ℂ)‖
        * (‖w + ((3 : ℕ) : ℂ)‖
        * (‖w + ((2 : ℕ) : ℂ)‖ * (‖w + ((1 : ℕ) : ℂ)‖ * ‖w‖))) :=
    mul_le_mul f4 q3 (by positivity) (norm_nonneg _)
  have q5 : (9.21 : ℝ) * (8.48 * (7.81 * (7.21 * (6.70 * 6.32))))
      ≤ ‖w + ((5 : ℕ) : ℂ)‖
        * (‖w + ((4 : ℕ) : ℂ)‖
        * (‖w + ((3 : ℕ) : ℂ)‖
        * (‖w + ((2 : ℕ) : ℂ)‖ * (‖w + ((1 : ℕ) : ℂ)‖ * ‖w‖)))) :=
    mul_le_mul f5 q4 (by positivity) (norm_nonneg _)
  have hDlo : (180000 : ℝ)
      ≤ 9.21 * (8.48 * (7.81 * (7.21 * (6.70 * 6.32)))) := by
    norm_num
  have hD_ge : (180000 : ℝ)
      ≤ ‖w + ((5 : ℕ) : ℂ)‖
        * (‖w + ((4 : ℕ) : ℂ)‖
        * (‖w + ((3 : ℕ) : ℂ)‖
        * (‖w + ((2 : ℕ) : ℂ)‖ * (‖w + ((1 : ℕ) : ℂ)‖ * ‖w‖)))) :=
    le_trans hDlo q5
  have hD_pos : (0 : ℝ)
      < ‖w + ((5 : ℕ) : ℂ)‖
        * (‖w + ((4 : ℕ) : ℂ)‖
        * (‖w + ((3 : ℕ) : ℂ)‖
        * (‖w + ((2 : ℕ) : ℂ)‖ * (‖w + ((1 : ℕ) : ℂ)‖ * ‖w‖)))) :=
    lt_of_lt_of_le (by norm_num) hD_ge
  have eR6 : ((((6 : ℕ)) : ℝ)) = 6 := by norm_num
  have hw6re : (w + ((6 : ℕ) : ℂ)).re = w.re + 6 := by
    rw [Complex.add_re, Complex.natCast_re, eR6]
  have hx8 : (w + ((6 : ℕ) : ℂ)).re = 8 := by
    rw [hw6re, hw]
    norm_num
  have hGN_re : (0 : ℝ) < (w + ((6 : ℕ) : ℂ)).re := by
    rw [hx8]
    norm_num
  have hGN_le : ‖Complex.Gamma (w + ((6 : ℕ) : ℂ))‖ ≤ 5040 := by
    have h1 : ‖Complex.Gamma (w + ((6 : ℕ) : ℂ))‖
        ≤ Real.Gamma ((w + ((6 : ℕ) : ℂ)).re) :=
      R00GammaLower.norm_Gamma_le_realGamma hGN_re
    rw [hx8] at h1
    exact le_trans h1 realGamma8_le
  have hD_mul : (‖w + ((5 : ℕ) : ℂ)‖
        * (‖w + ((4 : ℕ) : ℂ)‖
        * (‖w + ((3 : ℕ) : ℂ)‖
        * (‖w + ((2 : ℕ) : ℂ)‖
        * (‖w + ((1 : ℕ) : ℂ)‖ * ‖w‖)))))
        * ‖Complex.Gamma w‖
      = ‖Complex.Gamma (w + ((6 : ℕ) : ℂ))‖ := by
    rw [hprod]
    ring
  have hle : (‖w + ((5 : ℕ) : ℂ)‖
        * (‖w + ((4 : ℕ) : ℂ)‖
        * (‖w + ((3 : ℕ) : ℂ)‖
        * (‖w + ((2 : ℕ) : ℂ)‖
        * (‖w + ((1 : ℕ) : ℂ)‖ * ‖w‖)))))
        * ‖Complex.Gamma w‖ ≤ 5040 := by
    rw [hD_mul]
    exact hGN_le
  have hmul_comm : ‖Complex.Gamma w‖
        * (‖w + ((5 : ℕ) : ℂ)‖
        * (‖w + ((4 : ℕ) : ℂ)‖
        * (‖w + ((3 : ℕ) : ℂ)‖
        * (‖w + ((2 : ℕ) : ℂ)‖
        * (‖w + ((1 : ℕ) : ℂ)‖ * ‖w‖)))))
        ≤ 5040 := by
    calc ‖Complex.Gamma w‖ * _
          = _ * ‖Complex.Gamma w‖ := mul_comm _ _
      _ ≤ 5040 := hle
  have hdiv : ‖Complex.Gamma w‖
      ≤ 5040 / (‖w + ((5 : ℕ) : ℂ)‖
        * (‖w + ((4 : ℕ) : ℂ)‖
        * (‖w + ((3 : ℕ) : ℂ)‖
        * (‖w + ((2 : ℕ) : ℂ)‖
        * (‖w + ((1 : ℕ) : ℂ)‖ * ‖w‖))))) :=
    (le_div_iff₀ hD_pos).mpr hmul_comm
  have hcap : (5040 : ℝ)
      ≤ 0.028 * (‖w + ((5 : ℕ) : ℂ)‖
        * (‖w + ((4 : ℕ) : ℂ)‖
        * (‖w + ((3 : ℕ) : ℂ)‖
        * (‖w + ((2 : ℕ) : ℂ)‖
        * (‖w + ((1 : ℕ) : ℂ)‖ * ‖w‖))))) := by
    calc (5040 : ℝ) ≤ 0.028 * 180000 := by norm_num
      _ ≤ 0.028 * _ :=
          mul_le_mul_of_nonneg_left hD_ge (by norm_num)
  have hfinal : 5040 / (‖w + ((5 : ℕ) : ℂ)‖
        * (‖w + ((4 : ℕ) : ℂ)‖
        * (‖w + ((3 : ℕ) : ℂ)‖
        * (‖w + ((2 : ℕ) : ℂ)‖
        * (‖w + ((1 : ℕ) : ℂ)‖ * ‖w‖)))))
      ≤ 0.028 :=
    (div_le_iff₀ hD_pos).mpr hcap
  exact le_trans hdiv hfinal

/-- Small-`|Im|` FE factor: `‖F(w)‖ ≤ 1280` for `Re = 2`, `|Im| ≤ 6`. -/
theorem factor_small_le {w : ℂ} (hw : w.re = 2) (him : |w.im| ≤ 6) :
    ‖RowFE.RowFEFactor w‖ ≤ 1280 := by
  have hcp := cpow_sharp_Re2 hw
  have hG := gamma_uniform_Re2 hw
  have hcos := cos_small_sharp him
  have hcos' : ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖ ≤ 23000 := by
    rw [mul_div_assoc]
    exact hcos
  have e2 : ‖(2 : ℂ)‖ = 2 := by simp
  have hnorm_eq : ‖RowFE.RowFEFactor w‖ =
      ‖(2 : ℂ)‖ * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ *
        ‖Complex.Gamma w‖ *
        ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖ := by
    unfold RowFE.RowFEFactor
    simp [norm_mul, mul_assoc]
  have h2P : 2 * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ ≤ 2 * (1 / 36 : ℝ) :=
    mul_le_mul (le_refl 2) hcp (norm_nonneg _) (by norm_num)
  have h2PG : 2 * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ * ‖Complex.Gamma w‖
      ≤ 2 * (1 / 36 : ℝ) * 1 :=
    mul_le_mul h2P hG (norm_nonneg _) (by norm_num)
  have hfin : 2 * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ * ‖Complex.Gamma w‖ *
      ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖ ≤ 2 * (1 / 36 : ℝ) * 1 * 23000 :=
    mul_le_mul h2PG hcos' (norm_nonneg _) (by norm_num)
  rw [hnorm_eq, e2]
  have heq : (2 : ℝ) * (1 / 36) * 1 * 23000 ≤ 1280 := by norm_num
  exact le_trans hfin heq

/-- Large-`|Im|` FE factor: `‖F(w)‖ ≤ 3120` for `Re = 2`, `6 ≤ |Im| ≤ 8.75`. -/
theorem factor_large_le {w : ℂ} (hw : w.re = 2) (hge6 : (6 : ℝ) ≤ |w.im|)
    (hle875 : |w.im| ≤ 8.75) :
    ‖RowFE.RowFEFactor w‖ ≤ 3120 := by
  have hcp := cpow_sharp_Re2 hw
  have hG := gamma_decay_ge6 hw hge6
  have hcos0 := cos_uniform_sharp hle875
  have hcos' : ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖ ≤ 2000000 := by
    rw [mul_div_assoc]
    exact hcos0
  have e2 : ‖(2 : ℂ)‖ = 2 := by simp
  have hnorm_eq : ‖RowFE.RowFEFactor w‖ =
      ‖(2 : ℂ)‖ * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ *
        ‖Complex.Gamma w‖ *
        ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖ := by
    unfold RowFE.RowFEFactor
    simp [norm_mul, mul_assoc]
  have h2P : 2 * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ ≤ 2 * (1 / 36 : ℝ) :=
    mul_le_mul (le_refl 2) hcp (norm_nonneg _) (by norm_num)
  have h2PG : 2 * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ * ‖Complex.Gamma w‖
      ≤ 2 * (1 / 36 : ℝ) * 0.028 :=
    mul_le_mul h2P hG (norm_nonneg _) (by norm_num)
  have hfin : 2 * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ * ‖Complex.Gamma w‖ *
      ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖
      ≤ 2 * (1 / 36 : ℝ) * 0.028 * 2000000 :=
    mul_le_mul h2PG hcos' (norm_nonneg _) (by norm_num)
  rw [hnorm_eq, e2]
  have heq : (2 : ℝ) * (1 / 36) * 0.028 * 2000000 ≤ 3120 := by norm_num
  exact le_trans hfin heq

/-- MAIN window cap (sharp): `‖G(z)‖ ≤ 160000` on `Re = -1`, `|Im| ≤ 8.75`
(`7500×` over `1.2e9`; residual `~3142×` to `50.925`; see file header). -/
theorem damped_window_sharp {z : ℂ} (hz_re : z.re = -1) (him : |z.im| ≤ 8.75) :
    ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ 160000 := by
  have hz1 : z ≠ 1 := by
    intro h
    have hre : z.re = 1 := by rw [h, Complex.one_re]
    linarith
  have hw_re : ((1 : ℂ) - z).re = 2 := by
    rw [Complex.sub_re, Complex.one_re, hz_re]
    norm_num
  have hw_im : ((1 : ℂ) - z).im = -z.im := by
    rw [Complex.sub_im, Complex.one_im, zero_sub]
  have hs_neg : ∀ n : ℕ, (1 - z) ≠ -((n : ℂ)) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re,
      Complex.natCast_re] at hre
    rw [hz_re] at hre
    have hnn : (0 : ℝ) ≤ (((n : ℕ)) : ℝ) := Nat.cast_nonneg n
    linarith
  have hs1' : (1 - z) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re] at hre
    rw [hz_re] at hre
    norm_num at hre
  have hFE' : riemannZeta z
      = RowFE.RowFEFactor (1 - z) * riemannZeta (1 - z) := by
    have hFE := riemannZeta_one_sub (s := 1 - z) hs_neg hs1'
    have h1sub : (1 : ℂ) - (1 - z) = z := by ring
    rw [h1sub] at hFE
    have h2 : (2 * (2 * (Real.pi : ℂ)) ^ (-(1 - z)) * Complex.Gamma (1 - z)
        * Complex.cos ((Real.pi : ℂ) * (1 - z) / 2) * riemannZeta (1 - z))
        = RowFE.RowFEFactor (1 - z) * riemannZeta (1 - z) := by
      unfold RowFE.RowFEFactor
      ring
    rw [← h2]
    exact hFE
  have hZrefl : ‖riemannZeta (1 - z)‖ ≤ 2 := by
    have h := TailZetaUpper.zeta_rightEdge_B2 (s := 1 - z) (by linarith [hw_re])
    rwa [show zeta (1 - z) = riemannZeta (1 - z) from rfl] at h
  have himw875 : |((1 : ℂ) - z).im| ≤ 8.75 := by
    rw [hw_im, abs_neg]
    exact him
  have hsub : ‖z - 1‖ ≤ 9 := sub_upper_window hz_re him
  have hdamp : ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
      (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ ≤ 2.7183 :=
    damp_upper_window hz_re him
  by_cases hsmall : |((1 : ℂ) - z).im| ≤ 6
  · have hFactor : ‖RowFE.RowFEFactor (1 - z)‖ ≤ 1280 :=
      factor_small_le hw_re hsmall
    have hZ : ‖riemannZeta z‖ ≤ 2560 := by
      rw [hFE', norm_mul]
      calc ‖RowFE.RowFEFactor (1 - z)‖ * ‖riemannZeta (1 - z)‖
            ≤ 1280 * 2 :=
              mul_le_mul hFactor hZrefl (norm_nonneg _) (by norm_num)
        _ = 2560 := by norm_num
    have hF : ‖ZetaUpperR02ThreeLines.poleRemovedZeta z‖ ≤ 23040 := by
      rw [ZetaUpperR02ThreeLines.poleRemovedZeta_of_ne hz1, norm_mul]
      calc ‖z - 1‖ * ‖riemannZeta z‖ ≤ 9 * 2560 :=
            mul_le_mul hsub hZ (norm_nonneg _) (by norm_num)
        _ = 23040 := by norm_num
    have hfin : ZetaUpperR02ThreeLines.dampedPoleRemoved z =
        ZetaUpperR02ThreeLines.poleRemovedZeta z *
          Complex.exp (((1 / 100 : ℝ) : ℂ) *
            (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2) := rfl
    rw [hfin, norm_mul]
    calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta z‖ *
        ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
          (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖
          ≤ 23040 * 2.7183 :=
            mul_le_mul hF hdamp (norm_nonneg _) (by norm_num)
      _ ≤ 160000 := by norm_num
  · have hge6 : (6 : ℝ) ≤ |((1 : ℂ) - z).im| :=
      le_of_lt (lt_of_not_ge hsmall)
    have hFactor : ‖RowFE.RowFEFactor (1 - z)‖ ≤ 3120 :=
      factor_large_le hw_re hge6 himw875
    have hZ : ‖riemannZeta z‖ ≤ 6240 := by
      rw [hFE', norm_mul]
      calc ‖RowFE.RowFEFactor (1 - z)‖ * ‖riemannZeta (1 - z)‖
            ≤ 3120 * 2 :=
              mul_le_mul hFactor hZrefl (norm_nonneg _) (by norm_num)
        _ = 6240 := by norm_num
    have hF : ‖ZetaUpperR02ThreeLines.poleRemovedZeta z‖ ≤ 56160 := by
      rw [ZetaUpperR02ThreeLines.poleRemovedZeta_of_ne hz1, norm_mul]
      calc ‖z - 1‖ * ‖riemannZeta z‖ ≤ 9 * 6240 :=
            mul_le_mul hsub hZ (norm_nonneg _) (by norm_num)
        _ = 56160 := by norm_num
    have hfin : ZetaUpperR02ThreeLines.dampedPoleRemoved z =
        ZetaUpperR02ThreeLines.poleRemovedZeta z *
          Complex.exp (((1 / 100 : ℝ) : ℂ) *
            (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2) := rfl
    rw [hfin, norm_mul]
    calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta z‖ *
        ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
          (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖
          ≤ 56160 * 2.7183 :=
            mul_le_mul hF hdamp (norm_nonneg _) (by norm_num)
      _ ≤ 160000 := by norm_num

#print axioms Door3SharpWindow.cpow_sharp_Re2
#print axioms Door3SharpWindow.cos_uniform_sharp
#print axioms Door3SharpWindow.cos_small_sharp
#print axioms Door3SharpWindow.sub_upper_window
#print axioms Door3SharpWindow.damp_upper_window
#print axioms Door3SharpWindow.realGamma8_le
#print axioms Door3SharpWindow.gamma_uniform_Re2
#print axioms Door3SharpWindow.gamma_decay_ge6
#print axioms Door3SharpWindow.factor_small_le
#print axioms Door3SharpWindow.factor_large_le
#print axioms Door3SharpWindow.damped_window_sharp

end Door3SharpWindow

/-
JOINT `Γ·cos` EXPONENTIAL CANCELLATION (door-3 closure premise).

AL quantified the wall exactly: separate majorants lose `~1750×`
(`0.028·2e6 = 56000` vs true joint `≈ 32` at the edge) plus damp `2.7×`;
polynomial 6-shift floors (`1/|y|⁶`) vs `cosh(π|y|/2)` growth can NEVER close
the remaining `~3142×` to `50.925`. This section proves the joint identity
route, closing the premise.

WHAT IS PROVED (unconditional, no `sorry`/`admit`/`axiom`/stand-ins):
* Tier 1 `Gamma_one_add_im_normSq`: `‖Γ(1+iy)‖² = πy/sinh(πy)` for `y ≠ 0`.
* Tier 2 `joint_Gamma_cos_le`: `‖Γ(w)·cos(πw/2)‖ ≤ 34` on `Re = 2`,
  `|Im| ≤ 8.75` (true sup `≈ 32.6` at the edge; `4%` headroom, rigorous).
  Hence `0.028·2e6 = 56000` drops to `34`, a `1647×` joint-cancellation gain.
* Tier 3 `factor_joint_le`: `‖RowFEFactor w‖ ≤ 17/9` (`2·(1/36)·34`).
* Tier 3 `damp_sharp_window`: damping `≤ 1.02` (was `2.7183`; true sup
  `≈ 1.01`) via `exp(0.01) ≤ 1.02` from `exp(1) < 2.7183 < 3 ≤ 1.02^100`
  (Bernoulli `one_add_mul_le_pow` + 100th-root `le_of_pow_le_pow_left₀`).
* Tier 3 `damped_joint_window` (MAIN): `‖G(z)‖ ≤ 36` on `Re = -1`,
  `|Im| ≤ 8.75` (`34·1.02 = 34.68 ≤ 36`), i.e. `160000 → 36` (`4444×`)
  and `36 ≤ 50.925`, meeting AD's `ZetaUpperR02ThreeLines` threshold
  (`zetaUpper_R02_ten_of_bounds`) with margin `14.925`.

REUSE (nothing reimplemented):
* Mathlib: `Complex.Gamma_add_one` (`Gamma/Basic.lean:311`),
  `Complex.Gamma_conj` (`Basic.lean:355`),
  `Complex.Gamma_mul_Gamma_one_sub` (reflection, `Beta.lean:398`),
  `Complex.sin_mul_I`/`cos_mul_I`, `Complex.ofReal_sinh`/`ofReal_cosh`,
  `Complex.cos_add`/`cos_pi`/`sin_pi`, `Real.sinh_two_mul`,
  `Real.sinh_ne_zero`/`sinh_pos_iff`, `Real.cosh_pos`/`cosh_neg`/`sinh_neg`,
  `Real.add_one_le_exp`, `Real.exp_nat_mul`, `Real.exp_le_exp_of_le`,
  `Real.exp_one_lt_d9`, `Real.pi_gt_three`/`pi_lt_d4`/`pi_ne_zero`,
  `one_add_mul_le_pow`, `le_of_pow_le_pow_left₀`, `Complex.norm_conj`,
  `Complex.norm_real`, `Complex.sq_norm`, `Complex.normSq_apply`.
* In-file: `Door3SharpWindow.cpow_sharp_Re2` (`1/36`),
  `Door3SharpWindow.sub_upper_window` (`‖z-1‖ ≤ 9`),
  `TailZetaUpper.zeta_rightEdge_B2` (`‖ζ‖ ≤ 2` on `Re = 2`),
  `ZetaUpperR02ThreeLines` (`dampCenter`, `norm_complex_exp`,
  `poleRemovedZeta_of_ne`, `dampedPoleRemoved`), `RowFE.RowFEFactor`,
  `riemannZeta_one_sub` (cos-form FE).
* GREP RECORD (verified absent, hence created here): `normSq.*Gamma`,
  `Gamma_one_add_im`, `joint_Gamma`, `damped_joint`, `factor_joint`,
  `damp_sharp`, `cos_Re2`, `Gamma_Re2`, `t_mul_coth` return zero hits
  repo-wide; `im_decay`/`Gamma.*exp.*Im`/`norm_Gamma.*im` return only doc
  comments documenting the absence (no lemmas).
-/

namespace Door3JointGammaCos

open scoped ComplexConjugate

/-- Tier-1 identity: `‖Γ(1 + y·I)‖² = π·y / sinh(π·y)` for real `y ≠ 0`.
Via `Γ(1+iy) = iy·Γ(iy)` (`Gamma_add_one`), complex reflection
`Γ(iy)·Γ(1-iy) = π/sin(πiy)` (`Gamma_mul_Gamma_one_sub`),
`conj Γ(1+iy) = Γ(1-iy)` (`Gamma_conj`), and
`sin(πiy) = sinh(πy)·I` (`sin_mul_I` + `ofReal_sinh`). -/
theorem Gamma_one_add_im_normSq {y : ℝ} (hy : y ≠ 0) :
    ‖Complex.Gamma (1 + (y : ℂ) * Complex.I)‖ ^ 2
      = Real.pi * y / Real.sinh (Real.pi * y) := by
  set u : ℂ := (y : ℂ) * Complex.I with hu_def
  have hyC : ((y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy
  have hu_ne : u ≠ 0 := mul_ne_zero hyC Complex.I_ne_zero
  have hG1 : Complex.Gamma (1 + u) = u * Complex.Gamma u := by
    have h : (1 : ℂ) + u = u + 1 := add_comm _ _
    rw [h]
    exact Complex.Gamma_add_one u hu_ne
  have hrefl : Complex.Gamma u * Complex.Gamma (1 - u)
      = (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * u) :=
    Complex.Gamma_mul_Gamma_one_sub u
  have hconj_eq : conj (1 + u) = 1 - u := by
    rw [Complex.ext_iff]
    constructor
    · simp only [Complex.conj_re, Complex.add_re, Complex.sub_re, Complex.one_re,
        hu_def, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    · simp only [Complex.conj_im, Complex.add_im, Complex.sub_im, Complex.one_im,
        hu_def, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
  have hGconj : conj (Complex.Gamma (1 + u)) = Complex.Gamma (1 - u) := by
    rw [← Complex.Gamma_conj, hconj_eq]
  have hsin_eq : Complex.sin ((Real.pi : ℂ) * u)
      = ((Real.sinh (Real.pi * y) : ℝ) : ℂ) * Complex.I := by
    have e : (Real.pi : ℂ) * u = ((Real.pi * y : ℝ) : ℂ) * Complex.I := by
      rw [hu_def]
      push_cast
      ring
    rw [e, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  have hpy_ne : Real.pi * y ≠ 0 := mul_ne_zero Real.pi_ne_zero hy
  have hsinh_ne : Real.sinh (Real.pi * y) ≠ 0 := Real.sinh_ne_zero.mpr hpy_ne
  have hsinhC_ne : ((Real.sinh (Real.pi * y) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsinh_ne
  have hden_ne : ((Real.sinh (Real.pi * y) : ℝ) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero hsinhC_ne Complex.I_ne_zero
  have hprod : Complex.Gamma (1 + u) * Complex.Gamma (1 - u)
      = ((Real.pi * y / Real.sinh (Real.pi * y) : ℝ) : ℂ) := by
    rw [hG1, mul_assoc, hrefl, hsin_eq, hu_def, Complex.ofReal_div,
      Complex.ofReal_mul, ← mul_div_assoc, div_eq_div_iff hden_ne hsinhC_ne]
    ring
  have hpos : 0 < Real.pi * y / Real.sinh (Real.pi * y) := by
    have hpi : 0 < Real.pi := lt_trans (by norm_num) Real.pi_gt_three
    rcases lt_or_gt_of_ne hy with hyneg | hypos
    · refine div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hpi hyneg) ?_
      have h3 : 0 < Real.sinh (-(Real.pi * y)) :=
        Real.sinh_pos_iff.mpr (by linarith [mul_neg_of_pos_of_neg hpi hyneg])
      rw [Real.sinh_neg] at h3
      linarith
    · exact div_pos (mul_pos hpi hypos) (Real.sinh_pos_iff.mpr (mul_pos hpi hypos))
  have hzc : Complex.Gamma (1 + u) * conj (Complex.Gamma (1 + u))
      = ((Real.pi * y / Real.sinh (Real.pi * y) : ℝ) : ℂ) := by
    rw [hGconj]
    exact hprod
  have enorm : ‖Complex.Gamma (1 + u)‖ ^ 2
      = ‖Complex.Gamma (1 + u) * conj (Complex.Gamma (1 + u))‖ := by
    rw [norm_mul, Complex.norm_conj, pow_two]
  rw [enorm, hzc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]

/-- From-scratch `t·coth` bound: `t·(cosh t/sinh t) ≤ t + 1` for `t > 0`.
Proof: with `E = exp t`, `cosh/sinh = (E²+1)/(E²-1)` (via `cosh_eq`,
`sinh_eq`, `exp_neg` and `E·E⁻¹ = 1`), so the claim is
`t·(E²+1) ≤ (t+1)·(E²-1)`, i.e. `2t+1 ≤ E²`, which is `add_one_le_exp`. -/
theorem t_mul_coth_le {t : ℝ} (ht : 0 < t) :
    t * (Real.cosh t / Real.sinh t) ≤ t + 1 := by
  have hsinh_pos : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hEpos : 0 < Real.exp t := Real.exp_pos t
  have hEne : Real.exp t ≠ 0 := ne_of_gt hEpos
  have hEE : Real.exp t * (Real.exp t)⁻¹ = 1 := mul_inv_cancel₀ hEne
  have hEneg : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
  have hE2 : (1 : ℝ) + 2 * t ≤ (Real.exp t) ^ 2 := by
    have h := Real.add_one_le_exp (2 * t)
    have e : Real.exp (2 * t) = (Real.exp t) ^ 2 := by
      have h2 : (2 : ℝ) * t = t + t := by ring
      rw [h2, Real.exp_add, sq]
    linarith
  have hmul1 : (Real.exp t + (Real.exp t)⁻¹) * Real.exp t
      = (Real.exp t) ^ 2 + 1 := by
    linear_combination hEE
  have hmul2 : (Real.exp t - (Real.exp t)⁻¹) * Real.exp t
      = (Real.exp t) ^ 2 - 1 := by
    linear_combination -hEE
  have hkey2 : t * (Real.exp t + (Real.exp t)⁻¹)
      ≤ (t + 1) * (Real.exp t - (Real.exp t)⁻¹) := by
    have g : (t * (Real.exp t + (Real.exp t)⁻¹)) * Real.exp t
        ≤ ((t + 1) * (Real.exp t - (Real.exp t)⁻¹)) * Real.exp t := by
      rw [mul_assoc, hmul1, mul_assoc, hmul2]
      nlinarith [hE2]
    exact le_of_mul_le_mul_right g hEpos
  have hcosh_eq : Real.cosh t = (Real.exp t + (Real.exp t)⁻¹) / 2 := by
    rw [Real.cosh_eq, hEneg]
  have hsinh_eq : Real.sinh t = (Real.exp t - (Real.exp t)⁻¹) / 2 := by
    rw [Real.sinh_eq, hEneg]
  have key : t * ((Real.exp t + (Real.exp t)⁻¹) / 2)
      ≤ (t + 1) * ((Real.exp t - (Real.exp t)⁻¹) / 2) := by
    linarith [hkey2]
  rw [hcosh_eq, hsinh_eq, ← mul_div_assoc, ← hsinh_eq, div_le_iff₀ hsinh_pos,
    hsinh_eq]
  exact key

/-- Exact cos norm on the `Re = 2` line: `‖cos(πw/2)‖ = cosh(π·Im w/2)`.
Since `πw/2 = π + (πy/2)·I`, `cos` negates (`cos_add`/`cos_pi`/`sin_pi`)
and `cos(t·I) = cosh t` (`cos_mul_I` + `ofReal_cosh`). -/
theorem cos_Re2_norm {w : ℂ} (hw : w.re = 2) :
    ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖ = Real.cosh (Real.pi * w.im / 2) := by
  have h2c : ((2 : ℕ) : ℂ) = (2 : ℂ) := by norm_num
  have hre : ((Real.pi : ℂ) * w / 2).re = Real.pi := by
    rw [← h2c, Complex.div_natCast_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, hw]
    ring
  have him : ((Real.pi : ℂ) * w / 2).im = Real.pi * w.im / 2 := by
    rw [← h2c, Complex.div_natCast_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have harg : (Real.pi : ℂ) * w / 2
      = (Real.pi : ℂ) + ((Real.pi * w.im / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · rw [hre]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    · rw [him]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
  have hcosv : Complex.cos (((Real.pi * w.im / 2 : ℝ) : ℂ) * Complex.I)
      = ((Real.cosh (Real.pi * w.im / 2) : ℝ) : ℂ) := by
    rw [Complex.cos_mul_I, Complex.ofReal_cosh]
  rw [harg, Complex.cos_add, Complex.cos_pi, Complex.sin_pi]
  have hneg : (-1 : ℂ) * Complex.cos (((Real.pi * w.im / 2 : ℝ) : ℂ) * Complex.I)
      - 0 * Complex.sin (((Real.pi * w.im / 2 : ℝ) : ℂ) * Complex.I)
      = -Complex.cos (((Real.pi * w.im / 2 : ℝ) : ℂ) * Complex.I) := by ring
  rw [hneg, hcosv, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos _)]

/-- Gamma norm on the `Re = 2` line: `‖Γ(w)‖² = (1+y²)·πy/sinh(πy)` for
`w.im = y ≠ 0`. Via `Γ(w) = (1+iy)·Γ(1+iy)` (`Gamma_add_one` at `1+iy ≠ 0`)
times Tier 1, with `‖1+iy‖² = 1+y²` (`sq_norm` + `normSq_apply`). -/
theorem Gamma_Re2_normSq {w : ℂ} (hw : w.re = 2) (hy : w.im ≠ 0) :
    ‖Complex.Gamma w‖ ^ 2
      = (1 + w.im ^ 2) * (Real.pi * w.im / Real.sinh (Real.pi * w.im)) := by
  have hw_eq : w = (1 + ((w.im : ℝ) : ℂ) * Complex.I) + 1 := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      rw [hw]
      ring
    · simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
  have hs_ne : (1 + ((w.im : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have hre0 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re] at hre0
    norm_num at hre0
  have hnorm_s : ‖(1 + ((w.im : ℝ) : ℂ) * Complex.I)‖ ^ 2 = 1 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.add_im,
      Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hG : Complex.Gamma w
      = (1 + ((w.im : ℝ) : ℂ) * Complex.I)
        * Complex.Gamma (1 + ((w.im : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rw [hw_eq]
    exact Complex.Gamma_add_one _ hs_ne
  rw [hG, norm_mul, mul_pow, hnorm_s, Gamma_one_add_im_normSq hy]

/-- Tier-2 JOINT cap: `‖Γ(w)·cos(πw/2)‖ ≤ 34` on `Re = 2`, `|Im| ≤ 8.75`.
The `y = 0` case is direct (`Γ(2) = 1`, `cos π = -1`). For `y ≠ 0`,
`‖Γ·cos‖² = (1+a²)·(πa/sinh πa)·cosh²(πa/2)` with `a = |y|`, and
`sinh πa = 2·sinh(πa/2)·cosh(πa/2)` (`sinh_two_mul`) collapses this to
`(1+a²)·(t·coth t) ≤ (1+a²)·(t+1)` (`t_mul_coth_le`), bounded by
`77.5625·(3.1416·8.75/2+1) = 1143.62… ≤ 34²`. -/
theorem joint_Gamma_cos_le {w : ℂ} (hw : w.re = 2) (him : |w.im| ≤ 8.75) :
    ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ ≤ 34 := by
  by_cases hy0 : w.im = 0
  · have hw2 : w = ((2 : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [hw, Complex.ofReal_re]
      · rw [hy0, Complex.ofReal_im]
    have hG2 : Complex.Gamma ((2 : ℝ) : ℂ) = 1 := by
      have e : ((2 : ℝ) : ℂ) = (1 : ℂ) + 1 := by
        exact_mod_cast (by norm_num : (2 : ℝ) = 1 + 1)
      rw [e, Complex.Gamma_add_one _ one_ne_zero, Complex.Gamma_one, mul_one]
    have hcos : Complex.cos ((Real.pi : ℂ) * ((2 : ℝ) : ℂ) / 2) = -1 := by
      have e : (Real.pi : ℂ) * ((2 : ℝ) : ℂ) / 2 = (Real.pi : ℂ) := by
        push_cast
        ring
      rw [e, Complex.cos_pi]
    rw [hw2, hG2, hcos, one_mul, norm_neg, norm_one]
    norm_num
  · have hyne : w.im ≠ 0 := hy0
    have hG := Gamma_Re2_normSq hw hyne
    have hC := cos_Re2_norm hw
    have ha_pos : 0 < |w.im| := abs_pos.mpr hyne
    have hpi : 0 < Real.pi := lt_trans (by norm_num) Real.pi_gt_three
    have hthal_pos : 0 < Real.pi * |w.im| / 2 := by
      have h2 := mul_pos (mul_pos hpi ha_pos) (show (0 : ℝ) < 1 / 2 by norm_num)
      linarith
    have hsinh_half_pos : 0 < Real.sinh (Real.pi * |w.im| / 2) :=
      Real.sinh_pos_iff.mpr hthal_pos
    have hcosh_pos : 0 < Real.cosh (Real.pi * |w.im| / 2) := Real.cosh_pos _
    have hsymm : Real.pi * w.im / Real.sinh (Real.pi * w.im)
        = Real.pi * |w.im| / Real.sinh (Real.pi * |w.im|) := by
      rcases le_total w.im 0 with hynonpos | hynonneg
      · have hyneg : w.im < 0 := lt_of_le_of_ne hynonpos hyne
        rw [abs_of_neg hyneg, show Real.pi * -w.im = -(Real.pi * w.im) by ring,
          Real.sinh_neg, neg_div_neg_eq]
      · rw [abs_of_nonneg hynonneg]
    have heven : Real.cosh (Real.pi * w.im / 2)
        = Real.cosh (Real.pi * |w.im| / 2) := by
      rcases le_total w.im 0 with hynonpos | hynonneg
      · have hyneg : w.im < 0 := lt_of_le_of_ne hynonpos hyne
        rw [abs_of_neg hyneg,
          show Real.pi * -w.im / 2 = -(Real.pi * w.im / 2) by ring, Real.cosh_neg]
      · rw [abs_of_nonneg hynonneg]
    have hsinh2 : Real.sinh (Real.pi * |w.im|)
        = 2 * Real.sinh (Real.pi * |w.im| / 2)
          * Real.cosh (Real.pi * |w.im| / 2) := by
      have hdouble : Real.pi * |w.im| = 2 * (Real.pi * |w.im| / 2) := by ring
      conv_lhs => rw [hdouble]
      rw [Real.sinh_two_mul]
    have hsinh_half_ne : Real.sinh (Real.pi * |w.im| / 2) ≠ 0 :=
      ne_of_gt hsinh_half_pos
    have hcosh_ne : Real.cosh (Real.pi * |w.im| / 2) ≠ 0 := ne_of_gt hcosh_pos
    have hden_ne : 2 * Real.sinh (Real.pi * |w.im| / 2)
        * Real.cosh (Real.pi * |w.im| / 2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hsinh_half_ne) hcosh_ne
    have hstep : (1 + |w.im| ^ 2)
            * (Real.pi * |w.im| / Real.sinh (Real.pi * |w.im|))
            * (Real.cosh (Real.pi * |w.im| / 2)) ^ 2
        = (1 + |w.im| ^ 2)
          * ((Real.pi * |w.im| / 2)
            * (Real.cosh (Real.pi * |w.im| / 2)
              / Real.sinh (Real.pi * |w.im| / 2))) := by
      rw [hsinh2]
      field_simp
    have h1a2 : (1 : ℝ) + |w.im| ^ 2 ≤ 77.5625 := by
      have h1 : |w.im| ^ 2 ≤ (8.75 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) him 2
      have h2 : (8.75 : ℝ) ^ 2 = 76.5625 := by norm_num
      rw [h2] at h1
      linarith
    have ht1 : Real.pi * |w.im| / 2 + 1 ≤ 3.1416 * 8.75 / 2 + 1 := by
      have hpile : Real.pi ≤ 3.1416 := le_of_lt Real.pi_lt_d4
      have h1 : Real.pi * |w.im| ≤ 3.1416 * 8.75 :=
        mul_le_mul hpile him (abs_nonneg _) (by norm_num)
      linarith
    have hcoth := t_mul_coth_le hthal_pos
    have hnonneg : (0 : ℝ) ≤ 1 + |w.im| ^ 2 := by positivity
    have hnn1 : (0 : ℝ) ≤ Real.pi * |w.im| / 2 + 1 := by linarith [hthal_pos]
    have hnn2 : (0 : ℝ) ≤ 77.5625 := by norm_num
    have hfinal : (77.5625 : ℝ) * (3.1416 * 8.75 / 2 + 1) ≤ 34 ^ 2 := by norm_num
    have hsq : ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ ^ 2
        ≤ 34 ^ 2 := by
      have e1 : ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ ^ 2
          = ‖Complex.Gamma w‖ ^ 2 * ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖ ^ 2 := by
        rw [norm_mul, mul_pow]
      rw [e1, hG, hC, hsymm, heven, ← sq_abs w.im, hstep]
      exact le_trans (le_trans (mul_le_mul_of_nonneg_left hcoth hnonneg)
        (mul_le_mul h1a2 ht1 hnn1 hnn2)) hfinal
    have hle := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (show (0 : ℝ) ≤ (34 : ℝ) by norm_num)] at hle
    exact hle

/-- Tier-3 FE-factor cap via the joint bound:
`‖RowFEFactor w‖ = 2·‖(2π)^{-w}‖·‖Γ·cos‖ ≤ 2·(1/36)·34 = 17/9`.
Uses `Door3SharpWindow.cpow_sharp_Re2`; the `1280`/`3120` separate caps are
superseded here (that is the joint-cancellation gain). -/
theorem factor_joint_le {w : ℂ} (hw : w.re = 2) (him : |w.im| ≤ 8.75) :
    ‖RowFE.RowFEFactor w‖ ≤ 17 / 9 := by
  have hcpow := Door3SharpWindow.cpow_sharp_Re2 hw
  have hjoint := joint_Gamma_cos_le hw him
  have h2norm : ‖(2 : ℂ)‖ = 2 := by
    have e : ((2 : ℕ) : ℂ) = (2 : ℂ) := by norm_num
    rw [← e, RCLike.norm_natCast]
    norm_num
  have hnorm_eq : ‖RowFE.RowFEFactor w‖
      = ‖(2 : ℂ)‖ * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖
        * (‖Complex.Gamma w‖ * ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖) := by
    unfold RowFE.RowFEFactor
    rw [norm_mul, norm_mul, norm_mul]
    ring
  have hgc : ‖Complex.Gamma w‖ * ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖
      = ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ :=
    (norm_mul _ _).symm
  rw [hnorm_eq, h2norm, hgc]
  have h1 : (2 : ℝ) * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ ≤ 2 * (1 / 36) :=
    mul_le_mul_of_nonneg_left hcpow (by norm_num)
  exact le_trans
    (mul_le_mul h1 hjoint (norm_nonneg _) (by norm_num)) (by norm_num)

/-- Tier-3 sharp damping: `‖damp‖ ≤ 1.02` on the window (was `2.7183`).
`Re((s-c)²)/100 ≤ 0.01` as in `Door3SharpWindow.damp_upper_window`, then
`exp(0.01) ≤ 1.02`: `(exp 0.01)^100 = exp 1 < 2.7183 < 3 ≤ 1.02^100`
(Bernoulli) and take 100th roots. -/
theorem damp_sharp_window {z : ℂ} (hz_re : z.re = -1) (him : |z.im| ≤ 8.75) :
    ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
      (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ ≤ 1.02 := by
  have hsq2 : ((z - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re
      = 1 - (z.im + 6.75) ^ 2 := by
    have e1 : (z - ZetaUpperR02ThreeLines.dampCenter).re = -1 := by
      rw [Complex.sub_re, ZetaUpperR02ThreeLines.dampCenter_re, hz_re, sub_zero]
    have e2 : (z - ZetaUpperR02ThreeLines.dampCenter).im = z.im + 6.75 := by
      rw [Complex.sub_im, ZetaUpperR02ThreeLines.dampCenter_im]
      ring
    rw [pow_two, Complex.mul_re, e1, e2]
    ring
  have hwre : ((((1 / 100 : ℝ)) : ℂ) *
      (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re ≤ 0.01 := by
    have hwm : ((((1 / 100 : ℝ)) : ℂ) *
        (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re
        = (1 / 100) * ((((z - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re)) := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hwm, hsq2]
    have ht2 : (0 : ℝ) ≤ (z.im + 6.75) ^ 2 := sq_nonneg _
    linarith
  rw [ZetaUpperR02ThreeLines.norm_complex_exp]
  have hexp : Real.exp ((((1 / 100 : ℝ)) : ℂ) *
      (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re
      ≤ Real.exp 0.01 := Real.exp_le_exp_of_le hwre
  have h102 : Real.exp (0.01 : ℝ) ≤ 1.02 := by
    have hE100 : (Real.exp (0.01 : ℝ)) ^ 100 = Real.exp 1 := by
      have h := Real.exp_nat_mul (0.01 : ℝ) (100 : ℕ)
      have h100 : ((100 : ℕ) : ℝ) * 0.01 = 1 := by norm_num
      rw [h100] at h
      exact h.symm
    have hbern : (3 : ℝ) ≤ (1.02 : ℝ) ^ (100 : ℕ) := by
      have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ (0.02 : ℝ) by norm_num)
        (100 : ℕ)
      rw [show ((100 : ℕ) : ℝ) * (0.02 : ℝ) = 2 by norm_num,
        show (1 : ℝ) + 0.02 = 1.02 by norm_num,
        show (1 : ℝ) + 2 = 3 by norm_num] at hb
      exact hb
    have hlt : Real.exp (1 : ℝ) < 2.7182818286 := Real.exp_one_lt_d9
    have hle : (Real.exp (0.01 : ℝ)) ^ 100 ≤ (1.02 : ℝ) ^ (100 : ℕ) := by
      rw [hE100]
      linarith [hlt, hbern]
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hle
  linarith [hexp, h102]

/-- Tier-3 MAIN composed damped cap: `‖G(z)‖ ≤ 36` on `Re = -1`,
`|Im| ≤ 8.75` (`34·1.02 = 34.68 ≤ 36`). FE assembly mirrors
`Door3SharpWindow.damped_window_sharp` (single joint branch, no `|y| ≶ 6`
split): `‖ζ(z)‖ ≤ (17/9)·2 = 34/9`, `‖F‖ ≤ 9·(34/9) = 34`,
`‖G‖ ≤ 34·1.02 ≤ 36 ≤ 50.925`, meeting AD's
`ZetaUpperR02ThreeLines` threshold (`zetaUpper_R02_ten_of_bounds`). -/
theorem damped_joint_window {z : ℂ} (hz_re : z.re = -1) (him : |z.im| ≤ 8.75) :
    ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ 36 := by
  have hz1 : z ≠ 1 := by
    intro h
    have hre : z.re = 1 := by rw [h, Complex.one_re]
    linarith
  have hw_re : ((1 : ℂ) - z).re = 2 := by
    rw [Complex.sub_re, Complex.one_re, hz_re]
    norm_num
  have hw_im : ((1 : ℂ) - z).im = -z.im := by
    rw [Complex.sub_im, Complex.one_im, zero_sub]
  have hs_neg : ∀ n : ℕ, (1 - z) ≠ -((n : ℂ)) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re,
      Complex.natCast_re] at hre
    rw [hz_re] at hre
    have hnn : (0 : ℝ) ≤ (((n : ℕ)) : ℝ) := Nat.cast_nonneg n
    linarith
  have hs1' : (1 - z) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re] at hre
    rw [hz_re] at hre
    norm_num at hre
  have hFE' : riemannZeta z
      = RowFE.RowFEFactor (1 - z) * riemannZeta (1 - z) := by
    have hFE := riemannZeta_one_sub (s := 1 - z) hs_neg hs1'
    have h1sub : (1 : ℂ) - (1 - z) = z := by ring
    rw [h1sub] at hFE
    have h2 : (2 * (2 * (Real.pi : ℂ)) ^ (-(1 - z)) * Complex.Gamma (1 - z)
        * Complex.cos ((Real.pi : ℂ) * (1 - z) / 2) * riemannZeta (1 - z))
        = RowFE.RowFEFactor (1 - z) * riemannZeta (1 - z) := by
      unfold RowFE.RowFEFactor
      ring
    rw [← h2]
    exact hFE
  have hZrefl : ‖riemannZeta (1 - z)‖ ≤ 2 := by
    have h := TailZetaUpper.zeta_rightEdge_B2 (s := 1 - z) (by linarith [hw_re])
    rwa [show zeta (1 - z) = riemannZeta (1 - z) from rfl] at h
  have himw875 : |((1 : ℂ) - z).im| ≤ 8.75 := by
    rw [hw_im, abs_neg]
    exact him
  have hsub : ‖z - 1‖ ≤ 9 := Door3SharpWindow.sub_upper_window hz_re him
  have hdamp : ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
      (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ ≤ 1.02 :=
    damp_sharp_window hz_re him
  have hFactor : ‖RowFE.RowFEFactor (1 - z)‖ ≤ 17 / 9 :=
    factor_joint_le hw_re himw875
  have hZ : ‖riemannZeta z‖ ≤ 34 / 9 := by
    rw [hFE', norm_mul]
    calc ‖RowFE.RowFEFactor (1 - z)‖ * ‖riemannZeta (1 - z)‖ ≤ (17 / 9) * 2 :=
          mul_le_mul hFactor hZrefl (norm_nonneg _) (by norm_num)
      _ = 34 / 9 := by norm_num
  have hF : ‖ZetaUpperR02ThreeLines.poleRemovedZeta z‖ ≤ 34 := by
    rw [ZetaUpperR02ThreeLines.poleRemovedZeta_of_ne hz1, norm_mul]
    calc ‖z - 1‖ * ‖riemannZeta z‖ ≤ 9 * (34 / 9) :=
          mul_le_mul hsub hZ (norm_nonneg _) (by norm_num)
      _ = 34 := by norm_num
  have hfin : ZetaUpperR02ThreeLines.dampedPoleRemoved z =
      ZetaUpperR02ThreeLines.poleRemovedZeta z *
        Complex.exp (((1 / 100 : ℝ) : ℂ) *
          (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2) := rfl
  rw [hfin, norm_mul]
  calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta z‖ *
      ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
        (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖
        ≤ 34 * 1.02 :=
          mul_le_mul hF hdamp (norm_nonneg _) (by norm_num)
    _ ≤ 36 := by norm_num

#print axioms Door3JointGammaCos.Gamma_one_add_im_normSq
#print axioms Door3JointGammaCos.t_mul_coth_le
#print axioms Door3JointGammaCos.cos_Re2_norm
#print axioms Door3JointGammaCos.Gamma_Re2_normSq
#print axioms Door3JointGammaCos.joint_Gamma_cos_le
#print axioms Door3JointGammaCos.factor_joint_le
#print axioms Door3JointGammaCos.damp_sharp_window
#print axioms Door3JointGammaCos.damped_joint_window

end Door3JointGammaCos

/-!
# BF2 tail caps: AR window-36 to whole-line shapes (door-3/door-4 feeder, append-only)

GREP-FIRST RECORD (repo + Mathlib, via `rg`, 2026-09-04; everything below reuses,
nothing recreates):
* AD assembly + threshold: `ZetaUpperR02ThreeLines.zetaUpper_R02_ten_of_bounds`
  (`riemann_hypothesis_newsection.lean:1398`: whole-line `A ≤ 50.925` at `l = -1`,
  `B ≤ A` at `u = 2`, plus `BddAbove` ⇒ `‖ζ‖ ≤ 10` on the R02 rect).
* AJ assembly family: `TailZetaUpper_threeLines_FE_assembly` (`:1677`, whole-line
  constant caps + `BddAbove` ⇒ pointwise bound), `..._uniformExp` (`:1756`),
  `..._threshold_50p925` (`:1809`, fires only from whole-line `A ≤ 50.925`).
* AR window cap: `Door3JointGammaCos.damped_joint_window` (`:3043`:
  `‖G‖ ≤ 36` on `Re = -1`, `|Im| ≤ 8.75`, with `G = dampedPoleRemoved`).
* Right `ζ` edge, Im-uniform and whole-line: `TailZetaUpper.zeta_rightEdge_B2`
  (`:1040`, `Re ≥ 2 → ‖zeta‖ ≤ 2`).
* Sharp cpow `≤ 1/36` on `Re = 2` (hypothesis is only `Re`, hence whole-line):
  `Door3SharpWindow.cpow_sharp_Re2` (`:1972`); Gamma `≤ 1` on `Re = 2`:
  `Door3SharpWindow.gamma_uniform_Re2` (`:2256`).
* Generic cos majorant: `RowFE.RowFE_norm_cos_le` (`interval_arith.lean:30905`,
  `‖cos w‖ ≤ exp B` from `|Im w| ≤ B`).
* FE cos form: `riemannZeta_one_sub`; Mathlib:
  `Complex.norm_le_abs_re_add_abs_im`, `Real.exp_nat_mul`, `Real.exp_one_lt_d9`,
  `Real.add_one_le_exp`, `Real.exp_add`, `Complex.div_ofNat_im`,
  `le_of_pow_le_pow_left₀`, `le_div_iff₀`, `one_div_div`.

WHAT IS PROVED (unconditional, no `sorry`/`admit`/`axiom`/stand-ins):
* `damped_left_window_preimage`: AR's `36` restated in the exact preimage binder
  shape the assemblies consume
  (`∀ z ∈ preimage re {-1}, |Im| ≤ 8.75 → ‖G‖ ≤ 36`).
* `cos_FE_generic`, `damp_left_whole_le`, `factor_left_whole_le`,
  `zeta_Re_neg1_whole_le`: whole-line ingredients on `Re = -1`
  (cos `≤ exp(π|Im|/2)`, damping `≤ 1.02`, FE factor `≤ (1/18)·exp(π|Im|/2)`).
* `damped_left_whole_growth` (TIER-1 MAIN): whole-line
  `‖G(z)‖ ≤ (2 + |Im z|) · ((1/9) · 1.02 · exp(π|Im z|/2))` on `Re = -1`,
  the satisfiable whole-line variant with explicit `|Im|` growth.
* `damped_right_whole_36` (TIER-2 right piece): whole-line `‖G(s)‖ ≤ 36` on
  `Re = 2` in the exact `hRight` shape (`B = 36 ≤ A = 36`), via `B₂`, the triangle
  bound `‖s-1‖ ≤ 1 + |Im|`, `exp(0.04) ≤ 1.05`, `exp(-t) ≤ 1/(1+t)`, and the
  polynomial-times-Gaussian sup `(7.75+r)·100/(100+r²) ≤ 11`
  (i.e. `11r²-100r+325 ≥ 0`, discriminant `10000 - 14300 < 0`).

P1 VERDICT + RESIDUAL (report-and-stop): whole-line CONSTANT `A ≤ 50.925` on
`Re = -1` does NOT fit — the crude-majorant truth there is exponential
(`cosh(π|Im|/2)` versus Gaussian damping, worst around `|Im| ≈ 85`), while the
sharp truth `O(10)` needs the joint `Γ·cos` identity for ALL `Im` plus Stirling
(both absent repo-wide). Hence AD's `..._ten_of_bounds` (and AJ's
`..._threshold_50p925`) do NOT fire from this tail; `BddAbove` on `[-1,2]` stays
an explicit premise everywhere (needs strip `ζ`-growth, likewise absent); the
composed R02 `‖ζ‖ ≤ 10` stays OPEN. What now fits exactly: `hRight` with
`B = 36` (this tail) + windowed `hLeft` with `A = 36` (AR) + the whole-line
growth `hLeft`-variant (this tail).
-/

namespace BF2TailCaps

/-- AR's window cap in the exact preimage binder shape the assemblies consume. -/
theorem damped_left_window_preimage {z : ℂ}
    (hz : z ∈ Set.preimage Complex.re {(-1 : ℝ)}) (him : |z.im| ≤ 8.75) :
    ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ 36 := by
  have hz_re : z.re = -1 := by simpa using hz
  exact Door3JointGammaCos.damped_joint_window hz_re him

/-- Generic FE-cos bound: `‖cos(πw/2)‖ ≤ exp(π|Im w|/2)` for ALL `Im`
(via `RowFE_norm_cos_le`; no window hypothesis). -/
theorem cos_FE_generic {w : ℂ} :
    ‖Complex.cos ((Real.pi : ℂ) * (w / 2))‖ ≤ Real.exp (Real.pi * |w.im| / 2) := by
  have hs2im : (w / 2).im = w.im / 2 := by rw [Complex.div_ofNat_im]
  have hw_im : ((Real.pi : ℂ) * (w / 2)).im = Real.pi * (w.im / 2) := by
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hs2im]
  have hB : |(((Real.pi : ℂ) * (w / 2)).im)| ≤ Real.pi * |w.im| / 2 := by
    rw [hw_im]
    have h1 : |Real.pi * (w.im / 2)| = Real.pi * |w.im| / 2 := by
      rw [abs_mul, abs_of_pos Real.pi_pos, abs_div, abs_two]
      ring
    exact le_of_eq h1
  exact RowFE.RowFE_norm_cos_le hB

/-- Whole-line damping `≤ 1.02` on `Re = -1`: `(1-u²)/100 ≤ 0.01` for every `u`
(AR's `damp_sharp_window` proof minus the window hypothesis). -/
theorem damp_left_whole_le {z : ℂ} (hz_re : z.re = -1) :
    ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
      (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ ≤ 1.02 := by
  have hsq2 : ((z - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re
      = 1 - (z.im + 6.75) ^ 2 := by
    have e1 : (z - ZetaUpperR02ThreeLines.dampCenter).re = -1 := by
      rw [Complex.sub_re, ZetaUpperR02ThreeLines.dampCenter_re, hz_re, sub_zero]
    have e2 : (z - ZetaUpperR02ThreeLines.dampCenter).im = z.im + 6.75 := by
      rw [Complex.sub_im, ZetaUpperR02ThreeLines.dampCenter_im]
      ring
    rw [pow_two, Complex.mul_re, e1, e2]
    ring
  have hwre : ((((1 / 100 : ℝ)) : ℂ) *
      (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re ≤ 0.01 := by
    have hwm : ((((1 / 100 : ℝ)) : ℂ) *
        (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re
        = (1 / 100) * ((((z - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re)) := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hwm, hsq2]
    have ht2 : (0 : ℝ) ≤ (z.im + 6.75) ^ 2 := sq_nonneg _
    linarith
  rw [ZetaUpperR02ThreeLines.norm_complex_exp]
  have hexp : Real.exp ((((1 / 100 : ℝ)) : ℂ) *
      (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re
      ≤ Real.exp 0.01 := Real.exp_le_exp_of_le hwre
  have h102 : Real.exp (0.01 : ℝ) ≤ 1.02 := by
    have hE100 : (Real.exp (0.01 : ℝ)) ^ 100 = Real.exp 1 := by
      have h := Real.exp_nat_mul (0.01 : ℝ) (100 : ℕ)
      have h100 : ((100 : ℕ) : ℝ) * 0.01 = 1 := by norm_num
      rw [h100] at h
      exact h.symm
    have hbern : (3 : ℝ) ≤ (1.02 : ℝ) ^ (100 : ℕ) := by
      have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ (0.02 : ℝ) by norm_num)
        (100 : ℕ)
      rw [show ((100 : ℕ) : ℝ) * (0.02 : ℝ) = 2 by norm_num,
        show (1 : ℝ) + 0.02 = 1.02 by norm_num,
        show (1 : ℝ) + 2 = 3 by norm_num] at hb
      exact hb
    have hlt : Real.exp (1 : ℝ) < 2.7182818286 := Real.exp_one_lt_d9
    have hle : (Real.exp (0.01 : ℝ)) ^ 100 ≤ (1.02 : ℝ) ^ (100 : ℕ) := by
      rw [hE100]
      linarith [hlt, hbern]
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hle
  linarith [hexp, h102]

/-- Whole-line FE factor on `Re = 2`: `‖RowFEFactor w‖ ≤ (1/18)·exp(π|Im w|/2)`
(manual norm equation as in `factor_joint_le`, with the sharp whole-line cpow
`1/36`, uniform Gamma `≤ 1`, and the generic cos). -/
theorem factor_left_whole_le {w : ℂ} (hw : w.re = 2) :
    ‖RowFE.RowFEFactor w‖ ≤ (1 / 18) * Real.exp (Real.pi * |w.im| / 2) := by
  have hcpow := Door3SharpWindow.cpow_sharp_Re2 hw
  have hG : ‖Complex.Gamma w‖ ≤ 1 := Door3SharpWindow.gamma_uniform_Re2 hw
  have hcos : ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖
      ≤ Real.exp (Real.pi * |w.im| / 2) := by
    have e : (Real.pi : ℂ) * w / 2 = (Real.pi : ℂ) * (w / 2) :=
      mul_div_assoc _ _ _
    rw [e]
    exact cos_FE_generic
  have h2norm : ‖(2 : ℂ)‖ = 2 := by
    have e : ((2 : ℕ) : ℂ) = (2 : ℂ) := by norm_num
    rw [← e, RCLike.norm_natCast]
    norm_num
  have hnorm_eq : ‖RowFE.RowFEFactor w‖
      = ‖(2 : ℂ)‖ * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖
        * (‖Complex.Gamma w‖ * ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖) := by
    unfold RowFE.RowFEFactor
    rw [norm_mul, norm_mul, norm_mul]
    ring
  rw [hnorm_eq, h2norm]
  have hA : (2 : ℝ) * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ ≤ 2 * (1 / 36) :=
    mul_le_mul_of_nonneg_left hcpow (by norm_num)
  have hB : ‖Complex.Gamma w‖ * ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖
      ≤ 1 * Real.exp (Real.pi * |w.im| / 2) :=
    mul_le_mul hG hcos (norm_nonneg _) (by norm_num)
  calc (2 : ℝ) * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖
        * (‖Complex.Gamma w‖ * ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖)
      ≤ (2 * (1 / 36)) * (1 * Real.exp (Real.pi * |w.im| / 2)) :=
        mul_le_mul hA hB (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = (1 / 18) * Real.exp (Real.pi * |w.im| / 2) := by ring

/-- Whole-line `ζ` on `Re = -1` via FE reflection to `Re = 2` (where `B₂` is
Im-uniform): `‖ζ(z)‖ ≤ (1/9)·exp(π|Im z|/2)`. -/
theorem zeta_Re_neg1_whole_le {z : ℂ} (hz_re : z.re = -1) :
    ‖riemannZeta z‖ ≤ (1 / 9) * Real.exp (Real.pi * |z.im| / 2) := by
  have hz1 : z ≠ 1 := by
    intro h
    have hre : z.re = 1 := by rw [h, Complex.one_re]
    linarith
  have hw_re : ((1 : ℂ) - z).re = 2 := by
    rw [Complex.sub_re, Complex.one_re, hz_re]
    norm_num
  have hw_im : ((1 : ℂ) - z).im = -z.im := by
    rw [Complex.sub_im, Complex.one_im, zero_sub]
  have hs_neg : ∀ n : ℕ, (1 - z) ≠ -((n : ℂ)) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re,
      Complex.natCast_re] at hre
    rw [hz_re] at hre
    have hnn : (0 : ℝ) ≤ (((n : ℕ)) : ℝ) := Nat.cast_nonneg n
    linarith
  have hs1' : (1 - z) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re] at hre
    rw [hz_re] at hre
    norm_num at hre
  have hFE' : riemannZeta z
      = RowFE.RowFEFactor (1 - z) * riemannZeta (1 - z) := by
    have hFE := riemannZeta_one_sub (s := 1 - z) hs_neg hs1'
    have h1sub : (1 : ℂ) - (1 - z) = z := by ring
    rw [h1sub] at hFE
    have h2 : (2 * (2 * (Real.pi : ℂ)) ^ (-(1 - z)) * Complex.Gamma (1 - z)
        * Complex.cos ((Real.pi : ℂ) * (1 - z) / 2) * riemannZeta (1 - z))
        = RowFE.RowFEFactor (1 - z) * riemannZeta (1 - z) := by
      unfold RowFE.RowFEFactor
      ring
    rw [← h2]
    exact hFE
  have hZrefl : ‖riemannZeta (1 - z)‖ ≤ 2 := by
    have h := TailZetaUpper.zeta_rightEdge_B2 (s := 1 - z) (by linarith [hw_re])
    rwa [show zeta (1 - z) = riemannZeta (1 - z) from rfl] at h
  have him_eq : |((1 : ℂ) - z).im| = |z.im| := by
    rw [hw_im, abs_neg]
  have hFactor : ‖RowFE.RowFEFactor (1 - z)‖
      ≤ (1 / 18) * Real.exp (Real.pi * |z.im| / 2) := by
    have h := factor_left_whole_le (w := 1 - z) hw_re
    rwa [him_eq] at h
  rw [hFE', norm_mul]
  calc ‖RowFE.RowFEFactor (1 - z)‖ * ‖riemannZeta (1 - z)‖
      ≤ ((1 / 18) * Real.exp (Real.pi * |z.im| / 2)) * 2 :=
        mul_le_mul hFactor hZrefl (norm_nonneg _) (by positivity)
    _ = (1 / 9) * Real.exp (Real.pi * |z.im| / 2) := by ring

/-- TIER-1 MAIN: whole-line damped left cap with explicit `|Im|` growth. -/
theorem damped_left_whole_growth {z : ℂ} (hz_re : z.re = -1) :
    ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖
      ≤ (2 + |z.im|) * ((1 / 9) * 1.02 * Real.exp (Real.pi * |z.im| / 2)) := by
  have hz1 : z ≠ 1 := by
    intro h
    have hre : z.re = 1 := by rw [h, Complex.one_re]
    linarith
  have hsub : ‖z - 1‖ ≤ 2 + |z.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im (z - 1)
    have hre1 : (z - 1).re = -2 := by
      rw [Complex.sub_re, Complex.one_re, hz_re]
      norm_num
    have him1 : (z - 1).im = z.im := by
      rw [Complex.sub_im, Complex.one_im, sub_zero]
    have e : |(-2 : ℝ)| = 2 := by norm_num
    rw [hre1, him1, e] at h
    linarith
  have hZ := zeta_Re_neg1_whole_le hz_re
  have hdamp := damp_left_whole_le hz_re
  have hnn_e : (0 : ℝ) ≤ (1 / 9) * Real.exp (Real.pi * |z.im| / 2) :=
    mul_nonneg (by norm_num) (Real.exp_pos _).le
  have hF : ‖ZetaUpperR02ThreeLines.poleRemovedZeta z‖
      ≤ (2 + |z.im|) * ((1 / 9) * Real.exp (Real.pi * |z.im| / 2)) := by
    have h1 : ‖ZetaUpperR02ThreeLines.poleRemovedZeta z‖
        ≤ ‖z - 1‖ * ((1 / 9) * Real.exp (Real.pi * |z.im| / 2)) := by
      rw [ZetaUpperR02ThreeLines.poleRemovedZeta_of_ne hz1, norm_mul]
      exact mul_le_mul_of_nonneg_left hZ (norm_nonneg _)
    exact le_trans h1
      (mul_le_mul_of_nonneg_right hsub hnn_e)
  have hfin : ZetaUpperR02ThreeLines.dampedPoleRemoved z =
      ZetaUpperR02ThreeLines.poleRemovedZeta z *
        Complex.exp (((1 / 100 : ℝ) : ℂ) *
          (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2) := rfl
  rw [hfin, norm_mul]
  calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta z‖ *
      ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
        (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖
      ≤ ((2 + |z.im|) * ((1 / 9) * Real.exp (Real.pi * |z.im| / 2))) * 1.02 :=
        mul_le_mul hF hdamp (norm_nonneg _)
          (mul_nonneg (by have hnn := abs_nonneg z.im; linarith) hnn_e)
    _ = (2 + |z.im|) * ((1 / 9) * 1.02 * Real.exp (Real.pi * |z.im| / 2)) := by
        ring

/-- `exp(0.04) ≤ 1.05` (`(exp 0.04)^25 = exp 1 < 2.7183 < 3 ≤ 1.05^25`). -/
theorem exp_004_le_105 : Real.exp (0.04 : ℝ) ≤ 1.05 := by
  have hE25 : (Real.exp (0.04 : ℝ)) ^ (25 : ℕ) = Real.exp 1 := by
    have h := Real.exp_nat_mul (0.04 : ℝ) (25 : ℕ)
    have h25 : ((25 : ℕ) : ℝ) * 0.04 = 1 := by norm_num
    rw [h25] at h
    exact h.symm
  have hbern : (3 : ℝ) ≤ (1.05 : ℝ) ^ (25 : ℕ) := by norm_num
  have hlt : Real.exp (1 : ℝ) < 2.7182818286 := Real.exp_one_lt_d9
  have hle : (Real.exp (0.04 : ℝ)) ^ (25 : ℕ) ≤ (1.05 : ℝ) ^ (25 : ℕ) := by
    rw [hE25]
    linarith [hlt, hbern]
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hle

/-- `exp(-t) ≤ 1/(1+t)` for `t ≥ 0` (from `1+t ≤ exp t`). -/
theorem exp_neg_le_inv {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ 1 / (1 + t) := by
  have h1 : (1 : ℝ) + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hpos : (0 : ℝ) < 1 + t := by linarith
  have e : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hmul : Real.exp (-t) * (1 + t) ≤ 1 := by
    calc Real.exp (-t) * (1 + t) ≤ Real.exp (-t) * Real.exp t :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = 1 := e
  rw [le_div_iff₀ hpos]
  exact hmul

/-- Polynomial-times-Gaussian sup for the right edge:
`(7.75+r)·100/(100+r²) ≤ 11` for `r ≥ 0`
(i.e. `11r²-100r+325 ≥ 0`, discriminant `10000 - 14300 < 0`). -/
theorem right_sup_aux {r : ℝ} (_hr : 0 ≤ r) :
    (7.75 + r) * 100 / (100 + r ^ 2) ≤ 11 := by
  have hden : (0 : ℝ) < 100 + r ^ 2 := by
    have h := sq_nonneg r
    linarith
  rw [div_le_iff₀ hden]
  nlinarith [sq_nonneg (11 * r - 50)]

/-- Damping real part on `Re = 2`:
`Re((1/100)(s-c)²) = 0.04 - (Im+6.75)²/100`. -/
theorem damp_Re2_re {s : ℂ} (hs_re : s.re = 2) :
    ((((1 / 100 : ℝ)) : ℂ) *
      (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re
      = 0.04 - (s.im + 6.75) ^ 2 / 100 := by
  have hwre : ((((1 / 100 : ℝ)) : ℂ) *
      (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re
      = (1 / 100) * ((((s - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re)) := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsq2 : ((s - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re
      = (s.re) ^ 2 - (s.im + 6.75) ^ 2 := by
    have e1 : (s - ZetaUpperR02ThreeLines.dampCenter).re = s.re := by
      rw [Complex.sub_re, ZetaUpperR02ThreeLines.dampCenter_re, sub_zero]
    have e2 : (s - ZetaUpperR02ThreeLines.dampCenter).im = s.im + 6.75 := by
      rw [Complex.sub_im, ZetaUpperR02ThreeLines.dampCenter_im]
      ring
    rw [pow_two, Complex.mul_re, e1, e2]
    ring
  rw [hwre, hsq2, hs_re]
  ring

/-- Damping split on `Re = 2` (keeps the Gaussian decay explicit). -/
theorem damp_Re2_split {s : ℂ} (hs_re : s.re = 2) :
    ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
      (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖
      = Real.exp (0.04 : ℝ) * Real.exp (-((s.im + 6.75) ^ 2 / 100)) := by
  rw [ZetaUpperR02ThreeLines.norm_complex_exp, damp_Re2_re hs_re,
    ← Real.exp_add]
  congr 1

/-- TIER-2 right piece: whole-line `‖G(s)‖ ≤ 36` on `Re = 2`, in the exact
`hRight` preimage shape (`B = 36 ≤ A = 36` for the uniform assembly). -/
theorem damped_right_whole_36 {s : ℂ}
    (hs : s ∈ Set.preimage Complex.re {(2 : ℝ)}) :
    ‖ZetaUpperR02ThreeLines.dampedPoleRemoved s‖ ≤ 36 := by
  have hs_re : s.re = 2 := by simpa using hs
  have hs1 : s ≠ 1 := by
    intro h
    have hre : s.re = 1 := by rw [h, Complex.one_re]
    linarith
  have hZ : ‖riemannZeta s‖ ≤ 2 := by
    have h := TailZetaUpper.zeta_rightEdge_B2 (s := s) (by linarith [hs_re])
    rwa [show zeta s = riemannZeta s from rfl] at h
  have hsub : ‖s - 1‖ ≤ 1 + |s.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    have hre1 : (s - 1).re = 1 := by
      rw [Complex.sub_re, Complex.one_re, hs_re]
      norm_num
    have him1 : (s - 1).im = s.im := by
      rw [Complex.sub_im, Complex.one_im, sub_zero]
    rw [hre1, him1, abs_one] at h
    linarith
  have htri : |s.im| ≤ |s.im + 6.75| + 6.75 := by
    rw [abs_le]
    constructor
    · have h1 := neg_abs_le (s.im + 6.75)
      linarith
    · have h2 := le_abs_self (s.im + 6.75)
      linarith
  have hpos_e : (0 : ℝ) ≤ Real.exp (-((s.im + 6.75) ^ 2 / 100)) :=
    (Real.exp_pos _).le
  have hnn_1t : (0 : ℝ) ≤ 1 + |s.im| := by
    have hnn := abs_nonneg s.im
    linarith
  have hsup : (1 + |s.im|) *
      (Real.exp (0.04 : ℝ) * Real.exp (-((s.im + 6.75) ^ 2 / 100))) ≤ 11.55 := by
    have h1 : (1 : ℝ) + |s.im| ≤ 7.75 + |s.im + 6.75| := by linarith
    have hnn_7v : (0 : ℝ) ≤ 7.75 + |s.im + 6.75| := by
      have hnn := abs_nonneg (s.im + 6.75)
      linarith
    have h2 : Real.exp (-((s.im + 6.75) ^ 2 / 100))
        ≤ 100 / (100 + (s.im + 6.75) ^ 2) := by
      have h := exp_neg_le_inv
        (show (0 : ℝ) ≤ (s.im + 6.75) ^ 2 / 100 from
          div_nonneg (sq_nonneg _) (by norm_num))
      have ee : (1 : ℝ) / (1 + (s.im + 6.75) ^ 2 / 100)
          = 100 / (100 + (s.im + 6.75) ^ 2) := by
        have h1e : (1 : ℝ) + (s.im + 6.75) ^ 2 / 100
            = (100 + (s.im + 6.75) ^ 2) / 100 := by ring
        rw [h1e, one_div_div]
      rwa [ee] at h
    have h3 : ((7.75 + |s.im + 6.75|) * 100) / (100 + (s.im + 6.75) ^ 2)
        ≤ 11 := by
      have h := right_sup_aux (abs_nonneg (s.im + 6.75))
      rwa [sq_abs] at h
    calc (1 + |s.im|) *
          (Real.exp (0.04 : ℝ) * Real.exp (-((s.im + 6.75) ^ 2 / 100)))
        = Real.exp (0.04 : ℝ) * ((1 + |s.im|) *
            Real.exp (-((s.im + 6.75) ^ 2 / 100))) := by ring
      _ ≤ 1.05 * ((7.75 + |s.im + 6.75|) *
            (100 / (100 + (s.im + 6.75) ^ 2))) := by
          apply mul_le_mul _ _ _ _
          · exact exp_004_le_105
          · exact mul_le_mul h1 h2 hpos_e hnn_7v
          · exact mul_nonneg hnn_1t hpos_e
          · norm_num
      _ = 1.05 * (((7.75 + |s.im + 6.75|) * 100) / (100 + (s.im + 6.75) ^ 2)) := by
          rw [mul_div_assoc]
      _ ≤ 1.05 * 11 := mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = 11.55 := by norm_num
  have hF : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤ (1 + |s.im|) * 2 := by
    have h1 : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤ ‖s - 1‖ * 2 := by
      rw [ZetaUpperR02ThreeLines.poleRemovedZeta_of_ne hs1, norm_mul]
      exact mul_le_mul_of_nonneg_left hZ (norm_nonneg _)
    exact le_trans h1 (mul_le_mul_of_nonneg_right hsub (by norm_num))
  have hsplit := damp_Re2_split hs_re
  have hfin : ZetaUpperR02ThreeLines.dampedPoleRemoved s =
      ZetaUpperR02ThreeLines.poleRemovedZeta s *
        Complex.exp (((1 / 100 : ℝ) : ℂ) *
          (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2) := rfl
  rw [hfin, norm_mul, hsplit]
  have hnn_d : (0 : ℝ) ≤ Real.exp (0.04 : ℝ) *
      Real.exp (-((s.im + 6.75) ^ 2 / 100)) :=
    mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have e1 : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ *
      (Real.exp (0.04 : ℝ) * Real.exp (-((s.im + 6.75) ^ 2 / 100)))
      ≤ ((1 + |s.im|) * 2) *
        (Real.exp (0.04 : ℝ) * Real.exp (-((s.im + 6.75) ^ 2 / 100))) :=
    mul_le_mul_of_nonneg_right hF hnn_d
  have e2 : ((1 + |s.im|) * 2) *
      (Real.exp (0.04 : ℝ) * Real.exp (-((s.im + 6.75) ^ 2 / 100))) ≤ 36 := by
    have ee : ((1 + |s.im|) * 2) *
        (Real.exp (0.04 : ℝ) * Real.exp (-((s.im + 6.75) ^ 2 / 100)))
        = 2 * ((1 + |s.im|) *
          (Real.exp (0.04 : ℝ) * Real.exp (-((s.im + 6.75) ^ 2 / 100)))) := by
      ring
    rw [ee]
    linarith [hsup]
  linarith [e1, e2]

#print axioms BF2TailCaps.damped_left_window_preimage
#print axioms BF2TailCaps.cos_FE_generic
#print axioms BF2TailCaps.damp_left_whole_le
#print axioms BF2TailCaps.factor_left_whole_le
#print axioms BF2TailCaps.zeta_Re_neg1_whole_le
#print axioms BF2TailCaps.damped_left_whole_growth
#print axioms BF2TailCaps.exp_004_le_105
#print axioms BF2TailCaps.exp_neg_le_inv
#print axioms BF2TailCaps.right_sup_aux
#print axioms BF2TailCaps.damp_Re2_re
#print axioms BF2TailCaps.damp_Re2_split
#print axioms BF2TailCaps.damped_right_whole_36

end BF2TailCaps

/-!
# BH2 tail: windowed-strip three-lines interpolation for damped `G` (door-3/door-4 feeder, append-only)

GREP-FIRST RECORD (repo + Mathlib, via grep, 2026-09-04; everything below reuses,
nothing recreates):
* Windowed left cap `A = 36`: `Door3JointGammaCos.damped_joint_window`
  (`riemann_hypothesis_newsection.lean:3043`: `‖G‖ ≤ 36` on `Re = -1`, `|Im| ≤ 8.75`).
* Whole-line right cap `B = 36`: `BF2TailCaps.damped_right_whole_36` (`:3456`:
  `‖G‖ ≤ 36` on `Re = 2`; reused here both whole-line and in windowed restriction).
* Whole-strip three-lines EXISTS: `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`
  (`Mathlib/Analysis/Complex/Hadamard.lean:608`; whole-strip-only, so the windowed
  variant below feeds it via one explicit tail hypothesis).
* Pole-removed entire `F` EXISTS: `ZetaUpperR02ThreeLines.poleRemovedZeta_differentiable`
  (`:1172`; reused via `dampedPoleRemoved_diffContOnCl_strip` (`:1191`)).
* Threshold EXISTS: `ZetaUpperR02ThreeLines.zetaUpper_R02_ten_of_bounds` (`:1398`:
  whole-line `A ≤ 50.925` at `l = -1`, `B ≤ A` at `u = 2`, plus `BddAbove` ⇒ `‖ζ‖ ≤ 10`
  on the R02 rect).
* Damping norm identity EXISTS: `ZetaUpperR02ThreeLines.norm_complex_exp` (`:1226`).
* Tail majorant EXISTS: `BF2TailCaps.exp_neg_le_inv` (`:3398`: `exp(-t) ≤ 1/(1+t)`).
* R02 disc `s`-rect `Re ∈ [0.05,0.74]`, `Im ∈ [-8.25,-5.25]` sits strictly INSIDE the
  window (`max |Im| = 8.25 < 8.75 < 9`).

WHAT IS PROVED (unconditional, no `sorry`/`admit`/`axiom`/stand-ins):
* `damp_re_general`: damping real part `(σ²-(τ+6.75)²)/100` for general `s`.
* `damp_left_tail_le_one`: damping `≤ 1` on the left tail (`Re = -1`, `8.75 ≤ |Im|`;
  `(1-(τ+6.75)²)/100 ≤ -0.03 ≤ 0` since `(τ+6.75)² ≥ 4` there).
* `damp_top_edge_le`: damping `≤ 0.3` on the top window edge (`Im = 9`, `Re ∈ [-1,2]`;
  `(σ²-15.75²)/100 ≤ -2.440625`, so `exp ≤ 1/3.440625 ≤ 0.3`) — the quantified
  Gaussian edge-suppression (leakage) bound at `|Im| = 9`.
* `damp_bottom_edge_le_one`: damping `≤ 1` on the bottom window edge
  (`Im = -9`, `Re ∈ [-1,2]`; `(σ²-2.25²)/100 ≤ -0.010625 ≤ 0`).
* `damped_left_whole_36_of_tail` (TIER-1 assembly): AR window (`A = 36`) + explicit
  tail (`‖G‖ ≤ 36` outside the window) = whole-line left cap `36` on `Re = -1`.
* `damped_windowed_interp_36` (TIER-1 MAIN, commit-worthy alone): windowed-strip
  interpolation — `‖G s‖ ≤ 36` on the whole closed strip `[-1,2]` from the two
  windowed caps (`A = 36` left via AR + tail, `B = 36` right via BF2) + `BddAbove`
  (`36^(1-t)·36^t = 36` by `Real.rpow_add`).
* `zeta_R02_le_ten_of_tail` (TIER-2 P1): `‖ζ s‖ ≤ 10` on the R02 disc `s`-rect
  (`A = B = 36 ≤ 50.925`, margin `14.925`).

OPENS (explicit hypotheses, never `sorry`):
* `hTail`: `‖G‖ ≤ 36` on the left tail (`Re = -1`, `8.75 < |Im|`). TRUE (damping is
  `≤ 1` there by `damp_left_tail_le_one` and decays Gaussianly further out, dominating
  any fixed Stirling-scale polynomial growth of `F`) but unproved here: closing needs
  a strip polynomial bound on `F` (Stirling / FE-Phragmén, absent repo-wide).
* `hBdd`: `BddAbove` of `‖G‖` on the closed strip `[-1,2]` (strip `ζ`-growth, likewise
  absent repo-wide; satisfiable since the Gaussian dominates any fixed exponential).
-/

namespace BH2TailWindow

/-- Damping real part for general `s`:
`Re((1/100)(s-c)²) = (σ²-(τ+6.75)²)/100`. -/
theorem damp_re_general {s : ℂ} :
    ((((1 / 100 : ℝ)) : ℂ) *
      (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re
      = ((s.re) ^ 2 - (s.im + 6.75) ^ 2) / 100 := by
  have hwre : ((((1 / 100 : ℝ)) : ℂ) *
      (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re
      = (1 / 100) * ((((s - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re)) := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsq2 : ((s - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re
      = (s.re) ^ 2 - (s.im + 6.75) ^ 2 := by
    have e1 : (s - ZetaUpperR02ThreeLines.dampCenter).re = s.re := by
      rw [Complex.sub_re, ZetaUpperR02ThreeLines.dampCenter_re, sub_zero]
    have e2 : (s - ZetaUpperR02ThreeLines.dampCenter).im = s.im + 6.75 := by
      rw [Complex.sub_im, ZetaUpperR02ThreeLines.dampCenter_im]
      ring
    rw [pow_two, Complex.mul_re, e1, e2]
    ring
  rw [hwre, hsq2]
  ring

/-- Damping `≤ 1` on the left tail (`Re = -1`, `8.75 ≤ |Im|`). -/
theorem damp_left_tail_le_one {z : ℂ} (hz_re : z.re = -1) (htail : 8.75 ≤ |z.im|) :
    ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
      (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ ≤ 1 := by
  have h2 := damp_re_general (s := z)
  have hsq : (4 : ℝ) ≤ (z.im + 6.75) ^ 2 := by
    rcases le_or_gt 0 z.im with hnn | hneg
    · have habs : |z.im| = z.im := abs_of_nonneg hnn
      rw [habs] at htail
      have h15 : (15.5 : ℝ) ≤ z.im + 6.75 := by linarith
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ z.im + 6.75 - 15.5 by linarith)
        (show (0 : ℝ) ≤ z.im + 6.75 + 15.5 by linarith)]
    · have habs : |z.im| = -z.im := abs_of_neg hneg
      rw [habs] at htail
      have h2le : z.im + 6.75 ≤ (-2 : ℝ) := by linarith
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ -(z.im + 6.75 + 2) by linarith)
        (show (0 : ℝ) ≤ -(z.im + 6.75 - 2) by linarith)]
  have hsq2 : (z.re) ^ 2 = 1 := by
    rw [hz_re]
    norm_num
  have hre0 : ((((1 / 100 : ℝ)) : ℂ) *
      (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re ≤ 0 := by
    rw [h2, hsq2]
    linarith
  rw [ZetaUpperR02ThreeLines.norm_complex_exp]
  calc Real.exp ((((1 / 100 : ℝ)) : ℂ) *
        (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re
      ≤ Real.exp 0 := Real.exp_le_exp.mpr hre0
    _ = 1 := Real.exp_zero

/-- Damping `≤ 0.3` on the top window edge (`Im = 9`, `Re ∈ [-1,2]`): the quantified
Gaussian edge-suppression at `|Im| = 9`. -/
theorem damp_top_edge_le {s : ℂ} (hlo : -1 ≤ s.re) (hhi : s.re ≤ 2) (him : s.im = 9) :
    ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
      (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ ≤ 0.3 := by
  have h2 := damp_re_general (s := s)
  have hσ : (s.re) ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 - s.re by linarith)
      (show (0 : ℝ) ≤ s.re + 2 by linarith)]
  rw [him] at h2
  have e1575 : ((9 : ℝ) + 6.75) ^ 2 = 248.0625 := by norm_num
  rw [e1575] at h2
  have hre : ((((1 / 100 : ℝ)) : ℂ) *
      (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re ≤ -2.440625 := by
    rw [h2]
    linarith
  rw [ZetaUpperR02ThreeLines.norm_complex_exp]
  calc Real.exp ((((1 / 100 : ℝ)) : ℂ) *
        (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re
      ≤ Real.exp (-2.440625) := Real.exp_le_exp.mpr hre
    _ ≤ 1 / (1 + 2.440625) :=
        BF2TailCaps.exp_neg_le_inv (by norm_num)
    _ ≤ 0.3 := by norm_num

/-- Damping `≤ 1` on the bottom window edge (`Im = -9`, `Re ∈ [-1,2]`). -/
theorem damp_bottom_edge_le_one {s : ℂ} (hlo : -1 ≤ s.re) (hhi : s.re ≤ 2)
    (him : s.im = -9) :
    ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
      (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ ≤ 1 := by
  have h2 := damp_re_general (s := s)
  have hσ : (s.re) ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 - s.re by linarith)
      (show (0 : ℝ) ≤ s.re + 2 by linarith)]
  rw [him] at h2
  have e225 : ((-9 : ℝ) + 6.75) ^ 2 = 5.0625 := by norm_num
  rw [e225] at h2
  have hre : ((((1 / 100 : ℝ)) : ℂ) *
      (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re ≤ 0 := by
    rw [h2]
    linarith
  rw [ZetaUpperR02ThreeLines.norm_complex_exp]
  calc Real.exp ((((1 / 100 : ℝ)) : ℂ) *
        (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re
      ≤ Real.exp 0 := Real.exp_le_exp.mpr hre
    _ = 1 := Real.exp_zero

/-- TIER-1 assembly: AR's window cap (`A = 36`) + the explicit tail hypothesis =
whole-line left cap `36` on `Re = -1`. -/
theorem damped_left_whole_36_of_tail
    (hTail : ∀ z ∈ Set.preimage Complex.re {(-1 : ℝ)}, 8.75 < |z.im| →
      ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ 36) :
    ∀ z ∈ Set.preimage Complex.re {(-1 : ℝ)},
      ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ 36 := by
  intro z hz
  have hz_re : z.re = -1 := by simpa using hz
  by_cases h : |z.im| ≤ 8.75
  · exact Door3JointGammaCos.damped_joint_window hz_re h
  · push_neg at h
    exact hTail z hz h

/-- TIER-1 MAIN (windowed-strip three-lines interpolation): from the two windowed
caps (`A = 36` left via AR + tail, `B = 36` right via BF2) + `BddAbove`,
`‖G s‖ ≤ 36` on the whole closed strip `[-1,2]`. -/
theorem damped_windowed_interp_36
    (hTail : ∀ z ∈ Set.preimage Complex.re {(-1 : ℝ)}, 8.75 < |z.im| →
      ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ 36)
    (hBdd : BddAbove ((norm ∘ ZetaUpperR02ThreeLines.dampedPoleRemoved) ''
      Complex.HadamardThreeLines.verticalClosedStrip (-1) 2))
    {s : ℂ} (hs : s ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2) :
    ‖ZetaUpperR02ThreeLines.dampedPoleRemoved s‖ ≤ 36 := by
  have hLeft := damped_left_whole_36_of_tail hTail
  have hRight : ∀ z ∈ Set.preimage Complex.re ({(2 : ℝ)} : Set ℝ),
      ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ 36 :=
    fun z hz => BF2TailCaps.damped_right_whole_36 hz
  have h3 := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := ZetaUpperR02ThreeLines.dampedPoleRemoved) (a := 36) (b := 36)
    (l := -1) (u := 2) (by norm_num) hs
    (ZetaUpperR02ThreeLines.dampedPoleRemoved_diffContOnCl_strip (-1) 2) hBdd
    hLeft hRight
  have h36 : (0 : ℝ) < 36 := by norm_num
  have hpow : (36 : ℝ) ^ (1 - (s.re - -1) / (2 - -1)) *
      (36 : ℝ) ^ ((s.re - -1) / (2 - -1)) = 36 := by
    rw [← Real.rpow_add h36, sub_add_cancel, Real.rpow_one]
  rw [hpow] at h3
  exact h3

/-- TIER-2 P1: `‖ζ s‖ ≤ 10` on the R02 disc `s`-rect, from the explicit tail +
`BddAbove` (via `zetaUpper_R02_ten_of_bounds` at `A = B = 36 ≤ 50.925`). -/
theorem zeta_R02_le_ten_of_tail
    (hTail : ∀ z ∈ Set.preimage Complex.re {(-1 : ℝ)}, 8.75 < |z.im| →
      ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ 36)
    (hBdd : BddAbove ((norm ∘ ZetaUpperR02ThreeLines.dampedPoleRemoved) ''
      Complex.HadamardThreeLines.verticalClosedStrip (-1) 2))
    {s : ℂ} (hs_lo : 0.05 ≤ s.re) (hs_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25) :
    ‖riemannZeta s‖ ≤ 10 :=
  ZetaUpperR02ThreeLines.zetaUpper_R02_ten_of_bounds (A := 36) (B := 36)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hBdd
    (damped_left_whole_36_of_tail hTail) (fun z hz => BF2TailCaps.damped_right_whole_36 hz)
    hs_lo hs_hi him_lo him_hi

#print axioms BH2TailWindow.damp_re_general
#print axioms BH2TailWindow.damp_left_tail_le_one
#print axioms BH2TailWindow.damp_top_edge_le
#print axioms BH2TailWindow.damp_bottom_edge_le_one
#print axioms BH2TailWindow.damped_left_whole_36_of_tail
#print axioms BH2TailWindow.damped_windowed_interp_36
#print axioms BH2TailWindow.zeta_R02_le_ten_of_tail

end BH2TailWindow

/-!
BH2 P1 VERDICT + RESIDUAL (report-and-stop): TIER-1 green gives the windowed-strip
interpolation `‖G‖ ≤ 36` on `[-1,2]` from AR (`A = 36` in-window) + BF2 (`B = 36`
right) + two explicit opens; TIER-2 fires the existing threshold to conclude
`‖ζ‖ ≤ 10` on the R02 disc `s`-rect (`Re ∈ [0.05,0.74]`, `Im ∈ [-8.25,-5.25]`).
EXACT residual (numbers): (i) `hTail`: `‖G‖ ≤ 36` on `Re = -1`, `8.75 < |Im|`
(needs a Stirling-scale `F`-polynomial bound × the `≤ 1` damping proved above;
the crude-majorant whole-line truth there is exponential, so this is NOT closable
by majorants — same wall as BF2's report); (ii) `hBdd`: `BddAbove` of `‖G‖` on
`[-1,2]` (needs strip `ζ`-growth, absent repo-wide). No other opens.
-/

/-!
# BL tail (door-3 P1): Hadamard-`xi` → pole-removed-`F` bridge + conditional P1 assembly

Ownership: Agent BL tail append (import `ZeroFreeRegionHadamard` added at top-of-file;
everything else below is append-only).

What is proved here (all full proofs, no `sorry`/`admit`/`axiom`):
* `hadamardXi_eq_s_mul_GammaR_mul_poleRemoved`: unconditional algebraic bridge
  `ZeroFreeRegionHadamard.xi s = s * Complex.Gammaℝ s * F s` for `s ≠ 0, 1`
  (mirrors `xiShifted_eq_completed` / `classicalXi_eq_completed_add_half` in
  `riemann_hypothesis.lean`, and the `field_simp`+`ring` computation in
  `ZeroFreeRegionHadamard.lean` around `:2479`).
* `poleRemoved_norm_of_hadamardXi`: norm form
  `‖F s‖ = ‖xi s‖ / (‖s‖ * ‖Gammaℝ s‖)`.
* `F_of_xi_whole_plane`: the public whole-plane bound
  `ZeroFreeRegionHadamard.xi_norm_bound_whole_plane` (`:4535`) transferred to `F`,
  with the `s * Gammaℝ` denominators kept explicit.
* `StripEnvelope`: the exact residual envelope hypothesis R1
  (`∃ C K, ∀ s ∈ [-1,2], ‖F s‖ ≤ C * exp (K * |Im s|)`).
* `hBdd_of_stripEnvelope`: R1 ⇒ `BddAbove ‖G‖` on `[-1,2]` (Gaussian damping
  dominates any fixed exponential; completing-the-square cap
  `C * exp (25 * (K + 0.135)^2 + 0.04)`).
* `P1_R02_of_envelope_and_tail` + `R02_obligation_of_envelope_and_tail`:
  R1 + R2 (`hTail`) ⇒ `‖ζ‖ ≤ 10` on the R02 rect, discharging
  `DerivCauchyBridge.R02_zeta_upper_obligation` (rects match exactly).

Grep record (verified before writing; `rg -n` on this file + repo):
* `xi_norm_bound_whole_plane` — only `ZeroFreeRegionHadamard.lean:4535` (public;
  the `xi_bound_re_gt_one` at `:1522` is `private`, not usable here).
* `xiShifted_eq_completed` — only `riemann_hypothesis.lean:1961` (door-3 shifted xi,
  a different function from Hadamard `xi`); mirrored, not reused.
* Strip-uniform `Gammaℝ`/`Gamma` LOWER of shape `‖Γ‖ ≥ c * exp (-C|Im|)` — absent
  repo-wide (only pointwise/disc lowers: `CellGammaUniform`, `R02GammaLower`;
  only uppers on strips). Hence R1 stays an explicit hypothesis.
* Numerical crossover (why the crude `xi` envelope cannot yield R2 at threshold
  `8.75`): the `xi`-derived `F` envelope has shape `exp (O(|τ|^1.5))`, while the
  Gaussian damping is `exp (-(τ+6.75)^2/100)`; `τ^2/100` dominates `K|τ|^1.5` only
  for `|τ| ≳ (100K)^2`, so the interpolant on `[8.75, T]` is astronomically above
  `36`. R2 needs a Stirling-sharp *polynomial* `F`-bound (true `‖F‖ ~ |τ|^2.5`
  on `Re = -1`), which is residual R2 below — same wall as the BH2/BF2 reports.
-/

namespace BLMiddleEnvelope

/-- Algebraic bridge (unconditional): Hadamard `xi` factors as
`s * Gammaℝ s * F s` where `F` is pole-removed zeta. This is the
`xi`/`completedRiemannZeta₀` ↔ `F` bridge, mirroring `xiShifted_eq_completed`. -/
theorem hadamardXi_eq_s_mul_GammaR_mul_poleRemoved {s : ℂ} (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) (hΓ : Complex.Gamma (s / 2) ≠ 0) :
    ZeroFreeRegionHadamard.xi s
      = s * Complex.Gammaℝ s * ZetaUpperR02ThreeLines.poleRemovedZeta s := by
  have hpi0 : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpi : ((Real.pi : ℂ)) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpi0)
  have h1z : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hden : (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) ≠ 0 :=
    mul_ne_zero hpi hΓ
  have hGR : Complex.Gammaℝ s = (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) :=
    Complex.Gammaℝ_def s
  unfold ZeroFreeRegionHadamard.xi
  rw [hGR, ZetaUpperR02ThreeLines.poleRemovedZeta_of_ne hs1,
    riemannZeta_eq_completedRiemannZeta₀ hs0]
  field_simp
  ring

/-- Norm form of the bridge (unconditional). -/
theorem poleRemoved_norm_of_hadamardXi {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΓ : Complex.Gamma (s / 2) ≠ 0) :
    ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖
      = ‖ZeroFreeRegionHadamard.xi s‖ / (‖s‖ * ‖Complex.Gammaℝ s‖) := by
  have hbe := hadamardXi_eq_s_mul_GammaR_mul_poleRemoved hs0 hs1 hΓ
  have hpi0 : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpi : ((Real.pi : ℂ)) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpi0)
  have hGn : ‖Complex.Gammaℝ s‖ ≠ 0 := by
    have hne : Complex.Gammaℝ s ≠ 0 := by
      rw [Complex.Gammaℝ_def]
      exact mul_ne_zero hpi hΓ
    exact norm_ne_zero_iff.mpr hne
  have hsn : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs0
  have hdenR : ‖s‖ * ‖Complex.Gammaℝ s‖ ≠ 0 := mul_ne_zero hsn hGn
  have hnorm : ‖ZeroFreeRegionHadamard.xi s‖
      = ‖s‖ * ‖Complex.Gammaℝ s‖ * ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ := by
    rw [hbe, norm_mul, norm_mul]
  rw [hnorm, eq_div_iff hdenR]
  ring

/-- Whole-plane `xi` bound transferred to `F` (unconditional; the `s * Gammaℝ`
denominators stay explicit — bounding them below on the strip is residual R1). -/
theorem F_of_xi_whole_plane {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΓ : Complex.Gamma (s / 2) ≠ 0) :
    ∃ K : ℝ, ∃ C₀ : ℝ, (C₀ ≤ ‖s‖ →
      ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖
        ≤ Real.exp (K * ‖s‖ ^ (3 / 2 : ℝ)) / (‖s‖ * ‖Complex.Gammaℝ s‖)) := by
  obtain ⟨K, -, C₀, -, hxi⟩ := ZeroFreeRegionHadamard.xi_norm_bound_whole_plane
  exact ⟨K, C₀, fun hbig => by
    have hnorm := poleRemoved_norm_of_hadamardXi hs0 hs1 hΓ
    have hle := hxi s hbig
    have hpi0 : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hpi : ((Real.pi : ℂ)) ^ (-s / 2) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hpi0)
    have hD : 0 < ‖s‖ * ‖Complex.Gammaℝ s‖ := by
      have hGn : ‖Complex.Gammaℝ s‖ ≠ 0 := by
        have hne : Complex.Gammaℝ s ≠ 0 := by
          rw [Complex.Gammaℝ_def]
          exact mul_ne_zero hpi hΓ
        exact norm_ne_zero_iff.mpr hne
      have hGpos : 0 < ‖Complex.Gammaℝ s‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hGn)
      exact mul_pos (norm_pos_iff.mpr hs0) hGpos
    rw [hnorm]
    exact div_le_div_of_nonneg_right hle hD.le⟩

/-- Residual R1 (explicit): strip-exponential envelope for pole-removed `F` on
`[-1,2]`. Right third (`σ ∈ [1.5,2]`) follows from Euler `B = 3`
(`TailZetaUpper.zeta_rightEdge_B3`); left third (`σ ∈ [-1,-0.5]`) via FE
reflection generalizing `BF2TailCaps.zeta_Re_neg1_whole_le`; middle
(`σ ∈ [-0.5,1.5]`) needs the `Gammaℝ` lower via reflection (absent repo-wide). -/
def StripEnvelope : Prop :=
  ∃ C K : ℝ, ∀ s : ℂ, s ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2 →
    ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤ C * Real.exp (K * |s.im|)

/-- `hBdd` from the envelope (conditional on R1): Gaussian damping dominates any
fixed exponential. Completing the square:
`K|τ| + (σ² - (τ+6.75)²)/100 ≤ 25(K+0.135)² + 0.04` on `σ ∈ [-1,2]`. -/
theorem hBdd_of_stripEnvelope (hEnv : StripEnvelope) :
    BddAbove ((norm ∘ ZetaUpperR02ThreeLines.dampedPoleRemoved) ''
      Complex.HadamardThreeLines.verticalClosedStrip (-1) 2) := by
  obtain ⟨C, K, hCK⟩ := hEnv
  have h0mem : (0 : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2 := by
    unfold Complex.HadamardThreeLines.verticalClosedStrip
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor
    · simp only [Complex.zero_re]; norm_num
    · simp only [Complex.zero_re]; norm_num
  have hC : 0 ≤ C := by
    have h := hCK 0 h0mem
    have hnn : 0 ≤ C * Real.exp (K * |(0 : ℂ).im|) := le_trans (norm_nonneg _) h
    exact nonneg_of_mul_nonneg_left hnn (Real.exp_pos _)
  refine ⟨C * Real.exp (25 * (K + 0.135) ^ 2 + 0.04), ?_⟩
  intro y hy
  obtain ⟨s, hs, rfl⟩ := hy
  simp only [Function.comp_apply]
  have hmem : (-1 : ℝ) ≤ s.re ∧ s.re ≤ 2 := by
    unfold Complex.HadamardThreeLines.verticalClosedStrip at hs
    simp only [Set.mem_preimage, Set.mem_Icc] at hs
    exact hs
  obtain ⟨hlo, hhi⟩ := hmem
  have hF := hCK s hs
  have hdamp : ‖Complex.exp (((1 / 100 : ℝ) : ℂ)
      * (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖
      = Real.exp ((s.re ^ 2 - (s.im + 6.75) ^ 2) / 100) := by
    rw [ZetaUpperR02ThreeLines.norm_complex_exp, BH2TailWindow.damp_re_general]
  have hG : ZetaUpperR02ThreeLines.dampedPoleRemoved s
      = ZetaUpperR02ThreeLines.poleRemovedZeta s * Complex.exp (((1 / 100 : ℝ) : ℂ)
        * (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2) := rfl
  have hnorm : ‖ZetaUpperR02ThreeLines.dampedPoleRemoved s‖
      = ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖
        * ‖Complex.exp (((1 / 100 : ℝ) : ℂ)
          * (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ := by
    rw [hG, norm_mul]
  have hσ : s.re ^ 2 ≤ 4 := by
    have e1 : (0 : ℝ) ≤ s.re + 1 := by linarith
    have e2 : (0 : ℝ) ≤ 2 - s.re := by linarith
    nlinarith [mul_nonneg e1 e2]
  have hquad : K * |s.im| + (s.re ^ 2 - (s.im + 6.75) ^ 2) / 100
      ≤ 25 * (K + 0.135) ^ 2 + 0.04 := by
    have hcap : (0 : ℝ) ≤ 0.495625 - s.re ^ 2 / 100 := by linarith
    rcases le_total 0 s.im with ht | ht
    · rw [abs_of_nonneg ht]
      nlinarith [sq_nonneg (s.im / 10 - 5 * (K + 0.135)), hcap, ht]
    · rw [abs_of_nonpos ht]
      nlinarith [sq_nonneg ((-s.im) / 10 - 5 * (K + 0.135)), hcap, ht]
  have hexp_le : Real.exp (K * |s.im|)
      * Real.exp ((s.re ^ 2 - (s.im + 6.75) ^ 2) / 100)
      ≤ Real.exp (25 * (K + 0.135) ^ 2 + 0.04) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hquad
  rw [hnorm, hdamp]
  calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖
        * Real.exp ((s.re ^ 2 - (s.im + 6.75) ^ 2) / 100)
      ≤ (C * Real.exp (K * |s.im|))
        * Real.exp ((s.re ^ 2 - (s.im + 6.75) ^ 2) / 100) :=
        mul_le_mul hF (le_refl _) (Real.exp_nonneg _)
          (mul_nonneg hC (Real.exp_nonneg _))
    _ = C * (Real.exp (K * |s.im|)
        * Real.exp ((s.re ^ 2 - (s.im + 6.75) ^ 2) / 100)) := by ring
    _ ≤ C * Real.exp (25 * (K + 0.135) ^ 2 + 0.04) :=
        mul_le_mul_of_nonneg_left hexp_le hC

/-- Door-3 P1 conditional main (R1 + R2): envelope + left-tail cap ⇒
`‖ζ‖ ≤ 10` on the R02 disc `s`-rect. -/
theorem P1_R02_of_envelope_and_tail (hEnv : StripEnvelope)
    (hTail : ∀ z ∈ Set.preimage Complex.re {(-1 : ℝ)}, 8.75 < |z.im| →
      ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ 36)
    {s : ℂ} (hs_lo : 0.05 ≤ s.re) (hs_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25) :
    ‖riemannZeta s‖ ≤ 10 :=
  BH2TailWindow.zeta_R02_le_ten_of_tail hTail (hBdd_of_stripEnvelope hEnv)
    hs_lo hs_hi him_lo him_hi

/-- Discharge of `DerivCauchyBridge.R02_zeta_upper_obligation` (conditional on
R1 + R2; rects match exactly, `zeta = riemannZeta` by `rfl`). -/
theorem R02_obligation_of_envelope_and_tail (hEnv : StripEnvelope)
    (hTail : ∀ z ∈ Set.preimage Complex.re {(-1 : ℝ)}, 8.75 < |z.im| →
      ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ 36) :
    DerivCauchyBridge.R02_zeta_upper_obligation := by
  intro s hs_lo hs_hi him_lo him_hi
  have h : zeta s = riemannZeta s := rfl
  rw [h]
  exact P1_R02_of_envelope_and_tail hEnv hTail hs_lo hs_hi him_lo him_hi

#print axioms BLMiddleEnvelope.hadamardXi_eq_s_mul_GammaR_mul_poleRemoved
#print axioms BLMiddleEnvelope.poleRemoved_norm_of_hadamardXi
#print axioms BLMiddleEnvelope.F_of_xi_whole_plane
#print axioms BLMiddleEnvelope.hBdd_of_stripEnvelope
#print axioms BLMiddleEnvelope.P1_R02_of_envelope_and_tail
#print axioms BLMiddleEnvelope.R02_obligation_of_envelope_and_tail

end BLMiddleEnvelope

/-!
BL P1 VERDICT + RESIDUAL (report-and-stop): unconditional bridge `xi = s·Gammaℝ·F`
+ `xi`-to-`F` transfer banked; `hBdd` and the full P1 compose proved conditional.
EXACT residual (numbers): (R1) `BLMiddleEnvelope.StripEnvelope`
(`∃ C K, ∀ s ∈ [-1,2], ‖F s‖ ≤ C·exp(K·|Im s|)`) — needs the strip `Gammaℝ` lower
(reflection route; absent repo-wide); (R2) `hTail` (`‖G‖ ≤ 36` on `Re = -1`,
`8.75 < |Im|`) — needs a Stirling-sharp `F`-polynomial bound (true `‖F‖~|τ|^2.5`
there, so the crude `exp(O(|τ|^1.5))` envelope genuinely cannot close it at
threshold `8.75`). No other opens; no `sorry`/`admit`/`axiom` in this tail.
-/

/-!
# BN tail (door-3 R1): outer thirds of `StripEnvelope` (right via Euler, left via FE)

Ownership: Agent BN tail append (append-only after the BL verdict block; nothing above
touched; `import ZeroFreeRegionHadamard` at line 5 reused, not re-added).

What is proved here (all full proofs, no `sorry`/`admit`/`axiom`):
* `F_rightThird_le` — right third (`σ ∈ [3/2,2]`) of `StripEnvelope`:
  `‖F s‖ ≤ 3 * exp |Im s|`, via `F = (s-1)·ζ` (`poleRemovedZeta_of_ne`) and Euler
  `TailZetaUpper.zeta_rightEdge_B3` (`‖ζ‖ ≤ 3`), plus `1 + |τ| ≤ exp |τ|`.
* `realGamma_le_one_of_mem_32` — `Real.Gamma x ≤ 1` on `[3/2,2]` by the
  `Real.convexOn_Gamma` secant (mirrors `RowFE_realGamma_0895_le`).
* `cpow_two_pi_neg_le_one_of_re_ge` — crude `‖(2π)^{-w}‖ ≤ 1` for `3/2 ≤ Re w`
  (no numeral cap needed: `StripEnvelope` only needs exp shape).
* `gamma_upper_of_mem_32` — `‖Γ w‖ ≤ 1` for `Re w ∈ [3/2,2]`
  (generalizes `Door3SharpWindow.gamma_uniform_Re2` from the line `Re = 2`).
* `factor_upper_of_mem_32` — `‖RowFEFactor w‖ ≤ 2 * exp (π|Im w|/2)` on the range
  (mirrors `BF2TailCaps.factor_left_whole_le` with range caps).
* `zeta_leftThird_le` — `‖ζ z‖ ≤ 6 * exp (π|Im z|/2)` for `Re z ∈ [-1,-1/2]`,
  via Mathlib `riemannZeta_one_sub` reflection to `Re(1-z) ∈ [3/2,2]`
  (generalizes `BF2TailCaps.zeta_Re_neg1_whole_le` from `Re = -1`; Euler side B3).
* `F_leftThird_le` — left third of `StripEnvelope`:
  `‖F z‖ ≤ 18 * exp ((1 + π/2) * |Im z|)`.
* `F_outerThirds_le` — uniform outer-thirds corollary (feeds R1 directly):
  `(Re ≤ -1/2 ∨ 3/2 ≤ Re) → ‖F s‖ ≤ 18 * exp ((1+π/2) * |Im s|)`.

Grep record (verified by `rg -n` before writing):
* `zeta_rightEdge_B3` — only this file `:1033` (B2 at `:1041`).
* `poleRemovedZeta_of_ne` — this file `:1141`.
* `Complex.norm_le_abs_re_add_abs_im` — Mathlib; used in-file at `:3349`.
* `Real.add_one_le_exp`, `Real.exp_le_exp`, `Real.exp_add` — Mathlib.
* `riemannZeta_one_sub` — Mathlib; FE assembly copied from `:3313`-`:3324`.
* `RowFEFactor` (`interval_arith.lean:30856`), `RowFE_norm_cos_le` (`:30905`),
  `R00GammaLower.norm_Gamma_le_realGamma` (`:541`, public),
  `RowFE_Gamma_upper_of` (`:31257`, exact-`Re` only — hence the range version here).
* `Real.convexOn_Gamma` — Mathlib; secant pattern mirrors `:31232`-`:31253`.
* `Complex.norm_cpow_eq_rpow_re_of_pos` — Mathlib; cpow pattern mirrors `:1982`.
* `Real.rpow_le_rpow_of_exponent_le` — Mathlib.
* `BNStripThirds` + all lemma names below: absent repo-wide (checked).
-/

namespace BNStripThirds

/-- Right third of `StripEnvelope` (`σ ∈ [3/2,2]`): Euler `B = 3` direct. -/
theorem F_rightThird_le {s : ℂ}
    (hs : s ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2)
    (hlo : 3 / 2 ≤ s.re) :
    ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤ 3 * Real.exp |s.im| := by
  have hmem : (-1 : ℝ) ≤ s.re ∧ s.re ≤ 2 := by
    unfold Complex.HadamardThreeLines.verticalClosedStrip at hs
    simp only [Set.mem_preimage, Set.mem_Icc] at hs
    exact hs
  have hs1 : s ≠ 1 := by
    intro h
    have hre : s.re = 1 := by rw [h, Complex.one_re]
    linarith
  have hF := ZetaUpperR02ThreeLines.poleRemovedZeta_of_ne hs1
  have hZ : ‖riemannZeta s‖ ≤ 3 := by
    have h := TailZetaUpper.zeta_rightEdge_B3 (s := s) hlo
    rwa [show zeta s = riemannZeta s from rfl] at h
  have hsub : ‖s - 1‖ ≤ 1 + |s.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    have hre1 : (s - 1).re = s.re - 1 := by
      rw [Complex.sub_re, Complex.one_re]
    have him1 : (s - 1).im = s.im := by
      rw [Complex.sub_im, Complex.one_im, sub_zero]
    rw [hre1, him1] at h
    have habs : |s.re - 1| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hmem.2, hlo]
    linarith
  have hexp : (1 : ℝ) + |s.im| ≤ Real.exp |s.im| := by
    have h := Real.add_one_le_exp |s.im|
    linarith
  rw [hF, norm_mul]
  calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ (1 + |s.im|) * 3 :=
        mul_le_mul hsub hZ (norm_nonneg _) (by linarith [abs_nonneg s.im])
    _ ≤ Real.exp |s.im| * 3 :=
        mul_le_mul_of_nonneg_right hexp (by norm_num)
    _ = 3 * Real.exp |s.im| := by ring

/-- Real-Gamma secant cap: `Real.Gamma x ≤ 1` for `x ∈ [3/2,2]`
(convexity on `[1,2]` with `Gamma 1 = Gamma 2 = 1`). -/
theorem realGamma_le_one_of_mem_32 {x : ℝ} (hx1 : 3 / 2 ≤ x) (hx2 : x ≤ 2) :
    Real.Gamma x ≤ 1 := by
  have hy_mem1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have hy_mem2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have hconv := Real.convexOn_Gamma
  have ha_nn : (0 : ℝ) ≤ 2 - x := by linarith
  have hb_nn : (0 : ℝ) ≤ x - 1 := by linarith
  have hab : (2 - x) + (x - 1) = 1 := by ring
  have h := hconv.2 hy_mem1 hy_mem2 ha_nn hb_nn hab
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
  have heq : (2 - x) * 1 + (x - 1) * 2 = x := by ring
  rw [heq] at h
  have hrhs : (2 - x) * 1 + (x - 1) * 1 = (1 : ℝ) := by ring
  rw [hrhs] at h
  exact h

/-- Crude whole-range cpow cap: `‖(2π)^{-w}‖ ≤ 1` for `3/2 ≤ Re w`. -/
theorem cpow_two_pi_neg_le_one_of_re_ge {w : ℂ} (hw : 3 / 2 ≤ w.re) :
    ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ ≤ 1 := by
  have hbase_pos : (0 : ℝ) < 2 * Real.pi := by
    have h := Real.pi_pos
    linarith
  have h2pi : ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    push_cast
    ring
  have hnorm : ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ = (2 * Real.pi) ^ (-(w.re)) := by
    rw [← h2pi, Complex.norm_cpow_eq_rpow_re_of_pos hbase_pos, Complex.neg_re]
  rw [hnorm]
  have hbase1 : (1 : ℝ) ≤ 2 * Real.pi := by
    have h := Real.pi_gt_three
    linarith
  have hle : (2 * Real.pi) ^ (-(w.re)) ≤ (2 * Real.pi) ^ (0 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase1 (by linarith)
  rwa [Real.rpow_zero] at hle

/-- Range Gamma upper: `‖Γ w‖ ≤ 1` for `Re w ∈ [3/2,2]`
(generalizes `Door3SharpWindow.gamma_uniform_Re2`). -/
theorem gamma_upper_of_mem_32 {w : ℂ} (hw1 : 3 / 2 ≤ w.re) (hw2 : w.re ≤ 2) :
    ‖Complex.Gamma w‖ ≤ 1 :=
  le_trans (R00GammaLower.norm_Gamma_le_realGamma (by linarith))
    (realGamma_le_one_of_mem_32 hw1 hw2)

/-- Range FE-factor upper on `Re ∈ [3/2,2]`
(mirrors `BF2TailCaps.factor_left_whole_le`). -/
theorem factor_upper_of_mem_32 {w : ℂ} (hw1 : 3 / 2 ≤ w.re) (hw2 : w.re ≤ 2) :
    ‖RowFE.RowFEFactor w‖ ≤ 2 * Real.exp (Real.pi * |w.im| / 2) := by
  have hcpow : ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ ≤ 1 :=
    cpow_two_pi_neg_le_one_of_re_ge hw1
  have hG : ‖Complex.Gamma w‖ ≤ 1 := gamma_upper_of_mem_32 hw1 hw2
  have hcos : ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖
      ≤ Real.exp (Real.pi * |w.im| / 2) := by
    have e : (Real.pi : ℂ) * w / 2 = (Real.pi : ℂ) * (w / 2) :=
      mul_div_assoc _ _ _
    rw [e]
    exact BF2TailCaps.cos_FE_generic
  have h2norm : ‖(2 : ℂ)‖ = 2 := by
    have e : ((2 : ℕ) : ℂ) = (2 : ℂ) := by norm_num
    rw [← e, RCLike.norm_natCast]
    norm_num
  have hnorm_eq : ‖RowFE.RowFEFactor w‖
      = ‖(2 : ℂ)‖ * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖
        * (‖Complex.Gamma w‖ * ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖) := by
    unfold RowFE.RowFEFactor
    rw [norm_mul, norm_mul, norm_mul]
    ring
  rw [hnorm_eq, h2norm]
  have hA : (2 : ℝ) * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ ≤ 2 * 1 :=
    mul_le_mul_of_nonneg_left hcpow (by norm_num)
  have hB : ‖Complex.Gamma w‖ * ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖
      ≤ 1 * Real.exp (Real.pi * |w.im| / 2) :=
    mul_le_mul hG hcos (norm_nonneg _) (by norm_num)
  calc (2 : ℝ) * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖
        * (‖Complex.Gamma w‖ * ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖)
      ≤ (2 * 1) * (1 * Real.exp (Real.pi * |w.im| / 2)) :=
        mul_le_mul hA hB (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = 2 * Real.exp (Real.pi * |w.im| / 2) := by ring

/-- Left-third zeta cap via FE reflection to `Re ∈ [3/2,2]`
(generalizes `BF2TailCaps.zeta_Re_neg1_whole_le` from the line `Re = -1`). -/
theorem zeta_leftThird_le {z : ℂ} (hz1 : -1 ≤ z.re) (hz2 : z.re ≤ -1 / 2) :
    ‖riemannZeta z‖ ≤ 6 * Real.exp (Real.pi * |z.im| / 2) := by
  have hz_lo : (3 : ℝ) / 2 ≤ ((1 : ℂ) - z).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hz_hi : ((1 : ℂ) - z).re ≤ 2 := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hw_im : ((1 : ℂ) - z).im = -z.im := by
    rw [Complex.sub_im, Complex.one_im, zero_sub]
  have hs_neg : ∀ n : ℕ, (1 - z) ≠ -((n : ℂ)) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re,
      Complex.natCast_re] at hre
    have hnn : (0 : ℝ) ≤ (((n : ℕ)) : ℝ) := Nat.cast_nonneg n
    linarith
  have hs1' : (1 - z) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re] at hre
    linarith
  have hFE' : riemannZeta z
      = RowFE.RowFEFactor (1 - z) * riemannZeta (1 - z) := by
    have hFE := riemannZeta_one_sub (s := 1 - z) hs_neg hs1'
    have h1sub : (1 : ℂ) - (1 - z) = z := by ring
    rw [h1sub] at hFE
    have h2 : (2 * (2 * (Real.pi : ℂ)) ^ (-(1 - z)) * Complex.Gamma (1 - z)
        * Complex.cos ((Real.pi : ℂ) * (1 - z) / 2) * riemannZeta (1 - z))
        = RowFE.RowFEFactor (1 - z) * riemannZeta (1 - z) := by
      unfold RowFE.RowFEFactor
      ring
    rw [← h2]
    exact hFE
  have hZrefl : ‖riemannZeta (1 - z)‖ ≤ 3 := by
    have h := TailZetaUpper.zeta_rightEdge_B3 (s := 1 - z) hz_lo
    rwa [show zeta (1 - z) = riemannZeta (1 - z) from rfl] at h
  have him_eq : |((1 : ℂ) - z).im| = |z.im| := by
    rw [hw_im, abs_neg]
  have hFactor : ‖RowFE.RowFEFactor (1 - z)‖
      ≤ 2 * Real.exp (Real.pi * |z.im| / 2) := by
    have h := factor_upper_of_mem_32 (w := 1 - z) hz_lo hz_hi
    rwa [him_eq] at h
  rw [hFE', norm_mul]
  calc ‖RowFE.RowFEFactor (1 - z)‖ * ‖riemannZeta (1 - z)‖
      ≤ (2 * Real.exp (Real.pi * |z.im| / 2)) * 3 :=
        mul_le_mul hFactor hZrefl (norm_nonneg _) (by positivity)
    _ = 6 * Real.exp (Real.pi * |z.im| / 2) := by ring

/-- Left third of `StripEnvelope` (`σ ∈ [-1,-1/2]`). -/
theorem F_leftThird_le {z : ℂ}
    (hs : z ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2)
    (hz2 : z.re ≤ -1 / 2) :
    ‖ZetaUpperR02ThreeLines.poleRemovedZeta z‖
      ≤ 18 * Real.exp ((1 + Real.pi / 2) * |z.im|) := by
  have hmem : (-1 : ℝ) ≤ z.re ∧ z.re ≤ 2 := by
    unfold Complex.HadamardThreeLines.verticalClosedStrip at hs
    simp only [Set.mem_preimage, Set.mem_Icc] at hs
    exact hs
  have hz1 : z ≠ 1 := by
    intro h
    have hre : z.re = 1 := by rw [h, Complex.one_re]
    linarith
  have hF := ZetaUpperR02ThreeLines.poleRemovedZeta_of_ne hz1
  have hZ := zeta_leftThird_le hmem.1 hz2
  have hsub : ‖z - 1‖ ≤ 2 + |z.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im (z - 1)
    have hre1 : (z - 1).re = z.re - 1 := by
      rw [Complex.sub_re, Complex.one_re]
    have him1 : (z - 1).im = z.im := by
      rw [Complex.sub_im, Complex.one_im, sub_zero]
    rw [hre1, him1] at h
    have habs : |z.re - 1| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hmem.1, hz2]
    linarith
  have h23 : (2 : ℝ) + |z.im| ≤ 3 * Real.exp |z.im| := by
    have hexp : |z.im| + 1 ≤ Real.exp |z.im| := Real.add_one_le_exp _
    have hnn : (0 : ℝ) ≤ |z.im| := abs_nonneg _
    linarith
  have hsub3 : ‖z - 1‖ ≤ 3 * Real.exp |z.im| := le_trans hsub h23
  have hexpK : Real.exp |z.im| * Real.exp (Real.pi * |z.im| / 2)
      = Real.exp ((1 + Real.pi / 2) * |z.im|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hF, norm_mul]
  calc ‖z - 1‖ * ‖riemannZeta z‖
        ≤ (3 * Real.exp |z.im|) * (6 * Real.exp (Real.pi * |z.im| / 2)) :=
        mul_le_mul hsub3 hZ (norm_nonneg _) (by positivity)
    _ = 18 * (Real.exp |z.im| * Real.exp (Real.pi * |z.im| / 2)) := by ring
    _ = 18 * Real.exp ((1 + Real.pi / 2) * |z.im|) := by rw [hexpK]

/-- Uniform outer-thirds corollary: the two proved thirds at one constant pair
(`C = 18`, `K = 1 + π/2`), directly feeding R1 off the middle third. -/
theorem F_outerThirds_le {s : ℂ}
    (hs : s ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2)
    (ho : s.re ≤ -1 / 2 ∨ 3 / 2 ≤ s.re) :
    ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖
      ≤ 18 * Real.exp ((1 + Real.pi / 2) * |s.im|) := by
  rcases ho with h | h
  · exact F_leftThird_le hs h
  · have hR := F_rightThird_le hs h
    have h3 : (3 : ℝ) ≤ 18 * Real.exp ((Real.pi / 2) * |s.im|) := by
      have he : (1 : ℝ) ≤ Real.exp ((Real.pi / 2) * |s.im|) := by
        have hexp := Real.add_one_le_exp ((Real.pi / 2) * |s.im|)
        have hnn : (0 : ℝ) ≤ (Real.pi / 2) * |s.im| := by positivity
        linarith
      linarith
    have hmono : Real.exp |s.im| ≤ Real.exp ((1 + Real.pi / 2) * |s.im|) := by
      apply Real.exp_le_exp.mpr
      have hnn : (0 : ℝ) ≤ |s.im| := abs_nonneg _
      have hpi : (0 : ℝ) ≤ Real.pi / 2 * |s.im| := by positivity
      linarith
    calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤ 3 * Real.exp |s.im| := hR
      _ ≤ (18 * Real.exp ((Real.pi / 2) * |s.im|)) * Real.exp |s.im| :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
      _ = 18 * Real.exp ((1 + Real.pi / 2) * |s.im|) := by
        have heq : Real.exp ((Real.pi / 2) * |s.im|) * Real.exp |s.im|
            = Real.exp ((1 + Real.pi / 2) * |s.im|) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [mul_assoc, heq]

#print axioms BNStripThirds.F_rightThird_le
#print axioms BNStripThirds.realGamma_le_one_of_mem_32
#print axioms BNStripThirds.cpow_two_pi_neg_le_one_of_re_ge
#print axioms BNStripThirds.gamma_upper_of_mem_32
#print axioms BNStripThirds.factor_upper_of_mem_32
#print axioms BNStripThirds.zeta_leftThird_le
#print axioms BNStripThirds.F_leftThird_le
#print axioms BNStripThirds.F_outerThirds_le

end BNStripThirds

/-!
BN VERDICT + RESIDUAL (report-and-stop): outer thirds (`Re ∈ [-1,-1/2] ∪ [3/2,2]`)
of `BLMiddleEnvelope.StripEnvelope` proved with exp-linear shape
(`3·exp|τ|` right, `18·exp((1+π/2)|τ|)` uniform). Middle third
(`σ ∈ [-1/2,3/2]`) OPEN — no committed route; two verified dead ends:
(a) the `xi`-transfer (`F_of_xi_whole_plane`): numerator `exp (K|s|^{3/2})`
divided by any `c·exp(-C|τ|)` Gamma lower stays `exp (O(|τ|^{1.5}))`, which no
constants fit into `C·exp(K|τ|)` — so a strip `Gammaℝ` lower cannot discharge
R1 that way (that subtask is true but useless for R1, hence not attempted);
(b) three-lines (`norm_le_interp_of_mem_verticalClosedStrip'`) needs interior
`BddAbove`, i.e. `StripEnvelope` itself (circular). Closing the middle needs a
Phragmén–Lindelöf/convexity bound with finite-order control — new material.
No `sorry`/`admit`/`axiom` in this tail.
-/

/-!
# BP2 tail (door-3 R1 middle): exp-3/2 middle-third envelope via xi-transfer (conditional)

Ownership: Agent BP2 tail append (append-only after the BN verdict block; nothing above
touched; `import ZeroFreeRegionHadamard` at line 5 reused, not re-added).

What is proved here (all full proofs, no `sorry`/`admit`/`axiom`):
* `norm_le_two_add_abs_im_of_middle` — `‖s‖ ≤ 2 + |Im s|` on `Re ∈ [-1/2,3/2]`
  (via `Complex.norm_le_abs_re_add_abs_im` + `|Re| ≤ 3/2`).
* `middle_norm_rpow32_le` — rpow conversion
  `‖s‖^(3/2) ≤ 4^(3/2) + 2^(3/2)·|Im|^(3/2)` on the middle third.
  Split at `|Im| ≤ 2`: small case via `(2+t) ≤ 4`, large via `(2+t) ≤ 2·t`
  (`Real.rpow_le_rpow` + `Real.mul_rpow`; no convexity needed).
* `F_middleThird_exp32_of_GammaLower` — middle-third envelope in exp-3/2 form ONLY:
  `‖F s‖ ≤ C·exp(K·|Im s|^(3/2))` on `σ ∈ [-1/2,3/2]`, conditional on ONE explicit
  premise (strip `Gammaℝ` lower `c ≤ ‖Gammaℝ s‖`, absent repo-wide).
  Via BL's xi-transfer (`BLMiddleEnvelope.poleRemoved_norm_of_hadamardXi` +
  `ZeroFreeRegionHadamard.xi_norm_bound_whole_plane`): large `‖s‖ > max C0 1`
  uses the transfer (denominators `‖s‖ ≥ 1`, `‖Gammaℝ‖ ≥ c`; `s = 0/1` and
  `Gamma(s/2) = 0` excluded by the norm/gamma bounds); small `‖s‖ ≤ max C0 1`
  uses compactness (`IsCompact.exists_bound_of_continuousOn` on
  `closedBall ∩ strip`, `F` entire via `poleRemovedZeta_differentiable`),
  absorbed since `exp ≥ 1`. This is the minimum-viable ONE envelope lemma;
  `hBdd`/P1-composition NOT attempted (per brief: report-and-stop).

Grep record (verified by `rg -n` before writing):
* `xi_norm_bound_whole_plane` — only `ZeroFreeRegionHadamard.lean:4535` (public).
* `poleRemoved_norm_of_hadamardXi` / `StripEnvelope` — this file `:3863` / `:3915` (BL).
* `F_outerThirds_le` — this file `:4286` (BN, outer thirds only; middle open).
* `zeta_R02_le_ten_of_tail` — this file `:3762` (BH2, needs `hTail` + `hBdd`).
* Strip-uniform `Gammaℝ` LOWER `‖Gammaℝ‖ ≥ c·exp(-C|Im|)` — absent repo-wide
  (only pointwise/disc lowers); hence the explicit `hGlow` premise (conditional is fine).
* `BP2Middle32` + all lemma names below: absent repo-wide (checked).
-/

namespace BP2Middle32

/-- `‖s‖ ≤ 2 + |Im s|` on the middle third (`Re ∈ [-1/2,3/2]`). -/
theorem norm_le_two_add_abs_im_of_middle {s : ℂ}
    (hmid1 : -1 / 2 ≤ s.re) (hmid2 : s.re ≤ 3 / 2) :
    ‖s‖ ≤ 2 + |s.im| := by
  have h := Complex.norm_le_abs_re_add_abs_im s
  have habs : |s.re| ≤ 3 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  linarith

/-- Rpow conversion on the middle third:
`‖s‖^(3/2) ≤ 4^(3/2) + 2^(3/2)·|Im|^(3/2)`.
Split at `|Im| ≤ 2`: small via `(2+t) ≤ 4`, large via `(2+t) ≤ 2·t`. -/
theorem middle_norm_rpow32_le {s : ℂ}
    (hmid1 : -1 / 2 ≤ s.re) (hmid2 : s.re ≤ 3 / 2) :
    ‖s‖ ^ (3 / 2 : ℝ) ≤ (4 : ℝ) ^ (3 / 2 : ℝ) + (2 : ℝ) ^ (3 / 2 : ℝ) * |s.im| ^ (3 / 2 : ℝ) := by
  have hnorm : ‖s‖ ≤ 2 + |s.im| := norm_le_two_add_abs_im_of_middle hmid1 hmid2
  have hnn : (0 : ℝ) ≤ ‖s‖ := norm_nonneg _
  have hexpnn : (0 : ℝ) ≤ (3 / 2 : ℝ) := by norm_num
  have hle : ‖s‖ ^ (3 / 2 : ℝ) ≤ (2 + |s.im|) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hnn hnorm hexpnn
  have him_nn : (0 : ℝ) ≤ |s.im| := abs_nonneg _
  have h2t_nn : (0 : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * |s.im| ^ (3 / 2 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg him_nn _)
  rcases le_total |s.im| 2 with hsmall | hlarge
  · have h24 : (2 : ℝ) + |s.im| ≤ 4 := by linarith
    have h2nn : (0 : ℝ) ≤ 2 + |s.im| := by linarith [abs_nonneg s.im]
    have hmono : (2 + |s.im|) ^ (3 / 2 : ℝ) ≤ (4 : ℝ) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow h2nn h24 hexpnn
    linarith
  · have h2le : (2 : ℝ) + |s.im| ≤ 2 * |s.im| := by linarith
    have h2nn : (0 : ℝ) ≤ 2 + |s.im| := by linarith [abs_nonneg s.im]
    have hmono2 : (2 + |s.im|) ^ (3 / 2 : ℝ) ≤ (2 * |s.im|) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow h2nn h2le hexpnn
    have hmul : (2 * |s.im|) ^ (3 / 2 : ℝ) = (2 : ℝ) ^ (3 / 2 : ℝ) * |s.im| ^ (3 / 2 : ℝ) :=
      Real.mul_rpow (by norm_num) him_nn
    have h4nn : (0 : ℝ) ≤ (4 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
    linarith

/-- Middle-third envelope in exp-3/2 form (conditional on the strip `Gammaℝ` lower,
absent repo-wide): `‖F s‖ ≤ C·exp(K·|Im s|^(3/2))` on `σ ∈ [-1/2,3/2]`.
Large `‖s‖` via BL's xi-transfer; small `‖s‖` via compactness (entire `F`). -/
theorem F_middleThird_exp32_of_GammaLower {c : ℝ} (hc : 0 < c)
    (hGlow : ∀ s : ℂ, s ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2 →
      -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → c ≤ ‖Complex.Gammaℝ s‖) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ s : ℂ,
      s ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2 →
      -1 / 2 ≤ s.re → s.re ≤ 3 / 2 →
      ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤ C * Real.exp (K * (|s.im| ^ (3 / 2 : ℝ))) := by
  obtain ⟨Kxi, hKxi, C0, hC0, hxi⟩ := ZeroFreeRegionHadamard.xi_norm_bound_whole_plane
  have hKxi_nn : (0 : ℝ) ≤ Kxi := hKxi
  have hB2nn : (0 : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hKnn : (0 : ℝ) ≤ Kxi * (2 : ℝ) ^ (3 / 2 : ℝ) := mul_nonneg hKxi_nn hB2nn
  have hstrip_closed : IsClosed (Complex.HadamardThreeLines.verticalClosedStrip (-1) 2) := by
    unfold Complex.HadamardThreeLines.verticalClosedStrip
    exact IsClosed.preimage Complex.continuous_re isClosed_Icc
  have hKcompact : IsCompact (Metric.closedBall (0 : ℂ) (max C0 1) ∩
      Complex.HadamardThreeLines.verticalClosedStrip (-1) 2) :=
    (isCompact_closedBall _ _).inter_right hstrip_closed
  have hFcont : Continuous ZetaUpperR02ThreeLines.poleRemovedZeta :=
    ZetaUpperR02ThreeLines.poleRemovedZeta_differentiable.continuous
  obtain ⟨M, hM⟩ := hKcompact.exists_bound_of_continuousOn hFcont.continuousOn
  have hClarge_nn : (0 : ℝ) ≤ Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / c :=
    div_nonneg (Real.exp_nonneg _) hc.le
  have hCfin_nn : (0 : ℝ) ≤ max (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / c) M :=
    le_trans hClarge_nn (le_max_left _ _)
  refine ⟨max (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / c) M,
    Kxi * (2 : ℝ) ^ (3 / 2 : ℝ), hCfin_nn, hKnn, fun s hs hmid1 hmid2 => ?_⟩
  have hnorm_rpow := middle_norm_rpow32_le hmid1 hmid2
  by_cases hsmall : ‖s‖ ≤ max C0 1
  · have hdist : dist s (0 : ℂ) ≤ max C0 1 := by
      have e : dist s (0 : ℂ) = ‖s‖ := by
        rw [dist_eq_norm, sub_zero]
      rw [e]
      exact hsmall
    have hmemK : s ∈ Metric.closedBall (0 : ℂ) (max C0 1) ∩
        Complex.HadamardThreeLines.verticalClosedStrip (-1) 2 :=
      ⟨Metric.mem_closedBall.mpr hdist, hs⟩
    have hMs : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤ M := hM s hmemK
    have harg_nn : (0 : ℝ) ≤ (Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ)) :=
      mul_nonneg hKnn (Real.rpow_nonneg (abs_nonneg _) _)
    have hexp1 : (1 : ℝ) ≤ Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ))) := by
      have h := Real.add_one_le_exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ)))
      linarith
    calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤ M := hMs
      _ ≤ max (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / c) M := le_max_right _ _
      _ = max (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / c) M * 1 := (mul_one _).symm
      _ ≤ max (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / c) M *
          Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hexp1 hCfin_nn
  · have hlarge : max C0 1 < ‖s‖ := not_le.mp hsmall
    have hC0le : C0 ≤ ‖s‖ := le_trans (le_max_left _ _) (le_of_lt hlarge)
    have hs1le : (1 : ℝ) ≤ ‖s‖ := le_trans (le_max_right _ _) (le_of_lt hlarge)
    have hmax_nn : (0 : ℝ) ≤ max C0 1 :=
      le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right _ _)
    have hs_pos : (0 : ℝ) < ‖s‖ := lt_of_le_of_lt hmax_nn hlarge
    have hs0 : s ≠ 0 := by
      intro h
      rw [h, norm_zero] at hlarge
      linarith
    have hs1 : s ≠ 1 := by
      intro h
      rw [h, norm_one] at hlarge
      have h1le : (1 : ℝ) ≤ max C0 1 := le_max_right _ _
      linarith
    have hGlow_le : c ≤ ‖Complex.Gammaℝ s‖ := hGlow s hs hmid1 hmid2
    have hGRne : Complex.Gammaℝ s ≠ 0 := by
      intro h
      rw [h, norm_zero] at hGlow_le
      linarith
    have hGne : Complex.Gamma (s / 2) ≠ 0 := by
      intro hG0
      apply hGRne
      rw [Complex.Gammaℝ_def, hG0, mul_zero]
    have hnorm_eq := BLMiddleEnvelope.poleRemoved_norm_of_hadamardXi hs0 hs1 hGne
    have hxi_le := hxi s hC0le
    have hGn_pos : (0 : ℝ) < ‖Complex.Gammaℝ s‖ := lt_of_lt_of_le hc hGlow_le
    have hDpos : (0 : ℝ) < ‖s‖ * ‖Complex.Gammaℝ s‖ := mul_pos hs_pos hGn_pos
    have hDle : ‖s‖ * c ≤ ‖s‖ * ‖Complex.Gammaℝ s‖ :=
      mul_le_mul_of_nonneg_left hGlow_le hs_pos.le
    have hDc : c ≤ ‖s‖ * c := by
      calc c = 1 * c := (one_mul _).symm
        _ ≤ ‖s‖ * c := mul_le_mul_of_nonneg_right hs1le hc.le
    have hDle2 : c ≤ ‖s‖ * ‖Complex.Gammaℝ s‖ := le_trans hDc hDle
    have hFle1 : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤
        Real.exp (Kxi * ‖s‖ ^ (3 / 2 : ℝ)) / (‖s‖ * ‖Complex.Gammaℝ s‖) := by
      rw [hnorm_eq]
      exact div_le_div_of_nonneg_right hxi_le hDpos.le
    have hFle2 : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤
        Real.exp (Kxi * ‖s‖ ^ (3 / 2 : ℝ)) / c :=
      le_trans hFle1 (div_le_div_of_nonneg_left (Real.exp_nonneg _) hc hDle2)
    have hexp_mono : Kxi * ‖s‖ ^ (3 / 2 : ℝ) ≤ Kxi * (4 : ℝ) ^ (3 / 2 : ℝ) +
        (Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ)) := by
      have hmul_le : Kxi * ‖s‖ ^ (3 / 2 : ℝ) ≤
          Kxi * ((4 : ℝ) ^ (3 / 2 : ℝ) + (2 : ℝ) ^ (3 / 2 : ℝ) * |s.im| ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hnorm_rpow hKxi_nn
      have heq : Kxi * ((4 : ℝ) ^ (3 / 2 : ℝ) + (2 : ℝ) ^ (3 / 2 : ℝ) * |s.im| ^ (3 / 2 : ℝ)) =
          Kxi * (4 : ℝ) ^ (3 / 2 : ℝ) + (Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ)) := by
        ring
      rw [heq] at hmul_le
      exact hmul_le
    have hexp_le : Real.exp (Kxi * ‖s‖ ^ (3 / 2 : ℝ)) ≤
        Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) *
        Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ))) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hexp_mono
    have hFle3 : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤
        (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / c) *
        Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ))) := by
      calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤
            Real.exp (Kxi * ‖s‖ ^ (3 / 2 : ℝ)) / c := hFle2
        _ ≤ (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) *
            Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ)))) / c :=
          div_le_div_of_nonneg_right hexp_le hc.le
        _ = (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / c) *
            Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ))) := by
          ring
    calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤
          (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / c) *
          Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ))) := hFle3
      _ ≤ max (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / c) M *
          Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)

#print axioms BP2Middle32.norm_le_two_add_abs_im_of_middle
#print axioms BP2Middle32.middle_norm_rpow32_le
#print axioms BP2Middle32.F_middleThird_exp32_of_GammaLower

end BP2Middle32

/-!
BP2 VERDICT + RESIDUAL (report-and-stop): middle-third envelope in exp-3/2 form ONLY
(`‖F s‖ ≤ C·exp(K·|Im s|^(3/2))` on `σ ∈ [-1/2,3/2]`) proved conditional on ONE
explicit premise (strip `Gammaℝ` lower `c ≤ ‖Gammaℝ s‖`, absent repo-wide — conditional
is commit-worthy per brief). Via BL's xi-transfer (`F_of_xi_whole_plane` shape,
numerator `exp(K‖s‖^(3/2))`, denominators explicit) + rpow conversion
(`‖s‖^(3/2) ≤ 4^(3/2)+2^(3/2)·|Im|^(3/2)`) + compact absorption (`exp ≥ 1`).
STOP per brief: `hBdd`/P1-composition NOT attempted before this builds green.
No `sorry`/`admit`/`axiom` in this tail.
-/

/-!
# BU tail (door-3 hBdd via windowed decomposition): punctured-window GammaR lower + windowed middle envelope + conditional hBdd/P1

Ownership: Agent BU tail append (append-only after the BP2 verdict block; nothing above
touched; `import ZeroFreeRegionHadamard` at line 5 and `import interval_arith` at line 4
reused, not re-added).

What is proved here (all full proofs, no `sorry`/`admit`/`axiom`):
* (1) `exp18_le` — `Real.exp 18 ≤ 66000000` via `Real.exp_nat_mul` + `Real.exp_one_lt_d9`
  (same `Door3SharpWindow` pattern as `:2034`).
* (1) `sin_window_le` — windowed sine cap `‖sin(π(s/2))‖ ≤ 66000000` on
  `Re ∈ [-1/2,3/2]`, `|Im| ≤ 9`, via `BTStripGamma.sin_pi_half_strip_upper` + `exp ≤ exp 18`.
* (1) `cpow_pi_lower` — cpow lower `1/4 ≤ ‖π^(-s/2)‖` for `Re ≤ 3/2`
  (via `norm_cpow_eq_rpow_re_of_pos`, `rpow_le_rpow_of_exponent_le` with `1 ≤ π`,
  `π^(-1) = π⁻¹ ≥ 1/4` from `π < 4`).
* (1) `sin_ne_zero_of_punctured_window` — `sin(π(s/2)) ≠ 0` on the punctured window
  (`Re ∈ [-1/2,3/2]`, `|Im| ≤ 9`, `1 ≤ ‖s‖`), via `Complex.sin_eq_zero_iff`
  (`π(s/2) = kπ ⇒ s/2 = k ⇒ s = 2k`, integer in `[-0.25,0.75]` forces `k = 0 ⇒ s = 0`,
  contra `1 ≤ ‖s‖`).
* (1) MAIN `GammaR_window_lower` — punctured-window `Gammaℝ` lower
  `1/1000000000 ≤ ‖Gammaℝ s‖` on `[-1,2] × middle × |Im| ≤ 9` with `1 ≤ ‖s‖`,
  via reflection `Gamma(s/2)·Gamma(1-s/2) = π/sin(πs/2)` (`Gamma_mul_Gamma_one_sub`),
  `S = 66000000`, `U = 4` (`gamma_one_sub_half_strip_upper`), cpow `≥ 1/4`,
  `π ≥ 3` (`pi_gt_three`): `‖Gamma(s/2)‖ ≥ 3/(S·U)`, `‖Gammaℝ‖ ≥ (1/4)·3/(S·U) ≥ 1e-9`
  (`norm_num`: `1056000000 ≤ 3000000000`).
* (1) HONESTY `no_window_lower_unpunctured` — unpunctured windowed lower is still
  impossible (`s = 0` in the window, `Gammaℝ 0 = 0` via `BTStripGamma.GammaR_zero`);
  the `1 ≤ ‖s‖` puncture is load-bearing, not technical (mirrors BT impossibility).
* (2) `F_middle_window_exp32` — windowed middle envelope
  `‖F s‖ ≤ C·exp(K·|Im|^(3/2))` on `σ ∈ [-1/2,3/2]`, `|Im| ≤ 9`,
  mirroring `BP2Middle32.F_middleThird_exp32_of_GammaLower` with the windowed premise:
  small `‖s‖ ≤ max C0 1` via compactness (`closedBall ∩ strip`, `F` entire),
  large via BL xi-transfer (`poleRemoved_norm_of_hadamardXi` + `xi_norm_bound_whole_plane`)
  with denominators `‖s‖ ≥ 1`, `‖Gammaℝ‖ ≥ 1e-9` (punctured lower supplies it).
* (3) `damp_window_upper` — damping `≤ 2.7183` on the window (`Re ∈ [-1,2]`, `|Im| ≤ 9`)
  via `BH2TailWindow.damp_re_general` (`(σ²-(τ+6.75)²)/100 ≤ 0.04 ≤ 1`) + `exp_one_lt_d9`.
* (3) `G_window_bdd` — `BddAbove` of `‖G‖` on the window
  (`strip ∩ {|Im| ≤ 9}`): outer `Re` via `BNStripThirds.F_outerThirds_le`
  (`18·exp((1+π/2)·|Im|)`), middle via (2), both times damping cap.
* (3) `hBdd_of_window_and_tail` — full `hBdd` (`BddAbove ‖G‖` on `[-1,2]`) conditional on
  ONE explicit tail hypothesis `∃ T, ∀ s ∈ strip, 9 < |Im| → ‖G s‖ ≤ T`
  (middle-tail envelope absent repo-wide; window supplies `W`, tail supplies `T`,
  `max W T` works).
* (4) `P1_R02_of_window_and_tails` — `‖ζ‖ ≤ 10` on the R02 rect conditional on
  BH2 `hTail` (`‖G‖ ≤ 36` on `Re = -1`, `8.75 < |Im|`) + tail-`T` hypothesis,
  via `BH2TailWindow.zeta_R02_le_ten_of_tail` + (3).

Grep record (verified before writing; `grep` tool on this file + `Mathlib`):
* `BTStripGamma.sin_pi_half_strip_upper` / `gamma_one_sub_half_strip_upper` / `GammaR_zero`
  — only `interval_arith.lean:34266/:34325/:34339` (imported at line 4, reused).
* `BP2Middle32.F_middleThird_exp32_of_GammaLower` / `middle_norm_rpow32_le`
  — only this file `:4421/:4392` (mirrored/restricted, not modified).
* `BLMiddleEnvelope.poleRemoved_norm_of_hadamardXi` — this file `:3863` (reused).
* `BNStripThirds.F_outerThirds_le` — this file `:4286` (reused for outer window).
* `BH2TailWindow.damp_re_general` / `zeta_R02_le_ten_of_tail` — this file `:3623/:3762`
  (reused for damping cap + P1).
* `ZeroFreeRegionHadamard.xi_norm_bound_whole_plane` — `ZeroFreeRegionHadamard.lean:4535`.
* `Complex.Gamma_mul_Gamma_one_sub` — `Mathlib/.../Gamma/Beta.lean:398` (unconditional).
* `Complex.Gamma_ne_zero_of_re_pos` — `Mathlib/.../Gamma/Beta.lean:453`.
* `Complex.Gammaℝ_def` — `Mathlib/.../Gamma/Deligne.lean:45`.
* `Complex.norm_cpow_eq_rpow_re_of_pos` — `Mathlib/.../Pow/Real.lean:337`.
* `Complex.sin_eq_zero_iff` — `Mathlib/.../Trigonometric/Complex.lean:46`.
* `Real.exp_nat_mul` / `Real.exp_one_lt_d9` / `Real.pi_gt_three` / `Real.pi_lt_d4`
  — Mathlib + reused at `:2034/:2022/:1985` in this file.
* `BUWindowed` + all lemma names below: absent repo-wide (checked).
Opens stay EXPLICIT (never `sorry`): tail-`T` hypothesis for (3), BH2 `hTail` + tail-`T` for (4).
-/

namespace BUWindowed

/-- `Real.exp 18 ≤ 66000000` (`Door3SharpWindow` `:2034` pattern at `n = 18`). -/
theorem exp18_le : Real.exp (18 : ℝ) ≤ 66000000 := by
  have h1 : Real.exp (18 : ℝ) = (Real.exp 1) ^ (18 : ℕ) := by
    have h := Real.exp_nat_mul (1 : ℝ) (18 : ℕ)
    simpa using h.symm
  have h2 : (Real.exp 1) ^ (18 : ℕ) < (2.7182818286 : ℝ) ^ (18 : ℕ) := by
    apply pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos _)) (by norm_num)
  have h3 : (2.7182818286 : ℝ) ^ (18 : ℕ) < 66000000 := by norm_num
  rw [h1]
  exact le_of_lt (lt_trans h2 h3)

/-- Windowed sine cap: `‖sin(π(s/2))‖ ≤ 66000000` on `middle × |Im| ≤ 9`. -/
theorem sin_window_le {s : ℂ}
    (h1 : (-1 / 2 : ℝ) ≤ s.re) (h2 : s.re ≤ (3 / 2 : ℝ)) (him : |s.im| ≤ 9) :
    ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ ≤ 66000000 := by
  have hsin := BTStripGamma.sin_pi_half_strip_upper h1 h2
  have hexp_mono : Real.exp (2 * |s.im|) ≤ Real.exp (18 : ℝ) := by
    apply Real.exp_le_exp.mpr
    have h9 : |s.im| ≤ 9 := him
    linarith
  calc ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ ≤ Real.exp (2 * |s.im|) := hsin
    _ ≤ Real.exp (18 : ℝ) := hexp_mono
    _ ≤ 66000000 := exp18_le

/-- Cpow lower: `1/4 ≤ ‖π^(-s/2)‖` for `Re ≤ 3/2` (exponent `≥ -1`, base `π ≥ 1`). -/
theorem cpow_pi_lower {s : ℂ} (hre : s.re ≤ (3 / 2 : ℝ)) :
    (1 / 4 : ℝ) ≤ ‖(Real.pi : ℂ) ^ (-s / 2)‖ := by
  have hnorm : ‖(Real.pi : ℂ) ^ (-s / 2)‖ = Real.pi ^ ((-s / 2 : ℂ)).re :=
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos _
  have hdiv_re : (s / 2 : ℂ).re = s.re / 2 := by rw [Complex.div_ofNat_re]
  have hre_eq : ((-s / 2 : ℂ)).re = -s.re / 2 := by
    rw [Complex.div_ofNat_re, Complex.neg_re]
  rw [hnorm, hre_eq]
  have hpi1 : (1 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_three
    linarith
  have hexp_ge : (-1 : ℝ) ≤ -s.re / 2 := by linarith
  have hmono : Real.pi ^ (-1 : ℝ) ≤ Real.pi ^ (-s.re / 2) :=
    Real.rpow_le_rpow_of_exponent_le hpi1 hexp_ge
  have hpi_inv : Real.pi ^ (-1 : ℝ) = (Real.pi)⁻¹ := Real.rpow_neg_one _
  have hpi4 : Real.pi ≤ 4 := by
    have h := Real.pi_lt_d4
    linarith
  have h14 : (1 / 4 : ℝ) ≤ (Real.pi)⁻¹ := by
    have hpos : (0 : ℝ) < Real.pi := Real.pi_pos
    have h := one_div_le_one_div_of_le hpos hpi4
    simpa [one_div] using h
  rw [hpi_inv] at hmono
  exact le_trans h14 hmono

/-- `sin(π(s/2)) ≠ 0` on the punctured window (`1 ≤ ‖s‖` excludes the sole zero `s = 0`). -/
theorem sin_ne_zero_of_punctured_window {s : ℂ}
    (hmid1 : (-1 / 2 : ℝ) ≤ s.re) (hmid2 : s.re ≤ (3 / 2 : ℝ))
    (_him : |s.im| ≤ 9) (hnorm : (1 : ℝ) ≤ ‖s‖) :
    Complex.sin ((Real.pi : ℂ) * (s / 2)) ≠ 0 := by
  intro hsin0
  rw [Complex.sin_eq_zero_iff] at hsin0
  obtain ⟨k, hk⟩ := hsin0
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  have hk2 : (Real.pi : ℂ) * (s / 2) = (Real.pi : ℂ) * (k : ℂ) := by
    rw [hk, mul_comm]
  have hks : s / 2 = (k : ℂ) := mul_left_cancel₀ hpi_ne hk2
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  have h2 : s / 2 * 2 = s := div_mul_cancel₀ s h2ne
  rw [hks] at h2
  have hs_eq : s = 2 * (k : ℂ) := by
    rw [← h2, mul_comm]
  have hre_k : s.re = 2 * ((k : ℂ).re) := by
    rw [hs_eq, Complex.mul_re]
    simp
  have him_k : s.im = 0 := by
    have e : s.im = (2 * (k : ℂ)).im := by rw [hs_eq]
    rw [e, Complex.mul_im]
    simp
  simp only [Complex.intCast_re] at hre_k
  have hk_lo : (-1 / 4 : ℝ) ≤ ((k : ℤ) : ℝ) := by linarith
  have hk_hi : ((k : ℤ) : ℝ) ≤ (3 / 4 : ℝ) := by linarith
  have hk_le0 : k ≤ 0 := by
    by_contra h
    push_neg at h
    have h1 : (1 : ℤ) ≤ k := h
    have h1r : (1 : ℝ) ≤ ((k : ℤ) : ℝ) := by exact_mod_cast h1
    linarith
  have hk_ge0 : 0 ≤ k := by
    by_contra h
    push_neg at h
    have h1 : k ≤ (-1 : ℤ) := by omega
    have h1r : ((k : ℤ) : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h1
    linarith
  have hk0 : k = 0 := le_antisymm hk_le0 hk_ge0
  have hs0 : s = 0 := by
    rw [hs_eq, hk0, Int.cast_zero, mul_zero]
  rw [hs0, norm_zero] at hnorm
  linarith

/-- (1) MAIN: punctured-window `Gammaℝ` lower `1e-9 ≤ ‖Gammaℝ s‖`
(`S = 66000000`, `U = 4`, cpow `≥ 1/4`, `π ≥ 3`). -/
theorem GammaR_window_lower {s : ℂ}
    (_hs : s ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2)
    (hmid1 : (-1 / 2 : ℝ) ≤ s.re) (hmid2 : s.re ≤ (3 / 2 : ℝ))
    (him : |s.im| ≤ 9) (hnorm : (1 : ℝ) ≤ ‖s‖) :
    (1 / 1000000000 : ℝ) ≤ ‖Complex.Gammaℝ s‖ := by
  have hS : ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ ≤ 66000000 :=
    sin_window_le hmid1 hmid2 him
  have hU : ‖Complex.Gamma (1 - s / 2)‖ ≤ 4 :=
    BTStripGamma.gamma_one_sub_half_strip_upper hmid1 hmid2
  have hcpow_ge : (1 / 4 : ℝ) ≤ ‖(Real.pi : ℂ) ^ (-s / 2)‖ :=
    cpow_pi_lower hmid2
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * (s / 2)) ≠ 0 :=
    sin_ne_zero_of_punctured_window hmid1 hmid2 him hnorm
  have hdiv_re : (s / 2 : ℂ).re = s.re / 2 := by rw [Complex.div_ofNat_re]
  have h1sub_re : (1 - s / 2 : ℂ).re = 1 - s.re / 2 := by
    rw [Complex.sub_re, Complex.one_re, hdiv_re]
  have h1pos : (0 : ℝ) < (1 - s / 2 : ℂ).re := by
    rw [h1sub_re]
    linarith
  have hG1_ne : Complex.Gamma (1 - s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h1pos
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (s / 2)
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  have hrhs_ne : (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (s / 2)) ≠ 0 :=
    div_ne_zero hpi_ne hsin_ne
  have hGhalf_ne : Complex.Gamma (s / 2) ≠ 0 := left_ne_zero_of_mul (hrefl.symm ▸ hrhs_ne)
  have hT_pos : (0 : ℝ) < ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm (norm_ne_zero_iff.mpr hsin_ne))
  have hB_pos : (0 : ℝ) < ‖Complex.Gamma (1 - s / 2)‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm (norm_ne_zero_iff.mpr hG1_ne))
  have hT_ne : ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ ≠ 0 := ne_of_gt hT_pos
  have hB_ne : ‖Complex.Gamma (1 - s / 2)‖ ≠ 0 := ne_of_gt hB_pos
  have hpinorm : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hAB : ‖Complex.Gamma (s / 2)‖ * ‖Complex.Gamma (1 - s / 2)‖
      = Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ := by
    have h := congrArg norm hrefl
    rw [norm_mul, norm_div, hpinorm] at h
    exact h
  have hTB_le : ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ * ‖Complex.Gamma (1 - s / 2)‖
      ≤ 66000000 * 4 :=
    mul_le_mul hS hU (norm_nonneg _) (by norm_num)
  have hpi_ge : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
  have h3SU_le : (3 : ℝ) / (66000000 * 4)
      ≤ Real.pi / (‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ * ‖Complex.Gamma (1 - s / 2)‖) := by
    have hTB_pos : (0 : ℝ) < ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ * ‖Complex.Gamma (1 - s / 2)‖ :=
      mul_pos hT_pos hB_pos
    have hSU_pos : (0 : ℝ) < (66000000 : ℝ) * 4 := by norm_num
    have h1 : (3 : ℝ) / (66000000 * 4) ≤ Real.pi / (66000000 * 4) := by
      apply div_le_div_of_nonneg_right hpi_ge hSU_pos.le
    have h2 : Real.pi / (66000000 * 4)
        ≤ Real.pi / (‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ * ‖Complex.Gamma (1 - s / 2)‖) := by
      apply div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) hTB_pos hTB_le
    exact le_trans h1 h2
  have hA_eq : ‖Complex.Gamma (s / 2)‖
      = Real.pi / (‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ * ‖Complex.Gamma (1 - s / 2)‖) := by
    have hA2 : ‖Complex.Gamma (s / 2)‖ = (‖Complex.Gamma (s / 2)‖ * ‖Complex.Gamma (1 - s / 2)‖)
        / ‖Complex.Gamma (1 - s / 2)‖ := (mul_div_cancel_right₀ _ hB_ne).symm
    rw [hAB] at hA2
    rw [hA2, div_div]
  have hGhalf_ge : (3 : ℝ) / (66000000 * 4) ≤ ‖Complex.Gamma (s / 2)‖ := by
    rw [hA_eq]
    exact h3SU_le
  have hGR_eq : ‖Complex.Gammaℝ s‖
      = ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ := by
    rw [Complex.Gammaℝ_def, norm_mul]
  have hGR_ge : (1 / 4 : ℝ) * (3 / (66000000 * 4)) ≤ ‖Complex.Gammaℝ s‖ := by
    rw [hGR_eq]
    exact mul_le_mul hcpow_ge hGhalf_ge (by norm_num) (norm_nonneg _)
  have hnum : (1 / 1000000000 : ℝ) ≤ (1 / 4 : ℝ) * (3 / (66000000 * 4)) := by norm_num
  exact le_trans hnum hGR_ge

/-- (1) HONESTY: unpunctured windowed lower is still impossible (`s = 0` witness). -/
theorem no_window_lower_unpunctured :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ,
      s ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2 →
      (-1 / 2 : ℝ) ≤ s.re → s.re ≤ (3 / 2 : ℝ) → |s.im| ≤ 9 → c ≤ ‖Complex.Gammaℝ s‖ := by
  rintro ⟨c, hc, h⟩
  have h0mem : (0 : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2 := by
    unfold Complex.HadamardThreeLines.verticalClosedStrip
    simp only [Set.mem_preimage, Set.mem_Icc, Complex.zero_re]
    norm_num
  have h1 : (-1 / 2 : ℝ) ≤ (0 : ℂ).re := by rw [Complex.zero_re]; norm_num
  have h2 : (0 : ℂ).re ≤ (3 / 2 : ℝ) := by rw [Complex.zero_re]; norm_num
  have h3 : |(0 : ℂ).im| ≤ 9 := by rw [Complex.zero_im, abs_zero]; norm_num
  have hle := h 0 h0mem h1 h2 h3
  rw [BTStripGamma.GammaR_zero, norm_zero] at hle
  linarith

/-- (2) Windowed middle envelope (mirrors BP2, restricted to `|Im| ≤ 9`,
punctured lower supplies the large-`‖s‖` denominator). -/
theorem F_middle_window_exp32 :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ s : ℂ,
      s ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2 →
      -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → |s.im| ≤ 9 →
      ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤ C * Real.exp (K * (|s.im| ^ (3 / 2 : ℝ))) := by
  obtain ⟨Kxi, hKxi, C0, hC0, hxi⟩ := ZeroFreeRegionHadamard.xi_norm_bound_whole_plane
  have hKxi_nn : (0 : ℝ) ≤ Kxi := hKxi
  have hB2nn : (0 : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hKnn : (0 : ℝ) ≤ Kxi * (2 : ℝ) ^ (3 / 2 : ℝ) := mul_nonneg hKxi_nn hB2nn
  have hc : (0 : ℝ) < 1 / 1000000000 := by norm_num
  have hstrip_closed : IsClosed (Complex.HadamardThreeLines.verticalClosedStrip (-1) 2) := by
    unfold Complex.HadamardThreeLines.verticalClosedStrip
    exact IsClosed.preimage Complex.continuous_re isClosed_Icc
  have hKcompact : IsCompact (Metric.closedBall (0 : ℂ) (max C0 1) ∩
      Complex.HadamardThreeLines.verticalClosedStrip (-1) 2) :=
    (isCompact_closedBall _ _).inter_right hstrip_closed
  have hFcont : Continuous ZetaUpperR02ThreeLines.poleRemovedZeta :=
    ZetaUpperR02ThreeLines.poleRemovedZeta_differentiable.continuous
  obtain ⟨M, hM⟩ := hKcompact.exists_bound_of_continuousOn hFcont.continuousOn
  have hClarge_nn : (0 : ℝ) ≤ Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / (1 / 1000000000) :=
    div_nonneg (Real.exp_nonneg _) hc.le
  have hCfin_nn : (0 : ℝ) ≤ max (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / (1 / 1000000000)) M :=
    le_trans hClarge_nn (le_max_left _ _)
  refine ⟨max (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / (1 / 1000000000)) M,
    Kxi * (2 : ℝ) ^ (3 / 2 : ℝ), hCfin_nn, hKnn, fun s hs hmid1 hmid2 _him9 => ?_⟩
  have hnorm_rpow := BP2Middle32.middle_norm_rpow32_le hmid1 hmid2
  by_cases hsmall : ‖s‖ ≤ max C0 1
  · have hdist : dist s (0 : ℂ) ≤ max C0 1 := by
      have e : dist s (0 : ℂ) = ‖s‖ := by
        rw [dist_eq_norm, sub_zero]
      rw [e]
      exact hsmall
    have hmemK : s ∈ Metric.closedBall (0 : ℂ) (max C0 1) ∩
        Complex.HadamardThreeLines.verticalClosedStrip (-1) 2 :=
      ⟨Metric.mem_closedBall.mpr hdist, hs⟩
    have hMs : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤ M := hM s hmemK
    have harg_nn : (0 : ℝ) ≤ (Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ)) :=
      mul_nonneg hKnn (Real.rpow_nonneg (abs_nonneg _) _)
    have hexp1 : (1 : ℝ) ≤ Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ))) := by
      have h := Real.add_one_le_exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ)))
      linarith
    calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤ M := hMs
      _ ≤ max (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / (1 / 1000000000)) M := le_max_right _ _
      _ = max (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / (1 / 1000000000)) M * 1 := (mul_one _).symm
      _ ≤ max (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / (1 / 1000000000)) M *
          Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hexp1 hCfin_nn
  · have hlarge : max C0 1 < ‖s‖ := not_le.mp hsmall
    have hC0le : C0 ≤ ‖s‖ := le_trans (le_max_left _ _) (le_of_lt hlarge)
    have hs1le : (1 : ℝ) ≤ ‖s‖ := le_trans (le_max_right _ _) (le_of_lt hlarge)
    have hmax_nn : (0 : ℝ) ≤ max C0 1 :=
      le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right _ _)
    have hs_pos : (0 : ℝ) < ‖s‖ := lt_of_le_of_lt hmax_nn hlarge
    have hs0 : s ≠ 0 := by
      intro h
      rw [h, norm_zero] at hlarge
      linarith
    have hs1 : s ≠ 1 := by
      intro h
      rw [h, norm_one] at hlarge
      have h1le : (1 : ℝ) ≤ max C0 1 := le_max_right _ _
      linarith
    have hGlow_le : (1 / 1000000000 : ℝ) ≤ ‖Complex.Gammaℝ s‖ :=
      GammaR_window_lower hs hmid1 hmid2 _him9 hs1le
    have hGRne : Complex.Gammaℝ s ≠ 0 := by
      intro h
      rw [h, norm_zero] at hGlow_le
      linarith
    have hGne : Complex.Gamma (s / 2) ≠ 0 := by
      intro hG0
      apply hGRne
      rw [Complex.Gammaℝ_def, hG0, mul_zero]
    have hnorm_eq := BLMiddleEnvelope.poleRemoved_norm_of_hadamardXi hs0 hs1 hGne
    have hxi_le := hxi s hC0le
    have hGn_pos : (0 : ℝ) < ‖Complex.Gammaℝ s‖ := lt_of_lt_of_le hc hGlow_le
    have hDpos : (0 : ℝ) < ‖s‖ * ‖Complex.Gammaℝ s‖ := mul_pos hs_pos hGn_pos
    have hDle : ‖s‖ * (1 / 1000000000) ≤ ‖s‖ * ‖Complex.Gammaℝ s‖ :=
      mul_le_mul_of_nonneg_left hGlow_le hs_pos.le
    have hDc : (1 / 1000000000 : ℝ) ≤ ‖s‖ * (1 / 1000000000) := by
      calc (1 / 1000000000 : ℝ) = 1 * (1 / 1000000000) := (one_mul _).symm
        _ ≤ ‖s‖ * (1 / 1000000000) := mul_le_mul_of_nonneg_right hs1le hc.le
    have hDle2 : (1 / 1000000000 : ℝ) ≤ ‖s‖ * ‖Complex.Gammaℝ s‖ := le_trans hDc hDle
    have hFle1 : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤
        Real.exp (Kxi * ‖s‖ ^ (3 / 2 : ℝ)) / (‖s‖ * ‖Complex.Gammaℝ s‖) := by
      rw [hnorm_eq]
      exact div_le_div_of_nonneg_right hxi_le hDpos.le
    have hFle2 : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤
        Real.exp (Kxi * ‖s‖ ^ (3 / 2 : ℝ)) / (1 / 1000000000) :=
      le_trans hFle1 (div_le_div_of_nonneg_left (Real.exp_nonneg _) hc hDle2)
    have hexp_mono : Kxi * ‖s‖ ^ (3 / 2 : ℝ) ≤ Kxi * (4 : ℝ) ^ (3 / 2 : ℝ) +
        (Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ)) := by
      have hmul_le : Kxi * ‖s‖ ^ (3 / 2 : ℝ) ≤
          Kxi * ((4 : ℝ) ^ (3 / 2 : ℝ) + (2 : ℝ) ^ (3 / 2 : ℝ) * |s.im| ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hnorm_rpow hKxi_nn
      have heq : Kxi * ((4 : ℝ) ^ (3 / 2 : ℝ) + (2 : ℝ) ^ (3 / 2 : ℝ) * |s.im| ^ (3 / 2 : ℝ)) =
          Kxi * (4 : ℝ) ^ (3 / 2 : ℝ) + (Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ)) := by
        ring
      rw [heq] at hmul_le
      exact hmul_le
    have hexp_le : Real.exp (Kxi * ‖s‖ ^ (3 / 2 : ℝ)) ≤
        Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) *
        Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ))) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hexp_mono
    have hFle3 : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤
        (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / (1 / 1000000000)) *
        Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ))) := by
      calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤
            Real.exp (Kxi * ‖s‖ ^ (3 / 2 : ℝ)) / (1 / 1000000000) := hFle2
        _ ≤ (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) *
            Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ)))) / (1 / 1000000000) :=
          div_le_div_of_nonneg_right hexp_le hc.le
        _ = (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / (1 / 1000000000)) *
            Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ))) := by
          ring
    calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤
          (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / (1 / 1000000000)) *
          Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ))) := hFle3
      _ ≤ max (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) / (1 / 1000000000)) M *
          Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ)) * (|s.im| ^ (3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)

/-- (3) Damping cap `≤ 2.7183` on the window (`Re ∈ [-1,2]`, `|Im| ≤ 9`). -/
theorem damp_window_upper {s : ℂ}
    (hs : s ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2)
    (_him : |s.im| ≤ 9) :
    ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
      (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ ≤ 2.7183 := by
  have hmem : (-1 : ℝ) ≤ s.re ∧ s.re ≤ 2 := by
    unfold Complex.HadamardThreeLines.verticalClosedStrip at hs
    simp only [Set.mem_preimage, Set.mem_Icc] at hs
    exact hs
  obtain ⟨hlo, hhi⟩ := hmem
  have h2 := BH2TailWindow.damp_re_general (s := s)
  have hσ : s.re ^ 2 ≤ 4 := by
    have e1 : (0 : ℝ) ≤ s.re + 1 := by linarith
    have e2 : (0 : ℝ) ≤ 2 - s.re := by linarith
    nlinarith [mul_nonneg e1 e2]
  have hsq_nn : (0 : ℝ) ≤ (s.im + 6.75) ^ 2 := sq_nonneg _
  have hre : ((((1 / 100 : ℝ)) : ℂ) *
      (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re ≤ 0.04 := by
    rw [h2]
    linarith
  rw [ZetaUpperR02ThreeLines.norm_complex_exp]
  have h1 : Real.exp ((((1 / 100 : ℝ)) : ℂ) *
      (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2).re ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr (by linarith)
  have h2e : Real.exp (1 : ℝ) ≤ 2.7183 :=
    le_trans (le_of_lt Real.exp_one_lt_d9) (by norm_num)
  exact le_trans h1 h2e

/-- (3) Window `BddAbove` of `‖G‖` (outer via BN, middle via (2), damping cap). -/
theorem G_window_bdd :
    BddAbove ((norm ∘ ZetaUpperR02ThreeLines.dampedPoleRemoved) ''
      (Complex.HadamardThreeLines.verticalClosedStrip (-1) 2 ∩ {s | |s.im| ≤ 9})) := by
  obtain ⟨Cmid, Kmid, hCnn, _hKnn, hmid⟩ := F_middle_window_exp32
  have hKpi_nn : (0 : ℝ) ≤ 1 + Real.pi / 2 := by positivity
  have hexp9_nn : (0 : ℝ) ≤ Real.exp ((1 + Real.pi / 2) * 9) := Real.exp_nonneg _
  have hexp32_nn : (0 : ℝ) ≤ Real.exp (Kmid * ((9 : ℝ) ^ (3 / 2 : ℝ))) := Real.exp_nonneg _
  have hdamp_nn : (0 : ℝ) ≤ (2.7183 : ℝ) := by norm_num
  have hW1_nn : (0 : ℝ) ≤ 18 * Real.exp ((1 + Real.pi / 2) * 9) * 2.7183 :=
    mul_nonneg (mul_nonneg (by norm_num) hexp9_nn) hdamp_nn
  have hW2_nn : (0 : ℝ) ≤ Cmid * Real.exp (Kmid * ((9 : ℝ) ^ (3 / 2 : ℝ))) * 2.7183 :=
    mul_nonneg (mul_nonneg hCnn hexp32_nn) hdamp_nn
  refine ⟨max (18 * Real.exp ((1 + Real.pi / 2) * 9) * 2.7183)
    (Cmid * Real.exp (Kmid * ((9 : ℝ) ^ (3 / 2 : ℝ))) * 2.7183), ?_⟩
  intro y hy
  obtain ⟨s, hs, rfl⟩ := hy
  simp only [Function.comp_apply]
  obtain ⟨hs_strip, hs_win⟩ := hs
  simp only [Set.mem_setOf_eq] at hs_win
  have hmem : (-1 : ℝ) ≤ s.re ∧ s.re ≤ 2 := by
    unfold Complex.HadamardThreeLines.verticalClosedStrip at hs_strip
    simp only [Set.mem_preimage, Set.mem_Icc] at hs_strip
    exact hs_strip
  have hdamp := damp_window_upper hs_strip hs_win
  have hG : ZetaUpperR02ThreeLines.dampedPoleRemoved s
      = ZetaUpperR02ThreeLines.poleRemovedZeta s * Complex.exp (((1 / 100 : ℝ) : ℂ)
        * (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2) := rfl
  have hnorm : ‖ZetaUpperR02ThreeLines.dampedPoleRemoved s‖
      = ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖
        * ‖Complex.exp (((1 / 100 : ℝ) : ℂ)
          * (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ := by
    rw [hG, norm_mul]
  rw [hnorm]
  rcases le_total s.re (-1 / 2) with hleft | hmid1
  · have hF := BNStripThirds.F_leftThird_le hs_strip hleft
    have hmono : Real.exp ((1 + Real.pi / 2) * |s.im|)
        ≤ Real.exp ((1 + Real.pi / 2) * 9) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hs_win hKpi_nn
    have hF9 : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖
        ≤ 18 * Real.exp ((1 + Real.pi / 2) * 9) := by
      calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖
          ≤ 18 * Real.exp ((1 + Real.pi / 2) * |s.im|) := hF
        _ ≤ 18 * Real.exp ((1 + Real.pi / 2) * 9) :=
          mul_le_mul_of_nonneg_left hmono (by norm_num)
    calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖
          * ‖Complex.exp (((1 / 100 : ℝ) : ℂ) * (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖
        ≤ (18 * Real.exp ((1 + Real.pi / 2) * 9)) * 2.7183 :=
          mul_le_mul hF9 hdamp (norm_nonneg _) (mul_nonneg (by norm_num) hexp9_nn)
      _ = 18 * Real.exp ((1 + Real.pi / 2) * 9) * 2.7183 := by ring
      _ ≤ max (18 * Real.exp ((1 + Real.pi / 2) * 9) * 2.7183)
          (Cmid * Real.exp (Kmid * ((9 : ℝ) ^ (3 / 2 : ℝ))) * 2.7183) := le_max_left _ _
  · by_cases hright : (3 / 2 : ℝ) ≤ s.re
    · have hF := BNStripThirds.F_rightThird_le hs_strip hright
      have hmono : Real.exp ((1 + Real.pi / 2) * |s.im|)
          ≤ Real.exp ((1 + Real.pi / 2) * 9) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hs_win hKpi_nn
      have hF9 : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖
          ≤ 18 * Real.exp ((1 + Real.pi / 2) * 9) := by
        have h3 : (3 : ℝ) ≤ 18 * Real.exp ((Real.pi / 2) * |s.im|) := by
          have he : (1 : ℝ) ≤ Real.exp ((Real.pi / 2) * |s.im|) := by
            have hexp := Real.add_one_le_exp ((Real.pi / 2) * |s.im|)
            have hnn : (0 : ℝ) ≤ (Real.pi / 2) * |s.im| := by positivity
            linarith
          linarith
        calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤ 3 * Real.exp |s.im| := hF
          _ ≤ (18 * Real.exp ((Real.pi / 2) * |s.im|)) * Real.exp |s.im| :=
            mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
          _ = 18 * (Real.exp ((Real.pi / 2) * |s.im|) * Real.exp |s.im|) := by ring
          _ = 18 * Real.exp ((1 + Real.pi / 2) * |s.im|) := by
            have heq : Real.exp ((Real.pi / 2) * |s.im|) * Real.exp |s.im|
                = Real.exp ((1 + Real.pi / 2) * |s.im|) := by
              rw [← Real.exp_add]
              congr 1
              ring
            rw [heq]
          _ ≤ 18 * Real.exp ((1 + Real.pi / 2) * 9) :=
            mul_le_mul_of_nonneg_left hmono (by norm_num)
      calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖
            * ‖Complex.exp (((1 / 100 : ℝ) : ℂ) * (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖
          ≤ (18 * Real.exp ((1 + Real.pi / 2) * 9)) * 2.7183 :=
            mul_le_mul hF9 hdamp (norm_nonneg _) (mul_nonneg (by norm_num) hexp9_nn)
        _ = 18 * Real.exp ((1 + Real.pi / 2) * 9) * 2.7183 := by ring
        _ ≤ max (18 * Real.exp ((1 + Real.pi / 2) * 9) * 2.7183)
            (Cmid * Real.exp (Kmid * ((9 : ℝ) ^ (3 / 2 : ℝ))) * 2.7183) := le_max_left _ _
    · have hmid2 : s.re ≤ (3 / 2 : ℝ) := le_of_not_ge hright
      have hF := hmid s hs_strip hmid1 hmid2 hs_win
      have hrpow_mono : |s.im| ^ (3 / 2 : ℝ) ≤ (9 : ℝ) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg _) hs_win (by norm_num)
      have hKmid_nn2 : (0 : ℝ) ≤ Kmid := _hKnn
      have hmono : Real.exp (Kmid * (|s.im| ^ (3 / 2 : ℝ)))
          ≤ Real.exp (Kmid * ((9 : ℝ) ^ (3 / 2 : ℝ))) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hrpow_mono hKmid_nn2
      have hF9 : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖
          ≤ Cmid * Real.exp (Kmid * ((9 : ℝ) ^ (3 / 2 : ℝ))) := by
        calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖
            ≤ Cmid * Real.exp (Kmid * (|s.im| ^ (3 / 2 : ℝ))) := hF
          _ ≤ Cmid * Real.exp (Kmid * ((9 : ℝ) ^ (3 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hmono hCnn
      calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖
            * ‖Complex.exp (((1 / 100 : ℝ) : ℂ) * (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖
          ≤ (Cmid * Real.exp (Kmid * ((9 : ℝ) ^ (3 / 2 : ℝ)))) * 2.7183 :=
            mul_le_mul hF9 hdamp (norm_nonneg _) (mul_nonneg hCnn hexp32_nn)
        _ = Cmid * Real.exp (Kmid * ((9 : ℝ) ^ (3 / 2 : ℝ))) * 2.7183 := by ring
        _ ≤ max (18 * Real.exp ((1 + Real.pi / 2) * 9) * 2.7183)
            (Cmid * Real.exp (Kmid * ((9 : ℝ) ^ (3 / 2 : ℝ))) * 2.7183) := le_max_right _ _

/-- (3) Full `hBdd` conditional on ONE explicit tail hypothesis
(middle-tail envelope absent repo-wide). -/
theorem hBdd_of_window_and_tail
    (hTailBdd : ∃ T : ℝ, ∀ s : ℂ,
      s ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2 →
      9 < |s.im| → ‖ZetaUpperR02ThreeLines.dampedPoleRemoved s‖ ≤ T) :
    BddAbove ((norm ∘ ZetaUpperR02ThreeLines.dampedPoleRemoved) ''
      Complex.HadamardThreeLines.verticalClosedStrip (-1) 2) := by
  obtain ⟨T, hT⟩ := hTailBdd
  obtain ⟨W, hW⟩ := G_window_bdd
  refine ⟨max W T, ?_⟩
  intro y hy
  obtain ⟨s, hs, rfl⟩ := hy
  simp only [Function.comp_apply]
  by_cases hwin : |s.im| ≤ 9
  · have hmem_win : s ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2 ∩ {s | |s.im| ≤ 9} :=
      ⟨hs, hwin⟩
    have hle : (norm ∘ ZetaUpperR02ThreeLines.dampedPoleRemoved) s ≤ W := hW
      (Set.mem_image_of_mem _ hmem_win)
    simp only [Function.comp_apply] at hle
    exact le_trans hle (le_max_left _ _)
  · push_neg at hwin
    have hle := hT s hs hwin
    exact le_trans hle (le_max_right _ _)

/-- (4) P1 conditional: BH2 `hTail` + tail-`T` ⇒ `‖ζ‖ ≤ 10` on the R02 rect. -/
theorem P1_R02_of_window_and_tails
    (hTail : ∀ z ∈ Set.preimage Complex.re {(-1 : ℝ)}, 8.75 < |z.im| →
      ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ 36)
    (hTailBdd : ∃ T : ℝ, ∀ s : ℂ,
      s ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2 →
      9 < |s.im| → ‖ZetaUpperR02ThreeLines.dampedPoleRemoved s‖ ≤ T)
    {s : ℂ} (hs_lo : 0.05 ≤ s.re) (hs_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25) :
    ‖riemannZeta s‖ ≤ 10 :=
  BH2TailWindow.zeta_R02_le_ten_of_tail hTail (hBdd_of_window_and_tail hTailBdd)
    hs_lo hs_hi him_lo him_hi

#print axioms BUWindowed.exp18_le
#print axioms BUWindowed.sin_window_le
#print axioms BUWindowed.cpow_pi_lower
#print axioms BUWindowed.sin_ne_zero_of_punctured_window
#print axioms BUWindowed.GammaR_window_lower
#print axioms BUWindowed.no_window_lower_unpunctured
#print axioms BUWindowed.F_middle_window_exp32
#print axioms BUWindowed.damp_window_upper
#print axioms BUWindowed.G_window_bdd
#print axioms BUWindowed.hBdd_of_window_and_tail
#print axioms BUWindowed.P1_R02_of_window_and_tails

end BUWindowed

/-!
BU VERDICT + RESIDUAL (report-and-stop): door-3 `hBdd` via windowed decomposition.
(1) LANDED: punctured-window `Gammaℝ` lower `1e-9 ≤ ‖Gammaℝ s‖`
(`|Im| ≤ 9`, `1 ≤ ‖s‖`, `S = 66000000`, `U = 4`, cpow `≥ 1/4`, `π ≥ 3`;
unpunctured windowed lower REFUTED in-file via `s = 0`, so the puncture is load-bearing).
(2) LANDED: windowed middle envelope `‖F‖ ≤ C·exp(K·|Im|^(3/2))` on `|Im| ≤ 9`
(mirrors BP2 with the punctured premise; small-`‖s‖` via compactness, large via xi-transfer).
(3) WINDOW LANDED + FULL CONDITIONAL: `BddAbove ‖G‖` on the window unconditionally
(outer via BN + middle via (2) + damping `≤ 2.7183`); full-strip `hBdd` conditional on ONE
explicit tail hypothesis `∃ T, ∀ s ∈ [-1,2], 9 < |Im| → ‖G s‖ ≤ T`
(middle-tail exp-decay envelope absent repo-wide; Gaussian `-(τ+6.75)²/100` dominates any
fixed `K·|τ|^(3/2)` eventually, but the uniform `Kxi`-free domination lemma is not attempted
per brief report-and-stop).
(4) CONDITIONAL: P1 `‖ζ‖ ≤ 10` on R02 via BH2 from `hTail` (`‖G‖ ≤ 36` on `Re = -1`,
`8.75 < |Im|`) + tail-`T` hypothesis (through (3)).
Opens stay EXPLICIT: tail-`T` (`9 < |Im|` strip bound), BH2 `hTail` (`≤ 36` left tail).
No `sorry`/`admit`/`axiom` in this tail.
-/

/-!
BV2 tail (door-3 tail-`T`, outer envelope only): Gaussian-domination numeral for BN's
outer-thirds envelope (`‖F‖ ≤ 18·exp((1+π/2)|Im|)`).

Ownership: Agent BV2 tail append (append-only after the BU verdict block; nothing above
touched; no new imports).

What is proved here (full proof, no `sorry`/`admit`/`axiom`):
* `outer_gauss_le` — for `u ≥ 9`,
  `18·exp((1+π/2)·u)·exp(-((u+6.75)²)/100) ≤ 18·exp(165.225316)`.
  Proof: completing the square (`-u²/100 + K·u = 25·K² - (u-50·K)²/100 ≤ 25·K²`
  with `K = 1+π/2`), `(u+6.75)² ≥ u²` for `u ≥ 0` (the `+6.75` shift only helps),
  `K ≤ 2.5708` from `π ≤ 3.1416` (`Real.pi_lt_d4`), `25·2.5708² = 165.225316`
  by `norm_num`, then `Real.exp_le_exp` + `Real.exp_add`. Pure real analysis;
  feeds tail-`T` directly (outer-thirds `‖G‖` cap up to the `σ² ≤ 4` damping factor,
  i.e. an extra `exp(0.04)`; `u` plays the role of `|τ|`).

Grep record (verified by grep before writing):
* `BV2OuterTail` + `outer_gauss_le` + `165.225316`: absent repo-wide (checked).
* `BNStripThirds.F_outerThirds_le` — this file `:4286` (the fed envelope).
* `BUWindowed.hBdd_of_window_and_tail` — this file `:5081` (tail-`T` consumer).
* `Real.pi_lt_d4`, `Real.exp_le_exp`, `Real.exp_add` — Mathlib (used in-file).
-/

namespace BV2OuterTail

/-- Gaussian domination for BN's outer envelope: explicit tail constant
`T = 18·exp(165.225316)` (uniform for all `u ≥ 9`; in fact for all `u ≥ 0`). -/
theorem outer_gauss_le {u : ℝ} (hu : 9 ≤ u) :
    18 * Real.exp ((1 + Real.pi / 2) * u) * Real.exp (-(((u + 6.75) ^ 2) / 100)) ≤
      18 * Real.exp 165.225316 := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hKnn : (0 : ℝ) ≤ 1 + Real.pi / 2 := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    linarith
  have hpi_le : Real.pi ≤ 3.1416 := le_of_lt Real.pi_lt_d4
  have hKle : 1 + Real.pi / 2 ≤ (2.5708 : ℝ) := by linarith
  have hKsq : 25 * (1 + Real.pi / 2) ^ 2 ≤ (165.225316 : ℝ) := by
    have hnn1 : (0 : ℝ) ≤ 2.5708 - (1 + Real.pi / 2) := by linarith
    have hnn2 : (0 : ℝ) ≤ 2.5708 + (1 + Real.pi / 2) := by linarith
    have hprod : (0 : ℝ) ≤ (2.5708 - (1 + Real.pi / 2)) * (2.5708 + (1 + Real.pi / 2)) :=
      mul_nonneg hnn1 hnn2
    have hsq2 : (2.5708 : ℝ) ^ 2 = 6.60901264 := by norm_num
    nlinarith [hprod, hsq2]
  have hshift : u ^ 2 ≤ (u + 6.75) ^ 2 := by
    have e : (u + 6.75) ^ 2 = u ^ 2 + 13.5 * u + 45.5625 := by ring
    linarith [hu0]
  have hquad : (1 + Real.pi / 2) * u - (u + 6.75) ^ 2 / 100
      ≤ 25 * (1 + Real.pi / 2) ^ 2 := by
    have hsqnn : (0 : ℝ) ≤ (u - 50 * (1 + Real.pi / 2)) ^ 2 := sq_nonneg _
    have hcs : (1 + Real.pi / 2) * u - u ^ 2 / 100
        = 25 * (1 + Real.pi / 2) ^ 2 - (u - 50 * (1 + Real.pi / 2)) ^ 2 / 100 := by
      ring
    linarith [hsqnn, hshift, hcs]
  have hexp_arg : (1 + Real.pi / 2) * u + (-(((u + 6.75) ^ 2) / 100))
      ≤ (165.225316 : ℝ) := by
    linarith [hquad, hKsq]
  have hexp : Real.exp ((1 + Real.pi / 2) * u) * Real.exp (-(((u + 6.75) ^ 2) / 100))
      ≤ Real.exp 165.225316 := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hexp_arg
  calc 18 * Real.exp ((1 + Real.pi / 2) * u) * Real.exp (-(((u + 6.75) ^ 2) / 100))
      = 18 * (Real.exp ((1 + Real.pi / 2) * u) * Real.exp (-(((u + 6.75) ^ 2) / 100))) := by
        ring
    _ ≤ 18 * Real.exp 165.225316 :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)

#print axioms BV2OuterTail.outer_gauss_le

end BV2OuterTail

/-!
BV2 VERDICT + RESIDUAL (report-and-stop): the Gaussian-domination numeral for BN's outer
envelope is GREEN (`outer_gauss_le`, explicit `T = 18·exp(165.225316)`).
Outer-thirds tail-`T` contribution now needs only the `σ² ≤ 4` damping factor
(`exp((σ²-(u+6.75)²)/100) ≤ exp(0.04)·exp(-((u+6.75)²)/100)`, i.e. outer `‖G‖ ≤ T·exp(0.04)`
for `9 < |Im|` off the middle third). NOT attempted per brief (report-and-stop):
exp-3/2 middle case, `hTail`, P1. No `sorry`/`admit`/`axiom` in this tail.
-/

/-!
# BX tail (door-3 tail-`T`, middle exp-3/2 numeral): Young `u^{3/2}` bound + Gaussian domination

Ownership: Agent BX tail append (append-only after the BV2 verdict block; nothing above
touched; no new imports).

What is proved here (all full proofs, no `sorry`/`admit`/`axiom`):
* `young_pow3_le` — Young-type bound `K·t³ ≤ t⁴/200 + 1000000·K⁴` for `0 ≤ K`, `0 ≤ t`,
  proved directly by squaring (sum-of-squares certificate over `(t-200·K)²`, `(t²-20000·K²)²`;
  the identity `t⁴/200 + 10⁶K⁴ - K·t³ = t²(t-200K)²/400 + (t²-20000K²)²/400` is `ring`).
* `rpow32_eq_cube_sqrt` — `u^(3/2:ℝ) = (Real.sqrt u)³` for `0 < u`
  (`Real.rpow_add` + `Real.rpow_one` + `← Real.sqrt_eq_rpow` + `Real.sq_sqrt`).
* `young_rpow32` — `K·u^(3/2) ≤ u²/200 + 1000000·K⁴` for `0 ≤ K`, `0 ≤ u`
  (zero case via `Real.zero_rpow`; positive case via `t = Real.sqrt u`, `(√u)⁴ = u²`).
* `middle_gauss_le` — MAIN numeral mirroring `BV2OuterTail.outer_gauss_le` EXACTLY
  (shift `u² ≤ (u+6.75)²`, `Real.exp_le_exp` + `← Real.exp_add`, same `calc` skeleton):
  for `u ≥ 9`, `0 ≤ C`, `0 ≤ K`,
  `C·exp(K·u^{3/2})·exp(-((u+6.75)²)/100) ≤ C·exp(1000000·K⁴)`.
  So the middle tail-`T` contribution is `T = C·exp(10⁶·K⁴)` — explicit in the envelope
  constants `C,K` (the Gaussian absorbs `K·u^{3/2}` leaving room `-u²/200 ≤ 0`).

Grep record (verified by `rg -n` before writing):
* `Real.young_inequality` / `young_inequality_of_nonneg` — EXIST in
  `Mathlib/Analysis/MeanInequalities.lean:500,507` (needs `HolderConjugate` side
  conditions + rpow plumbing); per brief the concrete instance is proved directly by
  squaring instead (zero side-condition risk).
* `inner_le_Lp_mul_Lq` — EXISTS (`Mathlib/Analysis/MeanInequalities.lean:615`,
  Finset-Hölder); not used (direct SOS is shorter).
* `Real.sqrt_eq_rpow` (`Mathlib/.../Pow/Real.lean:984`), `Real.rpow_add` (`:207`),
  `Real.rpow_one` (`:148`), `Real.zero_rpow` (`:128`),
  `Real.sq_sqrt` (`Mathlib/Analysis/Real/Sqrt.lean:178`) — all verified.
* `BV2OuterTail.outer_gauss_le` — this file `:5178` (mirrored pattern).
* `BP2Middle32.F_middleThird_exp32_of_GammaLower` — this file `:4421`: its `C,K` are
  EXISTENTIAL (`Kxi` from `xi_norm_bound_whole_plane`, `M` from compactness) — NO
  explicit `C,K` numerals exist in-file (`Cmid|Kmid` absent repo-wide; `Kxi` occurs only
  as an obtained variable `:4428-:4541`, `:4823+`). So `T` is explicit as a FUNCTION
  `C·exp(10⁶K⁴)` of the envelope constants (cf. guide §1h: verified once, reported here,
  not spun). Instantiation awaits a middle envelope ON THE TAIL (see residual).
* `BUWindowed.hBdd_of_window_and_tail` — this file `:5081` (tail-`T` consumer).
* `BXMiddleTail` + all lemma names below: absent repo-wide (checked).
-/

namespace BXMiddleTail

/-- Young-type bound `K·t³ ≤ t⁴/200 + 1000000·K⁴` (direct sum-of-squares, no Hölder). -/
theorem young_pow3_le {K t : ℝ} (_hK : 0 ≤ K) (_ht : 0 ≤ t) :
    K * t ^ 3 ≤ t ^ 4 / 200 + 1000000 * K ^ 4 := by
  have w1 : (0 : ℝ) ≤ t ^ 2 * (t - 200 * K) ^ 2 :=
    mul_nonneg (sq_nonneg t) (sq_nonneg _)
  have w2 : (0 : ℝ) ≤ (t ^ 2 - 20000 * K ^ 2) ^ 2 := sq_nonneg _
  have key : t ^ 4 / 200 + 1000000 * K ^ 4 - K * t ^ 3
      = (t ^ 2 * (t - 200 * K) ^ 2) / 400 + ((t ^ 2 - 20000 * K ^ 2) ^ 2) / 400 := by
    ring
  have hnn : (0 : ℝ) ≤ (t ^ 2 * (t - 200 * K) ^ 2) / 400
      + ((t ^ 2 - 20000 * K ^ 2) ^ 2) / 400 :=
    add_nonneg (div_nonneg w1 (by norm_num)) (div_nonneg w2 (by norm_num))
  linarith

/-- `u^(3/2:ℝ) = (Real.sqrt u)³` for `0 < u`. -/
theorem rpow32_eq_cube_sqrt {u : ℝ} (hu : 0 < u) :
    u ^ (3 / 2 : ℝ) = (Real.sqrt u) ^ 3 := by
  have e : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
  rw [e, Real.rpow_add hu, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hsq := Real.sq_sqrt hu.le
  have h3 : (Real.sqrt u) ^ 3 = (Real.sqrt u) ^ 2 * Real.sqrt u := by ring
  rw [h3, hsq]

/-- Rpow Young bound: `K·u^(3/2) ≤ u²/200 + 1000000·K⁴`. -/
theorem young_rpow32 {K u : ℝ} (hK : 0 ≤ K) (hu : 0 ≤ u) :
    K * u ^ (3 / 2 : ℝ) ≤ u ^ 2 / 200 + 1000000 * K ^ 4 := by
  rcases eq_or_lt_of_le hu with h0 | hu0
  · subst h0
    rw [Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0), mul_zero]
    have h1 : (0 : ℝ) ≤ (0 : ℝ) ^ 2 / 200 := by positivity
    have h2 : (0 : ℝ) ≤ 1000000 * K ^ 4 := by positivity
    linarith
  · have ht_nn : (0 : ℝ) ≤ Real.sqrt u := Real.sqrt_nonneg u
    have hy := young_pow3_le hK ht_nn
    rw [← rpow32_eq_cube_sqrt hu0] at hy
    have h4 : (Real.sqrt u) ^ 4 = u ^ 2 := by
      have h4a : (Real.sqrt u) ^ 4 = ((Real.sqrt u) ^ 2) ^ 2 := by ring
      rw [h4a, Real.sq_sqrt hu]
    rw [h4] at hy
    exact hy

/-- Gaussian domination for the exp-3/2 middle envelope: explicit tail constant
`T = C·exp(1000000·K⁴)` (uniform for all `u ≥ 9`; in fact for all `u ≥ 0`). -/
theorem middle_gauss_le {u C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hu : 9 ≤ u) :
    C * Real.exp (K * u ^ (3 / 2 : ℝ)) * Real.exp (-(((u + 6.75) ^ 2) / 100)) ≤
      C * Real.exp (1000000 * K ^ 4) := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hyoung : K * u ^ (3 / 2 : ℝ) ≤ u ^ 2 / 200 + 1000000 * K ^ 4 :=
    young_rpow32 hK hu0
  have hshift : u ^ 2 ≤ (u + 6.75) ^ 2 := by
    have e : (u + 6.75) ^ 2 = u ^ 2 + 13.5 * u + 45.5625 := by ring
    linarith [hu0]
  have hquad : K * u ^ (3 / 2 : ℝ) - (u + 6.75) ^ 2 / 100 ≤ 1000000 * K ^ 4 := by
    have hnn2 : (0 : ℝ) ≤ (u + 6.75) ^ 2 := sq_nonneg _
    linarith [hyoung, hshift, hnn2]
  have hexp_arg : K * u ^ (3 / 2 : ℝ) + (-(((u + 6.75) ^ 2) / 100))
      ≤ 1000000 * K ^ 4 := by
    linarith [hquad]
  have hexp : Real.exp (K * u ^ (3 / 2 : ℝ)) * Real.exp (-(((u + 6.75) ^ 2) / 100))
      ≤ Real.exp (1000000 * K ^ 4) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hexp_arg
  calc C * Real.exp (K * u ^ (3 / 2 : ℝ)) * Real.exp (-(((u + 6.75) ^ 2) / 100))
      = C * (Real.exp (K * u ^ (3 / 2 : ℝ)) * Real.exp (-(((u + 6.75) ^ 2) / 100))) := by
        ring
    _ ≤ C * Real.exp (1000000 * K ^ 4) :=
        mul_le_mul_of_nonneg_left hexp hC

#print axioms BXMiddleTail.young_pow3_le
#print axioms BXMiddleTail.rpow32_eq_cube_sqrt
#print axioms BXMiddleTail.young_rpow32
#print axioms BXMiddleTail.middle_gauss_le

end BXMiddleTail

/-!
BX VERDICT + RESIDUAL (report-and-stop): the exp-3/2 middle-tail numeral is proved
(`middle_gauss_le`, explicit `T = C·exp(1000000·K⁴)` as a function of the envelope
constants; `u^{3/2} ≤ u²/200 + 10⁶K⁴` Young lemma via direct SOS, no Hölder import).
NOT attempted per brief (report-and-stop): tail-`T` assembly — blocked on (i) a middle
`F`-envelope ON THE TAIL (`σ ∈ [-1/2,3/2]`, `9 < |Im|`; BP2's is conditional on an
absent strip-uniform `Gammaℝ` lower, BU's windowed envelope stops at `|Im| ≤ 9`);
(ii) the negative-`τ` companion numeral (`(u-6.75)²` form for `τ < -9`, same SOS template
with `N = 3200` giving `C·exp(16384000000·K⁴)`); (iii) `hTail`, P1 downstream of BU.
No `sorry`/`admit`/`axiom` in this tail.
-/

/-!
# BZ tail (door-3 tail-envelope assembly): tail Gamma-lower + tail F-envelope +
# negative-`τ` numerals + tail-`T` → `hBdd` → P1

Ownership: Agent BZ tail append (append-only after the BX verdict block; nothing above
touched; no new imports).

What is proved here (all full proofs, no `sorry`/`admit`/`axiom`):
* TIER 1 — `GammaR_tail_lower`: tail Gamma-lower via reflection on `9 < |Im|`
  (`3/(16·exp(2|Im|)) ≤ ‖Gammaℝ s‖` on the middle third): sine-upper at tail from
  BT's strip piece (`BTStripGamma.sin_pi_half_strip_upper`, `exp (2|Im|)` form),
  reflected-Gamma-upper `U = 4` from the convexity chain
  (`BTStripGamma.gamma_one_sub_half_strip_upper`, strip-uniform hence valid on tails),
  cpow lower `1/4` (`BUWindowed.cpow_pi_lower`), `π ≥ 3` — the SAME reflection
  `Gamma(s/2)·Gamma(1-s/2) = π/sin(πs/2)` as BU's windowed lower, with tail
  numerals. Sine-nonzero on the tail needs no norm puncture (`9 < |Im|` kills the
  real-axis zeros `s = 2k` via `Im` alone). An honest tiny positive lower, any
  magnitude (decays with `|Im|`, as it must: the sine factor grows).
* TIER 2 — `F_middle_tail_exp32`: tail F-envelope via BL's xi-transfer fed with
  Tier 1 (whole-plane transfer `BLMiddleEnvelope.poleRemoved_norm_of_hadamardXi` +
  `xi_norm_bound_whole_plane`, restricted to the tail domain — same proof shape as
  BP2/BU, tail domain): `‖F s‖ ≤ C·exp(K·|Im|^(3/2))` on the middle third with
  `9 < |Im|`. The decaying Tier-1 lower contributes an extra `exp (2|Im|)` growth
  factor, absorbed into the 3/2-power via `abs_le_rpow32_div_three`
  (`2u ≤ (2/3)·u^(3/2)` for `9 ≤ u`); small-`‖s‖` via compactness over the
  (compact) tail slice of the ball. `C,K` stay existential (functions of `Kxi`).
* TIER 3 — negative-`τ` companion numerals (mirror BX's SOS template with the
  `(u−6.75)²` form, since `(τ+6.75)² = (|τ|−6.75)²` for `τ ≤ 0`):
  `middle_gauss_neg_le` (`C·exp(K·u^{3/2})·exp(−(u−6.75)²/100) ≤ C·exp(10⁶K⁴+1)`,
  Young + `(u−6.75)² ≥ u²−13.5u` + linear cap `0.135u−u²/200 ≤ 1` via
  `(u−13.5)² ≥ 0`) and `outer_gauss_neg_le` (BV2-mirror, exp-linear:
  `18·exp((1+π/2)u)·exp(−(u−6.75)²/100) ≤ 18·exp(183.034)` via completing the
  square at `K+0.135 ≤ 2.7058`).
* TIER 4 — `G_tail_bdd` (tail-`T`: `∃ T, ∀ s ∈ [-1,2], 9 < |Im| → ‖G s‖ ≤ T`,
  four cases outer/middle × positive/negative-`τ` from BN + Tier 2, damping split
  by sign, `σ² ≤ 4` cap `exp 0.04`); `hBdd_unconditional` (BU's tail premise
  discharged → full-strip `hBdd`); `P1_R02_of_hTail` (P1 `‖ζ‖ ≤ 10` on R02 with
  BH2 `hTail` the ONLY remaining explicit premise).

Grep record (verified by `rg -n` before writing):
* `BZTailEnvelope` + all lemma names below: absent repo-wide (checked).
* `BTStripGamma.sin_pi_half_strip_upper` / `gamma_one_sub_half_strip_upper` —
  `interval_arith.lean:34266/34325` (strip-uniform, valid on tails).
* `BUWindowed.cpow_pi_lower` — this file `:4655` (needs only `Re ≤ 3/2`, valid on tails).
* `BLMiddleEnvelope.poleRemoved_norm_of_hadamardXi` — this file `:3863` (reused).
* `BP2Middle32.middle_norm_rpow32_le` — this file `:4392` (reused).
* `BNStripThirds.F_outerThirds_le` — this file `:4286` (outer tail thirds).
* `BXMiddleTail.young_rpow32` — this file `:5298` (Young feeder for Tier 3a).
* `BV2OuterTail.outer_gauss_le` — this file `:5178` (positive-`τ` outer numeral).
* `BUWindowed.hBdd_of_window_and_tail` — this file `:5081` (tail-`T` consumer).
* `BUWindowed.P1_R02_of_window_and_tails` — this file `:5105` (P1 consumer).
* `BH2TailWindow.damp_re_general` — this file `:3623` (damping split).
* `ZeroFreeRegionHadamard.xi_norm_bound_whole_plane` —
  `ZeroFreeRegionHadamard.lean:4535`.
* `Complex.Gamma_mul_Gamma_one_sub`, `Complex.Gamma_ne_zero_of_re_pos`,
  `Complex.Gammaℝ_def`, `Complex.sin_eq_zero_iff` — Mathlib (same as BU).
* `Real.pi_lt_d4`, `Real.sqrt_le_sqrt`, `Real.sqrt_sq`, `Real.rpow_add`,
  `Real.rpow_one`, `Real.sqrt_eq_rpow` — Mathlib (same as BV2/BX).
-/

namespace BZTailEnvelope

/-- Sine-nonzero on the tail middle: `9 < |Im|` kills the real-axis zeros `s = 2k`
via `Im` alone (no norm puncture needed, unlike BU's windowed version). -/
theorem sin_ne_zero_of_tail_middle {s : ℂ}
    (_hmid1 : (-1 / 2 : ℝ) ≤ s.re) (_hmid2 : s.re ≤ (3 / 2 : ℝ))
    (htail : 9 < |s.im|) :
    Complex.sin ((Real.pi : ℂ) * (s / 2)) ≠ 0 := by
  intro hsin0
  rw [Complex.sin_eq_zero_iff] at hsin0
  obtain ⟨k, hk⟩ := hsin0
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  have hk2 : (Real.pi : ℂ) * (s / 2) = (Real.pi : ℂ) * (k : ℂ) := by
    rw [hk, mul_comm]
  have hks : s / 2 = (k : ℂ) := mul_left_cancel₀ hpi_ne hk2
  have him : s.im = 0 := by
    have hcongr := congrArg Complex.im hks
    rw [Complex.div_ofNat_im] at hcongr
    simp at hcongr
    linarith
  rw [him, abs_zero] at htail
  linarith

/-- (1) MAIN — tail `Gammaℝ` lower via reflection on `9 < |Im|`:
`3/(16·exp(2|Im|)) ≤ ‖Gammaℝ s‖` on the middle third
(`S = exp(2|Im|)` tail sine-upper, `U = 4` reflected upper, cpow `≥ 1/4`,
`π ≥ 3`; same reflection skeleton as `BUWindowed.GammaR_window_lower`). -/
theorem GammaR_tail_lower {s : ℂ}
    (_hs : s ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2)
    (hmid1 : (-1 / 2 : ℝ) ≤ s.re) (hmid2 : s.re ≤ (3 / 2 : ℝ))
    (htail : 9 < |s.im|) :
    3 / (16 * Real.exp (2 * |s.im|)) ≤ ‖Complex.Gammaℝ s‖ := by
  have hS : ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ ≤ Real.exp (2 * |s.im|) :=
    BTStripGamma.sin_pi_half_strip_upper hmid1 hmid2
  have hU : ‖Complex.Gamma (1 - s / 2)‖ ≤ 4 :=
    BTStripGamma.gamma_one_sub_half_strip_upper hmid1 hmid2
  have hcpow_ge : (1 / 4 : ℝ) ≤ ‖(Real.pi : ℂ) ^ (-s / 2)‖ :=
    BUWindowed.cpow_pi_lower hmid2
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * (s / 2)) ≠ 0 :=
    sin_ne_zero_of_tail_middle hmid1 hmid2 htail
  have hdiv_re : (s / 2 : ℂ).re = s.re / 2 := by rw [Complex.div_ofNat_re]
  have h1sub_re : (1 - s / 2 : ℂ).re = 1 - s.re / 2 := by
    rw [Complex.sub_re, Complex.one_re, hdiv_re]
  have h1pos : (0 : ℝ) < (1 - s / 2 : ℂ).re := by
    rw [h1sub_re]
    linarith
  have hG1_ne : Complex.Gamma (1 - s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h1pos
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (s / 2)
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  have hrhs_ne : (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (s / 2)) ≠ 0 :=
    div_ne_zero hpi_ne hsin_ne
  have hGhalf_ne : Complex.Gamma (s / 2) ≠ 0 := left_ne_zero_of_mul (hrefl.symm ▸ hrhs_ne)
  have hT_pos : (0 : ℝ) < ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm (norm_ne_zero_iff.mpr hsin_ne))
  have hB_pos : (0 : ℝ) < ‖Complex.Gamma (1 - s / 2)‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm (norm_ne_zero_iff.mpr hG1_ne))
  have hT_ne : ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ ≠ 0 := ne_of_gt hT_pos
  have hB_ne : ‖Complex.Gamma (1 - s / 2)‖ ≠ 0 := ne_of_gt hB_pos
  have hpinorm : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hAB : ‖Complex.Gamma (s / 2)‖ * ‖Complex.Gamma (1 - s / 2)‖
      = Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ := by
    have h := congrArg norm hrefl
    rw [norm_mul, norm_div, hpinorm] at h
    exact h
  have hTB_le : ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ * ‖Complex.Gamma (1 - s / 2)‖
      ≤ Real.exp (2 * |s.im|) * 4 :=
    mul_le_mul hS hU (norm_nonneg _) (Real.exp_nonneg _)
  have hpi_ge : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
  have hSU_pos : (0 : ℝ) < Real.exp (2 * |s.im|) * 4 := by positivity
  have h3SU_le : (3 : ℝ) / (Real.exp (2 * |s.im|) * 4)
      ≤ Real.pi / (‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ * ‖Complex.Gamma (1 - s / 2)‖) := by
    have hTB_pos : (0 : ℝ) < ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ * ‖Complex.Gamma (1 - s / 2)‖ :=
      mul_pos hT_pos hB_pos
    have h1 : (3 : ℝ) / (Real.exp (2 * |s.im|) * 4) ≤ Real.pi / (Real.exp (2 * |s.im|) * 4) := by
      apply div_le_div_of_nonneg_right hpi_ge hSU_pos.le
    have h2 : Real.pi / (Real.exp (2 * |s.im|) * 4)
        ≤ Real.pi / (‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ * ‖Complex.Gamma (1 - s / 2)‖) := by
      apply div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) hTB_pos hTB_le
    exact le_trans h1 h2
  have hA_eq : ‖Complex.Gamma (s / 2)‖
      = Real.pi / (‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ * ‖Complex.Gamma (1 - s / 2)‖) := by
    have hA2 : ‖Complex.Gamma (s / 2)‖ = (‖Complex.Gamma (s / 2)‖ * ‖Complex.Gamma (1 - s / 2)‖)
        / ‖Complex.Gamma (1 - s / 2)‖ := (mul_div_cancel_right₀ _ hB_ne).symm
    rw [hAB] at hA2
    rw [hA2, div_div]
  have hGhalf_ge : (3 : ℝ) / (Real.exp (2 * |s.im|) * 4) ≤ ‖Complex.Gamma (s / 2)‖ := by
    rw [hA_eq]
    exact h3SU_le
  have hGR_eq : ‖Complex.Gammaℝ s‖
      = ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ := by
    rw [Complex.Gammaℝ_def, norm_mul]
  have hGR_ge : (1 / 4 : ℝ) * (3 / (Real.exp (2 * |s.im|) * 4)) ≤ ‖Complex.Gammaℝ s‖ := by
    rw [hGR_eq]
    exact mul_le_mul hcpow_ge hGhalf_ge (by positivity) (norm_nonneg _)
  have hnum : 3 / (16 * Real.exp (2 * |s.im|))
      = (1 / 4 : ℝ) * (3 / (Real.exp (2 * |s.im|) * 4)) := by
    have hE : Real.exp (2 * |s.im|) ≠ 0 := Real.exp_ne_zero _
    field_simp
    ring
  rw [hnum]
  exact hGR_ge

/-- `u^(3/2:ℝ) = u·√u` for `0 < u` (feeder for the absorption lemma). -/
theorem rpow32_eq_mul_sqrt {u : ℝ} (hu : 0 < u) :
    u ^ (3 / 2 : ℝ) = u * Real.sqrt u := by
  have e : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
  rw [e, Real.rpow_add hu, Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- `3 ≤ √u` for `9 ≤ u`. -/
theorem sqrt_ge_three_of_nine_le {u : ℝ} (hu : 9 ≤ u) : 3 ≤ Real.sqrt u := by
  have h9 : Real.sqrt 9 = 3 := by
    have e : (9 : ℝ) = 3 ^ 2 := by norm_num
    rw [e, Real.sqrt_sq (by norm_num)]
  calc (3 : ℝ) = Real.sqrt 9 := h9.symm
    _ ≤ Real.sqrt u := Real.sqrt_le_sqrt hu

/-- Absorption of the sine-growth exponent into the 3/2-power:
`2u ≤ (2/3)·u^(3/2)` for `9 ≤ u` (since `u^(3/2) = u·√u ≥ 3u`). -/
theorem abs_le_rpow32_div_three {u : ℝ} (hu : 9 ≤ u) :
    2 * u ≤ (2 / 3) * u ^ (3 / 2 : ℝ) := by
  have hu0 : (0 : ℝ) < u := by linarith
  have h32 : u ^ (3 / 2 : ℝ) = u * Real.sqrt u := rpow32_eq_mul_sqrt hu0
  have hsq : (3 : ℝ) ≤ Real.sqrt u := sqrt_ge_three_of_nine_le hu
  have h3u : 3 * u ≤ u ^ (3 / 2 : ℝ) := by
    rw [h32]
    have h := mul_le_mul_of_nonneg_left hsq hu0.le
    linarith
  linarith

/-- (2) MAIN — tail middle envelope in exp-3/2 form via BL's xi-transfer fed with
Tier 1: `‖F s‖ ≤ C·exp(K·|Im s|^(3/2))` on `σ ∈ [-1/2,3/2]`, `9 < |Im|`.
Same proof shape as `BUWindowed.F_middle_window_exp32`, tail domain; the extra
`exp (2|Im|)` from the decaying Tier-1 lower is absorbed into `K`
(`K = Kxi·2^(3/2) + 2/3`). -/
theorem F_middle_tail_exp32 :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ s : ℂ,
      s ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2 →
      -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → 9 < |s.im| →
      ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤ C * Real.exp (K * (|s.im| ^ (3 / 2 : ℝ))) := by
  obtain ⟨Kxi, hKxi, C0, hC0, hxi⟩ := ZeroFreeRegionHadamard.xi_norm_bound_whole_plane
  have hKxi_nn : (0 : ℝ) ≤ Kxi := hKxi
  have hB2nn : (0 : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hKnn : (0 : ℝ) ≤ Kxi * (2 : ℝ) ^ (3 / 2 : ℝ) + 2 / 3 :=
    add_nonneg (mul_nonneg hKxi_nn hB2nn) (by norm_num)
  have hstrip_closed : IsClosed (Complex.HadamardThreeLines.verticalClosedStrip (-1) 2) := by
    unfold Complex.HadamardThreeLines.verticalClosedStrip
    exact IsClosed.preimage Complex.continuous_re isClosed_Icc
  have htail_closed : IsClosed {s : ℂ | 9 ≤ |s.im|} :=
    isClosed_Ici.preimage Complex.continuous_im.abs
  have hKcompact : IsCompact (Metric.closedBall (0 : ℂ) (max C0 1) ∩
      Complex.HadamardThreeLines.verticalClosedStrip (-1) 2 ∩ {s : ℂ | 9 ≤ |s.im|}) :=
    ((isCompact_closedBall _ _).inter_right hstrip_closed).inter_right htail_closed
  have hFcont : Continuous ZetaUpperR02ThreeLines.poleRemovedZeta :=
    ZetaUpperR02ThreeLines.poleRemovedZeta_differentiable.continuous
  obtain ⟨M, hM⟩ := hKcompact.exists_bound_of_continuousOn hFcont.continuousOn
  have hCfin_nn : (0 : ℝ) ≤ max (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) * 16 / 3) M :=
    le_trans (by positivity) (le_max_left _ _)
  refine ⟨max (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) * 16 / 3) M,
    Kxi * (2 : ℝ) ^ (3 / 2 : ℝ) + 2 / 3, hCfin_nn, hKnn,
    fun s hs hmid1 hmid2 htail => ?_⟩
  have hnorm_rpow := BP2Middle32.middle_norm_rpow32_le hmid1 hmid2
  have h9 : (9 : ℝ) ≤ |s.im| := le_of_lt htail
  by_cases hsmall : ‖s‖ ≤ max C0 1
  · have hdist : dist s (0 : ℂ) ≤ max C0 1 := by
      have e : dist s (0 : ℂ) = ‖s‖ := by
        rw [dist_eq_norm, sub_zero]
      rw [e]
      exact hsmall
    have hmemK : s ∈ Metric.closedBall (0 : ℂ) (max C0 1) ∩
        Complex.HadamardThreeLines.verticalClosedStrip (-1) 2 ∩ {s : ℂ | 9 ≤ |s.im|} :=
      ⟨⟨Metric.mem_closedBall.mpr hdist, hs⟩, h9⟩
    have hMs : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤ M := hM s hmemK
    have harg_nn : (0 : ℝ) ≤ (Kxi * (2 : ℝ) ^ (3 / 2 : ℝ) + 2 / 3) * (|s.im| ^ (3 / 2 : ℝ)) :=
      mul_nonneg hKnn (Real.rpow_nonneg (abs_nonneg _) _)
    have hexp1 : (1 : ℝ) ≤ Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ) + 2 / 3) * (|s.im| ^ (3 / 2 : ℝ))) := by
      have h := Real.add_one_le_exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ) + 2 / 3) * (|s.im| ^ (3 / 2 : ℝ)))
      linarith
    calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤ M := hMs
      _ ≤ max (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) * 16 / 3) M := le_max_right _ _
      _ = max (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) * 16 / 3) M * 1 := (mul_one _).symm
      _ ≤ max (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) * 16 / 3) M *
          Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ) + 2 / 3) * (|s.im| ^ (3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hexp1 hCfin_nn
  · have hlarge : max C0 1 < ‖s‖ := not_le.mp hsmall
    have hC0le : C0 ≤ ‖s‖ := le_trans (le_max_left _ _) (le_of_lt hlarge)
    have hs1le : (1 : ℝ) ≤ ‖s‖ := le_trans (le_max_right _ _) (le_of_lt hlarge)
    have hmax_nn : (0 : ℝ) ≤ max C0 1 :=
      le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right _ _)
    have hs_pos : (0 : ℝ) < ‖s‖ := lt_of_le_of_lt hmax_nn hlarge
    have hs0 : s ≠ 0 := by
      intro h
      rw [h, norm_zero] at hlarge
      linarith
    have hs1 : s ≠ 1 := by
      intro h
      rw [h, norm_one] at hlarge
      have h1le : (1 : ℝ) ≤ max C0 1 := le_max_right _ _
      linarith
    have hGlow_le : 3 / (16 * Real.exp (2 * |s.im|)) ≤ ‖Complex.Gammaℝ s‖ :=
      GammaR_tail_lower hs hmid1 hmid2 htail
    have hGRne : Complex.Gammaℝ s ≠ 0 := by
      intro h
      rw [h, norm_zero] at hGlow_le
      have hc : (0 : ℝ) < 3 / (16 * Real.exp (2 * |s.im|)) := by positivity
      linarith
    have hGne : Complex.Gamma (s / 2) ≠ 0 := by
      intro hG0
      apply hGRne
      rw [Complex.Gammaℝ_def, hG0, mul_zero]
    have hnorm_eq := BLMiddleEnvelope.poleRemoved_norm_of_hadamardXi hs0 hs1 hGne
    have hxi_le := hxi s hC0le
    have hc : (0 : ℝ) < 3 / (16 * Real.exp (2 * |s.im|)) := by positivity
    have hGn_pos : (0 : ℝ) < ‖Complex.Gammaℝ s‖ := lt_of_lt_of_le hc hGlow_le
    have hDpos : (0 : ℝ) < ‖s‖ * ‖Complex.Gammaℝ s‖ := mul_pos hs_pos hGn_pos
    have hDle2 : 3 / (16 * Real.exp (2 * |s.im|)) ≤ ‖s‖ * ‖Complex.Gammaℝ s‖ := by
      calc 3 / (16 * Real.exp (2 * |s.im|)) = 1 * (3 / (16 * Real.exp (2 * |s.im|))) := (one_mul _).symm
        _ ≤ ‖s‖ * ‖Complex.Gammaℝ s‖ :=
          mul_le_mul hs1le hGlow_le hc.le (norm_nonneg _)
    have hFle1 : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤
        Real.exp (Kxi * ‖s‖ ^ (3 / 2 : ℝ)) / (‖s‖ * ‖Complex.Gammaℝ s‖) := by
      rw [hnorm_eq]
      exact div_le_div_of_nonneg_right hxi_le hDpos.le
    have hFle2 : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤
        Real.exp (Kxi * ‖s‖ ^ (3 / 2 : ℝ)) / (3 / (16 * Real.exp (2 * |s.im|))) :=
      le_trans hFle1 (div_le_div_of_nonneg_left (Real.exp_nonneg _) hc hDle2)
    have hE : Real.exp (2 * |s.im|) ≠ 0 := Real.exp_ne_zero _
    have hFle2b : Real.exp (Kxi * ‖s‖ ^ (3 / 2 : ℝ)) / (3 / (16 * Real.exp (2 * |s.im|)))
        = (Real.exp (Kxi * ‖s‖ ^ (3 / 2 : ℝ)) * Real.exp (2 * |s.im|)) * (16 / 3) := by
      field_simp
    have hexp_mono : Kxi * ‖s‖ ^ (3 / 2 : ℝ) + 2 * |s.im|
        ≤ Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)
          + (Kxi * (2 : ℝ) ^ (3 / 2 : ℝ) + 2 / 3) * (|s.im| ^ (3 / 2 : ℝ)) := by
      have hmul_le : Kxi * ‖s‖ ^ (3 / 2 : ℝ) ≤
          Kxi * ((4 : ℝ) ^ (3 / 2 : ℝ) + (2 : ℝ) ^ (3 / 2 : ℝ) * |s.im| ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hnorm_rpow hKxi_nn
      have habsorb : 2 * |s.im| ≤ (2 / 3) * (|s.im| ^ (3 / 2 : ℝ)) :=
        abs_le_rpow32_div_three h9
      have heq : Kxi * ((4 : ℝ) ^ (3 / 2 : ℝ) + (2 : ℝ) ^ (3 / 2 : ℝ) * |s.im| ^ (3 / 2 : ℝ))
          + (2 / 3) * (|s.im| ^ (3 / 2 : ℝ))
          = Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)
            + (Kxi * (2 : ℝ) ^ (3 / 2 : ℝ) + 2 / 3) * (|s.im| ^ (3 / 2 : ℝ)) := by
        ring
      have h1 : Kxi * ‖s‖ ^ (3 / 2 : ℝ) + 2 * |s.im|
          ≤ Kxi * ((4 : ℝ) ^ (3 / 2 : ℝ) + (2 : ℝ) ^ (3 / 2 : ℝ) * |s.im| ^ (3 / 2 : ℝ))
            + (2 / 3) * (|s.im| ^ (3 / 2 : ℝ)) := by
        linarith [hmul_le, habsorb]
      rwa [heq] at h1
    have hexp_le : Real.exp (Kxi * ‖s‖ ^ (3 / 2 : ℝ)) * Real.exp (2 * |s.im|)
        ≤ Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) *
          Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ) + 2 / 3) * (|s.im| ^ (3 / 2 : ℝ))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr hexp_mono
    have hFle3 : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤
        (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) * 16 / 3) *
        Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ) + 2 / 3) * (|s.im| ^ (3 / 2 : ℝ))) := by
      calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤
            Real.exp (Kxi * ‖s‖ ^ (3 / 2 : ℝ)) / (3 / (16 * Real.exp (2 * |s.im|))) := hFle2
        _ = (Real.exp (Kxi * ‖s‖ ^ (3 / 2 : ℝ)) * Real.exp (2 * |s.im|)) * (16 / 3) := hFle2b
        _ ≤ (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) *
            Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ) + 2 / 3) * (|s.im| ^ (3 / 2 : ℝ)))) * (16 / 3) :=
          mul_le_mul_of_nonneg_right hexp_le (by norm_num)
        _ = (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) * 16 / 3) *
            Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ) + 2 / 3) * (|s.im| ^ (3 / 2 : ℝ))) := by
          ring
    calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ ≤
          (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) * 16 / 3) *
          Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ) + 2 / 3) * (|s.im| ^ (3 / 2 : ℝ))) := hFle3
      _ ≤ max (Real.exp (Kxi * (4 : ℝ) ^ (3 / 2 : ℝ)) * 16 / 3) M *
          Real.exp ((Kxi * (2 : ℝ) ^ (3 / 2 : ℝ) + 2 / 3) * (|s.im| ^ (3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)

/-- (3a) Middle negative-`τ` companion numeral (BX-mirror with the `(u−6.75)²`
form): for `u ≥ 9`, `C·exp(K·u^{3/2})·exp(−(u−6.75)²/100) ≤ C·exp(10⁶K⁴+1)`.
Young (`BXMiddleTail.young_rpow32`) + `(u−6.75)² ≥ u²−13.5u` + linear cap
`0.135u−u²/200 ≤ 1` (max `0.91125` at `u = 13.5`, via `(u−13.5)² ≥ 0`). -/
theorem middle_gauss_neg_le {u C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hu : 9 ≤ u) :
    C * Real.exp (K * u ^ (3 / 2 : ℝ)) * Real.exp (-(((u - 6.75) ^ 2) / 100)) ≤
      C * Real.exp (1000000 * K ^ 4 + 1) := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hyoung : K * u ^ (3 / 2 : ℝ) ≤ u ^ 2 / 200 + 1000000 * K ^ 4 :=
    BXMiddleTail.young_rpow32 hK hu0
  have hshift : u ^ 2 - 13.5 * u ≤ (u - 6.75) ^ 2 := by
    have e : (u - 6.75) ^ 2 = u ^ 2 - 13.5 * u + 45.5625 := by ring
    linarith
  have hlin : 0.135 * u - u ^ 2 / 200 ≤ 1 := by
    have hsq : (0 : ℝ) ≤ (u - 13.5) ^ 2 := sq_nonneg _
    linarith
  have hquad : K * u ^ (3 / 2 : ℝ) - (u - 6.75) ^ 2 / 100 ≤ 1000000 * K ^ 4 + 1 := by
    linarith [hyoung, hshift, hlin]
  have hexp_arg : K * u ^ (3 / 2 : ℝ) + (-(((u - 6.75) ^ 2) / 100))
      ≤ 1000000 * K ^ 4 + 1 := by
    linarith [hquad]
  have hexp : Real.exp (K * u ^ (3 / 2 : ℝ)) * Real.exp (-(((u - 6.75) ^ 2) / 100))
      ≤ Real.exp (1000000 * K ^ 4 + 1) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hexp_arg
  calc C * Real.exp (K * u ^ (3 / 2 : ℝ)) * Real.exp (-(((u - 6.75) ^ 2) / 100))
      = C * (Real.exp (K * u ^ (3 / 2 : ℝ)) * Real.exp (-(((u - 6.75) ^ 2) / 100))) := by
        ring
    _ ≤ C * Real.exp (1000000 * K ^ 4 + 1) :=
        mul_le_mul_of_nonneg_left hexp hC

/-- (3b) Outer negative-`τ` companion numeral (BV2-mirror with the `(u−6.75)²`
form, exp-linear): for `u ≥ 9`,
`18·exp((1+π/2)u)·exp(−(u−6.75)²/100) ≤ 18·exp(183.034)`.
Completing the square at `K+0.135 ≤ 2.7058` (`(u−6.75)² ≥ u²−13.5u` shifts the
linear coefficient by `+0.135`); `25·2.7058² = 183.033841 ≤ 183.034`. -/
theorem outer_gauss_neg_le {u : ℝ} (hu : 9 ≤ u) :
    18 * Real.exp ((1 + Real.pi / 2) * u) * Real.exp (-(((u - 6.75) ^ 2) / 100)) ≤
      18 * Real.exp 183.034 := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hKnn : (0 : ℝ) ≤ 1 + Real.pi / 2 := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    linarith
  have hpi_le : Real.pi ≤ 3.1416 := le_of_lt Real.pi_lt_d4
  have hKle : 1 + Real.pi / 2 + 0.135 ≤ (2.7058 : ℝ) := by linarith
  have hKsq : 25 * (1 + Real.pi / 2 + 0.135) ^ 2 ≤ (183.034 : ℝ) := by
    have hnn1 : (0 : ℝ) ≤ 2.7058 - (1 + Real.pi / 2 + 0.135) := by linarith
    have hnn2 : (0 : ℝ) ≤ 2.7058 + (1 + Real.pi / 2 + 0.135) := by linarith
    have hprod : (0 : ℝ) ≤ (2.7058 - (1 + Real.pi / 2 + 0.135)) * (2.7058 + (1 + Real.pi / 2 + 0.135)) :=
      mul_nonneg hnn1 hnn2
    have hsq2 : (2.7058 : ℝ) ^ 2 = 7.32135364 := by norm_num
    nlinarith [hprod, hsq2]
  have hshift : u ^ 2 - 13.5 * u ≤ (u - 6.75) ^ 2 := by
    have e : (u - 6.75) ^ 2 = u ^ 2 - 13.5 * u + 45.5625 := by ring
    linarith
  have hquad : (1 + Real.pi / 2) * u - (u - 6.75) ^ 2 / 100
      ≤ 25 * (1 + Real.pi / 2 + 0.135) ^ 2 := by
    have hsqnn : (0 : ℝ) ≤ (u - 50 * (1 + Real.pi / 2 + 0.135)) ^ 2 := sq_nonneg _
    have hcs : (1 + Real.pi / 2) * u - (u ^ 2 - 13.5 * u) / 100
        = 25 * (1 + Real.pi / 2 + 0.135) ^ 2 - (u - 50 * (1 + Real.pi / 2 + 0.135)) ^ 2 / 100 := by
      ring
    linarith [hsqnn, hshift, hcs]
  have hexp_arg : (1 + Real.pi / 2) * u + (-(((u - 6.75) ^ 2) / 100))
      ≤ (183.034 : ℝ) := by
    linarith [hquad, hKsq]
  have hexp : Real.exp ((1 + Real.pi / 2) * u) * Real.exp (-(((u - 6.75) ^ 2) / 100))
      ≤ Real.exp 183.034 := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hexp_arg
  calc 18 * Real.exp ((1 + Real.pi / 2) * u) * Real.exp (-(((u - 6.75) ^ 2) / 100))
      = 18 * (Real.exp ((1 + Real.pi / 2) * u) * Real.exp (-(((u - 6.75) ^ 2) / 100))) := by
        ring
    _ ≤ 18 * Real.exp 183.034 :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)

/-- (4a) MAIN — tail-`T`: an explicit uniform cap on `‖G‖` over the whole tail
`9 < |Im|` of the strip `[-1,2]`. Four cases (outer/middle ×
nonnegative/negative-`τ`): outer thirds via BN (`F_outerThirds_le`) with the
BV2/outer-neg numerals, middle via Tier 2 with the BX/middle-neg numerals;
damping split by sign of `τ`, `σ² ≤ 4` cap `exp 0.04`. -/
theorem G_tail_bdd :
    ∃ T : ℝ, ∀ s : ℂ,
      s ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1) 2 →
      9 < |s.im| → ‖ZetaUpperR02ThreeLines.dampedPoleRemoved s‖ ≤ T := by
  obtain ⟨Cmid, Kmid, hCnn, hKnn, hmid⟩ := F_middle_tail_exp32
  have hBop_nn : (0 : ℝ) ≤ 18 * Real.exp 165.225316 :=
    mul_nonneg (by norm_num) (Real.exp_nonneg _)
  have hBon_nn : (0 : ℝ) ≤ 18 * Real.exp 183.034 :=
    mul_nonneg (by norm_num) (Real.exp_nonneg _)
  have hTop_nn : (0 : ℝ) ≤ Cmid * Real.exp (1000000 * Kmid ^ 4) :=
    mul_nonneg hCnn (Real.exp_nonneg _)
  have hTon_nn : (0 : ℝ) ≤ Cmid * Real.exp (1000000 * Kmid ^ 4 + 1) :=
    mul_nonneg hCnn (Real.exp_nonneg _)
  refine ⟨max (max (18 * Real.exp 165.225316 * Real.exp 0.04)
      (18 * Real.exp 183.034 * Real.exp 0.04))
    (max (Cmid * Real.exp (1000000 * Kmid ^ 4) * Real.exp 0.04)
      (Cmid * Real.exp (1000000 * Kmid ^ 4 + 1) * Real.exp 0.04)),
    fun s hs htail => ?_⟩
  have hmem : (-1 : ℝ) ≤ s.re ∧ s.re ≤ 2 := by
    unfold Complex.HadamardThreeLines.verticalClosedStrip at hs
    simp only [Set.mem_preimage, Set.mem_Icc] at hs
    exact hs
  obtain ⟨hlo, hhi⟩ := hmem
  have hσ : s.re ^ 2 ≤ 4 := by
    have e1 : (0 : ℝ) ≤ s.re + 1 := by linarith
    have e2 : (0 : ℝ) ≤ 2 - s.re := by linarith
    nlinarith [mul_nonneg e1 e2]
  have h9 : (9 : ℝ) ≤ |s.im| := le_of_lt htail
  have hdamp_eq : ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
      (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖
      = Real.exp (s.re ^ 2 / 100) * Real.exp (-(((s.im + 6.75) ^ 2) / 100)) := by
    rw [ZetaUpperR02ThreeLines.norm_complex_exp, BH2TailWindow.damp_re_general,
      ← Real.exp_add]
    congr 1
    ring
  have hexp04 : Real.exp (s.re ^ 2 / 100) ≤ Real.exp 0.04 :=
    Real.exp_le_exp.mpr (by linarith)
  have hG : ZetaUpperR02ThreeLines.dampedPoleRemoved s
      = ZetaUpperR02ThreeLines.poleRemovedZeta s * Complex.exp (((1 / 100 : ℝ) : ℂ)
        * (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2) := rfl
  have hnorm : ‖ZetaUpperR02ThreeLines.dampedPoleRemoved s‖
      = ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖
        * ‖Complex.exp (((1 / 100 : ℝ) : ℂ)
          * (s - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ := by
    rw [hG, norm_mul]
  rw [hnorm, hdamp_eq]
  rcases le_total 0 s.im with hnn | hneg
  · -- Nonnegative-`τ` side: `(τ+6.75)² = (|τ|+6.75)²`.
    have habs : |s.im| = s.im := abs_of_nonneg hnn
    have hsq : (s.im + 6.75) ^ 2 = (|s.im| + 6.75) ^ 2 := by rw [habs]
    rw [hsq]
    rcases le_total s.re (-1 / 2) with hleft | hmid1
    · -- Outer-left, `τ ≥ 0`: BN + BV2.
      have hF := BNStripThirds.F_outerThirds_le hs (Or.inl hleft)
      have hnum := BV2OuterTail.outer_gauss_le (u := |s.im|) h9
      have hFE : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100))
          ≤ 18 * Real.exp ((1 + Real.pi / 2) * |s.im|) * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100)) :=
        mul_le_mul_of_nonneg_right hF (Real.exp_nonneg _)
      have hcap : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100))
          ≤ 18 * Real.exp 165.225316 := le_trans hFE hnum
      calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ *
            (Real.exp (s.re ^ 2 / 100) * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100)))
          = (‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100))) *
            Real.exp (s.re ^ 2 / 100) := by ring
        _ ≤ (18 * Real.exp 165.225316) * Real.exp (s.re ^ 2 / 100) :=
            mul_le_mul_of_nonneg_right hcap (Real.exp_nonneg _)
        _ ≤ (18 * Real.exp 165.225316) * Real.exp 0.04 :=
            mul_le_mul_of_nonneg_left hexp04 hBop_nn
        _ ≤ _ := le_trans (le_max_left _ _) (le_max_left _ _)
    · by_cases hright : (3 / 2 : ℝ) ≤ s.re
      · -- Outer-right, `τ ≥ 0`: BN + BV2.
        have hF := BNStripThirds.F_outerThirds_le hs (Or.inr hright)
        have hnum := BV2OuterTail.outer_gauss_le (u := |s.im|) h9
        have hFE : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100))
            ≤ 18 * Real.exp ((1 + Real.pi / 2) * |s.im|) * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100)) :=
          mul_le_mul_of_nonneg_right hF (Real.exp_nonneg _)
        have hcap : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100))
            ≤ 18 * Real.exp 165.225316 := le_trans hFE hnum
        calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ *
              (Real.exp (s.re ^ 2 / 100) * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100)))
            = (‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100))) *
              Real.exp (s.re ^ 2 / 100) := by ring
          _ ≤ (18 * Real.exp 165.225316) * Real.exp (s.re ^ 2 / 100) :=
              mul_le_mul_of_nonneg_right hcap (Real.exp_nonneg _)
          _ ≤ (18 * Real.exp 165.225316) * Real.exp 0.04 :=
              mul_le_mul_of_nonneg_left hexp04 hBop_nn
          _ ≤ _ := le_trans (le_max_left _ _) (le_max_left _ _)
      · -- Middle, `τ ≥ 0`: Tier 2 + BX.
        have hmid2 : s.re ≤ (3 / 2 : ℝ) := le_of_not_ge hright
        have hF := hmid s hs hmid1 hmid2 htail
        have hnum := BXMiddleTail.middle_gauss_le hCnn hKnn h9
        have hFE : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100))
            ≤ Cmid * Real.exp (Kmid * (|s.im| ^ (3 / 2 : ℝ))) * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100)) :=
          mul_le_mul_of_nonneg_right hF (Real.exp_nonneg _)
        have hcap : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100))
            ≤ Cmid * Real.exp (1000000 * Kmid ^ 4) := le_trans hFE hnum
        calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ *
              (Real.exp (s.re ^ 2 / 100) * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100)))
            = (‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ * Real.exp (-(((|s.im| + 6.75) ^ 2) / 100))) *
              Real.exp (s.re ^ 2 / 100) := by ring
          _ ≤ (Cmid * Real.exp (1000000 * Kmid ^ 4)) * Real.exp (s.re ^ 2 / 100) :=
              mul_le_mul_of_nonneg_right hcap (Real.exp_nonneg _)
          _ ≤ (Cmid * Real.exp (1000000 * Kmid ^ 4)) * Real.exp 0.04 :=
              mul_le_mul_of_nonneg_left hexp04 hTop_nn
          _ ≤ _ := le_trans (le_max_left _ _) (le_max_right _ _)
  · -- Negative-`τ` side: `(τ+6.75)² = (|τ|−6.75)²`.
    have habs : |s.im| = -s.im := abs_of_nonpos hneg
    have hsq : (s.im + 6.75) ^ 2 = (|s.im| - 6.75) ^ 2 := by
      rw [habs]
      ring
    rw [hsq]
    rcases le_total s.re (-1 / 2) with hleft | hmid1
    · -- Outer-left, `τ ≤ 0`: BN + outer-neg numeral.
      have hF := BNStripThirds.F_outerThirds_le hs (Or.inl hleft)
      have hnum := outer_gauss_neg_le (u := |s.im|) h9
      have hFE : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ * Real.exp (-(((|s.im| - 6.75) ^ 2) / 100))
          ≤ 18 * Real.exp ((1 + Real.pi / 2) * |s.im|) * Real.exp (-(((|s.im| - 6.75) ^ 2) / 100)) :=
        mul_le_mul_of_nonneg_right hF (Real.exp_nonneg _)
      have hcap : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ * Real.exp (-(((|s.im| - 6.75) ^ 2) / 100))
          ≤ 18 * Real.exp 183.034 := le_trans hFE hnum
      calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ *
            (Real.exp (s.re ^ 2 / 100) * Real.exp (-(((|s.im| - 6.75) ^ 2) / 100)))
          = (‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ * Real.exp (-(((|s.im| - 6.75) ^ 2) / 100))) *
            Real.exp (s.re ^ 2 / 100) := by ring
        _ ≤ (18 * Real.exp 183.034) * Real.exp (s.re ^ 2 / 100) :=
            mul_le_mul_of_nonneg_right hcap (Real.exp_nonneg _)
        _ ≤ (18 * Real.exp 183.034) * Real.exp 0.04 :=
            mul_le_mul_of_nonneg_left hexp04 hBon_nn
        _ ≤ _ := le_trans (le_max_right _ _) (le_max_left _ _)
    · by_cases hright : (3 / 2 : ℝ) ≤ s.re
      · -- Outer-right, `τ ≤ 0`: BN + outer-neg numeral.
        have hF := BNStripThirds.F_outerThirds_le hs (Or.inr hright)
        have hnum := outer_gauss_neg_le (u := |s.im|) h9
        have hFE : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ * Real.exp (-(((|s.im| - 6.75) ^ 2) / 100))
            ≤ 18 * Real.exp ((1 + Real.pi / 2) * |s.im|) * Real.exp (-(((|s.im| - 6.75) ^ 2) / 100)) :=
          mul_le_mul_of_nonneg_right hF (Real.exp_nonneg _)
        have hcap : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ * Real.exp (-(((|s.im| - 6.75) ^ 2) / 100))
            ≤ 18 * Real.exp 183.034 := le_trans hFE hnum
        calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ *
              (Real.exp (s.re ^ 2 / 100) * Real.exp (-(((|s.im| - 6.75) ^ 2) / 100)))
            = (‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ * Real.exp (-(((|s.im| - 6.75) ^ 2) / 100))) *
              Real.exp (s.re ^ 2 / 100) := by ring
          _ ≤ (18 * Real.exp 183.034) * Real.exp (s.re ^ 2 / 100) :=
              mul_le_mul_of_nonneg_right hcap (Real.exp_nonneg _)
          _ ≤ (18 * Real.exp 183.034) * Real.exp 0.04 :=
              mul_le_mul_of_nonneg_left hexp04 hBon_nn
          _ ≤ _ := le_trans (le_max_right _ _) (le_max_left _ _)
      · -- Middle, `τ ≤ 0`: Tier 2 + middle-neg numeral.
        have hmid2 : s.re ≤ (3 / 2 : ℝ) := le_of_not_ge hright
        have hF := hmid s hs hmid1 hmid2 htail
        have hnum := middle_gauss_neg_le hCnn hKnn h9
        have hFE : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ * Real.exp (-(((|s.im| - 6.75) ^ 2) / 100))
            ≤ Cmid * Real.exp (Kmid * (|s.im| ^ (3 / 2 : ℝ))) * Real.exp (-(((|s.im| - 6.75) ^ 2) / 100)) :=
          mul_le_mul_of_nonneg_right hF (Real.exp_nonneg _)
        have hcap : ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ * Real.exp (-(((|s.im| - 6.75) ^ 2) / 100))
            ≤ Cmid * Real.exp (1000000 * Kmid ^ 4 + 1) := le_trans hFE hnum
        calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ *
              (Real.exp (s.re ^ 2 / 100) * Real.exp (-(((|s.im| - 6.75) ^ 2) / 100)))
            = (‖ZetaUpperR02ThreeLines.poleRemovedZeta s‖ * Real.exp (-(((|s.im| - 6.75) ^ 2) / 100))) *
              Real.exp (s.re ^ 2 / 100) := by ring
          _ ≤ (Cmid * Real.exp (1000000 * Kmid ^ 4 + 1)) * Real.exp (s.re ^ 2 / 100) :=
              mul_le_mul_of_nonneg_right hcap (Real.exp_nonneg _)
          _ ≤ (Cmid * Real.exp (1000000 * Kmid ^ 4 + 1)) * Real.exp 0.04 :=
              mul_le_mul_of_nonneg_left hexp04 hTon_nn
          _ ≤ _ := le_trans (le_max_right _ _) (le_max_right _ _)

/-- (4b) Full-strip `hBdd`, UNCONDITIONAL: BU's tail premise discharged by `G_tail_bdd`. -/
theorem hBdd_unconditional :
    BddAbove ((norm ∘ ZetaUpperR02ThreeLines.dampedPoleRemoved) ''
      Complex.HadamardThreeLines.verticalClosedStrip (-1) 2) :=
  BUWindowed.hBdd_of_window_and_tail G_tail_bdd

/-- (4c) P1 conditional on BH2 `hTail` ONLY (BU's tail premise now discharged):
`‖ζ‖ ≤ 10` on the R02 rect. -/
theorem P1_R02_of_hTail
    (hTail : ∀ z ∈ Set.preimage Complex.re {(-1 : ℝ)}, 8.75 < |z.im| →
      ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤ 36)
    {s : ℂ} (hs_lo : 0.05 ≤ s.re) (hs_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25) :
    ‖riemannZeta s‖ ≤ 10 :=
  BUWindowed.P1_R02_of_window_and_tails hTail G_tail_bdd hs_lo hs_hi him_lo him_hi

#print axioms BZTailEnvelope.sin_ne_zero_of_tail_middle
#print axioms BZTailEnvelope.GammaR_tail_lower
#print axioms BZTailEnvelope.rpow32_eq_mul_sqrt
#print axioms BZTailEnvelope.sqrt_ge_three_of_nine_le
#print axioms BZTailEnvelope.abs_le_rpow32_div_three
#print axioms BZTailEnvelope.F_middle_tail_exp32
#print axioms BZTailEnvelope.middle_gauss_neg_le
#print axioms BZTailEnvelope.outer_gauss_neg_le
#print axioms BZTailEnvelope.G_tail_bdd
#print axioms BZTailEnvelope.hBdd_unconditional
#print axioms BZTailEnvelope.P1_R02_of_hTail

end BZTailEnvelope

/-!
BZ VERDICT + RESIDUAL (report-and-stop): door-3 tail-envelope assembly.
(1) GREEN: tail Gamma-lower via reflection on `9 < |Im|`
(`GammaR_tail_lower`, `3/(16·exp(2|Im|)) ≤ ‖Gammaℝ s‖`; tail numerals with BT's
strip sine-upper + reflected `U = 4`; sine-nonzero needs no puncture).
(2) GREEN: tail F-envelope via BL's xi-transfer fed with (1)
(`F_middle_tail_exp32`, `‖F‖ ≤ C·exp(K·|Im|^{3/2))}` on the tail middle;
`exp(2|Im|)` growth absorbed into `K = Kxi·2^{3/2}+2/3`).
(3) GREEN: negative-`τ` companion numerals (`middle_gauss_neg_le`,
`C·exp(10⁶K⁴+1)` cap; `outer_gauss_neg_le`, `18·exp(183.034)` cap).
(4) GREEN: tail-`T` assembled (`G_tail_bdd`) → BU's tail premise discharged →
`hBdd` UNCONDITIONAL (`hBdd_unconditional`) → P1 as far as honestly composes
(`P1_R02_of_hTail`, BH2 `hTail` the sole remaining explicit premise).
NOT reached (honest residual, needs Stirling-scale `F` bound, absent repo-wide):
BH2 `hTail` (`‖G‖ ≤ 36` on `Re = -1`, `8.75 < |Im|`); hence P1 stays conditional.
No `sorry`/`admit`/`axiom` in this tail.
-/

/-!
# CA2 tail (door-3 tier-1 minimum): off-window joint `Γ·cos` polynomial bound.

GOAL (brief tier 1, minimum viable): extend AR's on-window joint composition
(`Door3JointGammaCos.joint_Gamma_cos_le`, `|Im| ≤ 8.75 ⟹ ‖Γ·cos‖ ≤ 34`) OFF-window
to an honest `‖Γ·cos‖ ≤ POLY(|τ|)`-class bound for `8.75 < |Im|`.

METHOD: replay AR's EXACT identities (valid at ALL `Im`, grep-verified below) and
stop before AR's window numeral caps (`1+a² ≤ 77.5625`, `t+1 ≤ 3.1416·8.75/2+1`):
* `Door3JointGammaCos.Gamma_Re2_normSq`: `‖Γ(w)‖² = (1+y²)·πy/sinh(πy)` (`Re w = 2`);
* `Door3JointGammaCos.cos_Re2_norm`: `‖cos(πw/2)‖ = cosh(πy/2)`;
* `Door3JointGammaCos.t_mul_coth_le`: `t·coth t ≤ t+1`.
With `sinh πa = 2·sinh(πa/2)·cosh(πa/2)` this collapses to
`‖Γ·cos‖² ≤ (1+a²)·(πa/2+1)` (`a = |Im|`, squared-cubic ≈ `(π/2)·a³`) and, by AM-GM
(`AB ≤ ((A+B)/2)²` + `Real.sqrt_le_sqrt`), to the norm-quadratic
`‖Γ·cos‖ ≤ ((1+a²)+(πa/2+1))/2` (≈ `a²/2`). Both are POLY-class (polynomial
preferred per brief). The `Re = -1` wrappers restate this at `w = 1-z` (the FE
mirror used by `BH2TailWindow`/hTail assembly), so this plugs directly into the
tail `F`-envelope work.

BZ `S`/`U` ROUTE (grep record): `BZTailEnvelope.GammaR_tail_lower` gives
`3/(16·exp(2|Im|)) ≤ ‖Gammaℝ s‖` (a LOWER via `BTStripGamma.sin_pi_half_strip_upper`
`S = exp(2|Im|)` + `gamma_one_sub_half_strip_upper` `U = 4`); it bounds `Gammaℝ`
from BELOW on the middle third and hence cannot supply the UPPER joint bound
needed here. It was considered and honestly NOT used: the exact AR identities
already give a sharper (polynomial, not exponential) upper at all `Im`.

DAMPING (grep record): `BH2TailWindow.damp_left_tail_le_one` gives damping `≤ 1`
on this exact tail (`Re = -1`, `8.75 ≤ |Im|`). Full hTail composition
(`‖G‖ ≤ 36` via Gaussian decay beating the polynomial above) is NOT attempted
per brief — report-and-stop after tier 1.
Grep stems checked in-file: `Gamma_one_add_im_normSq`, `t_mul_coth_le`,
`GammaR_tail_lower`, `damp_left_tail_le_one`, `P1_R02_of_hTail`.
No `sorry`/`admit`/`axiom` in this tail.
-/

namespace CA2TailJoint

/-- Squared off-window joint bound on `Re = 2`: `‖Γ·cos‖² ≤ (1+a²)·(πa/2+1)`
with `a = |Im|`, for every nonzero `Im` (no window cap). Proof replays AR's
`sinh`-doubling collapse (`hsinh2`/`hstep`) and `t_mul_coth_le`. -/
theorem joint_sq_tail {w : ℂ} (hw : w.re = 2) (hy : w.im ≠ 0) :
    ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ ^ 2
      ≤ (1 + |w.im| ^ 2) * (Real.pi * |w.im| / 2 + 1) := by
  have hG := Door3JointGammaCos.Gamma_Re2_normSq hw hy
  have hC := Door3JointGammaCos.cos_Re2_norm hw
  have ha_pos : 0 < |w.im| := abs_pos.mpr hy
  have hpi : 0 < Real.pi := Real.pi_pos
  have hthal_pos : 0 < Real.pi * |w.im| / 2 := by
    have h2 := mul_pos (mul_pos hpi ha_pos) (show (0 : ℝ) < 1 / 2 by norm_num)
    linarith
  have hsinh_half_pos : 0 < Real.sinh (Real.pi * |w.im| / 2) :=
    Real.sinh_pos_iff.mpr hthal_pos
  have hcosh_pos : 0 < Real.cosh (Real.pi * |w.im| / 2) := Real.cosh_pos _
  have hsymm : Real.pi * w.im / Real.sinh (Real.pi * w.im)
      = Real.pi * |w.im| / Real.sinh (Real.pi * |w.im|) := by
    rcases le_total w.im 0 with hynonpos | hynonneg
    · have hyneg : w.im < 0 := lt_of_le_of_ne hynonpos hy
      rw [abs_of_neg hyneg, show Real.pi * -w.im = -(Real.pi * w.im) by ring,
        Real.sinh_neg, neg_div_neg_eq]
    · rw [abs_of_nonneg hynonneg]
  have heven : Real.cosh (Real.pi * w.im / 2)
      = Real.cosh (Real.pi * |w.im| / 2) := by
    rcases le_total w.im 0 with hynonpos | hynonneg
    · have hyneg : w.im < 0 := lt_of_le_of_ne hynonpos hy
      rw [abs_of_neg hyneg,
        show Real.pi * -w.im / 2 = -(Real.pi * w.im / 2) by ring, Real.cosh_neg]
    · rw [abs_of_nonneg hynonneg]
  have hsinh2 : Real.sinh (Real.pi * |w.im|)
      = 2 * Real.sinh (Real.pi * |w.im| / 2)
        * Real.cosh (Real.pi * |w.im| / 2) := by
    have hdouble : Real.pi * |w.im| = 2 * (Real.pi * |w.im| / 2) := by ring
    conv_lhs => rw [hdouble]
    rw [Real.sinh_two_mul]
  have hsinh_half_ne : Real.sinh (Real.pi * |w.im| / 2) ≠ 0 :=
    ne_of_gt hsinh_half_pos
  have hcosh_ne : Real.cosh (Real.pi * |w.im| / 2) ≠ 0 := ne_of_gt hcosh_pos
  have hden_ne : 2 * Real.sinh (Real.pi * |w.im| / 2)
      * Real.cosh (Real.pi * |w.im| / 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hsinh_half_ne) hcosh_ne
  have hstep : (1 + |w.im| ^ 2)
          * (Real.pi * |w.im| / Real.sinh (Real.pi * |w.im|))
          * (Real.cosh (Real.pi * |w.im| / 2)) ^ 2
      = (1 + |w.im| ^ 2)
        * ((Real.pi * |w.im| / 2)
          * (Real.cosh (Real.pi * |w.im| / 2)
            / Real.sinh (Real.pi * |w.im| / 2))) := by
    rw [hsinh2]
    field_simp
  have hcoth := Door3JointGammaCos.t_mul_coth_le hthal_pos
  have hnonneg : (0 : ℝ) ≤ 1 + |w.im| ^ 2 := by positivity
  have e1 : ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ ^ 2
      = ‖Complex.Gamma w‖ ^ 2 * ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖ ^ 2 := by
    rw [norm_mul, mul_pow]
  rw [e1, hG, hC, hsymm, heven, ← sq_abs w.im, hstep]
  exact mul_le_mul_of_nonneg_left hcoth hnonneg

/-- Norm-quadratic off-window joint bound via AM-GM (`AB ≤ ((A+B)/2)²` then
`Real.sqrt_le_sqrt`/`Real.sqrt_sq`, mirroring AR's sqrt close). -/
theorem joint_poly_tail {w : ℂ} (hw : w.re = 2) (hy : w.im ≠ 0) :
    ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖
      ≤ ((1 + |w.im| ^ 2) + (Real.pi * |w.im| / 2 + 1)) / 2 := by
  have hsq := joint_sq_tail hw hy
  have hBnn : (0 : ℝ) ≤ Real.pi * |w.im| / 2 + 1 := by
    have h1 : (0 : ℝ) ≤ Real.pi * |w.im| / 2 := by
      have hmul := mul_nonneg Real.pi_pos.le (abs_nonneg w.im)
      linarith
    linarith
  have hmid : (0 : ℝ) ≤ ((1 + |w.im| ^ 2) + (Real.pi * |w.im| / 2 + 1)) / 2 := by
    have hA : (0 : ℝ) ≤ 1 + |w.im| ^ 2 := by positivity
    linarith
  have hamgm : (1 + |w.im| ^ 2) * (Real.pi * |w.im| / 2 + 1)
      ≤ (((1 + |w.im| ^ 2) + (Real.pi * |w.im| / 2 + 1)) / 2) ^ 2 := by
    have h := sq_nonneg ((1 + |w.im| ^ 2) - (Real.pi * |w.im| / 2 + 1))
    nlinarith
  have hle : ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ ^ 2
      ≤ ((((1 + |w.im| ^ 2) + (Real.pi * |w.im| / 2 + 1)) / 2)) ^ 2 :=
    le_trans hsq hamgm
  have hle2 := Real.sqrt_le_sqrt hle
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hmid] at hle2
  exact hle2

/-- Fully-numeric off-window joint bound (`π ≤ 3.1416` via `Real.pi_lt_d4`,
same numeral as AR's window cap). -/
theorem joint_poly_tail_numeric {w : ℂ} (hw : w.re = 2) (hy : w.im ≠ 0) :
    ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖
      ≤ ((1 + |w.im| ^ 2) + (3.1416 * |w.im| / 2 + 1)) / 2 := by
  have h := joint_poly_tail hw hy
  have hpile : Real.pi ≤ 3.1416 := le_of_lt Real.pi_lt_d4
  have hmono : Real.pi * |w.im| / 2 + 1 ≤ 3.1416 * |w.im| / 2 + 1 := by
    have h1 : Real.pi * |w.im| ≤ 3.1416 * |w.im| :=
      mul_le_mul_of_nonneg_right hpile (abs_nonneg _)
    linarith
  linarith

/-- Squared joint bound at the FE mirror `w = 1 - z` for `z` on the hTail line
(`Re = -1`, `8.75 < |Im|`): same polynomial in `|z.im|`. -/
theorem joint_sq_of_Re_neg1 {z : ℂ} (hz : z.re = -1) (htail : 8.75 < |z.im|) :
    ‖Complex.Gamma (1 - z) * Complex.cos ((Real.pi : ℂ) * (1 - z) / 2)‖ ^ 2
      ≤ (1 + |z.im| ^ 2) * (Real.pi * |z.im| / 2 + 1) := by
  have hw_re : ((1 : ℂ) - z).re = 2 := by
    rw [Complex.sub_re, Complex.one_re, hz]
    norm_num
  have hw_im : ((1 : ℂ) - z).im = -z.im := by
    rw [Complex.sub_im, Complex.one_im, zero_sub]
  have hne : z.im ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at htail
    norm_num at htail
  have hy : ((1 : ℂ) - z).im ≠ 0 := by
    rw [hw_im]
    exact neg_ne_zero.mpr hne
  have h := joint_sq_tail hw_re hy
  rwa [hw_im, abs_neg] at h

/-- Norm-quadratic joint bound at the FE mirror `w = 1 - z` on the hTail line. -/
theorem joint_poly_of_Re_neg1 {z : ℂ} (hz : z.re = -1) (htail : 8.75 < |z.im|) :
    ‖Complex.Gamma (1 - z) * Complex.cos ((Real.pi : ℂ) * (1 - z) / 2)‖
      ≤ ((1 + |z.im| ^ 2) + (Real.pi * |z.im| / 2 + 1)) / 2 := by
  have hw_re : ((1 : ℂ) - z).re = 2 := by
    rw [Complex.sub_re, Complex.one_re, hz]
    norm_num
  have hw_im : ((1 : ℂ) - z).im = -z.im := by
    rw [Complex.sub_im, Complex.one_im, zero_sub]
  have hne : z.im ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at htail
    norm_num at htail
  have hy : ((1 : ℂ) - z).im ≠ 0 := by
    rw [hw_im]
    exact neg_ne_zero.mpr hne
  have h := joint_poly_tail hw_re hy
  rwa [hw_im, abs_neg] at h

#print axioms CA2TailJoint.joint_sq_tail
#print axioms CA2TailJoint.joint_poly_tail
#print axioms CA2TailJoint.joint_poly_tail_numeric
#print axioms CA2TailJoint.joint_sq_of_Re_neg1
#print axioms CA2TailJoint.joint_poly_of_Re_neg1

end CA2TailJoint

/-!
CA2 VERDICT + RESIDUAL (report-and-stop): tier-1 minimum GREEN.
(1) `CA2TailJoint.joint_sq_tail`: off-window squared joint bound
`‖Γ·cos‖² ≤ (1+a²)·(πa/2+1)`, all `Im ≠ 0` on `Re = 2` (squared-cubic POLY-class).
(2) `CA2TailJoint.joint_poly_tail[_numeric]`: norm-quadratic POLY-class bound
`‖Γ·cos‖ ≤ ((1+a²)+(πa/2+1))/2` (numeric: `π → 3.1416`).
(3) `CA2TailJoint.joint_sq_of_Re_neg1` / `joint_poly_of_Re_neg1`: same bounds at
the FE mirror `w = 1-z` on the hTail line (`Re = -1`, `8.75 < |Im|`), directly
pluggable into the tail `F`-envelope.
NOT attempted per brief: hTail composition (`‖G‖ ≤ 36` needs Gaussian decay vs
the polynomial above) and P1. Residual stays: BH2 `hTail` + strip `hBdd`-class
inputs (already mapped by BZ/BH2; `P1_R02_of_hTail` consumes `hTail` only).
No `sorry`/`admit`/`axiom` in this tail.
-/

/-!
# CC tail (door-3 hTail composition, honest cap + gap -- report-and-stop)

Ownership: Agent CC tail append (append-only after the CA2 verdict block; nothing above
touched; no new imports).

GOAL (door-3 hTail composition): on `Re = -1`, `8.75 < |Im|`, bound
`‖G‖ = ‖damp‖ * ‖F‖ ≤ 1 * (joint-poly via CA2 + FE) ≤ 36` with `norm_num`-checked
crossover numerals (if the joint bound exceeds 36 at 8.75, find the crossover `|Im|*`
where it dips below and bridge `[8.75, *]` with AR window monotonicity; if NO crossover
exists below a sane bound, prove the SHARPEST honest cap and quantify the gap to 36).

GREP-FIRST RECORD (verified by `rg -n` on this file + `interval_arith.lean` before writing):
* `CA2TailJoint.joint_poly_tail_numeric` (this file, CA2): norm-quadratic joint bound
  `‖Gamma w * cos(pi*w/2)‖ ≤ ((1+|w.im|^2)+(3.1416*|w.im|/2+1))/2` on `Re = 2`,
  `w.im ≠ 0` -- USED (feeds `factor_le` below).
* `CA2TailJoint.joint_poly_of_Re_neg1` (this file, CA2): same bound restated at the FE
  mirror `w = 1-z` on the hTail line -- CITED (conceptual link; the numeric version above
  is what carries numerals).
* `BH2TailWindow.damp_left_tail_le_one` (this file, BH2): damping `≤ 1` on
  `Re = -1`, `8.75 ≤ |Im|` -- USED (feeds `G_le` below).
* `BZTailEnvelope.GammaR_tail_lower` (this file, BZ): tail Gamma-lower
  `3/(16*exp(2|Im|)) ≤ ‖GammaR s‖` on the middle third -- CONSIDERED and honestly NOT
  USED for the UPPER joint bound (it is a LOWER via reflection `S = exp(2|Im|)`,
  `U = 4`; it bounds `GammaR` from BELOW and hence cannot supply the UPPER needed here;
  same verdict as CA2's own BZ-route note).
* `BV2OuterTail.outer_gauss_le` (`T = 18*exp(165.225316)`) + `BXMiddleTail.middle_gauss_le`
  / `young_rpow32` (Young `K*u^(3/2) ≤ u^2/200+10^6*K^4`): Gaussian-domination numerals for
  exp-linear / exp-3/2 strip envelopes with the `(u+6.75)^2` (nonnegative-`τ`) form --
  CONSIDERED and honestly NOT USED here (they dominate strip tail-`T` envelopes for
  `hBdd`, not the `Re = -1` FE poly route; the hTail line needs both signs and the FE
  `Gamma*cos` poly, not an `exp(K*|Im|^(3/2))` envelope).
* `BZTailEnvelope.P1_R02_of_hTail` (this file, BZ): P1 `‖zeta‖ ≤ 10` on R02 with `hTail`
  (`‖G‖ ≤ 36` on `Re = -1`, `8.75 < |Im|`) as the SOLE premise -- CITED but NOT FIRED
  (fires ONLY if hTail closes at 36; it does not -- see cap/gap below).
* `DerivCauchyBridge.R02_zeta_upper_obligation` -- NOT discharged (needs P1, which needs
  hTail at 36).

WHAT IS PROVED (all full proofs, no `sorry`/`admit`/`axiom`):
* `sub_le`: `‖z-1‖ ≤ 2+|z.im|` on `Re = -1` (triangle via `norm_le_abs_re_add_abs_im`).
* `factor_le`: `‖RowFEFactor (1-z)‖ ≤ X(|z.im|)` with
  `X(a) = (1+a^2)+(3.1416*a/2+1)` (cpow `≤ 1` via `RowFE_cpow_upper` + CA2 numeric joint
  bound, `2*(X/2) = X` by `ring`).
* `zeta_le`: `‖riemannZeta z‖ ≤ 2*X(|z.im|)` (FE `riemannZeta_one_sub` at `1-z` +
  reflected `‖zeta‖ ≤ 2` via `TailZetaUpper.zeta_rightEdge_B2`).
* `F_le`: `‖poleRemovedZeta z‖ ≤ (2+|z.im|)*(2*X(|z.im|))` (`(z-1)*zeta`).
* `G_le` (MAIN pointwise): `‖dampedPoleRemoved z‖ ≤ (2+|z.im|)*(2*X(|z.im|))`
  (damping `≤ 1` via `BH2TailWindow.damp_left_tail_le_one`).
* `bound_at_875`: `B(8.75) = 1984.6005` (`norm_num`; `B(a) = (2+a)*(2*X(a))`).
* `gap_at_875`: `B(8.75)-36 = 1948.6005` (`norm_num`).
* `bound_mono`: `B(8.75) ≤ B(a)` for `8.75 ≤ a` (both factors increasing;
  `a^2-8.75^2 = (a-8.75)*(a+8.75) ≥ 0` + linear `3.1416*(a-8.75)/2 ≥ 0` +
  `mul_le_mul`).
* `no_crossover`: `36 < B(|z.im|)` for every `8.75 < |z.im|` (hence the `1*poly`
  majorant NEVER dips below 36 on the tail -- NO crossover exists at any sane bound;
  the infimum on the tail is `B(8.75) = 1984.6005`).
* `sharpest_cap_gap` (MAIN cap+gap): packages `G_le` + `bound_at_875` + `bound_mono` +
  `no_crossover` -- the SHARPEST honest cap from the landed `damp ≤ 1` + CA2-poly
  pieces is the pointwise `B(|Im|)` with minimum `1984.6005`, gap `1948.6005`
  (`~55x` over 36). hTail (`≤ 36`) does NOT follow from this majorant; P1
  (`P1_R02_of_hTail`) and `R02_zeta_upper_obligation` are therefore NOT fired
  (report-and-stop per brief).
-/

namespace CC_hTailGap

/-- `‖z-1‖ ≤ 2+|z.im|` on `Re = -1` (triangle). -/
theorem sub_le {z : ℂ} (hz : z.re = -1) : ‖z - 1‖ ≤ 2 + |z.im| := by
  have h := Complex.norm_le_abs_re_add_abs_im (z - 1)
  have hre1 : (z - 1).re = -2 := by
    rw [Complex.sub_re, Complex.one_re, hz]
    norm_num
  have him1 : (z - 1).im = z.im := by
    rw [Complex.sub_im, Complex.one_im, sub_zero]
  rw [hre1, him1] at h
  have eabs : |(-2 : ℝ)| = 2 := by norm_num
  rw [eabs] at h
  exact h

/-- FE-factor joint cap on the hTail mirror: `‖RowFEFactor (1-z)‖ ≤ X(|z.im|)`. -/
theorem factor_le {z : ℂ} (hz : z.re = -1) (htail : 8.75 < |z.im|) :
    ‖RowFE.RowFEFactor (1 - z)‖ ≤
      (1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1) := by
  have hw_re : ((1 : ℂ) - z).re = 2 := by
    rw [Complex.sub_re, Complex.one_re, hz]
    norm_num
  have hw_im : ((1 : ℂ) - z).im = -z.im := by
    rw [Complex.sub_im, Complex.one_im, zero_sub]
  have hne : z.im ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at htail
    norm_num at htail
  have hy : ((1 : ℂ) - z).im ≠ 0 := by
    rw [hw_im]
    exact neg_ne_zero.mpr hne
  have hcp : ‖(2 * (Real.pi : ℂ)) ^ (-(1 - z))‖ ≤ 1 :=
    RowFE.RowFE_cpow_upper (by rw [hw_re]; norm_num)
  have hjoint : ‖Complex.Gamma (1 - z) *
      Complex.cos ((Real.pi : ℂ) * (1 - z) / 2)‖ ≤
      ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)) / 2 := by
    have h := CA2TailJoint.joint_poly_tail_numeric hw_re hy
    rwa [hw_im, abs_neg] at h
  have eRow : RowFE.RowFEFactor (1 - z) =
      (2 : ℂ) * (((2 * (Real.pi : ℂ)) ^ (-(1 - z))) *
        (Complex.Gamma (1 - z) *
          Complex.cos ((Real.pi : ℂ) * (1 - z) / 2))) := by
    unfold RowFE.RowFEFactor
    ring
  have e2 : ‖(2 : ℂ)‖ = 2 := by simp
  have hnorm_eq : ‖RowFE.RowFEFactor (1 - z)‖ =
      2 * (‖(2 * (Real.pi : ℂ)) ^ (-(1 - z))‖ *
        ‖Complex.Gamma (1 - z) *
          Complex.cos ((Real.pi : ℂ) * (1 - z) / 2)‖) := by
    rw [eRow, norm_mul, e2, norm_mul]
  have hprod : ‖(2 * (Real.pi : ℂ)) ^ (-(1 - z))‖ *
      ‖Complex.Gamma (1 - z) *
        Complex.cos ((Real.pi : ℂ) * (1 - z) / 2)‖ ≤
      1 * ((((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)) / 2)) :=
    mul_le_mul hcp hjoint (norm_nonneg _) (by norm_num)
  calc ‖RowFE.RowFEFactor (1 - z)‖
      = 2 * (‖(2 * (Real.pi : ℂ)) ^ (-(1 - z))‖ *
        ‖Complex.Gamma (1 - z) *
          Complex.cos ((Real.pi : ℂ) * (1 - z) / 2)‖) := hnorm_eq
    _ ≤ 2 * (1 * ((((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)) / 2))) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = (1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1) := by ring

/-- Zeta cap on the hTail line via FE: `‖zeta z‖ ≤ 2*X(|z.im|)`. -/
theorem zeta_le {z : ℂ} (hz : z.re = -1) (htail : 8.75 < |z.im|) :
    ‖riemannZeta z‖ ≤
      2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)) := by
  have hw_re : ((1 : ℂ) - z).re = 2 := by
    rw [Complex.sub_re, Complex.one_re, hz]
    norm_num
  have hs_neg : ∀ n : ℕ, (1 - z) ≠ -((n : ℂ)) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re,
      Complex.natCast_re] at hre
    rw [hz] at hre
    have hnn : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg n
    linarith
  have hs1' : (1 - z) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re] at hre
    rw [hz] at hre
    norm_num at hre
  have hFE' : riemannZeta z =
      RowFE.RowFEFactor (1 - z) * riemannZeta (1 - z) := by
    have hFE := riemannZeta_one_sub (s := 1 - z) hs_neg hs1'
    have h1sub : (1 : ℂ) - (1 - z) = z := by ring
    rw [h1sub] at hFE
    have h2 : (2 * (2 * (Real.pi : ℂ)) ^ (-(1 - z)) * Complex.Gamma (1 - z)
        * Complex.cos ((Real.pi : ℂ) * (1 - z) / 2) * riemannZeta (1 - z))
        = RowFE.RowFEFactor (1 - z) * riemannZeta (1 - z) := by
      unfold RowFE.RowFEFactor
      ring
    rw [← h2]
    exact hFE
  have hZrefl : ‖riemannZeta (1 - z)‖ ≤ 2 := by
    have h := TailZetaUpper.zeta_rightEdge_B2 (s := 1 - z) (by linarith [hw_re])
    rwa [show zeta (1 - z) = riemannZeta (1 - z) from rfl] at h
  have hFactor := factor_le hz htail
  have hXnn : (0 : ℝ) ≤ (1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1) := by
    have ha : (0 : ℝ) ≤ |z.im| := abs_nonneg _
    have h1 : (0 : ℝ) ≤ |z.im| ^ 2 := sq_nonneg _
    have hmul : (0 : ℝ) ≤ 3.1416 * |z.im| :=
      mul_nonneg (by norm_num) ha
    have h2 : (0 : ℝ) ≤ 3.1416 * |z.im| / 2 := by linarith
    linarith
  rw [hFE', norm_mul]
  calc ‖RowFE.RowFEFactor (1 - z)‖ * ‖riemannZeta (1 - z)‖
      ≤ ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)) * 2 :=
        mul_le_mul hFactor hZrefl (norm_nonneg _) hXnn
    _ = 2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)) := by ring

/-- Pole-removed cap on the hTail line: `‖F z‖ ≤ (2+|Im|)*(2*X(|Im|))`. -/
theorem F_le {z : ℂ} (hz : z.re = -1) (htail : 8.75 < |z.im|) :
    ‖ZetaUpperR02ThreeLines.poleRemovedZeta z‖ ≤
      (2 + |z.im|) * (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1))) := by
  have hz1 : z ≠ 1 := by
    intro h
    have hre : z.re = 1 := by rw [h, Complex.one_re]
    linarith
  have hsub := sub_le hz
  have hZ := zeta_le hz htail
  have hb_nn : (0 : ℝ) ≤ 2 + |z.im| := by
    have ha : (0 : ℝ) ≤ |z.im| := abs_nonneg _
    linarith
  rw [ZetaUpperR02ThreeLines.poleRemovedZeta_of_ne hz1, norm_mul]
  calc ‖z - 1‖ * ‖riemannZeta z‖
      ≤ (2 + |z.im|) * (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1))) :=
        mul_le_mul hsub hZ (norm_nonneg _) hb_nn

/-- MAIN pointwise hTail majorant: `‖G z‖ ≤ (2+|Im|)*(2*X(|Im|))` via damping `≤ 1`. -/
theorem G_le {z : ℂ} (hz : z.re = -1) (htail : 8.75 < |z.im|) :
    ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤
      (2 + |z.im|) * (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1))) := by
  have hF := F_le hz htail
  have hdamp : ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
      (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ ≤ 1 :=
    BH2TailWindow.damp_left_tail_le_one hz (le_of_lt htail)
  have hBnn : (0 : ℝ) ≤
      (2 + |z.im|) * (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1))) := by
    have ha : (0 : ℝ) ≤ |z.im| := abs_nonneg _
    have h1 : (0 : ℝ) ≤ |z.im| ^ 2 := sq_nonneg _
    have hmul : (0 : ℝ) ≤ 3.1416 * |z.im| :=
      mul_nonneg (by norm_num) ha
    have h2 : (0 : ℝ) ≤ 3.1416 * |z.im| / 2 := by linarith
    have hX : (0 : ℝ) ≤ (1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1) := by
      linarith
    have h2X : (0 : ℝ) ≤ 2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)) := by
      linarith
    have hb : (0 : ℝ) ≤ 2 + |z.im| := by linarith
    exact mul_nonneg hb h2X
  have hfin : ZetaUpperR02ThreeLines.dampedPoleRemoved z =
      ZetaUpperR02ThreeLines.poleRemovedZeta z *
        Complex.exp (((1 / 100 : ℝ) : ℂ) *
          (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2) := rfl
  rw [hfin, norm_mul]
  calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta z‖ *
      ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
        (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖
      ≤ ((2 + |z.im|) * (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)))) * 1 :=
        mul_le_mul hF hdamp (norm_nonneg _) hBnn
    _ = (2 + |z.im|) * (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1))) := by
        rw [mul_one]

/-- Numeral at the window edge: `B(8.75) = 1984.6005` (`norm_num`). -/
theorem bound_at_875 :
    (2 + (8.75 : ℝ)) * (2 * ((1 + (8.75 : ℝ) ^ 2) + (3.1416 * (8.75 : ℝ) / 2 + 1)))
      = 1984.6005 := by
  norm_num

/-- Gap at the window edge: `B(8.75)-36 = 1948.6005` (`norm_num`). -/
theorem gap_at_875 :
    (2 + (8.75 : ℝ)) * (2 * ((1 + (8.75 : ℝ) ^ 2) + (3.1416 * (8.75 : ℝ) / 2 + 1)))
      - 36 = 1948.6005 := by
  norm_num

/-- Edge exceeds 36: `36 < B(8.75)` (`norm_num` via `bound_at_875`). -/
theorem bound_gt_36 :
    (36 : ℝ) < (2 + (8.75 : ℝ)) *
      (2 * ((1 + (8.75 : ℝ) ^ 2) + (3.1416 * (8.75 : ℝ) / 2 + 1))) := by
  have hEq := bound_at_875
  linarith

/-- Monotonicity: `B(8.75) ≤ B(a)` for `8.75 ≤ a` (both factors increasing). -/
theorem bound_mono {a : ℝ} (ha : 8.75 ≤ a) :
    (2 + (8.75 : ℝ)) * (2 * ((1 + (8.75 : ℝ) ^ 2) + (3.1416 * (8.75 : ℝ) / 2 + 1)))
      ≤ (2 + a) * (2 * ((1 + a ^ 2) + (3.1416 * a / 2 + 1))) := by
  have h1 : (2 + (8.75 : ℝ)) ≤ 2 + a := by linarith
  have hsq : (8.75 : ℝ) ^ 2 ≤ a ^ 2 := by
    have hsub_nn : (0 : ℝ) ≤ a - 8.75 := by linarith
    have hadd_nn : (0 : ℝ) ≤ a + 8.75 := by linarith
    have hprod_nn : (0 : ℝ) ≤ (a - 8.75) * (a + 8.75) :=
      mul_nonneg hsub_nn hadd_nn
    have e : (a - 8.75) * (a + 8.75) = a ^ 2 - 8.75 ^ 2 := by ring
    linarith
  have hX : (1 + (8.75 : ℝ) ^ 2) + (3.1416 * (8.75 : ℝ) / 2 + 1)
      ≤ (1 + a ^ 2) + (3.1416 * a / 2 + 1) := by
    have hmul : 3.1416 * 8.75 ≤ 3.1416 * a :=
      mul_le_mul_of_nonneg_left ha (by norm_num)
    have hlin : 3.1416 * (8.75 : ℝ) / 2 ≤ 3.1416 * a / 2 := by linarith
    linarith [hsq, hlin]
  have h2X : 2 * ((1 + (8.75 : ℝ) ^ 2) + (3.1416 * (8.75 : ℝ) / 2 + 1))
      ≤ 2 * ((1 + a ^ 2) + (3.1416 * a / 2 + 1)) := by linarith [hX]
  have hXnn : (0 : ℝ) ≤
      2 * ((1 + (8.75 : ℝ) ^ 2) + (3.1416 * (8.75 : ℝ) / 2 + 1)) := by norm_num
  have hb_nn : (0 : ℝ) ≤ 2 + a := by linarith
  exact mul_le_mul h1 h2X hXnn hb_nn

/-- NO crossover: the `1*poly` majorant exceeds 36 everywhere on the tail. -/
theorem no_crossover {z : ℂ} (htail : 8.75 < |z.im|) :
    (36 : ℝ) < (2 + |z.im|) *
      (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1))) := by
  have ha : 8.75 ≤ |z.im| := le_of_lt htail
  have hmono := bound_mono ha
  have hgt := bound_gt_36
  linarith

/-- SHARPEST honest cap+gap: pointwise `B(|Im|)` with minimum `1984.6005`, gap `1948.6005`. -/
theorem sharpest_cap_gap {z : ℂ} (hz : z.re = -1) (htail : 8.75 < |z.im|) :
    ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤
        (2 + |z.im|) * (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)))
      ∧ (2 + (8.75 : ℝ)) *
          (2 * ((1 + (8.75 : ℝ) ^ 2) + (3.1416 * (8.75 : ℝ) / 2 + 1))) = 1984.6005
      ∧ (2 + (8.75 : ℝ)) *
          (2 * ((1 + (8.75 : ℝ) ^ 2) + (3.1416 * (8.75 : ℝ) / 2 + 1)))
          ≤ (2 + |z.im|) * (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)))
      ∧ (36 : ℝ) < (2 + |z.im|) *
          (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1))) := by
  exact ⟨G_le hz htail, bound_at_875, bound_mono (le_of_lt htail), no_crossover htail⟩

#print axioms CC_hTailGap.sub_le
#print axioms CC_hTailGap.factor_le
#print axioms CC_hTailGap.zeta_le
#print axioms CC_hTailGap.F_le
#print axioms CC_hTailGap.G_le
#print axioms CC_hTailGap.bound_at_875
#print axioms CC_hTailGap.gap_at_875
#print axioms CC_hTailGap.bound_gt_36
#print axioms CC_hTailGap.bound_mono
#print axioms CC_hTailGap.no_crossover
#print axioms CC_hTailGap.sharpest_cap_gap

end CC_hTailGap

/-!
CC VERDICT + RESIDUAL (report-and-stop): door-3 hTail composition HONEST NEGATIVE.
(1) hTail NOT CLOSED at 36: the landed `damp ≤ 1` (BH2) + CA2-poly (FE `Gamma*cos`)
majorant gives the pointwise cap `‖G(z)‖ ≤ B(|z.im|)` with
`B(a) = (2+a)*(2*((1+a^2)+(3.1416*a/2+1)))` (`CC_hTailGap.G_le`, FULL proof, no sorry).
At the window edge `B(8.75) = 1984.6005` (`bound_at_875`, `norm_num`), gap
`B(8.75)-36 = 1948.6005` (`gap_at_875`, `norm_num`; `~55x` over 36). `B` is increasing
for `a ≥ 8.75` (`bound_mono`), so `36 < B(|z.im|)` for EVERY `8.75 < |z.im|`
(`no_crossover`) -- NO crossover `|Im|*` exists at ANY sane bound for this majorant
(the cubic `~2*a^3` grows; damping `≤ 1` cannot beat it). Hence the `[8.75, *]` bridge
with AR's windowed cap (`Door3JointGammaCos.damped_joint_window`, `‖G‖ ≤ 36` for
`|Im| ≤ 8.75`) by explicit monotonicity is VACUOUS (nothing to bridge to -- the tail
majorant never reaches 36). The SHARPEST honest cap from these pieces is `B(|Im|)`
itself (`sharpest_cap_gap`); true `‖G‖` with sharp Gaussian damping DOES eventually
decay, but that needs Stirling-sharp `Γ·cos` + Gaussian joint analysis (absent
repo-wide) and is NOT claimed here.
(2) P1 NOT fired (per brief, ONLY if (1) closes at 36): `BZTailEnvelope.P1_R02_of_hTail`
(`hTail` sole premise ⇒ P1 `‖zeta‖ ≤ 10` on R02) stays conditional on the unclosed
`hTail`; `DerivCauchyBridge.R02_zeta_upper_obligation` stays open for the same reason.
hTail verdict: CAP + GAP (`B(8.75) = 1984.6005`, gap `1948.6005`, no crossover).
P1 verdict: CONDITIONAL (needs `hTail` at 36, not met).
Residual: `hTail` (`‖G‖ ≤ 36` on `Re = -1`, `8.75 < |Im|`) needs Stirling-sharp tail
`F`-bound (true `‖F‖ ~ |τ|^2.5` vs proved `~2*|τ|^3`; sharp Gaussian vs `≤ 1` damping);
then `P1_R02_of_hTail` fires immediately.
No `sorry`/`admit`/`axiom` in this tail.
-/





/-!
# CF tail (door-3 hTail SHARP Gaussian damping composition -- report-and-stop)

Ownership: Agent CF tail append (append-only after the CC verdict block; nothing above
touched; no new imports).

GOAL (door-3 hTail, minimum viable = ONE sharpener green): re-run CC's composition with
the HONEST Gaussian damping `‖damp z‖ = Real.exp ((1-(τ+6.75)^2)/100)` on `Re = -1`
(not `≤ 1`): `‖G z‖ ≤ B_sharp(τ)` where `B_sharp(τ) = exp((1-(τ+6.75)^2)/100)*B(|τ|)`
and `B` is CC's cubic joint majorant. Honest edge numerals via `norm_num`.

SIGN SPLIT (honest -- the Gaussian is centered at `τ = -6.75`, NOT at `0`):
* positive side (`τ > 8.75`): damping at edge `= exp(-2.3925)` (true `≈ 0.0914`), proved
  `≤ 0.1`; sharp edge `≤ 198.46005` (gap `162.46005`, between `5x` and `6x` over 36).
* negative side (`τ < -8.75`): damping at edge `= exp(-0.03)` (true `≈ 0.9704`), proved
  `≤ 0.971`; sharp edge `≤ 1927.0470855` (gap `1891.0470855`, between `53x` and `54x`
  over 36) -- barely better than CC's `1984.6005`, because the Gaussian center sits
  near the negative tail.
A single `B_sharp(|Im|)` carrying the `0.09` factor uniformly would be FALSE on the
negative side, so it is NOT stated; the exact-factor `G_le_sharp` holds on both sides
and the numerals are proved per side.

GREP-FIRST RECORD (verified by `rg -n` before writing):
* `CC_hTailGap.F_le` (this file, `:6363`): `‖F z‖ ≤ (2+|Im|)*(2*X(|Im|))` on `Re = -1`,
  `8.75 < |Im|` -- USED (feeds `G_le_sharp`; CC's cubic joint bound is re-run as-is,
  never rebuilt).
* `CC_hTailGap.bound_at_875` / `bound_mono` (this file, `:6415`/`:6434`):
  `B(8.75) = 1984.6005`, `B` increasing -- USED (edge numerals are `0.1*B(8.75)` and
  `0.971*B(8.75)` multiples; `bound_mono` feeds the packaging theorem).
* `BH2TailWindow.damp_re_general` (this file, `:3623`): damping real part
  `(σ^2-(τ+6.75)^2)/100` -- USED (feeds `damp_norm_eq_neg1`).
* `ZetaUpperR02ThreeLines.norm_complex_exp` (this file, `:1227`):
  `‖exp w‖ = exp (w.re)` -- USED (feeds `damp_norm_eq_neg1`).
* `ZetaUpperR02ThreeLines.dampedPoleRemoved` (this file, `:1134`):
  `G = F * damp` by `rfl` (per CC's `hfin`) -- USED (feeds `G_le_sharp`).
* `BF2TailCaps.exp_neg_le_inv` (this file, `:3399`): `exp(-t) ≤ 1/(1+t)` -- USED, but
  ONLY for the negative side (`exp(-0.03) ≤ 0.971`); on the positive side `1/(1+t)`
  gives only `≤ 0.295` (edge `≤ 585`), so the sharp `≤ 0.1` is built from
  `exp_one_gt_d9` instead (see next).
* `Real.exp_one_gt_d9` (`Mathlib/Analysis/Complex/ExponentialBounds.lean:35`):
  `2.7182818283 < Real.exp 1` -- USED (lower-bounds `exp 2.3925 ≥ 10`, hence the sharp
  positive-side `exp(-2.3925) ≤ 0.1`; created in-file as `exp_neg23925_le` since no
  such numeral exists repo-wide).
* `sq_le_sq'` (`Mathlib/Algebra/Order/Ring/Abs.lean:122`, used at `:1264`):
  two-sided square monotonicity -- USED (feeds `damp_mono_pos`).
* `CA2TailJoint.joint_poly_tail_numeric`, `BH2TailWindow.damp_left_tail_le_one`,
  `BZTailEnvelope.P1_R02_of_hTail` -- CITED (CC's inputs / downstream consumer; the
  `≤ 1` damping is SUPERSEDED here by the exact norm, never used).

WHAT IS PROVED (all full proofs, no `sorry`/`admit`/`axiom`):
* `damp_norm_eq_neg1`: exact damping norm `= exp((1-(τ+6.75)^2)/100)` on `Re = -1`.
* `G_le_sharp` (MAIN pointwise, both signs):
  `‖G z‖ ≤ exp((1-(τ+6.75)^2)/100) * B(|τ|)`.
* `damp_pos_le` + `exp_neg23925_le` (`exp(-2.3925) ≤ 0.1` via
  `exp 2.3925 = exp(1)^2*exp(0.3925) ≥ 2.7182818283^2*1.3925 ≥ 10`) + `G_le_sharp_pos`
  (MAIN positive-side): `‖G z‖ ≤ 0.1 * B(|Im|)` for `8.75 < τ`.
* `damp_mono_pos`: the Gaussian factor is decreasing for `τ ≥ 8.75`.
* `sharp_pos_edge`: `0.1*B(8.75) = 198.46005` (`norm_num`); `sharp_pos_gap`:
  `198.46005-36 = 162.46005`; `edge_gt_180` / `edge_lt_216` (`5x`-`6x` bracket).
* `damp_neg_le` + `exp_neg003_le` (`exp(-0.03) ≤ 0.971` via `exp_neg_le_inv`) +
  `G_le_sharp_neg`: `‖G z‖ ≤ 0.971 * B(|Im|)` for `τ < -8.75`.
* `sharp_neg_edge`: `0.971*B(8.75) = 1927.0470855` (`norm_num`); `sharp_neg_gap`:
  `1927.0470855-36 = 1891.0470855`; `edge_gt_1908` / `edge_lt_1944`
  (`53x`-`54x` bracket).
* `sharpest_sharp_cap_gap_pos` (packaging, mirrors CC's `sharpest_cap_gap`).
-/

namespace CF_SharpDamp

/-- Exact damping norm on `Re = -1`: `‖damp z‖ = exp((1-(τ+6.75)^2)/100)`. -/
theorem damp_norm_eq_neg1 {z : ℂ} (hz : z.re = -1) :
    ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
      (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖
      = Real.exp ((1 - (z.im + 6.75) ^ 2) / 100) := by
  have e : ((-1 : ℝ)) ^ 2 = 1 := by norm_num
  rw [ZetaUpperR02ThreeLines.norm_complex_exp, BH2TailWindow.damp_re_general, hz, e]

/-- MAIN pointwise sharp composition (both signs):
`‖G z‖ ≤ exp((1-(τ+6.75)^2)/100) * B(|τ|)` with CC's cubic `B`. -/
theorem G_le_sharp {z : ℂ} (hz : z.re = -1) (htail : 8.75 < |z.im|) :
    ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤
      Real.exp ((1 - (z.im + 6.75) ^ 2) / 100) *
        ((2 + |z.im|) * (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)))) := by
  have hF := CC_hTailGap.F_le hz htail
  have hdamp := damp_norm_eq_neg1 hz
  have hfin : ZetaUpperR02ThreeLines.dampedPoleRemoved z =
      ZetaUpperR02ThreeLines.poleRemovedZeta z *
        Complex.exp (((1 / 100 : ℝ) : ℂ) *
          (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2) := rfl
  rw [hfin, norm_mul, hdamp]
  calc ‖ZetaUpperR02ThreeLines.poleRemovedZeta z‖ *
      Real.exp ((1 - (z.im + 6.75) ^ 2) / 100)
      ≤ ((2 + |z.im|) * (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)))) *
        Real.exp ((1 - (z.im + 6.75) ^ 2) / 100) :=
        mul_le_mul_of_nonneg_right hF (Real.exp_pos _).le
    _ = Real.exp ((1 - (z.im + 6.75) ^ 2) / 100) *
        ((2 + |z.im|) * (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)))) := by
        ring

/-- Positive-side damping cap: `‖damp‖ ≤ exp(-2.3925)` for `8.75 < τ` on `Re = -1`
(`(τ+6.75)^2 ≥ 15.5^2 = 240.25`, so `Re ≤ (1-240.25)/100 = -2.3925`). -/
theorem damp_pos_le {z : ℂ} (hz : z.re = -1) (hpos : 8.75 < z.im) :
    ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
      (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ ≤ Real.exp (-2.3925) := by
  rw [damp_norm_eq_neg1 hz]
  apply Real.exp_le_exp.mpr
  have h15 : (15.5 : ℝ) ≤ z.im + 6.75 := by linarith
  have hsq : (240.25 : ℝ) ≤ (z.im + 6.75) ^ 2 := by
    have hnn1 : (0 : ℝ) ≤ z.im + 6.75 - 15.5 := by linarith
    have hnn2 : (0 : ℝ) ≤ z.im + 6.75 + 15.5 := by linarith
    have hprod : (0 : ℝ) ≤ (z.im + 6.75 - 15.5) * (z.im + 6.75 + 15.5) :=
      mul_nonneg hnn1 hnn2
    have e : (z.im + 6.75 - 15.5) * (z.im + 6.75 + 15.5)
        = (z.im + 6.75) ^ 2 - 240.25 := by ring
    linarith
  linarith

/-- Sharp positive-edge exponential: `exp(-2.3925) ≤ 0.1`
(`exp 2.3925 = exp(1)^2*exp(0.3925) ≥ 2.7182818283^2*1.3925 ≥ 10`). -/
theorem exp_neg23925_le : Real.exp (-2.3925 : ℝ) ≤ 0.1 := by
  have e1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have e2 : (1.3925 : ℝ) ≤ Real.exp 0.3925 := by
    have h := Real.add_one_le_exp (0.3925 : ℝ)
    linarith
  have h2 : (1 : ℝ) + 1 + 0.3925 = 2.3925 := by norm_num
  have h3 : Real.exp ((1 : ℝ) + 1 + 0.3925)
      = Real.exp 1 * Real.exp 1 * Real.exp 0.3925 := by
    rw [Real.exp_add, Real.exp_add]
  have esplit : Real.exp (2.3925 : ℝ)
      = Real.exp 1 * Real.exp 1 * Real.exp 0.3925 := by
    rw [h2] at h3
    exact h3
  have hnum : (10 : ℝ) ≤ 2.7182818283 * 2.7182818283 * 1.3925 := by norm_num
  have hinner : 2.7182818283 * 2.7182818283 ≤ Real.exp 1 * Real.exp 1 :=
    mul_le_mul e1.le e1.le (by norm_num) (Real.exp_pos _).le
  have g1 : 2.7182818283 * 2.7182818283 * 1.3925
      ≤ Real.exp 1 * Real.exp 1 * Real.exp 0.3925 :=
    mul_le_mul hinner e2 (by norm_num)
      (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  have h10 : (10 : ℝ) ≤ Real.exp 2.3925 := by
    rw [esplit]
    exact le_trans hnum g1
  have e : Real.exp (-2.3925 : ℝ) * Real.exp 2.3925 = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hmul : Real.exp (-2.3925 : ℝ) * 10 ≤ 1 :=
    calc Real.exp (-2.3925) * 10 ≤ Real.exp (-2.3925) * Real.exp 2.3925 :=
          mul_le_mul_of_nonneg_left h10 (Real.exp_pos _).le
      _ = 1 := e
  have hle : Real.exp (-2.3925 : ℝ) ≤ 1 / 10 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10)]
    exact hmul
  calc Real.exp (-2.3925 : ℝ) ≤ 1 / 10 := hle
    _ = 0.1 := by norm_num

/-- MAIN positive-side sharp cap: `‖G z‖ ≤ 0.1 * B(|Im|)` for `8.75 < τ`. -/
theorem G_le_sharp_pos {z : ℂ} (hz : z.re = -1) (hpos : 8.75 < z.im) :
    ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤
      (0.1 : ℝ) * ((2 + |z.im|) *
        (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)))) := by
  have habs : |z.im| = z.im := abs_of_nonneg (by linarith)
  have htail : 8.75 < |z.im| := by rw [habs]; exact hpos
  have hG := G_le_sharp hz htail
  have hde : Real.exp ((1 - (z.im + 6.75) ^ 2) / 100) ≤ Real.exp (-2.3925) := by
    have h := damp_pos_le hz hpos
    rw [damp_norm_eq_neg1 hz] at h
    exact h
  have hexp : Real.exp ((1 - (z.im + 6.75) ^ 2) / 100) ≤ 0.1 :=
    le_trans hde exp_neg23925_le
  have hBnn : (0 : ℝ) ≤
      (2 + |z.im|) * (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1))) := by
    have ha : (0 : ℝ) ≤ |z.im| := abs_nonneg _
    have h1 : (0 : ℝ) ≤ |z.im| ^ 2 := sq_nonneg _
    have hmul : (0 : ℝ) ≤ 3.1416 * |z.im| := mul_nonneg (by norm_num) ha
    have h2 : (0 : ℝ) ≤ 3.1416 * |z.im| / 2 := by linarith
    have hX : (0 : ℝ) ≤ (1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1) := by linarith
    have h2X : (0 : ℝ) ≤ 2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)) := by
      linarith
    have hb : (0 : ℝ) ≤ 2 + |z.im| := by linarith
    exact mul_nonneg hb h2X
  calc ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖
      ≤ Real.exp ((1 - (z.im + 6.75) ^ 2) / 100) *
        ((2 + |z.im|) * (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)))) := hG
    _ ≤ (0.1 : ℝ) * ((2 + |z.im|) *
        (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)))) :=
        mul_le_mul_of_nonneg_right hexp hBnn

/-- Gaussian factor decreasing on the positive tail (`τ ≥ 8.75`). -/
theorem damp_mono_pos {a b : ℝ} (ha : 8.75 ≤ a) (hab : a ≤ b) :
    Real.exp ((1 - (b + 6.75) ^ 2) / 100)
      ≤ Real.exp ((1 - (a + 6.75) ^ 2) / 100) := by
  apply Real.exp_le_exp.mpr
  have h1 : -(b + 6.75) ≤ a + 6.75 := by linarith
  have h2 : a + 6.75 ≤ b + 6.75 := by linarith
  have hsq : (a + 6.75) ^ 2 ≤ (b + 6.75) ^ 2 := sq_le_sq' h1 h2
  linarith

/-- Sharp positive edge numeral: `0.1 * B(8.75) = 198.46005` (`norm_num`). -/
theorem sharp_pos_edge :
    (0.1 : ℝ) * ((2 + (8.75 : ℝ)) *
      (2 * ((1 + (8.75 : ℝ) ^ 2) + (3.1416 * (8.75 : ℝ) / 2 + 1)))) = 198.46005 := by
  norm_num

/-- Sharp positive gap numeral: `198.46005 - 36 = 162.46005` (`norm_num`). -/
theorem sharp_pos_gap : (198.46005 : ℝ) - 36 = 162.46005 := by norm_num

/-- `5x` bracket below: `180 < 198.46005` (edge is MORE than `5x` over 36). -/
theorem edge_gt_180 : (180 : ℝ) < 198.46005 := by norm_num

/-- `6x` bracket above: `198.46005 < 216` (edge is LESS than `6x` over 36). -/
theorem edge_lt_216 : (198.46005 : ℝ) < 216 := by norm_num

/-- Negative-side damping cap: `‖damp‖ ≤ exp(-0.03)` for `τ < -8.75` on `Re = -1`
(`(τ+6.75)^2 ≥ (-2)^2 = 4`, so `Re ≤ (1-4)/100 = -0.03`). -/
theorem damp_neg_le {z : ℂ} (hz : z.re = -1) (hneg : z.im < -8.75) :
    ‖Complex.exp (((1 / 100 : ℝ) : ℂ) *
      (z - ZetaUpperR02ThreeLines.dampCenter) ^ 2)‖ ≤ Real.exp (-0.03) := by
  rw [damp_norm_eq_neg1 hz]
  apply Real.exp_le_exp.mpr
  have h2le : z.im + 6.75 ≤ (-2 : ℝ) := by linarith
  have hsq : (4 : ℝ) ≤ (z.im + 6.75) ^ 2 := by
    have hnn1 : (0 : ℝ) ≤ -(z.im + 6.75 + 2) := by linarith
    have hnn2 : (0 : ℝ) ≤ -(z.im + 6.75 - 2) := by linarith
    have hprod : (0 : ℝ) ≤ (-(z.im + 6.75 + 2)) * (-(z.im + 6.75 - 2)) :=
      mul_nonneg hnn1 hnn2
    have e : (-(z.im + 6.75 + 2)) * (-(z.im + 6.75 - 2))
        = (z.im + 6.75) ^ 2 - 4 := by ring
    linarith
  linarith

/-- Negative-edge exponential: `exp(-0.03) ≤ 0.971` (via `exp_neg_le_inv`). -/
theorem exp_neg003_le : Real.exp (-0.03 : ℝ) ≤ 0.971 := by
  have h := BF2TailCaps.exp_neg_le_inv (show (0 : ℝ) ≤ 0.03 by norm_num)
  calc Real.exp (-0.03 : ℝ) ≤ 1 / (1 + 0.03) := h
    _ ≤ 0.971 := by norm_num

/-- MAIN negative-side sharp cap: `‖G z‖ ≤ 0.971 * B(|Im|)` for `τ < -8.75`. -/
theorem G_le_sharp_neg {z : ℂ} (hz : z.re = -1) (hneg : z.im < -8.75) :
    ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤
      (0.971 : ℝ) * ((2 + |z.im|) *
        (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)))) := by
  have habs : |z.im| = -z.im := abs_of_neg (by linarith)
  have htail : 8.75 < |z.im| := by rw [habs]; linarith
  have hG := G_le_sharp hz htail
  have hde : Real.exp ((1 - (z.im + 6.75) ^ 2) / 100) ≤ Real.exp (-0.03) := by
    have h := damp_neg_le hz hneg
    rw [damp_norm_eq_neg1 hz] at h
    exact h
  have hexp : Real.exp ((1 - (z.im + 6.75) ^ 2) / 100) ≤ 0.971 :=
    le_trans hde exp_neg003_le
  have hBnn : (0 : ℝ) ≤
      (2 + |z.im|) * (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1))) := by
    have ha : (0 : ℝ) ≤ |z.im| := abs_nonneg _
    have h1 : (0 : ℝ) ≤ |z.im| ^ 2 := sq_nonneg _
    have hmul : (0 : ℝ) ≤ 3.1416 * |z.im| := mul_nonneg (by norm_num) ha
    have h2 : (0 : ℝ) ≤ 3.1416 * |z.im| / 2 := by linarith
    have hX : (0 : ℝ) ≤ (1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1) := by linarith
    have h2X : (0 : ℝ) ≤ 2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)) := by
      linarith
    have hb : (0 : ℝ) ≤ 2 + |z.im| := by linarith
    exact mul_nonneg hb h2X
  calc ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖
      ≤ Real.exp ((1 - (z.im + 6.75) ^ 2) / 100) *
        ((2 + |z.im|) * (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)))) := hG
    _ ≤ (0.971 : ℝ) * ((2 + |z.im|) *
        (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)))) :=
        mul_le_mul_of_nonneg_right hexp hBnn

/-- Sharp negative edge numeral: `0.971 * B(8.75) = 1927.0470855` (`norm_num`). -/
theorem sharp_neg_edge :
    (0.971 : ℝ) * ((2 + (8.75 : ℝ)) *
      (2 * ((1 + (8.75 : ℝ) ^ 2) + (3.1416 * (8.75 : ℝ) / 2 + 1)))) = 1927.0470855 := by
  norm_num

/-- Sharp negative gap numeral: `1927.0470855 - 36 = 1891.0470855` (`norm_num`). -/
theorem sharp_neg_gap : (1927.0470855 : ℝ) - 36 = 1891.0470855 := by norm_num

/-- `53x` bracket below: `1908 < 1927.0470855` (edge is MORE than `53x` over 36). -/
theorem edge_gt_1908 : (1908 : ℝ) < 1927.0470855 := by norm_num

/-- `54x` bracket above: `1927.0470855 < 1944` (edge is LESS than `54x` over 36). -/
theorem edge_lt_1944 : (1927.0470855 : ℝ) < 1944 := by norm_num

/-- SHARPEST positive-side cap+gap package: pointwise `0.1*B(|Im|)`, edge `198.46005`,
still above 36 (mirrors CC's `sharpest_cap_gap`). -/
theorem sharpest_sharp_cap_gap_pos {z : ℂ} (hz : z.re = -1) (hpos : 8.75 < z.im) :
    ‖ZetaUpperR02ThreeLines.dampedPoleRemoved z‖ ≤
        (0.1 : ℝ) * ((2 + |z.im|) *
          (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1))))
      ∧ (0.1 : ℝ) * ((2 + (8.75 : ℝ)) *
          (2 * ((1 + (8.75 : ℝ) ^ 2) + (3.1416 * (8.75 : ℝ) / 2 + 1)))) = 198.46005
      ∧ (36 : ℝ) < (0.1 : ℝ) * ((2 + |z.im|) *
          (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)))) := by
  have habs : |z.im| = z.im := abs_of_nonneg (by linarith)
  have hmono := CC_hTailGap.bound_mono (show 8.75 ≤ |z.im| by rw [habs]; exact le_of_lt hpos)
  have he := sharp_pos_edge
  have hle : (0.1 : ℝ) * ((2 + (8.75 : ℝ)) *
      (2 * ((1 + (8.75 : ℝ) ^ 2) + (3.1416 * (8.75 : ℝ) / 2 + 1))))
      ≤ (0.1 : ℝ) * ((2 + |z.im|) *
        (2 * ((1 + |z.im| ^ 2) + (3.1416 * |z.im| / 2 + 1)))) :=
    mul_le_mul_of_nonneg_left hmono (by norm_num)
  refine ⟨G_le_sharp_pos hz hpos, he, ?_⟩
  have h36 : (36 : ℝ) < 198.46005 := by norm_num
  linarith

#print axioms CF_SharpDamp.damp_norm_eq_neg1
#print axioms CF_SharpDamp.G_le_sharp
#print axioms CF_SharpDamp.damp_pos_le
#print axioms CF_SharpDamp.exp_neg23925_le
#print axioms CF_SharpDamp.G_le_sharp_pos
#print axioms CF_SharpDamp.damp_mono_pos
#print axioms CF_SharpDamp.sharp_pos_edge
#print axioms CF_SharpDamp.sharp_pos_gap
#print axioms CF_SharpDamp.edge_gt_180
#print axioms CF_SharpDamp.edge_lt_216
#print axioms CF_SharpDamp.damp_neg_le
#print axioms CF_SharpDamp.exp_neg003_le
#print axioms CF_SharpDamp.G_le_sharp_neg
#print axioms CF_SharpDamp.sharp_neg_edge
#print axioms CF_SharpDamp.sharp_neg_gap
#print axioms CF_SharpDamp.edge_gt_1908
#print axioms CF_SharpDamp.edge_lt_1944
#print axioms CF_SharpDamp.sharpest_sharp_cap_gap_pos

end CF_SharpDamp

/-!
CF VERDICT + RESIDUAL (report-and-stop): door-3 hTail SHARP-DAMPING SHARPENER GREEN,
hTail itself still OPEN. No closure claimed.
(1) Positive side CLOSED at the sharpener level: the honest Gaussian
`‖damp‖ = exp((1-(τ+6.75)^2)/100)` (`damp_norm_eq_neg1`, FULL proof) times CC's cubic
gives `‖G z‖ ≤ 0.1*B(|Im|)` (`G_le_sharp_pos`, FULL proof; `exp(-2.3925) ≤ 0.1` via
`exp 2.3925 ≥ 10`, itself FULL proof from `Real.exp_one_gt_d9`). At the window edge
`0.1*B(8.75) = 198.46005` (`sharp_pos_edge`, `norm_num`; true value `≈ 181.4` by
external arithmetic, so the damping-bound slack is only `~9%` -- the remainder sits in
the cubic `F` majorant, not in the damping estimate). Gap `198.46005-36 = 162.46005`
(`sharp_pos_gap`); edge is between `5x` and `6x` over 36 (`edge_gt_180`,
`edge_lt_216`). Gain over CC: `1984.6005 → 198.46005` (`~10x` from the damping alone).
The Gaussian factor is proved decreasing for `τ ≥ 8.75` (`damp_mono_pos`).
(2) Negative side HONEST NEGATIVE at the sharpener level: `‖G z‖ ≤ 0.971*B(|Im|)`
(`G_le_sharp_neg`, FULL proof); edge `0.971*B(8.75) = 1927.0470855`
(`sharp_neg_edge`), gap `1891.0470855`, between `53x` and `54x` over 36. The Gaussian
center `τ = -6.75` sits near this tail, so honest damping gives almost nothing there.
(3) P1 NOT fired: `BZTailEnvelope.P1_R02_of_hTail` stays conditional on the unclosed
`hTail` (`≤ 36`); `DerivCauchyBridge.R02_zeta_upper_obligation` stays open.
EXACT REMAINING GAP + WHAT CLOSES IT (estimates, not theorems -- STOP per brief):
* Positive side needs `5.5x` (`198.46 → 36`). A Stirling-sharp `F`-bound alone
  (true `~|τ|^2.5`; at edge `8.75^2.5 ≈ 226.5`): with honest constant `~3` that gives
  `≈ 3*226.5*0.09 ≈ 61` at edge (gap `≈ 25`, `1.7x` over) -- STILL SHORT. Closing
  needs the joint `Γ·cos` Gaussian analysis on the `Re = 2` mirror (CC's named
  true gap-closer; must cut the joint constant from `~92` to `~30` at the edge), or a
  Stirling constant `C ≤ 1.76` (`1.76*226.5*0.09 ≈ 35.9`).
* Negative side needs `53.5x` (`1927.05 → 36`): the `2.5`-power gives only `~3x`, so
  the joint `Γ·cos` analysis must supply the remaining `~18x` there -- it is the
  load-bearing piece on this side (a recentered damping is out of scope: it would move
  every windowed cap).
* The exact-factor `B_sharp(τ) = exp((1-(τ+6.75)^2)/100)*B(|τ|)` DOES decay
  super-exponentially on the positive side (external estimate: crosses 36 near
  `τ ≈ 17-18`) -- NOT proved here (needs tight large-`|t|` exp bounds beyond
  `1/(1+t)`, absent repo-wide) and NOT claimed.
hTail verdict: SHARPENER GREEN (`198.46005` pos / `1927.0470855` neg vs CC `1984.6005`).
P1 verdict: CONDITIONAL (needs `hTail` at 36, not met).
No `sorry`/`admit`/`axiom` in this tail.
-/

/-!
# CH2 Gamma-tail upper (door-3 hTail/P1 feeder, append-only)

GREPS FIRST (verified 2026-09-04, via `rg` in-file; nothing reimplemented):
* AR joint identity: `Door3JointGammaCos.Gamma_one_add_im_normSq`
  (`‖Γ(1+iy)‖² = πy/sinh(πy)`, `:2690`) + `Door3JointGammaCos.t_mul_coth_le`
  (`t·coth t ≤ t+1`, `:2756`) + `Door3JointGammaCos.Gamma_Re2_normSq`
  (`‖Γ(w)‖² = (1+y²)·πy/sinh(πy)` on `Re = 2`, `:2831`).
* CF sharp damping: `CF_SharpDamp.sharp_pos_edge` (`0.1*B(8.75) = 198.46005`)
  + `CF_SharpDamp.sharp_neg_edge` (`0.971*B(8.75) = 1927.0470855`); joint
  analysis load-bearing (top needs 5.5x, negative needs ~18x).
* BZ tail reflection: `BZTailEnvelope.GammaR_tail_lower` (tail Gamma-lower via
  `Complex.Gamma_mul_Gamma_one_sub`, reflection numerals).
* Absent hence created here: `CH2GammaTail`, `Gamma_Re2_tail`, `sinh_ge_exp`
  return zero hits (checked via `rg` before writing).

WHAT IS PROVED (unconditional, no `sorry`/`admit`/`axiom`/stand-ins):
* `sinh_ge_exp_div_four`: `exp t / 4 ≤ sinh t` for `1/2 ≤ t` (from-scratch via
  `Real.add_one_le_exp` at `2t`: `2 ≤ exp(2t)`, hence `exp(-t) ≤ exp(t)/2`).
* `Gamma_Re2_tail_sq` (MAIN, squared form): on `Re w = 2`, `8.75 ≤ |Im w|`,
  `‖Γ w‖² ≤ 16·|Im w|³·exp(-π·|Im w|)` — i.e. `C² = 16`.
  Via AR's exact `Gamma_Re2_normSq` + symmetrization `y → |y|` (mirror of AR's
  `hsymm`), the tail sinh lower bound above (decay extraction in place of AR's
  window `t·coth` cap), the tail poly numeral `1+|y|² ≤ (1241/1225)·|y|²`
  (from `|y|² ≥ 8.75² = 76.5625`; `1241/1225 = 77.5625/76.5625`), and the coeff
  numeral `(1241/1225)·(4π) ≤ 16` (via `π ≤ 3.1416`).
* `Gamma_Re2_tail_upper` (unsquared, EXPLICIT `C = 4`):
  `‖Γ w‖ ≤ 4·√(|Im w|³)·exp(-π·|Im w|/2)` on the same tail, by taking square
  roots (`Real.sqrt_le_sqrt` + `Real.sq_sqrt` + `exp(x/2)² = exp(x)`).
  Since `√(|y|³) = |y|^{3/2}`, this is exactly
  `‖Γ(2+iy)‖ ≤ C·|y|^{3/2}·e^{-π|y|/2}` with `C = 4`.

EXPLICIT C ACHIEVED: `C = 4` (squared `C² = 16`). True constant near edge:
`‖Γ‖²/(|y|³·e^{-π|y|}) ≈ 4π·1.013 ≈ 12.73`, so `C = 4` has ~25% headroom;
`C = 3.6` (`3.6² = 12.96`) would also hold but `4` keeps numerals `norm_num`-clean.
-/

namespace CH2GammaTail

/-- From-scratch tail decay extractor: `exp t / 4 ≤ sinh t` for `1/2 ≤ t`.
Proof: `exp(2t) ≥ 1+2t ≥ 2` (`Real.add_one_le_exp`), so
`2·exp(-t) ≤ exp(2t)·exp(-t) = exp(t)`, i.e. `exp(-t) ≤ exp(t)/2`;
then `sinh t = (exp t - exp(-t))/2 ≥ (exp t)/4`. -/
theorem sinh_ge_exp_div_four {t : ℝ} (ht : 1 / 2 ≤ t) :
    Real.exp t / 4 ≤ Real.sinh t := by
  have hEpos : 0 < Real.exp t := Real.exp_pos t
  have hEmpos : 0 < Real.exp (-t) := Real.exp_pos _
  have h2t : (2 : ℝ) ≤ Real.exp (2 * t) := by
    have h := Real.add_one_le_exp (2 * t)
    linarith
  have h2t_eq : (2 : ℝ) * t = t + t := by ring
  have hExp2 : Real.exp (2 * t) = Real.exp t * Real.exp t := by
    rw [h2t_eq, Real.exp_add]
  have hEt2 : (2 : ℝ) ≤ Real.exp t * Real.exp t := by
    rw [← hExp2]
    exact h2t
  have hEm : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hEm_le : Real.exp (-t) ≤ Real.exp t / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hEt2 (le_of_lt hEmpos)
    have e : (Real.exp t * Real.exp t) * Real.exp (-t) = Real.exp t := by
      rw [mul_assoc, mul_comm (Real.exp t) (Real.exp (-t)), hEm, mul_one]
    linarith
  have hsinh_eq : Real.sinh t = (Real.exp t - Real.exp (-t)) / 2 :=
    Real.sinh_eq t
  linarith

/-- Squared Stirling-sharp Gamma tail upper on `Re = 2`: `‖Γ w‖² ≤ 16·|y|³·e^{-π|y|}`
for `8.75 ≤ |y|`. Mirrors AR's `Gamma_Re2_normSq` proof shape (symmetrization +
`sinh`-denominator handling), extended off-window with tail numerals instead of
window caps (`t_mul_coth_le` is replaced by `sinh_ge_exp_div_four`). -/
theorem Gamma_Re2_tail_sq {w : ℂ} (hw : w.re = 2)
    (htail : (8.75 : ℝ) ≤ |w.im|) :
    ‖Complex.Gamma w‖ ^ 2
      ≤ 16 * |w.im| ^ 3 * Real.exp (-(Real.pi * |w.im|)) := by
  have hyne : w.im ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at htail
    norm_num at htail
  have hG := Door3JointGammaCos.Gamma_Re2_normSq hw hyne
  have hsq : w.im ^ 2 = |w.im| ^ 2 := (sq_abs _).symm
  have hsymm : Real.pi * w.im / Real.sinh (Real.pi * w.im)
      = Real.pi * |w.im| / Real.sinh (Real.pi * |w.im|) := by
    rcases le_total w.im 0 with hynonpos | hynonneg
    · have hyneg : w.im < 0 := lt_of_le_of_ne hynonpos hyne
      rw [abs_of_neg hyneg, show Real.pi * -w.im = -(Real.pi * w.im) by ring,
        Real.sinh_neg, neg_div_neg_eq]
    · rw [abs_of_nonneg hynonneg]
  have hG2 : ‖Complex.Gamma w‖ ^ 2
      = (1 + |w.im| ^ 2) * (Real.pi * |w.im| / Real.sinh (Real.pi * |w.im|)) := by
    rw [hsq, hsymm] at hG
    exact hG
  have ha_pos : 0 < |w.im| := lt_of_lt_of_le (by norm_num) htail
  have hpi : 0 < Real.pi := by linarith [Real.pi_gt_three]
  have ha_nonneg : 0 ≤ |w.im| := le_of_lt ha_pos
  have hpi_nonneg : 0 ≤ Real.pi := le_of_lt hpi
  have hpa_nonneg : 0 ≤ Real.pi * |w.im| := mul_nonneg hpi_nonneg ha_nonneg
  have ht_half : (1 : ℝ) / 2 ≤ Real.pi * |w.im| := by
    have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hmul := mul_le_mul_of_nonneg_right (le_of_lt h3) ha_nonneg
    have h3y : (3 : ℝ) * 8.75 ≤ 3 * |w.im| :=
      mul_le_mul_of_nonneg_left htail (by norm_num)
    have h326 : (3 : ℝ) * 8.75 = 26.25 := by norm_num
    linarith
  have hsinh_pos : 0 < Real.sinh (Real.pi * |w.im|) :=
    Real.sinh_pos_iff.mpr (by linarith)
  have hexp_pos : 0 < Real.exp (Real.pi * |w.im|) := Real.exp_pos _
  have hsinh_lower : Real.exp (Real.pi * |w.im|) / 4
      ≤ Real.sinh (Real.pi * |w.im|) :=
    sinh_ge_exp_div_four ht_half
  have hExp4 : Real.exp (Real.pi * |w.im|)
      ≤ 4 * Real.sinh (Real.pi * |w.im|) := by
    linarith
  have hS_nonneg : 0 ≤ Real.pi * |w.im| / Real.sinh (Real.pi * |w.im|) :=
    div_nonneg hpa_nonneg (le_of_lt hsinh_pos)
  have hS_le : Real.pi * |w.im| / Real.sinh (Real.pi * |w.im|)
      ≤ 4 * Real.pi * |w.im| * Real.exp (-(Real.pi * |w.im|)) := by
    rw [Real.exp_neg]
    have hcross : Real.pi * |w.im| * Real.exp (Real.pi * |w.im|)
        ≤ 4 * Real.pi * |w.im| * Real.sinh (Real.pi * |w.im|) := by
      have hnn := mul_nonneg hpa_nonneg (sub_nonneg.mpr hExp4)
      nlinarith [hnn]
    have hgoal : Real.pi * |w.im|
        ≤ (4 * Real.pi * |w.im| * Real.sinh (Real.pi * |w.im|))
          / Real.exp (Real.pi * |w.im|) :=
      (le_div_iff₀ hexp_pos).mpr hcross
    rw [div_eq_mul_inv] at hgoal
    have e : (4 * Real.pi * |w.im| * Real.sinh (Real.pi * |w.im|))
          * (Real.exp (Real.pi * |w.im|))⁻¹
        = 4 * Real.pi * |w.im| * (Real.exp (Real.pi * |w.im|))⁻¹
          * Real.sinh (Real.pi * |w.im|) := by ring
    rw [e] at hgoal
    exact (div_le_iff₀ hsinh_pos).mpr hgoal
  have hsq_ge : (8.75 : ℝ) ^ 2 ≤ |w.im| ^ 2 :=
    pow_le_pow_left₀ (by norm_num) htail 2
  have h875sq : (8.75 : ℝ) ^ 2 = 76.5625 := by norm_num
  have h76 : (76.5625 : ℝ) ≤ |w.im| ^ 2 := by linarith
  have hpoly : 1 + |w.im| ^ 2 ≤ (1241 / 1225 : ℝ) * |w.im| ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left h76 (show (0 : ℝ) ≤ 16 / 1225 by norm_num)
    have h16 : (16 / 1225 : ℝ) * 76.5625 = 1 := by norm_num
    have h1le : (1 : ℝ) ≤ (16 / 1225) * |w.im| ^ 2 := by linarith
    have hsplit : (1241 / 1225 : ℝ) * |w.im| ^ 2
        = |w.im| ^ 2 + (16 / 1225) * |w.im| ^ 2 := by ring
    linarith
  have hcoeff : (1241 / 1225 : ℝ) * (4 * Real.pi) ≤ 16 := by
    have hpi_le : Real.pi ≤ 3.1416 := le_of_lt Real.pi_lt_d4
    have hmul := mul_le_mul_of_nonneg_left hpi_le
      (show (0 : ℝ) ≤ (1241 / 1225) * 4 by norm_num)
    have hnum : ((1241 / 1225 : ℝ) * 4) * 3.1416 ≤ 16 := by norm_num
    have hbridge : (1241 / 1225 : ℝ) * (4 * Real.pi)
        = ((1241 / 1225) * 4) * Real.pi := by ring
    rw [hbridge]
    linarith
  have hpolyRHS_nonneg : 0 ≤ (1241 / 1225 : ℝ) * |w.im| ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  have hRHS_exp_nonneg : 0 ≤ Real.exp (-(Real.pi * |w.im|)) :=
    le_of_lt (Real.exp_pos _)
  have ha3_nonneg : 0 ≤ |w.im| ^ 3 := pow_nonneg ha_nonneg 3
  have hbound1 : (1 + |w.im| ^ 2)
        * (Real.pi * |w.im| / Real.sinh (Real.pi * |w.im|))
      ≤ ((1241 / 1225) * |w.im| ^ 2)
        * (4 * Real.pi * |w.im| * Real.exp (-(Real.pi * |w.im|))) :=
    mul_le_mul hpoly hS_le hS_nonneg hpolyRHS_nonneg
  have hEq : ((1241 / 1225) * |w.im| ^ 2)
        * (4 * Real.pi * |w.im| * Real.exp (-(Real.pi * |w.im|)))
      = ((1241 / 1225) * (4 * Real.pi)) * |w.im| ^ 3
        * Real.exp (-(Real.pi * |w.im|)) := by
    ring
  have hbound2 : ((1241 / 1225) * (4 * Real.pi)) * |w.im| ^ 3
        * Real.exp (-(Real.pi * |w.im|))
      ≤ 16 * |w.im| ^ 3 * Real.exp (-(Real.pi * |w.im|)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff ha3_nonneg) hRHS_exp_nonneg
  calc ‖Complex.Gamma w‖ ^ 2
      = (1 + |w.im| ^ 2) * (Real.pi * |w.im| / Real.sinh (Real.pi * |w.im|)) := hG2
    _ ≤ ((1241 / 1225) * |w.im| ^ 2)
        * (4 * Real.pi * |w.im| * Real.exp (-(Real.pi * |w.im|))) := hbound1
    _ = ((1241 / 1225) * (4 * Real.pi)) * |w.im| ^ 3
        * Real.exp (-(Real.pi * |w.im|)) := hEq
    _ ≤ 16 * |w.im| ^ 3 * Real.exp (-(Real.pi * |w.im|)) := hbound2

/-- Un-squared Stirling-sharp Gamma tail upper with EXPLICIT `C = 4`:
`‖Γ w‖ ≤ 4·√(|y|³)·e^{-π|y|/2}` for `Re w = 2`, `8.75 ≤ |y|`.
Since `√(|y|³) = |y|^{3/2}`, this is exactly the brief's
`‖Γ(2+iy)‖ ≤ C·|y|^{3/2}·e^{-π|y|/2}` with `C = 4`. -/
theorem Gamma_Re2_tail_upper {w : ℂ} (hw : w.re = 2)
    (htail : (8.75 : ℝ) ≤ |w.im|) :
    ‖Complex.Gamma w‖
      ≤ 4 * Real.sqrt (|w.im| ^ 3) * Real.exp (-(Real.pi * |w.im| / 2)) := by
  have hsq := Gamma_Re2_tail_sq hw htail
  have ha_nonneg : 0 ≤ |w.im| := abs_nonneg _
  have ha3_nonneg : 0 ≤ |w.im| ^ 3 := pow_nonneg ha_nonneg 3
  have hsqrt_nonneg : 0 ≤ Real.sqrt (|w.im| ^ 3) := Real.sqrt_nonneg _
  have hexp_nonneg : 0 ≤ Real.exp (-(Real.pi * |w.im| / 2)) :=
    le_of_lt (Real.exp_pos _)
  have hRHS_nonneg : 0 ≤ 4 * Real.sqrt (|w.im| ^ 3)
      * Real.exp (-(Real.pi * |w.im| / 2)) :=
    mul_nonneg (mul_nonneg (by norm_num) hsqrt_nonneg) hexp_nonneg
  have hsqrt_sq : (Real.sqrt (|w.im| ^ 3)) ^ 2 = |w.im| ^ 3 :=
    Real.sq_sqrt ha3_nonneg
  have hexp_sq : (Real.exp (-(Real.pi * |w.im| / 2))) ^ 2
      = Real.exp (-(Real.pi * |w.im|)) := by
    have e : (-(Real.pi * |w.im| / 2)) + (-(Real.pi * |w.im| / 2))
        = -(Real.pi * |w.im|) := by ring
    calc (Real.exp (-(Real.pi * |w.im| / 2))) ^ 2
        = Real.exp (-(Real.pi * |w.im| / 2))
          * Real.exp (-(Real.pi * |w.im| / 2)) := by ring
      _ = Real.exp ((-(Real.pi * |w.im| / 2)) + (-(Real.pi * |w.im| / 2))) := by
          rw [← Real.exp_add]
      _ = Real.exp (-(Real.pi * |w.im|)) := by rw [e]
  have hRHS_sq : (4 * Real.sqrt (|w.im| ^ 3)
        * Real.exp (-(Real.pi * |w.im| / 2))) ^ 2
      = 16 * |w.im| ^ 3 * Real.exp (-(Real.pi * |w.im|)) := by
    have e : (4 * Real.sqrt (|w.im| ^ 3)
          * Real.exp (-(Real.pi * |w.im| / 2))) ^ 2
        = 16 * ((Real.sqrt (|w.im| ^ 3)) ^ 2)
          * ((Real.exp (-(Real.pi * |w.im| / 2))) ^ 2) := by
      ring
    rw [e, hsqrt_sq, hexp_sq]
  have hle2 : ‖Complex.Gamma w‖ ^ 2
      ≤ (4 * Real.sqrt (|w.im| ^ 3) * Real.exp (-(Real.pi * |w.im| / 2))) ^ 2 := by
    rw [hRHS_sq]
    exact hsq
  have hle_sqrt := Real.sqrt_le_sqrt hle2
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hRHS_nonneg] at hle_sqrt
  exact hle_sqrt

#print axioms CH2GammaTail.sinh_ge_exp_div_four
#print axioms CH2GammaTail.Gamma_Re2_tail_sq
#print axioms CH2GammaTail.Gamma_Re2_tail_upper

end CH2GammaTail

/-!
CH2 VERDICT + RESIDUAL (report-and-stop): ONE Gamma-tail upper GREEN, stop per brief.
EXPLICIT C ACHIEVED: `C = 4` (`C² = 16`) in
`‖Γ w‖ ≤ 4·√(|Im w|³)·e^{-π|Im w|/2}` (`Re w = 2`, `8.75 ≤ |Im w|`),
squared form `‖Γ w‖² ≤ 16·|Im w|³·e^{-π|Im w|}`.
Route: AR reflection identity (`Gamma_Re2_normSq`) + `t·coth`-style decay
extraction (`sinh_ge_exp_div_four`, the tail analogue of `t_mul_coth_le`) +
explicit tail numerals (`1+|y|² ≤ (1241/1225)|y|²`, `(1241/1225)(4π) ≤ 16`).
No cosine-joint composition / edge numbers attempted (per brief: STOP after this
builds green — it is commit-worthy). Downstream hTail/P1 wiring (joint `Γ·cos`
Gaussian analysis, top-edge 5.5x / negative-edge ~18x) is NOT claimed here.
No `sorry`/`admit`/`axiom` in this tail.
-/
