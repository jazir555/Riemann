import riemann_hypothesis
import zeta_rigorous
import central_cover_assembly

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
