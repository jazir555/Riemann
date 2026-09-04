import riemann_hypothesis
import zeta_rigorous
import central_cover_assembly
import interval_arith

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


