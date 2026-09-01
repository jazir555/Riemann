import Mathlib
import riemann_hypothesis
import riemann_hypothesis_newsection

open Complex Real

/-!
# Cross-door synthesis: the xi-critical / hard-difference tail bridge

The three RH-equivalence doors each carry a committed bridge theorem.  Two of
them compose into a genuine cross-door advance:

* **Hard-difference door** (`riemann_hypothesis_newsection.lean`)
  `mollified_rouche_leaf_implies_tail_hard_difference_nonzero`:
  a `MollifiedRoucheLeaf K` forces
  `1/(z²+¼) - completedRiemannZeta₀(shiftedS z) ≠ 0` for every off-real `z`
  with `|Re z| > 10` and `0 < z.im < 1/2`.

* **Xi-critical door** (`riemann_hypothesis.lean`)
  `xiShifted_conjugate_symmetric_from_identity` + `xiShifted_eq_completed` +
  `xiShifted_ne_zero_iff_completed_ne_inv_D`:
  `xiShifted z ≠ 0 ↔ 1/(z²+¼) - completedRiemannZeta₀(shiftedS z) ≠ 0`
  (off the real axis), and the conjugation symmetry
  `xiShifted(star z) = star (xiShifted z)` maps the lower half of the strip
  onto the upper half.

Composing them yields a **two-sided** tail nonvanishing certificate for
`xiShifted`: the hard-difference bridge gives the upper half (`0 < z.im < 1/2`);
conjugation symmetry turns that into the lower half
(`-1/2 < z.im < 0`).  Combined with the `|Re z| > 10` condition (which already
covers both `Re z > 10` and `Re z < -10`), this closes the *entire* off-axis
tail `|Re z| > 10` from a single `MollifiedRoucheLeaf`.  The only residual — for BOTH doors — is a finite
zero-free cover of the central rectangle `|Re z| ≤ 10`.

This is the concrete cross-door advance: it halves the missing piece (one
Rouché leaf does both halves of the tail) and unifies the residual of the
xi-critical and hard-difference doors onto a single finite cover.
-/

open Complex Real

section CrossDoorTailBridge

/-- The upper-tail nonvanishing conclusion for `xiShifted` that follows from
the hard-difference door's Rouché bridge.  A `MollifiedRoucheLeaf K` forces
`xiShifted z ≠ 0` for every off-real `z` with `|Re z| > 10` and
`0 < z.im < 1/2`.  Proof: the bridge gives the difference
`1/(z²+¼) - completedRiemannZeta₀(shiftedS z) ≠ 0`, which equals
`2·xiShifted z/(z²+¼)`; the scalar factor and denominator are nonzero, so
`xiShifted z ≠ 0`. -/
theorem xiShifted_upper_tail_nonvanishing_from_mollified_rouche
    (K : ℕ) (H : MollifiedAttack.MollifiedRoucheLeaf K)
    (z : ℂ) (hx : 10 < |z.re|) (hy0 : 0 < z.im) (hy1 : z.im < (1 / 2 : ℝ)) :
    xiShifted z ≠ 0 := by
  have hdiff :
      1 / (z ^ 2 + (1 / 4 : ℂ)) - completedRiemannZeta₀ (shiftedS z) ≠ 0 :=
    MollifiedAttack.mollified_rouche_leaf_implies_tail_hard_difference_nonzero K H z hx hy0 hy1
  have heq : 1 / (z ^ 2 + (1 / 4 : ℂ)) - completedRiemannZeta₀ (shiftedS z) =
      2 * xiShifted z / (z ^ 2 + (1 / 4 : ℂ)) := by
    have h := completedZeta_shifted_eq_inv_D_sub_two_xiShifted_div_D z
      (by linarith : -(1 / 2 : ℝ) < z.im) hy1 (by linarith : z.im ≠ 0)
    calc
      1 / (z ^ 2 + (1 / 4 : ℂ)) - completedRiemannZeta₀ (shiftedS z)
          = 1 / (z ^ 2 + (1 / 4 : ℂ)) - (1 / (z ^ 2 + (1 / 4 : ℂ)) -
              2 * xiShifted z / (z ^ 2 + (1 / 4 : ℂ))) := by rw [h]
      _ = 2 * xiShifted z / (z ^ 2 + (1 / 4 : ℂ)) := by ring
  rw [heq] at hdiff
  have hxi_nz : xiShifted z ≠ 0 := by
    intro h
    apply hdiff
    rw [h, mul_zero, zero_div]
  exact hxi_nz

/-- The lower half of the strip is obtained from the upper half by the
conjugation symmetry `w = star z` (which flips the sign of `im`).  The
conjugation symmetry of `xiShifted` rewrites `xiShifted z = xiShifted (star w)`
to `star (xiShifted w)`, which is nonzero exactly when `xiShifted w ≠ 0`. -/
theorem xiShifted_lower_tail_nonvanishing_from_upper
    (upper : ∀ z : ℂ, 10 < |z.re| → 0 < z.im → z.im < (1 / 2 : ℝ) → xiShifted z ≠ 0)
    (z : ℂ) (hx : 10 < |z.re|) (hy0 : -(1 / 2 : ℝ) < z.im) (hy1 : z.im < 0) :
    xiShifted z ≠ 0 := by
  let w := star z
  have hw_re : |w.re| = |z.re| := by
    simp only [w]
    rfl
  have hw_im : w.im = -z.im := by simp [w]
  have hzim_pos : 0 < w.im := by rw [hw_im]; linarith
  have hzim_lt : w.im < (1 / 2 : ℝ) := by rw [hw_im]; linarith
  have hw_nz : xiShifted w ≠ 0 := upper w (by rw [hw_re]; exact hx) hzim_pos hzim_lt
  have hwz : z = star w := by simp [w]
  have hsym := classicalXi_symmetry.conj_symm w
      (by rw [hw_im]; linarith)
      (by rw [hw_im]; linarith)
  have h : xiShifted z = star (xiShifted w) := by rw [hwz]; exact hsym
  rw [h]
  intro hs
  have : xiShifted w = 0 := by rwa [star_eq_zero] at hs
  exact hw_nz this

/-- **Cross-door composition.**  A single `MollifiedRoucheLeaf K` forces
`xiShifted z ≠ 0` for every off-real `z` with `|Re z| > 10` and
`-1/2 < z.im < 1/2` (both halves of the strip).  This is the two-sided tail
certificate obtained by composing the hard-difference door's Rouché bridge
with the xi-critical door's conjugation symmetry. -/
theorem xiShifted_off_axis_tail_nonvanishing_from_mollified_rouche
    (K : ℕ) (H : MollifiedAttack.MollifiedRoucheLeaf K)
    (z : ℂ) (hx : 10 < |z.re|) (hy0 : -(1 / 2 : ℝ) < z.im)
    (hy1 : z.im < (1 / 2 : ℝ)) (hne : z.im ≠ 0) :
    xiShifted z ≠ 0 := by
  by_cases hpos : 0 < z.im
  · exact xiShifted_upper_tail_nonvanishing_from_mollified_rouche K H z hx hpos hy1
  · have hneg : z.im < 0 := by
      have hle : z.im ≤ 0 := by linarith
      exact lt_of_le_of_ne hle hne
    have upper := fun w hw0 hw1 hw2 =>
      xiShifted_upper_tail_nonvanishing_from_mollified_rouche K H w hw0 hw1 hw2
    exact xiShifted_lower_tail_nonvanishing_from_upper upper z hx hy0 hneg

end CrossDoorTailBridge
