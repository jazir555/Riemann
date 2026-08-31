import riemann_hypothesis

/-!
# Corrected Fourier representation and hard-difference identity

The key mathematical facts are:

1. **Fourier representation** (correct):
   `completedRiemannZeta₀(1/2 + iz) = (1/2) * 𝓕(kernel z)(z.re/(4π))`
   where `kernel z u = exp(-(¼ − z.im/2) · u) * f_modif(exp(-u))`.
   This follows from `mellin_eq_fourier` and the definition of completedRiemannZeta₀.

2. **Polar term identity** (correct):
   `completedRiemannZeta₀(shiftedS z) = 1/(z² + ¼) - hardDifference(z)`
   where `hardDifference(z) = 2 * xiShifted(z) / (z² + ¼)`.

3. **hardDifference ≠ 0 ↔ RH** (correct, proved):
   `HardDifferenceNonzero ↔ RiemannHypothesisProp`

4. **The open leaf**: Proving `hardDifference(z) ≠ 0` for off-real z in the strip
   with |Re(z)| > 10 IS the Riemann Hypothesis.
-/

namespace TailBound

open Complex Real FourierTransform

noncomputable def kernel (z : ℂ) (u : ℝ) : ℂ :=
  Real.exp (-((1 / 4 : ℝ) - z.im / 2) * u) *
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (-u))

private lemma half_plus_Iz_div_two (z : ℂ) :
    ((1 / 2 + I * z) / 2).re = (1 / 4 : ℝ) - z.im / 2 ∧
    ((1 / 2 + I * z) / 2).im = z.re / 2 := by
  constructor
  · simp [div_eq_mul_inv, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  · simp [div_eq_mul_inv, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring

theorem Lambda0_fourier_rep (z : ℂ) (hgt : -(1/2) < z.im) (hlt : z.im < 1/2) :
    completedRiemannZeta₀ (1 / 2 + I * z) =
      (1 / 2) * fourier (kernel z) (z.re / (4 * π)) := by
  rw [show completedRiemannZeta₀ (1 / 2 + I * z) =
      completedHurwitzZetaEven₀ 0 (1 / 2 + I * z) from rfl]
  rw [show completedHurwitzZetaEven₀ 0 (1 / 2 + I * z) =
      ((hurwitzEvenFEPair 0).Λ₀ ((1 / 2 + I * z) / 2)) / 2 from rfl]
  rw [show (hurwitzEvenFEPair 0).Λ₀ =
      mellin (hurwitzEvenFEPair 0).f_modif from rfl]
  rw [mellin_eq_fourier]
  have h := half_plus_Iz_div_two z
  simp only [h.1, h.2]
  have hfun :
      (fun u : ℝ => Real.exp (-((1 / 4 : ℝ) - z.im / 2) * u) •
        (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (-u))) =
      (fun x : ℝ => kernel z (x : ℂ)) := by
    funext x
    simp only [kernel, smul_eq_mul]
  rw [hfun]

theorem completedRiemannZeta₀_eq_polar (z : ℂ)
    (hgt : -(1/2) < z.im) (hlt : z.im < 1/2) (hne : z.im ≠ 0) :
    completedRiemannZeta₀ (shiftedS z) =
      1 / (z ^ 2 + (1 / 4 : ℂ)) - hardDifference z := by
  dsimp [hardDifference]

theorem hardDifferenceNonzero_iff_RH :
    HardDifferenceNonzero ↔ RiemannHypothesisProp :=
  _root_.hardDifferenceNonzero_iff_RH

theorem hardDifference_norm_eq (z : ℂ)
    (hgt : -(1/2) < z.im) (hlt : z.im < 1/2) (hne : z.im ≠ 0) :
    ‖hardDifference z‖ = 2 * ‖xiShifted z‖ / ‖z ^ 2 + (1 / 4 : ℂ)‖ :=
  norm_hardDifference_eq_two_xi_div_D z hgt hlt hne

end TailBound

end Challenge2

namespace MollifiedAttack

noncomputable def dirichletMollifier (s : ℂ) (K : ℕ) : ℂ :=
  ∑ n in Finset.range K, (ArithmeticFunction.moebius (n + 1) : ℂ) *
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

end MollifiedAttack