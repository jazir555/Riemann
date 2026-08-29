import Mathlib

open BigOperators Complex

/-!
# TailLaguerreScratch

Narrow scratch extraction of `TailCanonicalLaguerrePositivityLeaf` and
`MollifiedRoucheLeaf` from `riemannhypothesis.lean`.

The heavy RH machinery (`xiShiftedLaguerreCoefficient`, `zeta`, `shiftedS`,
`dirichletMollifier`) is re-declared here only as a *minimal interface stub* so
the two structures compile without importing the 133k-line source file. The
stubs are not proofs and are not `sorry`; they are placeholders for the
orchestrator to replace with the real definitions.

The only genuinely proven results here are two small, finite, analytic
sub-lemmas that feed the leaves:
* `geomTailDecay`  — a plain real tail-decay bound (geometric series).
* `rectNormBound`  — an explicit squared-modulus bound on a finite rectangle
  (`Complex.normSq z ≤ 2`, i.e. `|z| ≤ √2`, on `|Re z|,|Im z| ≤ 1`).
-/

-- Minimal interface stubs (placeholders; replace with real defs later).
noncomputable def xiShiftedLaguerreCoefficient (_n : ℕ) (_r : ℝ) : ℝ := 0
noncomputable def zeta (_s : ℂ) : ℂ := 0
def shiftedS (s : ℂ) : ℂ := s
def dirichletMollifier (_s : ℂ) (_K : ℕ) : ℂ := 1

/-- Extracted from `riemannhypothesis.lean` (structure at line 12269). -/
structure TailCanonicalLaguerrePositivityLeaf where
  coefficient_nonneg :
    ∀ n : ℕ, ∀ r : ℝ,
      10 < r →
      0 ≤ xiShiftedLaguerreCoefficient n r
  coefficient_exists_pos :
    ∀ r : ℝ,
      10 < r →
      ∃ n : ℕ, 0 < xiShiftedLaguerreCoefficient n r

/-- Extracted from `riemannhypothesis.lean` (structure at line 13731). -/
structure MollifiedRoucheLeaf (K : ℕ) where
  gap : ∀ (z : ℂ), 10 < |z.re| → 0 < z.im → z.im < (1 / 2 : ℝ) →
    ‖zeta (shiftedS z) * dirichletMollifier (shiftedS z) K - 1‖ < 1

/-- **Finite tail-decay estimate.** For `1 < r` the truncated tail
`∑_{i=0}^{N-1} r^{-(i+1)}` is strictly bounded by the convergent geometric sum
`1/(r-1)`. This is a plain real inequality and feeds any tail estimate in the
Laguerre / Rouché machinery. -/
theorem geomTailDecay {r : ℝ} (hr : 1 < r) (N : ℕ) :
    (∑ i ∈ Finset.range N, (r⁻¹) ^ (i + 1)) < 1 / (r - 1) := by
  let a := r⁻¹
  have hr' : 0 < r := by linarith
  have ha : 0 < a := by positivity
  have ha1 : a < 1 := by
    rw [show a = r⁻¹ by rfl]
    field_simp [ne_of_gt hr']
    linarith
  cases N with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty]
    exact div_pos zero_lt_one (sub_pos.mpr hr)
  | succ n =>
    have hsum : (∑ i ∈ Finset.range (n + 1), a ^ (i + 1)) =
        a * (1 - a ^ (n + 1)) / (1 - a) := by
      calc
        (∑ i ∈ Finset.range (n + 1), a ^ (i + 1))
            = (∑ i ∈ Finset.range (n + 1), a ^ i * a) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact pow_succ a i
        _ = (∑ i ∈ Finset.range (n + 1), a ^ i) * a := by rw [Finset.sum_mul]
        _ = a * (∑ i ∈ Finset.range (n + 1), a ^ i) := by rw [mul_comm]
        _ = a * ((a ^ (n + 1) - 1) / (a - 1)) := by rw [geom_sum_eq (ne_of_lt ha1) (n + 1)]
        _ = a * (1 - a ^ (n + 1)) / (1 - a) := by
              have h1 : (a ^ (n + 1) - 1) / (a - 1) = (1 - a ^ (n + 1)) / (1 - a) := by
                field_simp [sub_ne_zero.mpr (ne_of_lt ha1), sub_ne_zero.mpr (ne_of_lt ha1).symm]
                ring_nf
              rw [h1, mul_div_assoc]
    rw [hsum]
    have hlt : a * (1 - a ^ (n + 1)) < a := by
      nlinarith [mul_pos ha (pow_pos ha (n + 1))]
    have hden : 0 < 1 - a := by linarith
    have hmain : a * (1 - a ^ (n + 1)) / (1 - a) < a / (1 - a) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_lt_mul_of_pos_right hlt (inv_pos.mpr hden)
    have hfinal : a / (1 - a) = 1 / (r - 1) := by
      rw [show a = r⁻¹ by rfl]
      field_simp [ne_of_gt hr']
    exact hmain.trans_eq hfinal

/-- **Explicit bound on a finite rectangle.** On the box `|Re z| ≤ 1`,
`|Im z| ≤ 1` the squared complex modulus satisfies `Complex.normSq z ≤ 2`
(equivalently `|z| ≤ √2`). A plain real inequality via
`Complex.normSq z = Re(z)² + Im(z)²`; it is the elementary geometry behind any
finite-rectangle estimate feeding the leaves. -/
theorem rectNormBound (z : ℂ) (hre : |z.re| ≤ 1) (him : |z.im| ≤ 1) :
    z.re ^ 2 + z.im ^ 2 ≤ 2 := by
  rw [pow_two, pow_two]
  calc
    z.re * z.re + z.im * z.im ≤ 1 + 1 :=
      add_le_add (abs_le_one_iff_mul_self_le_one.mp hre) (abs_le_one_iff_mul_self_le_one.mp him)
    _ ≤ 2 := by norm_num
