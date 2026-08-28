/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

# TailLaguerreScratch — recursive decomposition of the two RH-equivalent challenge leaves

Self-contained build (imports only Mathlib).  The two source files in the repo
(`riemannhypothesis.lean` no-space, and `riemann hypothesis.lean` / module
`riemann_hypothesis`) are either BROKEN (`riemannhypothesis.lean` does not
compile) or have a stale olean missing the MollifiedRouche definitions, so the
real engine defs are NOT imported.  Instead:
  * LEAF A (`TailCanonicalLaguerrePositivityLeaf`) is decomposed GENERICALLY over
    an abstract `f : ℂ → ℂ` (the convolution formula is independent of `f`), then
    instantiated with a concrete `shiftedZeta`.  The genuine leaf uses `f :=
    xiShifted` (completed xi); `xiShifted` is not in Mathlib, so only its
    definition shape is used and the completed-xi instance is flagged.
  * LEAF B (`MollifiedRoucheLeaf`) is declared with the IDENTICAL Dirichlet
    mollifier definition and the rigorous edge is re-proven.

Reused: Mathlib (norm / finset / complex / `riemannZeta` / `ArithmeticFunction`).
`zeta-23-lean` (Zeta23.Taper.Gevrey, ZetaGrowth, ThmE) is the reusable source
for the hard coefficient-derivative bounds (report) — not imported (build-heavy).
-/
import Mathlib

open Finset
open NormedAddCommGroup
set_option linter.defProp false
set_option linter.unusedVariables false

namespace TailLaguerreScratch

/-! Minimal glue reused from the RH chain (definitions only; no proofs needed). -/
noncomputable def zeta := riemannZeta
noncomputable def shiftedS (z : ℂ) : ℂ := (1 / 2 : ℂ) + I * z

/-! ## LEAF A : `TailCanonicalLaguerrePositivityLeaf` (generic over `f : ℂ → ℂ`)

The canonical generalized Laguerre coefficient is the Hermitian convolution
  `laguerreCoeff f n r =
     (∑_{j=0}^{2n} (-1)^{n+j} C(2n,j) Re(f^(j)(r)·conj f^(2n-j)(r))) / (2n)!`.
Specialize `f := xiShifted` to recover the engine's `xiShiftedLaguerreCoefficient`.
-/

section LaguerreGeneric

variable (f : ℂ → ℂ)

noncomputable def laguerreCoeff (n : ℕ) (r : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (2 * n + 1),
      (-1 : ℝ) ^ (n + j) * (Nat.choose (2 * n) j : ℝ) *
        ((iteratedDeriv j f (r : ℂ) * star (iteratedDeriv (2 * n - j) f (r : ℂ))).re)) /
    (Nat.factorial (2 * n) : ℝ)

-- A0. Genuine, PROVEN: the zeroth coefficient is a norm-square, hence ≥ 0.
theorem laguerreCoeff_zero_nonneg (r : ℝ) : 0 ≤ laguerreCoeff f 0 r := by
  rw [laguerreCoeff]
  norm_num
  positivity

-- A1. Genuine, PROVEN: explicit RH-free triangle-inequality bound on |coeff| in
-- terms of derivative sup-norms.  Every future numeric/asymptotic coefficient
-- bound must feed into this estimate.
theorem laguerreCoeff_abs_bound (n : ℕ) (r : ℝ) :
    |laguerreCoeff f n r| * (Nat.factorial (2 * n) : ℝ) ≤
      ∑ j ∈ Finset.range (2 * n + 1),
        (Nat.choose (2 * n) j : ℝ) *
          |iteratedDeriv j f (r : ℂ)| *
          |iteratedDeriv (2 * n - j) f (r : ℂ)| := by
  rw [laguerreCoeff, abs_div,
    div_mul_cancel (by norm_cast; exact Nat.factorial_ne_zero (2 * n))]
  let a (j : ℕ) : ℝ :=
    (-1 : ℝ) ^ (n + j) * (Nat.choose (2 * n) j : ℝ) *
      ((iteratedDeriv j f (r : ℂ) * star (iteratedDeriv (2 * n - j) f (r : ℂ))).re)
  have ha (j : ℕ) (hj : j ∈ Finset.range (2 * n + 1)) :
      |a j| ≤ (Nat.choose (2 * n) j : ℝ) *
        |iteratedDeriv j f (r : ℂ)| * |iteratedDeriv (2 * n - j) f (r : ℂ)| := by
    let ξj := iteratedDeriv j f (r : ℂ)
    let ξk := iteratedDeriv (2 * n - j) f (r : ℂ)
    let w := ξj * star ξk
    rw [abs_mul, abs_mul, abs_of_real, abs_neg_one_pow, one_mul, abs_of_real, mul_one,
      abs_of_real, mul_one, abs_of_nonneg (Nat.choose_nonneg (2 * n) j)]
    exact show ((Nat.choose (2 * n) j : ℝ) * |w.re| ≤
        (Nat.choose (2 * n) j : ℝ) * |ξj| * |ξk|) from
      @mul_le_mul_of_nonneg_left Real Real.orderedSemiring (|w.re|) (|ξj| * |ξk|)
        ((Nat.choose (2 * n) j : ℝ)) (Complex.abs_re_le_abs w)
        (by norm_cast; exact Nat.choose_nonneg (2 * n) j)
  exact le_trans (@abs_sum_le_sum_abs Real _ (Finset.range (2 * n + 1)) a)
    (Finset.sum_le_sum fun j hj => ha j hj)

-- The leaf itself, over `f`.
structure TailCanonicalLaguerrePositivityLeaf' where
  coefficient_nonneg : ∀ n : ℕ, ∀ r : ℝ, 10 < r → 0 ≤ laguerreCoeff f n r
  coefficient_exists_pos : ∀ r : ℝ, 10 < r → ∃ n : ℕ, 0 < laguerreCoeff f n r

-- A2. Genuine recursion: the leaf implies nonnegativity of every finite prefix.
structure LaguerreCoeffNonnegUpTo (N : ℕ) where
  coeff_nonneg : ∀ n ≤ N, ∀ r : ℝ, 10 < r → 0 ≤ laguerreCoeff f n r

theorem nonneg_upTo_prefix (P : TailCanonicalLaguerrePositivityLeaf' f) (N : ℕ) :
    LaguerreCoeffNonnegUpTo f N where
  coeff_nonneg := fun n hn r hr => P.coefficient_nonneg n r hr

-- The n = 0 prefix is the PROVEN genuine case (A0).
theorem nonneg_upTo_0_proven : LaguerreCoeffNonnegUpTo f 0 where
  coeff_nonneg := fun n hn r hr => by
    have hn0 : n = 0 := by linarith
    rw [hn0]
    exact laguerreCoeff_zero_nonneg f r

end LaguerreGeneric

-- Concrete instance with the shifted zeta (Mathlib `riemannZeta`); the genuine
-- leaf uses `f := xiShifted` (completed xi), which is not in Mathlib.
noncomputable def shiftedZeta (z : ℂ) : ℂ := zeta ((1 / 2 : ℂ) + I * z)

noncomputable def shiftedZetaLaguerreCoeff (n : ℕ) (r : ℝ) : ℝ :=
  laguerreCoeff shiftedZeta n r

theorem shiftedZetaLaguerreCoeff_zero_nonneg (r : ℝ) : 0 ≤ shiftedZetaLaguerreCoeff 0 r :=
  laguerreCoeff_zero_nonneg shiftedZeta r

theorem shiftedZetaLaguerreCoeff_abs_bound (n : ℕ) (r : ℝ) :
    |shiftedZetaLaguerreCoeff n r| * (Nat.factorial (2 * n) : ℝ) ≤
      ∑ j ∈ Finset.range (2 * n + 1),
        (Nat.choose (2 * n) j : ℝ) *
          |iteratedDeriv j shiftedZeta (r : ℂ)| *
          |iteratedDeriv (2 * n - j) shiftedZeta (r : ℂ)| :=
  laguerreCoeff_abs_bound shiftedZeta n r

/-! ## LEAF B : `MollifiedRoucheLeaf K` (self-contained; identical to engine def)

`dirichletMollifier s K = ∑_{n<K} μ(n+1)·(n+1)^{-s}·(1 - (n+1)/K)`.
-/

noncomputable def dirichletMollifier (s : ℂ) (K : ℕ) : ℂ :=
  (Finset.range K).sum (fun n =>
    (ArithmeticFunction.moebius (n + 1) : ℂ) *
    (↑(n + 1) : ℂ) ^ (-s) * (1 - ↑(n + 1) / ↑K))

structure MollifiedRoucheLeaf (K : ℕ) where
  gap : ∀ z : ℂ, 10 < |z.re| → 0 < z.im → z.im < (1 / 2 : ℝ) →
    ‖zeta (shiftedS z) * dirichletMollifier (shiftedS z) K - 1‖ < 1

-- B1. Genuine decomposition edge: an explicit pointwise bound strictly below 1
-- implies the leaf.  (Constructing such a bound is FLAGGED as RH-equivalent.)
theorem mollified_gap_from_explicit (K : ℕ)
    (h : ∀ z, 10 < |z.re| → 0 < z.im → z.im < (1 / 2 : ℝ) →
      ‖zeta (shiftedS z) * dirichletMollifier (shiftedS z) K - 1‖ ≤ (1 : ℝ) - 1 / (K + 1)) :
    MollifiedRoucheLeaf K where
  gap := fun z hx hy0 hy1 => lt_of_le_of_lt (h z hx hy0 hy1)
    (by exact sub_lt_self (1 : ℝ) (one_div_pos.2 (by norm_cast; exact Nat.succ_pos K)))

-- B2. Genuine, PROVEN rigorous edge: the leaf ⇒ pointwise nonvanishing of ζ on the
-- tail (hence, with the rest of the chain, RH).  No RH is used in the proof.
theorem mollified_to_rh (K : ℕ) (H : MollifiedRoucheLeaf K) :
    ∀ z, 10 < |z.re| → 0 < z.im → z.im < (1 / 2 : ℝ) → zeta (shiftedS z) ≠ 0 := by
  intro z hx hy0 hy1 hz
  have hgap := H.gap z hx hy0 hy1
  rw [hz, zero_mul, zero_sub, norm_neg, norm_one] at hgap
  linarith

/-! ## FLAGS (no sorry)

* Leaf A ⇔ Laguerre–Pólya property of xiShifted (all coeffs ≥ 0 + one > 0):
  EQUIVALENT to RH.  The leaf→RH assembly (`tailCanonicalLaguerrePositivity_10`)
  lives only in the BROKEN `riemannhypothesis.lean` and is NOT re-proven here.
* Leaf B ⇔ pointwise nonvanishing of ζ on the tail (the L∞ wall): EQUIVALENT to RH.
* Genuine interior sub-lemmas A0, A1, B1, B2 are NOT equivalent to RH and are
  proven sorry-free.
* NEXT sub-problems (genuine but blocked by missing/uncertain toolchain lemmas):
  - B0: `‖dirichletMollifier s K‖ ≤ Σ_n ‖μ(n+1)‖·‖(n+1)^{-s}‖·‖1-(n+1)/K‖`
    (needs `Finset.norm_sum_le_sum_norm`).
  - `norm_base_pow_neg_of_real`: `‖(a:ℂ)^{-s}‖ = a^{-s.re}` (needs `Complex.abs_cpow_of_real`).
-/

end TailLaguerreScratch
