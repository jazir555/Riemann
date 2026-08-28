import Mathlib
import riemann_hypothesis

set_option maxHeartbeats 2000000

open Complex
open Filter
open scoped BigOperators

noncomputable section

namespace JensenScratch

/-!
# Decomposition DAG for `rh_iff_all_jensen_hyperbolic`
# (Pólya–Schur / Griffin–Ono–Rolen–Zagier 2019 theorem)

`JensenTranslation.lean` currently does not compile (its own tactic errors
prevent an `.olean`), so we mirror its three definitions verbatim here and
reuse `RiemannHypothesisProp`, `xiMathlibShifted`, `rh_iff_xiMathlib_shifted_real`,
`XiMathlibZeroEquivalence`, `XiMathlibShiftedZerosReal` from `riemann hypothesis.lean`.

Every node below compiles.  The ONLY unproven inputs are the two classical
analytic leaves `hPolya` and `hSchur` (the Pólya and Schur directions of the
1920s theorem).  Their own sub-decomposition (generating-function/section
identity + Hurwitz root-convergence) is recorded in the comments and in the
final report; each is a known, provable classical fact, not an open problem.

## DAG
  genFun_def                     : G = Ξ = xiMathlibShifted (the generating function)
  rh_bridge                     : RiemannHypothesisProp ↔ XiMathlibShiftedZerosReal
  Hyperbolic_const_mul          : scaling by a nonzero constant preserves hyperbolicity (ALGEBRA, proven)
  jensenPoly_zero               : J_{0,n} = γ_n (ALGEBRA, proven)
  polya_direction_closure       : XiMathlibShiftedZerosReal → ∀d n Hyperbolic(jensenPoly d n)
  schur_direction_closure       : (∀d n Hyperbolic(jensenPoly d n)) → XiMathlibShiftedZerosReal
  polya_schur_closure           : XiMathlibShiftedZerosReal ↔ ∀d n Hyperbolic(jensenPoly d n)
  rh_iff_all_jensen_hyperbolic_closure : RiemannHypothesisProp ↔ ∀d n Hyperbolic(jensenPoly d n)
-/

-- The completed zeta, shifted, IS the generating function G = Ξ(z).
noncomputable def genFun (z : ℂ) : ℂ := xiMathlibShifted z

-- The even Taylor coefficients of Ξ(z) = xiMathlibShifted(z) at 0.
noncomputable def taylorCoeff (n : ℕ) : ℝ :=
  ((Nat.factorial (2 * n) : ℝ)⁻¹) * (deriv^[2 * n] xiMathlibShifted 0).re

-- The Jensen polynomial of degree d and shift n (Pólya–GORZ convention):
--   J_{d,n}(x) = Σ_{k=0}^d binom(d,k)·γ_{n+k}·x^k.
noncomputable def jensenPoly (d n : ℕ) : Polynomial ℂ :=
  (Finset.sum (Finset.range (d + 1)) (fun k =>
    Polynomial.monomial k ((Nat.choose d k : ℝ) * taylorCoeff (n + k))))
    |>.map (algebraMap ℝ ℂ)

-- A polynomial is hyperbolic if all its complex roots are real.
def Hyperbolic (p : Polynomial ℂ) : Prop :=
  ∀ x : ℂ, p.eval x = 0 → x.im = 0

-- ── Node: bridge RH ↔ (shifted xi has only real zeros in the strip) ──────────
-- Reuses the existing equivalence `rh_iff_xiMathlib_shifted_real` from
-- `riemann hypothesis.lean`; `hEquiv` is the zero-equivalence between the
-- mathlib xi and the classical xi (supplied by the normalization chain there).
theorem rh_bridge (hEquiv : XiMathlibZeroEquivalence) :
    RiemannHypothesisProp ↔ XiMathlibShiftedZerosReal :=
  rh_iff_xiMathlib_shifted_real hEquiv

-- ── Node: scaling by a nonzero constant preserves hyperbolicity (ALGEBRA) ─────
theorem Hyperbolic_const_mul {c : ℂ} (hc : c ≠ 0) {p : Polynomial ℂ}
    (hp : Hyperbolic p) : Hyperbolic (Polynomial.C c * p) := by
  intro x hx
  have h' : Polynomial.eval x p = 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_C] at hx
    exact (mul_eq_zero.mp hx).resolve_left hc
  exact hp x h'

-- ── Node: J_{0,n} = γ_n (ALGEBRA) ────────────────────────────────────────────
theorem jensenPoly_zero (n : ℕ) :
    jensenPoly 0 n = Polynomial.C ((taylorCoeff n : ℝ) : ℂ) := by
  simp only [jensenPoly]
  rw [Finset.range_one, Finset.sum_singleton, Nat.choose_zero_right, Nat.cast_one,
      one_mul, Polynomial.monomial_zero_left, Polynomial.map_C]
  simp

-- ── Node: Pólya direction = (Ξ real-rooted) ⇒ (all Jensen hyperbolic) ────────
-- The genuine analytic content is the LP-class fact that sections of a
-- real-rooted entire function of order < 2 are hyperbolic.  It is the
-- hypothesis `hPolya`; the structural composition is proven.
theorem polya_direction_closure
  (hPolya : XiMathlibShiftedZerosReal → ∀ d n, Hyperbolic (jensenPoly d n))
  (hRR : XiMathlibShiftedZerosReal) :
  ∀ d n, Hyperbolic (jensenPoly d n) :=
  hPolya hRR

-- ── Node: Schur direction = (all Jensen hyperbolic) ⇒ (Ξ real-rooted) ────────
-- The genuine analytic content is Hurwitz' theorem: roots of a convergent
-- sequence of real-rooted polynomial sections converge to the roots of the
-- limit G.  It is the hypothesis `hSchur`; the structural composition is proven.
theorem schur_direction_closure
  (hSchur : (∀ d n, Hyperbolic (jensenPoly d n)) → XiMathlibShiftedZerosReal)
  (hAll : ∀ d n, Hyperbolic (jensenPoly d n)) :
  XiMathlibShiftedZerosReal :=
  hSchur hAll

-- ── Node: assemble the two directions into the Pólya–Schur equivalence ───────
theorem polya_schur_closure
  (hPolya : XiMathlibShiftedZerosReal → ∀ d n, Hyperbolic (jensenPoly d n))
  (hSchur : (∀ d n, Hyperbolic (jensenPoly d n)) → XiMathlibShiftedZerosReal) :
  XiMathlibShiftedZerosReal ↔ ∀ d n, Hyperbolic (jensenPoly d n) :=
  ⟨hPolya, hSchur⟩

-- ── Node: close `rh_iff_all_jensen_hyperbolic` ───────────────────────────────
-- Combines the bridge (RH ↔ shifted-real-rooted) with the Pólya–Schur
-- equivalence (shifted-real-rooted ↔ all Jensen hyperbolic).  This is exactly
-- the body of the `sorry` at `JensenTranslation.rh_iff_all_jensen_hyperbolic`.
theorem rh_iff_all_jensen_hyperbolic_closure
  (hEquiv : XiMathlibZeroEquivalence)
  (hPolya : XiMathlibShiftedZerosReal → ∀ d n, Hyperbolic (jensenPoly d n))
  (hSchur : (∀ d n, Hyperbolic (jensenPoly d n)) → XiMathlibShiftedZerosReal) :
  RiemannHypothesisProp ↔ ∀ d n, Hyperbolic (jensenPoly d n) := by
  rw [rh_bridge hEquiv, polya_schur_closure hPolya hSchur]

/-!
## Remaining analytic leaves (classical, known provable — decompose further)

### `hPolya` sub-decomposition
  P1. `genFun` (= xiMathlibShifted) is entire of order < 2 (order 1).
  P2. `jensenPoly d n` are precisely the Jensen/section polynomials of `genFun`.
  P3. (Pólya 1927) an entire function of order < 2 with only real zeros has
      real-rooted Jensen sections ⇒ each `jensenPoly d n` is hyperbolic.

### `hSchur` sub-decomposition (Hurwitz)
  S1. coefficientwise convergence: the Jensen sections `jensenPoly d n`
      converge to `genFun` (Taylor/section expansion of the entire function).
  S2. (Hurwitz' theorem) if `∀n, jensenPoly d n` are real-rooted and converge
      coefficientwise to `genFun`, then every zero of `genFun` is real.
  S3. combine S1+S2 (plus the standard no-outer-zeros fact for ξ) ⇒
      `XiMathlibShiftedZerosReal`.

Each of P1–P3 / S1–S3 is a standard lemma; none is an open problem.
-/

end JensenScratch
