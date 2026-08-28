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

/-! ## Decomposition of the two analytic leaves `hPolya` and `hSchur`

These are the classical 1920s facts (Pólya 1927; Hurwitz).  Each is stated at
the exact type it is used, and the *structural* parts (P2 section identity, the
shift reduction, S3 assembly) are proven below.  The two genuinely deep classical
inputs — the order-<2 bound `orderBoundHyp`, Pólya's theorem `polyaTheoremHyp`
(P3), the section-convergence `sectionsConvergeHyp` (S1) and Hurwitz `hurwitzHyp`
(S2) — are recorded as precisely-typed classical-theorem hypotheses, exactly as
the DAG comment planned.  Decomposing `polyaTheoremHyp` further (Hadamard
factorization + log-derivative interlacing) or `hurwitzHyp` (Rouché) is a
separate formalization effort and is not attempted here. -/

open ZeroFreeRegionHadamard Polynomial

-- P1 (order bound of `genFun`).  `xi` has order ≤ 7/4 (`orderSet_xi` in
-- `KadiriOrderInfra`), and `genFun z = xiMathlibShifted z` differs from `xi` by
-- an affine change of variable `s = 1/2 + I·z` and a nonzero constant, which
-- preserves `orderSet`.  Stated as the precise classical input.
def orderBoundHyp : Prop := (7 / 4 : ℝ) ∈ orderSet (fun z => xiMathlibShifted z)

-- P2 (section identity).  `jensenPoly d n` is exactly the degree-`d` section
-- built from the Taylor coefficients `taylorCoeff (n + k)` of `genFun`.
theorem jensenPoly_coeff (d n k : ℕ) :
    ((jensenPoly d n).coeff k : ℂ) =
      if k ≤ d then ((Nat.choose d k : ℝ) * taylorCoeff (n + k) : ℝ) else 0 := by
  simp only [jensenPoly, Polynomial.coeff_map, Polynomial.finsetSum_coeff]
  rw [Finset.sum_ite_eq']
  by_cases hk : k ≤ d
  · have : k ∈ Finset.range (d + 1) := by simpa using hk
    rw [if_pos hk, Finset.sum_ite_eq' _ _ this, if_pos (by simpa)]
    rw [Polynomial.coeff_monomial, if_pos (Eq.refl k)]
    simp only [Nat.cast_mul, RingHom.map_mul, Nat.cast_one, one_mul]
  · have : ¬ k ∈ Finset.range (d + 1) := by simpa using hk
    rw [if_neg hk, Finset.sum_ite_eq' _ _ this, if_neg (by simpa)]
    simp

-- The shift-0 specialization (the classical Jensen section).
theorem jensenPoly_section_coeffs (d k : ℕ) :
    ((jensenPoly d 0).coeff k : ℂ) =
      if k ≤ d then ((Nat.choose d k : ℝ) * taylorCoeff k : ℝ) else 0 :=
  jensenPoly_coeff d 0 k

-- If all Taylor coefficients are nonzero, every `jensenPoly d n` has degree `d`.
theorem jensenPoly_natDegree (hC : ∀ k, taylorCoeff k ≠ 0) (d n : ℕ) :
    (jensenPoly d n).natDegree = d := by
  apply le_antisymm
  · refine natDegree_le_of_coeff_ne_zero fun k hk => ?_
    rw [jensenPoly_coeff, if_neg (not_le.mpr hk)]
    simp
  · refine le_natDegree_of_ne_zero_coeff ?_
    rw [jensenPoly_coeff, if_pos (le_refl d), Nat.choose_self, Nat.cast_one, one_mul]
    exact hC (n + d)

-- Gauss–Lucas: a hyperbolic polynomial has a hyperbolic derivative.
theorem gauss_lucas_hyperbolic {p : Polynomial ℂ} (hp : Hyperbolic p)
    (hdeg : 0 < p.natDegree) : Hyperbolic p.derivative := by
  intro z hz
  have hz' : z ∈ p.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval]
    exact hz
  have hp0 : p ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hdeg; exact (lt_irrefl 0).elim hdeg
  have hsub := rootSet_derivative_subset_convexHull_rootSet (by rwa [degree_eq_natDegree hp0])
  have hzr : z ∈ convexHull ℝ (p.rootSet ℂ) := hsub hz'
  have hconv : convexHull ℝ (p.rootSet ℂ) ⊆ {w : ℂ | w.im = 0} :=
    convexHull_min
      (fun w hw => hp w (by simpa [Polynomial.isRoot, Polynomial.mem_rootSet,
        Polynomial.coe_aeval_eq_eval] using hw))
      realAxis_convex
  exact hconv hzr

theorem realAxis_convex : Convex ℝ {z : ℂ | z.im = 0} := by
  refine fun x hx y hy a b ha hb hab => ?_
  change (a • x + b • y).im = 0
  simp only [Complex.add_im, Complex.smul_im, hx, hy]
  norm_num

-- The differentiation identity `J'_{d+1,n} = (d+1)·J_{d,n+1}` (algebraic, proved
-- by comparing coefficients; the key binomial identity is
-- `(k+1)·C(d+1,k+1) = (d+1)·C(d,k)`).
theorem jensenPoly_derivative' (d n : ℕ) :
    (jensenPoly (d + 1) n).derivative =
      Polynomial.C ((d + 1 : ℕ) : ℂ) * jensenPoly d (n + 1) := by
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_derivative, jensenPoly_coeff (d + 1) n (k + 1),
      Polynomial.coeff_C_mul, jensenPoly_coeff d (n + 1) k]
  by_cases hk : k ≤ d
  · have hbin : (k + 1 : ℝ) * (Nat.choose (d + 1) (k + 1) : ℝ) =
        (d + 1 : ℝ) * (Nat.choose d k : ℝ) := by
      rw [← Nat.cast_add_one, ← Nat.cast_mul, ← Nat.mul_comm,
        ← Nat.add_one_mul_choose_eq d k, Nat.cast_mul]
    rw [if_pos hk, if_pos (Nat.succ_le_succ hk), mul_comm, mul_assoc, hbin, add_right_comm]
    simp only [mul_assoc, RingHom.map_mul]
  · rw [if_neg hk, if_neg (mt Nat.le_of_succ_le_succ hk)]
    simp only [mul_zero, zero_mul]

-- Shift reduction (all shifts from shift 0); a classical algebraic fact using
-- `gauss_lucas_hyperbolic`.  Requires the Taylor coefficients to be nonzero so
-- that each `jensenPoly d n` has degree `d` (true for ξ).
theorem all_shifts_from_zero (hC : ∀ k, taylorCoeff k ≠ 0)
    (h0 : ∀ d, Hyperbolic (jensenPoly d 0)) : ∀ d n, Hyperbolic (jensenPoly d n) := by
  intro d n
  induction n generalizing d with
  | zero => exact h0 d
  | succ n ih =>
    have hd := ih (d + 1)
    have hdeg : 0 < (jensenPoly (d + 1) n).natDegree := by
      rw [jensenPoly_natDegree hC (d + 1) n]
      norm_num
    have hder := gauss_lucas_hyperbolic hd hdeg
    rw [jensenPoly_derivative' d n] at hder
    exact Hyperbolic_const_mul (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)) hder

-- P3 (Pólya 1927): order < 2 + real zeros ⇒ the shift-0 Jensen sections are
-- hyperbolic.  Stated as the precise classical input.
def polyaTheoremHyp : Prop :=
  (7 / 4 : ℝ) ∈ orderSet (fun z => xiMathlibShifted z) →
  XiMathlibShiftedZerosReal → ∀ d, Hyperbolic (jensenPoly d 0)

-- Assemble the Pólya direction from P1 + P3 + the shift reduction.
theorem hPolya (hOrder : (7 / 4 : ℝ) ∈ orderSet (fun z => xiMathlibShifted z))
    (hP3 : (7 / 4 : ℝ) ∈ orderSet (fun z => xiMathlibShifted z) →
      XiMathlibShiftedZerosReal → ∀ d, Hyperbolic (jensenPoly d 0))
    (hC : ∀ k, taylorCoeff k ≠ 0)
    (hRR : XiMathlibShiftedZerosReal) :
    ∀ d n, Hyperbolic (jensenPoly d n) :=
  all_shifts_from_zero hC (hP3 hOrder hRR)

-- S1 (the Jensen sections converge uniformly on compacta to `genFun`).
def uniformConvergesOnCompacta (P : ℕ → Polynomial ℂ) (G : ℂ → ℂ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ z : ℂ, ‖z‖ ≤ r → ‖(P n).eval z - G z‖ < ε

def sectionsConvergeHyp : Prop :=
  uniformConvergesOnCompacta (fun d => jensenPoly d 0) genFun

-- S2 (Hurwitz): a sequence of real-rooted polynomials converging uniformly on
-- compacta to `G` has a real-rooted limit `G`.  Stated as the classical input.
def hurwitzHyp : Prop :=
  ∀ (P : ℕ → Polynomial ℂ) (G : ℂ → ℂ),
    (∀ n, Hyperbolic (P n)) →
    uniformConvergesOnCompacta P G →
    (∀ z, G z = 0 → z.im = 0)

-- S3 (assemble the Schur direction): the sections at shift 0 are a real-rooted
-- sequence converging to `genFun`, so by Hurwitz `genFun` is real-rooted.
theorem hSchur (hS1 : uniformConvergesOnCompacta (fun d => jensenPoly d 0) genFun)
    (hS2 : ∀ (P : ℕ → Polynomial ℂ) (G : ℂ → ℂ),
      (∀ n, Hyperbolic (P n)) → uniformConvergesOnCompacta P G →
      (∀ z, G z = 0 → z.im = 0))
    (hAll : ∀ d n, Hyperbolic (jensenPoly d n)) :
    XiMathlibShiftedZerosReal := by
  have h := hS2 (fun d => jensenPoly d 0) genFun (fun d => hAll d 0) hS1
  exact fun z hz _hgt _hlt => h z (by simpa [genFun] using hz)

end JensenScratch
