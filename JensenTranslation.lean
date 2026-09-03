import Mathlib
import riemann_hypothesis
import zeta_rigorous

set_option maxHeartbeats 2000000

open Complex
open Filter
open scoped BigOperators

noncomputable section

/-!
# Jensen-polynomial translation of the Riemann Hypothesis

## Why the complex-analytic attempt fails (the diagnosis)

On the critical line, ξ(1/2+it) is real, so Re(ξ'/ξ(1/2+it)) = 0, and the
Hadamard partial-fraction expansion gives

    Σ_ρ (1/2 − β_ρ)/|(1/2+it) − ρ|² = const        (all real t).

The tempting conclusion — "each Lorentzian must vanish, hence β_ρ = 1/2" —
is *vacuous*: the functional equation ξ(s) = ξ(1−s) pairs every zero
ρ = β + iγ with 1 − ρ = (1−β) + iγ (the SAME imaginary part), and the two
Lorentzian contributions cancel identically (same pole location, opposite
residues).  The identity is automatic; it carries no information about the
zeros.  This is why the Pólya-criterion-style route cannot work.

## The isomorphic translation (Riemann's integral representation)

There is a positive, even, rapidly-decaying Φ : ℝ → ℝ (a theta-function
series) such that

    Ξ(z) := ξ(1/2 + iz) = ∫_{−∞}^{∞} Φ(u) e^{iuz} du = 2∫₀^∞ Φ(u) cos(uz) du.

In this picture:

* the functional equation is *already absorbed*: it becomes the evenness of Ξ
  (Ξ(−z) = Ξ(z)), built into the cosine form;
* the Lorentzian cancellation phenomenon disappears — there are no paired
  zeros to cancel, because we have left the s-plane entirely;
* RH becomes the real-analysis statement "the cosine transform of the
  positive even function Φ has only real zeros", i.e. Ξ belongs to the
  Laguerre–Pólya class.

## The tractable branch: real-rooted polynomials (Jensen / Pólya–Schur / GORZ)

Ξ is even, so Ξ(z) = Σ γₙ z^{2n}/(2n)! with γₙ ∈ ℝ.  The classical criterion
(Pólya–Schur; Griffin–Ono–Rolen–Zagier 2019):

    Ξ has only real zeros  ⟺  ∀ d, n : ℕ, the Jensen polynomial
        J_{d,n}(x) = Σ_{k=0}^d binom(d,k)/binom(d+k,k) γ_{n+k} x^k
        is hyperbolic (all roots real).

So RH ⟺ every Jensen polynomial of the shifted xi function is hyperbolic.
This is a translation into the theory of real-rooted polynomials — a separate
branch with concrete algebraic criteria and unconditional asymptotic results:

* d = 1 is automatic (real linear polynomials are hyperbolic);
* d = 2 is the explicit inequality  2 γₙ₊₁² ≥ 3 γₙ γₙ₊₂  (discriminant ≥ 0);
* GORZ 2019: for each fixed d, all but finitely many J_{d,n} are hyperbolic,
  unconditionally, via the explicit formula.

The remaining gap — hyperbolicity for *all* n — is exactly the LP-class
membership of Ξ, i.e. exactly RH.  The translation therefore does not prove
RH, but it converts the open problem into a concrete, checkable statement in
a more algebraic setting, where genuine unconditional progress exists and
where each small degree is an explicit polynomial inequality.
-/

namespace JensenRH

/-- The even Taylor coefficients of Ξ(z) = xiMathlibShifted(z) at 0.
    Ξ is even (functional equation) and real on ℝ (conjugation), so
    Ξ(z) = Σ γₙ z^{2n}/(2n)! with γₙ ∈ ℝ. -/
noncomputable def taylorCoeff (n : ℕ) : ℝ :=
  ((Nat.factorial (2 * n) : ℝ)⁻¹) * (deriv^[2 * n] xiMathlibShifted 0).re

/-- Bridge: γₙ is the (2n)-th Taylor coefficient of the shifted xi function. -/
theorem taylorCoeff_eq (n : ℕ) :
    taylorCoeff n = ((Nat.factorial (2 * n) : ℝ)⁻¹) * (deriv^[2 * n] xiMathlibShifted 0).re := by
  rfl

/-- The Jensen polynomial of degree d and shift n, viewed over ℂ, in the
    Pólya–GORZ convention:
    J_{d,n}(x) = Σ_{k=0}^d binom(d,k) · γ_{n+k} · x^k.  (The binomial
    convention matters: the differentiation identity
    J'_{d+1,n} = (d+1)·J_{d,n+1} holds precisely in this convention,
    which yields Pólya's shift reduction below.) -/
noncomputable def jensenPoly (d n : ℕ) : Polynomial ℂ :=
  (Finset.sum (Finset.range (d + 1)) (fun k =>
    Polynomial.monomial k ((Nat.choose d k : ℝ) * taylorCoeff (n + k))))
    |>.map (algebraMap ℝ ℂ)

/-- A polynomial is hyperbolic if all its complex roots are real. -/
def Hyperbolic (p : Polynomial ℂ) : Prop :=
  ∀ x : ℂ, p.eval x = 0 → x.im = 0

/-- THE TRANSLATION.  RH ⟺ every Jensen polynomial of the shifted xi
    function is hyperbolic (Pólya–Schur; Griffin–Ono–Rolen–Zagier 2019). -/
theorem rh_iff_all_jensen_hyperbolic :
    RiemannHypothesisProp ↔ ∀ d n : ℕ, Hyperbolic (jensenPoly d n) := by
  sorry

/-- GORZ 2019: for each fixed degree d, all but finitely many Jensen
    polynomials are hyperbolic (unconditional). -/
theorem jensen_hyperbolic_eventually (d : ℕ) :
    ∀ᶠ n in atTop, Hyperbolic (jensenPoly d n) := by
  sorry

/-- Pure real-algebra fact (the tractable content): a real affine polynomial
    `a + b·X` that is not the zero polynomial has only real roots — the single
    root is `-a/b` when `b ≠ 0`, and there are no roots when `b = 0 ≠ a`. -/
theorem real_affine_hyperbolic {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) :
    Hyperbolic (Polynomial.map (algebraMap ℝ ℂ) (Polynomial.C a + Polynomial.monomial 1 b)) := by
  unfold Hyperbolic
  intro x hx
  have hx' : (a : ℂ) + (b : ℂ) * x = 0 := by
    simpa [Polynomial.eval_add, Polynomial.eval_monomial, Polynomial.map_add,
      Polynomial.map_monomial] using hx
  by_cases hb : b = 0
  · have : (a : ℂ) = 0 := by simpa [hb] using hx'
    have ha : a = 0 := by exact_mod_cast this
    exact False.elim ((h.resolve_left (by simpa [ha])) hb)
  · have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb
    have hx'' : x = -((a : ℂ) / (b : ℂ)) := by
      rw [eq_neg_iff_add_eq_zero]
      field_simp [hb']
      linear_combination hx'
    rw [hx'']
    simp

/-- A real quadratic `c + b·X + a·X²` with `a ≠ 0` and nonnegative
    discriminant is hyperbolic: its two roots are real.  Completes the
    d = 2 base case of the Jensen criterion. -/
theorem real_quadratic_hyperbolic_of_discriminant {a b c : ℝ} (ha : a ≠ 0)
    (hd : b ^ 2 ≥ 4 * a * c) :
    Hyperbolic (Polynomial.map (algebraMap ℝ ℂ)
      (Polynomial.C c + Polynomial.monomial 1 b + Polynomial.monomial 2 a)) := by
  unfold Hyperbolic
  intro x hx
  have hx' : (c : ℂ) + (b : ℂ) * x + (a : ℂ) * x ^ 2 = 0 := by
    simpa [Polynomial.eval_add, Polynomial.eval_monomial, Polynomial.map_add,
      Polynomial.map_monomial, pow_two] using hx
  let z : ℂ := 2 * (a : ℂ) * x + (b : ℂ)
  have hx'' : (a : ℂ) * x ^ 2 + (b : ℂ) * x + (c : ℂ) = 0 := by
    simpa [pow_two, add_assoc, add_comm, add_left_comm] using hx'
  have hz2 : z ^ 2 = ((b ^ 2 - 4 * a * c : ℝ) : ℂ) := by
    dsimp [z]
    have hlin : 4 * (a : ℂ) * ((a : ℂ) * x ^ 2 + (b : ℂ) * x + (c : ℂ)) = 0 := by
      rw [hx'']; ring
    have h0 : 4 * (a : ℂ) * (a : ℂ) * x ^ 2 + 4 * (a : ℂ) * (b : ℂ) * x + 4 * (a : ℂ) * (c : ℂ) = 0 := by
      calc 4 * (a : ℂ) * (a : ℂ) * x ^ 2 + 4 * (a : ℂ) * (b : ℂ) * x + 4 * (a : ℂ) * (c : ℂ)
          = 4 * (a : ℂ) * ((a : ℂ) * x ^ 2 + (b : ℂ) * x + (c : ℂ)) := by ring
        _ = 0 := hlin
    calc (2 * (a : ℂ) * x + (b : ℂ)) ^ 2
        = 4 * (a : ℂ) * (a : ℂ) * x ^ 2 + 4 * (a : ℂ) * (b : ℂ) * x + (b : ℂ) ^ 2 := by ring
      _ = (b : ℂ) ^ 2 - 4 * (a : ℂ) * (c : ℂ) := by
        calc 4 * (a : ℂ) * (a : ℂ) * x ^ 2 + 4 * (a : ℂ) * (b : ℂ) * x + (b : ℂ) ^ 2
            = 4 * (a : ℂ) * (a : ℂ) * x ^ 2 + 4 * (a : ℂ) * (b : ℂ) * x + 4 * (a : ℂ) * (c : ℂ) + (b : ℂ) ^ 2 - 4 * (a : ℂ) * (c : ℂ) := by ring
          _ = (b : ℂ) ^ 2 - 4 * (a : ℂ) * (c : ℂ) := by rw [h0]; ring
      _ = ((b ^ 2 - 4 * a * c : ℝ) : ℂ) := by push_cast; ring
  have hD : 0 ≤ b ^ 2 - 4 * a * c := by nlinarith
  -- z.im = 0 : z² is a nonnegative real, so z is real
  have hzim : z.im = 0 := by
    have him2 : (z ^ 2).im = 0 := by
      rw [hz2]
      exact Complex.ofReal_im (b ^ 2 - 4 * a * c)
    have hre2 : (z ^ 2).re = b ^ 2 - 4 * a * c := by
      rw [hz2]
      exact Complex.ofReal_re (b ^ 2 - 4 * a * c)
    have hre_sq : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by simp [pow_two, Complex.mul_re]
    have him_sq : (z ^ 2).im = 2 * z.re * z.im := by
      simp [pow_two, Complex.mul_im]
      ring
    have hmul0 : z.re * z.im = 0 := by
      have : 2 * z.re * z.im = 0 := by
        rw [← him_sq, him2]
      nlinarith
    by_cases hzi : z.im = 0
    · exact hzi
    · have hzr : z.re = 0 := (mul_eq_zero.mp hmul0).resolve_right hzi
      have hD' : 0 ≤ -z.im ^ 2 := by
        have : -z.im ^ 2 = b ^ 2 - 4 * a * c := by
          calc -z.im ^ 2 = z.re ^ 2 - z.im ^ 2 := by simp [hzr]
            _ = (z ^ 2).re := hre_sq.symm
            _ = b ^ 2 - 4 * a * c := hre2
        rw [this]
        exact hD
      have hzi2 : z.im ^ 2 ≤ 0 := by linarith
      have hzi' : z.im ^ 2 = 0 := le_antisymm hzi2 (sq_nonneg z.im)
      exact sq_eq_zero_iff.mp hzi'
  -- x = (z - b)/(2a) is the image of a real number
  have hxeq : x = (z - (b : ℂ)) / (2 * (a : ℂ)) := by
    have hden : 2 * (a : ℂ) ≠ 0 := by exact_mod_cast (mul_ne_zero (by norm_num) ha)
    dsimp [z]
    rw [eq_div_iff hden]
    ring
  have hzre : z = ((z.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hzim]
  rw [hxeq, hzre]
  have hnum : ((z.re : ℝ) : ℂ) - (b : ℂ) = ((z.re - b : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hdiv : ((z.re - b : ℝ) : ℂ) / (2 * (a : ℂ)) =
      (((z.re - b) / (2 * a) : ℝ) : ℂ) := by
    rw [Complex.ofReal_div]
    push_cast
    ring
  rw [hnum, hdiv]
  exact Complex.ofReal_im ((z.re - b) / (2 * a))

/-- Degree 1: J_{1,n}(x) = γₙ + (1/2)γₙ₊₁ x is a real linear polynomial;
    if it is not the zero polynomial, its single root is real, hence it is
    hyperbolic.  PROVED — this is the first genuine step in the translated
    branch: the d = 1 case of the Jensen criterion is real algebra, not
    analysis. -/
theorem jensen_degree_one_hyperbolic (n : ℕ)
    (h : taylorCoeff n ≠ 0 ∨ taylorCoeff (n + 1) ≠ 0) :
    Hyperbolic (jensenPoly 1 n) := by
  have hp : jensenPoly 1 n =
      Polynomial.map (algebraMap ℝ ℂ)
        (Polynomial.C (taylorCoeff n) + Polynomial.monomial 1 (taylorCoeff (n + 1))) := by
    simp [jensenPoly, Finset.sum_range_succ, Nat.choose]
  rw [hp]
  exact real_affine_hyperbolic (by
    rcases h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr h1)

/-- Degree 2, criterion direction: if the higher Turán inequality
    γₙ₊₁² ≥ γₙ γₙ₊₂ holds (and the leading coefficient γₙ₊₂ ≠ 0), then
    J_{2,n}(x) = γₙ + 2γₙ₊₁ x + γₙ₊₂ x² is hyperbolic, i.e. its discriminant
    (2γₙ₊₁)² - 4 γₙ γₙ₊₂ = 4(γₙ₊₁² - γₙ γₙ₊₂) is nonnegative.  This is the
    d = 2 case of the higher Turán inequalities.

    (The converse direction is also true once one rules out the
    zero-polynomial edge case; the literal `↔` is false when
    γₙ = γₙ₊₁ = γₙ₊₂ = 0, since then the zero polynomial is not hyperbolic
    while the inequality 0 ≥ 0 holds.) -/
theorem jensen_degree_two_hyperbolic_of_ineq (n : ℕ) (ha : taylorCoeff (n + 2) ≠ 0)
    (h : taylorCoeff (n + 1) ^ 2 ≥ taylorCoeff n * taylorCoeff (n + 2)) :
    Hyperbolic (jensenPoly 2 n) := by
  rw [jensenPoly, Finset.sum_range_succ, Finset.sum_range_succ, Finset.range_one,
    Finset.sum_singleton]
  rw [Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self]
  simp only [Nat.cast_one, one_mul]
  rw [Polynomial.monomial_zero_left]
  have hd : (2 * taylorCoeff (n + 1)) ^ 2 ≥ 4 * taylorCoeff (n + 2) * taylorCoeff n := by
    calc (2 * taylorCoeff (n + 1)) ^ 2 = 4 * taylorCoeff (n + 1) ^ 2 := by ring
      _ ≥ 4 * (taylorCoeff n * taylorCoeff (n + 2)) :=
        mul_le_mul_of_nonneg_left h.le (by norm_num : (0 : ℝ) ≤ 4)
      _ = 4 * taylorCoeff (n + 2) * taylorCoeff n :=
        by rw [mul_comm (taylorCoeff n) (taylorCoeff (n + 2)), ← mul_assoc (4 : ℝ)]
  exact real_quadratic_hyperbolic_of_discriminant ha hd

/-- Pure binomial identity: `(k+1)·C(d+1,k+1) = (d+1)·C(d,k)` (cast to ℝ). -/
lemma hbin (d k : ℕ) :
    (↑(Nat.choose (d + 1) (k + 1)) : ℝ) * ↑(k + 1) = ↑(d + 1) * ↑(Nat.choose d k) := by
  rw [← Nat.cast_mul, ← Nat.add_one_mul_choose_eq d k, Nat.cast_mul]

/-- Pure algebraic identity: derivative of J_{d+1,n} equals (d+1)·J_{d,n+1} (over ℝ). -/
theorem derivative_q_eq (d n : ℕ) :
    (Polynomial.derivative
        (Finset.sum (Finset.range (d + 2)) (fun k =>
          Polynomial.monomial k (↑(Nat.choose (d + 1) k) * taylorCoeff (n + k)))) :
        Polynomial ℝ) =
      Polynomial.C ((d + 1 : ℕ) : ℝ) *
        (Finset.sum (Finset.range (d + 1)) (fun k =>
          Polynomial.monomial k (↑(Nat.choose d k) * taylorCoeff (n + 1 + k)))) := by
  apply Polynomial.ext
  intro m
  rw [Polynomial.coeff_derivative, Polynomial.coeff_C_mul,
      Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_monomial]
  by_cases hm : m ≤ d
  · have h1 : m + 1 ∈ Finset.range (d + 2) := by simp; omega
    have h2 : m ∈ Finset.range (d + 1) := by simp; omega
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos h1, if_pos h2]
    rw [← Nat.cast_add_one, mul_assoc, mul_comm (taylorCoeff (n + (m + 1))) (↑(m + 1)),
        ← mul_assoc, hbin d m, mul_assoc, add_comm m 1, Nat.add_assoc]
  · have h1 : ¬ m + 1 ∈ Finset.range (d + 2) := by simp; omega
    have h2 : ¬ m ∈ Finset.range (d + 1) := by simp; omega
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq', if_neg h1, if_neg h2]
    simp

/-- Differentiation identity for Jensen polynomials (Pólya–GORZ convention):
    J'_{d+1,n} = (d+1)·J_{d,n+1}.  Proof: (k+1)·C(d+1,k+1) = (d+1)·C(d,k),
    a pure binomial identity, plus Polynomial.derivative_monomial.
    We work in `Polynomial ℝ` and then map to `ℂ`. -/
theorem jensenPoly_derivative (d n : ℕ) :
    (jensenPoly (d + 1) n).derivative =
      Polynomial.C ((d + 1 : ℕ) : ℂ) * jensenPoly d (n + 1) := by
  let φ : ℝ →+* ℂ := algebraMap ℝ ℂ
  let Q := Finset.sum (Finset.range (d + 2))
    (fun k => Polynomial.monomial k (↑(Nat.choose (d + 1) k) * taylorCoeff (n + k)))
  let P := Finset.sum (Finset.range (d + 1))
    (fun k => Polynomial.monomial k (↑(Nat.choose d k) * taylorCoeff (n + 1 + k)))
  have hQ : Q.map φ = jensenPoly (d + 1) n := rfl
  have hP : P.map φ = jensenPoly d (n + 1) := rfl
  rw [← hQ, ← hP, Polynomial.derivative_map Q φ, derivative_q_eq d n,
      Polynomial.map_mul, Polynomial.map_C, hP]
  simp

/-- Coefficient formula for Jensen polynomials. -/
theorem jensenPoly_coeff (d n k : ℕ) :
    ((jensenPoly d n).coeff k : ℂ) =
      if k ≤ d then ((Nat.choose d k : ℝ) * taylorCoeff (n + k) : ℝ) else 0 := by
  have key : (Finset.sum (Finset.range (d + 1)) (fun j =>
      Polynomial.monomial j ((Nat.choose d j : ℝ) * taylorCoeff (n + j)))).coeff k
      = if k ≤ d then ((Nat.choose d k : ℝ) * taylorCoeff (n + k)) else 0 := by
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range,
      Nat.lt_succ_iff]
  simp only [jensenPoly, Polynomial.coeff_map, key]
  by_cases hk : k ≤ d <;> simp [hk]

/-- Cancelling a constant factor preserves hyperbolicity:
    if `Hyperbolic (C c * p)` and `c ≠ 0`, then `Hyperbolic p`. -/
theorem Hyperbolic_of_const_mul (c : ℂ) (hc : c ≠ 0) {p : Polynomial ℂ}
    (hp : Hyperbolic (Polynomial.C c * p)) : Hyperbolic p := by
  intro x hx
  refine hp x ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, hx, mul_zero]

/-- Scaling by a nonzero constant preserves hyperbolicity (forward direction).
    Classical: the Laguerre–Pólya class is closed under nonzero scaling.
    Feeds the Pólya shift-reduction (`jensenPoly_derivative` produces a
    `C (d+1) * J` factor that must be cancelled/introduced). -/
theorem Hyperbolic_const_mul {c : ℂ} (hc : c ≠ 0) {p : Polynomial ℂ}
    (hp : Hyperbolic p) : Hyperbolic (Polynomial.C c * p) := by
  intro x hx
  have h' : Polynomial.eval x p = 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_C] at hx
    exact (mul_eq_zero.mp hx).resolve_left hc
  exact hp x h'

/-- The product of two hyperbolic polynomials is hyperbolic.
    Classical: the Laguerre–Pólya class is closed under multiplication.
    Proof: `(p*q).eval x = 0` implies `p.eval x = 0` or `q.eval x = 0`; in either
    case `x.im = 0`. -/
theorem Hyperbolic_mul {p q : Polynomial ℂ} (hp : Hyperbolic p) (hq : Hyperbolic q) :
    Hyperbolic (p * q) := by
  intro x hx
  have : p.eval x = 0 ∨ q.eval x = 0 := by
    have h := hx
    rw [Polynomial.eval_mul] at h
    exact (mul_eq_zero.mp h)
  rcases this with hp0 | hq0
  · exact hp x hp0
  · exact hq x hq0

/-- Degree-0 Jensen section: `J_{0,n} = C (γₙ)`.
    Hence `Hyperbolic (jensenPoly 0 n) ↔ taylorCoeff n ≠ 0`
    (constant nonzero polynomials are vacuously hyperbolic; the zero
    polynomial is not). -/
theorem jensenPoly_zero (n : ℕ) :
    jensenPoly 0 n = Polynomial.C ((taylorCoeff n : ℝ) : ℂ) := by
  simp only [jensenPoly]
  rw [Finset.range_one, Finset.sum_singleton, Nat.choose_zero_right, Nat.cast_one,
    one_mul, Polynomial.monomial_zero_left, Polynomial.map_C]
  simp

/-- If all Taylor coefficients are nonzero, every `jensenPoly d n` has degree `d`. -/
theorem jensenPoly_natDegree (hC : ∀ k, taylorCoeff k ≠ 0) (d n : ℕ) :
    (jensenPoly d n).natDegree = d := by
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [jensenPoly_coeff d n m, if_neg (not_le.mpr hm)]
    simp
  · refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [jensenPoly_coeff d n d, if_pos (le_refl d)]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, ne_eq, Complex.ofReal_eq_zero]
    exact hC (n + d)
/-- A sum of a multiset of nonnegative reals is nonnegative. -/
lemma msum_nonneg {M : Multiset ℝ} (h : ∀ x ∈ M, 0 ≤ x) : 0 ≤ M.sum := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    rw [Multiset.sum_cons]
    have ha : 0 ≤ a := h a (Multiset.mem_cons_self a M)
    have hM : 0 ≤ M.sum := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    linarith

/-- A nonempty sum of positive reals is positive. -/
lemma msum_pos {M : Multiset ℝ} (h : ∀ x ∈ M, 0 < x) (hn : M ≠ 0) : 0 < M.sum := by
  induction M using Multiset.induction_on with
  | empty => exact absurd rfl hn
  | cons a M ih =>
      rw [Multiset.sum_cons]
      have ha : 0 < a := h a (Multiset.mem_cons_self a M)
      have hM : 0 ≤ M.sum :=
        msum_nonneg (fun x hx => le_of_lt (h x (Multiset.mem_cons_of_mem hx)))
      linarith

/-- Logarithmic-derivative identity for a product of linear factors over ℂ:
     for `w` distinct from all roots `r`, `(∏ (X - r))'(w) = (∏ (X - r))(w)·Σ (w-r)⁻¹`. -/
lemma deriv_prod_identity (M : Multiset ℂ) (w : ℂ)
    (hne : ∀ r ∈ M, w ≠ r) :
    (Polynomial.derivative ((M.map fun r => Polynomial.X - Polynomial.C r).prod)).eval w =
      (M.map fun r => Polynomial.X - Polynomial.C r).prod.eval w *
        (M.map fun r => (w - r)⁻¹).sum := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
      have hane : w ≠ a := hne a (Multiset.mem_cons_self a M)
      have hsub : (w - a) ≠ 0 := sub_ne_zero.mpr hane
      have ihM := ih (fun r hr => hne r (Multiset.mem_cons_of_mem hr))
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons,
        Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
        Polynomial.derivative_C, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, sub_zero, one_mul]
      rw [ihM]
      field_simp

/-- Imaginary part of the sum of reciprocals `(w - r)⁻¹` over real roots `r`:
     it equals `-w.im` times the sum of `‖w - r‖⁻²`. -/
lemma sum_im_inv (w : ℂ) (M : Multiset ℂ)
    (hre : ∀ r ∈ M, r.im = 0) (hne : ∀ r ∈ M, w ≠ r) :
    ((M.map fun r => (w - r)⁻¹).sum).im =
      -w.im * (M.map fun r => (normSq (w - r))⁻¹).sum := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
      have hane : w ≠ a := hne a (Multiset.mem_cons_self a M)
      have hare : a.im = 0 := hre a (Multiset.mem_cons_self a M)
      have ihM := ih (fun r hr => hre r (Multiset.mem_cons_of_mem hr))
        (fun r hr => hne r (Multiset.mem_cons_of_mem hr))
      rw [Multiset.map_cons, Multiset.sum_cons, Complex.add_im, ihM, Multiset.map_cons,
        Multiset.sum_cons]
      rw [Complex.inv_im]
      have hsubim : (w - a).im = w.im := by simp [Complex.sub_im, hare]
      rw [hsubim]
      field_simp
      ring

/-- **Gauss–Lucas for hyperbolic polynomials**: the derivative of a hyperbolic
polynomial of positive degree is hyperbolic.  If `p'(w) = 0` with `w.im ≠ 0`, then `w`
is not a root of `p` (all roots of `p` are real), so `Σ_ρ (w - ρ)⁻¹ = p'(w)/p(w) = 0`;
taking imaginary parts gives `w.im · Σ_ρ ‖w - ρ‖⁻² = 0` with a strictly positive sum. -/
theorem derivative_hyperbolic {p : Polynomial ℂ} (hp : Hyperbolic p)
    (hdeg : 0 < Polynomial.natDegree p) : Hyperbolic p.derivative := by
  intro w hw
  by_contra hwim
  have hp0 : p ≠ 0 := by
    intro h; rw [h] at hdeg; simp at hdeg
  have hsplit : Polynomial.Splits p := IsAlgClosed.splits p
  have hcard : p.roots.card = p.natDegree := Polynomial.splits_iff_card_roots.mp hsplit
  have hrootsne : p.roots ≠ 0 := by
    intro h
    rw [h] at hcard
    simp at hcard
    omega
  have hrootre : ∀ r ∈ p.roots, r.im = 0 := fun r hr =>
    hp r (Polynomial.isRoot_of_mem_roots hr)
  have hwne : ∀ r ∈ p.roots, w ≠ r := by
    intro r hr h
    exact hwim (h ▸ hrootre r hr)
  have hfac : p = Polynomial.C p.leadingCoeff *
      (p.roots.map fun a => Polynomial.X - Polynomial.C a).prod :=
    hsplit.eq_prod_roots
  have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hPeval : ((p.roots.map fun a => Polynomial.X - Polynomial.C a).prod).eval w ≠ 0 := by
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    apply Multiset.prod_ne_zero
    intro hmem
    rw [Multiset.mem_map] at hmem
    obtain ⟨r, hr, hz⟩ := hmem
    simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at hz
    exact hwne r hr (sub_eq_zero.mp hz)
  have hderiv : Polynomial.derivative p = Polynomial.C p.leadingCoeff *
      Polynomial.derivative ((p.roots.map fun a => Polynomial.X - Polynomial.C a).prod) := by
    conv_lhs => rw [hfac]
    rw [Polynomial.derivative_C_mul]
  have hzero : p.leadingCoeff *
      (((p.roots.map fun a => Polynomial.X - Polynomial.C a).prod).eval w *
        (p.roots.map fun r => (w - r)⁻¹).sum) = 0 := by
    have h := hw
    rw [hderiv, Polynomial.eval_mul, Polynomial.eval_C,
      deriv_prod_identity p.roots w hwne] at h
    exact h
  have hS : (p.roots.map fun r => (w - r)⁻¹).sum = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h hlc
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hPeval
      · exact h'
  have hSim : ((p.roots.map fun r => (w - r)⁻¹).sum).im = 0 := by rw [hS]; simp
  rw [sum_im_inv w p.roots hrootre hwne] at hSim
  have hpos : 0 < (p.roots.map fun r => (normSq (w - r))⁻¹).sum := by
    apply msum_pos
    · intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      have hne0 : w - r ≠ 0 := sub_ne_zero.mpr (hwne r hr)
      exact inv_pos.mpr (Complex.normSq_pos.mpr hne0)
    · simpa [Multiset.map_eq_zero] using hrootsne
  have hwim0 : w.im = 0 := by
    rcases mul_eq_zero.mp hSim with h | h
    · linarith [neg_eq_zero.mp h]
    · linarith
  exact hwim hwim0

/-- **Hermite–Poulain lemma**: for a hyperbolic polynomial `P` of positive degree
    and a real constant `a`, the polynomial `P + a·P'` is hyperbolic.

    This is the fundamental real-rootedness-preserving operator. It is the
    mechanism behind the Pólya direction of the Jensen criterion: the Jensen
    differential identity `J'_{d+1,n} = (d+1)·J_{d,n+1}` shows that the Jensen
    sections are obtained from one another by exactly this class of operators,
    so hyperbolicity propagates. Classical (Hermite, Poulain, 19th century).

    Proof: if `(P + a·P')(w) = 0` with `w.im ≠ 0`, then `P(w) ≠ 0` (all roots of `P`
    are real), so `P'(w)/P(w) = -1/a` (real when `a ≠ 0`). But for a hyperbolic `P`,
    `P'(w)/P(w) = Σ (w - r)⁻¹` over real roots `r`; its imaginary part is
    `-w.im · Σ ‖w - r‖⁻² ≠ 0`, contradiction. (The `a = 0` case is Gauss–Lucas.) -/
theorem hyperbolic_add_smul_derivative {P : Polynomial ℂ} (hp : Hyperbolic P)
    (hdeg : 0 < P.natDegree) (a : ℝ) :
    Hyperbolic (P + Polynomial.C (a : ℂ) * P.derivative) := by
  intro w hw
  by_cases ha : a = 0
  · subst ha
    simp only [Complex.ofReal_zero, Polynomial.C_0, zero_mul, add_zero] at hw
    exact hp w hw
  · by_contra hwim
    have hp0 : P ≠ 0 := by
      intro h; rw [h, Polynomial.natDegree_zero] at hdeg; exact (lt_irrefl 0).elim hdeg
    have hsplit : Polynomial.Splits P := IsAlgClosed.splits P
    have hcard : P.roots.card = P.natDegree := Polynomial.splits_iff_card_roots.mp hsplit
    have hrootsne : P.roots ≠ 0 := by
      intro h; rw [h] at hcard; simp at hcard; omega
    have hrootre : ∀ r ∈ P.roots, r.im = 0 := fun r hr =>
      hp r (Polynomial.isRoot_of_mem_roots hr)
    have hwne : ∀ r ∈ P.roots, w ≠ r := by
      intro r hr h; exact hwim (h ▸ hrootre r hr)
    have hfac : P = Polynomial.C P.leadingCoeff *
        (P.roots.map fun r => Polynomial.X - Polynomial.C r).prod :=
      hsplit.eq_prod_roots
    have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
    have hlc' : (P.leadingCoeff : ℂ) ≠ 0 := by exact_mod_cast hlc
    have hQeval :
        (P.roots.map fun r => Polynomial.X - Polynomial.C r).prod.eval w ≠ 0 := by
      rw [Polynomial.eval_multiset_prod, Multiset.map_map]
      apply Multiset.prod_ne_zero
      intro hmem
      rw [Multiset.mem_map] at hmem
      obtain ⟨r, hr, hz⟩ := hmem
      simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C] at hz
      exact hwne r hr (sub_eq_zero.mp hz)
    have heval : (Polynomial.C (a : ℂ) * P.derivative).eval w = - P.eval w := by
      have h1 := hw
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at h1
      rw [Polynomial.eval_mul, Polynomial.eval_C]
      rw [← add_eq_zero_iff_eq_neg]
      rw [add_comm]
      exact h1
    have hPne : P.eval w ≠ 0 := by
      intro hP0
      have h1' : P.eval w = (P.leadingCoeff : ℂ) *
          (P.roots.map fun r => Polynomial.X - Polynomial.C r).prod.eval w := by
        conv_lhs => rw [hfac]
        rw [Polynomial.eval_mul, Polynomial.eval_C]
      have : (P.roots.map fun r => Polynomial.X - Polynomial.C r).prod.eval w = 0 := by
        calc (P.roots.map fun r => Polynomial.X - Polynomial.C r).prod.eval w
            = (P.leadingCoeff : ℂ)⁻¹ * P.eval w := by
              rw [h1']
              field_simp [hlc']
          _ = (P.leadingCoeff : ℂ)⁻¹ * 0 := by rw [hP0]
          _ = 0 := by simp
      exact hQeval this
    have hquot : P.derivative.eval w / P.eval w = -1 / (a : ℂ) := by
      have hd : (a : ℂ) ≠ 0 := by exact_mod_cast ha
      have hP0 : P.eval w ≠ 0 := hPne
      rw [div_eq_div_iff hP0 hd]
      field_simp [hd]
      have h := heval
      rw [Polynomial.eval_mul, Polynomial.eval_C] at h
      linear_combination h
    have hderiv : P.derivative = Polynomial.C P.leadingCoeff *
        (P.roots.map fun r => Polynomial.X - Polynomial.C r).prod.derivative := by
      conv_lhs => rw [hfac]
      rw [Polynomial.derivative_C_mul]
    have hsum : (P.roots.map fun r => (w - r)⁻¹).sum = -1 / (a : ℂ) := by
      have h1 := deriv_prod_identity P.roots w hwne
      have hsum_mul : P.derivative.eval w = P.eval w * (P.roots.map fun r => (w - r)⁻¹).sum := by
        let lc := (P.leadingCoeff : ℂ)
        let q := (P.roots.map fun r => Polynomial.X - Polynomial.C r).prod.eval w
        let qd := (P.roots.map fun r => Polynomial.X - Polynomial.C r).prod.derivative.eval w
        let σ := (P.roots.map fun r => (w - r)⁻¹).sum
        have hP'_eval : P.derivative.eval w = lc * qd := by
          rw [hderiv, Polynomial.eval_mul, Polynomial.eval_C]
        have hP_eval : P.eval w = lc * q := by
          rw [hfac, Polynomial.eval_mul, Polynomial.eval_C]
        have h1opaque : qd = q * σ := h1
        rw [hP'_eval, h1opaque, ← mul_assoc, ← hP_eval]
      have hP0 : P.eval w ≠ 0 := hPne
      have hsum_div : (P.roots.map fun r => (w - r)⁻¹).sum = P.derivative.eval w / P.eval w := by
        have hsum_mul_eq : P.derivative.eval w = P.eval w * (P.roots.map fun r => (w - r)⁻¹).sum := hsum_mul
        have : (P.roots.map fun r => (w - r)⁻¹).sum * P.eval w = P.derivative.eval w := by
          rw [hsum_mul_eq]
          ring
        exact (eq_div_iff_mul_eq hP0).mpr this
      rw [hsum_div, hquot]
    have hSim : ((P.roots.map fun r => (w - r)⁻¹).sum).im = 0 := by
      rw [hsum]
      simp
    have hSim' : ((P.roots.map fun r => (w - r)⁻¹).sum).im =
        -w.im * (P.roots.map fun r => (normSq (w - r))⁻¹).sum := by
      exact sum_im_inv w P.roots hrootre hwne
    have hpos : 0 < (P.roots.map fun r => (normSq (w - r))⁻¹).sum := by
      apply msum_pos
      · intro x hx
        rw [Multiset.mem_map] at hx
        obtain ⟨r, hr, rfl⟩ := hx
        have hne0 : w - r ≠ 0 := sub_ne_zero.mpr (hwne r hr)
        exact inv_pos.mpr (Complex.normSq_pos.mpr hne0)
      · simpa [Multiset.map_eq_zero] using hrootsne
    have hwim0 : w.im = 0 := by
      rw [hSim'] at hSim
      have : -w.im * (P.roots.map fun r => (normSq (w - r))⁻¹).sum = 0 := by
        linarith
      rcases mul_eq_zero.mp this with h | h
      · exact neg_eq_zero.mp h
      · linarith
    exact hwim hwim0

/-- **Conditional shift reduction** (Pólya–GORZ algebraic mechanism): under the
    non-degeneracy hypothesis `hC : ∀ k, taylorCoeff k ≠ 0` (all Taylor coefficients
    of Ξ nonzero, so every `jensenPoly d n` has full degree `d`), hyperbolicity
    propagates from shift 0 to all shifts:
    `(∀ d, Hyperbolic (jensenPoly d 0)) → (∀ d n, Hyperbolic (jensenPoly d n))`.

    Proof: `J_{d,n}` is a nonzero scalar multiple of the `n`-th derivative of
    `J_{d+n,0}` (by iterating `jensenPoly_derivative`), and `derivative_hyperbolic`
    shows differentiation preserves hyperbolicity.  This is the algebraic heart of
    the Pólya direction of the Jensen criterion.  The non-degeneracy hypothesis is
    necessary: if some `γ_k = 0` the degree drops and the Gauss–Lucas step fails. -/
theorem all_shifts_from_zero_of_nonvanishing (hC : ∀ k, taylorCoeff k ≠ 0)
    (h0 : ∀ d, Hyperbolic (jensenPoly d 0)) : ∀ d n, Hyperbolic (jensenPoly d n) := by
  intro d n
  induction n generalizing d with
  | zero => exact h0 d
  | succ n ih =>
    have hd := ih (d + 1)
    have hdeg : 0 < (jensenPoly (d + 1) n).natDegree := by
      rw [jensenPoly_natDegree hC (d + 1) n]
      norm_num
    have hder := derivative_hyperbolic hd hdeg
    rw [jensenPoly_derivative d n] at hder
    exact Hyperbolic_of_const_mul ((d + 1 : ℕ) : ℂ)
      (by exact_mod_cast (Nat.succ_ne_zero d)) hder

/-- OUT OF SCOPE (left as the open translation).  The genuine content is the
    Gauss–Lucas step: `jensenPoly d n` is a nonzero scalar multiple of the
    `n`-th derivative of `jensenPoly (d+n) 0` (by iterating `jensenPoly_derivative`),
    and `derivative_hyperbolic` shows differentiation preserves hyperbolicity.
    Concretely one would prove
        `Hyperbolic (jensenPoly (d+n) 0) → Hyperbolic (jensenPoly d n)`
    under the non-degeneracy hypothesis `n ≤ natDegree (jensenPoly (d+n) 0)`;
    this needs the base polynomials to have full degree, which is *not* derivable
    from the present root infrastructure and is itself part of the open
    RH/Jensen equivalence.  (E.g. if γ₀ = 1 and γ_k = 0 for k ≥ 1 then every
    `J_{d,0}` is the constant 1 — hyperbolic — yet every `J_{d,n}` with n ≥ 1 is
    the zero polynomial, which is not hyperbolic.)  Hence the unconditional
    statement cannot be proved here and is left as an RH-equivalent placeholder at line 483. -/
theorem all_shifts_from_zero (h0 : ∀ d : ℕ, Hyperbolic (jensenPoly d 0)) :
    ∀ d n : ℕ, Hyperbolic (jensenPoly d n) := by
  sorry

/-- OUT OF SCOPE (left as the open translation).  This is exactly the
    Jensen/GORZ characterization of RH: Ξ belongs to the Laguerre–Pólya class
    (all its zeros real) iff every Jensen polynomial is hyperbolic, i.e.
    `RiemannHypothesisProp ↔ ∀ d, Hyperbolic (jensenPoly d 0)`.  It is
    *equivalent* to RH and its proof requires the deep analysis connecting the
    zeros of the shifted xi function to hyperbolicity of the Jensen
    polynomials — material that is not present in the root infrastructure
    (which only defines `jensenPoly`, `Hyperbolic`, and the `rh_iff_*` engines
    that reduce RH to zero-free rectangles).  It is therefore left as an RH-equivalent placeholder at line 462. -/
theorem rh_iff_jensen_zero :
    RiemannHypothesisProp ↔ ∀ d : ℕ, Hyperbolic (jensenPoly d 0) := by
  sorry

/-- The open leaf of `riemann hypothesis.lean` — tail nonvanishing of the
    shifted xi function — is, by the translation, the same statement as
    universal Jensen hyperbolicity. -/
theorem tail_nonvanishing_iff_jensen :
    (∀ z : ℂ, 10 < |z.re| → -(1 / 2 : ℝ) < z.im → z.im < (1 / 2 : ℝ) →
      z.im ≠ 0 → xiShifted z ≠ 0)
      ↔ ∀ d n : ℕ, Hyperbolic (jensenPoly d n) := by
  sorry

/-- Unconditional bridge identity: `taylorCoeff 0` is the real part of the
    completed zeta value at `1/2`. This isolates the analytic content of
    `taylorCoeff_zero_ne_zero` to a single transcendental nonvanishing fact,
    fed by `zeta_rigorous.eta_half_pos` (Tendsto form) via
    `completedRiemannZeta = Gammaℝ * riemannZeta` and
    `completedRiemannZeta₀ = completedRiemannZeta + 1/s + 1/(1-s)`. -/
theorem taylorCoeff_zero_eq :
    taylorCoeff 0 = (completedRiemannZeta₀ (1/2 : ℂ)).re := by
  simp [taylorCoeff, xiMathlibShifted, xiMathlib]

/-- The 0-th Taylor coefficient of the shifted xi function is nonzero.
    `taylorCoeff 0 = (completedRiemannZeta₀ (1/2)).re`, and since
    `completedRiemannZeta₀ (1/2) = π^(-1/4) * Γ(1/4) * ζ(1/2) < 0`,
    this is nonzero. -/
lemma taylorCoeff_zero_ne_zero : taylorCoeff 0 ≠ 0 := by
  simp [taylorCoeff, xiMathlibShifted, xiMathlib]
  -- Goal: ¬(completedRiemannZeta₀ (1 / 2)).re = 0
  -- This is a transcendental constant. The claim is that
  -- completedRiemannZeta₀ (1/2) = π^(-1/4) * Γ(1/4) * ζ(1/2) < 0,
  -- so its real part is nonzero. Proving this requires numerical
  -- bounds on ζ(1/2) that are not available in Mathlib.
  unfold completedRiemannZeta₀
  -- Goal: ¬(HurwitzZeta.completedHurwitzZetaEven₀ 0 2⁻¹).re = 0
  sorry

/-! ## Quantitative Gamma / π intervals for `taylorCoeff_zero_ne_zero`.

The 0-th coefficient is `(completedRiemannZeta₀ (1/2)).re = (Λ(1/2)+4).re`
with `Λ(1/2) = Gammaℝ(1/2)·ζ(1/2)` and `Gammaℝ(1/2) = π^(-1/4)·Γ(1/4)`.
Since `Λ(1/2) ≈ -3.97`, separating `Λ(1/2)+4 ≈ 0.023` from 0 needs
two-sided bounds on the eta limit L (see `zeta_rigorous`: `S₂ ≤ L ≤ S₃ ≤ 1`)
plus tight intervals on `Γ(1/4)` and `π^(-1/4)`. The lemmas below are the
rigorous, unconditional part of that program (no `sorry`); the remaining gap
is documented after them.
-/

/-- Real Gamma at 1/4 is positive. -/
theorem gamma_quarter_pos : 0 < Real.Gamma (1/4 : ℝ) :=
  Real.Gamma_pos_of_pos (by norm_num)

/-- Gamma(5/4) ≤ 1 via convexity of Gamma on (0,∞) with Gamma(1)=Gamma(2)=1.
`5/4 = (3/4)·1 + (1/4)·2`. -/
theorem gamma_five_quarter_le_one : Real.Gamma (5/4 : ℝ) ≤ 1 := by
  have hconv := Real.convexOn_Gamma
  have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have h2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have h := hconv.2 h1 h2 (show (0 : ℝ) ≤ 3/4 by norm_num)
    (show (0 : ℝ) ≤ 1/4 by norm_num) (by norm_num)
  rw [Real.Gamma_one, Real.Gamma_two] at h
  simp only [smul_eq_mul] at h
  have h54 : (3/4 : ℝ) * 1 + (1/4 : ℝ) * 2 = 5/4 := by ring
  rw [h54] at h
  have h1' : (3/4 : ℝ) * 1 + (1/4 : ℝ) * 1 = (1 : ℝ) := by ring
  rw [h1'] at h
  exact h

/-- Gamma(1/4) ≤ 4 via `Gamma(5/4) = (1/4)·Gamma(1/4)`. -/
theorem gamma_quarter_le_four : Real.Gamma (1/4 : ℝ) ≤ 4 := by
  have h5 := gamma_five_quarter_le_one
  have hadd : Real.Gamma (5/4 : ℝ) = (1/4 : ℝ) * Real.Gamma (1/4 : ℝ) := by
    have h := Real.Gamma_add_one (show (1/4 : ℝ) ≠ 0 by norm_num)
    have h54 : ((1/4 : ℝ) + 1) = (5/4 : ℝ) := by ring
    rw [h54] at h
    -- h : Gamma(5/4) = 1/4 * Gamma(1/4); Lean has `1/4 * Gamma` vs `(1/4) * Gamma`
    exact h
  rw [hadd] at h5
  linarith

/-- The archimedean factor `π^(-1/4)` is positive. -/
theorem pi_rpow_neg_quarter_pos : 0 < Real.pi ^ (-(1/4) : ℝ) :=
  Real.rpow_pos_of_pos Real.pi_pos _

/-- The archimedean factor `π^(-1/4)` is < 1 (since π > 1, exponent negative). -/
theorem pi_rpow_neg_quarter_lt_one : Real.pi ^ (-(1/4) : ℝ) < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · linarith [Real.pi_gt_three]
  · norm_num

/-- `Gammaℝ(1/2)` as a real number: `π^(-1/4)·Γ(1/4)`. -/
theorem Gammaℝ_half_eq_real :
    Complex.Gammaℝ (1/2 : ℂ)
      = ((Real.Gamma (1/4 : ℝ) * Real.pi ^ (-(1/4) : ℝ) : ℝ) : ℂ) := by
  rw [Complex.Gammaℝ_def]
  have hs1 : (-(1/2 : ℂ) / 2) = (((-(1/4) : ℝ)) : ℂ) := by
    push_cast
    ring
  have hs2 : ((1/2 : ℂ) / 2) = (((1/4) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hs1, hs2, Complex.Gamma_ofReal,
    ← Complex.ofReal_cpow Real.pi_pos.le (-(1/4) : ℝ)]
  rw [mul_comm ((Real.pi ^ (-(1/4) : ℝ) : ℝ) : ℂ) _]
  rw [← Complex.ofReal_mul]

/-- `Gammaℝ(1/2)` has positive real part. -/
theorem Gammaℝ_half_re_pos : 0 < (Complex.Gammaℝ (1/2 : ℂ)).re := by
  rw [Gammaℝ_half_eq_real]
  simp only [Complex.ofReal_re]
  exact mul_pos gamma_quarter_pos pi_rpow_neg_quarter_pos

/-- `Gammaℝ(1/2)` is nonzero. -/
theorem Gammaℝ_half_ne_zero : Complex.Gammaℝ (1/2 : ℂ) ≠ 0 := by
  have h := Gammaℝ_half_re_pos
  intro hz
  rw [hz] at h
  simp at h

/-- Crude rigorous upper bound: `(Gammaℝ(1/2)).re ≤ 4`. -/
theorem Gammaℝ_half_re_le_four : (Complex.Gammaℝ (1/2 : ℂ)).re ≤ 4 := by
  rw [Gammaℝ_half_eq_real]
  simp only [Complex.ofReal_re]
  calc Real.Gamma (1/4 : ℝ) * Real.pi ^ (-(1/4) : ℝ)
      ≤ 4 * 1 := by
        apply mul_le_mul gamma_quarter_le_four pi_rpow_neg_quarter_lt_one.le
        · exact le_of_lt pi_rpow_neg_quarter_pos
        · norm_num
    _ = 4 := by ring

/-- Bridge: `Λ₀(1/2) = Λ(1/2) + 4` (the two polar terms are each 2). -/
theorem completedRiemannZeta₀_half_eq :
    completedRiemannZeta (1/2 : ℂ) + 4 = completedRiemannZeta₀ (1/2 : ℂ) := by
  have h := completedRiemannZeta_eq (1/2 : ℂ)
  have h1 : (1 : ℂ) / (1/2 : ℂ) = 2 := by norm_num
  have h2 : (1 : ℂ) / (1 - (1/2 : ℂ)) = 2 := by norm_num
  rw [h1, h2] at h
  linear_combination h

/-- Bridge: `Λ(1/2) = ζ(1/2)·Gammaℝ(1/2)`. -/
theorem completedRiemannZeta_half_eq :
    completedRiemannZeta (1/2 : ℂ)
      = riemannZeta (1/2 : ℂ) * Complex.Gammaℝ (1/2 : ℂ) := by
  have h := riemannZeta_def_of_ne_zero (show (1/2 : ℂ) ≠ 0 by norm_num)
  have hG := Gammaℝ_half_ne_zero
  rw [h]
  field_simp

/-- Combined bridge: `Λ₀(1/2) = ζ(1/2)·Gammaℝ(1/2) + 4`. -/
theorem completedRiemannZeta₀_half_eq_mul :
    completedRiemannZeta₀ (1/2 : ℂ)
      = riemannZeta (1/2 : ℂ) * Complex.Gammaℝ (1/2 : ℂ) + 4 := by
  have h0 := completedRiemannZeta₀_half_eq
  have h1 := completedRiemannZeta_half_eq
  linear_combination h1 - h0

/-- Conditional separation template: it suffices to show the product is not `-4`.
This isolates the exact remaining numeric goal; see the gap note below. -/
theorem completed₀_half_ne_zero_of_product_ne_neg_four
    (h : (riemannZeta (1/2 : ℂ) * Complex.Gammaℝ (1/2 : ℂ)).re ≠ -4) :
    (completedRiemannZeta₀ (1/2 : ℂ)).re ≠ 0 := by
  have hre : (completedRiemannZeta₀ (1/2 : ℂ)).re
      = (riemannZeta (1/2 : ℂ) * Complex.Gammaℝ (1/2 : ℂ)).re + 4 := by
    rw [completedRiemannZeta₀_half_eq_mul, Complex.add_re]
    simp
  rw [hre]
  intro h0
  apply h
  linarith

/-! ## Two-sided rigorous bounds on `Gamma(1/4)` (reflection + convexity).

We prove `3.33 < Gamma(1/4) < 3.78` (true value ≈ 3.6256) and
`0.751 < π^(-1/4) < 0.752` (true value ≈ 0.7511), hence
`2.50 < (Gammaℝ(1/2)).re < 2.85` (true value ≈ 2.7233).
Ingredients (all Mathlib, no `sorry`):
* upper: convexity chord of `Gamma` on `[1, 3/2]` at `5/4`, via
  `Gamma(3/2) = √π/2`, then `Gamma(1/4) = 4·Gamma(5/4)`;
* lower: Euler's reflection `Gamma(1/4)·Gamma(3/4) = π√2` plus the
  log-convexity chord on `[1/2, 1]` at `3/4`, giving `Gamma(3/4) < 1.3314`;
* numerics: `Real.pi_gt_d4`/`Real.pi_lt_d4` (4-digit π bounds) and explicit
  square/fourth-power comparisons discharged by `norm_num`.
-/

/-- `Gamma(3/2) = √π/2`, from the recurrence at `1/2`. -/
theorem gamma_three_half_eq : Real.Gamma (3/2 : ℝ) = Real.sqrt Real.pi / 2 := by
  have h := Real.Gamma_add_one (show (1/2 : ℝ) ≠ 0 by norm_num)
  have e : ((1/2 : ℝ) + 1) = (3/2 : ℝ) := by norm_num
  rw [e, Real.Gamma_one_half_eq] at h
  linarith

/-- Convexity upper bound at `5/4` on the chord `[1, 3/2]`
(`5/4 = (1/2)·1 + (1/2)·(3/2)`). -/
theorem gamma_five_quarter_le :
    Real.Gamma (5/4 : ℝ) ≤ (1 + Real.sqrt Real.pi / 2) / 2 := by
  have hconv := Real.convexOn_Gamma
  have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have h2 : (3/2 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have h := hconv.2 h1 h2 (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (0 : ℝ) ≤ 1/2 by norm_num) (by norm_num)
  have heq : (1/2 : ℝ) • (1 : ℝ) + (1/2 : ℝ) • (3/2 : ℝ) = (5/4 : ℝ) := by
    simp only [smul_eq_mul]
    ring
  rw [heq, Real.Gamma_one, gamma_three_half_eq] at h
  simp only [smul_eq_mul] at h
  linarith

/-- Transfer: `Gamma(1/4) ≤ 2 + √π`, via `Gamma(5/4) = (1/4)·Gamma(1/4)`. -/
theorem gamma_quarter_le_two_add_sqrt_pi :
    Real.Gamma (1/4 : ℝ) ≤ 2 + Real.sqrt Real.pi := by
  have h5 := gamma_five_quarter_le
  have hadd : Real.Gamma (5/4 : ℝ) = (1/4 : ℝ) * Real.Gamma (1/4 : ℝ) := by
    have h := Real.Gamma_add_one (show (1/4 : ℝ) ≠ 0 by norm_num)
    have h54 : ((1/4 : ℝ) + 1) = (5/4 : ℝ) := by ring
    rw [h54] at h
    exact h
  rw [hadd] at h5
  linarith

/-- Euler's reflection at `1/4`: `Gamma(1/4)·Gamma(3/4) = π√2`. -/
theorem gamma_quarter_mul_gamma_three_quarter :
    Real.Gamma (1/4 : ℝ) * Real.Gamma (3/4 : ℝ) = Real.pi * Real.sqrt 2 := by
  have hrefl := Real.Gamma_mul_Gamma_one_sub (1/4 : ℝ)
  have e1 : (1 : ℝ) - (1/4 : ℝ) = (3/4 : ℝ) := by norm_num
  have e2 : Real.pi * (1/4 : ℝ) = Real.pi / 4 := by ring
  rw [e1, e2, Real.sin_pi_div_four] at hrefl
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsqrt_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2pos : (0 : ℝ) < Real.sqrt 2 / 2 := div_pos hsqrt_pos (by norm_num)
  rw [eq_div_iff_mul_eq (ne_of_gt h2pos)] at hrefl
  have h2 : Real.Gamma (1/4 : ℝ) * Real.Gamma (3/4 : ℝ) * Real.sqrt 2
      = 2 * Real.pi := by
    linarith [hrefl]
  linear_combination (Real.sqrt 2 / 2) * h2 -
    (Real.Gamma (1/4 : ℝ) * Real.Gamma (3/4 : ℝ) / 2) * hsq

/-- Log-convexity chord on `[1/2, 1]` at `3/4`: `log Gamma(3/4) ≤ (log π)/4`. -/
theorem log_gamma_three_quarter_le :
    Real.log (Real.Gamma (3/4 : ℝ)) ≤ Real.log Real.pi / 4 := by
  have hconv := Real.convexOn_log_Gamma
  have h1 : (1/2 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have h2 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have h := hconv.2 h1 h2 (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (0 : ℝ) ≤ 1/2 by norm_num) (by norm_num)
  have heq : (1/2 : ℝ) • (1/2 : ℝ) + (1/2 : ℝ) • (1 : ℝ) = (3/4 : ℝ) := by
    simp only [smul_eq_mul]
    ring
  rw [heq] at h
  simp only [Function.comp_apply, smul_eq_mul] at h
  rw [Real.Gamma_one_half_eq, Real.Gamma_one] at h
  have hsqrt : Real.log (Real.sqrt Real.pi) = Real.log Real.pi / 2 := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow Real.pi_pos]
    ring
  rw [hsqrt, Real.log_one] at h
  linarith

/-- `Gamma(3/4) < 1.3314` (true value ≈ 1.2254). -/
theorem gamma_three_quarter_lt : Real.Gamma (3/4 : ℝ) < 1.3314 := by
  have hlog := log_gamma_three_quarter_le
  have h4 : (3.1416 : ℝ) < (1.3314 : ℝ) ^ 4 := by norm_num
  have hpi : Real.pi < (1.3314 : ℝ) ^ 4 := lt_trans Real.pi_lt_d4 h4
  have hlog2 : Real.log Real.pi < 4 * Real.log (1.3314 : ℝ) := by
    have h := (Real.log_lt_log_iff Real.pi_pos (by positivity)).mpr hpi
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hfin : Real.log (Real.Gamma (3/4 : ℝ)) < Real.log (1.3314 : ℝ) := by
    linarith
  exact (Real.log_lt_log_iff (Real.Gamma_pos_of_pos (by norm_num)) (by norm_num)).mp hfin

/-- `√2 > 1.4142`. -/
theorem sqrt_two_gt : (1.4142 : ℝ) < Real.sqrt 2 := by
  apply Real.lt_sqrt_of_sq_lt
  norm_num

/-- `√2 < 1.4143`. -/
theorem sqrt_two_lt : Real.sqrt 2 < (1.4143 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

/-- `√π < 1.7725`. -/
theorem sqrt_pi_lt : Real.sqrt Real.pi < 1.7725 := by
  rw [Real.sqrt_lt' (by norm_num)]
  exact lt_trans Real.pi_lt_d4 (by norm_num)

/-- Lower bound: `3.33 < Gamma(1/4)` (true value ≈ 3.6256). -/
theorem gamma_quarter_gt : (3.33 : ℝ) < Real.Gamma (1/4 : ℝ) := by
  have hprod := gamma_quarter_mul_gamma_three_quarter
  have h34 := gamma_three_quarter_lt
  have h34pos : 0 < Real.Gamma (3/4 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  have h34ne : Real.Gamma (3/4 : ℝ) ≠ 0 := ne_of_gt h34pos
  have hnum : (4.4427093 : ℝ) < Real.pi * Real.sqrt 2 := by
    calc (4.4427093 : ℝ) = 3.1415 * 1.4142 := by norm_num
      _ < Real.pi * 1.4142 :=
        mul_lt_mul_of_pos_right Real.pi_gt_d4 (by norm_num)
      _ < Real.pi * Real.sqrt 2 :=
        mul_lt_mul_of_pos_left sqrt_two_gt Real.pi_pos
  have hdecomp : Real.Gamma (1/4 : ℝ)
      = (Real.pi * Real.sqrt 2) / Real.Gamma (3/4 : ℝ) := by
    rw [eq_div_iff_mul_eq h34ne]
    exact hprod
  rw [hdecomp, lt_div_iff₀ h34pos]
  have hmul : (3.33 : ℝ) * Real.Gamma (3/4 : ℝ) < 3.33 * 1.3314 :=
    mul_lt_mul_of_pos_left h34 (by norm_num)
  have hle : (3.33 : ℝ) * 1.3314 < 4.4427093 := by norm_num
  linarith [hnum]

/-- Upper bound: `Gamma(1/4) < 3.78` (true value ≈ 3.6256). -/
theorem gamma_quarter_lt : Real.Gamma (1/4 : ℝ) < 3.78 := by
  have hle := gamma_quarter_le_two_add_sqrt_pi
  have hsq := sqrt_pi_lt
  linarith

/-- Two-sided interval: `3.33 < Gamma(1/4) < 3.78` (width `0.45`). -/
theorem gamma_quarter_bounds :
    (3.33 : ℝ) < Real.Gamma (1/4 : ℝ) ∧ Real.Gamma (1/4 : ℝ) < 3.78 :=
  ⟨gamma_quarter_gt, gamma_quarter_lt⟩

/-- `π^(1/4) > 1.3313`. -/
theorem pi_rpow_quarter_gt : (1.3313 : ℝ) < Real.pi ^ ((1/4 : ℝ)) := by
  have h4 : (1.3313 : ℝ) ^ 4 < 3.1415 := by norm_num
  have hpi : (1.3313 : ℝ) ^ 4 < Real.pi := lt_trans h4 Real.pi_gt_d4
  have hlog : 4 * Real.log (1.3313 : ℝ) < Real.log Real.pi := by
    have h := (Real.log_lt_log_iff (by positivity) Real.pi_pos).mpr hpi
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hrw : Real.log (Real.pi ^ ((1/4 : ℝ))) = (1/4) * Real.log Real.pi :=
    Real.log_rpow Real.pi_pos _
  have hfin : Real.log (1.3313 : ℝ) < Real.log (Real.pi ^ ((1/4 : ℝ))) := by
    rw [hrw]
    linarith
  exact (Real.log_lt_log_iff (by norm_num)
    (Real.rpow_pos_of_pos Real.pi_pos _)).mp hfin

/-- `π^(1/4) < 1.3314`. -/
theorem pi_rpow_quarter_lt : Real.pi ^ ((1/4 : ℝ)) < (1.3314 : ℝ) := by
  have h4 : (3.1416 : ℝ) < (1.3314 : ℝ) ^ 4 := by norm_num
  have hpi : Real.pi < (1.3314 : ℝ) ^ 4 := lt_trans Real.pi_lt_d4 h4
  have hlog : Real.log Real.pi < 4 * Real.log (1.3314 : ℝ) := by
    have h := (Real.log_lt_log_iff Real.pi_pos (by positivity)).mpr hpi
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hrw : Real.log (Real.pi ^ ((1/4 : ℝ))) = (1/4) * Real.log Real.pi :=
    Real.log_rpow Real.pi_pos _
  have hfin : Real.log (Real.pi ^ ((1/4 : ℝ))) < Real.log (1.3314 : ℝ) := by
    rw [hrw]
    linarith
  exact (Real.log_lt_log_iff (Real.rpow_pos_of_pos Real.pi_pos _) (by norm_num)).mp hfin

/-- `π^(-1/4) ∈ (0.751, 0.752)` (true value ≈ 0.7511). -/
theorem pi_rpow_neg_quarter_bounds :
    (0.751 : ℝ) < Real.pi ^ (-(1/4) : ℝ) ∧ Real.pi ^ (-(1/4) : ℝ) < 0.752 := by
  have hP1 := pi_rpow_quarter_gt
  have hP2 := pi_rpow_quarter_lt
  have hPpos : (0 : ℝ) < Real.pi ^ ((1/4 : ℝ)) :=
    Real.rpow_pos_of_pos Real.pi_pos _
  have heq : Real.pi ^ (-(1/4) : ℝ) = 1 / Real.pi ^ ((1/4 : ℝ)) := by
    have e1 : (-(1/4) : ℝ) = -((1/4) : ℝ) := by ring
    rw [e1, Real.rpow_neg (le_of_lt Real.pi_pos), inv_eq_one_div]
  rw [heq]
  have h1 : (1 : ℝ) / 1.3314 < 1 / Real.pi ^ ((1/4 : ℝ)) :=
    one_div_lt_one_div_of_lt hPpos hP2
  have h2 : 1 / Real.pi ^ ((1/4 : ℝ)) < 1 / (1.3313 : ℝ) :=
    one_div_lt_one_div_of_lt (by norm_num) hP1
  have b1 : (0.751 : ℝ) < 1 / 1.3314 := by norm_num
  have b2 : (1 : ℝ) / 1.3313 < 0.752 := by norm_num
  exact ⟨lt_trans b1 h1, lt_trans h2 b2⟩

/-- `(Gammaℝ(1/2)).re ∈ (2.50, 2.85)` (true value ≈ 2.7233). -/
theorem Gammaℝ_half_re_bounds :
    (2.50 : ℝ) < (Complex.Gammaℝ (1/2 : ℂ)).re ∧
      (Complex.Gammaℝ (1/2 : ℂ)).re < 2.85 := by
  rw [Gammaℝ_half_eq_real]
  simp only [Complex.ofReal_re]
  have hg1 := gamma_quarter_gt
  have hg2 := gamma_quarter_lt
  have hp1 := pi_rpow_neg_quarter_bounds.1
  have hp2 := pi_rpow_neg_quarter_bounds.2
  have hgpos : 0 < Real.Gamma (1/4 : ℝ) := gamma_quarter_pos
  have hppos : 0 < Real.pi ^ (-(1/4) : ℝ) := pi_rpow_neg_quarter_pos
  constructor
  · have e1 : (0.751 : ℝ) * 3.33 < 0.751 * Real.Gamma (1/4 : ℝ) :=
      mul_lt_mul_of_pos_left hg1 (by norm_num)
    have e2 : (0.751 : ℝ) * Real.Gamma (1/4 : ℝ)
        < Real.pi ^ (-(1/4) : ℝ) * Real.Gamma (1/4 : ℝ) :=
      mul_lt_mul_of_pos_right hp1 hgpos
    norm_num at e1
    linarith
  · have e1 : Real.Gamma (1/4 : ℝ) * Real.pi ^ (-(1/4) : ℝ)
        < 3.78 * Real.pi ^ (-(1/4) : ℝ) :=
      mul_lt_mul_of_pos_right hg2 hppos
    have e2 : (3.78 : ℝ) * Real.pi ^ (-(1/4) : ℝ) < 3.78 * 0.752 :=
      mul_lt_mul_of_pos_left hp2 (by norm_num)
    norm_num at e2
    linarith

/-- Bohr–Mollerup `n = 2` lower bound at `x = 1/4`: `3.38 < Gamma(1/4)`
(tightens `gamma_quarter_gt`; new interval `3.38 < Γ(1/4) < 3.78`, width `0.40`).
Note: `n = 1` gives only `Γ(1/4) ≥ 16/5 = 3.2` (weaker than `3.33`), so `n = 2`
is the first tightening approximant at `x = 1/4`. -/
theorem gamma_quarter_gt_BM2 : (3.38 : ℝ) < Real.Gamma (1/4 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hge := Real.BohrMollerup.ge_logGammaSeq Real.convexOn_log_Gamma hfeq hx
    (show (2 : ℕ) ≠ 0 by norm_num)
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hge
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 2
      = (5/4 : ℝ) * Real.log 2
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)) := by
    have f2 : Nat.factorial 2 = 2 := by decide
    have c2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + (2 : ℝ) = 9/4 := by norm_num
    have r2 : (2 : ℕ) = 1 + 1 := by norm_num
    have rr : Finset.range (2 : ℕ) = Finset.range (1 + 1) := by rw [r2]
    unfold Real.BohrMollerup.logGammaSeq
    rw [Finset.sum_range_succ, rr, Finset.sum_range_succ, Finset.sum_range_one,
      f2, c2, a0, a1, a2]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
      = Real.log 45 - 6 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have p : ((1/4 : ℝ) * (5/4)) * (9/4) = 45 / 64 := by norm_num
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log 45 - Real.log 64 := by
      rw [← Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
      have e64 : (64 : ℝ) = 2 ^ 6 := by norm_num
      rw [e64, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, l64]
  have hpow : (152.1 : ℝ) ^ 4 < 2 ^ 29 := by norm_num
  have hlog4 : 4 * Real.log (152.1 : ℝ) < 29 * Real.log 2 := by
    have h := (Real.log_lt_log_iff (by norm_num) (by positivity)).mpr hpow
    rwa [Real.log_pow, Real.log_pow] at h
  have e152 : Real.log (152.1 : ℝ) = Real.log (3.38 : ℝ) + Real.log 45 := by
    have p : (152.1 : ℝ) = 3.38 * 45 := by norm_num
    rw [p, Real.log_mul (by norm_num) (by norm_num)]
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff (by norm_num) hGpos]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_lt_of_le ?_ hge
  rw [hseq, hsum]
  linarith [hlog4, e152]

/-- `3^(1/4) < 1.3184` (true value ≈ 1.31607). -/
theorem three_rpow_quarter_lt : (3 : ℝ) ^ ((1/4 : ℝ)) < (1.3184 : ℝ) := by
  have h4 : (3 : ℝ) < (1.3184 : ℝ) ^ 4 := by norm_num
  have hlog : Real.log 3 < 4 * Real.log (1.3184 : ℝ) := by
    have h := (Real.log_lt_log_iff (by norm_num) (by positivity)).mpr h4
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hrw : Real.log ((3 : ℝ) ^ ((1/4 : ℝ))) = (1/4) * Real.log 3 :=
    Real.log_rpow (by norm_num) _
  have hfin : Real.log ((3 : ℝ) ^ ((1/4 : ℝ))) < Real.log (1.3184 : ℝ) := by
    rw [hrw]
    linarith
  exact (Real.log_lt_log_iff (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)).mp hfin

/-- Bohr–Mollerup `n = 2` upper bound at `x = 1/4`: `Gamma(1/4) < 3.751`
(mirror of `gamma_quarter_gt_BM2`; exact form `Γ ≤ 128·3^{1/4}/45 ≈ 3.743`;
new interval `3.38 < Γ(1/4) < 3.751`, width `0.371`). -/
theorem gamma_quarter_lt_BM2 : Real.Gamma (1/4 : ℝ) < (3.751 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hx' : (1/4 : ℝ) ≤ 1 := by norm_num
  have hle := Real.BohrMollerup.le_logGammaSeq Real.convexOn_log_Gamma hfeq hx hx' 2
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hle
  have c2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [c2] at hle
  have c3 : (2 : ℝ) + 1 = (3 : ℝ) := by norm_num
  rw [c3] at hle
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 2
      = (5/4 : ℝ) * Real.log 2
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)) := by
    have f2 : Nat.factorial 2 = 2 := by decide
    have c2' : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + (2 : ℝ) = 9/4 := by norm_num
    have r2 : (2 : ℕ) = 1 + 1 := by norm_num
    have rr : Finset.range (2 : ℕ) = Finset.range (1 + 1) := by rw [r2]
    unfold Real.BohrMollerup.logGammaSeq
    rw [Finset.sum_range_succ, rr, Finset.sum_range_succ, Finset.sum_range_one,
      f2, c2', a0, a1, a2]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
      = Real.log 45 - 6 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have p : ((1/4 : ℝ) * (5/4)) * (9/4) = 45 / 64 := by norm_num
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log 45 - Real.log 64 := by
      rw [← Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
      have e64 : (64 : ℝ) = 2 ^ 6 := by norm_num
      rw [e64, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, l64]
  have h3 := three_rpow_quarter_lt
  have hlog3 : Real.log ((3 : ℝ) ^ ((1/4 : ℝ))) < Real.log (1.3184 : ℝ) :=
    (Real.log_lt_log_iff (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)).mpr h3
  have hrw3 : Real.log ((3 : ℝ) ^ ((1/4 : ℝ))) = (1/4) * Real.log 3 :=
    Real.log_rpow (by norm_num) _
  have hq : (1/4 : ℝ) * Real.log 3 < Real.log (1.3184 : ℝ) := by
    rw [← hrw3]
    exact hlog3
  have hC : (1.3184 : ℝ) * 128 < 3.751 * 45 := by norm_num
  have hlogC : Real.log ((1.3184 : ℝ) * 128) < Real.log ((3.751 : ℝ) * 45) :=
    (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hC
  have l128 : Real.log ((1.3184 : ℝ) * 128)
      = Real.log 1.3184 + 7 * Real.log 2 := by
    have e128 : (128 : ℝ) = 2 ^ 7 := by norm_num
    have hm := Real.log_mul (show (1.3184 : ℝ) ≠ 0 by norm_num)
      (show (128 : ℝ) ≠ 0 by norm_num)
    rw [hm, e128, Real.log_pow]
    push_cast
    ring
  have r45 : Real.log ((3.751 : ℝ) * 45) = Real.log 3.751 + Real.log 45 :=
    Real.log_mul (by norm_num) (by norm_num)
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff hGpos (by norm_num)]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_le_of_lt hle ?_
  rw [hseq, hsum]
  linarith [hq, hlogC, l128, r45]

/-- Bohr–Mollerup `n = 3` lower bound at `x = 1/4`: `3.455 < Gamma(1/4)`
(tightens `gamma_quarter_gt_BM2`; exact `log`-of-rational value
`logΓ ≥ 9·log 2 - (3/4)·log 3 - log 5 - log 13 ≈ 1.240`,
i.e. `Γ ≥ 2^36/(3^3·5^4·13^4)` fourth root `≈ 3.4555`;
new interval `3.455 < Γ(1/4) < 3.751`, width `0.296`). -/
theorem gamma_quarter_gt_BM3 : (3.455 : ℝ) < Real.Gamma (1/4 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hge := Real.BohrMollerup.ge_logGammaSeq Real.convexOn_log_Gamma hfeq hx
    (show (3 : ℕ) ≠ 0 by norm_num)
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hge
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 3
      = (1/4 : ℝ) * Real.log 3 + Real.log 6
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
          + Real.log (9/4 : ℝ) + Real.log (13/4 : ℝ)) := by
    have f3 : Nat.factorial 3 = 6 := by decide
    have c3 : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f3, c3, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one, a0, a1, a2, a3]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        + Real.log (9/4 : ℝ) + Real.log (13/4 : ℝ)
      = Real.log 585 - 8 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have p : (((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4) = 585 / 256 := by norm_num
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log 585 - Real.log 256 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
      have e256 : (256 : ℝ) = 2 ^ 8 := by norm_num
      rw [e256, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, l256]
  have h6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    have e6 : (6 : ℝ) = 2 * 3 := by norm_num
    rw [e6, Real.log_mul (by norm_num) (by norm_num)]
  have h585 : Real.log (585 : ℝ) = 2 * Real.log 3 + Real.log 5 + Real.log 13 := by
    have e585 : (585 : ℝ) = (9 * 5) * 13 := by norm_num
    have e9 : (9 : ℝ) = 3 ^ 2 := by norm_num
    rw [e585, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e9, Real.log_pow]
    push_cast
    ring
  have hK : Real.log (481966875 : ℝ)
      = 3 * Real.log 3 + 4 * Real.log 5 + 4 * Real.log 13 := by
    have eK : (481966875 : ℝ) = (3 ^ 3 * 5 ^ 4) * 13 ^ 4 := by norm_num
    rw [eK, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpow : (3.455 : ℝ) ^ 4 * 481966875 < 2 ^ 36 := by norm_num
  have hlog4 : 4 * Real.log (3.455 : ℝ) + Real.log (481966875 : ℝ)
      < 36 * Real.log 2 := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpow
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff (by norm_num) hGpos]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_lt_of_le ?_ hge
  rw [hseq, hsum, h6, h585]
  linarith [hlog4, hK]

/-- Bohr–Mollerup `n = 3` upper bound at `x = 1/4`: `Gamma(1/4) < 3.714`
(mirror of `gamma_quarter_gt_BM3`; exact value
`logΓ ≤ (19/2)·log 2 - log 3 - log 5 - log 13 ≈ 1.312`,
i.e. `Γ ≤ 2^19/(195^2)` square root `≈ 3.7132`;
new interval `3.455 < Γ(1/4) < 3.714`, width `0.259`). -/
theorem gamma_quarter_lt_BM3 : Real.Gamma (1/4 : ℝ) < (3.714 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hx' : (1/4 : ℝ) ≤ 1 := by norm_num
  have hle := Real.BohrMollerup.le_logGammaSeq Real.convexOn_log_Gamma hfeq hx hx' 3
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hle
  have c3 : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
  rw [c3] at hle
  have c4 : (3 : ℝ) + 1 = (4 : ℝ) := by norm_num
  rw [c4] at hle
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 3
      = (1/4 : ℝ) * Real.log 3 + Real.log 6
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
          + Real.log (9/4 : ℝ) + Real.log (13/4 : ℝ)) := by
    have f3 : Nat.factorial 3 = 6 := by decide
    have c3' : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f3, c3', Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one, a0, a1, a2, a3]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        + Real.log (9/4 : ℝ) + Real.log (13/4 : ℝ)
      = Real.log 585 - 8 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have p : (((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4) = 585 / 256 := by norm_num
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log 585 - Real.log 256 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
      have e256 : (256 : ℝ) = 2 ^ 8 := by norm_num
      rw [e256, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, l256]
  have h6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    have e6 : (6 : ℝ) = 2 * 3 := by norm_num
    rw [e6, Real.log_mul (by norm_num) (by norm_num)]
  have h585 : Real.log (585 : ℝ) = 2 * Real.log 3 + Real.log 5 + Real.log 13 := by
    have e585 : (585 : ℝ) = (9 * 5) * 13 := by norm_num
    have e9 : (9 : ℝ) = 3 ^ 2 := by norm_num
    rw [e585, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e9, Real.log_pow]
    push_cast
    ring
  have l4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have e4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [e4, Real.log_pow]
    push_cast
    ring
  have h195 : Real.log (195 : ℝ) = Real.log 3 + Real.log 5 + Real.log 13 := by
    have e195 : (195 : ℝ) = (3 * 5) * 13 := by norm_num
    rw [e195, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  have hpowC : (2 : ℝ) ^ 19 < (195 * 3.714) ^ 2 := by norm_num
  have hlogC : 19 * Real.log 2 < 2 * Real.log (195 * 3.714) := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpowC
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have rC : Real.log (195 * 3.714) = Real.log 195 + Real.log 3.714 :=
    Real.log_mul (by norm_num) (by norm_num)
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff hGpos (by norm_num)]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_le_of_lt hle ?_
  rw [hseq, hsum, h6, h585, l4]
  linarith [hlogC, rC, h195]

/-- Two-sided Bohr–Mollerup `n = 3` interval: `3.455 < Γ(1/4) < 3.714`
(width `0.259`, tightening the `n = 2` interval `3.38 < Γ < 3.751`, width `0.371`). -/
theorem gamma_quarter_bounds_BM3 :
    (3.455 : ℝ) < Real.Gamma (1/4 : ℝ) ∧ Real.Gamma (1/4 : ℝ) < (3.714 : ℝ) :=
  ⟨gamma_quarter_gt_BM3, gamma_quarter_lt_BM3⟩

/-- Bohr–Mollerup `n = 4` lower bound at `x = 1/4`: `3.494 < Gamma(1/4)`
(tightens `gamma_quarter_gt_BM3`; exact `log`-of-rational value
`logΓ ≥ (27/2)·log 2 - log 3 - log 5 - log 13 - log 17 ≈ 1.2513`,
i.e. `Γ ≥ sqrt(2^27/(3^2·5^2·13^2·17^2)) ≈ 3.49479`;
new interval `3.494 < Γ(1/4) < 3.714`, width `0.220`). -/
theorem gamma_quarter_gt_BM4 : (3.494 : ℝ) < Real.Gamma (1/4 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hge := Real.BohrMollerup.ge_logGammaSeq Real.convexOn_log_Gamma hfeq hx
    (show (4 : ℕ) ≠ 0 by norm_num)
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hge
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 4
      = (1/4 : ℝ) * Real.log 4 + Real.log 24
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
          + Real.log (9/4 : ℝ) + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ)) := by
    have f4 : Nat.factorial 4 = 24 := by decide
    have c4 : ((4 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = 17/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f4, c4, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      a0, a1, a2, a3, a4]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hpos174 : (0 : ℝ) < 17/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        + Real.log (9/4 : ℝ) + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ)
      = Real.log 9945 - 10 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne').symm
    have p : ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4) = 9945 / 1024 := by
      norm_num
    have m4 : Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4))
        + Real.log (17/4 : ℝ)
        = Real.log 9945 - Real.log 1024 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l1024 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
      have e1024 : (1024 : ℝ) = 2 ^ 10 := by norm_num
      rw [e1024, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, l1024]
  have h24 : Real.log (24 : ℝ) = 3 * Real.log 2 + Real.log 3 := by
    have e24 : (24 : ℝ) = 8 * 3 := by norm_num
    have e8 : (8 : ℝ) = 2 ^ 3 := by norm_num
    rw [e24, Real.log_mul (by norm_num) (by norm_num), e8, Real.log_pow]
    push_cast
    ring
  have l4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have e4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [e4, Real.log_pow]
    push_cast
    ring
  have h9945 : Real.log (9945 : ℝ)
      = 2 * Real.log 3 + Real.log 5 + Real.log 13 + Real.log 17 := by
    have e9945 : (9945 : ℝ) = ((9 * 5) * 13) * 17 := by norm_num
    have e9 : (9 : ℝ) = 3 ^ 2 := by norm_num
    rw [e9945, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e9, Real.log_pow]
    push_cast
    ring
  have hK : Real.log (10989225 : ℝ)
      = 2 * Real.log 3 + 2 * Real.log 5 + 2 * Real.log 13 + 2 * Real.log 17 := by
    have eK : (10989225 : ℝ) = ((3 ^ 2 * 5 ^ 2) * 13 ^ 2) * 17 ^ 2 := by norm_num
    rw [eK, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpow : (3.494 : ℝ) ^ 2 * 10989225 < 2 ^ 27 := by norm_num
  have hlog2 : 2 * Real.log (3.494 : ℝ) + Real.log (10989225 : ℝ)
      < 27 * Real.log 2 := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpow
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff (by norm_num) hGpos]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_lt_of_le ?_ hge
  rw [hseq, hsum, h24, l4, h9945]
  linarith [hlog2, hK]

/-- Bohr–Mollerup `n = 4` upper bound at `x = 1/4`: `Gamma(1/4) < 3.696`
(mirror of `gamma_quarter_gt_BM4`; exact value
`logΓ ≤ 13·log 2 - log 3 - (3/4)·log 5 - log 13 - log 17 ≈ 1.3071`,
i.e. `Γ ≤ (2^52/(3^4·5^3·13^4·17^4))^{1/4} ≈ 3.69529`;
new interval `3.494 < Γ(1/4) < 3.696`, width `0.202`). -/
theorem gamma_quarter_lt_BM4 : Real.Gamma (1/4 : ℝ) < (3.696 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hx' : (1/4 : ℝ) ≤ 1 := by norm_num
  have hle := Real.BohrMollerup.le_logGammaSeq Real.convexOn_log_Gamma hfeq hx hx' 4
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hle
  have c4 : ((4 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
  rw [c4] at hle
  have c5 : (4 : ℝ) + 1 = (5 : ℝ) := by norm_num
  rw [c5] at hle
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 4
      = (1/4 : ℝ) * Real.log 4 + Real.log 24
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
          + Real.log (9/4 : ℝ) + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ)) := by
    have f4 : Nat.factorial 4 = 24 := by decide
    have c4' : ((4 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = 17/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f4, c4', Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      a0, a1, a2, a3, a4]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hpos174 : (0 : ℝ) < 17/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        + Real.log (9/4 : ℝ) + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ)
      = Real.log 9945 - 10 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne').symm
    have p : ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4) = 9945 / 1024 := by
      norm_num
    have m4 : Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4))
        + Real.log (17/4 : ℝ)
        = Real.log 9945 - Real.log 1024 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l1024 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
      have e1024 : (1024 : ℝ) = 2 ^ 10 := by norm_num
      rw [e1024, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, l1024]
  have h24 : Real.log (24 : ℝ) = 3 * Real.log 2 + Real.log 3 := by
    have e24 : (24 : ℝ) = 8 * 3 := by norm_num
    have e8 : (8 : ℝ) = 2 ^ 3 := by norm_num
    rw [e24, Real.log_mul (by norm_num) (by norm_num), e8, Real.log_pow]
    push_cast
    ring
  have l4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have e4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [e4, Real.log_pow]
    push_cast
    ring
  have h9945 : Real.log (9945 : ℝ)
      = 2 * Real.log 3 + Real.log 5 + Real.log 13 + Real.log 17 := by
    have e9945 : (9945 : ℝ) = ((9 * 5) * 13) * 17 := by norm_num
    have e9 : (9 : ℝ) = 3 ^ 2 := by norm_num
    rw [e9945, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e9, Real.log_pow]
    push_cast
    ring
  have hKup : Real.log (24152613220125 : ℝ)
      = 4 * Real.log 3 + 3 * Real.log 5 + 4 * Real.log 13 + 4 * Real.log 17 := by
    have eK : (24152613220125 : ℝ) = ((3 ^ 4 * 5 ^ 3) * 13 ^ 4) * 17 ^ 4 := by
      norm_num
    rw [eK, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpowC : (2 : ℝ) ^ 52 < (3.696 : ℝ) ^ 4 * 24152613220125 := by norm_num
  have hlogC : 52 * Real.log 2
      < 4 * Real.log (3.696 : ℝ) + Real.log (24152613220125 : ℝ) := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpowC
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff hGpos (by norm_num)]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_le_of_lt hle ?_
  rw [hseq, hsum, h24, l4, h9945]
  linarith [hlogC, hKup]

/-- Two-sided Bohr–Mollerup `n = 4` interval: `3.494 < Γ(1/4) < 3.696`
(width `0.202`, tightening the `n = 3` interval `3.455 < Γ < 3.714`, width `0.259`). -/
theorem gamma_quarter_bounds_BM4 :
    (3.494 : ℝ) < Real.Gamma (1/4 : ℝ) ∧ Real.Gamma (1/4 : ℝ) < (3.696 : ℝ) :=
  ⟨gamma_quarter_gt_BM4, gamma_quarter_lt_BM4⟩

/-- Bohr–Mollerup `n = 5` lower bound at `x = 1/4`: `3.519 < Gamma(1/4)`
(tightens `gamma_quarter_gt_BM4`; exact `log`-of-rational value
`logΓ ≥ 15·log 2 - 2·log 3 + (1/4)·log 5 - log 7 - log 13 - log 17 ≈ 1.2583`,
i.e. `Γ ≥ (2^60·5/(3^8·7^4·13^4·17^4))^{1/4} ≈ 3.51933`;
new interval `3.519 < Γ(1/4) < 3.696`, width `0.177`). -/
theorem gamma_quarter_gt_BM5 : (3.519 : ℝ) < Real.Gamma (1/4 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hge := Real.BohrMollerup.ge_logGammaSeq Real.convexOn_log_Gamma hfeq hx
    (show (5 : ℕ) ≠ 0 by norm_num)
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hge
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 5
      = (1/4 : ℝ) * Real.log 5 + Real.log 120
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)) := by
    have f5 : Nat.factorial 5 = 120 := by decide
    have c5 : ((5 : ℕ) : ℝ) = (5 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = 17/4 := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = 21/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f5, c5, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, a0, a1, a2, a3, a4, a5]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hpos174 : (0 : ℝ) < 17/4 := by norm_num
  have hpos214 : (0 : ℝ) < 21/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
      = Real.log 208845 - 12 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4))
        + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have p : (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) * (21/4)
        = 208845 / 4096 := by norm_num
    have m5 : Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
        + Real.log (21/4 : ℝ)
        = Real.log 208845 - Real.log 4096 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne', p, Real.log_div (by norm_num) (by norm_num)]
    have l4096 : Real.log (4096 : ℝ) = 12 * Real.log 2 := by
      have e4096 : (4096 : ℝ) = 2 ^ 12 := by norm_num
      rw [e4096, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, l4096]
  have h120 : Real.log (120 : ℝ) = 3 * Real.log 2 + Real.log 3 + Real.log 5 := by
    have e120 : (120 : ℝ) = (8 * 3) * 5 := by norm_num
    have e8 : (8 : ℝ) = 2 ^ 3 := by norm_num
    rw [e120, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e8, Real.log_pow]
    push_cast
    ring
  have h208845 : Real.log (208845 : ℝ)
      = 3 * Real.log 3 + Real.log 5 + Real.log 7 + Real.log 13
        + Real.log 17 := by
    have e208845 : (208845 : ℝ) = (((27 * 5) * 7) * 13) * 17 := by norm_num
    have e27 : (27 : ℝ) = 3 ^ 3 := by norm_num
    rw [e208845, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e27, Real.log_pow]
    push_cast
    ring
  have hK : Real.log (37577794973305041 : ℝ)
      = 8 * Real.log 3 + 4 * Real.log 7 + 4 * Real.log 13
        + 4 * Real.log 17 := by
    have eK : (37577794973305041 : ℝ)
        = ((3 ^ 8 * 7 ^ 4) * 13 ^ 4) * 17 ^ 4 := by norm_num
    rw [eK, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpow : (3.519 : ℝ) ^ 4 * 37577794973305041 < 2 ^ 60 * 5 := by norm_num
  have hlog4 : 4 * Real.log (3.519 : ℝ) + Real.log (37577794973305041 : ℝ)
      < 60 * Real.log 2 + Real.log 5 := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpow
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff (by norm_num) hGpos]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_lt_of_le ?_ hge
  rw [hseq, hsum, h120, h208845]
  linarith [hlog4, hK]

/-- Bohr–Mollerup `n = 5` upper bound at `x = 1/4`: `Gamma(1/4) < 3.684`
(mirror of `gamma_quarter_gt_BM5`; exact value
`logΓ ≤ (61/4)·log 2 - (7/4)·log 3 - log 7 - log 13 - log 17 ≈ 1.3039`,
i.e. `Γ ≤ (2^61/(3^7·7^4·13^4·17^4))^{1/4} ≈ 3.68345`;
new interval `3.519 < Γ(1/4) < 3.684`, width `0.165`). -/
theorem gamma_quarter_lt_BM5 : Real.Gamma (1/4 : ℝ) < (3.684 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hx' : (1/4 : ℝ) ≤ 1 := by norm_num
  have hle := Real.BohrMollerup.le_logGammaSeq Real.convexOn_log_Gamma hfeq hx hx' 5
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hle
  have c5 : ((5 : ℕ) : ℝ) = (5 : ℝ) := by norm_num
  rw [c5] at hle
  have c6 : (5 : ℝ) + 1 = (6 : ℝ) := by norm_num
  rw [c6] at hle
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 5
      = (1/4 : ℝ) * Real.log 5 + Real.log 120
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)) := by
    have f5 : Nat.factorial 5 = 120 := by decide
    have c5' : ((5 : ℕ) : ℝ) = (5 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = 17/4 := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = 21/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f5, c5', Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, a0, a1, a2, a3, a4, a5]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hpos174 : (0 : ℝ) < 17/4 := by norm_num
  have hpos214 : (0 : ℝ) < 21/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
      = Real.log 208845 - 12 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4))
        + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have p : (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) * (21/4)
        = 208845 / 4096 := by norm_num
    have m5 : Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
        + Real.log (21/4 : ℝ)
        = Real.log 208845 - Real.log 4096 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne', p, Real.log_div (by norm_num) (by norm_num)]
    have l4096 : Real.log (4096 : ℝ) = 12 * Real.log 2 := by
      have e4096 : (4096 : ℝ) = 2 ^ 12 := by norm_num
      rw [e4096, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, l4096]
  have h120 : Real.log (120 : ℝ) = 3 * Real.log 2 + Real.log 3 + Real.log 5 := by
    have e120 : (120 : ℝ) = (8 * 3) * 5 := by norm_num
    have e8 : (8 : ℝ) = 2 ^ 3 := by norm_num
    rw [e120, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e8, Real.log_pow]
    push_cast
    ring
  have h208845 : Real.log (208845 : ℝ)
      = 3 * Real.log 3 + Real.log 5 + Real.log 7 + Real.log 13
        + Real.log 17 := by
    have e208845 : (208845 : ℝ) = (((27 * 5) * 7) * 13) * 17 := by norm_num
    have e27 : (27 : ℝ) = 3 ^ 3 := by norm_num
    rw [e208845, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e27, Real.log_pow]
    push_cast
    ring
  have h6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    have e6 : (6 : ℝ) = 2 * 3 := by norm_num
    rw [e6, Real.log_mul (by norm_num) (by norm_num)]
  have hKup : Real.log (12525931657768347 : ℝ)
      = 7 * Real.log 3 + 4 * Real.log 7 + 4 * Real.log 13
        + 4 * Real.log 17 := by
    have eK : (12525931657768347 : ℝ)
        = ((3 ^ 7 * 7 ^ 4) * 13 ^ 4) * 17 ^ 4 := by norm_num
    rw [eK, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpowC : (2 : ℝ) ^ 61 < (3.684 : ℝ) ^ 4 * 12525931657768347 := by norm_num
  have hlogC : 61 * Real.log 2
      < 4 * Real.log (3.684 : ℝ) + Real.log (12525931657768347 : ℝ) := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpowC
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff hGpos (by norm_num)]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_le_of_lt hle ?_
  rw [hseq, hsum, h120, h208845, h6]
  linarith [hlogC, hKup]

/-- Two-sided Bohr–Mollerup `n = 5` interval: `3.519 < Γ(1/4) < 3.684`
(width `0.165`, tightening the `n = 4` interval `3.494 < Γ < 3.696`, width `0.202`). -/
theorem gamma_quarter_bounds_BM5 :
    (3.519 : ℝ) < Real.Gamma (1/4 : ℝ) ∧ Real.Gamma (1/4 : ℝ) < (3.684 : ℝ) :=
  ⟨gamma_quarter_gt_BM5, gamma_quarter_lt_BM5⟩

/-- Bohr–Mollerup `n = 6` lower bound at `x = 1/4`: `3.536 < Gamma(1/4)`
(tightens `gamma_quarter_gt_BM5`; exact `log`-of-rational value
`logΓ ≥ (73/4)·log 2 - (3/4)·log 3 - 2·log 5 - log 7 - log 13 - log 17 ≈ 1.2630`,
i.e. `Γ ≥ (2^73/(3^3·5^8·7^4·13^4·17^4))^{1/4} ≈ 3.53611`;
new interval `3.536 < Γ(1/4) < 3.684`, width `0.148`). -/
theorem gamma_quarter_gt_BM6 : (3.536 : ℝ) < Real.Gamma (1/4 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hge := Real.BohrMollerup.ge_logGammaSeq Real.convexOn_log_Gamma hfeq hx
    (show (6 : ℕ) ≠ 0 by norm_num)
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hge
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 6
      = (1/4 : ℝ) * Real.log 6 + Real.log 720
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
          + Real.log (25/4 : ℝ)) := by
    have f6 : Nat.factorial 6 = 720 := by decide
    have c6 : ((6 : ℕ) : ℝ) = (6 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = 17/4 := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = 21/4 := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = 25/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f6, c6, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one, a0, a1, a2, a3, a4, a5, a6]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hpos174 : (0 : ℝ) < 17/4 := by norm_num
  have hpos214 : (0 : ℝ) < 21/4 := by norm_num
  have hpos254 : (0 : ℝ) < 25/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ)
      = Real.log 5221125 - 14 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4))
        + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
        + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne').symm
    have p : ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) * (21/4))
        * (25/4) = 5221125 / 16384 := by norm_num
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) + Real.log (25/4 : ℝ)
        = Real.log 5221125 - Real.log 16384 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne')
        hpos174.ne') hpos214.ne') hpos254.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l16384 : Real.log (16384 : ℝ) = 14 * Real.log 2 := by
      have e16384 : (16384 : ℝ) = 2 ^ 14 := by norm_num
      rw [e16384, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, l16384]
  have h720 : Real.log (720 : ℝ)
      = 4 * Real.log 2 + 2 * Real.log 3 + Real.log 5 := by
    have e720 : (720 : ℝ) = (16 * 9) * 5 := by norm_num
    have e16 : (16 : ℝ) = 2 ^ 4 := by norm_num
    have e9 : (9 : ℝ) = 3 ^ 2 := by norm_num
    rw [e720, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e16, e9,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h5221125 : Real.log (5221125 : ℝ)
      = 3 * Real.log 3 + 3 * Real.log 5 + Real.log 7 + Real.log 13
        + Real.log 17 := by
    have e5221125 : (5221125 : ℝ) = ((((27 * 125) * 7) * 13) * 17) := by norm_num
    have e27 : (27 : ℝ) = 3 ^ 3 := by norm_num
    have e125 : (125 : ℝ) = 5 ^ 3 := by norm_num
    rw [e5221125, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e27, e125,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    have e6 : (6 : ℝ) = 2 * 3 := by norm_num
    rw [e6, Real.log_mul (by norm_num) (by norm_num)]
  have hK : Real.log (60406692022416796875 : ℝ)
      = 3 * Real.log 3 + 8 * Real.log 5 + 4 * Real.log 7 + 4 * Real.log 13
        + 4 * Real.log 17 := by
    have eK : (60406692022416796875 : ℝ)
        = ((((3 ^ 3 * 5 ^ 8) * 7 ^ 4) * 13 ^ 4) * 17 ^ 4) := by norm_num
    rw [eK, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpow : (3.536 : ℝ) ^ 4 * 60406692022416796875 < 2 ^ 73 := by norm_num
  have hlog4 : 4 * Real.log (3.536 : ℝ) + Real.log (60406692022416796875 : ℝ)
      < 73 * Real.log 2 := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpow
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff (by norm_num) hGpos]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_lt_of_le ?_ hge
  rw [hseq, hsum, h720, h5221125, h6]
  linarith [hlog4, hK]

/-- Bohr–Mollerup `n = 6` upper bound at `x = 1/4`: `Gamma(1/4) < 3.676`
(mirror of `gamma_quarter_gt_BM6`; exact value
`logΓ ≤ 18·log 2 - log 3 - 2·log 5 - (3/4)·log 7 - log 13 - log 17 ≈ 1.3016`,
i.e. `Γ ≤ (2^72/(3^4·5^8·7^3·13^4·17^4))^{1/4} ≈ 3.67505`;
new interval `3.536 < Γ(1/4) < 3.676`, width `0.140`). -/
theorem gamma_quarter_lt_BM6 : Real.Gamma (1/4 : ℝ) < (3.676 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hx' : (1/4 : ℝ) ≤ 1 := by norm_num
  have hle := Real.BohrMollerup.le_logGammaSeq Real.convexOn_log_Gamma hfeq hx hx' 6
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hle
  have c6 : ((6 : ℕ) : ℝ) = (6 : ℝ) := by norm_num
  rw [c6] at hle
  have c7 : (6 : ℝ) + 1 = (7 : ℝ) := by norm_num
  rw [c7] at hle
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 6
      = (1/4 : ℝ) * Real.log 6 + Real.log 720
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
          + Real.log (25/4 : ℝ)) := by
    have f6 : Nat.factorial 6 = 720 := by decide
    have c6' : ((6 : ℕ) : ℝ) = (6 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = 17/4 := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = 21/4 := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = 25/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f6, c6', Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one, a0, a1, a2, a3, a4, a5, a6]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hpos174 : (0 : ℝ) < 17/4 := by norm_num
  have hpos214 : (0 : ℝ) < 21/4 := by norm_num
  have hpos254 : (0 : ℝ) < 25/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ)
      = Real.log 5221125 - 14 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4))
        + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
        + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne').symm
    have p : ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) * (21/4))
        * (25/4) = 5221125 / 16384 := by norm_num
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) + Real.log (25/4 : ℝ)
        = Real.log 5221125 - Real.log 16384 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne')
        hpos174.ne') hpos214.ne') hpos254.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l16384 : Real.log (16384 : ℝ) = 14 * Real.log 2 := by
      have e16384 : (16384 : ℝ) = 2 ^ 14 := by norm_num
      rw [e16384, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, l16384]
  have h720 : Real.log (720 : ℝ)
      = 4 * Real.log 2 + 2 * Real.log 3 + Real.log 5 := by
    have e720 : (720 : ℝ) = (16 * 9) * 5 := by norm_num
    have e16 : (16 : ℝ) = 2 ^ 4 := by norm_num
    have e9 : (9 : ℝ) = 3 ^ 2 := by norm_num
    rw [e720, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e16, e9,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h5221125 : Real.log (5221125 : ℝ)
      = 3 * Real.log 3 + 3 * Real.log 5 + Real.log 7 + Real.log 13
        + Real.log 17 := by
    have e5221125 : (5221125 : ℝ) = ((((27 * 125) * 7) * 13) * 17) := by norm_num
    have e27 : (27 : ℝ) = 3 ^ 3 := by norm_num
    have e125 : (125 : ℝ) = 5 ^ 3 := by norm_num
    rw [e5221125, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e27, e125,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    have e6 : (6 : ℝ) = 2 * 3 := by norm_num
    rw [e6, Real.log_mul (by norm_num) (by norm_num)]
  have h7 : Real.log (7 : ℝ) = Real.log 7 := rfl
  have hKup : Real.log (25888582295321484375 : ℝ)
      = 4 * Real.log 3 + 8 * Real.log 5 + 3 * Real.log 7 + 4 * Real.log 13
        + 4 * Real.log 17 := by
    have eK : (25888582295321484375 : ℝ)
        = ((((3 ^ 4 * 5 ^ 8) * 7 ^ 3) * 13 ^ 4) * 17 ^ 4) := by norm_num
    rw [eK, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpowC : (2 : ℝ) ^ 72 < (3.676 : ℝ) ^ 4 * 25888582295321484375 := by norm_num
  have hlogC : 72 * Real.log 2
      < 4 * Real.log (3.676 : ℝ) + Real.log (25888582295321484375 : ℝ) := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpowC
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff hGpos (by norm_num)]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_le_of_lt hle ?_
  rw [hseq, hsum, h720, h5221125, h6, h7]
  linarith [hlogC, hKup]

/-- Two-sided Bohr–Mollerup `n = 6` interval: `3.536 < Γ(1/4) < 3.676`
(width `0.140`, tightening the `n = 5` interval `3.519 < Γ < 3.684`, width `0.165`). -/
theorem gamma_quarter_bounds_BM6 :
    (3.536 : ℝ) < Real.Gamma (1/4 : ℝ) ∧ Real.Gamma (1/4 : ℝ) < (3.676 : ℝ) :=
  ⟨gamma_quarter_gt_BM6, gamma_quarter_lt_BM6⟩

/-- Bohr–Mollerup `n = 7` lower bound at `x = 1/4`: `3.548 < Gamma(1/4)`
(tightens `gamma_quarter_gt_BM6`; exact `log`-of-rational value
`logΓ ≥ 20·log 2 - log 3 - 2·log 5 + (1/4)·log 7 - log 13 - log 17 - log 29 ≈ 1.2665`,
i.e. `Γ ≥ (2^80·7/(3^4·5^8·13^4·17^4·29^4))^{1/4} ≈ 3.54832`;
new interval `3.548 < Γ(1/4) < 3.676`, width `0.128`). -/
theorem gamma_quarter_gt_BM7 : (3.548 : ℝ) < Real.Gamma (1/4 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hge := Real.BohrMollerup.ge_logGammaSeq Real.convexOn_log_Gamma hfeq hx
    (show (7 : ℕ) ≠ 0 by norm_num)
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hge
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 7
      = (1/4 : ℝ) * Real.log 7 + Real.log 5040
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
          + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ)) := by
    have f7 : Nat.factorial 7 = 5040 := by decide
    have c7 : ((7 : ℕ) : ℝ) = (7 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = 17/4 := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = 21/4 := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = 25/4 := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = 29/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f7, c7, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      a0, a1, a2, a3, a4, a5, a6, a7]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hpos174 : (0 : ℝ) < 17/4 := by norm_num
  have hpos214 : (0 : ℝ) < 21/4 := by norm_num
  have hpos254 : (0 : ℝ) < 25/4 := by norm_num
  have hpos294 : (0 : ℝ) < 29/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ)
      = Real.log 151412625 - 16 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4))
        + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
        + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne')
        hpos174.ne') hpos214.ne') hpos254.ne').symm
    have p : (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4) = 151412625 / 65536 := by norm_num
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) + Real.log (29/4 : ℝ)
        = Real.log 151412625 - Real.log 65536 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne')
        hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l65536 : Real.log (65536 : ℝ) = 16 * Real.log 2 := by
      have e65536 : (65536 : ℝ) = 2 ^ 16 := by norm_num
      rw [e65536, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, l65536]
  have h5040 : Real.log (5040 : ℝ)
      = 4 * Real.log 2 + 2 * Real.log 3 + Real.log 5 + Real.log 7 := by
    have e5040 : (5040 : ℝ) = ((16 * 9) * 5) * 7 := by norm_num
    have e16 : (16 : ℝ) = 2 ^ 4 := by norm_num
    have e9 : (9 : ℝ) = 3 ^ 2 := by norm_num
    rw [e5040, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e16, e9,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (151412625 : ℝ)
      = 3 * Real.log 3 + 3 * Real.log 5 + Real.log 7 + Real.log 13
        + Real.log 17 + Real.log 29 := by
    have eN : (151412625 : ℝ) = (((((27 * 125) * 7) * 13) * 17) * 29) := by
      norm_num
    have e27 : (27 : ℝ) = 3 ^ 3 := by norm_num
    have e125 : (125 : ℝ) = 5 ^ 3 := by norm_num
    rw [eN, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e27, e125,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hK : Real.log (53383388846697594140625 : ℝ)
      = 4 * Real.log 3 + 8 * Real.log 5 + 4 * Real.log 13
        + 4 * Real.log 17 + 4 * Real.log 29 := by
    have eK : (53383388846697594140625 : ℝ)
        = ((((3 ^ 4 * 5 ^ 8) * 13 ^ 4) * 17 ^ 4) * 29 ^ 4) := by norm_num
    rw [eK, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpow : (3.548 : ℝ) ^ 4 * 53383388846697594140625 < 2 ^ 80 * 7 := by
    norm_num
  have hlog4 : 4 * Real.log (3.548 : ℝ) + Real.log (53383388846697594140625 : ℝ)
      < 80 * Real.log 2 + Real.log 7 := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpow
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff (by norm_num) hGpos]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_lt_of_le ?_ hge
  rw [hseq, hsum, h5040, hN]
  linarith [hlog4, hK]

/-- Bohr–Mollerup `n = 7` upper bound at `x = 1/4`: `Gamma(1/4) < 3.669`
(mirror of `gamma_quarter_gt_BM7`; exact value
`logΓ ≤ 20.75·log 2 - log 3 - 2·log 5 - log 13 - log 17 - log 29 ≈ 1.2999`,
i.e. `Γ ≤ (2^83/(3^4·5^8·13^4·17^4·29^4))^{1/4} ≈ 3.66877`;
new interval `3.548 < Γ(1/4) < 3.669`, width `0.121`). -/
theorem gamma_quarter_lt_BM7 : Real.Gamma (1/4 : ℝ) < (3.669 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hx' : (1/4 : ℝ) ≤ 1 := by norm_num
  have hle := Real.BohrMollerup.le_logGammaSeq Real.convexOn_log_Gamma hfeq hx hx' 7
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hle
  have c7 : ((7 : ℕ) : ℝ) = (7 : ℝ) := by norm_num
  rw [c7] at hle
  have c8 : (7 : ℝ) + 1 = (8 : ℝ) := by norm_num
  rw [c8] at hle
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 7
      = (1/4 : ℝ) * Real.log 7 + Real.log 5040
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
          + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ)) := by
    have f7 : Nat.factorial 7 = 5040 := by decide
    have c7' : ((7 : ℕ) : ℝ) = (7 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = 17/4 := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = 21/4 := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = 25/4 := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = 29/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f7, c7', Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      a0, a1, a2, a3, a4, a5, a6, a7]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hpos174 : (0 : ℝ) < 17/4 := by norm_num
  have hpos214 : (0 : ℝ) < 21/4 := by norm_num
  have hpos254 : (0 : ℝ) < 25/4 := by norm_num
  have hpos294 : (0 : ℝ) < 29/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ)
      = Real.log 151412625 - 16 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4))
        + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
        + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne')
        hpos174.ne') hpos214.ne') hpos254.ne').symm
    have p : (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4) = 151412625 / 65536 := by norm_num
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) + Real.log (29/4 : ℝ)
        = Real.log 151412625 - Real.log 65536 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne')
        hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l65536 : Real.log (65536 : ℝ) = 16 * Real.log 2 := by
      have e65536 : (65536 : ℝ) = 2 ^ 16 := by norm_num
      rw [e65536, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, l65536]
  have h5040 : Real.log (5040 : ℝ)
      = 4 * Real.log 2 + 2 * Real.log 3 + Real.log 5 + Real.log 7 := by
    have e5040 : (5040 : ℝ) = ((16 * 9) * 5) * 7 := by norm_num
    have e16 : (16 : ℝ) = 2 ^ 4 := by norm_num
    have e9 : (9 : ℝ) = 3 ^ 2 := by norm_num
    rw [e5040, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e16, e9,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (151412625 : ℝ)
      = 3 * Real.log 3 + 3 * Real.log 5 + Real.log 7 + Real.log 13
        + Real.log 17 + Real.log 29 := by
    have eN : (151412625 : ℝ) = (((((27 * 125) * 7) * 13) * 17) * 29) := by
      norm_num
    have e27 : (27 : ℝ) = 3 ^ 3 := by norm_num
    have e125 : (125 : ℝ) = 5 ^ 3 := by norm_num
    rw [eN, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e27, e125,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    have e8 : (8 : ℝ) = 2 ^ 3 := by norm_num
    rw [e8, Real.log_pow]
    push_cast
    ring
  have h7 : Real.log (7 : ℝ) = Real.log 7 := rfl
  have hKup : Real.log (53383388846697594140625 : ℝ)
      = 4 * Real.log 3 + 8 * Real.log 5 + 4 * Real.log 13
        + 4 * Real.log 17 + 4 * Real.log 29 := by
    have eK : (53383388846697594140625 : ℝ)
        = ((((3 ^ 4 * 5 ^ 8) * 13 ^ 4) * 17 ^ 4) * 29 ^ 4) := by norm_num
    rw [eK, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpowC : (2 : ℝ) ^ 83 < (3.669 : ℝ) ^ 4 * 53383388846697594140625 := by
    norm_num
  have hlogC : 83 * Real.log 2
      < 4 * Real.log (3.669 : ℝ) + Real.log (53383388846697594140625 : ℝ) := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpowC
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff hGpos (by norm_num)]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_le_of_lt hle ?_
  rw [hseq, hsum, h5040, hN, h8, h7]
  linarith [hlogC, hKup]

/-- Two-sided Bohr–Mollerup `n = 7` interval: `3.548 < Γ(1/4) < 3.669`
(width `0.121`, tightening the `n = 6` interval `3.536 < Γ < 3.676`, width `0.140`). -/
theorem gamma_quarter_bounds_BM7 :
    (3.548 : ℝ) < Real.Gamma (1/4 : ℝ) ∧ Real.Gamma (1/4 : ℝ) < (3.669 : ℝ) :=
  ⟨gamma_quarter_gt_BM7, gamma_quarter_lt_BM7⟩

/-- Bohr–Mollerup `n = 8` lower bound at `x = 1/4`: `3.557 < Gamma(1/4)`
(tightens `gamma_quarter_gt_BM7`; exact `log`-of-rational value
`logΓ ≥ 25.75·log 2 - 2·log 3 - 2·log 5 - log 11 - log 13 - log 17 - log 29 ≈ 1.2691`,
i.e. `Γ ≥ (2^103/(3^8·5^8·11^4·13^4·17^4·29^4))^{1/4} ≈ 3.55760`;
new interval `3.557 < Γ(1/4) < 3.669`, width `0.112`). -/
theorem gamma_quarter_gt_BM8 : (3.557 : ℝ) < Real.Gamma (1/4 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hge := Real.BohrMollerup.ge_logGammaSeq Real.convexOn_log_Gamma hfeq hx
    (show (8 : ℕ) ≠ 0 by norm_num)
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hge
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 8
      = (1/4 : ℝ) * Real.log 8 + Real.log 40320
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
          + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)) := by
    have f8 : Nat.factorial 8 = 40320 := by decide
    have c8 : ((8 : ℕ) : ℝ) = (8 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = 17/4 := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = 21/4 := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = 25/4 := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = 29/4 := by norm_num
    have a8 : (1/4 : ℝ) + ((8 : ℕ) : ℝ) = 33/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f8, c8, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, a0, a1, a2, a3, a4, a5, a6, a7, a8]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hpos174 : (0 : ℝ) < 17/4 := by norm_num
  have hpos214 : (0 : ℝ) < 21/4 := by norm_num
  have hpos254 : (0 : ℝ) < 25/4 := by norm_num
  have hpos294 : (0 : ℝ) < 29/4 := by norm_num
  have hpos334 : (0 : ℝ) < 33/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
      = Real.log 4996616625 - 18 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4))
        + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
        + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne')
        hpos174.ne') hpos214.ne') hpos254.ne').symm
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) + Real.log (29/4 : ℝ)
        = Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne')
        hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne').symm
    have p : ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4) = 4996616625 / 262144 := by
      norm_num
    have m8 : Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) + Real.log (33/4 : ℝ)
        = Real.log 4996616625 - Real.log 262144 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne')
        hpos294.ne') hpos334.ne', p, Real.log_div (by norm_num) (by norm_num)]
    have l262144 : Real.log (262144 : ℝ) = 18 * Real.log 2 := by
      have e262144 : (262144 : ℝ) = 2 ^ 18 := by norm_num
      rw [e262144, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, m8, l262144]
  have h40320 : Real.log (40320 : ℝ)
      = 7 * Real.log 2 + 2 * Real.log 3 + Real.log 5 + Real.log 7 := by
    have e40320 : (40320 : ℝ) = ((128 * 9) * 5) * 7 := by norm_num
    have e128 : (128 : ℝ) = 2 ^ 7 := by norm_num
    have e9 : (9 : ℝ) = 3 ^ 2 := by norm_num
    rw [e40320, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e128, e9,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (4996616625 : ℝ)
      = 4 * Real.log 3 + 3 * Real.log 5 + Real.log 7 + Real.log 11
        + Real.log 13 + Real.log 17 + Real.log 29 := by
    have eN : (4996616625 : ℝ) = ((((((81 * 125) * 7) * 11) * 13) * 17) * 29) := by
      norm_num
    have e81 : (81 : ℝ) = 3 ^ 4 := by norm_num
    have e125 : (125 : ℝ) = 5 ^ 3 := by norm_num
    rw [eN, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e81, e125,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    have e8 : (8 : ℝ) = 2 ^ 3 := by norm_num
    rw [e8, Real.log_pow]
    push_cast
    ring
  have hK : Real.log (63308481884464457540844140625 : ℝ)
      = 8 * Real.log 3 + 8 * Real.log 5 + 4 * Real.log 11
        + 4 * Real.log 13 + 4 * Real.log 17 + 4 * Real.log 29 := by
    have eK : (63308481884464457540844140625 : ℝ)
        = (((((3 ^ 8 * 5 ^ 8) * 11 ^ 4) * 13 ^ 4) * 17 ^ 4) * 29 ^ 4) := by
      norm_num
    rw [eK, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  have hpow : (3.557 : ℝ) ^ 4 * 63308481884464457540844140625 < 2 ^ 103 := by
    norm_num
  have hlog4 : 4 * Real.log (3.557 : ℝ)
        + Real.log (63308481884464457540844140625 : ℝ) < 103 * Real.log 2 := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpow
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff (by norm_num) hGpos]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_lt_of_le ?_ hge
  rw [hseq, hsum, h40320, hN, h8]
  linarith [hlog4, hK]

/-- Bohr–Mollerup `n = 8` upper bound at `x = 1/4`: `Gamma(1/4) < 3.664`
(mirror of `gamma_quarter_gt_BM8`; exact value
`logΓ ≤ 25·log 2 - 1.5·log 3 - 2·log 5 - log 11 - log 13 - log 17 - log 29 ≈ 1.2985`,
i.e. `Γ ≤ (2^100/(3^6·5^8·11^4·13^4·17^4·29^4))^{1/4} ≈ 3.66391`;
new interval `3.557 < Γ(1/4) < 3.664`, width `0.107`). -/
theorem gamma_quarter_lt_BM8 : Real.Gamma (1/4 : ℝ) < (3.664 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hx' : (1/4 : ℝ) ≤ 1 := by norm_num
  have hle := Real.BohrMollerup.le_logGammaSeq Real.convexOn_log_Gamma hfeq hx hx' 8
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hle
  have c8 : ((8 : ℕ) : ℝ) = (8 : ℝ) := by norm_num
  rw [c8] at hle
  have c9 : (8 : ℝ) + 1 = (9 : ℝ) := by norm_num
  rw [c9] at hle
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 8
      = (1/4 : ℝ) * Real.log 8 + Real.log 40320
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
          + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)) := by
    have f8 : Nat.factorial 8 = 40320 := by decide
    have c8' : ((8 : ℕ) : ℝ) = (8 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = 17/4 := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = 21/4 := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = 25/4 := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = 29/4 := by norm_num
    have a8 : (1/4 : ℝ) + ((8 : ℕ) : ℝ) = 33/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f8, c8', Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, a0, a1, a2, a3, a4, a5, a6, a7, a8]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hpos174 : (0 : ℝ) < 17/4 := by norm_num
  have hpos214 : (0 : ℝ) < 21/4 := by norm_num
  have hpos254 : (0 : ℝ) < 25/4 := by norm_num
  have hpos294 : (0 : ℝ) < 29/4 := by norm_num
  have hpos334 : (0 : ℝ) < 33/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
      = Real.log 4996616625 - 18 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4))
        + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
        + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne')
        hpos174.ne') hpos214.ne') hpos254.ne').symm
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) + Real.log (29/4 : ℝ)
        = Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne')
        hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne').symm
    have p : ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4) = 4996616625 / 262144 := by
      norm_num
    have m8 : Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) + Real.log (33/4 : ℝ)
        = Real.log 4996616625 - Real.log 262144 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne')
        hpos294.ne') hpos334.ne', p, Real.log_div (by norm_num) (by norm_num)]
    have l262144 : Real.log (262144 : ℝ) = 18 * Real.log 2 := by
      have e262144 : (262144 : ℝ) = 2 ^ 18 := by norm_num
      rw [e262144, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, m8, l262144]
  have h40320 : Real.log (40320 : ℝ)
      = 7 * Real.log 2 + 2 * Real.log 3 + Real.log 5 + Real.log 7 := by
    have e40320 : (40320 : ℝ) = ((128 * 9) * 5) * 7 := by norm_num
    have e128 : (128 : ℝ) = 2 ^ 7 := by norm_num
    have e9 : (9 : ℝ) = 3 ^ 2 := by norm_num
    rw [e40320, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e128, e9,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (4996616625 : ℝ)
      = 4 * Real.log 3 + 3 * Real.log 5 + Real.log 7 + Real.log 11
        + Real.log 13 + Real.log 17 + Real.log 29 := by
    have eN : (4996616625 : ℝ) = ((((((81 * 125) * 7) * 11) * 13) * 17) * 29) := by
      norm_num
    have e81 : (81 : ℝ) = 3 ^ 4 := by norm_num
    have e125 : (125 : ℝ) = 5 ^ 3 := by norm_num
    rw [eN, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e81, e125,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    have e8 : (8 : ℝ) = 2 ^ 3 := by norm_num
    rw [e8, Real.log_pow]
    push_cast
    ring
  have h9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    have e9 : (9 : ℝ) = 3 ^ 2 := by norm_num
    rw [e9, Real.log_pow]
    push_cast
    ring
  have hKup : Real.log (7034275764940495282316015625 : ℝ)
      = 6 * Real.log 3 + 8 * Real.log 5 + 4 * Real.log 11
        + 4 * Real.log 13 + 4 * Real.log 17 + 4 * Real.log 29 := by
    have eK : (7034275764940495282316015625 : ℝ)
        = (((((3 ^ 6 * 5 ^ 8) * 11 ^ 4) * 13 ^ 4) * 17 ^ 4) * 29 ^ 4) := by
      norm_num
    rw [eK, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  have hpowC : (2 : ℝ) ^ 100 < (3.664 : ℝ) ^ 4 * 7034275764940495282316015625 := by
    norm_num
  have hlogC : 100 * Real.log 2
      < 4 * Real.log (3.664 : ℝ) + Real.log (7034275764940495282316015625 : ℝ) := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpowC
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff hGpos (by norm_num)]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_le_of_lt hle ?_
  rw [hseq, hsum, h40320, hN, h8, h9]
  linarith [hlogC, hKup]

/-- Two-sided Bohr–Mollerup `n = 8` interval: `3.557 < Γ(1/4) < 3.664`
(width `0.107`, tightening the `n = 7` interval `3.548 < Γ < 3.669`, width `0.121`). -/
theorem gamma_quarter_bounds_BM8 :
    (3.557 : ℝ) < Real.Gamma (1/4 : ℝ) ∧ Real.Gamma (1/4 : ℝ) < (3.664 : ℝ) :=
  ⟨gamma_quarter_gt_BM8, gamma_quarter_lt_BM8⟩

/-- Bohr–Mollerup `n = 9` lower bound at `x = 1/4`: `3.564 < Gamma(1/4)`
(tightens `gamma_quarter_gt_BM8`; exact `log`-of-rational value
`logΓ ≥ 27·log 2 + 0.5·log 3 - 2·log 5 - log 11 - log 13 - log 17 - log 29
- log 37 ≈ 1.2711`,
i.e. `Γ ≥ (2^108·3^2/(5^8·11^4·13^4·17^4·29^4·37^4))^{1/4} ≈ 3.56489`;
new interval `3.564 < Γ(1/4) < 3.664`, width `0.100`). -/
theorem gamma_quarter_gt_BM9 : (3.564 : ℝ) < Real.Gamma (1/4 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hge := Real.BohrMollerup.ge_logGammaSeq Real.convexOn_log_Gamma hfeq hx
    (show (9 : ℕ) ≠ 0 by norm_num)
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hge
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 9
      = (1/4 : ℝ) * Real.log 9 + Real.log 362880
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
          + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
          + Real.log (37/4 : ℝ)) := by
    have f9 : Nat.factorial 9 = 362880 := by decide
    have c9 : ((9 : ℕ) : ℝ) = (9 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = 17/4 := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = 21/4 := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = 25/4 := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = 29/4 := by norm_num
    have a8 : (1/4 : ℝ) + ((8 : ℕ) : ℝ) = 33/4 := by norm_num
    have a9 : (1/4 : ℝ) + ((9 : ℕ) : ℝ) = 37/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f9, c9, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hpos174 : (0 : ℝ) < 17/4 := by norm_num
  have hpos214 : (0 : ℝ) < 21/4 := by norm_num
  have hpos254 : (0 : ℝ) < 25/4 := by norm_num
  have hpos294 : (0 : ℝ) < 29/4 := by norm_num
  have hpos334 : (0 : ℝ) < 33/4 := by norm_num
  have hpos374 : (0 : ℝ) < 37/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
        + Real.log (37/4 : ℝ)
      = Real.log 184874815125 - 20 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4))
        + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
        + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne')
        hpos174.ne') hpos214.ne') hpos254.ne').symm
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) + Real.log (29/4 : ℝ)
        = Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne')
        hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne').symm
    have m8 : Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) + Real.log (33/4 : ℝ)
        = Real.log (((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne')
        hpos294.ne') hpos334.ne').symm
    have p : (((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)
        = 184874815125 / 1048576 := by norm_num
    have m9 : Real.log (((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) + Real.log (37/4 : ℝ)
        = Real.log 184874815125 - Real.log 1048576 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne')
        hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l1048576 : Real.log (1048576 : ℝ) = 20 * Real.log 2 := by
      have e1048576 : (1048576 : ℝ) = 2 ^ 20 := by norm_num
      rw [e1048576, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, m8, m9, l1048576]
  have h362880 : Real.log (362880 : ℝ)
      = 7 * Real.log 2 + 4 * Real.log 3 + Real.log 5 + Real.log 7 := by
    have e362880 : (362880 : ℝ) = ((128 * 81) * 5) * 7 := by norm_num
    have e128 : (128 : ℝ) = 2 ^ 7 := by norm_num
    have e81 : (81 : ℝ) = 3 ^ 4 := by norm_num
    rw [e362880, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e128, e81,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (184874815125 : ℝ)
      = 4 * Real.log 3 + 3 * Real.log 5 + Real.log 7 + Real.log 11
        + Real.log 13 + Real.log 17 + Real.log 29 + Real.log 37 := by
    have eN : (184874815125 : ℝ)
        = (((((((81 * 125) * 7) * 11) * 13) * 17) * 29) * 37) := by norm_num
    have e81 : (81 : ℝ) = 3 ^ 4 := by norm_num
    have e125 : (125 : ℝ) = 5 ^ 3 := by norm_num
    rw [eN, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e81, e125,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    have e9 : (9 : ℝ) = 3 ^ 2 := by norm_num
    rw [e9, Real.log_pow]
    push_cast
    ring
  have hK : Real.log (18084177368856849902332875390625 : ℝ)
      = 8 * Real.log 5 + 4 * Real.log 11 + 4 * Real.log 13
        + 4 * Real.log 17 + 4 * Real.log 29 + 4 * Real.log 37 := by
    have eK : (18084177368856849902332875390625 : ℝ)
        = (((((5 ^ 8 * 11 ^ 4) * 13 ^ 4) * 17 ^ 4) * 29 ^ 4) * 37 ^ 4) := by
      norm_num
    rw [eK, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  have hpow : (3.564 : ℝ) ^ 4 * 18084177368856849902332875390625
      < 2 ^ 108 * 3 ^ 2 := by norm_num
  have hlog4 : 4 * Real.log (3.564 : ℝ)
        + Real.log (18084177368856849902332875390625 : ℝ)
      < 108 * Real.log 2 + 2 * Real.log 3 := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpow
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff (by norm_num) hGpos]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_lt_of_le ?_ hge
  rw [hseq, hsum, h362880, hN, h9]
  linarith [hlog4, hK]

/-- Bohr–Mollerup `n = 9` upper bound at `x = 1/4`: `Gamma(1/4) < 3.661`
(mirror of `gamma_quarter_gt_BM9`; exact value
`logΓ ≤ 27.25·log 2 - 1.75·log 5 - log 11 - log 13 - log 17 - log 29
- log 37 ≈ 1.2975`,
i.e. `Γ ≤ (2^109/(5^7·11^4·13^4·17^4·29^4·37^4))^{1/4} ≈ 3.66003`;
new interval `3.564 < Γ(1/4) < 3.661`, width `0.097`). -/
theorem gamma_quarter_lt_BM9 : Real.Gamma (1/4 : ℝ) < (3.661 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hx' : (1/4 : ℝ) ≤ 1 := by norm_num
  have hle := Real.BohrMollerup.le_logGammaSeq Real.convexOn_log_Gamma hfeq hx hx' 9
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hle
  have c9 : ((9 : ℕ) : ℝ) = (9 : ℝ) := by norm_num
  rw [c9] at hle
  have c10 : (9 : ℝ) + 1 = (10 : ℝ) := by norm_num
  rw [c10] at hle
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 9
      = (1/4 : ℝ) * Real.log 9 + Real.log 362880
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
          + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
          + Real.log (37/4 : ℝ)) := by
    have f9 : Nat.factorial 9 = 362880 := by decide
    have c9' : ((9 : ℕ) : ℝ) = (9 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = 17/4 := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = 21/4 := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = 25/4 := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = 29/4 := by norm_num
    have a8 : (1/4 : ℝ) + ((8 : ℕ) : ℝ) = 33/4 := by norm_num
    have a9 : (1/4 : ℝ) + ((9 : ℕ) : ℝ) = 37/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f9, c9', Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hpos174 : (0 : ℝ) < 17/4 := by norm_num
  have hpos214 : (0 : ℝ) < 21/4 := by norm_num
  have hpos254 : (0 : ℝ) < 25/4 := by norm_num
  have hpos294 : (0 : ℝ) < 29/4 := by norm_num
  have hpos334 : (0 : ℝ) < 33/4 := by norm_num
  have hpos374 : (0 : ℝ) < 37/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
        + Real.log (37/4 : ℝ)
      = Real.log 184874815125 - 20 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4))
        + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
        + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne')
        hpos174.ne') hpos214.ne') hpos254.ne').symm
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) + Real.log (29/4 : ℝ)
        = Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne')
        hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne').symm
    have m8 : Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) + Real.log (33/4 : ℝ)
        = Real.log (((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne')
        hpos294.ne') hpos334.ne').symm
    have p : (((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)
        = 184874815125 / 1048576 := by norm_num
    have m9 : Real.log (((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) + Real.log (37/4 : ℝ)
        = Real.log 184874815125 - Real.log 1048576 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne')
        hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l1048576 : Real.log (1048576 : ℝ) = 20 * Real.log 2 := by
      have e1048576 : (1048576 : ℝ) = 2 ^ 20 := by norm_num
      rw [e1048576, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, m8, m9, l1048576]
  have h362880 : Real.log (362880 : ℝ)
      = 7 * Real.log 2 + 4 * Real.log 3 + Real.log 5 + Real.log 7 := by
    have e362880 : (362880 : ℝ) = ((128 * 81) * 5) * 7 := by norm_num
    have e128 : (128 : ℝ) = 2 ^ 7 := by norm_num
    have e81 : (81 : ℝ) = 3 ^ 4 := by norm_num
    rw [e362880, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e128, e81,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (184874815125 : ℝ)
      = 4 * Real.log 3 + 3 * Real.log 5 + Real.log 7 + Real.log 11
        + Real.log 13 + Real.log 17 + Real.log 29 + Real.log 37 := by
    have eN : (184874815125 : ℝ)
        = (((((((81 * 125) * 7) * 11) * 13) * 17) * 29) * 37) := by norm_num
    have e81 : (81 : ℝ) = 3 ^ 4 := by norm_num
    have e125 : (125 : ℝ) = 5 ^ 3 := by norm_num
    rw [eN, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e81, e125,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    have e9 : (9 : ℝ) = 3 ^ 2 := by norm_num
    rw [e9, Real.log_pow]
    push_cast
    ring
  have h10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    have e10 : (10 : ℝ) = 2 * 5 := by norm_num
    rw [e10, Real.log_mul (by norm_num) (by norm_num)]
  have hKup : Real.log (3616835473771369980466575078125 : ℝ)
      = 7 * Real.log 5 + 4 * Real.log 11 + 4 * Real.log 13
        + 4 * Real.log 17 + 4 * Real.log 29 + 4 * Real.log 37 := by
    have eK : (3616835473771369980466575078125 : ℝ)
        = (((((5 ^ 7 * 11 ^ 4) * 13 ^ 4) * 17 ^ 4) * 29 ^ 4) * 37 ^ 4) := by
      norm_num
    rw [eK, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  have hpowC : (2 : ℝ) ^ 109 < (3.661 : ℝ) ^ 4 * 3616835473771369980466575078125 := by
    norm_num
  have hlogC : 109 * Real.log 2
      < 4 * Real.log (3.661 : ℝ) + Real.log (3616835473771369980466575078125 : ℝ) := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpowC
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff hGpos (by norm_num)]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_le_of_lt hle ?_
  rw [hseq, hsum, h362880, hN, h9, h10]
  linarith [hlogC, hKup]

/-- Two-sided Bohr–Mollerup `n = 9` interval: `3.564 < Γ(1/4) < 3.661`
(width `0.097`, tightening the `n = 8` interval `3.557 < Γ < 3.664`, width `0.107`). -/
theorem gamma_quarter_bounds_BM9 :
    (3.564 : ℝ) < Real.Gamma (1/4 : ℝ) ∧ Real.Gamma (1/4 : ℝ) < (3.661 : ℝ) :=
  ⟨gamma_quarter_gt_BM9, gamma_quarter_lt_BM9⟩

/-- Bohr–Mollerup `n = 10` lower bound at `x = 1/4`: `3.570 < Gamma(1/4)`
(tightens `gamma_quarter_gt_BM9`; exact `log`-of-rational value
`logΓ ≥ 30.25·log 2 - 0.75·log 5 - log 11 - log 13 - log 17 - log 29
- log 37 - log 41 ≈ 1.2728`,
i.e. `Γ ≥ (2^121/(5^3·11^4·13^4·17^4·29^4·37^4·41^4))^{1/4} ≈ 3.57077`;
new interval `3.570 < Γ(1/4) < 3.661`, width `0.091`). -/
theorem gamma_quarter_gt_BM10 : (3.570 : ℝ) < Real.Gamma (1/4 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hge := Real.BohrMollerup.ge_logGammaSeq Real.convexOn_log_Gamma hfeq hx
    (show (10 : ℕ) ≠ 0 by norm_num)
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hge
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 10
      = (1/4 : ℝ) * Real.log 10 + Real.log 3628800
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
          + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
          + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ)) := by
    have f10 : Nat.factorial 10 = 3628800 := by decide
    have c10 : ((10 : ℕ) : ℝ) = (10 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = 17/4 := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = 21/4 := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = 25/4 := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = 29/4 := by norm_num
    have a8 : (1/4 : ℝ) + ((8 : ℕ) : ℝ) = 33/4 := by norm_num
    have a9 : (1/4 : ℝ) + ((9 : ℕ) : ℝ) = 37/4 := by norm_num
    have a10 : (1/4 : ℝ) + ((10 : ℕ) : ℝ) = 41/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f10, c10, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hpos174 : (0 : ℝ) < 17/4 := by norm_num
  have hpos214 : (0 : ℝ) < 21/4 := by norm_num
  have hpos254 : (0 : ℝ) < 25/4 := by norm_num
  have hpos294 : (0 : ℝ) < 29/4 := by norm_num
  have hpos334 : (0 : ℝ) < 33/4 := by norm_num
  have hpos374 : (0 : ℝ) < 37/4 := by norm_num
  have hpos414 : (0 : ℝ) < 41/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
        + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ)
      = Real.log 7579867420125 - 22 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4))
        + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
        + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne')
        hpos174.ne') hpos214.ne') hpos254.ne').symm
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) + Real.log (29/4 : ℝ)
        = Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne')
        hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne').symm
    have m8 : Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) + Real.log (33/4 : ℝ)
        = Real.log (((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne')
        hpos294.ne') hpos334.ne').symm
    have m9 : Real.log (((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) + Real.log (37/4 : ℝ)
        = Real.log ((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne')
        hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne').symm
    have p : ((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) * (41/4)
        = 7579867420125 / 4194304 := by norm_num
    have m10 : Real.log ((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4))
        + Real.log (41/4 : ℝ)
        = Real.log 7579867420125 - Real.log 4194304 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne')
        hpos414.ne', p, Real.log_div (by norm_num) (by norm_num)]
    have l4194304 : Real.log (4194304 : ℝ) = 22 * Real.log 2 := by
      have e4194304 : (4194304 : ℝ) = 2 ^ 22 := by norm_num
      rw [e4194304, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, l4194304]
  have h3628800 : Real.log (3628800 : ℝ)
      = 8 * Real.log 2 + 4 * Real.log 3 + 2 * Real.log 5 + Real.log 7 := by
    have e3628800 : (3628800 : ℝ) = ((256 * 81) * 25) * 7 := by norm_num
    have e256 : (256 : ℝ) = 2 ^ 8 := by norm_num
    have e81 : (81 : ℝ) = 3 ^ 4 := by norm_num
    have e25 : (25 : ℝ) = 5 ^ 2 := by norm_num
    rw [e3628800, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e256, e81, e25,
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (7579867420125 : ℝ)
      = 4 * Real.log 3 + 3 * Real.log 5 + Real.log 7 + Real.log 11
        + Real.log 13 + Real.log 17 + Real.log 29 + Real.log 37
        + Real.log 41 := by
    have eN : (7579867420125 : ℝ)
        = ((((((((81 * 125) * 7) * 11) * 13) * 17) * 29) * 37) * 41) := by
      norm_num
    have e81 : (81 : ℝ) = 3 ^ 4 := by norm_num
    have e125 : (125 : ℝ) = 5 ^ 3 := by norm_num
    rw [eN, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e81, e125,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    have e10 : (10 : ℝ) = 2 * 5 := by norm_num
    rw [e10, Real.log_mul (by norm_num) (by norm_num)]
  have hK : Real.log (16352500200319456331797135454940125 : ℝ)
      = 3 * Real.log 5 + 4 * Real.log 11 + 4 * Real.log 13
        + 4 * Real.log 17 + 4 * Real.log 29 + 4 * Real.log 37
        + 4 * Real.log 41 := by
    have eK : (16352500200319456331797135454940125 : ℝ)
        = ((((((5 ^ 3 * 11 ^ 4) * 13 ^ 4) * 17 ^ 4) * 29 ^ 4) * 37 ^ 4)
          * 41 ^ 4) := by norm_num
    rw [eK, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpow : (3.570 : ℝ) ^ 4 * 16352500200319456331797135454940125
      < 2 ^ 121 := by norm_num
  have hlog4 : 4 * Real.log (3.570 : ℝ)
        + Real.log (16352500200319456331797135454940125 : ℝ)
      < 121 * Real.log 2 := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpow
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff (by norm_num) hGpos]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_lt_of_le ?_ hge
  rw [hseq, hsum, h3628800, hN, h10]
  linarith [hlog4, hK]

/-- Bohr–Mollerup `n = 10` upper bound at `x = 1/4`: `Gamma(1/4) < 3.657`
(mirror of `gamma_quarter_gt_BM10`; exact value
`logΓ ≤ 30·log 2 - log 5 - 0.75·log 11 - log 13 - log 17 - log 29
- log 37 - log 41 ≈ 1.2966`,
i.e. `Γ ≤ (2^120/(5^4·11^3·13^4·17^4·29^4·37^4·41^4))^{1/4} ≈ 3.65687`;
new interval `3.570 < Γ(1/4) < 3.657`, width `0.087`). -/
theorem gamma_quarter_lt_BM10 : Real.Gamma (1/4 : ℝ) < (3.657 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hx' : (1/4 : ℝ) ≤ 1 := by norm_num
  have hle := Real.BohrMollerup.le_logGammaSeq Real.convexOn_log_Gamma hfeq hx hx' 10
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hle
  have c10 : ((10 : ℕ) : ℝ) = (10 : ℝ) := by norm_num
  rw [c10] at hle
  have c11 : (10 : ℝ) + 1 = (11 : ℝ) := by norm_num
  rw [c11] at hle
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 10
      = (1/4 : ℝ) * Real.log 10 + Real.log 3628800
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
          + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
          + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ)) := by
    have f10 : Nat.factorial 10 = 3628800 := by decide
    have c10' : ((10 : ℕ) : ℝ) = (10 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = 17/4 := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = 21/4 := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = 25/4 := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = 29/4 := by norm_num
    have a8 : (1/4 : ℝ) + ((8 : ℕ) : ℝ) = 33/4 := by norm_num
    have a9 : (1/4 : ℝ) + ((9 : ℕ) : ℝ) = 37/4 := by norm_num
    have a10 : (1/4 : ℝ) + ((10 : ℕ) : ℝ) = 41/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f10, c10', Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hpos174 : (0 : ℝ) < 17/4 := by norm_num
  have hpos214 : (0 : ℝ) < 21/4 := by norm_num
  have hpos254 : (0 : ℝ) < 25/4 := by norm_num
  have hpos294 : (0 : ℝ) < 29/4 := by norm_num
  have hpos334 : (0 : ℝ) < 33/4 := by norm_num
  have hpos374 : (0 : ℝ) < 37/4 := by norm_num
  have hpos414 : (0 : ℝ) < 41/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
        + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ)
      = Real.log 7579867420125 - 22 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4))
        + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
        + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne')
        hpos174.ne') hpos214.ne') hpos254.ne').symm
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) + Real.log (29/4 : ℝ)
        = Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne')
        hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne').symm
    have m8 : Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) + Real.log (33/4 : ℝ)
        = Real.log (((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne')
        hpos294.ne') hpos334.ne').symm
    have m9 : Real.log (((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) + Real.log (37/4 : ℝ)
        = Real.log ((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne')
        hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne').symm
    have p : ((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) * (41/4)
        = 7579867420125 / 4194304 := by norm_num
    have m10 : Real.log ((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4))
        + Real.log (41/4 : ℝ)
        = Real.log 7579867420125 - Real.log 4194304 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne')
        hpos414.ne', p, Real.log_div (by norm_num) (by norm_num)]
    have l4194304 : Real.log (4194304 : ℝ) = 22 * Real.log 2 := by
      have e4194304 : (4194304 : ℝ) = 2 ^ 22 := by norm_num
      rw [e4194304, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, l4194304]
  have h3628800 : Real.log (3628800 : ℝ)
      = 8 * Real.log 2 + 4 * Real.log 3 + 2 * Real.log 5 + Real.log 7 := by
    have e3628800 : (3628800 : ℝ) = ((256 * 81) * 25) * 7 := by norm_num
    have e256 : (256 : ℝ) = 2 ^ 8 := by norm_num
    have e81 : (81 : ℝ) = 3 ^ 4 := by norm_num
    have e25 : (25 : ℝ) = 5 ^ 2 := by norm_num
    rw [e3628800, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e256, e81, e25,
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (7579867420125 : ℝ)
      = 4 * Real.log 3 + 3 * Real.log 5 + Real.log 7 + Real.log 11
        + Real.log 13 + Real.log 17 + Real.log 29 + Real.log 37
        + Real.log 41 := by
    have eN : (7579867420125 : ℝ)
        = ((((((((81 * 125) * 7) * 11) * 13) * 17) * 29) * 37) * 41) := by
      norm_num
    have e81 : (81 : ℝ) = 3 ^ 4 := by norm_num
    have e125 : (125 : ℝ) = 5 ^ 3 := by norm_num
    rw [eN, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e81, e125,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    have e10 : (10 : ℝ) = 2 * 5 := by norm_num
    rw [e10, Real.log_mul (by norm_num) (by norm_num)]
  have h11 : Real.log (11 : ℝ) = Real.log 11 := rfl
  have hKup : Real.log (7432954636508843787180516115881875 : ℝ)
      = 4 * Real.log 5 + 3 * Real.log 11 + 4 * Real.log 13
        + 4 * Real.log 17 + 4 * Real.log 29 + 4 * Real.log 37
        + 4 * Real.log 41 := by
    have eK : (7432954636508843787180516115881875 : ℝ)
        = ((((((5 ^ 4 * 11 ^ 3) * 13 ^ 4) * 17 ^ 4) * 29 ^ 4) * 37 ^ 4)
          * 41 ^ 4) := by norm_num
    rw [eK, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpowC : (2 : ℝ) ^ 120 < (3.657 : ℝ) ^ 4 * 7432954636508843787180516115881875 := by
    norm_num
  have hlogC : 120 * Real.log 2
      < 4 * Real.log (3.657 : ℝ) + Real.log (7432954636508843787180516115881875 : ℝ) := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpowC
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff hGpos (by norm_num)]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_le_of_lt hle ?_
  rw [hseq, hsum, h3628800, hN, h10, h11]
  linarith [hlogC, hKup]

/-- Two-sided Bohr–Mollerup `n = 10` interval: `3.570 < Γ(1/4) < 3.657`
(width `0.087`, tightening the `n = 9` interval `3.564 < Γ < 3.661`, width `0.097`). -/
theorem gamma_quarter_bounds_BM10 :
    (3.570 : ℝ) < Real.Gamma (1/4 : ℝ) ∧ Real.Gamma (1/4 : ℝ) < (3.657 : ℝ) :=
  ⟨gamma_quarter_gt_BM10, gamma_quarter_lt_BM10⟩

/-- Bohr–Mollerup `n = 11` lower bound at `x = 1/4`: `3.575 < Gamma(1/4)`
(tightens `gamma_quarter_gt_BM10`; exact `log`-of-rational value
`logΓ ≥ 32·log 2 - 2·log 3 - 2·log 5 + 0.25·log 11 - log 13 - log 17
- log 29 - log 37 - log 41 ≈ 1.2744`,
i.e. `Γ ≥ (2^128·11/(3^8·5^8·13^4·17^4·29^4·37^4·41^4))^{1/4} ≈ 3.57561`;
new interval `3.575 < Γ(1/4) < 3.657`, width `0.082`). -/
theorem gamma_quarter_gt_BM11 : (3.575 : ℝ) < Real.Gamma (1/4 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hge := Real.BohrMollerup.ge_logGammaSeq Real.convexOn_log_Gamma hfeq hx
    (show (11 : ℕ) ≠ 0 by norm_num)
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hge
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 11
      = (1/4 : ℝ) * Real.log 11 + Real.log 39916800
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
          + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
          + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ)
          + Real.log (45/4 : ℝ)) := by
    have f11 : Nat.factorial 11 = 39916800 := by decide
    have c11 : ((11 : ℕ) : ℝ) = (11 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = 17/4 := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = 21/4 := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = 25/4 := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = 29/4 := by norm_num
    have a8 : (1/4 : ℝ) + ((8 : ℕ) : ℝ) = 33/4 := by norm_num
    have a9 : (1/4 : ℝ) + ((9 : ℕ) : ℝ) = 37/4 := by norm_num
    have a10 : (1/4 : ℝ) + ((10 : ℕ) : ℝ) = 41/4 := by norm_num
    have a11 : (1/4 : ℝ) + ((11 : ℕ) : ℝ) = 45/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f11, c11, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hpos174 : (0 : ℝ) < 17/4 := by norm_num
  have hpos214 : (0 : ℝ) < 21/4 := by norm_num
  have hpos254 : (0 : ℝ) < 25/4 := by norm_num
  have hpos294 : (0 : ℝ) < 29/4 := by norm_num
  have hpos334 : (0 : ℝ) < 33/4 := by norm_num
  have hpos374 : (0 : ℝ) < 37/4 := by norm_num
  have hpos414 : (0 : ℝ) < 41/4 := by norm_num
  have hpos454 : (0 : ℝ) < 45/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
        + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ)
      = Real.log 341094033905625 - 24 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4))
        + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
        + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne')
        hpos174.ne') hpos214.ne') hpos254.ne').symm
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) + Real.log (29/4 : ℝ)
        = Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne')
        hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne').symm
    have m8 : Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) + Real.log (33/4 : ℝ)
        = Real.log (((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne')
        hpos294.ne') hpos334.ne').symm
    have m9 : Real.log (((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) + Real.log (37/4 : ℝ)
        = Real.log ((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne')
        hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne').symm
    have m10 : Real.log ((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4))
        + Real.log (41/4 : ℝ)
        = Real.log (((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) * (41/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne')
        hpos414.ne').symm
    have p : (((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) * (41/4))
          * (45/4)
        = 341094033905625 / 16777216 := by norm_num
    have m11 : Real.log (((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) * (41/4))
        + Real.log (45/4 : ℝ)
        = Real.log 341094033905625 - Real.log 16777216 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne')
        hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne')
        hpos374.ne') hpos414.ne') hpos454.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l16777216 : Real.log (16777216 : ℝ) = 24 * Real.log 2 := by
      have e16777216 : (16777216 : ℝ) = 2 ^ 24 := by norm_num
      rw [e16777216, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, l16777216]
  have h39916800 : Real.log (39916800 : ℝ)
      = 8 * Real.log 2 + 4 * Real.log 3 + 2 * Real.log 5 + Real.log 7
        + Real.log 11 := by
    have e39916800 : (39916800 : ℝ) = ((((256 * 81) * 25) * 7) * 11) := by
      norm_num
    have e256 : (256 : ℝ) = 2 ^ 8 := by norm_num
    have e81 : (81 : ℝ) = 3 ^ 4 := by norm_num
    have e25 : (25 : ℝ) = 5 ^ 2 := by norm_num
    rw [e39916800, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e256, e81, e25,
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (341094033905625 : ℝ)
      = 6 * Real.log 3 + 4 * Real.log 5 + Real.log 7 + Real.log 11
        + Real.log 13 + Real.log 17 + Real.log 29 + Real.log 37
        + Real.log 41 := by
    have eN : (341094033905625 : ℝ)
        = ((((((((729 * 625) * 7) * 11) * 13) * 17) * 29) * 37) * 41) := by
      norm_num
    have e729 : (729 : ℝ) = 3 ^ 6 := by norm_num
    have e625 : (625 : ℝ) = 5 ^ 4 := by norm_num
    rw [eN, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e729, e625,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hK : Real.log (22899894520160839635467395866031640625 : ℝ)
      = 8 * Real.log 3 + 8 * Real.log 5 + 4 * Real.log 13
        + 4 * Real.log 17 + 4 * Real.log 29 + 4 * Real.log 37
        + 4 * Real.log 41 := by
    have eK : (22899894520160839635467395866031640625 : ℝ)
        = ((((((3 ^ 8 * 5 ^ 8) * 13 ^ 4) * 17 ^ 4) * 29 ^ 4) * 37 ^ 4)
          * 41 ^ 4) := by norm_num
    rw [eK, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpow : (3.575 : ℝ) ^ 4 * 22899894520160839635467395866031640625
      < 2 ^ 128 * 11 := by norm_num
  have hlog4 : 4 * Real.log (3.575 : ℝ)
        + Real.log (22899894520160839635467395866031640625 : ℝ)
      < 128 * Real.log 2 + Real.log 11 := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpow
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff (by norm_num) hGpos]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_lt_of_le ?_ hge
  rw [hseq, hsum, h39916800, hN]
  linarith [hlog4, hK]

/-- Bohr–Mollerup `n = 11` upper bound at `x = 1/4`: `Gamma(1/4) < 3.655`
(mirror of `gamma_quarter_gt_BM11`; exact value
`logΓ ≤ 32.5·log 2 - 1.75·log 3 - 2·log 5 - log 13 - log 17 - log 29
- log 37 - log 41 ≈ 1.2961`,
i.e. `Γ ≤ (2^130/(3^7·5^8·13^4·17^4·29^4·37^4·41^4))^{1/4} ≈ 3.65424`;
new interval `3.575 < Γ(1/4) < 3.655`, width `0.080`). -/
theorem gamma_quarter_lt_BM11 : Real.Gamma (1/4 : ℝ) < (3.655 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hx' : (1/4 : ℝ) ≤ 1 := by norm_num
  have hle := Real.BohrMollerup.le_logGammaSeq Real.convexOn_log_Gamma hfeq hx hx' 11
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hle
  have c11 : ((11 : ℕ) : ℝ) = (11 : ℝ) := by norm_num
  rw [c11] at hle
  have c12 : (11 : ℝ) + 1 = (12 : ℝ) := by norm_num
  rw [c12] at hle
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 11
      = (1/4 : ℝ) * Real.log 11 + Real.log 39916800
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
          + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
          + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ)
          + Real.log (45/4 : ℝ)) := by
    have f11 : Nat.factorial 11 = 39916800 := by decide
    have c11' : ((11 : ℕ) : ℝ) = (11 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = 17/4 := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = 21/4 := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = 25/4 := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = 29/4 := by norm_num
    have a8 : (1/4 : ℝ) + ((8 : ℕ) : ℝ) = 33/4 := by norm_num
    have a9 : (1/4 : ℝ) + ((9 : ℕ) : ℝ) = 37/4 := by norm_num
    have a10 : (1/4 : ℝ) + ((10 : ℕ) : ℝ) = 41/4 := by norm_num
    have a11 : (1/4 : ℝ) + ((11 : ℕ) : ℝ) = 45/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f11, c11', Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hpos174 : (0 : ℝ) < 17/4 := by norm_num
  have hpos214 : (0 : ℝ) < 21/4 := by norm_num
  have hpos254 : (0 : ℝ) < 25/4 := by norm_num
  have hpos294 : (0 : ℝ) < 29/4 := by norm_num
  have hpos334 : (0 : ℝ) < 33/4 := by norm_num
  have hpos374 : (0 : ℝ) < 37/4 := by norm_num
  have hpos414 : (0 : ℝ) < 41/4 := by norm_num
  have hpos454 : (0 : ℝ) < 45/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
        + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ)
      = Real.log 341094033905625 - 24 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4))
        + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
        + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne')
        hpos174.ne') hpos214.ne') hpos254.ne').symm
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) + Real.log (29/4 : ℝ)
        = Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne')
        hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne').symm
    have m8 : Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) + Real.log (33/4 : ℝ)
        = Real.log (((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne')
        hpos294.ne') hpos334.ne').symm
    have m9 : Real.log (((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) + Real.log (37/4 : ℝ)
        = Real.log ((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne')
        hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne').symm
    have m10 : Real.log ((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4))
        + Real.log (41/4 : ℝ)
        = Real.log (((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) * (41/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne')
        hpos414.ne').symm
    have p : (((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) * (41/4))
          * (45/4)
        = 341094033905625 / 16777216 := by norm_num
    have m11 : Real.log (((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) * (41/4))
        + Real.log (45/4 : ℝ)
        = Real.log 341094033905625 - Real.log 16777216 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne')
        hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne')
        hpos374.ne') hpos414.ne') hpos454.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l16777216 : Real.log (16777216 : ℝ) = 24 * Real.log 2 := by
      have e16777216 : (16777216 : ℝ) = 2 ^ 24 := by norm_num
      rw [e16777216, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, l16777216]
  have h39916800 : Real.log (39916800 : ℝ)
      = 8 * Real.log 2 + 4 * Real.log 3 + 2 * Real.log 5 + Real.log 7
        + Real.log 11 := by
    have e39916800 : (39916800 : ℝ) = ((((256 * 81) * 25) * 7) * 11) := by
      norm_num
    have e256 : (256 : ℝ) = 2 ^ 8 := by norm_num
    have e81 : (81 : ℝ) = 3 ^ 4 := by norm_num
    have e25 : (25 : ℝ) = 5 ^ 2 := by norm_num
    rw [e39916800, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e256, e81, e25,
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (341094033905625 : ℝ)
      = 6 * Real.log 3 + 4 * Real.log 5 + Real.log 7 + Real.log 11
        + Real.log 13 + Real.log 17 + Real.log 29 + Real.log 37
        + Real.log 41 := by
    have eN : (341094033905625 : ℝ)
        = ((((((((729 * 625) * 7) * 11) * 13) * 17) * 29) * 37) * 41) := by
      norm_num
    have e729 : (729 : ℝ) = 3 ^ 6 := by norm_num
    have e625 : (625 : ℝ) = 5 ^ 4 := by norm_num
    rw [eN, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e729, e625,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h12 : Real.log (12 : ℝ) = 2 * Real.log 2 + Real.log 3 := by
    have e12 : (12 : ℝ) = 4 * 3 := by norm_num
    have e4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [e12, Real.log_mul (by norm_num) (by norm_num), e4, Real.log_pow]
    push_cast
    ring
  have hKup : Real.log (7633298173386946545155798622010546875 : ℝ)
      = 7 * Real.log 3 + 8 * Real.log 5 + 4 * Real.log 13
        + 4 * Real.log 17 + 4 * Real.log 29 + 4 * Real.log 37
        + 4 * Real.log 41 := by
    have eK : (7633298173386946545155798622010546875 : ℝ)
        = ((((((3 ^ 7 * 5 ^ 8) * 13 ^ 4) * 17 ^ 4) * 29 ^ 4) * 37 ^ 4)
          * 41 ^ 4) := by norm_num
    rw [eK, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpowC : (2 : ℝ) ^ 130 < (3.655 : ℝ) ^ 4 * 7633298173386946545155798622010546875 := by
    norm_num
  have hlogC : 130 * Real.log 2
      < 4 * Real.log (3.655 : ℝ) + Real.log (7633298173386946545155798622010546875 : ℝ) := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpowC
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff hGpos (by norm_num)]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_le_of_lt hle ?_
  rw [hseq, hsum, h39916800, hN, h12]
  linarith [hlogC, hKup]

/-- Two-sided Bohr–Mollerup `n = 11` interval: `3.575 < Γ(1/4) < 3.655`
(width `0.080`, tightening the `n = 10` interval `3.570 < Γ < 3.657`, width `0.087`). -/
theorem gamma_quarter_bounds_BM11 :
    (3.575 : ℝ) < Real.Gamma (1/4 : ℝ) ∧ Real.Gamma (1/4 : ℝ) < (3.655 : ℝ) :=
  ⟨gamma_quarter_gt_BM11, gamma_quarter_lt_BM11⟩

/-- Bohr–Mollerup `n = 12` lower bound at `x = 1/4`: `3.579 < Gamma(1/4)`
(tightens `gamma_quarter_gt_BM11`; exact `log`-of-rational value
`logΓ ≥ 36.5·log 2 - 0.75·log 3 - 2·log 5 - 2·log 7 - log 13 - log 17
- log 29 - log 37 - log 41 ≈ 1.2754`,
i.e. `Γ ≥ (2^146/(3^3·5^8·7^8·13^4·17^4·29^4·37^4·41^4))^{1/4} ≈ 3.57966`;
new interval `3.579 < Γ(1/4) < 3.655`, width `0.076`). -/
theorem gamma_quarter_gt_BM12 : (3.579 : ℝ) < Real.Gamma (1/4 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hge := Real.BohrMollerup.ge_logGammaSeq Real.convexOn_log_Gamma hfeq hx
    (show (12 : ℕ) ≠ 0 by norm_num)
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hge
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 12
      = (1/4 : ℝ) * Real.log 12 + Real.log 479001600
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
          + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
          + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ)
          + Real.log (45/4 : ℝ) + Real.log (49/4 : ℝ)) := by
    have f12 : Nat.factorial 12 = 479001600 := by decide
    have c12 : ((12 : ℕ) : ℝ) = (12 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = 17/4 := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = 21/4 := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = 25/4 := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = 29/4 := by norm_num
    have a8 : (1/4 : ℝ) + ((8 : ℕ) : ℝ) = 33/4 := by norm_num
    have a9 : (1/4 : ℝ) + ((9 : ℕ) : ℝ) = 37/4 := by norm_num
    have a10 : (1/4 : ℝ) + ((10 : ℕ) : ℝ) = 41/4 := by norm_num
    have a11 : (1/4 : ℝ) + ((11 : ℕ) : ℝ) = 45/4 := by norm_num
    have a12 : (1/4 : ℝ) + ((12 : ℕ) : ℝ) = 49/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f12, c12, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hpos174 : (0 : ℝ) < 17/4 := by norm_num
  have hpos214 : (0 : ℝ) < 21/4 := by norm_num
  have hpos254 : (0 : ℝ) < 25/4 := by norm_num
  have hpos294 : (0 : ℝ) < 29/4 := by norm_num
  have hpos334 : (0 : ℝ) < 33/4 := by norm_num
  have hpos374 : (0 : ℝ) < 37/4 := by norm_num
  have hpos414 : (0 : ℝ) < 41/4 := by norm_num
  have hpos454 : (0 : ℝ) < 45/4 := by norm_num
  have hpos494 : (0 : ℝ) < 49/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
        + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ)
        + Real.log (49/4 : ℝ)
      = Real.log 16713607661375625 - 26 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4))
        + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
        + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne')
        hpos174.ne') hpos214.ne') hpos254.ne').symm
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) + Real.log (29/4 : ℝ)
        = Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne')
        hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne').symm
    have m8 : Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) + Real.log (33/4 : ℝ)
        = Real.log (((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne')
        hpos294.ne') hpos334.ne').symm
    have m9 : Real.log (((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) + Real.log (37/4 : ℝ)
        = Real.log ((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne')
        hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne').symm
    have m10 : Real.log ((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4))
        + Real.log (41/4 : ℝ)
        = Real.log (((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) * (41/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne')
        hpos414.ne').symm
    have m11 : Real.log (((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) * (41/4))
        + Real.log (45/4 : ℝ)
        = Real.log ((((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) * (41/4))
          * (45/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne')
        hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne')
        hpos374.ne') hpos414.ne') hpos454.ne').symm
    have p : ((((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) * (41/4))
          * (45/4)) * (49/4)
        = 16713607661375625 / 67108864 := by norm_num
    have m12 : Real.log ((((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) * (41/4))
          * (45/4))
        + Real.log (49/4 : ℝ)
        = Real.log 16713607661375625 - Real.log 67108864 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne')
        hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne')
        hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l67108864 : Real.log (67108864 : ℝ) = 26 * Real.log 2 := by
      have e67108864 : (67108864 : ℝ) = 2 ^ 26 := by norm_num
      rw [e67108864, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, l67108864]
  have h479001600 : Real.log (479001600 : ℝ)
      = 10 * Real.log 2 + 5 * Real.log 3 + 2 * Real.log 5 + Real.log 7
        + Real.log 11 := by
    have e479001600 : (479001600 : ℝ) = ((((1024 * 243) * 25) * 7) * 11) := by
      norm_num
    have e1024 : (1024 : ℝ) = 2 ^ 10 := by norm_num
    have e243 : (243 : ℝ) = 3 ^ 5 := by norm_num
    have e25 : (25 : ℝ) = 5 ^ 2 := by norm_num
    rw [e479001600, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e1024, e243, e25,
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (16713607661375625 : ℝ)
      = 6 * Real.log 3 + 4 * Real.log 5 + 3 * Real.log 7 + Real.log 11
        + Real.log 13 + Real.log 17 + Real.log 29 + Real.log 37
        + Real.log 41 := by
    have eN : (16713607661375625 : ℝ)
        = ((((((((729 * 625) * 343) * 11) * 13) * 17) * 29) * 37) * 41) := by
      norm_num
    have e729 : (729 : ℝ) = 3 ^ 6 := by norm_num
    have e625 : (625 : ℝ) = 5 ^ 4 := by norm_num
    have e343 : (343 : ℝ) = 7 ^ 3 := by norm_num
    rw [eN, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e729, e625, e343,
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h12 : Real.log (12 : ℝ) = 2 * Real.log 2 + Real.log 3 := by
    have e12 : (12 : ℝ) = 4 * 3 := by norm_num
    have e4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [e12, Real.log_mul (by norm_num) (by norm_num), e4, Real.log_pow]
    push_cast
    ring
  have hK : Real.log (543264752385669664573588803110679291796875 : ℝ)
      = 3 * Real.log 3 + 8 * Real.log 5 + 8 * Real.log 7 + 4 * Real.log 13
        + 4 * Real.log 17 + 4 * Real.log 29 + 4 * Real.log 37
        + 4 * Real.log 41 := by
    have eK : (543264752385669664573588803110679291796875 : ℝ)
        = (((((((3 ^ 3 * 5 ^ 8) * 7 ^ 8) * 13 ^ 4) * 17 ^ 4) * 29 ^ 4)
          * 37 ^ 4) * 41 ^ 4) := by norm_num
    rw [eK, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpow : (3.579 : ℝ) ^ 4 * 543264752385669664573588803110679291796875
      < 2 ^ 146 := by norm_num
  have hlog4 : 4 * Real.log (3.579 : ℝ)
        + Real.log (543264752385669664573588803110679291796875 : ℝ)
      < 146 * Real.log 2 := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpow
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff (by norm_num) hGpos]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_lt_of_le ?_ hge
  rw [hseq, hsum, h479001600, hN, h12]
  linarith [hlog4, hK]

/-- Bohr–Mollerup `n = 12` upper bound at `x = 1/4`: `Gamma(1/4) < 3.653`
(mirror of `gamma_quarter_gt_BM12`; exact value
`logΓ ≤ 36·log 2 - log 3 - 2·log 5 - 2·log 7 - 0.75·log 13 - log 17
- log 29 - log 37 - log 41 ≈ 1.2956`,
i.e. `Γ ≤ (2^144/(3^4·5^8·7^8·13^3·17^4·29^4·37^4·41^4))^{1/4} ≈ 3.65201`;
new interval `3.579 < Γ(1/4) < 3.653`, width `0.074`). -/
theorem gamma_quarter_lt_BM12 : Real.Gamma (1/4 : ℝ) < (3.653 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hx' : (1/4 : ℝ) ≤ 1 := by norm_num
  have hle := Real.BohrMollerup.le_logGammaSeq Real.convexOn_log_Gamma hfeq hx hx' 12
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hle
  have c12 : ((12 : ℕ) : ℝ) = (12 : ℝ) := by norm_num
  rw [c12] at hle
  have c13 : (12 : ℝ) + 1 = (13 : ℝ) := by norm_num
  rw [c13] at hle
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 12
      = (1/4 : ℝ) * Real.log 12 + Real.log 479001600
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
          + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
          + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ)
          + Real.log (45/4 : ℝ) + Real.log (49/4 : ℝ)) := by
    have f12 : Nat.factorial 12 = 479001600 := by decide
    have c12' : ((12 : ℕ) : ℝ) = (12 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = 1/4 := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = 5/4 := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = 9/4 := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = 13/4 := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = 17/4 := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = 21/4 := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = 25/4 := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = 29/4 := by norm_num
    have a8 : (1/4 : ℝ) + ((8 : ℕ) : ℝ) = 33/4 := by norm_num
    have a9 : (1/4 : ℝ) + ((9 : ℕ) : ℝ) = 37/4 := by norm_num
    have a10 : (1/4 : ℝ) + ((10 : ℕ) : ℝ) = 41/4 := by norm_num
    have a11 : (1/4 : ℝ) + ((11 : ℕ) : ℝ) = 45/4 := by norm_num
    have a12 : (1/4 : ℝ) + ((12 : ℕ) : ℝ) = 49/4 := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f12, c12', Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]
    ring
  have hpos14 : (0 : ℝ) < 1/4 := by norm_num
  have hpos54 : (0 : ℝ) < 5/4 := by norm_num
  have hpos94 : (0 : ℝ) < 9/4 := by norm_num
  have hpos134 : (0 : ℝ) < 13/4 := by norm_num
  have hpos174 : (0 : ℝ) < 17/4 := by norm_num
  have hpos214 : (0 : ℝ) < 21/4 := by norm_num
  have hpos254 : (0 : ℝ) < 25/4 := by norm_num
  have hpos294 : (0 : ℝ) < 29/4 := by norm_num
  have hpos334 : (0 : ℝ) < 33/4 := by norm_num
  have hpos374 : (0 : ℝ) < 37/4 := by norm_num
  have hpos414 : (0 : ℝ) < 41/4 := by norm_num
  have hpos454 : (0 : ℝ) < 45/4 := by norm_num
  have hpos494 : (0 : ℝ) < 49/4 := by norm_num
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
        + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ)
        + Real.log (49/4 : ℝ)
      = Real.log 16713607661375625 - 26 * Real.log 2 := by
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4)) * (9/4)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4))
        + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
        + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne')
        hpos174.ne') hpos214.ne') hpos254.ne').symm
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) + Real.log (29/4 : ℝ)
        = Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne')
        hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne').symm
    have m8 : Real.log ((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) + Real.log (33/4 : ℝ)
        = Real.log (((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne')
        hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne')
        hpos294.ne') hpos334.ne').symm
    have m9 : Real.log (((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) + Real.log (37/4 : ℝ)
        = Real.log ((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne'
        hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne')
        hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne').symm
    have m10 : Real.log ((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4))
        + Real.log (41/4 : ℝ)
        = Real.log (((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) * (41/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne')
        hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne')
        hpos414.ne').symm
    have m11 : Real.log (((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) * (41/4))
        + Real.log (45/4 : ℝ)
        = Real.log ((((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) * (41/4))
          * (45/4)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne')
        hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne')
        hpos374.ne') hpos414.ne') hpos454.ne').symm
    have p : ((((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) * (41/4))
          * (45/4)) * (49/4)
        = 16713607661375625 / 67108864 := by norm_num
    have m12 : Real.log ((((((((((((1/4 : ℝ) * (5/4)) * (9/4)) * (13/4)) * (17/4))
          * (21/4)) * (25/4)) * (29/4)) * (33/4)) * (37/4)) * (41/4))
          * (45/4))
        + Real.log (49/4 : ℝ)
        = Real.log 16713607661375625 - Real.log 67108864 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne')
        hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne')
        hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l67108864 : Real.log (67108864 : ℝ) = 26 * Real.log 2 := by
      have e67108864 : (67108864 : ℝ) = 2 ^ 26 := by norm_num
      rw [e67108864, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, l67108864]
  have h479001600 : Real.log (479001600 : ℝ)
      = 10 * Real.log 2 + 5 * Real.log 3 + 2 * Real.log 5 + Real.log 7
        + Real.log 11 := by
    have e479001600 : (479001600 : ℝ) = ((((1024 * 243) * 25) * 7) * 11) := by
      norm_num
    have e1024 : (1024 : ℝ) = 2 ^ 10 := by norm_num
    have e243 : (243 : ℝ) = 3 ^ 5 := by norm_num
    have e25 : (25 : ℝ) = 5 ^ 2 := by norm_num
    rw [e479001600, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e1024, e243, e25,
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (16713607661375625 : ℝ)
      = 6 * Real.log 3 + 4 * Real.log 5 + 3 * Real.log 7 + Real.log 11
        + Real.log 13 + Real.log 17 + Real.log 29 + Real.log 37
        + Real.log 41 := by
    have eN : (16713607661375625 : ℝ)
        = ((((((((729 * 625) * 343) * 11) * 13) * 17) * 29) * 37) * 41) := by
      norm_num
    have e729 : (729 : ℝ) = 3 ^ 6 := by norm_num
    have e625 : (625 : ℝ) = 5 ^ 4 := by norm_num
    have e343 : (343 : ℝ) = 7 ^ 3 := by norm_num
    rw [eN, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), e729, e625, e343,
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h12 : Real.log (12 : ℝ) = 2 * Real.log 2 + Real.log 3 := by
    have e12 : (12 : ℝ) = 4 * 3 := by norm_num
    have e4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [e12, Real.log_mul (by norm_num) (by norm_num), e4, Real.log_pow]
    push_cast
    ring
  have hKup : Real.log (125368789012077614901597416102464451953125 : ℝ)
      = 4 * Real.log 3 + 8 * Real.log 5 + 8 * Real.log 7 + 3 * Real.log 13
        + 4 * Real.log 17 + 4 * Real.log 29 + 4 * Real.log 37
        + 4 * Real.log 41 := by
    have eK : (125368789012077614901597416102464451953125 : ℝ)
        = (((((((3 ^ 4 * 5 ^ 8) * 7 ^ 8) * 13 ^ 3) * 17 ^ 4) * 29 ^ 4)
          * 37 ^ 4) * 41 ^ 4) := by norm_num
    rw [eK, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpowC : (2 : ℝ) ^ 144 < (3.653 : ℝ) ^ 4 * 125368789012077614901597416102464451953125 := by
    norm_num
  have hlogC : 144 * Real.log 2
      < 4 * Real.log (3.653 : ℝ) + Real.log (125368789012077614901597416102464451953125 : ℝ) := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpowC
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff hGpos (by norm_num)]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_le_of_lt hle ?_
  rw [hseq, hsum, h479001600, hN, h12]
  linarith [hlogC, hKup]

/-- Two-sided Bohr–Mollerup `n = 12` interval: `3.579 < Γ(1/4) < 3.653`
(width `0.074`, tightening the `n = 11` interval `3.575 < Γ < 3.655`, width `0.080`). -/
theorem gamma_quarter_bounds_BM12 :
    (3.579 : ℝ) < Real.Gamma (1/4 : ℝ) ∧ Real.Gamma (1/4 : ℝ) < (3.653 : ℝ) :=
  ⟨gamma_quarter_gt_BM12, gamma_quarter_lt_BM12⟩

/-- Bohr–Mollerup `n = 13` lower bound at `x = 1/4`: `3.583 < Gamma(1/4)`
(tightens `gamma_quarter_gt_BM12`; exact `log`-of-rational value
`logΓ ≥ 38·log 2 - log 3 - 2·log 5 - 2·log 7 + 0.25·log 13 - log 17 - log 29 - log 37 - log 41 - log 53 ≈ 1.276231, Γ ≈ 3.58311`,
i.e. `Γ ≥ (2^152·13/(3^4·5^8·7^8·17^4·29^4·37^4·41^4·53^4))^{1/4}`;
new interval `3.583 < Γ(1/4) < 3.651`, width `0.068`). -/
theorem gamma_quarter_gt_BM13 : (3.583 : ℝ) < Real.Gamma (1/4 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hge := Real.BohrMollerup.ge_logGammaSeq Real.convexOn_log_Gamma hfeq hx
    (show (13 : ℕ) ≠ 0 by norm_num)
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hge
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 13
      = (1/4 : ℝ) * Real.log 13 + Real.log 6227020800
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
          + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
          + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ)
          + Real.log (49/4 : ℝ) + Real.log (53/4 : ℝ)) := by
    have f13 : Nat.factorial 13 = 6227020800 := by decide
    have c13' : ((13 : ℕ) : ℝ) = (13 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = (1/4 : ℝ) := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = (5/4 : ℝ) := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = (9/4 : ℝ) := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = (13/4 : ℝ) := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = (17/4 : ℝ) := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = (21/4 : ℝ) := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = (25/4 : ℝ) := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = (29/4 : ℝ) := by norm_num
    have a8 : (1/4 : ℝ) + ((8 : ℕ) : ℝ) = (33/4 : ℝ) := by norm_num
    have a9 : (1/4 : ℝ) + ((9 : ℕ) : ℝ) = (37/4 : ℝ) := by norm_num
    have a10 : (1/4 : ℝ) + ((10 : ℕ) : ℝ) = (41/4 : ℝ) := by norm_num
    have a11 : (1/4 : ℝ) + ((11 : ℕ) : ℝ) = (45/4 : ℝ) := by norm_num
    have a12 : (1/4 : ℝ) + ((12 : ℕ) : ℝ) = (49/4 : ℝ) := by norm_num
    have a13 : (1/4 : ℝ) + ((13 : ℕ) : ℝ) = (53/4 : ℝ) := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f13, c13', Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13]
    ring
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
        + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ)
        + Real.log (49/4 : ℝ) + Real.log (53/4 : ℝ)
      = Real.log 885821206052908125 - 28 * Real.log 2 := by
    have hpos14 : (0 : ℝ) < (1/4 : ℝ) := by norm_num
    have hpos54 : (0 : ℝ) < (5/4 : ℝ) := by norm_num
    have hpos94 : (0 : ℝ) < (9/4 : ℝ) := by norm_num
    have hpos134 : (0 : ℝ) < (13/4 : ℝ) := by norm_num
    have hpos174 : (0 : ℝ) < (17/4 : ℝ) := by norm_num
    have hpos214 : (0 : ℝ) < (21/4 : ℝ) := by norm_num
    have hpos254 : (0 : ℝ) < (25/4 : ℝ) := by norm_num
    have hpos294 : (0 : ℝ) < (29/4 : ℝ) := by norm_num
    have hpos334 : (0 : ℝ) < (33/4 : ℝ) := by norm_num
    have hpos374 : (0 : ℝ) < (37/4 : ℝ) := by norm_num
    have hpos414 : (0 : ℝ) < (41/4 : ℝ) := by norm_num
    have hpos454 : (0 : ℝ) < (45/4 : ℝ) := by norm_num
    have hpos494 : (0 : ℝ) < (49/4 : ℝ) := by norm_num
    have hpos534 : (0 : ℝ) < (53/4 : ℝ) := by norm_num
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4 : ℝ)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4 : ℝ)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne').symm
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) + Real.log (29/4 : ℝ)
        = Real.log ((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne').symm
    have m8 : Real.log ((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) + Real.log (33/4 : ℝ)
        = Real.log (((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne').symm
    have m9 : Real.log (((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) + Real.log (37/4 : ℝ)
        = Real.log ((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne').symm
    have m10 : Real.log ((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) + Real.log (41/4 : ℝ)
        = Real.log (((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne').symm
    have m11 : Real.log (((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) + Real.log (45/4 : ℝ)
        = Real.log ((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne').symm
    have m12 : Real.log ((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) + Real.log (49/4 : ℝ)
        = Real.log (((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne').symm
    have p : ((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ))
        = 885821206052908125 / 268435456 := by norm_num
    have m13 : Real.log (((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ))
        + Real.log (53/4 : ℝ)
        = Real.log 885821206052908125 - Real.log 268435456 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l268435456 : Real.log (268435456 : ℝ) = 28 * Real.log 2 := by
      have e268435456 : (268435456 : ℝ) = 2 ^ 28 := by norm_num
      rw [e268435456, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, l268435456]
  have h6227020800 : Real.log (6227020800 : ℝ)
      = 10 * Real.log 2 + 5 * Real.log 3 + 2 * Real.log 5 + Real.log 7
      + Real.log 11 + Real.log 13 := by
    have e6227020800 : (6227020800 : ℝ) = ((((((1024 * 243) * 25) * 7) * 11) * 13)) := by
      norm_num
    have e1024 : (1024 : ℝ) = 2 ^ 10 := by norm_num
    have e243 : (243 : ℝ) = 3 ^ 5 := by norm_num
    have e25 : (25 : ℝ) = 5 ^ 2 := by norm_num
    rw [e6227020800, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), e1024, e243, e25, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (885821206052908125 : ℝ)
      = 6 * Real.log 3 + 4 * Real.log 5 + 3 * Real.log 7 + Real.log 11
      + Real.log 13 + Real.log 17 + Real.log 29 + Real.log 37
      + Real.log 41 + Real.log 53 := by
    have e885821206052908125 : (885821206052908125 : ℝ) = ((((((((((729 * 625) * 343) * 11) * 13) * 17) * 29) * 37) * 41) * 53)) := by
      norm_num
    have e729 : (729 : ℝ) = 3 ^ 6 := by norm_num
    have e625 : (625 : ℝ) = 5 ^ 4 := by norm_num
    have e343 : (343 : ℝ) = 7 ^ 3 := by norm_num
    rw [e885821206052908125, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), e729, e625, e343, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hK : Real.log (450259466405465266684738862724437783937890625 : ℝ)
      = 4 * Real.log 3 + 8 * Real.log 5 + 8 * Real.log 7 + 4 * Real.log 17
      + 4 * Real.log 29 + 4 * Real.log 37 + 4 * Real.log 41
      + 4 * Real.log 53 := by
    have e450259466405465266684738862724437783937890625 : (450259466405465266684738862724437783937890625 : ℝ) = ((((((((3 ^ 4 * 5 ^ 8) * 7 ^ 8) * 17 ^ 4) * 29 ^ 4) * 37 ^ 4) * 41 ^ 4) * 53 ^ 4)) := by
      norm_num
    rw [e450259466405465266684738862724437783937890625, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpow : (3.583 : ℝ) ^ 4 * 450259466405465266684738862724437783937890625
      < 13 * 2 ^ 152 := by norm_num
  have hlog4 : 4 * Real.log (3.583 : ℝ)
        + Real.log (450259466405465266684738862724437783937890625 : ℝ)
      < Real.log 13 + 152 * Real.log 2 := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpow
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff (by norm_num) hGpos]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_lt_of_le ?_ hge
  rw [hseq, hsum, h6227020800, hN]
  linarith [hlog4, hK]

/-- Bohr–Mollerup `n = 13` upper bound at `x = 1/4`: `Gamma(1/4) < 3.651`
(mirror of `gamma_quarter_gt_BM13`; exact value
`logΓ ≤ 38.25·log 2 - log 3 - 2·log 5 - 1.75·log 7 - log 17 - log 29 - log 37 - log 41 - log 53 ≈ 1.294758, Γ ≈ 3.65011`,
i.e. `Γ ≤ (2^153/(3^4·5^8·7^7·17^4·29^4·37^4·41^4·53^4))^{1/4}`;
new interval `3.583 < Γ(1/4) < 3.651`, width `0.068`). -/
theorem gamma_quarter_lt_BM13 : Real.Gamma (1/4 : ℝ) < (3.651 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hx' : (1/4 : ℝ) ≤ 1 := by norm_num
  have hle := Real.BohrMollerup.le_logGammaSeq Real.convexOn_log_Gamma hfeq hx hx' 13
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hle
  have c13 : ((13 : ℕ) : ℝ) = (13 : ℝ) := by norm_num
  rw [c13] at hle
  have c14 : (13 : ℝ) + 1 = (14 : ℝ) := by norm_num
  rw [c14] at hle
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 13
      = (1/4 : ℝ) * Real.log 13 + Real.log 6227020800
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
          + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
          + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ)
          + Real.log (49/4 : ℝ) + Real.log (53/4 : ℝ)) := by
    have f13 : Nat.factorial 13 = 6227020800 := by decide
    have c13' : ((13 : ℕ) : ℝ) = (13 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = (1/4 : ℝ) := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = (5/4 : ℝ) := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = (9/4 : ℝ) := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = (13/4 : ℝ) := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = (17/4 : ℝ) := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = (21/4 : ℝ) := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = (25/4 : ℝ) := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = (29/4 : ℝ) := by norm_num
    have a8 : (1/4 : ℝ) + ((8 : ℕ) : ℝ) = (33/4 : ℝ) := by norm_num
    have a9 : (1/4 : ℝ) + ((9 : ℕ) : ℝ) = (37/4 : ℝ) := by norm_num
    have a10 : (1/4 : ℝ) + ((10 : ℕ) : ℝ) = (41/4 : ℝ) := by norm_num
    have a11 : (1/4 : ℝ) + ((11 : ℕ) : ℝ) = (45/4 : ℝ) := by norm_num
    have a12 : (1/4 : ℝ) + ((12 : ℕ) : ℝ) = (49/4 : ℝ) := by norm_num
    have a13 : (1/4 : ℝ) + ((13 : ℕ) : ℝ) = (53/4 : ℝ) := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f13, c13', Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13]
    ring
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
        + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ)
        + Real.log (49/4 : ℝ) + Real.log (53/4 : ℝ)
      = Real.log 885821206052908125 - 28 * Real.log 2 := by
    have hpos14 : (0 : ℝ) < (1/4 : ℝ) := by norm_num
    have hpos54 : (0 : ℝ) < (5/4 : ℝ) := by norm_num
    have hpos94 : (0 : ℝ) < (9/4 : ℝ) := by norm_num
    have hpos134 : (0 : ℝ) < (13/4 : ℝ) := by norm_num
    have hpos174 : (0 : ℝ) < (17/4 : ℝ) := by norm_num
    have hpos214 : (0 : ℝ) < (21/4 : ℝ) := by norm_num
    have hpos254 : (0 : ℝ) < (25/4 : ℝ) := by norm_num
    have hpos294 : (0 : ℝ) < (29/4 : ℝ) := by norm_num
    have hpos334 : (0 : ℝ) < (33/4 : ℝ) := by norm_num
    have hpos374 : (0 : ℝ) < (37/4 : ℝ) := by norm_num
    have hpos414 : (0 : ℝ) < (41/4 : ℝ) := by norm_num
    have hpos454 : (0 : ℝ) < (45/4 : ℝ) := by norm_num
    have hpos494 : (0 : ℝ) < (49/4 : ℝ) := by norm_num
    have hpos534 : (0 : ℝ) < (53/4 : ℝ) := by norm_num
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4 : ℝ)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4 : ℝ)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne').symm
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) + Real.log (29/4 : ℝ)
        = Real.log ((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne').symm
    have m8 : Real.log ((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) + Real.log (33/4 : ℝ)
        = Real.log (((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne').symm
    have m9 : Real.log (((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) + Real.log (37/4 : ℝ)
        = Real.log ((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne').symm
    have m10 : Real.log ((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) + Real.log (41/4 : ℝ)
        = Real.log (((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne').symm
    have m11 : Real.log (((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) + Real.log (45/4 : ℝ)
        = Real.log ((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne').symm
    have m12 : Real.log ((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) + Real.log (49/4 : ℝ)
        = Real.log (((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne').symm
    have p : ((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ))
        = 885821206052908125 / 268435456 := by norm_num
    have m13 : Real.log (((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ))
        + Real.log (53/4 : ℝ)
        = Real.log 885821206052908125 - Real.log 268435456 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l268435456 : Real.log (268435456 : ℝ) = 28 * Real.log 2 := by
      have e268435456 : (268435456 : ℝ) = 2 ^ 28 := by norm_num
      rw [e268435456, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, l268435456]
  have h6227020800 : Real.log (6227020800 : ℝ)
      = 10 * Real.log 2 + 5 * Real.log 3 + 2 * Real.log 5 + Real.log 7
      + Real.log 11 + Real.log 13 := by
    have e6227020800 : (6227020800 : ℝ) = ((((((1024 * 243) * 25) * 7) * 11) * 13)) := by
      norm_num
    have e1024 : (1024 : ℝ) = 2 ^ 10 := by norm_num
    have e243 : (243 : ℝ) = 3 ^ 5 := by norm_num
    have e25 : (25 : ℝ) = 5 ^ 2 := by norm_num
    rw [e6227020800, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), e1024, e243, e25, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (885821206052908125 : ℝ)
      = 6 * Real.log 3 + 4 * Real.log 5 + 3 * Real.log 7 + Real.log 11
      + Real.log 13 + Real.log 17 + Real.log 29 + Real.log 37
      + Real.log 41 + Real.log 53 := by
    have e885821206052908125 : (885821206052908125 : ℝ) = ((((((((((729 * 625) * 343) * 11) * 13) * 17) * 29) * 37) * 41) * 53)) := by
      norm_num
    have e729 : (729 : ℝ) = 3 ^ 6 := by norm_num
    have e625 : (625 : ℝ) = 5 ^ 4 := by norm_num
    have e343 : (343 : ℝ) = 7 ^ 3 := by norm_num
    rw [e885821206052908125, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), e729, e625, e343, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h14 : Real.log (14 : ℝ) = Real.log 2 + Real.log 7 := by
    have e14 : (14 : ℝ) = 2 * 7 := by norm_num
    rw [e14, Real.log_mul (by norm_num) (by norm_num)]
  have hKup : Real.log (64322780915066466669248408960633969133984375 : ℝ)
      = 4 * Real.log 3 + 8 * Real.log 5 + 7 * Real.log 7 + 4 * Real.log 17
      + 4 * Real.log 29 + 4 * Real.log 37 + 4 * Real.log 41
      + 4 * Real.log 53 := by
    have e64322780915066466669248408960633969133984375 : (64322780915066466669248408960633969133984375 : ℝ) = ((((((((3 ^ 4 * 5 ^ 8) * 7 ^ 7) * 17 ^ 4) * 29 ^ 4) * 37 ^ 4) * 41 ^ 4) * 53 ^ 4)) := by
      norm_num
    rw [e64322780915066466669248408960633969133984375, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpowC : (2 : ℝ) ^ 153 < (3.651 : ℝ) ^ 4 * 64322780915066466669248408960633969133984375 := by
    norm_num
  have hlogC : 153 * Real.log 2
      < 4 * Real.log (3.651 : ℝ) + Real.log (64322780915066466669248408960633969133984375 : ℝ) := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpowC
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff hGpos (by norm_num)]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_le_of_lt hle ?_
  rw [hseq, hsum, h6227020800, hN, h14]
  linarith [hlogC, hKup]

/-- Two-sided Bohr–Mollerup `n = 13` interval: `3.583 < Γ(1/4) < 3.651`
(width `0.068`, tightening the `n = 12` interval `3.579 < Γ < 3.653`, width `0.074`). -/
theorem gamma_quarter_bounds_BM13 :
    (3.583 : ℝ) < Real.Gamma (1/4 : ℝ) ∧ Real.Gamma (1/4 : ℝ) < (3.651 : ℝ) :=
  ⟨gamma_quarter_gt_BM13, gamma_quarter_lt_BM13⟩

/-- Bohr–Mollerup `n = 14` lower bound at `x = 1/4`: `3.586 < Gamma(1/4)`
(tightens `gamma_quarter_gt_BM13`; exact `log`-of-rational value
`logΓ ≥ 41.25·log 2 - 2·log 3 - 2·log 5 - 0.75·log 7 - log 17 - log 19 - log 29 - log 37 - log 41 - log 53 ≈ 1.277058, Γ ≈ 3.58607`,
i.e. `Γ ≥ (2^165/(3^8·5^8·7^3·17^4·19^4·29^4·37^4·41^4·53^4))^{1/4}`;
new interval `3.586 < Γ(1/4) < 3.649`, width `0.063`). -/
theorem gamma_quarter_gt_BM14 : (3.586 : ℝ) < Real.Gamma (1/4 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hge := Real.BohrMollerup.ge_logGammaSeq Real.convexOn_log_Gamma hfeq hx
    (show (14 : ℕ) ≠ 0 by norm_num)
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hge
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 14
      = (1/4 : ℝ) * Real.log 14 + Real.log 87178291200
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
          + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
          + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ)
          + Real.log (49/4 : ℝ) + Real.log (53/4 : ℝ) + Real.log (57/4 : ℝ)) := by
    have f14 : Nat.factorial 14 = 87178291200 := by decide
    have c14' : ((14 : ℕ) : ℝ) = (14 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = (1/4 : ℝ) := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = (5/4 : ℝ) := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = (9/4 : ℝ) := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = (13/4 : ℝ) := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = (17/4 : ℝ) := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = (21/4 : ℝ) := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = (25/4 : ℝ) := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = (29/4 : ℝ) := by norm_num
    have a8 : (1/4 : ℝ) + ((8 : ℕ) : ℝ) = (33/4 : ℝ) := by norm_num
    have a9 : (1/4 : ℝ) + ((9 : ℕ) : ℝ) = (37/4 : ℝ) := by norm_num
    have a10 : (1/4 : ℝ) + ((10 : ℕ) : ℝ) = (41/4 : ℝ) := by norm_num
    have a11 : (1/4 : ℝ) + ((11 : ℕ) : ℝ) = (45/4 : ℝ) := by norm_num
    have a12 : (1/4 : ℝ) + ((12 : ℕ) : ℝ) = (49/4 : ℝ) := by norm_num
    have a13 : (1/4 : ℝ) + ((13 : ℕ) : ℝ) = (53/4 : ℝ) := by norm_num
    have a14 : (1/4 : ℝ) + ((14 : ℕ) : ℝ) = (57/4 : ℝ) := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f14, c14', Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14]
    ring
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
        + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ)
        + Real.log (49/4 : ℝ) + Real.log (53/4 : ℝ) + Real.log (57/4 : ℝ)
      = Real.log 50491808745015763125 - 30 * Real.log 2 := by
    have hpos14 : (0 : ℝ) < (1/4 : ℝ) := by norm_num
    have hpos54 : (0 : ℝ) < (5/4 : ℝ) := by norm_num
    have hpos94 : (0 : ℝ) < (9/4 : ℝ) := by norm_num
    have hpos134 : (0 : ℝ) < (13/4 : ℝ) := by norm_num
    have hpos174 : (0 : ℝ) < (17/4 : ℝ) := by norm_num
    have hpos214 : (0 : ℝ) < (21/4 : ℝ) := by norm_num
    have hpos254 : (0 : ℝ) < (25/4 : ℝ) := by norm_num
    have hpos294 : (0 : ℝ) < (29/4 : ℝ) := by norm_num
    have hpos334 : (0 : ℝ) < (33/4 : ℝ) := by norm_num
    have hpos374 : (0 : ℝ) < (37/4 : ℝ) := by norm_num
    have hpos414 : (0 : ℝ) < (41/4 : ℝ) := by norm_num
    have hpos454 : (0 : ℝ) < (45/4 : ℝ) := by norm_num
    have hpos494 : (0 : ℝ) < (49/4 : ℝ) := by norm_num
    have hpos534 : (0 : ℝ) < (53/4 : ℝ) := by norm_num
    have hpos574 : (0 : ℝ) < (57/4 : ℝ) := by norm_num
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4 : ℝ)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4 : ℝ)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne').symm
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) + Real.log (29/4 : ℝ)
        = Real.log ((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne').symm
    have m8 : Real.log ((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) + Real.log (33/4 : ℝ)
        = Real.log (((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne').symm
    have m9 : Real.log (((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) + Real.log (37/4 : ℝ)
        = Real.log ((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne').symm
    have m10 : Real.log ((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) + Real.log (41/4 : ℝ)
        = Real.log (((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne').symm
    have m11 : Real.log (((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) + Real.log (45/4 : ℝ)
        = Real.log ((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne').symm
    have m12 : Real.log ((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) + Real.log (49/4 : ℝ)
        = Real.log (((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne').symm
    have m13 : Real.log (((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) + Real.log (53/4 : ℝ)
        = Real.log ((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne').symm
    have p : (((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) * (57/4 : ℝ))
        = 50491808745015763125 / 1073741824 := by norm_num
    have m14 : Real.log ((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ))
        + Real.log (57/4 : ℝ)
        = Real.log 50491808745015763125 - Real.log 1073741824 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne') hpos574.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l1073741824 : Real.log (1073741824 : ℝ) = 30 * Real.log 2 := by
      have e1073741824 : (1073741824 : ℝ) = 2 ^ 30 := by norm_num
      rw [e1073741824, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, l1073741824]
  have h87178291200 : Real.log (87178291200 : ℝ)
      = 11 * Real.log 2 + 5 * Real.log 3 + 2 * Real.log 5 + 2 * Real.log 7
      + Real.log 11 + Real.log 13 := by
    have e87178291200 : (87178291200 : ℝ) = ((((((2048 * 243) * 25) * 49) * 11) * 13)) := by
      norm_num
    have e2048 : (2048 : ℝ) = 2 ^ 11 := by norm_num
    have e243 : (243 : ℝ) = 3 ^ 5 := by norm_num
    have e25 : (25 : ℝ) = 5 ^ 2 := by norm_num
    have e49 : (49 : ℝ) = 7 ^ 2 := by norm_num
    rw [e87178291200, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), e2048, e243, e25, e49, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (50491808745015763125 : ℝ)
      = 7 * Real.log 3 + 4 * Real.log 5 + 3 * Real.log 7 + Real.log 11
      + Real.log 13 + Real.log 17 + Real.log 19 + Real.log 29
      + Real.log 37 + Real.log 41 + Real.log 53 := by
    have e50491808745015763125 : (50491808745015763125 : ℝ) = (((((((((((2187 * 625) * 343) * 11) * 13) * 17) * 19) * 29) * 37) * 41) * 53)) := by
      norm_num
    have e2187 : (2187 : ℝ) = 3 ^ 7 := by norm_num
    have e625 : (625 : ℝ) = 5 ^ 4 := by norm_num
    have e343 : (343 : ℝ) = 7 ^ 3 := by norm_num
    rw [e50491808745015763125, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), e2187, e625, e343, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hK : Real.log (282795226848072693555623854326056284386633984375 : ℝ)
      = 8 * Real.log 3 + 8 * Real.log 5 + 3 * Real.log 7 + 4 * Real.log 17
      + 4 * Real.log 19 + 4 * Real.log 29 + 4 * Real.log 37
      + 4 * Real.log 41 + 4 * Real.log 53 := by
    have e282795226848072693555623854326056284386633984375 : (282795226848072693555623854326056284386633984375 : ℝ) = (((((((((3 ^ 8 * 5 ^ 8) * 7 ^ 3) * 17 ^ 4) * 19 ^ 4) * 29 ^ 4) * 37 ^ 4) * 41 ^ 4) * 53 ^ 4)) := by
      norm_num
    rw [e282795226848072693555623854326056284386633984375, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpow : (3.586 : ℝ) ^ 4 * 282795226848072693555623854326056284386633984375
      < 2 ^ 165 := by norm_num
  have hlog4 : 4 * Real.log (3.586 : ℝ)
        + Real.log (282795226848072693555623854326056284386633984375 : ℝ)
      < 165 * Real.log 2 := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpow
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff (by norm_num) hGpos]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_lt_of_le ?_ hge
  have h14 : Real.log (14 : ℝ) = Real.log 2 + Real.log 7 := by
    have e14 : (14 : ℝ) = 2 * 7 := by norm_num
    rw [e14, Real.log_mul (by norm_num) (by norm_num)]
  rw [hseq, hsum, h87178291200, hN, h14]
  linarith [hlog4, hK]

/-- Bohr–Mollerup `n = 14` upper bound at `x = 1/4`: `Gamma(1/4) < 3.649`
(mirror of `gamma_quarter_gt_BM14`; exact value
`logΓ ≤ 41·log 2 - 1.75·log 3 - 1.75·log 5 - log 7 - log 17 - log 19 - log 29 - log 37 - log 41 - log 53 ≈ 1.294306, Γ ≈ 3.64846`,
i.e. `Γ ≤ (2^164/(3^7·5^7·7^4·17^4·19^4·29^4·37^4·41^4·53^4))^{1/4}`;
new interval `3.586 < Γ(1/4) < 3.649`, width `0.063`). -/
theorem gamma_quarter_lt_BM14 : Real.Gamma (1/4 : ℝ) < (3.649 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hx' : (1/4 : ℝ) ≤ 1 := by norm_num
  have hle := Real.BohrMollerup.le_logGammaSeq Real.convexOn_log_Gamma hfeq hx hx' 14
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hle
  have c14 : ((14 : ℕ) : ℝ) = (14 : ℝ) := by norm_num
  rw [c14] at hle
  have c15 : (14 : ℝ) + 1 = (15 : ℝ) := by norm_num
  rw [c15] at hle
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 14
      = (1/4 : ℝ) * Real.log 14 + Real.log 87178291200
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
          + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
          + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
          + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ)
          + Real.log (49/4 : ℝ) + Real.log (53/4 : ℝ) + Real.log (57/4 : ℝ)) := by
    have f14 : Nat.factorial 14 = 87178291200 := by decide
    have c14' : ((14 : ℕ) : ℝ) = (14 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = (1/4 : ℝ) := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = (5/4 : ℝ) := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = (9/4 : ℝ) := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = (13/4 : ℝ) := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = (17/4 : ℝ) := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = (21/4 : ℝ) := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = (25/4 : ℝ) := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = (29/4 : ℝ) := by norm_num
    have a8 : (1/4 : ℝ) + ((8 : ℕ) : ℝ) = (33/4 : ℝ) := by norm_num
    have a9 : (1/4 : ℝ) + ((9 : ℕ) : ℝ) = (37/4 : ℝ) := by norm_num
    have a10 : (1/4 : ℝ) + ((10 : ℕ) : ℝ) = (41/4 : ℝ) := by norm_num
    have a11 : (1/4 : ℝ) + ((11 : ℕ) : ℝ) = (45/4 : ℝ) := by norm_num
    have a12 : (1/4 : ℝ) + ((12 : ℕ) : ℝ) = (49/4 : ℝ) := by norm_num
    have a13 : (1/4 : ℝ) + ((13 : ℕ) : ℝ) = (53/4 : ℝ) := by norm_num
    have a14 : (1/4 : ℝ) + ((14 : ℕ) : ℝ) = (57/4 : ℝ) := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f14, c14', Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14]
    ring
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
        + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ)
        + Real.log (49/4 : ℝ) + Real.log (53/4 : ℝ) + Real.log (57/4 : ℝ)
      = Real.log 50491808745015763125 - 30 * Real.log 2 := by
    have hpos14 : (0 : ℝ) < (1/4 : ℝ) := by norm_num
    have hpos54 : (0 : ℝ) < (5/4 : ℝ) := by norm_num
    have hpos94 : (0 : ℝ) < (9/4 : ℝ) := by norm_num
    have hpos134 : (0 : ℝ) < (13/4 : ℝ) := by norm_num
    have hpos174 : (0 : ℝ) < (17/4 : ℝ) := by norm_num
    have hpos214 : (0 : ℝ) < (21/4 : ℝ) := by norm_num
    have hpos254 : (0 : ℝ) < (25/4 : ℝ) := by norm_num
    have hpos294 : (0 : ℝ) < (29/4 : ℝ) := by norm_num
    have hpos334 : (0 : ℝ) < (33/4 : ℝ) := by norm_num
    have hpos374 : (0 : ℝ) < (37/4 : ℝ) := by norm_num
    have hpos414 : (0 : ℝ) < (41/4 : ℝ) := by norm_num
    have hpos454 : (0 : ℝ) < (45/4 : ℝ) := by norm_num
    have hpos494 : (0 : ℝ) < (49/4 : ℝ) := by norm_num
    have hpos534 : (0 : ℝ) < (53/4 : ℝ) := by norm_num
    have hpos574 : (0 : ℝ) < (57/4 : ℝ) := by norm_num
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4 : ℝ)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4 : ℝ)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne').symm
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) + Real.log (29/4 : ℝ)
        = Real.log ((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne').symm
    have m8 : Real.log ((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) + Real.log (33/4 : ℝ)
        = Real.log (((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne').symm
    have m9 : Real.log (((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) + Real.log (37/4 : ℝ)
        = Real.log ((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne').symm
    have m10 : Real.log ((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) + Real.log (41/4 : ℝ)
        = Real.log (((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne').symm
    have m11 : Real.log (((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) + Real.log (45/4 : ℝ)
        = Real.log ((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne').symm
    have m12 : Real.log ((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) + Real.log (49/4 : ℝ)
        = Real.log (((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne').symm
    have m13 : Real.log (((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) + Real.log (53/4 : ℝ)
        = Real.log ((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne').symm
    have p : (((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) * (57/4 : ℝ))
        = 50491808745015763125 / 1073741824 := by norm_num
    have m14 : Real.log ((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ))
        + Real.log (57/4 : ℝ)
        = Real.log 50491808745015763125 - Real.log 1073741824 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne') hpos574.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l1073741824 : Real.log (1073741824 : ℝ) = 30 * Real.log 2 := by
      have e1073741824 : (1073741824 : ℝ) = 2 ^ 30 := by norm_num
      rw [e1073741824, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, l1073741824]
  have h87178291200 : Real.log (87178291200 : ℝ)
      = 11 * Real.log 2 + 5 * Real.log 3 + 2 * Real.log 5 + 2 * Real.log 7
      + Real.log 11 + Real.log 13 := by
    have e87178291200 : (87178291200 : ℝ) = ((((((2048 * 243) * 25) * 49) * 11) * 13)) := by
      norm_num
    have e2048 : (2048 : ℝ) = 2 ^ 11 := by norm_num
    have e243 : (243 : ℝ) = 3 ^ 5 := by norm_num
    have e25 : (25 : ℝ) = 5 ^ 2 := by norm_num
    have e49 : (49 : ℝ) = 7 ^ 2 := by norm_num
    rw [e87178291200, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), e2048, e243, e25, e49, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (50491808745015763125 : ℝ)
      = 7 * Real.log 3 + 4 * Real.log 5 + 3 * Real.log 7 + Real.log 11
      + Real.log 13 + Real.log 17 + Real.log 19 + Real.log 29
      + Real.log 37 + Real.log 41 + Real.log 53 := by
    have e50491808745015763125 : (50491808745015763125 : ℝ) = (((((((((((2187 * 625) * 343) * 11) * 13) * 17) * 19) * 29) * 37) * 41) * 53)) := by
      norm_num
    have e2187 : (2187 : ℝ) = 3 ^ 7 := by norm_num
    have e625 : (625 : ℝ) = 5 ^ 4 := by norm_num
    have e343 : (343 : ℝ) = 7 ^ 3 := by norm_num
    rw [e50491808745015763125, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), e2187, e625, e343, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h15 : Real.log (15 : ℝ) = Real.log 3 + Real.log 5 := by
    have e15 : (15 : ℝ) = 3 * 5 := by norm_num
    rw [e15, Real.log_mul (by norm_num) (by norm_num)]
  have hKup : Real.log (131971105862433923659291132018826266047095859375 : ℝ)
      = 7 * Real.log 3 + 7 * Real.log 5 + 4 * Real.log 7 + 4 * Real.log 17
      + 4 * Real.log 19 + 4 * Real.log 29 + 4 * Real.log 37
      + 4 * Real.log 41 + 4 * Real.log 53 := by
    have e131971105862433923659291132018826266047095859375 : (131971105862433923659291132018826266047095859375 : ℝ) = (((((((((3 ^ 7 * 5 ^ 7) * 7 ^ 4) * 17 ^ 4) * 19 ^ 4) * 29 ^ 4) * 37 ^ 4) * 41 ^ 4) * 53 ^ 4)) := by
      norm_num
    rw [e131971105862433923659291132018826266047095859375, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpowC : (2 : ℝ) ^ 164 < (3.649 : ℝ) ^ 4 * 131971105862433923659291132018826266047095859375 := by
    norm_num
  have hlogC : 164 * Real.log 2
      < 4 * Real.log (3.649 : ℝ) + Real.log (131971105862433923659291132018826266047095859375 : ℝ) := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpowC
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff hGpos (by norm_num)]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_le_of_lt hle ?_
  rw [hseq, hsum, h87178291200, hN, h15]
  linarith [hlogC, hKup]

/-- Two-sided Bohr–Mollerup `n = 14` interval: `3.586 < Γ(1/4) < 3.649`
(width `0.063`, tightening the `n = 13` interval `3.583 < Γ < 3.651`, width `0.068`). -/
theorem gamma_quarter_bounds_BM14 :
    (3.586 : ℝ) < Real.Gamma (1/4 : ℝ) ∧ Real.Gamma (1/4 : ℝ) < (3.649 : ℝ) :=
  ⟨gamma_quarter_gt_BM14, gamma_quarter_lt_BM14⟩

/-- Bohr–Mollerup `n = 15` lower bound at `x = 1/4`: `3.588 < Gamma(1/4)`
(tightens `gamma_quarter_gt_BM14`; exact `log`-of-rational value
`logΓ ≥ 43·log 2 - 0.75·log 3 - 0.75·log 5 - log 7 - log 17 - log 19 - log 29 - log 37 - log 41 - log 53 - log 61 ≈ 1.277777, Γ ≈ 3.58865`,
i.e. `Γ ≥ (2^172/(3^3·5^3·7^4·17^4·19^4·29^4·37^4·41^4·53^4·61^4))^{1/4}`;
new interval `3.588 < Γ(1/4) < 3.648`, width `0.060`). -/
theorem gamma_quarter_gt_BM15 : (3.588 : ℝ) < Real.Gamma (1/4 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hge := Real.BohrMollerup.ge_logGammaSeq Real.convexOn_log_Gamma hfeq hx
    (show (15 : ℕ) ≠ 0 by norm_num)
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hge
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 15
      = (1/4 : ℝ) * Real.log 15 + Real.log 1307674368000
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ) + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ) + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ) + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ) + Real.log (49/4 : ℝ) + Real.log (53/4 : ℝ) + Real.log (57/4 : ℝ) + Real.log (61/4 : ℝ)) := by
    have f15 : Nat.factorial 15 = 1307674368000 := by decide
    have c15' : ((15 : ℕ) : ℝ) = (15 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = (1/4 : ℝ) := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = (5/4 : ℝ) := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = (9/4 : ℝ) := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = (13/4 : ℝ) := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = (17/4 : ℝ) := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = (21/4 : ℝ) := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = (25/4 : ℝ) := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = (29/4 : ℝ) := by norm_num
    have a8 : (1/4 : ℝ) + ((8 : ℕ) : ℝ) = (33/4 : ℝ) := by norm_num
    have a9 : (1/4 : ℝ) + ((9 : ℕ) : ℝ) = (37/4 : ℝ) := by norm_num
    have a10 : (1/4 : ℝ) + ((10 : ℕ) : ℝ) = (41/4 : ℝ) := by norm_num
    have a11 : (1/4 : ℝ) + ((11 : ℕ) : ℝ) = (45/4 : ℝ) := by norm_num
    have a12 : (1/4 : ℝ) + ((12 : ℕ) : ℝ) = (49/4 : ℝ) := by norm_num
    have a13 : (1/4 : ℝ) + ((13 : ℕ) : ℝ) = (53/4 : ℝ) := by norm_num
    have a14 : (1/4 : ℝ) + ((14 : ℕ) : ℝ) = (57/4 : ℝ) := by norm_num
    have a15 : (1/4 : ℝ) + ((15 : ℕ) : ℝ) = (61/4 : ℝ) := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f15, c15', Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]
    ring
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
        + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ)
        + Real.log (49/4 : ℝ) + Real.log (53/4 : ℝ) + Real.log (57/4 : ℝ)
        + Real.log (61/4 : ℝ)
      = Real.log 3080000333445961550625 - 32 * Real.log 2 := by
    have hpos14 : (0 : ℝ) < (1/4 : ℝ) := by norm_num
    have hpos54 : (0 : ℝ) < (5/4 : ℝ) := by norm_num
    have hpos94 : (0 : ℝ) < (9/4 : ℝ) := by norm_num
    have hpos134 : (0 : ℝ) < (13/4 : ℝ) := by norm_num
    have hpos174 : (0 : ℝ) < (17/4 : ℝ) := by norm_num
    have hpos214 : (0 : ℝ) < (21/4 : ℝ) := by norm_num
    have hpos254 : (0 : ℝ) < (25/4 : ℝ) := by norm_num
    have hpos294 : (0 : ℝ) < (29/4 : ℝ) := by norm_num
    have hpos334 : (0 : ℝ) < (33/4 : ℝ) := by norm_num
    have hpos374 : (0 : ℝ) < (37/4 : ℝ) := by norm_num
    have hpos414 : (0 : ℝ) < (41/4 : ℝ) := by norm_num
    have hpos454 : (0 : ℝ) < (45/4 : ℝ) := by norm_num
    have hpos494 : (0 : ℝ) < (49/4 : ℝ) := by norm_num
    have hpos534 : (0 : ℝ) < (53/4 : ℝ) := by norm_num
    have hpos574 : (0 : ℝ) < (57/4 : ℝ) := by norm_num
    have hpos614 : (0 : ℝ) < (61/4 : ℝ) := by norm_num
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4 : ℝ)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4 : ℝ)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne').symm
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) + Real.log (29/4 : ℝ)
        = Real.log ((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne').symm
    have m8 : Real.log ((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) + Real.log (33/4 : ℝ)
        = Real.log (((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne').symm
    have m9 : Real.log (((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) + Real.log (37/4 : ℝ)
        = Real.log ((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne').symm
    have m10 : Real.log ((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) + Real.log (41/4 : ℝ)
        = Real.log (((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne').symm
    have m11 : Real.log (((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) + Real.log (45/4 : ℝ)
        = Real.log ((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne').symm
    have m12 : Real.log ((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) + Real.log (49/4 : ℝ)
        = Real.log (((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne').symm
    have m13 : Real.log (((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) + Real.log (53/4 : ℝ)
        = Real.log ((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne').symm
    have m14 : Real.log ((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) + Real.log (57/4 : ℝ)
        = Real.log (((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) * (57/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne') hpos574.ne').symm
    have p : ((((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) * (57/4 : ℝ)) * (61/4 : ℝ))
        = 3080000333445961550625 / 4294967296 := by norm_num
    have m15 : Real.log (((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) * (57/4 : ℝ))
        + Real.log (61/4 : ℝ)
        = Real.log 3080000333445961550625 - Real.log 4294967296 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne') hpos574.ne') hpos614.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l4294967296 : Real.log (4294967296 : ℝ) = 32 * Real.log 2 := by
      have e4294967296 : (4294967296 : ℝ) = 2 ^ 32 := by norm_num
      rw [e4294967296, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, l4294967296]
  have h1307674368000 : Real.log (1307674368000 : ℝ)
      = 11 * Real.log 2 + 6 * Real.log 3 + 3 * Real.log 5 + 2 * Real.log 7
      + Real.log 11 + Real.log 13 := by
    have e1307674368000 : (1307674368000 : ℝ) = ((((((2048 * 729) * 125) * 49) * 11) * 13)) := by
      norm_num
    have e2048 : (2048 : ℝ) = 2 ^ 11 := by norm_num
    have e729 : (729 : ℝ) = 3 ^ 6 := by norm_num
    have e125 : (125 : ℝ) = 5 ^ 3 := by norm_num
    have e49 : (49 : ℝ) = 7 ^ 2 := by norm_num
    rw [e1307674368000, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), e2048, e729, e125, e49, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (3080000333445961550625 : ℝ)
      = 7 * Real.log 3 + 4 * Real.log 5 + 3 * Real.log 7 + Real.log 11
      + Real.log 13 + Real.log 17 + Real.log 19 + Real.log 29
      + Real.log 37 + Real.log 41 + Real.log 53 + Real.log 61 := by
    have e3080000333445961550625 : (3080000333445961550625 : ℝ) = ((((((((((((2187 * 625) * 343) * 11) * 13) * 17) * 19) * 29) * 37) * 41) * 53) * 61)) := by
      norm_num
    have e2187 : (2187 : ℝ) = 3 ^ 7 := by norm_num
    have e625 : (625 : ℝ) = 5 ^ 4 := by norm_num
    have e343 : (343 : ℝ) = 7 ^ 3 := by norm_num
    rw [e3080000333445961550625, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), e2187, e625, e343, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hK : Real.log (36093845893638083555411025908991160223442721593375 : ℝ)
      = 3 * Real.log 3 + 3 * Real.log 5 + 4 * Real.log 7 + 4 * Real.log 17
      + 4 * Real.log 19 + 4 * Real.log 29 + 4 * Real.log 37
      + 4 * Real.log 41 + 4 * Real.log 53 + 4 * Real.log 61 := by
    have e36093845893638083555411025908991160223442721593375 : (36093845893638083555411025908991160223442721593375 : ℝ) = ((((((((((3 ^ 3 * 5 ^ 3) * 7 ^ 4) * 17 ^ 4) * 19 ^ 4) * 29 ^ 4) * 37 ^ 4) * 41 ^ 4) * 53 ^ 4) * 61 ^ 4)) := by
      norm_num
    rw [e36093845893638083555411025908991160223442721593375, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpow : (3.588 : ℝ) ^ 4 * 36093845893638083555411025908991160223442721593375
      < 2 ^ 172 := by norm_num
  have hlog4 : 4 * Real.log (3.588 : ℝ)
        + Real.log (36093845893638083555411025908991160223442721593375 : ℝ)
      < 172 * Real.log 2 := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpow
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff (by norm_num) hGpos]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_lt_of_le ?_ hge
  have h15 : Real.log (15 : ℝ) = Real.log 3 + Real.log 5 := by
    have e15 : (15 : ℝ) = 3 * 5 := by norm_num
    rw [e15, Real.log_mul (by norm_num) (by norm_num)]
  rw [hseq, hsum, h1307674368000, hN, h15]
  linarith [hlog4, hK]

/-- Bohr–Mollerup `n = 15` upper bound at `x = 1/4`: `Gamma(1/4) < 3.648`
(mirror of `gamma_quarter_gt_BM15`; exact value
`logΓ ≤ 44·log 2 - log 3 - log 5 - log 7 - log 17 - log 19 - log 29 - log 37 - log 41 - log 53 - log 61 ≈ 1.293912, Γ ≈ 3.64702`,
i.e. `Γ ≤ (2^176/(3^4·5^4·7^4·17^4·19^4·29^4·37^4·41^4·53^4·61^4))^{1/4}`;
new interval `3.588 < Γ(1/4) < 3.648`, width `0.060`). -/
theorem gamma_quarter_lt_BM15 : Real.Gamma (1/4 : ℝ) < (3.648 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hx' : (1/4 : ℝ) ≤ 1 := by norm_num
  have hle := Real.BohrMollerup.le_logGammaSeq Real.convexOn_log_Gamma hfeq hx hx' 15
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hle
  have c15 : ((15 : ℕ) : ℝ) = (15 : ℝ) := by norm_num
  rw [c15] at hle
  have c16 : (15 : ℝ) + 1 = (16 : ℝ) := by norm_num
  rw [c16] at hle
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 15
      = (1/4 : ℝ) * Real.log 15 + Real.log 1307674368000
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ) + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ) + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ) + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ) + Real.log (49/4 : ℝ) + Real.log (53/4 : ℝ) + Real.log (57/4 : ℝ) + Real.log (61/4 : ℝ)) := by
    have f15 : Nat.factorial 15 = 1307674368000 := by decide
    have c15' : ((15 : ℕ) : ℝ) = (15 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = (1/4 : ℝ) := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = (5/4 : ℝ) := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = (9/4 : ℝ) := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = (13/4 : ℝ) := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = (17/4 : ℝ) := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = (21/4 : ℝ) := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = (25/4 : ℝ) := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = (29/4 : ℝ) := by norm_num
    have a8 : (1/4 : ℝ) + ((8 : ℕ) : ℝ) = (33/4 : ℝ) := by norm_num
    have a9 : (1/4 : ℝ) + ((9 : ℕ) : ℝ) = (37/4 : ℝ) := by norm_num
    have a10 : (1/4 : ℝ) + ((10 : ℕ) : ℝ) = (41/4 : ℝ) := by norm_num
    have a11 : (1/4 : ℝ) + ((11 : ℕ) : ℝ) = (45/4 : ℝ) := by norm_num
    have a12 : (1/4 : ℝ) + ((12 : ℕ) : ℝ) = (49/4 : ℝ) := by norm_num
    have a13 : (1/4 : ℝ) + ((13 : ℕ) : ℝ) = (53/4 : ℝ) := by norm_num
    have a14 : (1/4 : ℝ) + ((14 : ℕ) : ℝ) = (57/4 : ℝ) := by norm_num
    have a15 : (1/4 : ℝ) + ((15 : ℕ) : ℝ) = (61/4 : ℝ) := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f15, c15', Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]
    ring
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
        + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ)
        + Real.log (49/4 : ℝ) + Real.log (53/4 : ℝ) + Real.log (57/4 : ℝ)
        + Real.log (61/4 : ℝ)
      = Real.log 3080000333445961550625 - 32 * Real.log 2 := by
    have hpos14 : (0 : ℝ) < (1/4 : ℝ) := by norm_num
    have hpos54 : (0 : ℝ) < (5/4 : ℝ) := by norm_num
    have hpos94 : (0 : ℝ) < (9/4 : ℝ) := by norm_num
    have hpos134 : (0 : ℝ) < (13/4 : ℝ) := by norm_num
    have hpos174 : (0 : ℝ) < (17/4 : ℝ) := by norm_num
    have hpos214 : (0 : ℝ) < (21/4 : ℝ) := by norm_num
    have hpos254 : (0 : ℝ) < (25/4 : ℝ) := by norm_num
    have hpos294 : (0 : ℝ) < (29/4 : ℝ) := by norm_num
    have hpos334 : (0 : ℝ) < (33/4 : ℝ) := by norm_num
    have hpos374 : (0 : ℝ) < (37/4 : ℝ) := by norm_num
    have hpos414 : (0 : ℝ) < (41/4 : ℝ) := by norm_num
    have hpos454 : (0 : ℝ) < (45/4 : ℝ) := by norm_num
    have hpos494 : (0 : ℝ) < (49/4 : ℝ) := by norm_num
    have hpos534 : (0 : ℝ) < (53/4 : ℝ) := by norm_num
    have hpos574 : (0 : ℝ) < (57/4 : ℝ) := by norm_num
    have hpos614 : (0 : ℝ) < (61/4 : ℝ) := by norm_num
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4 : ℝ)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4 : ℝ)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne').symm
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) + Real.log (29/4 : ℝ)
        = Real.log ((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne').symm
    have m8 : Real.log ((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) + Real.log (33/4 : ℝ)
        = Real.log (((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne').symm
    have m9 : Real.log (((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) + Real.log (37/4 : ℝ)
        = Real.log ((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne').symm
    have m10 : Real.log ((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) + Real.log (41/4 : ℝ)
        = Real.log (((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne').symm
    have m11 : Real.log (((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) + Real.log (45/4 : ℝ)
        = Real.log ((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne').symm
    have m12 : Real.log ((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) + Real.log (49/4 : ℝ)
        = Real.log (((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne').symm
    have m13 : Real.log (((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) + Real.log (53/4 : ℝ)
        = Real.log ((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne').symm
    have m14 : Real.log ((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) + Real.log (57/4 : ℝ)
        = Real.log (((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) * (57/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne') hpos574.ne').symm
    have p : ((((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) * (57/4 : ℝ)) * (61/4 : ℝ))
        = 3080000333445961550625 / 4294967296 := by norm_num
    have m15 : Real.log (((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) * (57/4 : ℝ))
        + Real.log (61/4 : ℝ)
        = Real.log 3080000333445961550625 - Real.log 4294967296 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne') hpos574.ne') hpos614.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l4294967296 : Real.log (4294967296 : ℝ) = 32 * Real.log 2 := by
      have e4294967296 : (4294967296 : ℝ) = 2 ^ 32 := by norm_num
      rw [e4294967296, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, l4294967296]
  have h1307674368000 : Real.log (1307674368000 : ℝ)
      = 11 * Real.log 2 + 6 * Real.log 3 + 3 * Real.log 5 + 2 * Real.log 7
      + Real.log 11 + Real.log 13 := by
    have e1307674368000 : (1307674368000 : ℝ) = ((((((2048 * 729) * 125) * 49) * 11) * 13)) := by
      norm_num
    have e2048 : (2048 : ℝ) = 2 ^ 11 := by norm_num
    have e729 : (729 : ℝ) = 3 ^ 6 := by norm_num
    have e125 : (125 : ℝ) = 5 ^ 3 := by norm_num
    have e49 : (49 : ℝ) = 7 ^ 2 := by norm_num
    rw [e1307674368000, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), e2048, e729, e125, e49, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (3080000333445961550625 : ℝ)
      = 7 * Real.log 3 + 4 * Real.log 5 + 3 * Real.log 7 + Real.log 11
      + Real.log 13 + Real.log 17 + Real.log 19 + Real.log 29
      + Real.log 37 + Real.log 41 + Real.log 53 + Real.log 61 := by
    have e3080000333445961550625 : (3080000333445961550625 : ℝ) = ((((((((((((2187 * 625) * 343) * 11) * 13) * 17) * 19) * 29) * 37) * 41) * 53) * 61)) := by
      norm_num
    have e2187 : (2187 : ℝ) = 3 ^ 7 := by norm_num
    have e625 : (625 : ℝ) = 5 ^ 4 := by norm_num
    have e343 : (343 : ℝ) = 7 ^ 3 := by norm_num
    rw [e3080000333445961550625, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), e2187, e625, e343, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    have e16 : (16 : ℝ) = 2 ^ 4 := by norm_num
    rw [e16, Real.log_pow]
    push_cast
    ring
  have hKup : Real.log (541407688404571253331165388634867403351640823900625 : ℝ)
      = 4 * Real.log 3 + 4 * Real.log 5 + 4 * Real.log 7 + 4 * Real.log 17
      + 4 * Real.log 19 + 4 * Real.log 29 + 4 * Real.log 37
      + 4 * Real.log 41 + 4 * Real.log 53 + 4 * Real.log 61 := by
    have e541407688404571253331165388634867403351640823900625 : (541407688404571253331165388634867403351640823900625 : ℝ) = ((((((((((3 ^ 4 * 5 ^ 4) * 7 ^ 4) * 17 ^ 4) * 19 ^ 4) * 29 ^ 4) * 37 ^ 4) * 41 ^ 4) * 53 ^ 4) * 61 ^ 4)) := by
      norm_num
    rw [e541407688404571253331165388634867403351640823900625, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpowC : (2 : ℝ) ^ 176 < (3.648 : ℝ) ^ 4 * 541407688404571253331165388634867403351640823900625 := by
    norm_num
  have hlogC : 176 * Real.log 2
      < 4 * Real.log (3.648 : ℝ) + Real.log (541407688404571253331165388634867403351640823900625 : ℝ) := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpowC
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff hGpos (by norm_num)]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_le_of_lt hle ?_
  rw [hseq, hsum, h1307674368000, hN, h16]
  linarith [hlogC, hKup]

/-- Two-sided Bohr–Mollerup `n = 15` interval: `3.588 < Γ(1/4) < 3.648`
(width `0.060`, tightening the `n = 14` interval `3.586 < Γ < 3.649`, width `0.063`). -/
theorem gamma_quarter_bounds_BM15 :
    (3.588 : ℝ) < Real.Gamma (1/4 : ℝ) ∧ Real.Gamma (1/4 : ℝ) < (3.648 : ℝ) :=
  ⟨gamma_quarter_gt_BM15, gamma_quarter_lt_BM15⟩

/-- Bohr–Mollerup `n = 16` lower bound at `x = 1/4`: `3.59 < Gamma(1/4)`
(tightens `gamma_quarter_gt_BM15`; exact `log`-of-rational value
`logΓ ≥ 50·log 2 - log 3 - 2·log 5 - log 7 - log 13 - log 17 - log 19 - log 29 - log 37 - log 41 - log 53 - log 61 ≈ 1.278407, Γ ≈ 3.59092`,
i.e. `Γ ≥ (2^200/(3^4·5^8·7^4·13^4·17^4·19^4·29^4·37^4·41^4·53^4·61^4))^{1/4}`;
new interval `3.59 < Γ(1/4) < 3.646`, width `0.056`). -/
theorem gamma_quarter_gt_BM16 : (3.59 : ℝ) < Real.Gamma (1/4 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hge := Real.BohrMollerup.ge_logGammaSeq Real.convexOn_log_Gamma hfeq hx
    (show (16 : ℕ) ≠ 0 by norm_num)
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hge
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 16
      = (1/4 : ℝ) * Real.log 16 + Real.log 20922789888000
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ) + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ) + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ) + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ) + Real.log (49/4 : ℝ) + Real.log (53/4 : ℝ) + Real.log (57/4 : ℝ) + Real.log (61/4 : ℝ) + Real.log (65/4 : ℝ)) := by
    have f16 : Nat.factorial 16 = 20922789888000 := by decide
    have c16' : ((16 : ℕ) : ℝ) = (16 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = (1/4 : ℝ) := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = (5/4 : ℝ) := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = (9/4 : ℝ) := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = (13/4 : ℝ) := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = (17/4 : ℝ) := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = (21/4 : ℝ) := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = (25/4 : ℝ) := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = (29/4 : ℝ) := by norm_num
    have a8 : (1/4 : ℝ) + ((8 : ℕ) : ℝ) = (33/4 : ℝ) := by norm_num
    have a9 : (1/4 : ℝ) + ((9 : ℕ) : ℝ) = (37/4 : ℝ) := by norm_num
    have a10 : (1/4 : ℝ) + ((10 : ℕ) : ℝ) = (41/4 : ℝ) := by norm_num
    have a11 : (1/4 : ℝ) + ((11 : ℕ) : ℝ) = (45/4 : ℝ) := by norm_num
    have a12 : (1/4 : ℝ) + ((12 : ℕ) : ℝ) = (49/4 : ℝ) := by norm_num
    have a13 : (1/4 : ℝ) + ((13 : ℕ) : ℝ) = (53/4 : ℝ) := by norm_num
    have a14 : (1/4 : ℝ) + ((14 : ℕ) : ℝ) = (57/4 : ℝ) := by norm_num
    have a15 : (1/4 : ℝ) + ((15 : ℕ) : ℝ) = (61/4 : ℝ) := by norm_num
    have a16 : (1/4 : ℝ) + ((16 : ℕ) : ℝ) = (65/4 : ℝ) := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f16, c16', Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16]
    ring
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
        + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ)
        + Real.log (49/4 : ℝ) + Real.log (53/4 : ℝ) + Real.log (57/4 : ℝ)
        + Real.log (61/4 : ℝ) + Real.log (65/4 : ℝ)
      = Real.log 200200021673987500790625 - 34 * Real.log 2 := by
    have hpos14 : (0 : ℝ) < (1/4 : ℝ) := by norm_num
    have hpos54 : (0 : ℝ) < (5/4 : ℝ) := by norm_num
    have hpos94 : (0 : ℝ) < (9/4 : ℝ) := by norm_num
    have hpos134 : (0 : ℝ) < (13/4 : ℝ) := by norm_num
    have hpos174 : (0 : ℝ) < (17/4 : ℝ) := by norm_num
    have hpos214 : (0 : ℝ) < (21/4 : ℝ) := by norm_num
    have hpos254 : (0 : ℝ) < (25/4 : ℝ) := by norm_num
    have hpos294 : (0 : ℝ) < (29/4 : ℝ) := by norm_num
    have hpos334 : (0 : ℝ) < (33/4 : ℝ) := by norm_num
    have hpos374 : (0 : ℝ) < (37/4 : ℝ) := by norm_num
    have hpos414 : (0 : ℝ) < (41/4 : ℝ) := by norm_num
    have hpos454 : (0 : ℝ) < (45/4 : ℝ) := by norm_num
    have hpos494 : (0 : ℝ) < (49/4 : ℝ) := by norm_num
    have hpos534 : (0 : ℝ) < (53/4 : ℝ) := by norm_num
    have hpos574 : (0 : ℝ) < (57/4 : ℝ) := by norm_num
    have hpos614 : (0 : ℝ) < (61/4 : ℝ) := by norm_num
    have hpos654 : (0 : ℝ) < (65/4 : ℝ) := by norm_num
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4 : ℝ)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4 : ℝ)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne').symm
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) + Real.log (29/4 : ℝ)
        = Real.log ((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne').symm
    have m8 : Real.log ((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) + Real.log (33/4 : ℝ)
        = Real.log (((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne').symm
    have m9 : Real.log (((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) + Real.log (37/4 : ℝ)
        = Real.log ((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne').symm
    have m10 : Real.log ((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) + Real.log (41/4 : ℝ)
        = Real.log (((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne').symm
    have m11 : Real.log (((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) + Real.log (45/4 : ℝ)
        = Real.log ((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne').symm
    have m12 : Real.log ((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) + Real.log (49/4 : ℝ)
        = Real.log (((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne').symm
    have m13 : Real.log (((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) + Real.log (53/4 : ℝ)
        = Real.log ((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne').symm
    have m14 : Real.log ((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) + Real.log (57/4 : ℝ)
        = Real.log (((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) * (57/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne') hpos574.ne').symm
    have m15 : Real.log (((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) * (57/4 : ℝ)) + Real.log (61/4 : ℝ)
        = Real.log ((((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) * (57/4 : ℝ)) * (61/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne') hpos574.ne') hpos614.ne').symm
    have p : (((((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) * (57/4 : ℝ)) * (61/4 : ℝ)) * (65/4 : ℝ))
        = 200200021673987500790625 / 17179869184 := by norm_num
    have m16 : Real.log ((((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) * (57/4 : ℝ)) * (61/4 : ℝ))
        + Real.log (65/4 : ℝ)
        = Real.log 200200021673987500790625 - Real.log 17179869184 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne') hpos574.ne') hpos614.ne') hpos654.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l17179869184 : Real.log (17179869184 : ℝ) = 34 * Real.log 2 := by
      have e17179869184 : (17179869184 : ℝ) = 2 ^ 34 := by norm_num
      rw [e17179869184, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, l17179869184]
  have h20922789888000 : Real.log (20922789888000 : ℝ)
      = 15 * Real.log 2 + 6 * Real.log 3 + 3 * Real.log 5 + 2 * Real.log 7
      + Real.log 11 + Real.log 13 := by
    have e20922789888000 : (20922789888000 : ℝ) = ((((((32768 * 729) * 125) * 49) * 11) * 13)) := by
      norm_num
    have e32768 : (32768 : ℝ) = 2 ^ 15 := by norm_num
    have e729 : (729 : ℝ) = 3 ^ 6 := by norm_num
    have e125 : (125 : ℝ) = 5 ^ 3 := by norm_num
    have e49 : (49 : ℝ) = 7 ^ 2 := by norm_num
    rw [e20922789888000, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), e32768, e729, e125, e49, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (200200021673987500790625 : ℝ)
      = 7 * Real.log 3 + 5 * Real.log 5 + 3 * Real.log 7 + Real.log 11
      + 2 * Real.log 13 + Real.log 17 + Real.log 19 + Real.log 29
      + Real.log 37 + Real.log 41 + Real.log 53 + Real.log 61 := by
    have e200200021673987500790625 : (200200021673987500790625 : ℝ) = ((((((((((((2187 * 3125) * 343) * 11) * 169) * 17) * 19) * 29) * 37) * 41) * 53) * 61)) := by
      norm_num
    have e2187 : (2187 : ℝ) = 3 ^ 7 := by norm_num
    have e3125 : (3125 : ℝ) = 5 ^ 5 := by norm_num
    have e343 : (343 : ℝ) = 7 ^ 3 := by norm_num
    have e169 : (169 : ℝ) = 13 ^ 2 := by norm_num
    rw [e200200021673987500790625, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), e2187, e3125, e343, e169, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hK : Real.log (9664465617826849728994634165500279941953883482141094140625 : ℝ)
      = 4 * Real.log 3 + 8 * Real.log 5 + 4 * Real.log 7 + 4 * Real.log 13
      + 4 * Real.log 17 + 4 * Real.log 19 + 4 * Real.log 29
      + 4 * Real.log 37 + 4 * Real.log 41 + 4 * Real.log 53 + 4 * Real.log 61 := by
    have e9664465617826849728994634165500279941953883482141094140625 : (9664465617826849728994634165500279941953883482141094140625 : ℝ) = (((((((((((3 ^ 4 * 5 ^ 8) * 7 ^ 4) * 13 ^ 4) * 17 ^ 4) * 19 ^ 4) * 29 ^ 4) * 37 ^ 4) * 41 ^ 4) * 53 ^ 4) * 61 ^ 4)) := by
      norm_num
    rw [e9664465617826849728994634165500279941953883482141094140625, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpow : (3.59 : ℝ) ^ 4 * 9664465617826849728994634165500279941953883482141094140625
      < 2 ^ 200 := by norm_num
  have hlog4 : 4 * Real.log (3.59 : ℝ)
        + Real.log (9664465617826849728994634165500279941953883482141094140625 : ℝ)
      < 200 * Real.log 2 := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpow
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff (by norm_num) hGpos]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_lt_of_le ?_ hge
  have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    have e16 : (16 : ℝ) = 2 ^ 4 := by norm_num
    rw [e16, Real.log_pow]
    push_cast
    ring
  rw [hseq, hsum, h20922789888000, hN, h16]
  linarith [hlog4, hK]

/-- Bohr–Mollerup `n = 16` upper bound at `x = 1/4`: `Gamma(1/4) < 3.646`
(mirror of `gamma_quarter_gt_BM16`; exact value
`logΓ ≤ 49·log 2 - log 3 - 2·log 5 - log 7 - log 13 - 0.75·log 17 - log 19 - log 29 - log 37 - log 41 - log 53 - log 61 ≈ 1.293564, Γ ≈ 3.64576`,
i.e. `Γ ≤ (2^196/(3^4·5^8·7^4·13^4·17^3·19^4·29^4·37^4·41^4·53^4·61^4))^{1/4}`;
new interval `3.59 < Γ(1/4) < 3.646`, width `0.056`). -/
theorem gamma_quarter_lt_BM16 : Real.Gamma (1/4 : ℝ) < (3.646 : ℝ) := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hx : (0 : ℝ) < 1/4 := by norm_num
  have hx' : (1/4 : ℝ) ≤ 1 := by norm_num
  have hle := Real.BohrMollerup.le_logGammaSeq Real.convexOn_log_Gamma hfeq hx hx' 16
  have h1 : (Real.log ∘ Real.Gamma) (1 : ℝ) = 0 := by
    simp [Real.Gamma_one]
  rw [h1, zero_add] at hle
  have c16 : ((16 : ℕ) : ℝ) = (16 : ℝ) := by norm_num
  rw [c16] at hle
  have c17 : (16 : ℝ) + 1 = (17 : ℝ) := by norm_num
  rw [c17] at hle
  have hseq : Real.BohrMollerup.logGammaSeq (1/4 : ℝ) 16
      = (1/4 : ℝ) * Real.log 16 + Real.log 20922789888000
        - (Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ) + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ) + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ) + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ) + Real.log (49/4 : ℝ) + Real.log (53/4 : ℝ) + Real.log (57/4 : ℝ) + Real.log (61/4 : ℝ) + Real.log (65/4 : ℝ)) := by
    have f16 : Nat.factorial 16 = 20922789888000 := by decide
    have c16' : ((16 : ℕ) : ℝ) = (16 : ℝ) := by norm_num
    have a0 : (1/4 : ℝ) + ((0 : ℕ) : ℝ) = (1/4 : ℝ) := by norm_num
    have a1 : (1/4 : ℝ) + ((1 : ℕ) : ℝ) = (5/4 : ℝ) := by norm_num
    have a2 : (1/4 : ℝ) + ((2 : ℕ) : ℝ) = (9/4 : ℝ) := by norm_num
    have a3 : (1/4 : ℝ) + ((3 : ℕ) : ℝ) = (13/4 : ℝ) := by norm_num
    have a4 : (1/4 : ℝ) + ((4 : ℕ) : ℝ) = (17/4 : ℝ) := by norm_num
    have a5 : (1/4 : ℝ) + ((5 : ℕ) : ℝ) = (21/4 : ℝ) := by norm_num
    have a6 : (1/4 : ℝ) + ((6 : ℕ) : ℝ) = (25/4 : ℝ) := by norm_num
    have a7 : (1/4 : ℝ) + ((7 : ℕ) : ℝ) = (29/4 : ℝ) := by norm_num
    have a8 : (1/4 : ℝ) + ((8 : ℕ) : ℝ) = (33/4 : ℝ) := by norm_num
    have a9 : (1/4 : ℝ) + ((9 : ℕ) : ℝ) = (37/4 : ℝ) := by norm_num
    have a10 : (1/4 : ℝ) + ((10 : ℕ) : ℝ) = (41/4 : ℝ) := by norm_num
    have a11 : (1/4 : ℝ) + ((11 : ℕ) : ℝ) = (45/4 : ℝ) := by norm_num
    have a12 : (1/4 : ℝ) + ((12 : ℕ) : ℝ) = (49/4 : ℝ) := by norm_num
    have a13 : (1/4 : ℝ) + ((13 : ℕ) : ℝ) = (53/4 : ℝ) := by norm_num
    have a14 : (1/4 : ℝ) + ((14 : ℕ) : ℝ) = (57/4 : ℝ) := by norm_num
    have a15 : (1/4 : ℝ) + ((15 : ℕ) : ℝ) = (61/4 : ℝ) := by norm_num
    have a16 : (1/4 : ℝ) + ((16 : ℕ) : ℝ) = (65/4 : ℝ) := by norm_num
    unfold Real.BohrMollerup.logGammaSeq
    rw [f16, c16', Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16]
    ring
  have hsum : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ) + Real.log (9/4 : ℝ)
        + Real.log (13/4 : ℝ) + Real.log (17/4 : ℝ) + Real.log (21/4 : ℝ)
        + Real.log (25/4 : ℝ) + Real.log (29/4 : ℝ) + Real.log (33/4 : ℝ)
        + Real.log (37/4 : ℝ) + Real.log (41/4 : ℝ) + Real.log (45/4 : ℝ)
        + Real.log (49/4 : ℝ) + Real.log (53/4 : ℝ) + Real.log (57/4 : ℝ)
        + Real.log (61/4 : ℝ) + Real.log (65/4 : ℝ)
      = Real.log 200200021673987500790625 - 34 * Real.log 2 := by
    have hpos14 : (0 : ℝ) < (1/4 : ℝ) := by norm_num
    have hpos54 : (0 : ℝ) < (5/4 : ℝ) := by norm_num
    have hpos94 : (0 : ℝ) < (9/4 : ℝ) := by norm_num
    have hpos134 : (0 : ℝ) < (13/4 : ℝ) := by norm_num
    have hpos174 : (0 : ℝ) < (17/4 : ℝ) := by norm_num
    have hpos214 : (0 : ℝ) < (21/4 : ℝ) := by norm_num
    have hpos254 : (0 : ℝ) < (25/4 : ℝ) := by norm_num
    have hpos294 : (0 : ℝ) < (29/4 : ℝ) := by norm_num
    have hpos334 : (0 : ℝ) < (33/4 : ℝ) := by norm_num
    have hpos374 : (0 : ℝ) < (37/4 : ℝ) := by norm_num
    have hpos414 : (0 : ℝ) < (41/4 : ℝ) := by norm_num
    have hpos454 : (0 : ℝ) < (45/4 : ℝ) := by norm_num
    have hpos494 : (0 : ℝ) < (49/4 : ℝ) := by norm_num
    have hpos534 : (0 : ℝ) < (53/4 : ℝ) := by norm_num
    have hpos574 : (0 : ℝ) < (57/4 : ℝ) := by norm_num
    have hpos614 : (0 : ℝ) < (61/4 : ℝ) := by norm_num
    have hpos654 : (0 : ℝ) < (65/4 : ℝ) := by norm_num
    have m1 : Real.log (1/4 : ℝ) + Real.log (5/4 : ℝ)
        = Real.log ((1/4 : ℝ) * (5/4 : ℝ)) :=
      (Real.log_mul hpos14.ne' hpos54.ne').symm
    have m2 : Real.log ((1/4 : ℝ) * (5/4 : ℝ)) + Real.log (9/4 : ℝ)
        = Real.log (((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne').symm
    have m3 : Real.log (((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) + Real.log (13/4 : ℝ)
        = Real.log ((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne').symm
    have m4 : Real.log ((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) + Real.log (17/4 : ℝ)
        = Real.log (((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne').symm
    have m5 : Real.log (((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) + Real.log (21/4 : ℝ)
        = Real.log ((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne').symm
    have m6 : Real.log ((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) + Real.log (25/4 : ℝ)
        = Real.log (((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne').symm
    have m7 : Real.log (((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) + Real.log (29/4 : ℝ)
        = Real.log ((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne').symm
    have m8 : Real.log ((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) + Real.log (33/4 : ℝ)
        = Real.log (((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne').symm
    have m9 : Real.log (((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) + Real.log (37/4 : ℝ)
        = Real.log ((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne').symm
    have m10 : Real.log ((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) + Real.log (41/4 : ℝ)
        = Real.log (((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne').symm
    have m11 : Real.log (((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) + Real.log (45/4 : ℝ)
        = Real.log ((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne').symm
    have m12 : Real.log ((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) + Real.log (49/4 : ℝ)
        = Real.log (((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne').symm
    have m13 : Real.log (((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) + Real.log (53/4 : ℝ)
        = Real.log ((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne').symm
    have m14 : Real.log ((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) + Real.log (57/4 : ℝ)
        = Real.log (((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) * (57/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne') hpos574.ne').symm
    have m15 : Real.log (((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) * (57/4 : ℝ)) + Real.log (61/4 : ℝ)
        = Real.log ((((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) * (57/4 : ℝ)) * (61/4 : ℝ)) :=
      (Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne') hpos574.ne') hpos614.ne').symm
    have p : (((((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) * (57/4 : ℝ)) * (61/4 : ℝ)) * (65/4 : ℝ))
        = 200200021673987500790625 / 17179869184 := by norm_num
    have m16 : Real.log ((((((((((((((((1/4 : ℝ) * (5/4 : ℝ)) * (9/4 : ℝ)) * (13/4 : ℝ)) * (17/4 : ℝ)) * (21/4 : ℝ)) * (25/4 : ℝ)) * (29/4 : ℝ)) * (33/4 : ℝ)) * (37/4 : ℝ)) * (41/4 : ℝ)) * (45/4 : ℝ)) * (49/4 : ℝ)) * (53/4 : ℝ)) * (57/4 : ℝ)) * (61/4 : ℝ))
        + Real.log (65/4 : ℝ)
        = Real.log 200200021673987500790625 - Real.log 17179869184 := by
      rw [← Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hpos14.ne' hpos54.ne') hpos94.ne') hpos134.ne') hpos174.ne') hpos214.ne') hpos254.ne') hpos294.ne') hpos334.ne') hpos374.ne') hpos414.ne') hpos454.ne') hpos494.ne') hpos534.ne') hpos574.ne') hpos614.ne') hpos654.ne', p,
        Real.log_div (by norm_num) (by norm_num)]
    have l17179869184 : Real.log (17179869184 : ℝ) = 34 * Real.log 2 := by
      have e17179869184 : (17179869184 : ℝ) = 2 ^ 34 := by norm_num
      rw [e17179869184, Real.log_pow]
      push_cast
      ring
    linarith [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, l17179869184]
  have h20922789888000 : Real.log (20922789888000 : ℝ)
      = 15 * Real.log 2 + 6 * Real.log 3 + 3 * Real.log 5 + 2 * Real.log 7
      + Real.log 11 + Real.log 13 := by
    have e20922789888000 : (20922789888000 : ℝ) = ((((((32768 * 729) * 125) * 49) * 11) * 13)) := by
      norm_num
    have e32768 : (32768 : ℝ) = 2 ^ 15 := by norm_num
    have e729 : (729 : ℝ) = 3 ^ 6 := by norm_num
    have e125 : (125 : ℝ) = 5 ^ 3 := by norm_num
    have e49 : (49 : ℝ) = 7 ^ 2 := by norm_num
    rw [e20922789888000, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), e32768, e729, e125, e49, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hN : Real.log (200200021673987500790625 : ℝ)
      = 7 * Real.log 3 + 5 * Real.log 5 + 3 * Real.log 7 + Real.log 11
      + 2 * Real.log 13 + Real.log 17 + Real.log 19 + Real.log 29
      + Real.log 37 + Real.log 41 + Real.log 53 + Real.log 61 := by
    have e200200021673987500790625 : (200200021673987500790625 : ℝ) = ((((((((((((2187 * 3125) * 343) * 11) * 169) * 17) * 19) * 29) * 37) * 41) * 53) * 61)) := by
      norm_num
    have e2187 : (2187 : ℝ) = 3 ^ 7 := by norm_num
    have e3125 : (3125 : ℝ) = 5 ^ 5 := by norm_num
    have e343 : (343 : ℝ) = 7 ^ 3 := by norm_num
    have e169 : (169 : ℝ) = 13 ^ 2 := by norm_num
    rw [e200200021673987500790625, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), e2187, e3125, e343, e169, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hKup : Real.log (568497977519226454646743186205898820114934322478887890625 : ℝ)
      = 4 * Real.log 3 + 8 * Real.log 5 + 4 * Real.log 7 + 4 * Real.log 13
      + 3 * Real.log 17 + 4 * Real.log 19 + 4 * Real.log 29
      + 4 * Real.log 37 + 4 * Real.log 41 + 4 * Real.log 53 + 4 * Real.log 61 := by
    have e568497977519226454646743186205898820114934322478887890625 : (568497977519226454646743186205898820114934322478887890625 : ℝ) = (((((((((((3 ^ 4 * 5 ^ 8) * 7 ^ 4) * 13 ^ 4) * 17 ^ 3) * 19 ^ 4) * 29 ^ 4) * 37 ^ 4) * 41 ^ 4) * 53 ^ 4) * 61 ^ 4)) := by
      norm_num
    rw [e568497977519226454646743186205898820114934322478887890625, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpowC : (2 : ℝ) ^ 196 < (3.646 : ℝ) ^ 4 * 568497977519226454646743186205898820114934322478887890625 := by
    norm_num
  have hlogC : 196 * Real.log 2
      < 4 * Real.log (3.646 : ℝ) + Real.log (568497977519226454646743186205898820114934322478887890625 : ℝ) := by
    have h := (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpowC
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow] at h
    push_cast at h
    linarith
  have hGpos : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos hx
  rw [← Real.log_lt_log_iff hGpos (by norm_num)]
  have hlogG : Real.log (Real.Gamma (1/4 : ℝ))
      = (Real.log ∘ Real.Gamma) (1/4 : ℝ) := rfl
  rw [hlogG]
  refine lt_of_le_of_lt hle ?_
  rw [hseq, hsum, h20922789888000, hN]
  linarith [hlogC, hKup]

/-- Two-sided Bohr–Mollerup `n = 16` interval: `3.59 < Γ(1/4) < 3.646`
(width `0.056`, tightening the `n = 15` interval `3.588 < Γ < 3.648`, width `0.060`). -/
theorem gamma_quarter_bounds_BM16 :
    (3.59 : ℝ) < Real.Gamma (1/4 : ℝ) ∧ Real.Gamma (1/4 : ℝ) < (3.646 : ℝ) :=
  ⟨gamma_quarter_gt_BM16, gamma_quarter_lt_BM16⟩



/-! ### Remaining gap (no `sorry`; explicit hypotheses).

With the unconditional pieces above plus `zeta_rigorous`
(`etaPartial 2 ≤ L ≤ etaPartial 3 ≤ 1`, `0 < etaPartial 2`):

* MISSING FEEDER 1 (analytic continuation): the identity
  `riemannZeta (1/2:ℂ) = (L:ℂ) / (1 - √2)` where `L` is the Tendsto limit of
  the eta partial sums (`L ≈ 0.604`). Mathlib has no Dirichlet-eta function and
  no `η(s) = (1 - 2^(1-s))·ζ(s)` for `Re s > 0, s ≠ 1`; proving it needs the
  alternating-series `HasSum` at `s = 1/2` plus analytic continuation, i.e. the
  `tendsto`/`HasSum` link currently absent.
* MISSING FEEDER 2 (tightness): `Λ₀(1/2) = Γℝ(1/2)·ζ(1/2)+4 ≈ 0.023` lies
  `≈ 0.02` from 0. Status: the Gamma side now has a rigorous two-sided
  interval `3.33 < Γ(1/4) < 3.78` (`gamma_quarter_bounds`, width `0.45`,
  true value ≈ 3.6256), `0.751 < π^(-1/4) < 0.752`
  (`pi_rpow_neg_quarter_bounds`), hence `2.50 < Γℝ(1/2).re < 2.85`
  (`Gammaℝ_half_re_bounds`, true value ≈ 2.7233) — a ~10× tightening over
  the old crude `(0, 4]`. This alone does not separate yet: with
  `S₂ = 1-1/√2 ≈ 0.293 ≤ L ≤ 1` the product interval still contains `-4`.
  Closing needs `L` to `±0.003` (∼10⁴ alternating terms,
  remainder `≤ 1/√(N+1)`) and `Γ(1/4)` to `±0.01`. The natural next step on
  the Gamma side is finite Bohr–Mollerup approximants
  (`BohrMollerup.ge_logGammaSeq`/`le_logGammaSeq` at `x = 1/4`, whose values
  are exact `log`-of-rational identities, e.g. `n = 1` gives `Γ(1/4) ≥ 16/5`)
  plus fourth-root bounds as in `pi_rpow_quarter_gt/lt` (width there scales
  like `O(1/n)` in `log`, so `n ≈ 60`–`100` suffices for `±0.01`), or
  verified quadrature of the `Real.Gamma` integral; then
  `completed₀_half_ne_zero_of_product_ne_neg_four`.
* `taylorCoeff_zero_ne_zero` follows from `taylorCoeff_zero_eq` plus the above
  once feeders 1–2 are supplied.
-/

end JensenRH
