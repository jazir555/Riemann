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
