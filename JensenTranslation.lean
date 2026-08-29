import Mathlib
import riemann_hypothesis

set_option maxHeartbeats 1000000

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

/-- A sum of a multiset of nonnegative reals is nonnegative. -/
lemma msum_nonneg {M : Multiset ℝ} (h : ∀ x ∈ M, 0 ≤ x) : 0 ≤ M.sum :=
  Multiset.sum_nonneg h

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

/-- PÓLYA'S SHIFT REDUCTION (Pólya 1927; GORZ 2019):
    Hyperbolicity at shift n = 0 for every degree d implies hyperbolicity
    for all shifts n, because J_{d,n} is a constant multiple of the n-th
    derivative of J_{d+n,0} (by iterating `jensenPoly_derivative`) and
    differentiation preserves hyperbolicity (by `derivative_hyperbolic`).
    Hence RH ⟺ ∀ d, J_{d,0} is hyperbolic. -/
theorem all_shifts_from_zero (h0 : ∀ d : ℕ, Hyperbolic (jensenPoly d 0)) :
    ∀ d n : ℕ, Hyperbolic (jensenPoly d n) := by
  sorry

/-- THE SHIFT-REDUCED TRANSLATION: RH ⟺ hyperbolicity of the Jensen
    polynomials at shift zero, for every degree d.
    (Pólya 1927; Griffin–Ono–Rolen–Zagier 2019, "it would be enough to
    show hyperbolicity for the J_{d,0}".) -/
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

end JensenRH
