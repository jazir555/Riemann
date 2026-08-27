import Mathlib
set_option maxHeartbeats 1000000

noncomputable section

namespace JensenRHTest

open scoped BigOperators

def taylorCoeff (n : ℕ) : ℝ := 0

def jensenPoly (d n : ℕ) : Polynomial ℂ :=
  (Finset.sum (Finset.range (d + 1)) (fun k =>
    Polynomial.monomial k ((Nat.choose d k : ℝ) * taylorCoeff (n + k))))
    |>.map (algebraMap ℝ ℂ)

/-- Approximation lemma: derivative commutes up to the binomial identity. -/
theorem derivative_q_eq (d n : ℕ) :
    (Polynomial.derivative
        (Finset.sum (Finset.range (d + 2)) (fun k =>
          Polynomial.monomial k (↑(Nat.choose (d + 1) k) * taylorCoeff (n + k)))) :
        Polynomial ℝ) =
      Polynomial.C ((d + 1 : ℕ) : ℝ) *
        (Finset.sum (Finset.range (d + 1)) (fun k =>
          Polynomial.monomial k (↑(Nat.choose d k) * taylorCoeff (n + 1 + k)))) := by
  let q : Polynomial ℝ := Finset.sum (Finset.range (d + 2))
    (fun k => Polynomial.monomial k (↑(Nat.choose (d + 1) k) * taylorCoeff (n + k)))
  let p : Polynomial ℝ := Finset.sum (Finset.range (d + 1))
    (fun k => Polynomial.monomial k (↑(Nat.choose d k) * taylorCoeff (n + 1 + k)))
  change Polynomial.derivative q = Polynomial.C ((d + 1 : ℕ) : ℝ) * p
  apply Polynomial.ext
  intro m
  rw [Polynomial.coeff_derivative]
  simp only [q, p, Polynomial.coeff_sum, Polynomial.coeff_monomial,
    Polynomial.coeff_C_mul, if_true, if_false, Finset.mem_range, Finset.sum_ite_eq',
    Finset.sum_ite_eq, zero_mul, mul_zero, add_zero, zero_add]
  by_cases hm : m ≤ d
  · have h1 : m + 1 < d + 2 := by omega
    have h2 : m < d + 1 := by omega
    simp [h1, h2]
    have hb : ↑((Nat.choose (d + 1) (m + 1)) * (m + 1)) = ↑((d + 1) * Nat.choose d m) := by
      congr 1
      rw [Nat.add_one_mul_choose_eq d m]
    have ht : taylorCoeff (n + (m + 1)) = taylorCoeff (n + 1 + m) := by
      congr 1
      omega
    rw [show ↑(m + 1) * (↑(Nat.choose (d + 1) (m + 1)) * taylorCoeff (n + (m + 1))) =
          ↑(Nat.choose (d + 1) (m + 1)) * ↑(m + 1) * taylorCoeff (n + (m + 1)) by ring]
    rw [← Nat.cast_mul, hb, Nat.cast_mul, ht]
    ring
  · have h1 : ¬ m + 1 < d + 2 := by omega
    have h2 : ¬ m < d + 1 := by omega
    simp [h1, h2]

/-- derivative_q_eq transported through the algebra map to `Polynomial ℂ`. -/
theorem jensenPoly_derivative (d n : ℕ) :
    (jensenPoly (d + 1) n).derivative =
      Polynomial.C ((d + 1 : ℕ) : ℂ) * jensenPoly d (n + 1) := by
  let φ : ℝ →+* ℂ := algebraMap ℝ ℂ
  let q' : Polynomial ℝ := Finset.sum (Finset.range (d + 2))
    (fun k => Polynomial.monomial k (↑(Nat.choose (d + 1) k) * taylorCoeff (n + k)))
  let p' : Polynomial ℝ := Finset.sum (Finset.range (d + 1))
    (fun k => Polynomial.monomial k (↑(Nat.choose d k) * taylorCoeff (n + 1 + k)))
  change Polynomial.derivative (q'.map φ) = Polynomial.C ((d + 1 : ℕ) : ℂ) * p'.map φ
  rw [Polynomial.derivative_map q' φ, derivative_q_eq d n]
  rw [Polynomial.map_mul, Polynomial.map_C]
  rfl

end JensenRHTest

end