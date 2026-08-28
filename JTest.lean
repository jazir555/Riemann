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

/-- `(k+1) * C(d+1,k+1) = (d+1) * C(d,k)` (cast to ℝ). -/
lemma hbin (d k : ℕ) :
    (↑(Nat.choose (d + 1) (k + 1)) : ℝ) * ↑(k + 1) = ↑(d + 1) * ↑(Nat.choose d k) := by
  rw [← Nat.cast_mul, ← Nat.add_one_mul_choose_eq d k, Nat.cast_mul]

/-- Pure algebraic identity: derivative of J_{d+1,n} equals (d+1)·J_{d,n+1}. -/
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

/-- `derivative_q_eq` transported through the algebra map to `Polynomial ℂ`. -/
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

end JensenRHTest

end
