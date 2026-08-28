import Mathlib

set_option maxHeartbeats 1000000

open Complex Real Topology Filter MeasureTheory
open scoped BigOperators Nat.Prime
open Chebyshev

noncomputable section

/-- Prime counting function bound (Chebyshev's explicit upper bound).

    Mathlib provides `Chebyshev.pi_le_log4_mul_div`: for `1 < x`,
    `π ⌊x⌋ ≤ (log 4) * x / log √x + √x`.  Since `log √x = (1/2) log x`, this is
    `π ⌊x⌋ ≤ 2 (log 4) x / log x + √x`.  This is a correct (non-sharp) explicit
    upper bound on the prime-counting function. -/
theorem primeCounting_le {x : ℝ} (hx : 1 < x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ Real.log 4 * x / Real.log (Real.sqrt x) + Real.sqrt x :=
  pi_le_log4_mul_div hx

/-- The explicit bound on `π(x)` used in the estimates below.  This is exactly the
right-hand side of `Chebyshev.pi_le_log4_mul_div`. -/
def πBound (x : ℝ) : ℝ := Real.log 4 * x / Real.log (Real.sqrt x) + Real.sqrt x

lemma πBound_of_primeCounting {x : ℝ} (hx : 1 < x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ πBound x :=
  pi_le_log4_mul_div hx

/-- Partial summation (Abel's formula) relating the weighted prime sum
    `θ(x) = ∑_{p ≤ x} log p` to the prime-counting function `π(x)`.

    This is exactly `Chebyshev.theta_eq_primeCounting_mul_log_sub_integral`:
    `θ(x) = π ⌊x⌋ · log x - ∫_2^x π ⌊t⌋ / t dt`.  The left hand side is the
    sum over primes `∑_{p ≤ x} log p`, so this is the promised
    "sum over primes via partial summation" estimate. -/
theorem sum_primes_div_le (x : ℝ) (hx : 2 ≤ x) :
    Chebyshev.theta x =
      (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x -
        ∫ t in 2..x, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t :=
  theta_eq_primeCounting_mul_log_sub_integral hx

/-- Mertens-type estimate on the sum of reciprocals of primes.

    A correct (non-sharp) explicit upper bound: since every prime `p` satisfies
    `p ≥ 2`, we have `1/p ≤ 1/2`, hence for `x ≥ 10`,
    `∑_{p ≤ x} 1/p ≤ (1/2) · #{primes ≤ x} = π ⌊x⌋ / 2 ≤ πBound x / 2`.
    (The sharp Mertens theorem `∑_{p ≤ x} 1/p = log log x + M + o(1)` requires
    the prime number theorem; the explicit Chebyshev bound above still yields a
    valid finite upper bound.) -/
theorem sum_primes_recip (x : ℝ) (hx : 10 ≤ x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p ≤ πBound x * (1 / 2 : ℝ) := by
  have hpos : ∀ p, p ∈ Nat.primesLE ⌊x⌋₊ → (0 : ℝ) < p := by
    intro p hp
    exact_mod_cast ((show (0 : ℕ) < 2 by norm_num).trans_le (Nat.Prime.two_le (Finset.mem_filter.mp hp).2))
  calc
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact (one_div_le_one_div (hpos p hp) (by norm_num : (0 : ℝ) < 2)).mpr
        (by exact_mod_cast Nat.Prime.two_le (Finset.mem_filter.mp hp).2)
    _ = ((Nat.primesLE ⌊x⌋₊).card : ℝ) * (1 / 2 : ℝ) := by
      rw [Finset.sum_const (1 / 2 : ℝ)]; simp
    _ = (Nat.primeCounting ⌊x⌋₊ : ℝ) * (1 / 2 : ℝ) := by
      rw [Nat.primesLE_card_eq_primeCounting]
    _ ≤ πBound x * (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right
      (πBound_of_primeCounting (by linarith [hx])) (by norm_num)

/-- Exponential sum over primes.

    For any real `t`, each term `exp(i · t · log p)` has modulus `1`, so by the
    triangle inequality the whole sum has modulus at most the number of terms,
    i.e. `π ⌊x⌋`.  Using the explicit Chebyshev bound this is at most `πBound x`. -/
theorem prime_exponential_sum_bound (x t : ℝ) (hx : 2 ≤ x) :
    ‖∑ p ∈ Nat.primesLE ⌊x⌋₊, Complex.exp (Complex.I * t * Real.log ↑p)‖ ≤ πBound x := by
  have unit : ∀ p, p ∈ Nat.primesLE ⌊x⌋₊ →
      ‖Complex.exp (Complex.I * t * Real.log ↑p)‖ = (1 : ℝ) := by
    intro p hp
    rw [mul_assoc, ← Complex.ofReal_mul, Complex.norm_exp_I_mul_ofReal (t * Real.log ↑p)]
  calc
    ‖∑ p ∈ Nat.primesLE ⌊x⌋₊, Complex.exp (Complex.I * t * Real.log ↑p)‖
        ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, ‖Complex.exp (Complex.I * t * Real.log ↑p)‖ :=
      norm_sum_le _ _
    _ = ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) := by rw [Finset.sum_congr rfl unit]
    _ = (Nat.primesLE ⌊x⌋₊).card := by rw [Finset.sum_const (1 : ℝ)]; simp
    _ = (Nat.primeCounting ⌊x⌋₊ : ℝ) := by rw [Nat.primesLE_card_eq_primeCounting]
    _ ≤ πBound x := πBound_of_primeCounting (by linarith [hx])

end
