import Mathlib
import Zeta23.FromPNTPlus.Mertens

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

/-! ## Sharp Mertens estimates, imported from the `Zeta23` library

The bounds above are the elementary Chebyshev ones (`π(x) ≤ πBound x`), which are
*correct but not sharp*.  `Zeta23.FromPNTPlus.Mertens` proves **Mertens' first theorem
with an explicit constant**, stated against Mathlib's `ArithmeticFunction.vonMangoldt`:

  `|∑_{d ≤ x} Λ(d)/d − log x| ≤ log 4 + 4`   (`Mertens.sum_mangoldt_div_eq_log`).

Since `Zeta23` uses Mathlib's `vonMangoldt` (and Mathlib's `riemannZeta`), that estimate
transfers verbatim; everything below is unconditional and sorry-free.  In particular
`sum_primes_recip_le_log` replaces the `πBound x / 2 = O(x / log x)` bound of
`sum_primes_recip` by the far better `O(log x)` bound. -/

/-- **Mertens' first theorem (von Mangoldt form), with an explicit constant**:
`|∑_{d ≤ x} Λ(d)/d − log x| ≤ log 4 + 4` for `x ≥ 1`.  This is
`Zeta23`'s `Mertens.sum_mangoldt_div_eq_log`, applied to Mathlib's `vonMangoldt`. -/
theorem mertens_first_vonMangoldt {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt d / d - Real.log x|
      ≤ Real.log 4 + 4 :=
  Mertens.sum_mangoldt_div_eq_log hx

/-- Upper half of Mertens' first theorem. -/
theorem sum_vonMangoldt_div_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt d / d
      ≤ Real.log x + (Real.log 4 + 4) := by
  have h := abs_le.mp (mertens_first_vonMangoldt hx)
  linarith [h.2]

/-- Lower half of Mertens' first theorem. -/
theorem sum_vonMangoldt_div_ge {x : ℝ} (hx : 1 ≤ x) :
    Real.log x - (Real.log 4 + 4)
      ≤ ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt d / d := by
  have h := abs_le.mp (mertens_first_vonMangoldt hx)
  linarith [h.1]

/-- **Sharp Chebyshev–Mertens bound for the prime sum** `∑_{p ≤ x} (log p)/p ≤ log x + log 4 + 4`.
The primes form a subset of `Ioc 0 ⌊x⌋₊` on which `Λ p = log p`, and all `Λ`-terms are
nonnegative, so this follows from `sum_vonMangoldt_div_le`. -/
theorem sum_primes_log_div_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p ≤ Real.log x + (Real.log 4 + 4) := by
  have hsubset : Nat.primesLE ⌊x⌋₊ ⊆ Finset.Ioc 0 ⌊x⌋₊ := by
    intro p hp
    exact Finset.mem_Ioc.mpr ⟨(Nat.prime_of_mem_primesLE hp).pos, Nat.le_of_mem_primesLE hp⟩
  have heq : ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p
      = ∑ p ∈ Nat.primesLE ⌊x⌋₊, ArithmeticFunction.vonMangoldt p / p :=
    Finset.sum_congr rfl (fun p hp => by
      rw [ArithmeticFunction.vonMangoldt_apply_prime (Nat.prime_of_mem_primesLE hp)])
  rw [heq]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_) (sum_vonMangoldt_div_le hx)
  intro d _ _
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d)

/-- **Mertens-type bound on the sum of prime reciprocals**:
`∑_{p ≤ x} 1/p ≤ (log x + log 4 + 4)/log 2`.
Each prime satisfies `log 2 ≤ log p`, so `1/p ≤ (log p / p)/log 2`, and the claim follows from
`sum_primes_log_div_le`.  (The truly sharp form `∑_{p ≤ x} 1/p = log log x + M + o(1)` needs
partial summation on top of Mertens' first theorem; this `O(log x)` bound is already an
exponential improvement on the Chebyshev bound `sum_primes_recip`.) -/
theorem sum_primes_recip_le_log {x : ℝ} (hx : 1 ≤ x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p
      ≤ (Real.log x + (Real.log 4 + 4)) / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hterm : ∀ p ∈ Nat.primesLE ⌊x⌋₊,
      (1 : ℝ) / p ≤ (Real.log p / p) / Real.log 2 := by
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hppos : (0 : ℝ) < (p : ℝ) := by linarith
    have hlogp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
    rw [le_div_iff₀ hlog2]
    have hdiv : Real.log 2 / (p : ℝ) ≤ Real.log p / (p : ℝ) := by gcongr
    calc (1 : ℝ) / p * Real.log 2 = Real.log 2 / (p : ℝ) := by ring
      _ ≤ Real.log p / (p : ℝ) := hdiv
  calc ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p
      ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log p / p) / Real.log 2 :=
        Finset.sum_le_sum hterm
    _ = (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p) / Real.log 2 := by
        rw [Finset.sum_div]
    _ ≤ (Real.log x + (Real.log 4 + 4)) / Real.log 2 := by
        gcongr
        exact sum_primes_log_div_le hx

end
