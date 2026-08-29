import Mathlib
import Zeta23.FromPNTPlus.Mertens

set_option maxHeartbeats 1000000

open Complex Real Topology Filter MeasureTheory
open scoped BigOperators Nat.Prime
open Chebyshev

noncomputable section

/-- **Mertens' first theorem (von Mangoldt form), with an explicit constant.** -/
theorem mertens_first_vonMangoldt {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt d / d - Real.log x|
      ≤ Real.log 4 + 4 :=
  Mertens.sum_mangoldt_div_eq_log hx

theorem sum_vonMangoldt_div_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt d / d
      ≤ Real.log x + (Real.log 4 + 4) := by
  have h := abs_le.mp (mertens_first_vonMangoldt hx)
  linarith [h.2]

theorem sum_vonMangoldt_div_ge {x : ℝ} (hx : 1 ≤ x) :
    Real.log x - (Real.log 4 + 4)
      ≤ ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt d / d := by
  have h := abs_le.mp (mertens_first_vonMangoldt hx)
  linarith [h.1]

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
    rw [div_div, div_le_div_iff (by positivity) (by positivity)]
    nlinarith [hlogp, hppos]
  calc ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p
      ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log p / p) / Real.log 2 :=
        Finset.sum_le_sum hterm
    _ = (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p) / Real.log 2 := by
        rw [Finset.sum_div]
    _ ≤ (Real.log x + (Real.log 4 + 4)) / Real.log 2 := by
        gcongr
        exact sum_primes_log_div_le hx

end
