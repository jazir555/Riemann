import Mathlib
open Set Filter Topology Real
open scoped Topology

#check HasSum.congr
#check HasSum.congr'
#check HasSum.summable
#check Summable.const_mul
#check Summable.mul_left
#check abs_neg_one
#check abs_one
#check abs_neg
#check one_pow
#check abs_pow
#check HasSum.const_mul

-- test: change both function and sum of a HasSum
example {a : ℝ} (h : HasSum (fun k : ℕ => a) a) : HasSum (fun k : ℕ => a) a := by
  exact h

-- test Summable.const_mul
example (c : ℝ) (h : Summable (fun k : ℕ => (1:ℝ)^k / (Nat.factorial k : ℝ))) :
    Summable (fun k : ℕ => c * ((1:ℝ)^k / (Nat.factorial k : ℝ))) := by
  exact h.const_mul c
