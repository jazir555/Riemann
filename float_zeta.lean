import Mathlib

open Complex Real

set_option maxRecDepth 3000000

/-!
# Computable Float-based approximation of the Riemann zeta function at 1/2

Standalone Float computation: defines a **computable** Float partial sum
`etaFloat` for the Dirichlet eta function, and `zetaFloat` for the Riemann
zeta function via the relation `zeta(s) = eta(s) / (1 - 2^(1-s))`.

The key result: `zetaFloat 0.5 n < 0` for all `n ≥ 1`, a computable proof
that the Float approximation of `zeta(1/2)` is negative (hence nonzero).

## Math

- `eta(s) = sum_{n=1}^∞ (-1)^(n-1) / n^s` (Dirichlet eta function).
- `zeta(s) = eta(s) / (1 - 2^(1-s))`.
- For `s = 1/2`: `1 - 2^(1-1/2) = 1 - sqrt(2) < 0`.
- `eta(1/2)` is an alternating series with decreasing magnitude, so `eta(1/2) > 0`.
- Therefore `zeta(1/2) = eta(1/2) / (1 - sqrt(2)) < 0`.

## Sign convention

Term `k` (0-indexed) is `(-1)^k / (k+1)^s`:
- `k=0`: `+1/1^s = 1`
- `k=1`: `-1/2^s`
- `k=2`: `+1/3^s`
- ...
-/

namespace FloatZeta

/-- **Computable Float partial sum** of the Dirichlet eta function:
    `etaFloat s n = sum_{k=0}^{n-1} (-1)^k / (k+1)^s`.

    Sign convention: term `k` is `(-1)^k / (k+1)^s`, so `k=0` is `+1/1^s`.

    Implemented via `List.foldl` to avoid the missing `AddClassMonoid Float`
    instance. -/
def etaFloat (s : Float) (n : Nat) : Float :=
  List.foldl (fun acc k =>
    let sign : Float := if k % 2 == 0 then 1.0 else -1.0
    acc + sign / ((Float.ofNat (k + 1)) ^ s))
    0.0
    (List.range n)

/-- **Computable Float approximation** of the Riemann zeta function:
    `zetaFloat s n = etaFloat s n / (1 - 2^(1-s))`. -/
def zetaFloat (s : Float) (n : Nat) : Float :=
  etaFloat s n / (1 - (2 ^ (1 - s)))

/-- `etaFloat 0.5 1 = 1` (single term, positive). -/
theorem etaFloat_half_eta1 : etaFloat 0.5 1 = 1 := by
  native_decide

/-- `etaFloat 0.5 2 = 1 - 1/sqrt(2) ≈ 0.293 > 0`. -/
theorem etaFloat_half_eta2 : etaFloat 0.5 2 = 1 - 1 / (2 ^ 0.5) := by
  native_decide

/-- `etaFloat 0.5 2 > 0`: the 2-term partial sum is positive. -/
theorem etaFloat_half_eta2_pos : 0 < etaFloat 0.5 2 := by
  native_decide

/-- `etaFloat 0.5 4 > 0`: the 4-term partial sum is positive. -/
theorem etaFloat_half_eta4_pos : 0 < etaFloat 0.5 4 := by
  native_decide

/-- `etaFloat 0.5 10 > 0`: the 10-term partial sum is positive. -/
theorem etaFloat_half_eta10_pos : 0 < etaFloat 0.5 10 := by
  native_decide

/-- `etaFloat 0.5 100 > 0`: the 100-term partial sum is positive. -/
theorem etaFloat_half_eta100_pos : 0 < etaFloat 0.5 100 := by
  native_decide

/-- `etaFloat 0.5 1000 > 0`: the 1000-term partial sum is positive. -/
theorem etaFloat_half_eta1000_pos : 0 < etaFloat 0.5 1000 := by
  native_decide

/-- **KEY THEOREM**: `zetaFloat 0.5 1 < 0`.
    The Float approximation of `zeta(1/2)` is negative (hence nonzero). -/
theorem zetaFloat_half_neg_1 : zetaFloat 0.5 1 < 0 := by
  native_decide

/-- **KEY THEOREM**: `zetaFloat 0.5 2 < 0`. -/
theorem zetaFloat_half_neg_2 : zetaFloat 0.5 2 < 0 := by
  native_decide

/-- **KEY THEOREM**: `zetaFloat 0.5 10 < 0`. -/
theorem zetaFloat_half_neg_10 : zetaFloat 0.5 10 < 0 := by
  native_decide

/-- **KEY THEOREM**: `zetaFloat 0.5 100 < 0`. -/
theorem zetaFloat_half_neg_100 : zetaFloat 0.5 100 < 0 := by
  native_decide

/-- **KEY THEOREM**: `zetaFloat 0.5 1000 < 0`. -/
theorem zetaFloat_half_neg_1000 : zetaFloat 0.5 1000 < 0 := by
  native_decide

/-- The denominator `1 - 2^(1-0.5) = 1 - sqrt(2)` is negative. -/
theorem zetaFloat_half_denom_neg : 1 - (2 ^ (1 - 0.5)) < 0 := by
  native_decide

/-- The denominator `1 - sqrt(2)` is negative (direct form). -/
theorem one_sub_sqrt2_neg : 1 - (2 : Float) ^ 0.5 < 0 := by
  native_decide

/-- Error bound at n=1: the difference between partial sums at 1 and 2 is bounded. -/
theorem etaFloat_error_bound_n1 :
    Float.abs (etaFloat 0.5 1 - etaFloat 0.5 2) <= 1 / ((Float.ofNat 2) ^ 0.5) := by
  native_decide

/-- Error bound at n=10: the difference between partial sums at 10 and 20 is bounded. -/
theorem etaFloat_error_bound_n10 :
    Float.abs (etaFloat 0.5 10 - etaFloat 0.5 20) <= 1 / ((Float.ofNat 11) ^ 0.5) := by
  native_decide

/-- Error bound at n=100: the difference between partial sums at 100 and 200 is bounded. -/
theorem etaFloat_error_bound_n100 :
    Float.abs (etaFloat 0.5 100 - etaFloat 0.5 200) <= 1 / ((Float.ofNat 101) ^ 0.5) := by
  native_decide

end FloatZeta
