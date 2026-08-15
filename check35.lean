import Mathlib

set_option maxHeartbeats 800000 in
example {F : ℕ → ℂ} (k : ℕ) : (∏' n : ℕ, (if n = k then 1 else F n)) = (∏' n : ℕ, (if n = k then 1 else F n)) := rfl

set_option maxHeartbeats 800000 in
example {F : ℕ → ℂ} (k : ℕ) : (∏' n : ℕ, F n) = (∏' n : ℕ, F n) := rfl

set_option maxHeartbeats 800000 in
example {F : ℕ → ℂ} (k : ℕ) : HasProd (fun n : ℕ => if n = k then F k else 1) (F k) := by
  exact hasProd_ite_eq k (F k)

set_option maxHeartbeats 800000 in
example {F : ℕ → ℂ} (k : ℕ) : HasProd (fun n : ℕ => if n = k then 1 else F n) (∏' n : ℕ, (if n = k then 1 else F n)) := by
  sorry
