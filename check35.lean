import Mathlib

set_option maxHeartbeats 800000 in
example (a : ℕ → ℂ) (hane : ∀ n, a n ≠ 0) (k : ℕ) :
    meromorphicOrderAt (fun z : ℂ => 1 - z / a k) (a k) = 1 := by
  have hform1 : (fun z : ℂ => 1 - z / a k) = fun z : ℂ => (-1 / a k) * (z - a k) := by
    funext z
    field_simp [hane k]
    ring
  rw [hform1]
  have hc : meromorphicOrderAt (fun z : ℂ => (-1 / a k)) (a k) = 0 := by
    have hne : (-1 / a k) ≠ 0 := by
      exact div_ne_zero (by norm_num) (hane k)
    rw [meromorphicOrderAt_const (a k) (-1 / a k)]
    simp [hne]
  have hsub : meromorphicOrderAt (fun z : ℂ => z - a k) (a k) = 1 := by
    simpa using (meromorphicOrderAt_id_sub_const (𝕜 := ℂ) (x := a k))
  calc
    meromorphicOrderAt ((fun z : ℂ => (-1 / a k)) * (fun z : ℂ => z - a k)) (a k)
        = meromorphicOrderAt (fun z : ℂ => (-1 / a k)) (a k) +
            meromorphicOrderAt (fun z : ℂ => z - a k) (a k) := by
          exact meromorphicOrderAt_mul
            (AnalyticAt.meromorphicAt ((differentiable_const (-1 / a k)).analyticAt (a k)))
            (AnalyticAt.meromorphicAt (Differentiable.analyticAt (differentiable_id.sub (differentiable_const (a k))) (a k)))
      _ = 1 := by rw [hc, hsub]; simp
