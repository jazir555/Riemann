import Mathlib
open Complex Real MeasureTheory Filter
open scoped Topology

-- Test: can we use @integral_mono_ae with explicit arguments?
example (a b : ℝ) (hab : a ≤ b) (f g : ℝ → ℝ)
    (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (h : f ≤ g) :
    ∫ x in a..b, f x ≤ ∫ x in a..b, g x :=
  intervalIntegral.integral_mono_ae hab hf hg (ae_of_all volume h)
