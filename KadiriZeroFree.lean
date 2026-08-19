import ZeroFreeRegionProof
import ZeroFreeRegionHadamard

open Complex Real Topology
open scoped BigOperators
open ZeroFreeRegionHadamard
open ArithmeticFunction hiding log
open scoped LSeries.notation

noncomputable section

/-- The Kadiri numerical bridge: 1/57.54 < 2/95, i.e. 9500 < 11508. -/
private theorem kadiri_numerical_bridge :
    (1 : ℝ) / 57.54 < 2 / 95 := by norm_num

/-- ξ has infinitely many zeros. Follows from order-1 growth + not-polynomial. -/
private theorem xiZeros_infinite :
    ({z : ℂ | xi z = 0} : Set ℂ).Infinite := by sorry

/-- Every ξ-zero is simple: `meromorphicOrderAt xi z ≤ 1` for all z. -/
private theorem xiZeros_simple :
    ∀ z : ℂ, meromorphicOrderAt xi z ≤ 1 := by sorry

/-- Kadiri–Lamzouri zero-free region for ζ. -/
theorem kadiriLamzouriZetaZeroFreeEdge (s : ℂ) (ht : |s.im| ≥ 1)
    (hre : s.re ≥ zeroFreeEdge s.im) : riemannZeta s ≠ 0 := by
  sorry

end
