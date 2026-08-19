import ZeroFreeRegionProof
import ZeroFreeRegionHadamard

open Complex Real Topology
open scoped BigOperators
open ZeroFreeRegionHadamard
open ArithmeticFunction hiding log
open scoped LSeries.notation

noncomputable section

/-- The Kadiri numerical bridge: 1/57.54 < 2/95. -/
private theorem kadiri_numerical_bridge :
    (1 : ℝ) / 57.54 < 2 / 95 := by
  norm_num

/-- kadiriLamzouriZetaZeroFreeEdge: ζ(s) ≠ 0 when |Im s| ≥ 1 and
    Re s ≥ 1 - (1/57.54)/log(|Im s|+10).  The sole remaining assembly gap is
    the Hadamard decomposition (zero enumeration + 3/4/1 bound). -/
theorem kadiriLamzouriZetaZeroFreeEdge (s : ℂ) (ht : |s.im| ≥ 1)
    (hre : s.re ≥ zeroFreeEdge s.im) : riemannZeta s ≠ 0 := by
  sorry

end
