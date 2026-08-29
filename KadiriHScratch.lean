import ZeroFreeRegionProof
import ZeroFreeRegionHadamard
import KadiriOrderInfra

open Complex Real Topology
open scoped BigOperators
open ZeroFreeRegionHadamard
open ArithmeticFunction hiding log
open scoped LSeries.notation

noncomputable section

/-! Corrected `kadiriLamzouriZetaZeroFreeEdge`.

The intended proof (gamma/digamma 3-4-1 bound via `logDeriv_completedZeta`
minus the full ξ-zero tail) is under construction; the deep estimate is
currently a `sorry` pending closure (e.g. via the now-built `Zeta23`
zero-free-region machinery). -/
theorem kadiriLamzouriZetaZeroFreeEdge'
    (xiZeros_infinite : ({z : ℂ | xi z = 0} : Set ℂ).Infinite)
    (s : ℂ) (ht : |s.im| ≥ 1) (hre : s.re ≥ zeroFreeEdge s.im) :
    riemannZeta s ≠ 0 := by sorry
