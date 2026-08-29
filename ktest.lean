import ZeroFreeRegionProof
import ZeroFreeRegionHadamard

open Complex Real Topology
open ZeroFreeRegionHadamard

#check @AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero
#check @MeromorphicOn.AnalyticOnNhd.divisor_apply
#check @MeromorphicOn.AnalyticOnNhd.divisor_nonneg
#check @MeromorphicOn.divisor_apply
#check @AnalyticAt.meromorphicOrderAt_nonneg
#check @ZeroFreeRegionHadamard.zeroCount_le_rpow_of_orderSet
#check @ZeroFreeRegionHadamard.xi_norm_bound_whole_plane

example (r : ℝ) : ZeroFreeRegionHadamard.zeroCount ZeroFreeRegionHadamard.xi r
    = ((∑ᶠ u : ℂ, MeromorphicOn.divisor ZeroFreeRegionHadamard.xi (Metric.closedBall 0 r) u : ℤ) : ℝ) :=
  rfl
