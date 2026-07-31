import Mathlib

open Complex Real MeasureTheory Filter
open scoped Topology

#check Filter.eventually_of_forall
#check eventually_of_forall
#check Filter.Frequently.of_mem
#check Filter.frequently_of_mem
#check summable_nat_add_one_iff
#check Summable.comp_injective
#check convex_halfSpace_re_gt
#check convex_halfSpace_im_gt
#check convex_halfPlane_re
#check Complex.continuousAt_log
#check Complex.continuousOn_log
#check Real.continuousAt_log
#check ContinuousAt.ofReal
#check ContinuousAt.congr
#check ContinuousAt.congr_of_eventuallyEq
#check Filter.Eventually.continuousAt
#check intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
#check intervalIntegral.intervalIntegrable_const
#check intervalIntegral.intervalIntegrable_norm
#check intervalIntegral.integral_comp_add_right
#check intervalIntegral.integral_comp_add_left
#check intervalIntegral.integral_ofReal
#check intervalIntegral.intervalIntegrable_iff
#check intervalIntegral.intervalIntegrable_id
#check intervalIntegral.intervalIntegrable_const
#check Complex.hasDerivAt_log
#check HasDerivAt.neg
#check HasDerivAt.mul
#check HasDerivAt.div
#check analyticAt_id
#check AnalyticAt.id
#check isPreconnected_Ioi
#check Set.Ioi_preconnected
#check isConnected_Ioi
#check preconnected_Ioi
#check convex_Ioi
#check Convex.preimage
#check ContinuousLinearMap.preimage
#check isOpen_lt
#check isOpen_Ioi
#check differentiable_riemannZeta₀
#check analyticAt_const
