import Mathlib

open Complex Real MeasureTheory Filter
open scoped Topology

#check Real.rpow_le_rpow_of_exponent_le
#check Real.rpow_le_rpow_of_exponent_ge
#check Real.rpow_lt_rpow_of_exponent_lt
#check Real.rpow_strictMono
#check Real.rpow_mono
#check Complex.norm_ofReal
#check Complex.abs_ofReal
#check Complex.norm_eq_abs
#check Complex.abs_of_nonneg
#check Complex.normSq_ofReal
#check HasDerivAt.congr_deriv
#check HasDerivAt.congr
#check HasDerivAt.congr' 
#check Filter.inter_mem
#check Filter.nonempty_of_mem
#check nhdsWithin_neBot
#check Filter.NeBot.nhdsWithin
#check Filter.NeBot (𝓝[≠] (2 : ℝ))
#check Complex.continuous_ofReal
#check continuousAt_id.sub
#check ContinuousAt.sub
#check ContinuousAt.norm
#check ContinuousAt.mul
#check Real.continuousAt_log
#check Complex.ofReal_inv
#check Complex.ofReal_mul
#check tsum_congr
#check rpow_neg
#check Real.rpow_neg
#check div_eq_mul_inv
#check Complex.ofReal_div
#check Complex.ofReal_sub
