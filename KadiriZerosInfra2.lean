import ZeroFreeRegionHadamard

open ZeroFreeRegionHadamard Complex Real Topology
open scoped BigOperators

-- sanity: reuse an existing lemma
example : Differentiable ℂ xi := xi_differentiable
