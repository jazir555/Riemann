import KadiriOrderInfra

open ZeroFreeRegionHadamard

/-!
This file previously contained an independent proof of
`orderSet_xi : (7/4 : ℝ) ∈ orderSet xi`. That statement is now proved (and
norm-numbered) in `KadiriOrderInfra.lean`, so this module is reduced to a thin
re-export so it still builds as part of the RH scratch library.
-/

example : (7 / 4 : ℝ) ∈ orderSet xi := orderSet_xi
