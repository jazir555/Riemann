/- BorelCaratheodory.lean

This file is now REDUNDANT — Mathlib already contains:

  Mathlib/Analysis/Complex/BorelCaratheodory.lean:
    Complex.borelCaratheodory_zero : f analytic on ball 0 R, f 0 = 0, Re(f z) ≤ M
                                     ⟹ ‖f z‖ ≤ 2*M*‖z‖/(R-‖z‖)
    Complex.borelCaratheodory      : general version without f 0 = 0

  Mathlib/Analysis/Complex/AbsMax.lean:
    Complex.norm_eqOn_closedBall_of_isMaxOn : maximum modulus principle

This file exists only as a compatibility shim.
-/
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.AbsMax
