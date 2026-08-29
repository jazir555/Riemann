import ZeroFreeRegionProof
import ZeroFreeRegionHadamard
import KadiriOrderInfra
import KadiriZeroFree

open Complex Real Topology
open scoped BigOperators
open ZeroFreeRegionHadamard
open ArithmeticFunction hiding log
open scoped LSeries.notation

noncomputable section

/-! Corrected `kadiriLamzouriZetaZeroFreeEdge`.

Status after the `Zeta23` integration (this file is now **fully proved**):

* the ξ-zero infinitude hypothesis of the previous version is no longer needed — it is a
  theorem, `xiZeros_infinite`, proved in `KadiriZeroFree.lean` from `Zeta23`'s
  Riemann–von Mangoldt formula (`Zeta23.RvM.riemannVonMangoldt`);
* the summability input `Σ ‖ρ‖⁻²` is likewise a theorem, `xi_enum_ncard_bound`, from
  `Zeta23`'s local zero count `N(t, t+1] ≤ A₀ log(|t|+3)`;
* the remaining deep estimate (Kadiri's sharp 3–4–1 bound for the analytic part of
  `−ζ′/ζ`) is carried **explicitly** as the named hypothesis `KadiriAnalyticInput`
  instead of a placeholder proof.  Nothing in `Zeta23` implies it: the zero-free input available
  there (`Zeta23.FromPNTPlus.ZetaBounds.ZetaZeroFree`) only gives the strictly thinner
  region `Re s ≥ 1 − A/(log|Im s|)^9` with an unspecified constant `A`.

For the unconditional (but thinner) region that `Zeta23` *does* provide, see
`zeta_ne_zero_of_pow_edge` below. -/

/-- Kadiri–Lamzouri zero-free edge, conditional on the single named deep estimate
`KadiriAnalyticInput`.  Fully proved (conditional on `KadiriAnalyticInput`). -/
theorem kadiriLamzouriZetaZeroFreeEdge'
    (hIn : KadiriAnalyticInput)
    (s : ℂ) (ht : |s.im| ≥ 1) (hre : s.re ≥ zeroFreeEdge s.im) :
    riemannZeta s ≠ 0 :=
  kadiriLamzouriZetaZeroFreeEdge_of_analyticInput hIn s ht hre

/-- The ξ-zero infinitude that the previous version of `kadiriLamzouriZetaZeroFreeEdge'`
took as a hypothesis is now available as a theorem (from `Zeta23`). -/
theorem xiZeros_infinite_holds : ({z : ℂ | xi z = 0} : Set ℂ).Infinite :=
  xiZeros_infinite

/-- The unconditional zero-free region supplied by `Zeta23`/PNT+ for Mathlib's `riemannZeta`
(thinner than Kadiri's edge, but fully proved and hypothesis-free). -/
theorem zeta_ne_zero_of_pow_edge' :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℂ, 3 < |s.im| →
      1 - A / (Real.log |s.im|) ^ 9 ≤ s.re → riemannZeta s ≠ 0 :=
  zeta_ne_zero_of_pow_edge

end
