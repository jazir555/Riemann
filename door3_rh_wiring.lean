import Mathlib
import central_cover_assembly
import door3_gamma_cutoff
import door3_zeta_cutoff
import door3_cutL10_remainders
import door3_sliver_nonvan
import door3_closed_cover

/-! # Downstream CutR10 wiring (import-cycle-free zone)

`riemann_hypothesis.lean` cannot import `central_cover_assembly` (that file
imports it), so the lane-banked `Door3GammaCutoff.cutR10_gammaRemainder` is
unwirable there. This downstream module does the wiring: Gamma remainder
(banked, no hypotheses) + zeta / deriv remainders (explicit premises owned
by the off-axis and real-arc lanes) assemble to
`CellFencingHypotheses CutR10 0.001 0.04`, hence right-cutoff-line
nonvanishing, hence `XiCutoffLines10` (with the left line as a premise),
hence the `rh_from_mainBand10_edgeStrips10_tail10_cutoff` capstone.
-/

namespace Door3RHWiring

open CentralCoverAssembly

open scoped BigOperators

/-- Banked Gamma remainder at the CutR10 center (Stirling wall, closed). -/
theorem cutR10_gamma_banked : Door3CutR10Center.cutR10_gammaRemainder :=
  Door3GammaCutoff.cutR10_gammaRemainder

/-- Zeta remainder from the off-axis slow-sum certificate. The three numeric
premises (`hSlow`/`hTail`/`hEnough`, `door3_zeta_cutoff:384`) are owned by
the off-axis lane; this is only the adapter wiring. -/
theorem cutR10_zeta_of_slowCert
    (N : ℕ) (S : ℂ)
    (hSdef : S = ∑ k ∈ Finset.range N,
      etaDirichletTerm Door3ZetaCutoff.sCut k)
    (slow rtail : ℝ) (hSlow : slow ≤ ‖S‖)
    (hTail : ‖(∑' m, etaPairTerm Door3ZetaCutoff.sCut m) - S‖ ≤ rtail)
    (hEnough : (7 / 5 : ℝ) + rtail ≤ slow) :
    Door3CutR10Center.cutR10_zetaRemainder :=
  Door3ZetaCutoff.cutR10_zetaRemainder_of_certificate_one N S hSdef slow rtail
    hSlow hTail hEnough

/-- Deriv remainder from the real-arc closedBall sup. The sup premise
(`door3_zeta_cutoff:404`) is owned by the real-arc lane. -/
theorem cutR10_deriv_of_ballSup
    (hC : ∀ z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1),
      ‖xiShiftedEntire z‖ ≤ (0.04 : ℝ)) :
    Door3CutR10Center.cutR10_derivRemainder 0.04 :=
  Door3ZetaCutoff.cutR10_derivRemainder_of_closedBall_sup hC

/-- Full CutR10 fencing package: banked Gamma remainder plus the two explicit
open premises above. -/
theorem cutR10_fencing_of_slowCert_and_ballSup
    (N : ℕ) (S : ℂ)
    (hSdef : S = ∑ k ∈ Finset.range N,
      etaDirichletTerm Door3ZetaCutoff.sCut k)
    (slow rtail : ℝ) (hSlow : slow ≤ ‖S‖)
    (hTail : ‖(∑' m, etaPairTerm Door3ZetaCutoff.sCut m) - S‖ ≤ rtail)
    (hEnough : (7 / 5 : ℝ) + rtail ≤ slow)
    (hC : ∀ z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1),
      ‖xiShiftedEntire z‖ ≤ (0.04 : ℝ)) :
    CellFencingHypotheses CutR10 0.001 0.04 :=
  Door3CutR10Center.cutR10_fencing_of_remainders cutR10_gamma_banked
    (cutR10_zeta_of_slowCert N S hSdef slow rtail hSlow hTail hEnough)
    (cutR10_deriv_of_ballSup hC)

/-- Fencing gives pointwise nonvanishing on the closed CutR10 rect (strip
H-leaf on closed `mem`; no strict-inequality repackaging needed). -/
theorem cutR10_rect_nonvanishing
    (H : CellFencingHypotheses CutR10 0.001 0.04)
    {z : ℂ} (hz : CutR10.mem z) : xiShifted z ≠ 0 := by
  have hle := xi_rect_lower_bound_of_center_bound_strip CutR10 0.001 0.04
    CutR10_strip_lo CutR10_strip_hi H.deriv_bound H.center_bound z hz
  intro hz0
  rw [hz0, norm_zero] at hle
  norm_num at hle

/-- Right cutoff line (`Re = 10`, `|Im| ≤ 0.49`) from CutR10 fencing. -/
theorem cutR10_rightLine_nonvanishing_of_fencing
    (H : CellFencingHypotheses CutR10 0.001 0.04)
    {z : ℂ} (hx : z.re = 10)
    (hlo : -(0.49 : ℝ) ≤ z.im) (hhi : z.im ≤ 0.49) :
    xiShifted z ≠ 0 :=
  cutR10_rect_nonvanishing H (CutR10_mem_of_line hx hlo hhi)

/-- `XiCutoffLines10` from CutR10 fencing: the right thin-rect case is wired
above; the left line (`CutL10`, another lane) and the `0.49 ≤ |Im|` sliver
(edge-strip lane) stay explicit premises. -/
theorem xiCutoffLines10_of_cutR10_and_leftLine
    (H : CellFencingHypotheses CutR10 0.001 0.04)
    (hLeft : ∀ z : ℂ, z.re = (-10 : ℝ) → -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) → z.im ≠ 0 → xiShifted z ≠ 0)
    (hSliver : ∀ z : ℂ, (z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) →
      -(1 / 2 : ℝ) < z.im → z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      (0.49 ≤ z.im ∨ z.im ≤ -0.49) → xiShifted z ≠ 0) :
    RHProofScaffold.XiCutoffLines10 := by
  intro z heq hgt hlt hne
  have hgt' : -(1 / 2 : ℝ) < z.im := by linarith
  rcases cutoffLines_either heq hgt' hlt with h | hs
  · rcases h with hL | hR
    · rcases heq with hx | hx
      · obtain ⟨_, hx1, _, _⟩ := hL
        rw [CutL10_x1, hx] at hx1
        norm_num at hx1
      · exact hLeft z hx hgt' hlt hne
    · exact cutR10_rect_nonvanishing H hR
  · exact hSliver z heq hgt' hlt hne hs

/-- Canned RH from the wired right cutoff line: main band + edge strips +
tail feed the existing assembly unchanged; only `Hcut` is discharged here
(modulo the left-line and sliver premises above). -/
theorem rh_of_cutR10_fencing_and_premises
    (Hmain : RHProofScaffold.XiCentralMainBand10)
    (Hedge : RHProofScaffold.XiCentralEdgeStrips10)
    (Htail : XiTailPointwiseNonvanishingForX (10 : ℝ))
    (H : CellFencingHypotheses CutR10 0.001 0.04)
    (hLeft : ∀ z : ℂ, z.re = (-10 : ℝ) → -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) → z.im ≠ 0 → xiShifted z ≠ 0)
    (hSliver : ∀ z : ℂ, (z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) →
      -(1 / 2 : ℝ) < z.im → z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      (0.49 ≤ z.im ∨ z.im ≤ -0.49) → xiShifted z ≠ 0) :
    RiemannHypothesisProp :=
  RHProofScaffold.rh_from_mainBand10_edgeStrips10_tail10_cutoff Hmain Hedge Htail
    (xiCutoffLines10_of_cutR10_and_leftLine H hLeft hSliver)

/-! ## Door-3 left-lane + sliver + edge-strip + bottom-strip wiring (pure adapters)

All theorems below are sorry-free adapters with explicit premises; they
compose the already-banked lane certificates without adding analytic content.
Residual premises are exactly the off-axis slow-sum datum, the closed-ball
sups, the eta-lower numeral (left lane), the joint product sup (left ball),
the edge outer-bound numerals, and the uniform bottom-strip minorant + tube.
-/

/-- CutL10 Gamma remainder banked through the proved conjugacy
(`cutL10_gammaRemainder_of_banked` over the closed right-lane Stirling cert).
Transitively hypothesis-free. -/
theorem cutL10_gamma_banked : Door3CutL10Center.cutL10_gammaRemainder :=
  Door3CutL10GammaConj.cutL10_gammaRemainder_of_banked cutR10_gamma_banked

/-- CutL10 zeta remainder from the left-lane eta certificate numeral. -/
theorem cutL10_zeta_of_etaCert
    (N : ℕ) (S : ℂ)
    (hSdef : S = ∑ k ∈ Finset.range N,
      etaDirichletTerm Door3CutL10EtaFactor.sCutL k)
    (slow rtail : ℝ) (hSlow : slow ≤ ‖S‖)
    (hTail : ‖(∑' m, etaPairTerm Door3CutL10EtaFactor.sCutL m) - S‖ ≤ rtail)
    (hEnough : (7 / 5 : ℝ) + rtail ≤ slow)
    (hLower : slow - rtail ≤ ‖zeta Door3CutL10EtaFactor.sCutL‖) :
    Door3CutL10Center.cutL10_zetaRemainder :=
  Door3CutL10Center.cutL10_zetaRemainder_of_etaCertificate
    N S hSdef slow rtail hSlow hTail hEnough hLower

/-- CutL10 deriv remainder from the left center-ball sup. -/
theorem cutL10_deriv_of_ballSup
    (hC : ∀ z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1),
      ‖xiShiftedEntire z‖ ≤ (0.04 : ℝ)) :
    Door3CutL10Center.cutL10_derivRemainder 0.04 :=
  Door3CutL10Center.cutL10_derivRemainder_of_closedBall_sup hC

/-- Full CutL10 fencing package: banked Gamma plus the two explicit open
premises above (eta numeral + ball sup). -/
theorem cutL10_fencing_of_etaCert_and_ballSup
    (N : ℕ) (S : ℂ)
    (hSdef : S = ∑ k ∈ Finset.range N,
      etaDirichletTerm Door3CutL10EtaFactor.sCutL k)
    (slow rtail : ℝ) (hSlow : slow ≤ ‖S‖)
    (hTail : ‖(∑' m, etaPairTerm Door3CutL10EtaFactor.sCutL m) - S‖ ≤ rtail)
    (hEnough : (7 / 5 : ℝ) + rtail ≤ slow)
    (hLower : slow - rtail ≤ ‖zeta Door3CutL10EtaFactor.sCutL‖)
    (hC : ∀ z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1),
      ‖xiShiftedEntire z‖ ≤ (0.04 : ℝ)) :
    CellFencingHypotheses CutL10 0.001 0.04 :=
  Door3CutL10Center.cutL10_fencing_of_remainders cutL10_gamma_banked
    (cutL10_zeta_of_etaCert N S hSdef slow rtail hSlow hTail hEnough hLower)
    (cutL10_deriv_of_ballSup hC)

/-- Exact `hLeft` capstone shape from CutL10 fencing (thin-rect arm wired;
left sliver stays an explicit edge-strip-lane premise). -/
theorem hLeft_of_cutL10_fencing
    (H : CellFencingHypotheses CutL10 0.001 0.04)
    (hSliverL : ∀ z : ℂ, z.re = (-10 : ℝ) → -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      (0.49 ≤ z.im ∨ z.im ≤ -0.49) → xiShifted z ≠ 0) :
    ∀ z : ℂ, z.re = (-10 : ℝ) → -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) → z.im ≠ 0 → xiShifted z ≠ 0 :=
  fun z hx hgt hlt hne =>
    Door3CutL10Center.hLeft_of_cutL10_fencing_and_sliver H hSliverL z hx hgt hlt hne

/-- `XiCutoffLines10` from BOTH thin-rect fencings plus the sliver premise. -/
theorem xiCutoffLines10_of_both_fencings
    (HL : CellFencingHypotheses CutL10 0.001 0.04)
    (HR : CellFencingHypotheses CutR10 0.001 0.04)
    (hSliver : ∀ z : ℂ, (z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) →
      -(1 / 2 : ℝ) < z.im → z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      (0.49 ≤ z.im ∨ z.im ≤ -0.49) → xiShifted z ≠ 0) :
    RHProofScaffold.XiCutoffLines10 :=
  Door3CutL10Center.xiCutoffLines10_of_cutL10_and_cutR10_fencing HL HR hSliver

/-- Exact `hSliver` capstone shape from explicit numeric edge data (outer-bound
CENTER `hTopLower`/`hBotLower` + DERIV `hTopDeriv`/`hBotDeriv` + width gates).
Wraps `sliver_hSliver_of_numericData` as a closed `∀`-statement. -/
theorem hSliver_of_edgeNumericData (mT MT mB MB : ℝ)
    (hmT : 0 < mT) (hMT : 0 < MT) (hmB : 0 < mB) (hMB : 0 < MB)
    (hδTle : mT / MT ≤ 1) (hδBle : mB / MB ≤ 1)
    (hTopLower : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      mT ≤ ‖xiShiftedEntire ((x : ℂ) + Complex.I * (1 / 2 : ℂ))‖)
    (hTopDeriv : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      ∀ y ∈ Set.Icc ((1 / 2 : ℝ) - mT / MT) (1 / 2 : ℝ),
        ‖deriv xiShiftedEntire ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ MT)
    (hGateT : (0.01 : ℝ) < mT / MT)
    (hBotLower : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      mB ≤ ‖xiShiftedEntire ((x : ℂ) - Complex.I * (1 / 2 : ℂ))‖)
    (hBotDeriv : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      ∀ y ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + mB / MB),
        ‖deriv xiShiftedEntire ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ MB)
    (hGateB : (0.01 : ℝ) < mB / MB) :
    ∀ z : ℂ, (z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) →
      -(1 / 2 : ℝ) < z.im → z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      (0.49 ≤ z.im ∨ z.im ≤ -0.49) → xiShifted z ≠ 0 :=
  fun z heq hgt hlt hne hs =>
    Door3SliverNonvan.sliver_hSliver_of_numericData mT MT mB MB
      hmT hMT hmB hMB hδTle hδBle hTopLower hTopDeriv hGateT
      hBotLower hBotDeriv hGateB z heq hgt hlt hne hs

/-- Exact `hSliver` shape from TOP numeric data only (bottom via proved
conjugation). -/
theorem hSliver_of_topNumericData_via_conj (mT MT : ℝ)
    (hmT : 0 < mT) (hMT : 0 < MT)
    (hδTle : mT / MT ≤ 1)
    (hTopLower : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      mT ≤ ‖xiShiftedEntire ((x : ℂ) + Complex.I * (1 / 2 : ℂ))‖)
    (hTopDeriv : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      ∀ y ∈ Set.Icc ((1 / 2 : ℝ) - mT / MT) (1 / 2 : ℝ),
        ‖deriv xiShiftedEntire ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ MT)
    (hGateT : (0.01 : ℝ) < mT / MT) :
    ∀ z : ℂ, (z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) →
      -(1 / 2 : ℝ) < z.im → z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      (0.49 ≤ z.im ∨ z.im ≤ -0.49) → xiShifted z ≠ 0 :=
  fun z heq hgt hlt hne hs =>
    Door3SliverNonvan.sliver_hSliver_of_topNumericData_via_conj mT MT
      hmT hMT hδTle hTopLower hTopDeriv hGateT z heq hgt hlt hne hs

/-- `hSliver` from TOP numeric data at the example ratio `11/1000`, bottom via
proved conjugation: the ratio gate `0.01 < 11/1000` is closed by the banked
`sliver_example_gate_top` (plus `norm_num` side conditions), leaving only the
two supplier bounds (`hTopLower`/`hTopDeriv`) as residual premises. -/
theorem hSliver_of_topNumericData_011_via_conj
    (hTopLower : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      (11 : ℝ) ≤ ‖xiShiftedEntire ((x : ℂ) + Complex.I * (1 / 2 : ℂ))‖)
    (hTopDeriv : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      ∀ y ∈ Set.Icc ((1 / 2 : ℝ) - 11 / 1000) (1 / 2 : ℝ),
        ‖deriv xiShiftedEntire ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ (1000 : ℝ)) :
    ∀ z : ℂ, (z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) →
      -(1 / 2 : ℝ) < z.im → z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      (0.49 ≤ z.im ∨ z.im ≤ -0.49) → xiShifted z ≠ 0 :=
  hSliver_of_topNumericData_via_conj (11 : ℝ) (1000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    hTopLower hTopDeriv Door3SliverNonvan.sliver_example_gate_top

/-- Bottom ratio gate at the example ratio `11/1000`, proved directly: no
banked `sliver_example_gate_bottom` exists in `door3_sliver_nonvan.lean`
(only `sliver_example_gate_top:460-461`), so this closes the same
`0.01 < 11/1000` arithmetic by `norm_num` with short numerals. -/
theorem gate_bottom_011 : (0.01 : ℝ) < 11 / 1000 := by norm_num

/-- `hSliver` from explicit numeric edge data at `11/1000` on both edges:
instantiates `hSliver_of_edgeNumericData` at `mT = mB = 11`, `MT = MB = 1000`
exactly as `hSliver_of_topNumericData_011_via_conj` did for the top-only
adapter. The top gate is closed by the banked `sliver_example_gate_top`,
the bottom gate by the directly proved `gate_bottom_011` (plus `norm_num`
side conditions), leaving only the four supplier bounds
(`hTopLower`/`hTopDeriv`/`hBotLower`/`hBotDeriv`) as residual premises. -/
theorem hSliver_of_edgeNumericData_011
    (hTopLower : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      (11 : ℝ) ≤ ‖xiShiftedEntire ((x : ℂ) + Complex.I * (1 / 2 : ℂ))‖)
    (hTopDeriv : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      ∀ y ∈ Set.Icc ((1 / 2 : ℝ) - 11 / 1000) (1 / 2 : ℝ),
        ‖deriv xiShiftedEntire ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ (1000 : ℝ))
    (hBotLower : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      (11 : ℝ) ≤ ‖xiShiftedEntire ((x : ℂ) - Complex.I * (1 / 2 : ℂ))‖)
    (hBotDeriv : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      ∀ y ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 11 / 1000),
        ‖deriv xiShiftedEntire ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ (1000 : ℝ)) :
    ∀ z : ℂ, (z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) →
      -(1 / 2 : ℝ) < z.im → z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      (0.49 ≤ z.im ∨ z.im ≤ -0.49) → xiShifted z ≠ 0 :=
  hSliver_of_edgeNumericData (11 : ℝ) (1000 : ℝ) (11 : ℝ) (1000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    hTopLower hTopDeriv Door3SliverNonvan.sliver_example_gate_top
    hBotLower hBotDeriv gate_bottom_011

/-- EDGE-NEXT sweep note (filed, not fixed): residual supplier spec at the example
ratio `11/1000`. None of the four `hSliver_of_edgeNumericData_011` premises above
matches a banked in-tree numeral, so none is forced here.
* `hTopLower`/`hBotLower` at `11` are infeasible as stated: the banked consumer-form
endpoint norms equal `1/2` at `x = 0`
(`Door3SliverEdge.edgeTop_consumer_norm_at_zero` / `edgeBot_consumer_norm_at_zero`,
`door3_sliver_edge.lean:221-234`, sharpness `:203-210`), and
`(0 : ℝ) ∈ Set.Icc (-10) 10`, so any closable uniform `mT`/`mB` must satisfy
`m ≤ 1/2`. Missing numeral: a *uniform* lower `m ≤ 1/2` over `Set.Icc (-10) 10`
at edge heights `s = I*x` (top) / `s = 1 + I*x` (bottom); owned by the edge/zeta
lane (needs `‖ζ‖` floors at `Re s = 0` / `Re s = 1`, where no `premZeta`/`premGamma`
floor is banked — existing floors sit at grid `Re ∈ {0.395, 0.2, 0.105}` centers,
`door3_premise_zeta.lean:66-98`).
* `hTopDeriv`/`hBotDeriv` at `1000` each reduce to one closed-ball sup `C = 1000`
on `Metric.closedBall 0 12` via `Door3SliverEdge.uniform_top_deriv_of_closedBall` /
`uniform_bot_deriv_of_closedBall` (`door3_sliver_edge.lean:322-370`); no banked `C`
numeral exists in-tree (open premise there too). Owned by the deriv lane. -/
def edge011_topLower_missing : Prop :=
  ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
    (11 : ℝ) ≤ ‖xiShiftedEntire ((x : ℂ) + Complex.I * (1 / 2 : ℂ))‖

/-- EDGE-NEXT2 (filed, not fixed): feasible `m = 1/2` adapters + one banked
grid-cell leaf. `ses_f51527e69` refuted the `m = 11` ratio above: the banked
consumer-form endpoint norms equal `1/2` at `x = 0`
(`Door3SliverEdge.edgeTop_consumer_norm_at_zero` /
`edgeBot_consumer_norm_at_zero`), and `(0 : ℝ) ∈ Set.Icc (-10) 10`, so any
closable uniform `m` satisfies `m ≤ 1/2`. The three sliver/strip theorems
below fix `mT = mB = 1/2` (the maximal closable uniform value; `0 < 1/2`
closed by `norm_num`) and leave every `MT`/`MB` numeral inside explicit
premises (deriv caps, `δ`-intervals, `δ ≤ 1` side conditions, `0.01 < δ`
width gates, strip nonvanishing) — ready for the day edge/zeta lane to feed
the numerals. The fourth theorem banks the `c00` leaf of the grid-fine
`Hgrid` premise from the sorry-free `R00` fencing assembly (conditional only
on the two `R00_leaf_obligations` enclosures). Pivot rationale: the uniform
bottom minorant has NO banked uniform input (only the `x = 0` point
`xiShiftedEntire_zero_minorant`, still modulo the open ball sup), while the
`R00` cell has its full fencing package proved — so the grid-cell instance
is the bankable step. -/

/-- `hSliver` from TOP numeric data at the feasible uniform `mT = 1/2`,
bottom via proved conjugation. Mirrors `hSliver_of_topNumericData_011_via_conj`
with `mT` fixed at the maximal closable value; the `MT` numeral (deriv cap,
`δ`-interval, `δ ≤ 1` side condition, width gate) stays entirely in explicit
premises for the day edge/zeta lane. -/
theorem hSliver_of_topNumericData_half_via_conj (MT : ℝ)
    (hMT : 0 < MT)
    (hδTle : (1 / 2 : ℝ) / MT ≤ 1)
    (hTopLower : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      (1 / 2 : ℝ) ≤ ‖xiShiftedEntire ((x : ℂ) + Complex.I * (1 / 2 : ℂ))‖)
    (hTopDeriv : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      ∀ y ∈ Set.Icc ((1 / 2 : ℝ) - (1 / 2 : ℝ) / MT) (1 / 2 : ℝ),
        ‖deriv xiShiftedEntire ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ MT)
    (hGateT : (0.01 : ℝ) < (1 / 2 : ℝ) / MT) :
    ∀ z : ℂ, (z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) →
      -(1 / 2 : ℝ) < z.im → z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      (0.49 ≤ z.im ∨ z.im ≤ -0.49) → xiShifted z ≠ 0 :=
  hSliver_of_topNumericData_via_conj (1 / 2 : ℝ) MT
    (by norm_num) hMT hδTle hTopLower hTopDeriv hGateT

/-- `hSliver` from explicit numeric edge data at feasible `mT = mB = 1/2`:
mirrors `hSliver_of_edgeNumericData_011` with both uniform lowers fixed at
the maximal closable value; both `MT`/`MB` numerals stay in explicit
premises. Residual: the four supplier bounds plus the two width gates and
the two `δ ≤ 1` side conditions. -/
theorem hSliver_of_edgeNumericData_half (MT MB : ℝ)
    (hMT : 0 < MT) (hMB : 0 < MB)
    (hδTle : (1 / 2 : ℝ) / MT ≤ 1) (hδBle : (1 / 2 : ℝ) / MB ≤ 1)
    (hTopLower : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      (1 / 2 : ℝ) ≤ ‖xiShiftedEntire ((x : ℂ) + Complex.I * (1 / 2 : ℂ))‖)
    (hTopDeriv : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      ∀ y ∈ Set.Icc ((1 / 2 : ℝ) - (1 / 2 : ℝ) / MT) (1 / 2 : ℝ),
        ‖deriv xiShiftedEntire ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ MT)
    (hGateT : (0.01 : ℝ) < (1 / 2 : ℝ) / MT)
    (hBotLower : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      (1 / 2 : ℝ) ≤ ‖xiShiftedEntire ((x : ℂ) - Complex.I * (1 / 2 : ℂ))‖)
    (hBotDeriv : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      ∀ y ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + (1 / 2 : ℝ) / MB),
        ‖deriv xiShiftedEntire ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ MB)
    (hGateB : (0.01 : ℝ) < (1 / 2 : ℝ) / MB) :
    ∀ z : ℂ, (z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) →
      -(1 / 2 : ℝ) < z.im → z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      (0.49 ≤ z.im ∨ z.im ≤ -0.49) → xiShifted z ≠ 0 :=
  hSliver_of_edgeNumericData (1 / 2 : ℝ) MT (1 / 2 : ℝ) MB
    (by norm_num) hMT (by norm_num) hMB hδTle hδBle
    hTopLower hTopDeriv hGateT hBotLower hBotDeriv hGateB

/-- Interior edge strips at feasible widths `δT = (1/2)/MT`,
`δB = (1/2)/MB`: mirrors `xiCentralEdgeStrips10_of_uniformStrips_011` with
the `m = 11`, `M = 1000` numerals replaced by the feasible `m = 1/2` shape;
both width gates stay explicit premises (they close by `norm_num` once the
day lane feeds `MT`/`MB` numerals with `(1/2)/M > 0.01`). -/
theorem xiCentralEdgeStrips10_of_uniformStrips_half (MT MB : ℝ)
    (hstripT : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      (1 / 2 : ℝ) - (1 / 2 : ℝ) / MT < y → y < (1 / 2 : ℝ) →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0)
    (hwidthT : (1 / 2 : ℝ) - (1 / 2 : ℝ) / MT < 0.49)
    (hstripB : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      -(1 / 2 : ℝ) < y → y < -(1 / 2 : ℝ) + (1 / 2 : ℝ) / MB →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0)
    (hwidthB : (-0.49 : ℝ) < -(1 / 2 : ℝ) + (1 / 2 : ℝ) / MB) :
    RHProofScaffold.XiCentralEdgeStrips10 :=
  xiCentralEdgeStrips10_of_uniformStrips (δT := (1 / 2 : ℝ) / MT) (δB := (1 / 2 : ℝ) / MB)
    hstripT hwidthT hstripB hwidthB

/-- Banked `c00 = (-10, -7.5, 0.01, 0.2)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R00_H_instance` at the banked membership
`R00_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R00_leaf_obligations` only — the two numerical enclosures
(`0.002 + 0.05 * radius ≤ ‖ξ‖` at `s = 0.395 - 8.75·I`, uniform
`‖ξ'‖ ≤ 0.05` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:1172-1129`. -/
theorem gridH_c00_of_R00 (h : CentralCoverAssembly.R00_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-10, -7.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-10, -7.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-10, -7.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-10, -7.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R00_H_instance h
    ((-10, -7.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R00_mem_gridFine rfl

/-- Interior edge strips (`0.49 ≤ |Im| < 1/2` on `-10 < Re < 10`) from the
same uniform outer-bound certificates that feed the sliver: top/bottom strip
premises plus the two numeric width gates (`δ ≥ 0.01`). This is the
CENTER (`hTopLower`/`hBotLower`) + DERIV (`hTopDeriv`/`hBotDeriv`) +
outer-bound (width-gate) packaging of the edge-strip lane. -/
theorem xiCentralEdgeStrips10_of_uniformStrips
    {δT δB : ℝ}
    (hstripT : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      (1 / 2 : ℝ) - δT < y → y < (1 / 2 : ℝ) →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0)
    (hwidthT : (1 / 2 : ℝ) - δT < 0.49)
    (hstripB : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      -(1 / 2 : ℝ) < y → y < -(1 / 2 : ℝ) + δB →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0)
    (hwidthB : (-0.49 : ℝ) < -(1 / 2 : ℝ) + δB) :
    RHProofScaffold.XiCentralEdgeStrips10 := by
  intro z hx_lo hx_hi hgt hlt hne hs
  have hx : z.re ∈ Set.Icc (-10 : ℝ) (10 : ℝ) :=
    ⟨le_of_lt hx_lo, le_of_lt hx_hi⟩
  have hpoint : ((z.re : ℂ) + Complex.I * (z.im : ℂ)) = z :=
    Door3SliverNonvan.sliver_point_eq_vertical z
  rcases hs with h | h
  · have hlow : (1 / 2 : ℝ) - δT < z.im := lt_of_lt_of_le hwidthT h
    have h := hstripT z.re hx z.im hlow hlt
    rwa [hpoint] at h
  · have hhigh : z.im < -(1 / 2 : ℝ) + δB := lt_of_le_of_lt h hwidthB
    have hgt' : -(1 / 2 : ℝ) < z.im := by linarith
    have h := hstripB z.re hx z.im hgt' hhigh
    rwa [hpoint] at h

/-- Interior edge strips at the example width `11/1000 = 0.011`: the two
width numerals (`1/2 - 11/1000 < 0.49`, `-0.49 < -(1/2) + 11/1000`) are closed
by `norm_num`, leaving only the two uniform strip premises. -/
theorem xiCentralEdgeStrips10_of_uniformStrips_011
    (hstripT : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      (1 / 2 : ℝ) - 11 / 1000 < y → y < (1 / 2 : ℝ) →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0)
    (hstripB : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      -(1 / 2 : ℝ) < y → y < -(1 / 2 : ℝ) + 11 / 1000 →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0) :
    RHProofScaffold.XiCentralEdgeStrips10 :=
  xiCentralEdgeStrips10_of_uniformStrips (δT := (11 / 1000 : ℝ)) (δB := (11 / 1000 : ℝ))
    hstripT (by norm_num) hstripB (by norm_num)

/-- `BottomStripObligations` from the uniform real-axis minorant + tube sup
(re-export of the `door3_zeta_cutoff` bridge with the residual premises made
explicit at the wiring site). -/
theorem bottomStrip_obligations_of_uniform_closed {B : ℝ}
    (hb : ∀ (x : ℝ), -10 < x → x < 10 →
      (0.025 : ℝ) ≤ ‖xiShiftedEntire (x : ℂ)‖)
    (hB : ∀ (x : ℝ), -10 < x → x < 10 → ∀ (z : ℂ),
      z ∈ Metric.closedBall (Door3ZetaCutoff.bsCenter x) 1 →
      ‖xiShiftedEntire z‖ ≤ B)
    (hM : B / (1 / 2 : ℝ) ≤ (1 : ℝ)) :
    BottomStripObligations :=
  Door3ZetaCutoff.bottomStrip_obligations_of_uniform_bounds hb hB hM

/-- Upper main band (`0 < Im ≤ 0.49` on `-10 < Re < 10`) from the bottom strip
(`(0, 0.01]` arm) plus the closed-grid fencing (`[0.01, 0.49]` arm). The lower
half (`Im < 0`) stays residual (grid lower half covers `[-0.49, -0.01]`; the
`(-0.01, 0)` sliver needs the conjugated bottom strip, left explicit). -/
theorem mainBand_upper_of_strip_and_grid
    (hStrip : BottomStripObligations)
    (Hgrid : ∀ c ∈ gridFine, ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖)
    {z : ℂ} (hx_lo : -10 < z.re) (hx_hi : z.re < 10)
    (hy_pos : 0 < z.im) (hy_le : z.im ≤ 0.49) :
    xiShifted z ≠ 0 := by
  by_cases hle : z.im ≤ (0.01 : ℝ)
  · exact bottom_strip_covered hStrip hx_lo hx_hi hy_pos hle
  · push_neg at hle
    exact closed_inner_nonvanishing_of_fenced_grid_fine Hgrid
      (le_of_lt hx_lo) (le_of_lt hx_hi) (le_of_lt hle) hy_le

/-- Banked `c02 = (-8, -5.5, 0.01, 0.2)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R02_H_instance` at the banked membership
`R02_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R02_leaf_obligations` only — the two numerical enclosures
(`0.002 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.395 - 6.75·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:1470` (`R02_leaf_obligations`) and `:1499`
(`R02_H_instance`). `R01` is skipped by design: it has no
`R01_mem_gridFine` (row-overlap cell, would be false). -/
theorem gridH_c02_of_R02 (h : CentralCoverAssembly.R02_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-8, -5.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-8, -5.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-8, -5.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-8, -5.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R02_H_instance h
    ((-8, -5.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R02_mem_gridFine rfl

/-- Banked `c03 = (-6, -3.5, 0.01, 0.2)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R03_H_instance` at the banked membership
`R03_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R03_leaf_obligations` only — the two numerical enclosures
(`0.05 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.395 - 4.75·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:1556` (`R03_leaf_obligations`) and `:1585`
(`R03_H_instance`). -/
theorem gridH_c03_of_R03 (h : CentralCoverAssembly.R03_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-6, -3.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-6, -3.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-6, -3.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-6, -3.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R03_H_instance h
    ((-6, -3.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R03_mem_gridFine rfl

/-- Banked `c04 = (-4, -1.5, 0.01, 0.2)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R04_H_instance` at the banked membership
`R04_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R04_leaf_obligations` only — the two numerical enclosures
(`0.05 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.395 - 2.75·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:1642` (`R04_leaf_obligations`) and `:1671`
(`R04_H_instance`). -/
theorem gridH_c04_of_R04 (h : CentralCoverAssembly.R04_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-4, -1.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-4, -1.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-4, -1.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-4, -1.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R04_H_instance h
    ((-4, -1.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R04_mem_gridFine rfl

/-- Banked `c05 = (-2, 0.5, 0.01, 0.2)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R05_H_instance` at the banked membership
`R05_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R05_leaf_obligations` only — the two numerical enclosures
(`0.15 + 0.06 * radius ≤ ‖ξ‖` at `s = 0.395 - 0.75·I`, uniform
`‖ξ'‖ ≤ 0.06` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:1728` (`R05_leaf_obligations`) and `:1757`
(`R05_H_instance`). -/
theorem gridH_c05_of_R05 (h : CentralCoverAssembly.R05_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-2, 0.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-2, 0.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-2, 0.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-2, 0.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R05_H_instance h
    ((-2, 0.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R05_mem_gridFine rfl

/-- Banked `c06 = (0, 2.5, 0.01, 0.2)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R06_H_instance` at the banked membership
`R06_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R06_leaf_obligations` only — the two numerical enclosures
(`0.15 + 0.06 * radius ≤ ‖ξ‖` at `s = 0.395 + 1.25·I`, uniform
`‖ξ'‖ ≤ 0.06` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:1814` (`R06_leaf_obligations`) and `:1843`
(`R06_H_instance`). -/
theorem gridH_c06_of_R06 (h : CentralCoverAssembly.R06_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((0, 2.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((0, 2.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((0, 2.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((0, 2.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R06_H_instance h
    ((0, 2.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R06_mem_gridFine rfl

/-- Banked `c07 = (2, 4.5, 0.01, 0.2)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R07_H_instance` at the banked membership
`R07_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R07_leaf_obligations` only — the two numerical enclosures
(`0.05 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.395 + 3.25·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:1900` (`R07_leaf_obligations`) and `:1929`
(`R07_H_instance`). -/
theorem gridH_c07_of_R07 (h : CentralCoverAssembly.R07_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((2, 4.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((2, 4.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((2, 4.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((2, 4.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R07_H_instance h
    ((2, 4.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R07_mem_gridFine rfl

/-- Banked `c08 = (4, 6.5, 0.01, 0.2)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R08_H_instance` at the banked membership
`R08_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R08_leaf_obligations` only — the two numerical enclosures
(`0.05 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.395 + 5.25·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:1986` (`R08_leaf_obligations`) and `:2015`
(`R08_H_instance`). -/
theorem gridH_c08_of_R08 (h : CentralCoverAssembly.R08_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((4, 6.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((4, 6.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((4, 6.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((4, 6.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R08_H_instance h
    ((4, 6.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R08_mem_gridFine rfl

/-- Banked `c09 = (6, 8.5, 0.01, 0.2)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R09_H_instance` at the banked membership
`R09_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R09_leaf_obligations` only — the two numerical enclosures
(`0.002 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.395 + 7.25·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:2072` (`R09_leaf_obligations`) and `:2101`
(`R09_H_instance`). -/
theorem gridH_c09_of_R09 (h : CentralCoverAssembly.R09_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((6, 8.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((6, 8.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((6, 8.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((6, 8.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R09_H_instance h
    ((6, 8.5, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R09_mem_gridFine rfl

/-- Banked `c10 = (7.5, 10, 0.01, 0.2)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R10_H_instance` at the banked membership
`R10_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R10_leaf_obligations` only — the two numerical enclosures
(`0.002 + 0.05 * radius ≤ ‖ξ‖` at `s = 0.395 + 8.75·I`, uniform
`‖ξ'‖ ≤ 0.05` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:2158` (`R10_leaf_obligations`) and `:2187`
(`R10_H_instance`). -/
theorem gridH_c10_of_R10 (h : CentralCoverAssembly.R10_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((7.5, 10, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((7.5, 10, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((7.5, 10, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((7.5, 10, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R10_H_instance h
    ((7.5, 10, 0.01, 0.2) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R10_mem_gridFine rfl

/-- Banked `c11 = (-10, -7.5, 0.1, 0.3)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R11_H_instance` at the banked membership
`R11_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R11_leaf_obligations` only — the two numerical enclosures
(`0.002 + 0.05 * radius ≤ ‖ξ‖` at `s = 0.3 - 8.75·I`, uniform
`‖ξ'‖ ≤ 0.05` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:2533` (`R11_leaf_obligations`) and `:2562`
(`R11_H_instance`). -/
theorem gridH_c11_of_R11 (h : CentralCoverAssembly.R11_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-10, -7.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-10, -7.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-10, -7.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-10, -7.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R11_H_instance h
    ((-10, -7.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R11_mem_gridFine rfl

/-- Banked `c12 = (-8, -5.5, 0.1, 0.3)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R12_H_instance` at the banked membership
`R12_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R12_leaf_obligations` only — the two numerical enclosures
(`0.002 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.3 - 6.75·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:2617` (`R12_leaf_obligations`) and `:2646`
(`R12_H_instance`). -/
theorem gridH_c12_of_R12 (h : CentralCoverAssembly.R12_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-8, -5.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-8, -5.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-8, -5.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-8, -5.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R12_H_instance h
    ((-8, -5.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R12_mem_gridFine rfl

/-- Banked `c13 = (-6, -3.5, 0.1, 0.3)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R13_H_instance` at the banked membership
`R13_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R13_leaf_obligations` only — the two numerical enclosures
(`0.05 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.3 - 4.75·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:2701` (`R13_leaf_obligations`) and `:2730`
(`R13_H_instance`). -/
theorem gridH_c13_of_R13 (h : CentralCoverAssembly.R13_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-6, -3.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-6, -3.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-6, -3.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-6, -3.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R13_H_instance h
    ((-6, -3.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R13_mem_gridFine rfl

/-- Banked `c14 = (-4, -1.5, 0.1, 0.3)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R14_H_instance` at the banked membership
`R14_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R14_leaf_obligations` only — the two numerical enclosures
(`0.05 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.3 - 2.75·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:2785` (`R14_leaf_obligations`) and `:2814`
(`R14_H_instance`). -/
theorem gridH_c14_of_R14 (h : CentralCoverAssembly.R14_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-4, -1.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-4, -1.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-4, -1.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-4, -1.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R14_H_instance h
    ((-4, -1.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R14_mem_gridFine rfl

/-- Banked `c15 = (-2, 0.5, 0.1, 0.3)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R15_H_instance` at the banked membership
`R15_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R15_leaf_obligations` only — the two numerical enclosures
(`0.15 + 0.06 * radius ≤ ‖ξ‖` at `s = 0.3 - 0.75·I`, uniform
`‖ξ'‖ ≤ 0.06` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:2869` (`R15_leaf_obligations`) and `:2898`
(`R15_H_instance`). -/
theorem gridH_c15_of_R15 (h : CentralCoverAssembly.R15_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-2, 0.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-2, 0.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-2, 0.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-2, 0.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R15_H_instance h
    ((-2, 0.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R15_mem_gridFine rfl

/-- Banked `c16 = (0, 2.5, 0.1, 0.3)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R16_H_instance` at the banked membership
`R16_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R16_leaf_obligations` only — the two numerical enclosures
(`0.15 + 0.06 * radius ≤ ‖ξ‖` at `s = 0.3 + 1.25·I`, uniform
`‖ξ'‖ ≤ 0.06` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:2953` (`R16_leaf_obligations`) and `:2982`
(`R16_H_instance`). -/
theorem gridH_c16_of_R16 (h : CentralCoverAssembly.R16_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((0, 2.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((0, 2.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((0, 2.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((0, 2.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R16_H_instance h
    ((0, 2.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R16_mem_gridFine rfl

/-- Banked `c17 = (2, 4.5, 0.1, 0.3)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R17_H_instance` at the banked membership
`R17_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R17_leaf_obligations` only — the two numerical enclosures
(`0.05 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.3 + 3.25·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:3037` (`R17_leaf_obligations`) and `:3066`
(`R17_H_instance`). -/
theorem gridH_c17_of_R17 (h : CentralCoverAssembly.R17_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((2, 4.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((2, 4.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((2, 4.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((2, 4.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R17_H_instance h
    ((2, 4.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R17_mem_gridFine rfl

/-- Banked `c18 = (4, 6.5, 0.1, 0.3)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R18_H_instance` at the banked membership
`R18_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R18_leaf_obligations` only — the two numerical enclosures
(`0.05 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.3 + 5.25·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:3121` (`R18_leaf_obligations`) and `:3150`
(`R18_H_instance`). -/
theorem gridH_c18_of_R18 (h : CentralCoverAssembly.R18_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((4, 6.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((4, 6.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((4, 6.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((4, 6.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R18_H_instance h
    ((4, 6.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R18_mem_gridFine rfl

/-- Banked `c19 = (6, 8.5, 0.1, 0.3)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R19_H_instance` at the banked membership
`R19_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R19_leaf_obligations` only — the two numerical enclosures
(`0.002 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.3 + 7.25·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:3205` (`R19_leaf_obligations`) and `:3234`
(`R19_H_instance`). -/
theorem gridH_c19_of_R19 (h : CentralCoverAssembly.R19_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((6, 8.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((6, 8.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((6, 8.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((6, 8.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R19_H_instance h
    ((6, 8.5, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R19_mem_gridFine rfl

/-- Banked `c20 = (7.5, 10, 0.1, 0.3)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R20_H_instance` at the banked membership
`R20_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R20_leaf_obligations` only — the two numerical enclosures
(`0.002 + 0.05 * radius ≤ ‖ξ‖` at `s = 0.3 + 8.75·I`, uniform
`‖ξ'‖ ≤ 0.05` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:3289` (`R20_leaf_obligations`) and `:3318`
(`R20_H_instance`). -/
theorem gridH_c20_of_R20 (h : CentralCoverAssembly.R20_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((7.5, 10, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((7.5, 10, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((7.5, 10, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((7.5, 10, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R20_H_instance h
    ((7.5, 10, 0.1, 0.3) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R20_mem_gridFine rfl

/-- Banked `c21 = (-10, -7.5, 0.2, 0.4)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R21_H_instance` at the banked membership
`R21_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R21_leaf_obligations` only — the two numerical enclosures
(`0.002 + 0.05 * radius ≤ ‖ξ‖` at `s = 0.2 - 8.75·I`, uniform
`‖ξ'‖ ≤ 0.05` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:3375` (`R21_leaf_obligations`) and `:3404`
(`R21_H_instance`). -/
theorem gridH_c21_of_R21 (h : CentralCoverAssembly.R21_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-10, -7.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-10, -7.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-10, -7.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-10, -7.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R21_H_instance h
    ((-10, -7.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R21_mem_gridFine rfl

/-- Banked `c22 = (-8, -5.5, 0.2, 0.4)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R22_H_instance` at the banked membership
`R22_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R22_leaf_obligations` only — the two numerical enclosures
(`0.002 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.2 - 6.75·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:3459` (`R22_leaf_obligations`) and `:3488`
(`R22_H_instance`). -/
theorem gridH_c22_of_R22 (h : CentralCoverAssembly.R22_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-8, -5.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-8, -5.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-8, -5.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-8, -5.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R22_H_instance h
    ((-8, -5.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R22_mem_gridFine rfl

/-- Banked `c23 = (-6, -3.5, 0.2, 0.4)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R23_H_instance` at the banked membership
`R23_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R23_leaf_obligations` only — the two numerical enclosures
(`0.05 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.2 - 4.75·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:3543` (`R23_leaf_obligations`) and `:3572`
(`R23_H_instance`). -/
theorem gridH_c23_of_R23 (h : CentralCoverAssembly.R23_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-6, -3.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-6, -3.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-6, -3.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-6, -3.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R23_H_instance h
    ((-6, -3.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R23_mem_gridFine rfl

/-- Banked `c24 = (-4, -1.5, 0.2, 0.4)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R24_H_instance` at the banked membership
`R24_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R24_leaf_obligations` only — the two numerical enclosures
(`0.05 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.2 - 2.75·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:3627` (`R24_leaf_obligations`) and `:3656`
(`R24_H_instance`). -/
theorem gridH_c24_of_R24 (h : CentralCoverAssembly.R24_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-4, -1.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-4, -1.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-4, -1.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-4, -1.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R24_H_instance h
    ((-4, -1.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R24_mem_gridFine rfl

/-- Banked `c25 = (-2, 0.5, 0.2, 0.4)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R25_H_instance` at the banked membership
`R25_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R25_leaf_obligations` only — the two numerical enclosures
(`0.15 + 0.06 * radius ≤ ‖ξ‖` at `s = 0.2 - 0.75·I`, uniform
`‖ξ'‖ ≤ 0.06` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:3711` (`R25_leaf_obligations`) and `:3740`
(`R25_H_instance`). -/
theorem gridH_c25_of_R25 (h : CentralCoverAssembly.R25_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-2, 0.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-2, 0.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-2, 0.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-2, 0.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R25_H_instance h
    ((-2, 0.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R25_mem_gridFine rfl

/-- Banked `c26 = (0, 2.5, 0.2, 0.4)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R26_H_instance` at the banked membership
`R26_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R26_leaf_obligations` only — the two numerical enclosures
(`0.15 + 0.06 * radius ≤ ‖ξ‖` at `s = 0.2 + 1.25·I`, uniform
`‖ξ'‖ ≤ 0.06` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:3795` (`R26_leaf_obligations`) and `:3824`
(`R26_H_instance`). -/
theorem gridH_c26_of_R26 (h : CentralCoverAssembly.R26_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((0, 2.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((0, 2.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((0, 2.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((0, 2.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R26_H_instance h
    ((0, 2.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R26_mem_gridFine rfl

/-- Banked `c27 = (2, 4.5, 0.2, 0.4)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R27_H_instance` at the banked membership
`R27_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R27_leaf_obligations` only — the two numerical enclosures
(`0.05 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.2 + 3.25·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:3879` (`R27_leaf_obligations`) and `:3908`
(`R27_H_instance`). -/
theorem gridH_c27_of_R27 (h : CentralCoverAssembly.R27_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((2, 4.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((2, 4.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((2, 4.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((2, 4.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R27_H_instance h
    ((2, 4.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R27_mem_gridFine rfl

/-- Banked `c28 = (4, 6.5, 0.2, 0.4)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R28_H_instance` at the banked membership
`R28_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R28_leaf_obligations` only — the two numerical enclosures
(`0.05 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.2 + 5.25·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:3963` (`R28_leaf_obligations`) and `:3992`
(`R28_H_instance`). -/
theorem gridH_c28_of_R28 (h : CentralCoverAssembly.R28_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((4, 6.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((4, 6.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((4, 6.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((4, 6.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R28_H_instance h
    ((4, 6.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R28_mem_gridFine rfl

/-- Banked `c29 = (6, 8.5, 0.2, 0.4)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R29_H_instance` at the banked membership
`R29_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R29_leaf_obligations` only — the two numerical enclosures
(`0.002 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.2 + 7.25·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:4047` (`R29_leaf_obligations`) and `:4076`
(`R29_H_instance`). -/
theorem gridH_c29_of_R29 (h : CentralCoverAssembly.R29_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((6, 8.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((6, 8.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((6, 8.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((6, 8.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R29_H_instance h
    ((6, 8.5, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R29_mem_gridFine rfl

/-- Banked `c30 = (7.5, 10, 0.2, 0.4)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R30_H_instance` at the banked membership
`R30_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R30_leaf_obligations` only — the two numerical enclosures
(`0.002 + 0.05 * radius ≤ ‖ξ‖` at `s = 0.2 + 8.75·I`, uniform
`‖ξ'‖ ≤ 0.05` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:4131` (`R30_leaf_obligations`) and `:4160`
(`R30_H_instance`). -/
theorem gridH_c30_of_R30 (h : CentralCoverAssembly.R30_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((7.5, 10, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((7.5, 10, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((7.5, 10, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((7.5, 10, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R30_H_instance h
    ((7.5, 10, 0.2, 0.4) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R30_mem_gridFine rfl

/-- Banked `c31 = (-10, -7.5, 0.3, 0.49)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R31_H_instance` at the banked membership
`R31_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R31_leaf_obligations` only — the two numerical enclosures
(`0.002 + 0.05 * radius ≤ ‖ξ‖` at `s = 0.105 - 8.75·I`, uniform
`‖ξ'‖ ≤ 0.05` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:4217` (`R31_leaf_obligations`) and `:4246`
(`R31_H_instance`). -/
theorem gridH_c31_of_R31 (h : CentralCoverAssembly.R31_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-10, -7.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-10, -7.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-10, -7.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-10, -7.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R31_H_instance h
    ((-10, -7.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R31_mem_gridFine rfl

/-- Banked `c32 = (-8, -5.5, 0.3, 0.49)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R32_H_instance` at the banked membership
`R32_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R32_leaf_obligations` only — the two numerical enclosures
(`0.002 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.105 - 6.75·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:4301` (`R32_leaf_obligations`) and `:4330`
(`R32_H_instance`). -/
theorem gridH_c32_of_R32 (h : CentralCoverAssembly.R32_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-8, -5.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-8, -5.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-8, -5.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-8, -5.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R32_H_instance h
    ((-8, -5.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R32_mem_gridFine rfl

/-- Banked `c33 = (-6, -3.5, 0.3, 0.49)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R33_H_instance` at the banked membership
`R33_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R33_leaf_obligations` only — the two numerical enclosures
(`0.05 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.105 - 4.75·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:4385` (`R33_leaf_obligations`) and `:4414`
(`R33_H_instance`). -/
theorem gridH_c33_of_R33 (h : CentralCoverAssembly.R33_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-6, -3.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-6, -3.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-6, -3.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-6, -3.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R33_H_instance h
    ((-6, -3.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R33_mem_gridFine rfl

/-- Banked `c34 = (-4, -1.5, 0.3, 0.49)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R34_H_instance` at the banked membership
`R34_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R34_leaf_obligations` only — the two numerical enclosures
(`0.05 + 0.07 * radius ≤ ‖ξ‖` at `s = 0.105 - 2.75·I`, uniform
`‖ξ'‖ ≤ 0.07` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:4469` (`R34_leaf_obligations`) and `:4498`
(`R34_H_instance`). -/
theorem gridH_c34_of_R34 (h : CentralCoverAssembly.R34_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-4, -1.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-4, -1.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-4, -1.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-4, -1.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R34_H_instance h
    ((-4, -1.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R34_mem_gridFine rfl

/-- Banked `c35 = (-2, 0.5, 0.3, 0.49)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R35_H_instance` at the banked membership
`R35_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R35_leaf_obligations` only — the two numerical enclosures
(`0.15 + 0.06 * radius ≤ ‖ξ‖` at `s = 0.105 - 0.75·I`, uniform
`‖ξ'‖ ≤ 0.06` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:4553` (`R35_leaf_obligations`) and `:4582`
(`R35_H_instance`). -/
theorem gridH_c35_of_R35 (h : CentralCoverAssembly.R35_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((-2, 0.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((-2, 0.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((-2, 0.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((-2, 0.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R35_H_instance h
    ((-2, 0.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R35_mem_gridFine rfl

/-- Banked `c36 = (0, 2.5, 0.3, 0.49)` leaf of the grid-fine `Hgrid`
premise (consumed by `mainBand_upper_of_strip_and_grid` via
`closed_inner_nonvanishing_of_fenced_grid_fine`): re-exports the sorry-free
`CentralCoverAssembly.R36_H_instance` at the banked membership
`R36_mem_gridFine`, in exactly the `Hgrid` existential shape. Honest
residual: `R36_leaf_obligations` only — the two numerical enclosures
(`0.15 + 0.06 * radius ≤ ‖ξ‖` at `s = 0.105 + 1.25·I`, uniform
`‖ξ'‖ ≤ 0.06` on the rect), unprovable in Mathlib per
`central_cover_assembly.lean:4637` (`R36_leaf_obligations`) and `:4666`
(`R36_H_instance`). -/
theorem gridH_c36_of_R36 (h : CentralCoverAssembly.R36_leaf_obligations) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = ((0, 2.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).1 ∧
      R.x1 = ((0, 2.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).2.1 ∧
      R.y0 = ((0, 2.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).2.2.1 ∧
      R.y1 = ((0, 2.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ).2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ :=
  CentralCoverAssembly.R36_H_instance h
    ((0, 2.5, 0.3, 0.49) : ℝ × ℝ × ℝ × ℝ)
    CentralCoverAssembly.R36_mem_gridFine rfl

end Door3RHWiring

#print axioms Door3RHWiring.cutR10_gamma_banked
#print axioms Door3RHWiring.cutR10_zeta_of_slowCert
#print axioms Door3RHWiring.cutR10_deriv_of_ballSup
#print axioms Door3RHWiring.cutR10_fencing_of_slowCert_and_ballSup
#print axioms Door3RHWiring.cutR10_rect_nonvanishing
#print axioms Door3RHWiring.cutR10_rightLine_nonvanishing_of_fencing
#print axioms Door3RHWiring.xiCutoffLines10_of_cutR10_and_leftLine
#print axioms Door3RHWiring.rh_of_cutR10_fencing_and_premises
#print axioms Door3RHWiring.cutL10_gamma_banked
#print axioms Door3RHWiring.cutL10_zeta_of_etaCert
#print axioms Door3RHWiring.cutL10_deriv_of_ballSup
#print axioms Door3RHWiring.cutL10_fencing_of_etaCert_and_ballSup
#print axioms Door3RHWiring.hLeft_of_cutL10_fencing
#print axioms Door3RHWiring.xiCutoffLines10_of_both_fencings
#print axioms Door3RHWiring.hSliver_of_edgeNumericData
#print axioms Door3RHWiring.hSliver_of_topNumericData_via_conj
#print axioms Door3RHWiring.xiCentralEdgeStrips10_of_uniformStrips
#print axioms Door3RHWiring.xiCentralEdgeStrips10_of_uniformStrips_011
#print axioms Door3RHWiring.bottomStrip_obligations_of_uniform_closed
#print axioms Door3RHWiring.mainBand_upper_of_strip_and_grid
#print axioms Door3RHWiring.hSliver_of_topNumericData_half_via_conj
#print axioms Door3RHWiring.hSliver_of_edgeNumericData_half
#print axioms Door3RHWiring.xiCentralEdgeStrips10_of_uniformStrips_half
#print axioms Door3RHWiring.gridH_c00_of_R00
#print axioms Door3RHWiring.gridH_c02_of_R02
#print axioms Door3RHWiring.gridH_c03_of_R03
#print axioms Door3RHWiring.gridH_c04_of_R04
#print axioms Door3RHWiring.gridH_c05_of_R05
#print axioms Door3RHWiring.gridH_c06_of_R06
