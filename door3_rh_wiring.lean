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
    have h := hstripB z.re hx z.im hgt hhigh
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
