import Mathlib
import central_cover_assembly
import door3_gamma_cutoff
import door3_zeta_cutoff

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

end Door3RHWiring

#print axioms Door3RHWiring.cutR10_gamma_banked
#print axioms Door3RHWiring.cutR10_zeta_of_slowCert
#print axioms Door3RHWiring.cutR10_deriv_of_ballSup
#print axioms Door3RHWiring.cutR10_fencing_of_slowCert_and_ballSup
#print axioms Door3RHWiring.cutR10_rect_nonvanishing
#print axioms Door3RHWiring.cutR10_rightLine_nonvanishing_of_fencing
#print axioms Door3RHWiring.xiCutoffLines10_of_cutR10_and_leftLine
#print axioms Door3RHWiring.rh_of_cutR10_fencing_and_premises
