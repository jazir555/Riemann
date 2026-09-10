import central_cover_assembly
import zeta_rigorous

/-! # Door-3 CutL10 remainder interface + fencing assembly (cover lane, left cutoff)

Mirror of the CutR10 lane, serving capstone premise (c) `hLeft`
(`xiShifted z ≠ 0` on `Re = -10`, off-axis).

MIRROR MAP (read-only sources; this file touches no existing file):
- `Door3CutR10Center` namespace: `central_cover_assembly.lean:16636-16803`
  (`cutR10_s_eq`, `cutR10_gammaRemainder`, `cutR10_zetaRemainder`,
  `cutR10_derivRemainder`, `cutR10_center_bound_of_gamma_zeta`,
  `cutR10_fencing_of_remainders`). Every item is mirrored below with prefix
  `cutL10_`.
- `CutL10` geometry: same file `:6826-6905` (thin rect
  `x ∈ [-10.25,-9.75]`, `y ∈ [-0.49,0.49]`, center `≈ -10`, `radius < 0.56`
  via `CutL10_radius_lt`, `CutL10_mem_of_line`).
- `Door3CutR10EtaFactor` section: same file `:16813-16960` (conversion-factor
  cap `‖1 - 2^(1-sCutR)‖ ≤ 1`, phase-cosine floor, floor/need arithmetic).
- Gamma bank: `Door3GammaCutoff.cutR10_gammaRemainder`
  (`door3_gamma_cutoff.lean:122`)
  with type `Door3CutR10Center.cutR10_gammaRemainder`, proved there via
  `cutoff_gamma_lower` at `(1/4:ℂ) + 5*I` (no hypotheses).
- Zeta adapter shape: `Door3ZetaCutoff.cutR10_zetaRemainder_of_certificate_one`
  (`door3_zeta_cutoff.lean:384`); deriv adapter shape:
  `Door3ZetaCutoff.cutR10_derivRemainder_of_closedBall_sup` (same file `:404`).
- Final plug-in shape: `cutoffLines_either` (`central_cover_assembly.lean:6908`)
  and `Door3RHWiring.xiCutoffLines10_of_cutR10_and_leftLine`
  (`door3_rh_wiring.lean:88-106`).

CAPSTONE PREMISE (c) `hLeft` — exact shape quoted from
`door3_rh_wiring.lean:88-106` (the `xiCutoffLines10_of_cutR10_and_leftLine`
binder this file discharges):
```
    (hLeft : ∀ z : ℂ, z.re = (-10 : ℝ) → -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) → z.im ≠ 0 → xiShifted z ≠ 0)
    (hSliver : ∀ z : ℂ, (z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) →
      -(1 / 2 : ℝ) < z.im → z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      (0.49 ≤ z.im ∨ z.im ≤ -0.49) → xiShifted z ≠ 0)
```
The `|Im| ≤ 0.49` part of `hLeft` is closed here from CutL10 fencing
(`hLeft_of_cutL10_fencing_and_sliver`); the `0.49 ≤ |Im|` sliver stays an
explicit premise owned by the edge-strip lane (same split as the right lane).

DRAFTING DISCIPLINE: every proof below is complete (no placeholders).
Anything not closable this wave is an explicit `Prop` premise (see the three
lane contracts and the fix-wave list at the bottom of each section).
-/

open scoped BigOperators

namespace Door3CutL10Center

open CentralCoverAssembly

/-- CutL10 center is the real point `-10`
(midpoints `(-10.25 + -9.75)/2`, `(-0.49 + 0.49)/2`). -/
theorem cutL10_center_eq : CutL10.center = (((-10 : ℝ)) : ℂ) := by
  unfold CellProofEngine.Rect2D.center
  rw [CutL10_x0, CutL10_x1, CutL10_y0, CutL10_y1]
  apply Complex.ext <;> simp <;> norm_num

/-- Shifted `s`-point at the CutL10 center: `(1/2:ℂ) + I*(-10) = 1/2 - 10*I`,
the complex conjugate of the CutR10 `s`-point `1/2 + 10*I`. -/
theorem cutL10_s_eq :
    (1 / 2 : ℂ) + Complex.I * CutL10.center
      = (((1 / 2 : ℝ)) : ℂ) + (((-10 : ℝ)) : ℂ) * Complex.I := by
  rw [cutL10_center_eq]
  push_cast
  ring

/-- Poly factor exact value at the CutL10 `s`-point:
`(1/2)(1/2 - 10i)(-1/2 - 10i) = -401/8` (same numeral as the right lane:
conjugation preserves the product `(1/2)(-1/4 - 100) = -401/8`). -/
theorem cutL10_poly_eq :
    (1 / 2 : ℂ) * ((((1 / 2 : ℝ)) : ℂ) + (((-10 : ℝ)) : ℂ) * Complex.I)
      * (((((1 / 2 : ℝ)) : ℂ) + (((-10 : ℝ)) : ℂ) * Complex.I) - 1)
      = (((-401 / 8 : ℝ)) : ℂ) := by
  apply Complex.ext <;> simp [Complex.I_mul_I] <;> norm_num

/-- Poly factor norm `401/8` (exact; mirror of `cutR10_poly_norm`). -/
theorem cutL10_poly_norm :
    ‖(1 / 2 : ℂ) * ((((1 / 2 : ℝ)) : ℂ) + (((-10 : ℝ)) : ℂ) * Complex.I)
      * (((((1 / 2 : ℝ)) : ℂ) + (((-10 : ℝ)) : ℂ) * Complex.I) - 1)‖
      = (401 / 8 : ℝ) := by
  rw [cutL10_poly_eq, Complex.norm_real, Real.norm_eq_abs]
  norm_num

/-- `Re` of the pi-power exponent at the CutL10 `s`-point is `-1/4`
(depends only on `Re s = 1/2`, hence identical to the right lane). -/
theorem cutL10_piExp_re :
    (-((((1 / 2 : ℝ)) : ℂ) + (((-10 : ℝ)) : ℂ) * Complex.I) / 2).re
      = (-(1 / 4) : ℝ) := by
  simp <;> norm_num

/-- Pi-power factor lower bound `3/4` (mirror of `cutR10_pi_norm_lower`;
identical proof: only `Re` of the exponent is used). -/
theorem cutL10_pi_norm_lower :
    (3 / 4 : ℝ)
      ≤ ‖((Real.pi : ℂ)
        ^ (-((((1 / 2 : ℝ)) : ℂ) + (((-10 : ℝ)) : ℂ) * Complex.I) / 2))‖ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, cutL10_piExp_re]
  have hpi_le : Real.pi ≤ (256 / 81 : ℝ) := by
    have h := Real.pi_lt_d2
    norm_num at h ⊢
    linarith
  have h14 : Real.pi ^ ((1 / 4 : ℝ)) ≤ (4 / 3 : ℝ) := by
    have h1 : Real.pi ^ ((1 / 4 : ℝ)) ≤ (256 / 81 : ℝ) ^ ((1 / 4 : ℝ)) :=
      Real.rpow_le_rpow (le_of_lt Real.pi_pos) hpi_le (by norm_num)
    have hq : (256 / 81 : ℝ) = (4 / 3 : ℝ) ^ (4 : ℕ) := by norm_num
    have hexp : (((4 : ℕ)) : ℝ) * (1 / 4 : ℝ) = 1 := by norm_num
    have h2 : ((256 / 81 : ℝ) ^ ((1 / 4 : ℝ))) = 4 / 3 := by
      rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hexp,
        Real.rpow_one]
    rwa [h2] at h1
  have hfin : (3 / 4 : ℝ) ≤ Real.pi ^ (-(1 / 4 : ℝ)) := by
    rw [Real.rpow_neg (le_of_lt Real.pi_pos)]
    have h43 : (3 / 4 : ℝ) = 1 / (4 / 3 : ℝ) := by norm_num
    rw [h43]
    simpa only [one_div] using
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos Real.pi_pos _) h14
  exact hfin

/-- Conditional CutL10 center enclosure at tier `(0.001, 0.04)`
(mirror of `cutR10_center_bound_of_gamma_zeta`; same floor `8421/320000`
covers the same need `117/5000`). -/
theorem cutL10_center_bound_of_gamma_zeta
    (hG : (1 / 2000 : ℝ)
      ≤ ‖Complex.Gamma (((1 / 2 : ℂ) + Complex.I * CutL10.center) / 2)‖)
    (hZ : (7 / 5 : ℝ) ≤ ‖zeta ((1 / 2 : ℂ) + Complex.I * CutL10.center)‖) :
    (0.001 : ℝ) + 0.04 * CutL10.radius ≤ ‖xiShifted CutL10.center‖ := by
  have hrad : CutL10.radius < 0.56 := CutL10_radius_lt
  have hM : (0.04 : ℝ) * CutL10.radius ≤ 0.04 * 0.56 :=
    mul_le_mul_of_nonneg_left hrad.le (by norm_num)
  have hs : ((1 / 2 : ℂ) + Complex.I * CutL10.center)
      = ((((1 / 2 : ℝ)) : ℂ) + (((-10 : ℝ)) : ℂ) * Complex.I) := cutL10_s_eq
  have hpoly : ((401 / 8 : ℝ)) ≤ ‖(1 / 2 : ℂ)
      * ((1 / 2 : ℂ) + Complex.I * CutL10.center)
      * (((1 / 2 : ℂ) + Complex.I * CutL10.center) - 1)‖ := by
    rw [hs, cutL10_poly_norm]
  have hpi : ((3 / 4 : ℝ)) ≤ ‖(Real.pi : ℂ)
      ^ (-(((1 / 2 : ℂ) + Complex.I * CutL10.center) / 2))‖ := by
    rw [hs]
    simpa only [neg_div] using cutL10_pi_norm_lower
  have hpref : classicalXiPrefactor ((1 / 2 : ℂ) + Complex.I * CutL10.center)
      = ((1 / 2 : ℂ) * ((1 / 2 : ℂ) + Complex.I * CutL10.center)
        * (((1 / 2 : ℂ) + Complex.I * CutL10.center) - 1))
        * ((Real.pi : ℂ) ^ (-(((1 / 2 : ℂ) + Complex.I * CutL10.center) / 2)))
        * (Complex.Gamma (((1 / 2 : ℂ) + Complex.I * CutL10.center) / 2)) := rfl
  have hxi : xiShifted CutL10.center
      = classicalXiPrefactor ((1 / 2 : ℂ) + Complex.I * CutL10.center)
        * zeta ((1 / 2 : ℂ) + Complex.I * CutL10.center) := rfl
  have h1 : ((401 / 8 : ℝ)) * (3 / 4) * (1 / 2000) * (7 / 5)
      ≤ ‖classicalXiPrefactor ((1 / 2 : ℂ) + Complex.I * CutL10.center)‖
        * ‖zeta ((1 / 2 : ℂ) + Complex.I * CutL10.center)‖ := by
    rw [hpref]
    simp only [norm_mul]
    have g1 : (401 / 8 : ℝ) * (3 / 4)
        ≤ ‖(1 / 2 : ℂ) * ((1 / 2 : ℂ) + Complex.I * CutL10.center)
          * (((1 / 2 : ℂ) + Complex.I * CutL10.center) - 1)‖
          * ‖(Real.pi : ℂ) ^ (-(((1 / 2 : ℂ) + Complex.I * CutL10.center) / 2))‖ :=
      mul_le_mul hpoly hpi (by norm_num) (norm_nonneg _)
    have g2 : (401 / 8 : ℝ) * (3 / 4) * (1 / 2000)
        ≤ (‖(1 / 2 : ℂ) * ((1 / 2 : ℂ) + Complex.I * CutL10.center)
          * (((1 / 2 : ℂ) + Complex.I * CutL10.center) - 1)‖
          * ‖(Real.pi : ℂ) ^ (-(((1 / 2 : ℂ) + Complex.I * CutL10.center) / 2))‖)
          * ‖Complex.Gamma (((1 / 2 : ℂ) + Complex.I * CutL10.center) / 2)‖ :=
      mul_le_mul g1 hG (by norm_num)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have g3 : (401 / 8 : ℝ) * (3 / 4) * (1 / 2000) * (7 / 5)
        ≤ ((‖(1 / 2 : ℂ) * ((1 / 2 : ℂ) + Complex.I * CutL10.center)
          * (((1 / 2 : ℂ) + Complex.I * CutL10.center) - 1)‖
          * ‖(Real.pi : ℂ) ^ (-(((1 / 2 : ℂ) + Complex.I * CutL10.center) / 2))‖)
          * ‖Complex.Gamma (((1 / 2 : ℂ) + Complex.I * CutL10.center) / 2)‖)
          * ‖zeta ((1 / 2 : ℂ) + Complex.I * CutL10.center)‖ :=
      mul_le_mul g2 hZ (by norm_num)
        (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (norm_nonneg _))
    simpa only [norm_mul] using g3
  have hxi_norm : ‖classicalXiPrefactor ((1 / 2 : ℂ) + Complex.I * CutL10.center)‖
        * ‖zeta ((1 / 2 : ℂ) + Complex.I * CutL10.center)‖
        = ‖xiShifted CutL10.center‖ := by
    rw [hxi, norm_mul]
  have hneed : (0.001 : ℝ) + 0.04 * 0.56
      ≤ (401 / 8 : ℝ) * (3 / 4) * (1 / 2000) * (7 / 5) := by
    norm_num
  have hstep : (0.001 : ℝ) + 0.04 * CutL10.radius
      ≤ (401 / 8 : ℝ) * (3 / 4) * (1 / 2000) * (7 / 5) := by
    linarith [hM, hneed]
  have hle : (401 / 8 : ℝ) * (3 / 4) * (1 / 2000) * (7 / 5)
      ≤ ‖xiShifted CutL10.center‖ := by
    rw [← hxi_norm]
    exact h1
  exact le_trans hstep hle

/-- Deriv-side remainder for CutL10 at tier `M = 0.04` (interface Prop;
mirror of `cutR10_derivRemainder`). -/
def cutL10_derivRemainder (M : ℝ) : Prop :=
  ∀ w, CutL10.mem w → ‖deriv xiShifted w‖ ≤ M

/-- Gamma-factor remainder: explicit Stirling lower at
`sCutL/2 = 1/4 - 5*I`, the conjugate of the banked `1/4 + 5*I` point
(mirror of `cutR10_gammaRemainder`; same numeral `1/2000`). -/
def cutL10_gammaRemainder : Prop :=
  (1 / 2000 : ℝ)
    ≤ ‖Complex.Gamma (((1 / 2 : ℂ) + Complex.I * CutL10.center) / 2)‖

/-- Zeta-factor remainder: Dirichlet-eta lower at `sCutL = 1/2 - 10*I`
(mirror of `cutR10_zetaRemainder`; same numeral `7/5`, same true value by
conjugation — banked via `cutL10_zetaRemainder_of_etaCertificate` below). -/
def cutL10_zetaRemainder : Prop :=
  (7 / 5 : ℝ) ≤ ‖zeta ((1 / 2 : ℂ) + Complex.I * CutL10.center)‖

/-- GAMMA-LANE CONTRACT: the banked right-lane Stirling certificate
`Door3GammaCutoff.cutR10_gammaRemainder :
  Door3CutR10Center.cutR10_gammaRemainder`
(`door3_gamma_cutoff.lean:122`, no hypotheses) transfers to the left lane
along the single explicit conjugation-norm premise below.
FIX-WAVE TASK: close `hConjNorm` by the Mathlib Gamma-conjugation bridge at
`1/4 ± 5*I` (norm of `Gamma` at conjugate points agree; exact Mathlib lemma
name — e.g. a `Gamma_conj`/`norm`-congr form — to be pinned at build time;
this draft could not determine it without running Lean). -/
theorem cutL10_gammaRemainder_of_conj
    (hConjNorm : ‖Complex.Gamma (((1 / 2 : ℂ) + Complex.I * CutL10.center) / 2)‖
      = ‖Complex.Gamma (((1 / 2 : ℂ) + Complex.I * CutR10.center) / 2)‖)
    (hBanked : Door3CutR10Center.cutR10_gammaRemainder) :
    cutL10_gammaRemainder := by
  have hB : (1 / 2000 : ℝ)
      ≤ ‖Complex.Gamma (((1 / 2 : ℂ) + Complex.I * CutR10.center) / 2)‖ :=
    hBanked
  unfold cutL10_gammaRemainder
  rw [hConjNorm]
  exact hB

/-- ZETA-LANE CONTRACT (adapter mirror of
`Door3ZetaCutoff.cutR10_zetaRemainder_of_certificate_one`,
`door3_zeta_cutoff.lean:384`).
The zeta-lane agent banks the numeral separately with EXACTLY these
hypothesis shapes at `Door3CutL10EtaFactor.sCutL`:
```
  (N : ℕ) (S : ℂ)
  (hSdef : S = ∑ k ∈ Finset.range N,
    etaDirichletTerm Door3CutL10EtaFactor.sCutL k)
  (slow rtail : ℝ) (hSlow : slow ≤ ‖S‖)
  (hTail : ‖(∑' m, etaPairTerm Door3CutL10EtaFactor.sCutL m) - S‖ ≤ rtail)
  (hEnough : (7 / 5 : ℝ) + rtail ≤ slow)
```
and from them derives (via `zeta_lower_of_Sn_tail_factor`
(`zeta_rigorous.lean:3440`) at `s := sCutL` with `cF = 1`, using the
conversion-factor cap `cutL10_etaFactor_le_one` banked in the eta-factor
section below together with `sCutL_pos` / `sCutL_re_ne_one`, also banked
below; note the engine concludes `‖riemannZeta sCutL‖` while `hLower` is
stated with `zeta`, which is definitionally `riemannZeta`
(`riemann_hypothesis.lean:16`, so `exact`/`show` bridges it):
```
  (hLower : slow - rtail ≤ ‖zeta Door3CutL10EtaFactor.sCutL‖)
```
This adapter turns that banked numeral into `cutL10_zetaRemainder`. -/
theorem cutL10_zetaRemainder_of_etaCertificate
    (N : ℕ) (S : ℂ)
    (hSdef : S = ∑ k ∈ Finset.range N,
      etaDirichletTerm Door3CutL10EtaFactor.sCutL k)
    (slow rtail : ℝ) (hSlow : slow ≤ ‖S‖)
    (hTail : ‖(∑' m, etaPairTerm Door3CutL10EtaFactor.sCutL m) - S‖ ≤ rtail)
    (hEnough : (7 / 5 : ℝ) + rtail ≤ slow)
    (hLower : slow - rtail ≤ ‖zeta Door3CutL10EtaFactor.sCutL‖) :
    cutL10_zetaRemainder := by
  unfold cutL10_zetaRemainder
  have hbl : (7 / 5 : ℝ) ≤ slow - rtail := by linarith
  have hsc : Door3CutL10EtaFactor.sCutL
      = (1 / 2 : ℂ) + Complex.I * CutL10.center :=
    Door3CutL10EtaFactor.sCutL_eq_center
  rw [← hsc]
  exact le_trans hbl hLower

/-- DERIV-LANE CONTRACT (mirror of
`Door3ZetaCutoff.cutR10_derivRemainder_of_closedBall_sup`,
`door3_zeta_cutoff.lean:404`): a single entire-function sup enclosure on the
CutL10 center ball of radius `CutL10.radius + 1` gives the named `M = 0.04`
derivative remainder. The sup premise shape is owned by the real-arc lane. -/
theorem cutL10_derivRemainder_of_closedBall_sup
    (hC : ∀ z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1),
      ‖xiShiftedEntire z‖ ≤ (0.04 : ℝ)) :
    cutL10_derivRemainder 0.04 := by
  unfold cutL10_derivRemainder
  have hstrip : ∀ w, CutL10.mem w →
      -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
    intro w hw
    have hlo : CutL10.y0 ≤ w.im := hw.2.2.1
    have hhi : w.im ≤ CutL10.y1 := hw.2.2.2
    rw [CutL10_y0] at hlo
    rw [CutL10_y1] at hhi
    constructor <;> linarith
  have hD := DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CutL10 1 (0.04 : ℝ) (by norm_num) hstrip hC
  intro w hw
  have hle := hD w hw
  norm_num at hle ⊢
  exact hle

/-- H-leaf assembly: the three remainders give the full fencing package
`CellFencingHypotheses CutL10 0.001 0.04` (mirror of
`cutR10_fencing_of_remainders`). -/
theorem cutL10_fencing_of_remainders
    (hG : cutL10_gammaRemainder) (hZ : cutL10_zetaRemainder)
    (hD : cutL10_derivRemainder 0.04) :
    CellFencingHypotheses CutL10 0.001 0.04 := by
  refine { ε_pos := by norm_num, deriv_bound := hD, center_bound := ?_ }
  exact cutL10_center_bound_of_gamma_zeta hG hZ

/-- Fencing gives pointwise nonvanishing on the closed CutL10 rect (strip
H-leaf on closed `mem`; mirror of `Door3RHWiring.cutR10_rect_nonvanishing`). -/
theorem cutL10_rect_nonvanishing
    (H : CellFencingHypotheses CutL10 0.001 0.04)
    {z : ℂ} (hz : CutL10.mem z) : xiShifted z ≠ 0 := by
  have hle := xi_rect_lower_bound_of_center_bound_strip CutL10 0.001 0.04
    CutL10_strip_lo CutL10_strip_hi H.deriv_bound H.center_bound z hz
  intro hz0
  rw [hz0, norm_zero] at hle
  norm_num at hle

/-- Left cutoff line (`Re = -10`, `|Im| ≤ 0.49`) from CutL10 fencing
(mirror of `Door3RHWiring.cutR10_rightLine_nonvanishing_of_fencing`). -/
theorem cutL10_leftLine_nonvanishing_of_fencing
    (H : CellFencingHypotheses CutL10 0.001 0.04)
    {z : ℂ} (hx : z.re = -10)
    (hlo : -(0.49 : ℝ) ≤ z.im) (hhi : z.im ≤ 0.49) :
    xiShifted z ≠ 0 :=
  cutL10_rect_nonvanishing H (CutL10_mem_of_line hx hlo hhi)

/-- Capstone premise (c) `hLeft` in its EXACT `door3_rh_wiring.lean:88-106`
shape, from CutL10 fencing: the thin-rect part (`|Im| ≤ 0.49`) is wired
above; the `0.49 ≤ |Im|` sliver stays the explicit edge-strip-lane premise
`hSliverL` (same split as the right lane). Feeds
`Door3RHWiring.xiCutoffLines10_of_cutR10_and_leftLine` as `hLeft`. -/
theorem hLeft_of_cutL10_fencing_and_sliver
    (H : CellFencingHypotheses CutL10 0.001 0.04)
    (hSliverL : ∀ z : ℂ, z.re = (-10 : ℝ) → -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      (0.49 ≤ z.im ∨ z.im ≤ -0.49) → xiShifted z ≠ 0)
    (z : ℂ) (hx : z.re = (-10 : ℝ)) (hgt : -(1 / 2 : ℝ) < z.im)
    (hlt : z.im < (1 / 2 : ℝ)) (hne : z.im ≠ 0) :
    xiShifted z ≠ 0 := by
  by_cases h1 : -(0.49 : ℝ) ≤ z.im
  · by_cases h2 : z.im ≤ 0.49
    · exact cutL10_leftLine_nonvanishing_of_fencing H hx h1 h2
    · exact hSliverL z hx hgt hlt hne (Or.inl (le_of_lt (lt_of_not_ge h2)))
  · exact hSliverL z hx hgt hlt hne (Or.inr (le_of_lt (lt_of_not_ge h1)))

/-- `XiCutoffLines10` from BOTH fencings (left thin-rect case wired above;
right thin-rect case inline, mirroring
`Door3RHWiring.xiCutoffLines10_of_cutR10_and_leftLine`; the sliver stays an
explicit premise). Lets a fix-wave close the capstone without importing
`door3_rh_wiring`. -/
theorem xiCutoffLines10_of_cutL10_and_cutR10_fencing
    (HL : CellFencingHypotheses CutL10 0.001 0.04)
    (HR : CellFencingHypotheses CutR10 0.001 0.04)
    (hSliver : ∀ z : ℂ, (z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) →
      -(1 / 2 : ℝ) < z.im → z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      (0.49 ≤ z.im ∨ z.im ≤ -0.49) → xiShifted z ≠ 0) :
    RHProofScaffold.XiCutoffLines10 := by
  intro z heq hgt hlt hne
  have hgt' : -(1 / 2 : ℝ) < z.im := by linarith
  rcases cutoffLines_either heq hgt' hlt with h | hs
  · rcases h with hL | hR
    · exact cutL10_rect_nonvanishing HL hL
    · have hle := xi_rect_lower_bound_of_center_bound_strip CutR10 0.001 0.04
        CutR10_strip_lo CutR10_strip_hi HR.deriv_bound HR.center_bound z hR
      intro hz0
      rw [hz0, norm_zero] at hle
      norm_num at hle
  · exact hSliver z heq hgt' hlt hne hs

end Door3CutL10Center

/-! ## Door-3 CutL10 eta conversion factor (cover lane, `cF = 1` wall)

Mirror of `Door3CutR10EtaFactor` (`central_cover_assembly.lean:16813-16960`)
at the conjugate point `sCutL = 1/2 - 10*I`: since `1 - sCutL = 1/2 + 10*I`
has the same modulus data (`Re = 1/2`, `|Im| = 10*log 2` after `log`) and
`Real.cos` is even, the phase-cosine floor — hence the conversion-factor cap
`‖1 - 2^(1-sCutL)‖ ≤ 1` feeding the `_one` certificate adapter — transfers
with only a sign flip in the imaginary-part computation.
-/

namespace Door3CutL10EtaFactor

/-- CutL10 `s`-point in closed form (`Re = 1/2`, `Im = -10`). -/
noncomputable def sCutL : ℂ := (((1 / 2 : ℝ)) : ℂ) + (((-10 : ℝ)) : ℂ) * Complex.I

theorem sCutL_re : sCutL.re = (1 / 2 : ℝ) := by
  simp [sCutL]

theorem sCutL_im : sCutL.im = (-10 : ℝ) := by
  simp [sCutL]

theorem sCutL_pos : 0 < sCutL.re := by rw [sCutL_re]; norm_num

theorem sCutL_re_ne_one : sCutL.re ≠ 1 := by rw [sCutL_re]; norm_num

/-- Transfer: `sCutL` is the shifted point at the CutL10 center. -/
theorem sCutL_eq_center :
    sCutL = (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.CutL10.center := by
  unfold sCutL
  rw [← Door3CutL10Center.cutL10_s_eq]

/-- Conjugation record vs the right-lane point (stated as `re`/`im`
equations so no `star` simp-normal-form risk): `sCutL` is the complex
conjugate of `Door3CutR10EtaFactor.sCutR`. -/
theorem sCutL_re_eq_sCutR_re :
    sCutL.re = Door3CutR10EtaFactor.sCutR.re := by
  rw [sCutL_re, Door3CutR10EtaFactor.sCutR_re]

theorem sCutL_im_eq_neg_sCutR_im :
    sCutL.im = -Door3CutR10EtaFactor.sCutR.im := by
  rw [sCutL_im, Door3CutR10EtaFactor.sCutR_im]; norm_num

/-- Norm of `2^s` (mirror of `cutR10_two_cpow_norm`). -/
theorem cutL10_two_cpow_norm (s : ℂ) :
    ‖(2 : ℂ) ^ s‖ = (2 : ℝ) ^ s.re := by
  have h2 : (2 : ℂ) = (((2 : ℝ)) : ℂ) := by norm_cast
  rw [h2, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Phase-cosine floor at the cutoff (identical statement and proof to
`cutR10_phase_cos_lower`: `|Im|` agrees, `cos` is even). -/
theorem cutL10_phase_cos_lower :
    (3 / 4 : ℝ) ≤ Real.cos (10 * Real.log 2) := by
  have hloglo := Real.log_two_gt_d9
  have hloghi := Real.log_two_lt_d9
  have hπlo := Real.pi_gt_d4
  have hπhi := Real.pi_lt_d4
  have hdlo : (0.6482 : ℝ) < 10 * Real.log 2 - 2 * Real.pi := by linarith
  have hdhi : 10 * Real.log 2 - 2 * Real.pi < (0.6486 : ℝ) := by linarith
  have hsq : (10 * Real.log 2 - 2 * Real.pi) ^ 2 ≤ (0.6486 : ℝ) ^ 2 := by
    have hp : 0 ≤ 10 * Real.log 2 - 2 * Real.pi := by linarith
    nlinarith [sq_nonneg (10 * Real.log 2 - 2 * Real.pi)]
  have hc := Real.one_sub_sq_div_two_le_cos (x := 10 * Real.log 2 - 2 * Real.pi)
  have hbase : (3 / 4 : ℝ) ≤ 1 - (0.6486 : ℝ) ^ 2 / 2 := by norm_num
  have hcosd : (3 / 4 : ℝ) ≤ Real.cos (10 * Real.log 2 - 2 * Real.pi) := by
    nlinarith [hc, hsq]
  rw [Real.cos_sub_two_pi] at hcosd
  exact hcosd

/-- Eta conversion-factor cap `1` at the left cutoff (mirror of
`cutR10_etaFactor_le_one`; the only change is the sign of the imaginary
part: `(log 2 * (1 - sCutL)).im = +(10 * log 2)`, and `cos` needs no `neg`
rewrite since the argument is already positive). -/
theorem cutL10_etaFactor_le_one :
    ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - sCutL)‖ ≤ (1 : ℝ) := by
  have hlog : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) :=
    (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  have hlogre : (Complex.log (2 : ℂ)).re = Real.log 2 := by rw [hlog]; rfl
  have hlogim : (Complex.log (2 : ℂ)).im = 0 := by rw [hlog]; rfl
  let q : ℂ := (2 : ℂ) ^ ((1 : ℂ) - sCutL)
  have hqre : q.re = Real.sqrt 2 * Real.cos (10 * Real.log 2) := by
    dsimp [q]
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    rw [Complex.exp_re]
    have hargre : (Complex.log (2 : ℂ) * (1 - sCutL)).re = Real.log 2 / 2 := by
      rw [Complex.mul_re, hlogre, hlogim]
      simp [sCutL]
      ring
    have hargim : (Complex.log (2 : ℂ) * (1 - sCutL)).im = 10 * Real.log 2 := by
      rw [Complex.mul_im, hlogre, hlogim]
      simp [sCutL]
      ring
    rw [hargre, hargim]
    have hexp : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
      calc
        Real.exp (Real.log 2 / 2) = Real.exp (Real.log 2 * (1 / 2 : ℝ)) := by congr 1 <;> ring
        _ = (2 : ℝ) ^ (1 / 2 : ℝ) :=
          (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _).symm
        _ = Real.sqrt 2 := by rw [← Real.sqrt_eq_rpow]
    rw [hexp]
  have hqnorm : ‖q‖ = Real.sqrt 2 := by
    dsimp [q]
    rw [cutL10_two_cpow_norm]
    have hpow : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 2 := by rw [← Real.sqrt_eq_rpow]
    convert hpow using 1 <;> norm_num [sCutL]
  have hsqid : ‖(1 : ℂ) - q‖ ^ 2 = 1 + ‖q‖ ^ 2 - 2 * q.re := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hq : ‖q‖ ^ 2 = q.re ^ 2 + q.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [hq]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      sub_zero, zero_sub]
    ring
  have hsqrt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hcos := cutL10_phase_cos_lower
  have hprod : (1 : ℝ) ≤ Real.sqrt 2 * Real.cos (10 * Real.log 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hsqrt (by nlinarith [hcos])]
  have hsq : ‖(1 : ℂ) - q‖ ^ 2 ≤ 1 := by
    rw [hsqid, hqnorm, hqre]
    have hsqroot : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
      exact Real.sq_sqrt (by norm_num)
    nlinarith
  have hnonneg : 0 ≤ ‖(1 : ℂ) - q‖ := norm_nonneg _
  nlinarith

/-- Conversion-factor cap stated at the CutL10 center point. -/
theorem cutL10_etaFactor_at_center_le_one :
    ‖(1 : ℂ) - (2 : ℂ) ^
      ((1 : ℂ) - ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.CutL10.center))‖ ≤
      (1 : ℝ) := by
  have h := cutL10_etaFactor_le_one
  rwa [sCutL_eq_center] at h

/-- Product floor value (same numerals as the right lane). -/
theorem cutL10_floor_eq :
    (401 / 8 : ℝ) * (3 / 4) * (1 / 2000) * (7 / 5) = 8421 / 320000 := by norm_num

/-- Fencing need at tier `(0.001, 0.04)` with the banked radius cap `0.56`. -/
theorem cutL10_need_eq : (0.001 : ℝ) + 0.04 * 0.56 = 117 / 5000 := by norm_num

/-- The floor covers the need (so tier `(0.001, 0.04)` is reachable). -/
theorem cutL10_floor_suffices : (117 / 5000 : ℝ) ≤ 8421 / 320000 := by norm_num

/-- Honest negative: the floor does NOT reach the outer tier need `0.03`
(mirror of `cutR10_outer_tier_negative`). -/
theorem cutL10_outer_tier_negative : (8421 / 320000 : ℝ) < 0.03 := by norm_num

end Door3CutL10EtaFactor

#print axioms Door3CutL10Center.cutL10_center_eq
#print axioms Door3CutL10Center.cutL10_s_eq
#print axioms Door3CutL10Center.cutL10_poly_eq
#print axioms Door3CutL10Center.cutL10_poly_norm
#print axioms Door3CutL10Center.cutL10_piExp_re
#print axioms Door3CutL10Center.cutL10_pi_norm_lower
#print axioms Door3CutL10Center.cutL10_center_bound_of_gamma_zeta
#print axioms Door3CutL10Center.cutL10_gammaRemainder_of_conj
#print axioms Door3CutL10Center.cutL10_zetaRemainder_of_etaCertificate
#print axioms Door3CutL10Center.cutL10_derivRemainder_of_closedBall_sup
#print axioms Door3CutL10Center.cutL10_fencing_of_remainders
#print axioms Door3CutL10Center.cutL10_rect_nonvanishing
#print axioms Door3CutL10Center.cutL10_leftLine_nonvanishing_of_fencing
#print axioms Door3CutL10Center.hLeft_of_cutL10_fencing_and_sliver
#print axioms Door3CutL10Center.xiCutoffLines10_of_cutL10_and_cutR10_fencing
#print axioms Door3CutL10EtaFactor.sCutL_re
#print axioms Door3CutL10EtaFactor.sCutL_im
#print axioms Door3CutL10EtaFactor.sCutL_eq_center
#print axioms Door3CutL10EtaFactor.cutL10_two_cpow_norm
#print axioms Door3CutL10EtaFactor.cutL10_phase_cos_lower
#print axioms Door3CutL10EtaFactor.cutL10_etaFactor_le_one
#print axioms Door3CutL10EtaFactor.cutL10_etaFactor_at_center_le_one
#print axioms Door3CutL10EtaFactor.cutL10_floor_eq
#print axioms Door3CutL10EtaFactor.cutL10_need_eq
#print axioms Door3CutL10EtaFactor.cutL10_floor_suffices
#print axioms Door3CutL10EtaFactor.cutL10_outer_tier_negative
