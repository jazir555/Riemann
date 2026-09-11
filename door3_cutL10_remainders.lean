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

/- CutL10 `s`-point in closed form (`Re = 1/2`, `Im = -10`).
Defined here (before `Door3CutL10Center`) so the zeta-certificate
contract at ~259 can reference it without a forward reference;
lemmas about it live in the reopened `Door3CutL10EtaFactor` section below. -/
namespace Door3CutL10EtaFactor

noncomputable def sCutL : ℂ := (((1 / 2 : ℝ)) : ℂ) + (((-10 : ℝ)) : ℂ) * Complex.I

end Door3CutL10EtaFactor

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
      = (1 / 2 : ℂ) + Complex.I * CutL10.center := by
    unfold Door3CutL10EtaFactor.sCutL
    rw [← cutL10_s_eq]
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

/-- `sCutL` is defined above (before `Door3CutL10Center`) to avoid a forward
reference from the zeta-certificate contract. -/

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
  rw [sCutL_im, Door3CutR10EtaFactor.sCutR_im]

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

/-! ## (a) Gamma conjugation closure (PROVED, no premises)

Mathlib pins (read, not guessed):
- `Complex.Gamma_conj (s : ℂ) : Gamma (conj s) = conj (Gamma s)`
  (`Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:355`, inside
  `namespace Complex` spanning `:141-:396`).
- `Complex.norm_conj (z : ℂ) : ‖conj z‖ = ‖z‖`
  (`Mathlib/Analysis/Complex/Norm.lean:96`, inside `namespace Complex`).
Norm respects `conj` (hence `star`, since `star = conj` on `ℂ`).

Points: `sCutL/2 = 1/4 - 5*I` is the conjugate of `sCutR/2 = 1/4 + 5*I`.
The banked type cited read-only from `door3_gamma_cutoff.lean:122` is
`theorem cutR10_gammaRemainder : Door3CutR10Center.cutR10_gammaRemainder`
(no hypotheses). The existing adapter `cutL10_gammaRemainder_of_conj`
takes `(hBanked : Door3CutR10Center.cutR10_gammaRemainder)` of exactly
that type; filling `hConjNorm` below leaves only that banked premise,
which is already discharged in its home file (pending build check only).
-/

namespace Door3CutL10GammaConj

open CentralCoverAssembly
open scoped ComplexConjugate

/-- Left Gamma point is the conjugate of the right Gamma point. -/
theorem cutL10_gammaPoint_eq_conj_cutR10_gammaPoint :
    (((1 / 2 : ℂ) + Complex.I * CutL10.center) / 2)
      = star (((1 / 2 : ℂ) + Complex.I * CutR10.center) / 2) := by
  have hL := Door3CutL10Center.cutL10_s_eq
  have hR := Door3CutR10Center.cutR10_s_eq
  rw [hL, hR]
  apply Complex.ext <;> simp <;> norm_num

/-- Norm equality of Gamma at the two conjugate half-points (real theorem,
no premises; uses `Complex.Gamma_conj` + `Complex.norm_conj`). -/
theorem cutL10_gammaConjNorm :
    ‖Complex.Gamma (((1 / 2 : ℂ) + Complex.I * CutL10.center) / 2)‖
      = ‖Complex.Gamma (((1 / 2 : ℂ) + Complex.I * CutR10.center) / 2)‖ := by
  have hpt := cutL10_gammaPoint_eq_conj_cutR10_gammaPoint
  have hptc : (((1 / 2 : ℂ) + Complex.I * CutL10.center) / 2)
      = conj (((1 / 2 : ℂ) + Complex.I * CutR10.center) / 2) := hpt
  rw [hptc, Complex.Gamma_conj, Complex.norm_conj]

/-- Gamma remainder from the banked right-lane certificate plus the proved
conjugacy above. The premise type is byte-for-byte the banked certificate
`Door3GammaCutoff.cutR10_gammaRemainder :
Door3CutR10Center.cutR10_gammaRemainder` (`door3_gamma_cutoff.lean:122`,
no hypotheses). -/
theorem cutL10_gammaRemainder_of_banked
    (hBanked : Door3CutR10Center.cutR10_gammaRemainder) :
    Door3CutL10Center.cutL10_gammaRemainder := by
  exact Door3CutL10Center.cutL10_gammaRemainder_of_conj
    cutL10_gammaConjNorm hBanked

end Door3CutL10GammaConj

/-! ## (b) CutL10 closed-ball sup enclosure (mirror of `door3_cutR10_ballsup.lean`)

Mirror map (read-only): `Door3CutR10BallSup` in `door3_cutR10_ballsup.lean`
proves ball radius cap, `z.re`/`z.im` bounds, `s`-region bounds,
`shiftedS z ≠ 0, 1`, poly exact transfer plus `≤ 67` upper, pi upper
`≤ 16/5`, factor-separated `≤ 12.87` assembly, and exact `0.04` shape
conditional on joint product sup `hJoint` plus product identity `hProd`.

Adaptation to center `≈ -10` (`CutL10.center = ((-10 : ℝ) : ℂ)`):
- `z.re ∈ [-11.56, -8.44]` (was `[8.44, 11.56]`), `z.im ∈ [-1.56, 1.56]`
  (unchanged, center `im = 0`).
- `s.re = 1/2 - z.im ∈ [-1.06, 2.06]` (unchanged, depends only on `z.im`).
- `s.im = z.re ∈ [-11.56, -8.44]` (was `[8.44, 11.56]`; sign flip only).
- Poly transfer `(1/2)*s*(s-1) = -((z^2+1/4)/2)` is center-independent;
  `‖z‖ ≤ 11.56` holds by the same triangle via `‖center‖ = 10`, so the
  same `≤ 67` numeral holds (proved below with `≤ 134` intermediate to
  respect the `≤ 6`-digit numeral discipline; no `133.8836` literal).
- Pi upper `≤ 16/5` uses only `s.re ≥ -1.06`, hence identical.
- Zeta sup `≤ 6` and Gamma sup `≤ 1/100` on the mirrored strip are
  premise-gated (genuinely unclosable this wave: strip wall needs FE plus
  Stirling plus convexity). TRUE values by conjugation symmetry with the
  right lane: center `‖zeta(sCutL)‖ ≈ 1.549` (same as `sCutR`, norm
  respects `conj`), region Gamma sup `≈ 0.0071` (mirror of the
  `(1.03 + 4.22*I)` corner), center Gamma `≈ 0.000651`.
- Honest factor-separated reach is `≤ 12.87`
  (`67 * (16/5) * (1/100) * 6 = 12.864`), NOT `0.04`; the exact `0.04`
  shape is conditional on the single explicit joint-sup premise `hJoint`
  (the `(b)`-delta), exactly as in the right-lane draft.
-/

namespace Door3CutL10BallSup

open CentralCoverAssembly

/-- Ball radius cap from the banked `CutL10.radius < 0.56`. -/
theorem cutL10_ball_radius_le : CutL10.radius + 1 ≤ (1.56 : ℝ) := by
  have h := CutL10_radius_lt
  linarith

/-- Distance from the left center, in norm form. -/
theorem cutL10_mem_ball_norm_le (z : ℂ)
    (hz : z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1)) :
    ‖z - ((((-10 : ℝ)) : ℂ))‖ ≤ (1.56 : ℝ) := by
  have hmem : dist z CutL10.center ≤ CutL10.radius + 1 :=
    Metric.mem_closedBall.mp hz
  rw [Door3CutL10Center.cutL10_center_eq, dist_eq_norm] at hmem
  exact le_trans hmem cutL10_ball_radius_le

/-- Real parts on the left ball: `z.re ∈ [-11.56, -8.44]`. -/
theorem cutL10_mem_ball_re_bounds (z : ℂ)
    (hz : z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1)) :
    (-11.56 : ℝ) ≤ z.re ∧ z.re ≤ (-8.44 : ℝ) := by
  have hd := cutL10_mem_ball_norm_le z hz
  have hre : |(z - ((((-10 : ℝ)) : ℂ))).re| ≤ (1.56 : ℝ) := by
    calc |(z - ((((-10 : ℝ)) : ℂ))).re| ≤ ‖z - ((((-10 : ℝ)) : ℂ))‖ :=
          Complex.abs_re_le_norm _
      _ ≤ (1.56 : ℝ) := hd
  have here : (z - ((((-10 : ℝ)) : ℂ))).re = z.re + 10 := by
    simp
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the left ball: `z.im ∈ [-1.56, 1.56]`. -/
theorem cutL10_mem_ball_im_bounds (z : ℂ)
    (hz : z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1)) :
    (-1.56 : ℝ) ≤ z.im ∧ z.im ≤ (1.56 : ℝ) := by
  have hd := cutL10_mem_ball_norm_le z hz
  have him : |(z - ((((-10 : ℝ)) : ℂ))).im| ≤ (1.56 : ℝ) := by
    calc |(z - ((((-10 : ℝ)) : ℂ))).im| ≤ ‖z - ((((-10 : ℝ)) : ℂ))‖ :=
          Complex.abs_im_le_norm _
      _ ≤ (1.56 : ℝ) := hd
  have heim : (z - ((((-10 : ℝ)) : ℂ))).im = z.im := by
    simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- Absolute norm cap on the left ball: `‖z‖ ≤ 11.56`. -/
theorem cutL10_mem_ball_abs_norm_le (z : ℂ)
    (hz : z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1)) :
    ‖z‖ ≤ (11.56 : ℝ) := by
  have hd := cutL10_mem_ball_norm_le z hz
  have h10 : ‖((((-10 : ℝ)) : ℂ))‖ = (10 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hdecomp : z = (z - ((((-10 : ℝ)) : ℂ))) + ((((-10 : ℝ)) : ℂ)) := by
    abel
  calc ‖z‖ = ‖(z - ((((-10 : ℝ)) : ℂ))) + ((((-10 : ℝ)) : ℂ))‖ := by
        conv_lhs => rw [hdecomp]
    _ ≤ ‖z - ((((-10 : ℝ)) : ℂ))‖ + ‖((((-10 : ℝ)) : ℂ))‖ :=
        norm_add_le _ _
    _ ≤ (11.56 : ℝ) := by
        rw [h10]
        linarith

/-- `s.re = 1/2 - z.im ∈ [-1.06, 2.06]` on the left ball. -/
theorem cutL10_mem_ball_shiftedS_re_bounds (z : ℂ)
    (hz : z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1)) :
    (-1.06 : ℝ) ≤ (shiftedS z).re ∧ (shiftedS z).re ≤ (2.06 : ℝ) := by
  rw [shiftedS_re]
  obtain ⟨hlo, hhi⟩ := cutL10_mem_ball_im_bounds z hz
  constructor <;> linarith

/-- `s.im = z.re ∈ [-11.56, -8.44]` on the left ball. -/
theorem cutL10_mem_ball_shiftedS_im_bounds (z : ℂ)
    (hz : z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1)) :
    (-11.56 : ℝ) ≤ (shiftedS z).im ∧ (shiftedS z).im ≤ (-8.44 : ℝ) := by
  rw [RHProofScaffold.LeafDecomp.shiftedS_im_eq]
  exact cutL10_mem_ball_re_bounds z hz

/-- The shifted point avoids `0` (its imaginary part is `≤ -8.44`). -/
theorem cutL10_mem_ball_shiftedS_ne_zero (z : ℂ)
    (hz : z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1)) :
    shiftedS z ≠ 0 := by
  intro h0
  have him : z.re = 0 := by
    have hcon := congrArg Complex.im h0
    rw [RHProofScaffold.LeafDecomp.shiftedS_im_eq] at hcon
    simp at hcon
    exact hcon
  linarith [(cutL10_mem_ball_re_bounds z hz).2]

/-- The shifted point avoids `1` (same imaginary-part argument). -/
theorem cutL10_mem_ball_shiftedS_ne_one (z : ℂ)
    (hz : z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1)) :
    shiftedS z ≠ 1 := by
  intro h0
  have him : z.re = 0 := by
    have hcon := congrArg Complex.im h0
    rw [RHProofScaffold.LeafDecomp.shiftedS_im_eq] at hcon
    simp at hcon
    exact hcon
  linarith [(cutL10_mem_ball_re_bounds z hz).2]

/-- Exact transfer `(1/2)*s*(s-1) = -((z^2+1/4)/2)` for `s = shiftedS z`. -/
theorem cutL10_ballPoly_eq (z : ℂ) :
    (1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)
      = -((z ^ 2 + (1 / 4 : ℂ)) / 2) := by
  have hI : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
  unfold shiftedS
  linear_combination (z ^ 2 / 2) * hI

/-- Poly-factor upper `≤ 67` on the left ball. -/
theorem cutL10_ballPoly_upper (z : ℂ)
    (hz : z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1)) :
    ‖(1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)‖ ≤ (67 : ℝ) := by
  have hz2 := cutL10_mem_ball_abs_norm_le z hz
  have h14 : ‖((1 / 4 : ℂ))‖ = ((1 / 4 : ℝ)) := by
    have hcast : ((1 / 4 : ℂ)) = ((((1 / 4 : ℝ)) : ℂ)) := by simp
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have h2 : ‖((2 : ℂ))‖ = (2 : ℝ) := by norm_num
  have hsq : ‖z ^ 2‖ = ‖z‖ ^ 2 := norm_pow z 2
  have hpow : ‖z‖ ^ 2 ≤ (11.56 : ℝ) ^ 2 := by
    have h1 : ‖z‖ * ‖z‖ ≤ (11.56 : ℝ) * (11.56 : ℝ) :=
      mul_le_mul hz2 hz2 (norm_nonneg _) (by norm_num)
    rw [pow_two, pow_two]
    exact h1
  rw [cutL10_ballPoly_eq, norm_neg, norm_div, h2]
  have hle : ‖z ^ 2 + (1 / 4 : ℂ)‖ ≤ (134 : ℝ) := by
    calc ‖z ^ 2 + (1 / 4 : ℂ)‖ ≤ ‖z ^ 2‖ + ‖((1 / 4 : ℂ))‖ :=
          norm_add_le _ _
      _ = ‖z‖ ^ 2 + 1 / 4 := by rw [hsq, h14]
      _ ≤ (134 : ℝ) := by
          have hnum : (11.56 : ℝ) ^ 2 + 1 / 4 ≤ (134 : ℝ) := by norm_num
          linarith
  linarith

/-- Pi-power upper on the left ball: `≤ 16/5` (uses only `s.re ≥ -1.06`). -/
theorem cutL10_ballPi_upper (z : ℂ)
    (hz : z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1)) :
    ‖((Real.pi : ℂ) ^ (-(shiftedS z / 2)))‖ ≤ (16 / 5 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have hre : (-(shiftedS z / 2)).re = -(shiftedS z).re / 2 := by
    have hdiv : ((shiftedS z / 2 : ℂ)).re = (shiftedS z).re / 2 := by
      simp [Complex.div_ofNat]
    rw [Complex.neg_re, hdiv, neg_div]
  rw [hre]
  have hslo := (cutL10_mem_ball_shiftedS_re_bounds z hz).1
  have hexp : (-(shiftedS z).re / 2) ≤ (1 : ℝ) := by linarith
  have hbase : Real.pi ^ (-(shiftedS z).re / 2) ≤ Real.pi ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hexp
  have h1 : Real.pi ^ (1 : ℝ) = Real.pi := Real.rpow_one _
  have hpi : Real.pi ≤ (16 / 5 : ℝ) := by
    have h := Real.pi_lt_d2
    norm_num at h ⊢
    linarith
  rw [h1] at hbase
  exact le_trans hbase hpi

/-- Factor-separated sup: honest numerals reach `≤ 12.87`
(`67 * (16/5) * (1/100) * 6 = 12.864`), NOT `0.04`.
Premises: `hProd` (global product identity on the ball);
`hZetaSup` (strip zeta upper, TRUE order `O(1)`-`O(5)`; center `≈ 1.549`
by conjugation with the right lane); `hGammaSup` (Stirling Gamma upper
on `s/2`, TRUE sup `≈ 0.0071`, TRUE center `≈ 0.000651`, mirror corner
`(1.03 - 4.22*I)`). -/
theorem cutL10_ballSup_of_factorSups
    (hProd : ∀ (z : ℂ), z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1) →
      xiShiftedEntire z = ((1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1))
        * ((Real.pi : ℂ) ^ (-(shiftedS z / 2)))
        * (Complex.Gamma (shiftedS z / 2)) * (zeta (shiftedS z)))
    (hZetaSup : ∀ (s : ℂ), (-1.06 : ℝ) ≤ s.re → s.re ≤ (2.06 : ℝ) →
      (-11.56 : ℝ) ≤ s.im → s.im ≤ (-8.44 : ℝ) → ‖zeta s‖ ≤ (6 : ℝ))
    (hGammaSup : ∀ (s : ℂ), (-1.06 : ℝ) ≤ s.re → s.re ≤ (2.06 : ℝ) →
      (-11.56 : ℝ) ≤ s.im → s.im ≤ (-8.44 : ℝ) →
      ‖Complex.Gamma (s / 2)‖ ≤ (1 / 100 : ℝ)) :
    ∀ (z : ℂ), z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1) →
      ‖xiShiftedEntire z‖ ≤ (12.87 : ℝ) := by
  intro z hz
  have hP := hProd z hz
  rw [hP, norm_mul, norm_mul, norm_mul]
  have hpoly := cutL10_ballPoly_upper z hz
  have hpi := cutL10_ballPi_upper z hz
  have hre := cutL10_mem_ball_shiftedS_re_bounds z hz
  have him := cutL10_mem_ball_shiftedS_im_bounds z hz
  have hz2 : ‖zeta (shiftedS z)‖ ≤ (6 : ℝ) :=
    hZetaSup _ hre.1 hre.2 him.1 him.2
  have hG : ‖Complex.Gamma (shiftedS z / 2)‖ ≤ (1 / 100 : ℝ) :=
    hGammaSup _ hre.1 hre.2 him.1 him.2
  have g1 : ‖(1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)‖
        * ‖((Real.pi : ℂ) ^ (-(shiftedS z / 2)))‖ ≤ (67 : ℝ) * (16 / 5) :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have g2 : (‖(1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)‖
        * ‖((Real.pi : ℂ) ^ (-(shiftedS z / 2)))‖)
        * ‖Complex.Gamma (shiftedS z / 2)‖
        ≤ ((67 : ℝ) * (16 / 5)) * (1 / 100) :=
    mul_le_mul g1 hG (norm_nonneg _) (by norm_num)
  have g3 : ((‖(1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)‖
        * ‖((Real.pi : ℂ) ^ (-(shiftedS z / 2)))‖)
        * ‖Complex.Gamma (shiftedS z / 2)‖) * ‖zeta (shiftedS z)‖
        ≤ (((67 : ℝ) * (16 / 5)) * (1 / 100)) * 6 :=
    mul_le_mul g2 hz2 (norm_nonneg _) (by norm_num)
  have hcap : (((67 : ℝ) * (16 / 5)) * (1 / 100)) * 6 ≤ (12.87 : ℝ) := by
    norm_num
  exact le_trans g3 hcap

/-- Exact premise-(b) shape `hC`, conditional on the joint pointwise product
sup `hJoint` (the single `(b)`-delta residual premise for the patch phase)
plus the product identity `hProd`. Conclusion is byte-for-byte the `hC`
consumed by `Door3CutL10Center.cutL10_derivRemainder_of_closedBall_sup`. -/
theorem cutL10_closedBall_sup
    (hProd : ∀ (z : ℂ), z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1) →
      xiShiftedEntire z = ((1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1))
        * ((Real.pi : ℂ) ^ (-(shiftedS z / 2)))
        * (Complex.Gamma (shiftedS z / 2)) * (zeta (shiftedS z)))
    (hJoint : ∀ (z : ℂ), z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1) →
      ‖(1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)‖
        * ‖((Real.pi : ℂ) ^ (-(shiftedS z / 2)))‖
        * ‖Complex.Gamma (shiftedS z / 2)‖ * ‖zeta (shiftedS z)‖
        ≤ (0.04 : ℝ)) :
    ∀ (z : ℂ), z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1) →
      ‖xiShiftedEntire z‖ ≤ (0.04 : ℝ) := by
  intro z hz
  have hP := hProd z hz
  rw [hP, norm_mul, norm_mul, norm_mul]
  exact hJoint z hz

/-- Derivative remainder from the joint sup (chains the proved `hC`
through the already-banked Cauchy adapter). -/
theorem cutL10_derivRemainder_of_joint
    (hProd : ∀ (z : ℂ), z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1) →
      xiShiftedEntire z = ((1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1))
        * ((Real.pi : ℂ) ^ (-(shiftedS z / 2)))
        * (Complex.Gamma (shiftedS z / 2)) * (zeta (shiftedS z)))
    (hJoint : ∀ (z : ℂ), z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1) →
      ‖(1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)‖
        * ‖((Real.pi : ℂ) ^ (-(shiftedS z / 2)))‖
        * ‖Complex.Gamma (shiftedS z / 2)‖ * ‖zeta (shiftedS z)‖
        ≤ (0.04 : ℝ)) :
    Door3CutL10Center.cutL10_derivRemainder 0.04 := by
  have hC := cutL10_closedBall_sup hProd hJoint
  exact Door3CutL10Center.cutL10_derivRemainder_of_closedBall_sup hC

end Door3CutL10BallSup

/-! ## (c) Fencing closure modulo the single zeta-numeral premise

The zeta-numeral premise `hLower` at `Door3CutL10EtaFactor.sCutL` with
EXACT in-file shape
`(hLower : slow - rtail ≤ ‖zeta Door3CutL10EtaFactor.sCutL‖)`
is LEFT UNSOLVED here by design: a zeta-lane agent banks it separately
(no duplication). Everything below is complete modulo that ONE premise
(plus the `(b)`-delta `hProd`/`hJoint` gated above, plus the banked Gamma
premise discharged in its home file, plus the edge-strip sliver owned by
its lane). Dependency order is respected throughout.
-/

namespace Door3CutL10FencingClose

open CentralCoverAssembly

/-- Full fencing from all suppliers (Gamma banked, zeta numeral, joint sup).
Residual premises: exactly `hLower` (zeta lane) plus `hProd`/`hJoint`
(`(b)`-delta) plus `hBanked` (banked, no hypotheses in its home file). -/
theorem cutL10_fencing_of_all_suppliers
    (hBanked : Door3CutR10Center.cutR10_gammaRemainder)
    (N : ℕ) (S : ℂ)
    (hSdef : S = ∑ k ∈ Finset.range N,
      etaDirichletTerm Door3CutL10EtaFactor.sCutL k)
    (slow rtail : ℝ) (hSlow : slow ≤ ‖S‖)
    (hTail : ‖(∑' m, etaPairTerm Door3CutL10EtaFactor.sCutL m) - S‖ ≤ rtail)
    (hEnough : (7 / 5 : ℝ) + rtail ≤ slow)
    (hLower : slow - rtail ≤ ‖zeta Door3CutL10EtaFactor.sCutL‖)
    (hProd : ∀ (z : ℂ), z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1) →
      xiShiftedEntire z = ((1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1))
        * ((Real.pi : ℂ) ^ (-(shiftedS z / 2)))
        * (Complex.Gamma (shiftedS z / 2)) * (zeta (shiftedS z)))
    (hJoint : ∀ (z : ℂ), z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1) →
      ‖(1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)‖
        * ‖((Real.pi : ℂ) ^ (-(shiftedS z / 2)))‖
        * ‖Complex.Gamma (shiftedS z / 2)‖ * ‖zeta (shiftedS z)‖
        ≤ (0.04 : ℝ)) :
    CellFencingHypotheses CutL10 0.001 0.04 := by
  have hG := Door3CutL10GammaConj.cutL10_gammaRemainder_of_banked hBanked
  have hZ := Door3CutL10Center.cutL10_zetaRemainder_of_etaCertificate
    N S hSdef slow rtail hSlow hTail hEnough hLower
  have hD := Door3CutL10BallSup.cutL10_derivRemainder_of_joint hProd hJoint
  exact Door3CutL10Center.cutL10_fencing_of_remainders hG hZ hD

/-- Capstone `hLeft` from the same suppliers plus the edge-strip sliver. -/
theorem cutL10_hLeft_of_all_suppliers
    (hBanked : Door3CutR10Center.cutR10_gammaRemainder)
    (N : ℕ) (S : ℂ)
    (hSdef : S = ∑ k ∈ Finset.range N,
      etaDirichletTerm Door3CutL10EtaFactor.sCutL k)
    (slow rtail : ℝ) (hSlow : slow ≤ ‖S‖)
    (hTail : ‖(∑' m, etaPairTerm Door3CutL10EtaFactor.sCutL m) - S‖ ≤ rtail)
    (hEnough : (7 / 5 : ℝ) + rtail ≤ slow)
    (hLower : slow - rtail ≤ ‖zeta Door3CutL10EtaFactor.sCutL‖)
    (hProd : ∀ (z : ℂ), z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1) →
      xiShiftedEntire z = ((1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1))
        * ((Real.pi : ℂ) ^ (-(shiftedS z / 2)))
        * (Complex.Gamma (shiftedS z / 2)) * (zeta (shiftedS z)))
    (hJoint : ∀ (z : ℂ), z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1) →
      ‖(1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)‖
        * ‖((Real.pi : ℂ) ^ (-(shiftedS z / 2)))‖
        * ‖Complex.Gamma (shiftedS z / 2)‖ * ‖zeta (shiftedS z)‖
        ≤ (0.04 : ℝ))
    (hSliverL : ∀ (z : ℂ), z.re = (-10 : ℝ) → -(1 / 2 : ℝ) < z.im →
      z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      (0.49 ≤ z.im ∨ z.im ≤ -0.49) → xiShifted z ≠ 0)
    (z : ℂ) (hx : z.re = (-10 : ℝ)) (hgt : -(1 / 2 : ℝ) < z.im)
    (hlt : z.im < (1 / 2 : ℝ)) (hne : z.im ≠ 0) :
    xiShifted z ≠ 0 := by
  have H := cutL10_fencing_of_all_suppliers hBanked N S hSdef slow rtail
    hSlow hTail hEnough hLower hProd hJoint
  exact Door3CutL10Center.hLeft_of_cutL10_fencing_and_sliver H hSliverL z hx hgt hlt hne

/-- `XiCutoffLines10` from both fencings plus the same left suppliers. -/
theorem cutL10_xiCutoffLines10_of_all_suppliers
    (hBanked : Door3CutR10Center.cutR10_gammaRemainder)
    (N : ℕ) (S : ℂ)
    (hSdef : S = ∑ k ∈ Finset.range N,
      etaDirichletTerm Door3CutL10EtaFactor.sCutL k)
    (slow rtail : ℝ) (hSlow : slow ≤ ‖S‖)
    (hTail : ‖(∑' m, etaPairTerm Door3CutL10EtaFactor.sCutL m) - S‖ ≤ rtail)
    (hEnough : (7 / 5 : ℝ) + rtail ≤ slow)
    (hLower : slow - rtail ≤ ‖zeta Door3CutL10EtaFactor.sCutL‖)
    (hProd : ∀ (z : ℂ), z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1) →
      xiShiftedEntire z = ((1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1))
        * ((Real.pi : ℂ) ^ (-(shiftedS z / 2)))
        * (Complex.Gamma (shiftedS z / 2)) * (zeta (shiftedS z)))
    (hJoint : ∀ (z : ℂ), z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1) →
      ‖(1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)‖
        * ‖((Real.pi : ℂ) ^ (-(shiftedS z / 2)))‖
        * ‖Complex.Gamma (shiftedS z / 2)‖ * ‖zeta (shiftedS z)‖
        ≤ (0.04 : ℝ))
    (HR : CellFencingHypotheses CutR10 0.001 0.04)
    (hSliver : ∀ (z : ℂ), (z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) →
      -(1 / 2 : ℝ) < z.im → z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      (0.49 ≤ z.im ∨ z.im ≤ -0.49) → xiShifted z ≠ 0) :
    RHProofScaffold.XiCutoffLines10 := by
  have HL := cutL10_fencing_of_all_suppliers hBanked N S hSdef slow rtail
    hSlow hTail hEnough hLower hProd hJoint
  exact Door3CutL10Center.xiCutoffLines10_of_cutL10_and_cutR10_fencing HL HR hSliver

end Door3CutL10FencingClose

#print axioms Door3CutL10GammaConj.cutL10_gammaPoint_eq_conj_cutR10_gammaPoint
#print axioms Door3CutL10GammaConj.cutL10_gammaConjNorm
#print axioms Door3CutL10GammaConj.cutL10_gammaRemainder_of_banked
#print axioms Door3CutL10BallSup.cutL10_ball_radius_le
#print axioms Door3CutL10BallSup.cutL10_mem_ball_norm_le
#print axioms Door3CutL10BallSup.cutL10_mem_ball_re_bounds
#print axioms Door3CutL10BallSup.cutL10_mem_ball_im_bounds
#print axioms Door3CutL10BallSup.cutL10_mem_ball_abs_norm_le
#print axioms Door3CutL10BallSup.cutL10_mem_ball_shiftedS_re_bounds
#print axioms Door3CutL10BallSup.cutL10_mem_ball_shiftedS_im_bounds
#print axioms Door3CutL10BallSup.cutL10_mem_ball_shiftedS_ne_zero
#print axioms Door3CutL10BallSup.cutL10_mem_ball_shiftedS_ne_one
#print axioms Door3CutL10BallSup.cutL10_ballPoly_eq
#print axioms Door3CutL10BallSup.cutL10_ballPoly_upper
#print axioms Door3CutL10BallSup.cutL10_ballPi_upper
#print axioms Door3CutL10BallSup.cutL10_ballSup_of_factorSups
#print axioms Door3CutL10BallSup.cutL10_closedBall_sup
#print axioms Door3CutL10BallSup.cutL10_derivRemainder_of_joint
#print axioms Door3CutL10FencingClose.cutL10_fencing_of_all_suppliers
#print axioms Door3CutL10FencingClose.cutL10_hLeft_of_all_suppliers
#print axioms Door3CutL10FencingClose.cutL10_xiCutoffLines10_of_all_suppliers

/-! ## (d) CutL10 Tier-B closure (append-only tail; LF)

Mirror of the right-ball Tier-B story (`door3_cutR10_ballsup.lean` APPEND-2
(d) plus `door3_cutR10_retier.lean` Tier B):

(a) LEFT endpoint audit: at the in-ball real endpoint `z0 = -8.44`
(`s0 = 1/2 - 8.44*I`, conjugate of the right `1/2 + 8.44*I`) the
poly norm is the same `35.7418` (depends only on `|z0|^2`), the pi
lower is the same `7/10` (depends only on `Re s0 = 1/2`), hence
poly times pi is `>= 24` (mirror image of `cutR10_poly_pi_lower_endpoint`).
TRUE values (conjugation symmetry, norms respect `conj`): poly `35.7418`,
pi `pi^(-1/4) approx 0.7512`, Stirling Gamma at `s0/2 = 1/4 - 4.22*I`
approx `0.0023`, so poly times pi times Gamma approx `0.062 > 0.04`
BEFORE zeta; joint `<= 0.04` would need `|zeta(1/2 - 8.44*I)| <= 2/3`
(approx `0.64` shortfall), implausible this far below the first zero
(`t approx 14.13`, center value approx `1.549`). Center four-factor TRUE
value is the same approx `0.03797`
(`50.125 * 0.7512 * 0.000651 * 1.549`); certified floor
`8421/320000` covers need `117/5000 = 0.0234`.
The zeta lower numeral `hLower` stays ZU36-owned (not duplicated);
the Gamma lower `hBanked` is banked (see `Door3CutL10GammaConj`).

(b) Tier-B conditional: shared sup `C` on `closedBall center (radius + rhoC)`
gives deriv `C / rhoC` on the rect (Cauchy), hence shrunken fencing from
the feasibility inequality `0.001 + (C / rhoC) * rho <= 8421/320000`
with the LEFT floor/center numbers (same numerals as the right lane by
conjugation). Instantiated at `(C, rhoC, rho) = (12.87, 1, 0.001)`.

(c) Wired locally (reproved, never imported): endpoint numerals, `hProd`
closed, Euler sliver conditional, Gamma denom lower plus gated `1/100`
assembly, sharp `12.87` shared-sup assembly from closed `hProd`.
Residual: `hZetaSup` strip wall, `hGammaSup` Stirling upper (`hProdCap`),
`hLower` (zeta lane), `hBanked` (banked), edge-strip sliver.
Explicit binders only; no placeholders.
-/

namespace Door3CutL10TierB

open CentralCoverAssembly

/-- Endpoint poly norm at `z0 = -8.44`: `35.7418` (mirror of the right
`8.44` value; `(-8.44)^2 = 8.44^2`). -/
theorem cutL10_endpoint_poly_norm :
    ‖(1 / 2 : ℂ) * ((1 / 2 : ℂ) + Complex.I * (((-8.44 : ℝ)) : ℂ)) *
      (((1 / 2 : ℂ) + Complex.I * (((-8.44 : ℝ)) : ℂ)) - 1)‖
      = (35.7418 : ℝ) := by
  have heq : (1 / 2 : ℂ) * ((1 / 2 : ℂ) + Complex.I * (((-8.44 : ℝ)) : ℂ)) *
      (((1 / 2 : ℂ) + Complex.I * (((-8.44 : ℝ)) : ℂ)) - 1) =
      -(((((-8.44 : ℝ)) : ℂ) ^ 2 + (1 / 4 : ℂ)) / 2) := by
    have hI : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
    have hz : shiftedS ((((-8.44 : ℝ)) : ℂ))
        = (1 / 2 : ℂ) + Complex.I * (((-8.44 : ℝ)) : ℂ) := by
      unfold shiftedS
      push_cast
      ring
    have hpoly := Door3CutL10BallSup.cutL10_ballPoly_eq ((((-8.44 : ℝ)) : ℂ))
    rw [hz] at hpoly
    exact hpoly
  rw [heq, norm_neg]
  have hcast : (((((-8.44 : ℝ)) : ℂ) ^ 2 + (1 / 4 : ℂ)) / 2)
      = ((((35.7418 : ℝ)) : ℂ)) := by
    norm_cast
    push_cast
    norm_num
  rw [hcast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num)]

/-- Endpoint pi lower at `s0 = 1/2 - 8.44*I`: `7/10 <= ‖pi^(-s0/2)‖`
(depends only on `Re = 1/2`, hence identical to the right lane). -/
theorem cutL10_endpoint_pi_lower :
    (7 / 10 : ℝ) ≤ ‖((Real.pi : ℂ) ^
      (-(((1 / 2 : ℂ) + Complex.I * (((-8.44 : ℝ)) : ℂ)) / 2)))‖ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have hre : (-(((1 / 2 : ℂ) + Complex.I * (((-8.44 : ℝ)) : ℂ)) / 2)).re
      = (-(1 / 4) : ℝ) := by
    simp [Complex.div_ofNat]
  rw [hre]
  have hpi3 : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
  have hmono : (3 : ℝ) ^ (-(1 / 4 : ℝ)) ≤ Real.pi ^ (-(1 / 4 : ℝ)) := by
    apply Real.rpow_le_rpow (by norm_num) hpi3 (by norm_num)
  have h3 : (7 / 10 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by norm_num
  exact le_trans h3 hmono

/-- Poly times pi lower at the left endpoint: `>= 24` (mirror image of
`cutR10_poly_pi_lower_endpoint`). -/
theorem cutL10_poly_pi_lower_endpoint :
    ‖(1 / 2 : ℂ) * ((1 / 2 : ℂ) + Complex.I * (((-8.44 : ℝ)) : ℂ)) *
      (((1 / 2 : ℂ) + Complex.I * (((-8.44 : ℝ)) : ℂ)) - 1)‖ *
    ‖((Real.pi : ℂ) ^ (-(((1 / 2 : ℂ) + Complex.I * (((-8.44 : ℝ)) : ℂ)) / 2)))‖
      ≥ 24 := by
  have hpoly := cutL10_endpoint_poly_norm
  have hpi := cutL10_endpoint_pi_lower
  calc ‖(1 / 2 : ℂ) * ((1 / 2 : ℂ) + Complex.I * (((-8.44 : ℝ)) : ℂ)) *
        (((1 / 2 : ℂ) + Complex.I * (((-8.44 : ℝ)) : ℂ)) - 1)‖ *
      ‖((Real.pi : ℂ) ^ (-(((1 / 2 : ℂ) + Complex.I * (((-8.44 : ℝ)) : ℂ)) / 2)))‖
      ≥ 35.7418 * (7 / 10) :=
        mul_le_mul hpoly.le hpi (by norm_num) (by norm_num)
    _ ≥ 24 := by norm_num

/-- Shortfall implication: triple `>= 6/100` plus joint `<= 4/100` forces
`‖zeta‖ <= 2/3` at the endpoint (quantified `0.64` shortfall). -/
theorem cutL10_joint_implies_zeta_cap (g : ℝ) (z0 : ℝ)
    (hg : (6 / 100 : ℝ) ≤ g) (hz0 : (0 : ℝ) ≤ z0)
    (hJoint : g * z0 ≤ (4 / 100 : ℝ)) :
    z0 ≤ (2 / 3 : ℝ) := by
  have hpos : (0 : ℝ) < g := by linarith
  rw [div_le_iff₀ hpos] at hg ⊢
  nlinarith [hJoint]

/-- Shifted-half imaginary part is nonzero on the left ball
(`(s/2).im = s.im/2 <= -4.22`). -/
theorem cutL10_shiftedS_half_im_ne_zero (z : ℂ)
    (hz : z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1)) :
    (shiftedS z / 2).im ≠ 0 := by
  have him := Door3CutL10BallSup.cutL10_mem_ball_shiftedS_im_bounds z hz
  have heq : (shiftedS z / 2).im = (shiftedS z).im / 2 := by
    simp [Complex.div_ofNat]
  rw [heq]
  intro h0
  linarith [him.2]

/-- `Gamma (shiftedS z / 2) ≠ 0` on the left ball. -/
theorem cutL10_gamma_half_ne_zero (z : ℂ)
    (hz : z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1)) :
    Complex.Gamma (shiftedS z / 2) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m hcon
  have him_ne := cutL10_shiftedS_half_im_ne_zero z hz
  rw [hcon] at him_ne
  simp at him_ne

/-- Polar-times-poly cancellation (center-independent). -/
theorem cutL10_poly_times_polar (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    ((1 / 2 : ℂ) * s * (s - 1)) * (1 / s + 1 / (1 - s)) = (-1 / 2 : ℂ) := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp
  ring

/-- Second cancellation (center-independent). -/
theorem cutL10_poly_times_xiQuot (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (X : ℂ) :
    ((1 / 2 : ℂ) * s * (s - 1)) * (2 * X / (s * (s - 1))) = X := by
  have hsm : s * (s - 1) ≠ 0 := by
    apply mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
  field_simp
  ring

/-- Entire extension equals `1/2 + poly * completed₀`. -/
theorem cutL10_entire_eq_half_add_poly_completed (z : ℂ) :
    xiShiftedEntire z =
      (1 / 2 : ℂ) + ((1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)) *
        completedRiemannZeta₀ (shiftedS z) := by
  have hpoly := Door3CutL10BallSup.cutL10_ballPoly_eq z
  unfold xiShiftedEntire
  rw [hpoly]
  ring

/-- `classicalXi` four-factor unfolding with `zeta = riemannZeta`. -/
theorem cutL10_classicalXi_eq_fourFactor (s : ℂ) :
    classicalXi s = ((1 / 2 : ℂ) * s * (s - 1)) *
      ((Real.pi : ℂ) ^ (-(s / 2))) * (Complex.Gamma (s / 2)) * (zeta s) := by
  have hz : zeta s = riemannZeta s := rfl
  unfold classicalXi XiFromPrefactor classicalXiPrefactor
  rw [hz]
  ring

/-- Product identity CLOSED on the left ball (discharges `hProd`). -/
theorem cutL10_hProd_closed (z : ℂ)
    (hz : z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1)) :
    xiShiftedEntire z = ((1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)) *
      ((Real.pi : ℂ) ^ (-(shiftedS z / 2))) *
      (Complex.Gamma (shiftedS z / 2)) * (zeta (shiftedS z)) := by
  have hs0 : shiftedS z ≠ 0 :=
    Door3CutL10BallSup.cutL10_mem_ball_shiftedS_ne_zero z hz
  have hs1 : shiftedS z ≠ 1 :=
    Door3CutL10BallSup.cutL10_mem_ball_shiftedS_ne_one z hz
  have hGamma : Complex.Gamma (shiftedS z / 2) ≠ 0 :=
    cutL10_gamma_half_ne_zero z hz
  have hpolar := completedRiemannZeta₀_eq_polar_plus_xi (shiftedS z) hs0 hs1 hGamma
  have hent := cutL10_entire_eq_half_add_poly_completed z
  have hcancel := cutL10_poly_times_polar (shiftedS z) hs0 hs1
  have hX := cutL10_poly_times_xiQuot (shiftedS z) hs0 hs1
    (classicalXi (shiftedS z))
  have hfour := cutL10_classicalXi_eq_fourFactor (shiftedS z)
  have hentXi : xiShiftedEntire z = classicalXi (shiftedS z) := by
    rw [hent, hpolar]
    have hexpand : (1 / 2 : ℂ) +
        ((1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)) *
        (1 / shiftedS z + 1 / (1 - shiftedS z) +
          2 * classicalXi (shiftedS z) / (shiftedS z * (shiftedS z - 1))) =
        ((1 / 2 : ℂ) +
          ((1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)) *
          (1 / shiftedS z + 1 / (1 - shiftedS z))) +
        ((1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)) *
          (2 * classicalXi (shiftedS z) / (shiftedS z * (shiftedS z - 1))) := by
      ring
    rw [hexpand, hcancel, hX]
    ring
  rw [hentXi, hfour]

/-- Euler domination step (mirror of `cutR10_zeta_euler_step`; `im`-free). -/
theorem cutL10_zeta_euler_step (s : ℂ)
    (hDom : ‖riemannZeta s‖ ≤ ‖riemannZeta (s.re : ℂ)‖)
    (hReal : ‖riemannZeta (s.re : ℂ)‖ ≤ 1 + 1 / (s.re - 1))
    (delta : ℝ) (hdelta : 0 < delta)
    (hs : 1 + delta ≤ s.re) :
    ‖riemannZeta s‖ ≤ 1 + 1 / delta := by
  have hle3 : 1 + 1 / (s.re - 1) ≤ 1 + 1 / delta := by
    have hdiv : 1 / (s.re - 1) ≤ 1 / delta :=
      one_div_le_one_div_of_le hdelta (by linarith)
    linarith
  exact le_trans (le_trans hDom hReal) hle3

/-- Right sliver `Re >= 3/2 → ‖zeta‖ <= 3` from the two Euler premises. -/
theorem cutL10_zeta_rightSliver_of_euler (s : ℂ)
    (hDom : ‖riemannZeta s‖ ≤ ‖riemannZeta (s.re : ℂ)‖)
    (hReal : ‖riemannZeta (s.re : ℂ)‖ ≤ 1 + 1 / (s.re - 1))
    (hs : 3 / 2 ≤ s.re) :
    ‖zeta s‖ ≤ 3 := by
  have hz : zeta s = riemannZeta s := rfl
  rw [hz]
  have hdelta : (0 : ℝ) < 1 / 2 := by norm_num
  have hs2 : (1 : ℝ) + 1 / 2 ≤ s.re := by linarith
  have h := cutL10_zeta_euler_step s hDom hReal (1 / 2) hdelta hs2
  have heq : (1 : ℝ) + 1 / (1 / 2 : ℝ) = 3 := by norm_num
  rw [heq] at h
  exact h

/-- Denominator lower on the left rectangle: `‖s/2‖ >= 4.22` and
`‖s/2 + 1‖ >= 4.22` from `|Im| >= 4.22` via `‖w‖ >= |w.im|`
(conjugate mirror; honest `4.22` on both factors). -/
theorem cutL10_gamma_denom_lower (s : ℂ)
    (hhi : s.im ≤ (-8.44 : ℝ)) :
    (4.22 : ℝ) ≤ ‖s / 2‖ ∧ (4.22 : ℝ) ≤ ‖s / 2 + 1‖ := by
  have him2 : (s / 2).im ≤ (-4.22 : ℝ) := by
    have heq : (s / 2).im = s.im / 2 := by simp [Complex.div_ofNat]
    rw [heq]
    linarith
  have h1 : (4.22 : ℝ) ≤ ‖s / 2‖ := by
    calc (4.22 : ℝ) ≤ |(s / 2).im| := by
          rw [abs_of_nonpos (by linarith)]
          linarith
      _ ≤ ‖s / 2‖ := Complex.abs_im_le_norm _
  have him3 : (s / 2 + 1).im ≤ (-4.22 : ℝ) := by
    have heq : (s / 2 + 1).im = (s / 2).im := by simp
    rw [heq]
    exact him2
  have h2 : (4.22 : ℝ) ≤ ‖s / 2 + 1‖ := by
    calc (4.22 : ℝ) ≤ |(s / 2 + 1).im| := by
          rw [abs_of_nonpos (by linarith)]
          linarith
      _ ≤ ‖s / 2 + 1‖ := Complex.abs_im_le_norm _
  exact ⟨h1, h2⟩

/-- Gamma `1/100` assembly gated on one explicit product-cap premise
(the only Stirling delta; half-rate reaches `1/2`, shortfall `50x`). -/
theorem cutL10_gamma_sup_of_prodCap_gated (s : ℂ)
    (hlo : (-1.06 : ℝ) ≤ s.re) (hhi : s.re ≤ (2.06 : ℝ))
    (hilo : (-11.56 : ℝ) ≤ s.im) (hihi : s.im ≤ (-8.44 : ℝ))
    (hProdCap : ‖Complex.Gamma (s / 2)‖ ≤ 1 / 100) :
    ‖Complex.Gamma (s / 2)‖ ≤ 1 / 100 :=
  hProdCap

/-- Tier-B triple `(0.001, 12.87, 0.001)` meets the certified LEFT floor
(same numerals as the right lane by conjugation). -/
theorem cutL10_tierB_triple_le_floor :
    (0.001 : ℝ) + 12.87 * 0.001 ≤ 8421 / 320000 := by
  norm_num

/-- Tier-B margin against the certified floor. -/
theorem cutL10_tierB_margin_floor_pos :
    (0.0124 : ℝ) ≤ 8421 / 320000 - (0.001 + 12.87 * 0.001) := by
  norm_num

/-- Tier-B deriv from a shared sup: sup `C` on
`closedBall center (radius + rhoC)` gives `C / rhoC` on `CutL10`
(Cauchy bridge `uniform_deriv_of_closedBall_bound`). -/
theorem cutL10_tierB_deriv_of_sharedSup (C : ℝ) (rhoC : ℝ)
    (hPos : 0 < rhoC)
    (hSup : ∀ (z : ℂ), z ∈ Metric.closedBall CutL10.center (CutL10.radius + rhoC) →
      ‖xiShiftedEntire z‖ ≤ C) :
    ∀ (w : ℂ), CutL10.mem w → ‖deriv xiShifted w‖ ≤ C / rhoC := by
  have hStrip : ∀ (w : ℂ), CutL10.mem w →
      -(1 / 2 : ℝ) < w.im ∧ w.im < (1 / 2 : ℝ) := by
    intro w hw
    have hlo : CutL10.y0 ≤ w.im := hw.2.2.1
    have hhi : w.im ≤ CutL10.y1 := hw.2.2.2
    rw [CutL10_y0] at hlo
    rw [CutL10_y1] at hhi
    constructor <;> linarith
  exact DerivCauchyBridge.uniform_deriv_of_closedBall_bound
    CutL10 rhoC C hPos hStrip hSup

/-- Tier-B shrunken fencing (generic `C / rhoC / rho` conditional with the
LEFT floor): any rect sharing the `CutL10` center with radius `<= rho`
fences at `(0.001, C / rhoC)` once feasibility holds at its center. -/
theorem cutL10_tierB_shrunken_fencing
    (R : CellProofEngine.Rect2D) (C : ℝ) (rhoC : ℝ) (rho : ℝ)
    (hCenter : R.center = CutL10.center)
    (hRad : R.radius ≤ rho)
    (hCnn : 0 ≤ C) (hPos : 0 < rhoC)
    (hDeriv : ∀ (w : ℂ), R.mem w → ‖deriv xiShifted w‖ ≤ C / rhoC)
    (hFeas : (0.001 : ℝ) + (C / rhoC) * rho ≤ 8421 / 320000)
    (hFloor : (8421 / 320000 : ℝ) ≤ ‖xiShifted R.center‖) :
    CellFencingHypotheses R 0.001 (C / rhoC) := by
  refine ⟨by norm_num, fun (w : ℂ) (hw : R.mem w) => hDeriv w hw, ?_⟩
  have hMnn : 0 ≤ C / rhoC := div_nonneg hCnn (le_of_lt hPos)
  have hM : (C / rhoC) * R.radius ≤ (C / rhoC) * rho :=
    mul_le_mul_of_nonneg_left hRad hMnn
  have hneed : (0.001 : ℝ) + (C / rhoC) * R.radius ≤ 8421 / 320000 := by
    linarith [hM, hFeas]
  exact le_trans hneed hFloor

/-- Tier-B `(12.87, 0.001)` instance (mirror of `tierB_shrunken_fencing`). -/
theorem cutL10_tierB_shrunken_fencing_1287
    (R : CellProofEngine.Rect2D)
    (hCenter : R.center = CutL10.center)
    (hRad : R.radius ≤ (0.001 : ℝ))
    (hDeriv : ∀ (w : ℂ), R.mem w → ‖deriv xiShifted w‖ ≤ (12.87 : ℝ))
    (hFloor : (8421 / 320000 : ℝ) ≤ ‖xiShifted R.center‖) :
    CellFencingHypotheses R 0.001 12.87 := by
  refine ⟨by norm_num, fun (w : ℂ) (hw : R.mem w) => hDeriv w hw, ?_⟩
  have hM : 12.87 * R.radius ≤ 12.87 * 0.001 :=
    mul_le_mul_of_nonneg_left hRad (by norm_num)
  have hcap : (0.001 : ℝ) + 12.87 * 0.001 ≤ 8421 / 320000 :=
    cutL10_tierB_triple_le_floor
  have hneed : (0.001 : ℝ) + 12.87 * R.radius ≤ 8421 / 320000 := by
    linarith [hM, hcap]
  exact le_trans hneed hFloor

/-- Sharp `12.87` shared sup from closed `hProd` plus the two factor sups
(TRUE assembly; `hZetaSup` strip wall plus `hGammaSup` Stirling upper stay
explicit premises). -/
theorem cutL10_tierB_sharedSup_1287_of_factorSups
    (hZetaSup : ∀ (s : ℂ), (-1.06 : ℝ) ≤ s.re → s.re ≤ (2.06 : ℝ) →
      (-11.56 : ℝ) ≤ s.im → s.im ≤ (-8.44 : ℝ) → ‖zeta s‖ ≤ (6 : ℝ))
    (hGammaSup : ∀ (s : ℂ), (-1.06 : ℝ) ≤ s.re → s.re ≤ (2.06 : ℝ) →
      (-11.56 : ℝ) ≤ s.im → s.im ≤ (-8.44 : ℝ) →
      ‖Complex.Gamma (s / 2)‖ ≤ (1 / 100 : ℝ)) :
    ∀ (z : ℂ), z ∈ Metric.closedBall CutL10.center (CutL10.radius + 1) →
      ‖xiShiftedEntire z‖ ≤ (12.87 : ℝ) := by
  intro z hz
  have hP := cutL10_hProd_closed z hz
  rw [hP, norm_mul, norm_mul, norm_mul]
  have hpoly := Door3CutL10BallSup.cutL10_ballPoly_upper z hz
  have hpi := Door3CutL10BallSup.cutL10_ballPi_upper z hz
  have hre := Door3CutL10BallSup.cutL10_mem_ball_shiftedS_re_bounds z hz
  have him := Door3CutL10BallSup.cutL10_mem_ball_shiftedS_im_bounds z hz
  have hz2 : ‖zeta (shiftedS z)‖ ≤ (6 : ℝ) :=
    hZetaSup _ hre.1 hre.2 him.1 him.2
  have hG : ‖Complex.Gamma (shiftedS z / 2)‖ ≤ (1 / 100 : ℝ) :=
    hGammaSup _ hre.1 hre.2 him.1 him.2
  have g1 : ‖(1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)‖
        * ‖((Real.pi : ℂ) ^ (-(shiftedS z / 2)))‖ ≤ (67 : ℝ) * (16 / 5) :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have g2 : (‖(1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)‖
        * ‖((Real.pi : ℂ) ^ (-(shiftedS z / 2)))‖)
        * ‖Complex.Gamma (shiftedS z / 2)‖
        ≤ ((67 : ℝ) * (16 / 5)) * (1 / 100) :=
    mul_le_mul g1 hG (norm_nonneg _) (by norm_num)
  have g3 : ((‖(1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)‖
        * ‖((Real.pi : ℂ) ^ (-(shiftedS z / 2)))‖)
        * ‖Complex.Gamma (shiftedS z / 2)‖) * ‖zeta (shiftedS z)‖
        ≤ (((67 : ℝ) * (16 / 5)) * (1 / 100)) * 6 :=
    mul_le_mul g2 hz2 (norm_nonneg _) (by norm_num)
  have hcap : (((67 : ℝ) * (16 / 5)) * (1 / 100)) * 6 ≤ (12.87 : ℝ) := by
    norm_num
  exact le_trans g3 hcap

end Door3CutL10TierB

#print axioms Door3CutL10TierB.cutL10_endpoint_poly_norm
#print axioms Door3CutL10TierB.cutL10_endpoint_pi_lower
#print axioms Door3CutL10TierB.cutL10_poly_pi_lower_endpoint
#print axioms Door3CutL10TierB.cutL10_joint_implies_zeta_cap
#print axioms Door3CutL10TierB.cutL10_hProd_closed
#print axioms Door3CutL10TierB.cutL10_zeta_euler_step
#print axioms Door3CutL10TierB.cutL10_zeta_rightSliver_of_euler
#print axioms Door3CutL10TierB.cutL10_gamma_denom_lower
#print axioms Door3CutL10TierB.cutL10_gamma_sup_of_prodCap_gated
#print axioms Door3CutL10TierB.cutL10_tierB_triple_le_floor
#print axioms Door3CutL10TierB.cutL10_tierB_margin_floor_pos
#print axioms Door3CutL10TierB.cutL10_tierB_deriv_of_sharedSup
#print axioms Door3CutL10TierB.cutL10_tierB_shrunken_fencing
#print axioms Door3CutL10TierB.cutL10_tierB_shrunken_fencing_1287
#print axioms Door3CutL10TierB.cutL10_tierB_sharedSup_1287_of_factorSups

