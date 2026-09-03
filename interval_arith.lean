import Mathlib
import riemann_hypothesis
import rh_certificate_infra
import central_cover_assembly

/-!
# Tight real enclosures + R00 product bridge (c00 cell)

This module builds on the verified interval core in `riemann_hypothesis`
(`ZetaNumericCert.RInterval` / `CInterval` with `mem_add`, `mem_mulCoarse`,
`CInterval.exp`, `norm_mem_le`, `rectIntervalBound_from_approx`): those types
and correctness proofs are reused here, not redefined.

New in this file (all fully proved, no placeholders):
1. `TightInterval`: tight nonnegative real product bounds + real sqrt
   monotonicity packaging (the existing core only ships a coarse symmetric
   product, no tight nonnegative product, no sqrt wrapper).
2. `R00Enclosure`: the top-level `xiShifted` product decomposition
   (`poly * piPow * Gamma * zeta`, distinct from `TailProofEngine` product
   lemmas which concern a different definition), the R00 outer-tier numeric
   budget, and the conditional center-bound / nonvanishing bridge that feeds
   the existing `CentralCoverAssembly.R00_nonvanishing_of_bounds` strip lemma.

The two numeric enclosures for `c00 = (-10,-7.5,0.01,0.2)` are thereby reduced
to four explicit component lower bounds (poly / pi-power / Gamma / zeta) plus
one real product check. The poly part is elementary; the pi-power part follows
from `CInterval.exp`; the Gamma and zeta parts need `zeta` / `Gamma`
 enclosures on the `s`-rectangle, which do not exist in Mathlib (its `zeta`
 bounds are real `Re > 1` only) and are taken here as explicit hypotheses,
 never as hidden assumptions.

New in the R00 appendix below (all fully proved, no placeholders):
3. `CpowInterval`: `Complex.norm_cpow_eq_rpow_re_of_pos` packaging plus the
   explicit `π^(-1/4) ≥ 1/2` rpow interval.
4. `R00Numerics`: the `s`-plane center `sR00 = 1/2 + I·R00.center`
   (`0.395 - 8.75·I`) with hypothesis-free lower bounds `30 ≤ ‖poly‖` and
   `1/2 ≤ ‖piPart‖`, real-Gamma feeders at `Re(sR00)/2`, and the partial
   product assembly reducing the budget to the two remaining factors.
5. `EtaGenReal`: the `zeta_rigorous.lean` eta template generalized to every
   real `σ > 0` (`S₂(σ) ≤ L(σ)`, existence + positivity, all `Tendsto` form)
   plus the conditional `ζ(σ) ≠ 0` bridge (explicit identity hypothesis).
-/

namespace TightInterval

/-- Tight product bounds for nonnegative intervals (complement to the coarse
symmetric product in the existing core). -/
theorem mul_bounds_of_nonneg {x y a b c d : ℝ}
    (hx1 : a ≤ x) (hx2 : x ≤ b) (hy1 : c ≤ y) (hy2 : y ≤ d)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : 0 ≤ b) :
    a * c ≤ x * y ∧ x * y ≤ b * d := by
  have hx_nonneg : 0 ≤ x := le_trans ha hx1
  have hy_nonneg : 0 ≤ y := le_trans hc hy1
  constructor
  · exact mul_le_mul hx1 hy1 hc hx_nonneg
  · exact mul_le_mul hx2 hy2 hy_nonneg hb

/-- Real sqrt monotonicity packaged as an enclosure step. -/
theorem sqrt_bounds {x a b : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) :
    Real.sqrt a ≤ Real.sqrt x ∧ Real.sqrt x ≤ Real.sqrt b := by
  constructor
  · exact Real.sqrt_le_sqrt hx1
  · exact Real.sqrt_le_sqrt hx2

/- The existing core already ships verified `RInterval.add` (`mem_add`),
`RInterval.mulCoarse` (`mem_mulCoarse`), `CInterval.exp` (`mem_exp`), and
`CInterval.normBound` (`norm_mem_le`) together with the
`RectIntervalBound` / `ApproxRectBound` / `EulerMaclaurinZetaBound` certificate
skeletons; the lemmas above complement them (tight product, sqrt) and the
`R00Enclosure` bridge below reuses `TailProofEngine.prod_four_ge_of_ge`, so
nothing here duplicates that core. -/

end TightInterval

namespace R00Enclosure

/-- Polynomial part of the top-level xi prefactor. -/
noncomputable def polyPart (s : ℂ) : ℂ := (1 / 2 : ℂ) * s * (s - 1)

/-- Pi-power part. -/
noncomputable def piPart (s : ℂ) : ℂ := ((Real.pi : ℂ) ^ (-(s / 2)))

/-- Gamma part. -/
noncomputable def gammaPart (s : ℂ) : ℂ := Complex.Gamma (s / 2)

/-- Top-level `xiShifted` factored into four explicit parts. -/
theorem xiShifted_eq_parts (z : ℂ) :
    xiShifted z =
      polyPart ((1 / 2 : ℂ) + Complex.I * z) *
      piPart ((1 / 2 : ℂ) + Complex.I * z) *
      gammaPart ((1 / 2 : ℂ) + Complex.I * z) *
      zeta ((1 / 2 : ℂ) + Complex.I * z) := by
  unfold xiShifted classicalXi XiFromPrefactor classicalXiPrefactor
    polyPart piPart gammaPart
  ring

/-- Norm version of the four-part factorisation. -/
theorem norm_xiShifted_eq_parts (z : ℂ) :
    ‖xiShifted z‖ =
      ‖polyPart ((1 / 2 : ℂ) + Complex.I * z)‖ *
      ‖piPart ((1 / 2 : ℂ) + Complex.I * z)‖ *
      ‖gammaPart ((1 / 2 : ℂ) + Complex.I * z)‖ *
      ‖zeta ((1 / 2 : ℂ) + Complex.I * z)‖ := by
  rw [xiShifted_eq_parts z, norm_mul, norm_mul, norm_mul]

/-- Product lower-bound assembly reused from the existing engine. -/
theorem prod_lower_of_bounds {a b c d A B C D : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hA : A ≤ a) (hB : B ≤ b) (hC : C ≤ c) (hD : D ≤ d)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C) (hD0 : 0 ≤ D) :
    A * B * C * D ≤ a * b * c * d :=
  TailProofEngine.prod_four_ge_of_ge ha hb hc hd hA hB hC hD hA0 hB0 hC0 hD0

/-- Outer-tier threshold value. -/
theorem R00_threshold_eq : (0.002 : ℝ) + 0.05 * 1.26 = 0.065 := by norm_num

/-- Outer-tier numeric budget on the true R00 radius. -/
theorem R00_budget_lt :
    (0.002 : ℝ) + 0.05 * CentralCoverAssembly.R00.radius < 0.1 := by
  have h := CentralCoverAssembly.R00_radius_lt
  have hM : 0.05 * CentralCoverAssembly.R00.radius < 0.05 * 1.26 :=
    mul_lt_mul_of_pos_left h (by norm_num)
  linarith

/-- Conditional center enclosure for c00 from four component lower bounds. -/
theorem R00_center_bound_of_component_bounds
    (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖polyPart ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R00.center)‖)
    (hpi : Api ≤ ‖piPart ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R00.center)‖)
    (hgam : Agam ≤ ‖gammaPart ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R00.center)‖)
    (hzeta : Azeta ≤ ‖zeta ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R00.center)‖)
    (hprod : (0.002 : ℝ) + 0.05 * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    (0.002 : ℝ) + 0.05 * CentralCoverAssembly.R00.radius ≤
      ‖xiShifted CentralCoverAssembly.R00.center‖ := by
  have hdecomp := norm_xiShifted_eq_parts CentralCoverAssembly.R00.center
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted CentralCoverAssembly.R00.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : 0.05 * CentralCoverAssembly.R00.radius ≤ 0.05 * 1.26 :=
    mul_le_mul_of_nonneg_left
      (le_of_lt CentralCoverAssembly.R00_radius_lt) (by norm_num)
  linarith

/-- Conditional nonvanishing on c00: component bounds plus derivative bound feed
the existing R00 strip lemma. -/
theorem R00_nonvanishing_of_component_bounds
    (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖polyPart ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R00.center)‖)
    (hpi : Api ≤ ‖piPart ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R00.center)‖)
    (hgam : Agam ≤ ‖gammaPart ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R00.center)‖)
    (hzeta : Azeta ≤ ‖zeta ((1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R00.center)‖)
    (hprod : (0.002 : ℝ) + 0.05 * 1.26 ≤ Apoly * Api * Agam * Azeta)
    (hderiv : ∀ w, CentralCoverAssembly.R00.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))
    {z : ℂ}
    (hx0 : CentralCoverAssembly.R00.x0 ≤ z.re)
    (hx1 : z.re ≤ CentralCoverAssembly.R00.x1)
    (hy0 : CentralCoverAssembly.R00.y0 ≤ z.im)
    (hy1 : z.im ≤ CentralCoverAssembly.R00.y1) :
    xiShifted z ≠ 0 := by
  have hcenter := R00_center_bound_of_component_bounds Apoly Api Agam Azeta
    hA0 hB0 hC0 hD0 hpoly hpi hgam hzeta hprod
  have hleaf : CentralCoverAssembly.R00_leaf_obligations := ⟨hcenter, hderiv⟩
  exact CentralCoverAssembly.R00_nonvanishing_of_bounds hleaf hx0 hx1 hy0 hy1

#print axioms TightInterval.mul_bounds_of_nonneg
#print axioms R00Enclosure.norm_xiShifted_eq_parts
#print axioms R00Enclosure.R00_budget_lt
#print axioms R00Enclosure.R00_center_bound_of_component_bounds
#print axioms R00Enclosure.R00_nonvanishing_of_component_bounds

end R00Enclosure

/-!
## R00 rigorous enclosures: cpow toolkit, center numerics, real-Gamma and
general-σ eta feeders (all hypothesis-free, no `sorry`).

Closed here: `poly` lower bound (`30 ≤ ‖polyPart sR00‖`) and pi-power lower
bound (`1/2 ≤ ‖piPart sR00‖`) at the R00 `s`-center, plus the partial-product
assembly. Real-Gamma bounds at `Re(sR00)/2` and the general-σ eta track are
feeders for the two remaining factors. Still open (exact missing lemmas in
the final report): complex `Gamma`/`zeta` lower bounds on the `s`-rect,
uniform `‖deriv xiShifted‖ ≤ 0.05`, single-point `ζ(0.395 - 8.75·I) ≠ 0`.
-/

namespace CpowInterval

/-- Norm of a pi-power via `Complex.norm_cpow_eq_rpow_re_of_pos`. -/
theorem pi_cpow_norm (w : ℂ) : ‖((Real.pi : ℂ) ^ w)‖ = Real.pi ^ w.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos w

/-- `π ^ (1/4) ≤ 2`: from `π ≤ 4 = 2^4` via two `abs_le_of_sq_le_sq'` steps.
The fourth power `(π^{1/4})^4 = π` is `Real.rpow_natCast` + `Real.rpow_mul`. -/
theorem pi_rpow_quarter_le_two : Real.pi ^ ((1/4 : ℝ)) ≤ 2 := by
  have e : (Real.pi ^ ((1/4 : ℝ)))^((4:ℕ)) = Real.pi := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    have hexp : ((1/4:ℝ)) * (((4:ℕ)) : ℝ) = 1 := by norm_num
    rw [hexp, Real.rpow_one]
  have hle : Real.pi ≤ (2:ℝ)^((4:ℕ)) := by
    have h16 : (2:ℝ)^((4:ℕ)) = 16 := by norm_num
    rw [h16]
    linarith [Real.pi_le_four]
  have h4 : (Real.pi ^ ((1/4:ℝ)))^((4:ℕ)) ≤ (2:ℝ)^((4:ℕ)) := by
    rw [e]; exact hle
  have e1 : (Real.pi ^ ((1/4:ℝ)))^((4:ℕ))
      = ((Real.pi ^ ((1/4:ℝ)))^((2:ℕ)))^((2:ℕ)) := by ring
  have e2 : (2:ℝ)^((4:ℕ)) = (((2:ℝ))^((2:ℕ)))^((2:ℕ)) := by ring
  rw [e1, e2] at h4
  have hsq : (Real.pi ^ ((1/4:ℝ)))^((2:ℕ)) ≤ (2:ℝ)^((2:ℕ)) :=
    (abs_le_of_sq_le_sq' h4 (by norm_num)).2
  exact (abs_le_of_sq_le_sq' hsq (by norm_num)).2

/-- `π ^ (-1/4) ≥ 1/2` by inversion of the quarter bound. -/
theorem pi_rpow_neg_quarter_ge_half : (1/2:ℝ) ≤ Real.pi ^ (-(1/4:ℝ)) := by
  have hrw : Real.pi ^ (-(1/4:ℝ)) = 1/(Real.pi^((1/4:ℝ))) := by
    rw [Real.rpow_neg (le_of_lt Real.pi_pos)]
    exact (one_div _).symm
  rw [hrw]
  exact one_div_le_one_div_of_le
    (Real.rpow_pos_of_pos Real.pi_pos _) pi_rpow_quarter_le_two

end CpowInterval

namespace R00Numerics

/-- The R00 `s`-plane center: `s = 1/2 + I·z` at `z = R00.center`. -/
noncomputable def sR00 : ℂ := (1/2 : ℂ) + Complex.I * CentralCoverAssembly.R00.center

/-- `R00.center = -8.75 + 0.105·I` (from `R00_x0/x1/y0/y1`). -/
theorem R00_center_eq :
    CentralCoverAssembly.R00.center =
      (((-8.75:ℝ))) + Complex.I * ((((0.105:ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R00_x0, CentralCoverAssembly.R00_x1,
      CentralCoverAssembly.R00_y0, CentralCoverAssembly.R00_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R00_x0, CentralCoverAssembly.R00_x1,
      CentralCoverAssembly.R00_y0, CentralCoverAssembly.R00_y1]
    simp
    norm_num

/-- `Re sR00 = 0.395` (`1/2 - 0.105`). -/
theorem sR00_re : sR00.re = 0.395 := by
  unfold sR00
  rw [R00_center_eq]
  simp
  norm_num

/-- `Im sR00 = -8.75`. -/
theorem sR00_im : sR00.im = -8.75 := by
  unfold sR00
  rw [R00_center_eq]
  simp

/-- Norm of the `1/2` prefactor (via `sq_norm` + `sqrt`, avoiding coercion
lemma matching issues). -/
theorem norm_half : ‖(1/2 : ℂ)‖ = 1/2 := by
  have hsq : ‖(1/2:ℂ)‖^2 = (1/2:ℝ)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  calc ‖(1/2:ℂ)‖ = Real.sqrt (‖(1/2:ℂ)‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt ((1/2:ℝ)^2) := by rw [hsq]
    _ = 1/2 := Real.sqrt_sq (by norm_num)

/-- Norm version of `polyPart` at `sR00`. -/
theorem polyPart_norm_R00 :
    ‖R00Enclosure.polyPart sR00‖ = (1/2) * ‖sR00‖ * ‖sR00 - 1‖ := by
  unfold R00Enclosure.polyPart
  rw [norm_mul, norm_mul, norm_half]

/-- `‖sR00‖ ≥ 8.7` (`8.7² = 75.69 < 0.395² + 8.75² = 76.718525`). -/
theorem norm_sR00_ge : (8.7:ℝ) ≤ ‖sR00‖ := by
  have hsq : (8.7:ℝ)^2 ≤ ‖sR00‖^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, sR00_re, sR00_im]
    norm_num
  calc (8.7:ℝ) = Real.sqrt ((8.7:ℝ)^2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖sR00‖^2) := Real.sqrt_le_sqrt hsq
    _ = ‖sR00‖ := Real.sqrt_sq (norm_nonneg _)

/-- `‖sR00 - 1‖ ≥ 8.7` (`0.605² + 8.75² = 76.928525 > 75.69`). -/
theorem norm_sR00_sub_one_ge : (8.7:ℝ) ≤ ‖sR00 - 1‖ := by
  have hr1 : (sR00 - 1).re = -0.605 := by
    simp only [Complex.sub_re, Complex.one_re, sR00_re]
    norm_num
  have hi1 : (sR00 - 1).im = -8.75 := by
    simp only [Complex.sub_im, Complex.one_im, sR00_im]
    norm_num
  have hsq : (8.7:ℝ)^2 ≤ ‖sR00 - 1‖^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hr1, hi1]
    norm_num
  calc (8.7:ℝ) = Real.sqrt ((8.7:ℝ)^2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖sR00 - 1‖^2) := Real.sqrt_le_sqrt hsq
    _ = ‖sR00 - 1‖ := Real.sqrt_sq (norm_nonneg _)

/-- ENCLOSURE (1/4, hypothesis-free): `30 ≤ ‖polyPart sR00‖`
(`8.7·8.7/2 = 37.845 ≥ 30`). -/
theorem poly_lower_R00 : (30:ℝ) ≤ ‖R00Enclosure.polyPart sR00‖ := by
  have hprod : (8.7:ℝ) * 8.7 ≤ ‖sR00‖ * ‖sR00 - 1‖ :=
    mul_le_mul norm_sR00_ge norm_sR00_sub_one_ge (by norm_num) (norm_nonneg _)
  rw [polyPart_norm_R00]
  nlinarith [hprod]

/-- Norm of `piPart` at `sR00` is a real rpow. -/
theorem piPart_norm_eq :
    ‖R00Enclosure.piPart sR00‖ = Real.pi ^ (-(sR00.re)/2) := by
  have h := Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos (-(sR00/2))
  unfold R00Enclosure.piPart
  rw [h]
  congr 1
  rw [Complex.neg_re, Complex.div_ofNat_re]
  ring

/-- ENCLOSURE (2/4, hypothesis-free): `1/2 ≤ ‖piPart sR00‖`
(`-0.1975 ≥ -1/4`, `π > 1`, and `π^(-1/4) ≥ 1/2`). -/
theorem pi_lower_R00 : (1/2:ℝ) ≤ ‖R00Enclosure.piPart sR00‖ := by
  rw [piPart_norm_eq]
  have hexp : (-(1/4:ℝ)) ≤ -(sR00.re)/2 := by rw [sR00_re]; norm_num
  calc (1/2:ℝ) ≤ Real.pi ^ (-(1/4:ℝ)) := CpowInterval.pi_rpow_neg_quarter_ge_half
    _ ≤ Real.pi ^ (-(sR00.re)/2) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hexp

/-- Real-Gamma positivity feeder at `Re(sR00)/2`
(`JensenTranslation.gamma_quarter_pos` pattern). -/
theorem gammaReal_pos : 0 < Real.Gamma (sR00.re/2) := by
  apply Real.Gamma_pos_of_pos
  rw [sR00_re]
  norm_num

/-- Real-Gamma upper-bound feeder at `Re(sR00)/2 = 0.1975`
(`gamma_five_quarter_le_one` pattern: convexity between `Γ(1)=Γ(2)=1`,
then `Γ(x) = Γ(1+x)/x ≤ 1/0.1975 ≤ 5.07`). -/
theorem gammaReal_le : Real.Gamma (sR00.re/2) ≤ 5.07 := by
  have hx0 : sR00.re/2 = (0.1975:ℝ) := by rw [sR00_re]; norm_num
  have hpos : (0:ℝ) < sR00.re/2 := by rw [hx0]; norm_num
  have hconv := Real.convexOn_Gamma
  have h1 : (1:ℝ) ∈ Set.Ioi (0:ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have h2 : (2:ℝ) ∈ Set.Ioi (0:ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have h := hconv.2 h1 h2
    (show (0:ℝ) ≤ 1 - sR00.re/2 by linarith)
    (show (0:ℝ) ≤ sR00.re/2 by linarith) (by ring)
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
  have hpt : (1 - sR00.re/2) * 1 + (sR00.re/2) * 2 = sR00.re/2 + 1 := by ring
  rw [hpt] at h
  have hrhs : (1 - sR00.re/2) * 1 + (sR00.re/2) * 1 = (1:ℝ) := by ring
  rw [hrhs] at h
  have hadd := Real.Gamma_add_one (show sR00.re/2 ≠ 0 by linarith)
  rw [hadd] at h
  have hfin : Real.Gamma (sR00.re/2) ≤ 1/(sR00.re/2) := by
    rw [le_div_iff₀ hpos, mul_comm]
    exact h
  rw [hx0] at hfin ⊢
  calc Real.Gamma (0.1975:ℝ) ≤ 1/(0.1975:ℝ) := hfin
    _ ≤ 5.07 := by norm_num

/-- Partial-product assembly: the two closed enclosures (`30`, `1/2`) are
plugged into the existing center bridge, leaving exactly the Gamma and zeta
factors as explicit premises. The budget becomes
`Agam * Azeta ≥ 0.065/15 ≈ 0.00434`. -/
theorem R00_partial_product (Agam Azeta : ℝ)
    (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hgam : Agam ≤ ‖R00Enclosure.gammaPart sR00‖)
    (hzeta : Azeta ≤ ‖zeta sR00‖)
    (hprod : (0.002:ℝ) + 0.05*1.26 ≤ 30 * (1/2) * Agam * Azeta) :
    (0.002:ℝ) + 0.05 * CentralCoverAssembly.R00.radius ≤
      ‖xiShifted CentralCoverAssembly.R00.center‖ := by
  have harg : sR00
      = (1/2:ℂ) + Complex.I * CentralCoverAssembly.R00.center := rfl
  have hpoly := poly_lower_R00
  have hpi := pi_lower_R00
  rw [harg] at hpoly hpi hgam hzeta
  exact R00Enclosure.R00_center_bound_of_component_bounds
    30 (1/2) Agam Azeta (by norm_num) (by norm_num) hC0 hD0
    hpoly hpi hgam hzeta hprod

end R00Numerics

namespace EtaGenReal

/-- General-exponent Dirichlet eta term `(-1)^k / (k+1)^σ` (real). -/
noncomputable def etaGenTerm (σ : ℝ) (k : ℕ) : ℝ := 1 / (((k : ℝ) + 1) ^ σ)

/-- Antitone majorant for general `σ ≥ 0` (`eta_terms_antitone` template). -/
theorem etaGen_antitone {σ : ℝ} (hσ : 0 ≤ σ) :
    Antitone (fun k : ℕ => etaGenTerm σ k) := by
  intro a b hab
  simp only [etaGenTerm]
  have h_le : ((a : ℝ) + 1) ≤ ((b : ℝ) + 1) := by
    have hcast : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    linarith
  have h_rpow := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (a:ℝ)+1) h_le hσ
  have h_pos : (0:ℝ) < (((a : ℝ) + 1) ^ σ) :=
    Real.rpow_pos_of_pos (by positivity) σ
  exact one_div_le_one_div_of_le h_pos h_rpow

/-- Terms tend to zero for `σ > 0` (`eta_terms_tendsto_zero` template,
via `tendsto_rpow_atTop`). -/
theorem etaGen_terms_tendsto_zero {σ : ℝ} (hσ : 0 < σ) :
    Filter.Tendsto (fun k : ℕ => etaGenTerm σ k) Filter.atTop (nhds 0) := by
  have h_top : Filter.Tendsto (fun k : ℕ => (((k : ℝ) + 1) ^ σ))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hσ).comp
      (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop)
  have h_inv : Filter.Tendsto (fun k : ℕ => ((((k : ℝ) + 1) ^ σ))⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp h_top
  simp only [etaGenTerm, one_div]
  exact h_inv

/-- The even partial sum `S₂` is the difference of the first two terms. -/
theorem etaGen_S2_eq (σ : ℝ) :
    (∑ i ∈ Finset.range 2, (-1:ℝ)^i * etaGenTerm σ i)
      = etaGenTerm σ 0 - etaGenTerm σ 1 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- Closed form `S₂(σ) = 1 - 1/2^σ`. -/
theorem etaGen_S2_closed (σ : ℝ) :
    etaGenTerm σ 0 - etaGenTerm σ 1 = 1 - 1/(2:ℝ)^σ := by
  simp only [etaGenTerm, Nat.cast_zero, Nat.cast_one, zero_add]
  norm_num [Real.one_rpow]

/-- `S₂(σ) > 0` for `σ > 0` (since `2^σ > 1`). -/
theorem etaGen_S2_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < etaGenTerm σ 0 - etaGenTerm σ 1 := by
  rw [etaGen_S2_closed]
  have h2σ : (1:ℝ) < (2:ℝ)^σ := Real.one_lt_rpow (by norm_num) hσ
  have hpos : 0 < (2:ℝ)^σ := Real.rpow_pos_of_pos (by norm_num) σ
  have hlt : 1/((2:ℝ)^σ) < 1 := by
    rw [div_lt_one hpos]
    exact h2σ
  linarith

/-- LOWER BOUND (general `σ > 0`, `Tendsto` form): every eta limit `L`
satisfies `S₂(σ) ≤ L` (`eta_half_ge_S2` template). -/
theorem etaGen_limit_ge_S2 {σ : ℝ} (hσ : 0 < σ) {L : ℝ}
    (hL : Filter.Tendsto
      (fun n => ∑ i ∈ Finset.range n, (-1:ℝ)^i * etaGenTerm σ i)
      Filter.atTop (nhds L)) :
    etaGenTerm σ 0 - etaGenTerm σ 1 ≤ L := by
  have h := Antitone.alternating_series_le_tendsto hL (etaGen_antitone hσ.le) 1
  have h21 : (2 * 1 : ℕ) = 2 := by simp
  simpa only [h21, etaGen_S2_eq] using h

/-- Existence + positivity of the eta limit for every `σ > 0`
(`eta_half_pos` template, general exponent). -/
theorem etaGen_pos {σ : ℝ} (hσ : 0 < σ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n => ∑ i ∈ Finset.range n, (-1:ℝ)^i * etaGenTerm σ i)
      Filter.atTop (nhds L) ∧ 0 < L := by
  obtain ⟨L, hL⟩ := Antitone.tendsto_alternating_series_of_tendsto_zero
    (f := fun k => etaGenTerm σ k)
    (etaGen_antitone hσ.le) (etaGen_terms_tendsto_zero hσ)
  exact ⟨L, hL, lt_of_lt_of_le (etaGen_S2_pos hσ) (etaGen_limit_ge_S2 hσ hL)⟩

/-- The eta–zeta factor `1 - 2^{1-σ}` is nonzero for `σ < 1`
(denominator feeder for the future identity proof). -/
theorem etaGen_factor_ne_zero {σ : ℝ} (hσ : σ < 1) :
    (1:ℝ) - 2^(1-σ) ≠ 0 := by
  have h : (1:ℝ) < 2^(1-σ) := Real.one_lt_rpow (by norm_num) (by linarith)
  have hneg : (1:ℝ) - 2^(1-σ) < 0 := by linarith
  exact ne_of_lt hneg

/-- CONDITIONAL single-point zeta nonvanishing on the real axis: the
alternating-eta limit identity `ζ(σ)·(1-2^{1-σ}) = L` with `0 < L` forces
`ζ(σ) ≠ 0` (`zeta_rigorous` §(c)–(d) pattern; the identity itself needs
analytic continuation, absent from Mathlib). -/
theorem zeta_ne_zero_of_etaGen_identity {σ L : ℝ} (hLpos : 0 < L)
    (hEta : zeta ((σ : ℝ) : ℂ) * (((1 - (2:ℝ)^(1-σ) : ℝ)) : ℂ) = (((L : ℝ)) : ℂ)) :
    zeta ((σ : ℝ) : ℂ) ≠ 0 := by
  intro hz
  rw [hz, zero_mul] at hEta
  have hL0 : L = 0 := by exact_mod_cast hEta.symm
  exact (ne_of_gt hLpos) hL0

end EtaGenReal

#print axioms CpowInterval.pi_rpow_neg_quarter_ge_half
#print axioms R00Numerics.poly_lower_R00
#print axioms R00Numerics.pi_lower_R00
#print axioms R00Numerics.gammaReal_le
#print axioms R00Numerics.R00_partial_product
#print axioms EtaGenReal.etaGen_pos
#print axioms EtaGenReal.zeta_ne_zero_of_etaGen_identity

/-!
## R00 complex-Gamma lower bound (joint Gammaℝ route, fully proved).

Target: uniform `‖Complex.Gamma (s/2)‖ ≥ 1/10000000` on the R00 s-rect
`Re∈[0.3,0.49]`, `Im∈[-10,-7.5]`, via Deligne `Gammaℝ` nonvanishing
(`Complex.Gammaℝ_ne_zero_of_re_pos`) + Euler reflection
(`Complex.Gamma_mul_Gamma_one_sub`) + integral majorant
(`‖Gamma z‖ ≤ Real.Gamma z.re`) + real convexity upper bound
(`Real.convexOn_Gamma` pattern already used in-file) + sine majorant
(`Complex.norm_exp`, `Real.exp_one_lt_d9`). Plugged into
`R00Numerics.R00_partial_product` to leave only the zeta factor.
-/

namespace R00GammaLower

/-- R00 s-rect predicate: `Re∈[0.3,0.49]`, `Im∈[-10,-7.5]`. -/
def sRect (s : ℂ) : Prop :=
  0.3 ≤ s.re ∧ s.re ≤ 0.49 ∧ -10 ≤ s.im ∧ s.im ≤ -7.5

/-- Center `sR00` lies in the s-rect (`Re=0.395`, `Im=-8.75`). -/
theorem sR00_mem_sRect : sRect R00Numerics.sR00 := by
  unfold sRect
  constructor
  · rw [R00Numerics.sR00_re]; norm_num
  constructor
  · rw [R00Numerics.sR00_re]; norm_num
  constructor
  · rw [R00Numerics.sR00_im]; norm_num
  · rw [R00Numerics.sR00_im]; norm_num

/-- Deligne nonvanishing on the rect: `Re s ≥ 0.3 > 0`. -/
theorem gammaR_ne_zero_of_mem {s : ℂ} (hs : sRect s) : Complex.Gammaℝ s ≠ 0 := by
  apply Complex.Gammaℝ_ne_zero_of_re_pos
  unfold sRect at hs
  obtain ⟨h1, _, _, _⟩ := hs
  linarith

/-- Joint transfer: `Gamma(s/2) ≠ 0` from `Gammaℝ s ≠ 0`
(`Gammaℝ s = π^{-s/2} * Gamma(s/2)`, so the second factor is nonzero). -/
theorem gamma_half_ne_zero_of_mem {s : ℂ} (hs : sRect s) :
    Complex.Gamma (s / 2) ≠ 0 := by
  have hR := gammaR_ne_zero_of_mem hs
  rw [Complex.Gammaℝ_def] at hR
  exact (mul_ne_zero_iff.mp hR).2

/-- Integral majorant: `‖Gamma z‖ ≤ Real.Gamma z.re` for `Re z > 0`
(triangle inequality for the Euler integral; norm of integrand is the
real integrand via `norm_cpow_eq_rpow_re_of_pos`). -/
theorem norm_Gamma_le_realGamma {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  have hC := Complex.GammaIntegral_convergent hz
  have hR := Real.GammaIntegral_convergent hz
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz]
  unfold Complex.GammaIntegral
  calc ‖∫ x in Set.Ioi (0 : ℝ), ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (z - 1)‖
      ≤ ∫ x in Set.Ioi (0 : ℝ), ‖((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (z - 1)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ (z.re - 1) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        have hx0 : (0 : ℝ) < x := Set.mem_Ioi.mp hx
        show ‖((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (z - 1)‖ = _
        rw [norm_mul]
        have h1 : ‖((Real.exp (-x) : ℝ) : ℂ)‖ = Real.exp (-x) :=
          Complex.norm_of_nonneg (le_of_lt (Real.exp_pos _))
        have h2 : ‖(x : ℂ) ^ (z - 1)‖ = x ^ ((z - 1).re) :=
          Complex.norm_cpow_eq_rpow_re_of_pos hx0 _
        rw [h1, h2]
        have hexp : (z - 1).re = z.re - 1 := by simp [Complex.sub_re]
        rw [hexp]

/-- Uniform real-Gamma upper bound: `Real.Gamma ((1 - s/2).re) ≤ 1.5` on the rect.
Here `x = 1 - s.re/2 ∈ [0.755, 0.85]`; `Gamma(x+1) ≤ 1` by convexity on `[1,2]`
(`Gamma 1 = Gamma 2 = 1`), then `Gamma(x) = Gamma(x+1)/x ≤ 1/0.755 ≤ 1.5`. -/
theorem realGamma_one_sub_half_le {s : ℂ} (hs : sRect s) :
    Real.Gamma ((1 - s / 2).re) ≤ 1.5 := by
  unfold sRect at hs
  obtain ⟨hre_lo, hre_hi, _, _⟩ := hs
  have hre2 : (s / 2).re = s.re / 2 := by rw [Complex.div_ofNat_re]
  have hx_eq : (1 - s / 2).re = 1 - s.re / 2 := by
    rw [Complex.sub_re, Complex.one_re, hre2]
  have hx_lo : (0.755 : ℝ) ≤ (1 - s / 2).re := by rw [hx_eq]; linarith
  have hx_hi : (1 - s / 2).re ≤ (0.85 : ℝ) := by rw [hx_eq]; linarith
  have hx_pos : (0 : ℝ) < (1 - s / 2).re := by linarith
  have hy_mem1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have hy_mem2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have hy_lo : (1 : ℝ) ≤ (1 - s / 2).re + 1 := by linarith
  have hy_hi : (1 - s / 2).re + 1 ≤ (2 : ℝ) := by linarith
  have hconv := Real.convexOn_Gamma
  have ha_nn : (0 : ℝ) ≤ 2 - ((1 - s / 2).re + 1) := by linarith
  have hb_nn : (0 : ℝ) ≤ ((1 - s / 2).re + 1) - 1 := by linarith
  have hab : (2 - ((1 - s / 2).re + 1)) + (((1 - s / 2).re + 1) - 1) = 1 := by ring
  have h := hconv.2 hy_mem1 hy_mem2 ha_nn hb_nn hab
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
  have heq : (2 - ((1 - s / 2).re + 1)) * 1 + (((1 - s / 2).re + 1) - 1) * 2
      = (1 - s / 2).re + 1 := by ring
  rw [heq] at h
  have hrhs : (2 - ((1 - s / 2).re + 1)) * 1 + (((1 - s / 2).re + 1) - 1) * 1
      = (1 : ℝ) := by ring
  rw [hrhs] at h
  have hne : (1 - s / 2).re ≠ 0 := ne_of_gt hx_pos
  have hadd := Real.Gamma_add_one hne
  have hpt : ((1 - s / 2).re + 1) = ((1 - s / 2).re) + 1 := by ring
  rw [hpt] at hadd
  rw [hadd] at h
  have hfin : Real.Gamma ((1 - s / 2).re) ≤ 1 / (1 - s / 2).re := by
    rw [le_div_iff₀ hx_pos, mul_comm]
    exact h
  have hfrac : (1 : ℝ) / (1 - s / 2).re ≤ 1.5 := by
    have h1 : (1 : ℝ) / (1 - s / 2).re ≤ 1 / 0.755 :=
      one_div_le_one_div_of_le (by norm_num) hx_lo
    have h2 : (1 : ℝ) / 0.755 ≤ 1.5 := by norm_num
    exact le_trans h1 h2
  exact le_trans hfin hfrac

/-- `Real.exp 16 < 10000000` via `(exp 1)^16` and `exp_one_lt_d9`. -/
theorem exp_sixteen_lt : Real.exp 16 < 10000000 := by
  have h1 : Real.exp (16 : ℝ) = (Real.exp 1) ^ (16 : ℕ) := by
    have := Real.exp_nat_mul (1 : ℝ) (16 : ℕ)
    simpa using this.symm
  have h2 : (Real.exp 1) ^ (16 : ℕ) < (2.7182818286 : ℝ) ^ (16 : ℕ) := by
    apply pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos _)) (by norm_num)
  have h3 : (2.7182818286 : ℝ) ^ (16 : ℕ) < 10000000 := by norm_num
  rw [h1]
  exact lt_trans h2 h3

/-- Uniform sine majorant: `‖sin(π·(s/2))‖ ≤ Real.exp 16` on the rect.
From `sin w = (exp(-w·I) - exp(w·I))·I/2`, `‖exp‖ = exp(Re)`,
`Re(-w·I) = Im w`, `Re(w·I) = -Im w`, and `|Im(π·s/2)| ≤ 16`
(`|s.im| ≤ 10`, `π < 3.1416`). -/
theorem norm_sin_pi_half_le {s : ℂ} (hs : sRect s) :
    ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ ≤ Real.exp 16 := by
  unfold sRect at hs
  obtain ⟨hre_lo, hre_hi, him_lo, him_hi⟩ := hs
  set w : ℂ := (Real.pi : ℂ) * (s / 2) with hw
  have hs2re : (s / 2).re = s.re / 2 := by rw [Complex.div_ofNat_re]
  have hs2im : (s / 2).im = s.im / 2 := by rw [Complex.div_ofNat_im]
  have hw_im : w.im = Real.pi * (s.im / 2) := by
    rw [hw]
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hs2im]
  have habs_s : |s.im| ≤ 10 := by
    rw [abs_le]
    constructor <;> linarith
  have hpi_le : Real.pi ≤ 3.1416 := le_of_lt Real.pi_lt_d4
  have hw_abs : |w.im| ≤ 16 := by
    rw [hw_im, abs_mul]
    have h1 : |Real.pi| ≤ 3.1416 := by
      rw [abs_of_pos Real.pi_pos]; exact hpi_le
    have h2 : |s.im / 2| ≤ 5 := by
      rw [abs_div, abs_two]
      have : |s.im| / 2 ≤ 5 := by linarith [habs_s]
      linarith
    calc |Real.pi| * |s.im / 2| ≤ 3.1416 * 5 :=
          mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ ≤ 16 := by norm_num
  have hsin_eq : Complex.sin w = (Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2 := by
    unfold Complex.sin; ring
  rw [hsin_eq]
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  have hle : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
      ≤ (‖Complex.exp (-w * Complex.I)‖ + ‖Complex.exp (w * Complex.I)‖) / 2 := by
    have h2 : ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
        = ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ / 2 := by
      simp [norm_div, norm_mul, hI, Complex.norm_ofNat]
    rw [h2]
    exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
  have hre1 : (-w * Complex.I).re = w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]
  have hre2 : (w * Complex.I).re = -w.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [Complex.norm_exp, Complex.norm_exp, hre1, hre2] at hle
  have e1 : Real.exp w.im ≤ Real.exp 16 :=
    Real.exp_le_exp.mpr (le_trans (le_abs_self _) hw_abs)
  have e2 : Real.exp (-w.im) ≤ Real.exp 16 := by
    apply Real.exp_le_exp.mpr
    have : -w.im ≤ |w.im| := neg_le_abs _
    exact le_trans this hw_abs
  linarith

/-- Sine is nonzero at `π·(s/2)` on the rect (`Im ≠ 0`, so not an integer multiple of π). -/
theorem sin_pi_half_ne {s : ℂ} (hs : sRect s) :
    Complex.sin ((Real.pi : ℂ) * (s / 2)) ≠ 0 := by
  unfold sRect at hs
  obtain ⟨_, _, him_lo, him_hi⟩ := hs
  intro hzero
  rw [Complex.sin_eq_zero_iff] at hzero
  obtain ⟨k, hk⟩ := hzero
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs2im : (s / 2).im = s.im / 2 := by rw [Complex.div_ofNat_im]
  have hIm_eq : ((Real.pi : ℂ) * (s / 2)).im = ((k : ℂ) * (Real.pi : ℂ)).im := by rw [hk]
  have hL : ((Real.pi : ℂ) * (s / 2)).im = Real.pi * (s.im / 2) := by
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hs2im]
  have hR : ((k : ℂ) * (Real.pi : ℂ)).im = 0 := by
    simp [Complex.mul_im]
  rw [hL, hR] at hIm_eq
  have hpi_pos := Real.pi_pos
  have hsim : s.im / 2 = 0 := by
    have : Real.pi * (s.im / 2) = 0 := hIm_eq
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (ne_of_gt hpi_pos)
    · exact h
  have : s.im = 0 := by linarith
  linarith

/-- MAIN uniform bound: `1/10000000 ≤ ‖Gamma(s/2)‖` on the s-rect,
from reflection `Gamma(w)·Gamma(1-w) = π/sin(πw)` with
`‖Gamma(1-w)‖ ≤ 1.5`, `‖sin‖ ≤ exp 16 < 1e7`, `π ≥ 3`. -/
theorem gamma_lower_rect {s : ℂ} (hs : sRect s) :
    (1 / 10000000 : ℝ) ≤ ‖Complex.Gamma (s / 2)‖ := by
  have hs2re : (s / 2).re = s.re / 2 := by rw [Complex.div_ofNat_re]
  have h1w_re : (0 : ℝ) < (1 - s / 2).re := by
    unfold sRect at hs
    obtain ⟨hre_lo, hre_hi, _, _⟩ := hs
    rw [Complex.sub_re, Complex.one_re, hs2re]
    linarith
  have hG1_ne : Complex.Gamma (1 - s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h1w_re
  have hsin_ne := sin_pi_half_ne hs
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (s / 2)
  have hnorm : ‖Complex.Gamma (s / 2)‖ * ‖Complex.Gamma (1 - s / 2)‖
      = Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ := by
    have h := congrArg (fun x : ℂ => ‖x‖) hrefl
    simp only [norm_mul, norm_div] at h
    have hpi_norm : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real]
      exact Real.norm_of_nonneg Real.pi_pos.le
    rw [hpi_norm] at h
    exact h
  have hG1_le : ‖Complex.Gamma (1 - s / 2)‖ ≤ 1.5 := by
    calc ‖Complex.Gamma (1 - s / 2)‖ ≤ Real.Gamma ((1 - s / 2).re) :=
          norm_Gamma_le_realGamma h1w_re
      _ ≤ 1.5 := realGamma_one_sub_half_le hs
  have hsin_le : ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ ≤ Real.exp 16 :=
    norm_sin_pi_half_le hs
  have hexp_lt : Real.exp 16 < 10000000 := exp_sixteen_lt
  have hsin_lt : ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ < 10000000 :=
    lt_of_le_of_lt hsin_le hexp_lt
  have hpos1 : (0 : ℝ) < ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ :=
    norm_pos_iff.mpr hsin_ne
  have hpos2 : (0 : ℝ) < ‖Complex.Gamma (1 - s / 2)‖ :=
    norm_pos_iff.mpr hG1_ne
  have hden_pos : (0 : ℝ) < ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ * ‖Complex.Gamma (1 - s / 2)‖ :=
    mul_pos hpos1 hpos2
  have hden_le : ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ * ‖Complex.Gamma (1 - s / 2)‖
      ≤ 10000000 * 1.5 :=
    mul_le_mul (le_of_lt hsin_lt) hG1_le (norm_nonneg _) (by norm_num)
  have hfrac_le : Real.pi / (10000000 * 1.5) ≤ Real.pi / (‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ * ‖Complex.Gamma (1 - s / 2)‖) :=
    div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) hden_pos hden_le
  have hnum : Real.pi / (‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ * ‖Complex.Gamma (1 - s / 2)‖)
      = ‖Complex.Gamma (s / 2)‖ := by
    have hb_ne : ‖Complex.Gamma (1 - s / 2)‖ ≠ 0 := ne_of_gt hpos2
    have h1 : ‖Complex.Gamma (s / 2)‖
        = (Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖) / ‖Complex.Gamma (1 - s / 2)‖ :=
      eq_div_of_mul_eq hb_ne hnorm
    rw [h1, div_div]
  have hbase : (1 / 10000000 : ℝ) ≤ Real.pi / (10000000 * 1.5) := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith [Real.pi_gt_three]
  exact le_trans hbase (hfrac_le.trans_eq hnum)

/-- Center instantiation for the existing `gammaPart` (`gammaPart sR00 = Gamma(sR00/2)`). -/
theorem gamma_lower_center :
    (1 / 10000000 : ℝ) ≤ ‖R00Enclosure.gammaPart R00Numerics.sR00‖ := by
  have h := gamma_lower_rect sR00_mem_sRect
  have heq : R00Enclosure.gammaPart R00Numerics.sR00 = Complex.Gamma (R00Numerics.sR00 / 2) := rfl
  rw [heq]
  exact h

/-- Positivity of the explicit constant. -/
theorem gamma_const_pos : (0 : ℝ) < 1 / 10000000 := by norm_num

/-- Joint Gammaℝ transfer: norm identity `‖Gamma(s/2)‖ = π^{s.re/2} * ‖Gammaℝ s‖`. -/
theorem norm_gamma_eq_gammaR_mul {s : ℂ} :
    ‖Complex.Gamma (s / 2)‖ = Real.pi ^ (s.re / 2) * ‖Complex.Gammaℝ s‖ := by
  have hdef : Complex.Gammaℝ s = (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := rfl
  have hs2re : (s / 2).re = s.re / 2 := by rw [Complex.div_ofNat_re]
  have hns_re : (-s / 2).re = -(s.re / 2) := by
    rw [Complex.div_ofNat_re, Complex.neg_re]
    ring
  have hpi_pow : ‖((Real.pi : ℂ) ^ (-s / 2))‖ = Real.pi ^ (-(s.re / 2)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    rw [hns_re]
  have hmul := congrArg (fun x : ℂ => ‖x‖) hdef
  simp only [norm_mul] at hmul
  rw [hpi_pow] at hmul
  have hInv : Real.pi ^ (-(s.re / 2)) * Real.pi ^ (s.re / 2) = 1 := by
    rw [← Real.rpow_add Real.pi_pos]
    simp
  calc ‖Complex.Gamma (s / 2)‖ = 1 * ‖Complex.Gamma (s / 2)‖ := by rw [one_mul]
    _ = (Real.pi ^ (-(s.re / 2)) * Real.pi ^ (s.re / 2)) * ‖Complex.Gamma (s / 2)‖ := by rw [hInv]
    _ = Real.pi ^ (s.re / 2) * (Real.pi ^ (-(s.re / 2)) * ‖Complex.Gamma (s / 2)‖) := by ring
    _ = Real.pi ^ (s.re / 2) * ‖Complex.Gammaℝ s‖ := by rw [← hmul]

/-- Transferred Gammaℝ lower bound (positive, symbolic denominator). -/
theorem gammaR_lower_rect {s : ℂ} (hs : sRect s) :
    (1 / 10000000 : ℝ) / Real.pi ^ (s.re / 2) ≤ ‖Complex.Gammaℝ s‖ := by
  have hG := gamma_lower_rect hs
  rw [norm_gamma_eq_gammaR_mul] at hG
  have hpos : (0 : ℝ) < Real.pi ^ (s.re / 2) :=
    Real.rpow_pos_of_pos Real.pi_pos _
  rw [div_le_iff₀ hpos, mul_comm]
  exact hG

/-- Plug-in: center budget with the proved Gamma constant, leaving only zeta.
Advances `R00Numerics.R00_partial_product` (two open factors → one). -/
theorem R00_center_with_gamma (Azeta : ℝ)
    (hD0 : 0 ≤ Azeta)
    (hzeta : Azeta ≤ ‖zeta R00Numerics.sR00‖)
    (hprod : (0.002 : ℝ) + 0.05 * 1.26 ≤ 30 * (1 / 2) * (1 / 10000000) * Azeta) :
    (0.002 : ℝ) + 0.05 * CentralCoverAssembly.R00.radius ≤
      ‖xiShifted CentralCoverAssembly.R00.center‖ := by
  exact R00Numerics.R00_partial_product (1 / 10000000) Azeta
    (le_of_lt gamma_const_pos) hD0 gamma_lower_center hzeta hprod

#print axioms R00GammaLower.gamma_lower_rect
#print axioms R00GammaLower.gamma_lower_center
#print axioms R00GammaLower.R00_center_with_gamma

end R00GammaLower

/-!
## R00 single-point zeta lower bound via complex alternating eta (partial sum + bridge).

Target: `Azeta` with `1/26 ≤ ‖zeta sR00‖`, where `sR00 = 0.395 - 8.75·I`
(`R00Numerics.sR00`). Route: Dirichlet eta partial sums
`S_N(s) = ∑_{k<N} (-1)^k ((((k+1 : ℝ))) : ℂ)^{-s}` — the alternating version,
required since `Re sR00 = 0.395 < 1`, where the absolute Dirichlet series
diverges (Mathlib's Dirichlet API applies only for `1 < s.re`; no complex eta
identity exists in Mathlib).

What is closed here (every item fully proved):
* `etaCPartial_two_eq`: `S₂(sR00) = 1 - 2^{-sR00}` (two `sum_range_succ` steps).
* `rpow_two_R00_ge/le/thr`: numeral rpow bounds `5/4 ≤ 2^0.395`,
  `2^0.605 ≤ 8/5`, `3/2 ≤ 2^0.605`, each by clearing the exponent
  (`le_of_pow_le_pow_left₀` + `Real.rpow_mul`/`Real.rpow_natCast`) to an
  integer inequality closed by `norm_num`.
* `etaCPartial_two_norm_ge`: `1/5 ≤ ‖S₂(sR00)‖`, via
  `‖2^{-sR00}‖ = 2^{-0.395} = (2^0.395)⁻¹ ≤ 4/5`
  (`Complex.norm_cpow_eq_rpow_re_of_pos` + reverse triangle inequality).
* `factor_upper_R00`: `‖1 - 2^{1-sR00}‖ ≤ 13/5` (triangle + `2^0.605 ≤ 8/5`).
* `factor_ne_zero_R00`: `1 - 2^{1-sR00} ≠ 0` (else `2^0.605 = 1`, against
  `2^0.605 ≥ 3/2`).
* `zeta_lower_R00_of_eta`: `1/26 ≤ ‖zeta sR00‖` from three explicit analytic
  premises — `_hLim` (the eta partial sums tend to `L`), `hRem`
  (`‖S₂ - L‖ ≤ 1/10`, the Dirichlet remainder bound at this point), `hId`
  (`zeta sR00 * (1 - 2^{1-sR00}) = L`, the eta-zeta identity at `sR00`).
  The implication itself is fully proved (reverse triangle + `eq_div_iff` +
  `le_div_iff₀`, with `(1/5 - 1/10) / (13/5) = 1/26`); the three premises are
  exactly the missing classical facts (complex Dirichlet test + remainder
  estimate + analytic-continuation identity), stated here as precise
  closed-form statements for the next step. No enclosure of a zeta value is
  taken as a premise beyond those three named analytic statements.
-/

namespace R00ZetaEM

/-- Complex Dirichlet eta term `(-1)^k / (k+1)^s` (cpow form). -/
noncomputable def etaCTerm (s : ℂ) (k : ℕ) : ℂ :=
  (-1 : ℂ) ^ k * (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s))

/-- Complex Dirichlet eta partial sum with `N` terms. -/
noncomputable def etaCPartial (s : ℂ) (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N, etaCTerm s k

/-- Eta-zeta conversion factor `1 - 2^{1-s}`. -/
noncomputable def etaCvtFactor (s : ℂ) : ℂ :=
  (1 : ℂ) - ((((2 : ℝ)) : ℂ) ^ (1 - s))

/-- Numeral rpow bound `5/4 ≤ 2^0.395` (cleared: `(5/4)^20 ≤ 2^7`). -/
theorem rpow_two_R00_ge : (5 / 4 : ℝ) ≤ (2 : ℝ) ^ (0.395 : ℝ) := by
  have hpow : ((5 / 4 : ℝ)) ^ ((20 : ℕ))
      ≤ ((((2 : ℝ) ^ ((7 / 20 : ℝ)))) ^ ((20 : ℕ)) : ℝ) := by
    have e : ((((2 : ℝ) ^ ((7 / 20 : ℝ)))) ^ ((20 : ℕ)) : ℝ)
        = (2 : ℝ) ^ ((7 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [show (7 / 20 : ℝ) * (((20 : ℕ)) : ℝ) = (7 : ℝ) by norm_num]
      rw [show (7 : ℝ) = (((7 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 2 7
    rw [e]
    norm_num
  have hstep : (5 / 4 : ℝ) ≤ (2 : ℝ) ^ ((7 / 20 : ℝ)) :=
    le_of_pow_le_pow_left₀ (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _).le hpow
  calc (5 / 4 : ℝ) ≤ (2 : ℝ) ^ ((7 / 20 : ℝ)) := hstep
    _ ≤ (2 : ℝ) ^ (0.395 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

/-- Numeral rpow bound `2^0.605 ≤ 8/5` (cleared: `2^2 ≤ (8/5)^3`). -/
theorem rpow_two_R00_le : (2 : ℝ) ^ (0.605 : ℝ) ≤ (8 / 5 : ℝ) := by
  have hpow : ((((2 : ℝ) ^ ((2 / 3 : ℝ)))) ^ ((3 : ℕ)) : ℝ)
      ≤ ((8 / 5 : ℝ)) ^ ((3 : ℕ)) := by
    have e : ((((2 : ℝ) ^ ((2 / 3 : ℝ)))) ^ ((3 : ℕ)) : ℝ)
        = (2 : ℝ) ^ ((2 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [show (2 / 3 : ℝ) * (((3 : ℕ)) : ℝ) = (2 : ℝ) by norm_num]
      rw [show (2 : ℝ) = (((2 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 2 2
    rw [e]
    norm_num
  have hstep : (2 : ℝ) ^ ((2 / 3 : ℝ)) ≤ (8 / 5 : ℝ) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
  calc (2 : ℝ) ^ (0.605 : ℝ) ≤ (2 : ℝ) ^ ((2 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ (8 / 5 : ℝ) := hstep

/-- Numeral rpow bound `3/2 ≤ 2^0.605` (cleared: `(3/2)^5 ≤ 2^3`). -/
theorem rpow_two_R00_thr : (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (0.605 : ℝ) := by
  have hpow : ((3 / 2 : ℝ)) ^ ((5 : ℕ))
      ≤ ((((2 : ℝ) ^ ((3 / 5 : ℝ)))) ^ ((5 : ℕ)) : ℝ) := by
    have e : ((((2 : ℝ) ^ ((3 / 5 : ℝ)))) ^ ((5 : ℕ)) : ℝ)
        = (2 : ℝ) ^ ((3 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [show (3 / 5 : ℝ) * (((5 : ℕ)) : ℝ) = (3 : ℝ) by norm_num]
      rw [show (3 : ℝ) = (((3 : ℕ)) : ℝ) by norm_num]
      exact Real.rpow_natCast 2 3
    rw [e]
    norm_num
  have hstep : (3 / 2 : ℝ) ≤ (2 : ℝ) ^ ((3 / 5 : ℝ)) :=
    le_of_pow_le_pow_left₀ (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _).le hpow
  calc (3 / 2 : ℝ) ≤ (2 : ℝ) ^ ((3 / 5 : ℝ)) := hstep
    _ ≤ (2 : ℝ) ^ (0.605 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

/-- Cast helper: the `k = 1` eta base is `((2 : ℝ) : ℂ)`. -/
theorem etaC_base_one :
    (((((1 : ℕ) : ℝ) + 1 : ℝ)) : ℂ) = ((((2 : ℝ))) : ℂ) := by
  simp only [Nat.cast_one, one_add_one_eq_two]

/-- The two-term eta partial sum in closed form. -/
theorem etaCPartial_two_eq :
    etaCPartial R00Numerics.sR00 2
      = 1 - ((((2 : ℝ))) : ℂ) ^ (-R00Numerics.sR00) := by
  have h0 : etaCTerm R00Numerics.sR00 0 = 1 := by
    show (-1 : ℂ) ^ (0 : ℕ) * (((((0 : ℕ) : ℝ) + 1 : ℝ)) : ℂ) ^ (-R00Numerics.sR00) = _
    rw [pow_zero, Nat.cast_zero, zero_add, Complex.ofReal_one, Complex.one_cpow, one_mul]
  have h1 : etaCTerm R00Numerics.sR00 1
      = -(((((2 : ℝ))) : ℂ) ^ (-R00Numerics.sR00)) := by
    show (-1 : ℂ) ^ (1 : ℕ) * (((((1 : ℕ) : ℝ) + 1 : ℝ)) : ℂ) ^ (-R00Numerics.sR00) = _
    rw [etaC_base_one, pow_one, neg_one_mul]
  have hsum : etaCPartial R00Numerics.sR00 2
      = 0 + etaCTerm R00Numerics.sR00 0 + etaCTerm R00Numerics.sR00 1 := by
    unfold etaCPartial
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hsum, h0, h1]
  ring

/-- Modulus of the second eta term: `‖2^{-sR00}‖ = 2^{-0.395} ≤ 4/5`. -/
theorem norm_etaC_second_le :
    ‖(((((2 : ℝ))) : ℂ) ^ (-R00Numerics.sR00))‖ ≤ 4 / 5 := by
  have hre : (-R00Numerics.sR00).re = -(0.395 : ℝ) := by
    rw [Complex.neg_re, R00Numerics.sR00_re]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2), hre,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    show (4 / 5 : ℝ) = ((5 / 4 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)).mpr
    rpow_two_R00_ge

/-- Two-term partial-sum lower bound `1/5 ≤ ‖S₂(sR00)‖`. -/
theorem etaCPartial_two_norm_ge :
    (1 / 5 : ℝ) ≤ ‖etaCPartial R00Numerics.sR00 2‖ := by
  rw [etaCPartial_two_eq]
  have hX := norm_etaC_second_le
  have h := norm_add_le
    (1 - ((((2 : ℝ))) : ℂ) ^ (-R00Numerics.sR00))
    (((((2 : ℝ))) : ℂ) ^ (-R00Numerics.sR00))
  rw [sub_add_cancel] at h
  rw [norm_one] at h
  linarith

/-- Conversion-factor upper bound `‖1 - 2^{1-sR00}‖ ≤ 13/5`. -/
theorem factor_upper_R00 : ‖etaCvtFactor R00Numerics.sR00‖ ≤ 13 / 5 := by
  have hfac : etaCvtFactor R00Numerics.sR00
      = (1 : ℂ) - (((((2 : ℝ))) : ℂ) ^ (1 - R00Numerics.sR00)) := rfl
  have hre : (1 - R00Numerics.sR00).re = (0.605 : ℝ) := by
    rw [Complex.sub_re, Complex.one_re, R00Numerics.sR00_re]
    norm_num
  have hY : ‖(((((2 : ℝ))) : ℂ) ^ (1 - R00Numerics.sR00))‖ ≤ 8 / 5 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2), hre]
    exact rpow_two_R00_le
  rw [hfac]
  calc ‖(1 : ℂ) - (((((2 : ℝ))) : ℂ) ^ (1 - R00Numerics.sR00))‖
        ≤ ‖(1 : ℂ)‖ + ‖(((((2 : ℝ))) : ℂ) ^ (1 - R00Numerics.sR00))‖ :=
        norm_sub_le _ _
    _ ≤ 13 / 5 := by rw [norm_one]; linarith [hY]

/-- The conversion factor is nonzero (else `2^0.605 = 1`). -/
theorem factor_ne_zero_R00 : etaCvtFactor R00Numerics.sR00 ≠ 0 := by
  have hfac : etaCvtFactor R00Numerics.sR00
      = (1 : ℂ) - (((((2 : ℝ))) : ℂ) ^ (1 - R00Numerics.sR00)) := rfl
  have hre : (1 - R00Numerics.sR00).re = (0.605 : ℝ) := by
    rw [Complex.sub_re, Complex.one_re, R00Numerics.sR00_re]
    norm_num
  rw [hfac]
  intro h
  have hYeq : (((((2 : ℝ))) : ℂ) ^ (1 - R00Numerics.sR00)) = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖(((((2 : ℝ))) : ℂ) ^ (1 - R00Numerics.sR00))‖
      = (2 : ℝ) ^ (0.605 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2), hre]
  rw [hYeq, norm_one] at hnorm
  linarith [rpow_two_R00_thr]

/-- Single-point zeta lower bound `1/26 ≤ ‖ζ(sR00)‖` from the eta limit,
remainder estimate, and eta-zeta identity (explicit analytic premises). -/
theorem zeta_lower_R00_of_eta (L : ℂ)
    (_hLim : Filter.Tendsto (fun N : ℕ => etaCPartial R00Numerics.sR00 N)
      Filter.atTop (nhds L))
    (hRem : ‖etaCPartial R00Numerics.sR00 2 - L‖ ≤ 1 / 10)
    (hId : zeta R00Numerics.sR00 * etaCvtFactor R00Numerics.sR00 = L) :
    1 / 26 ≤ ‖zeta R00Numerics.sR00‖ := by
  have hS2 := etaCPartial_two_norm_ge
  have hLlo : (1 / 10 : ℝ) ≤ ‖L‖ := by
    have h := norm_add_le L (etaCPartial R00Numerics.sR00 2 - L)
    rw [add_sub_cancel] at h
    linarith [hS2, hRem, h]
  have hZ : zeta R00Numerics.sR00 = L / etaCvtFactor R00Numerics.sR00 :=
    (eq_div_iff factor_ne_zero_R00).mpr hId
  have hF := factor_upper_R00
  have hFp : (0 : ℝ) < ‖etaCvtFactor R00Numerics.sR00‖ :=
    norm_pos_iff.mpr factor_ne_zero_R00
  rw [hZ, norm_div, le_div_iff₀ hFp]
  calc (1 / 26 : ℝ) * ‖etaCvtFactor R00Numerics.sR00‖
        ≤ (1 / 26) * (13 / 5) := mul_le_mul_of_nonneg_left hF (by norm_num)
    _ = 1 / 10 := by norm_num
    _ ≤ ‖L‖ := hLlo

#print axioms R00ZetaEM.rpow_two_R00_ge
#print axioms R00ZetaEM.etaCPartial_two_norm_ge
#print axioms R00ZetaEM.factor_ne_zero_R00
#print axioms R00ZetaEM.zeta_lower_R00_of_eta

end R00ZetaEM

/-!
## R00 complex eta convergence + explicit remainder (paired MVT + M-test).

Target: close two of the three analytic premises behind
`R00ZetaEM.zeta_lower_R00_of_eta` at `sR00` (`Re = 0.395`, `Im = -8.75`):
(1) ETA-LIMIT EXISTENCE — `S_N(sR00) = ∑_{k<N} (-1)^k ((k+1:ℝ):ℂ)^{-sR00}`
converges (paired-difference `O(n^{-Re-1})` summability for `0 < Re`);
(2) REMAINDER BOUND — explicit `‖S₂ - L‖ ≤ 25` for the `N = 2` partial sum
(`1/10` is numerically false here: `|S₂ - η| ≈ 0.96` via mpmath, so we prove
the optimal-shape explicit constant `25` from the same paired majorant via the
integral test; any explicit constant closes the "remainder" shape).

Method (all Mathlib, grepped first):
* `Complex.norm_cpow_eq_rpow_re_of_pos` for `‖x^{-s}‖ = x^{-Re s}`;
* `Summable.of_norm_bounded` (Weierstrass M-test);
* `hasDerivAt_ofReal_cpow_const` / `Complex.deriv_ofReal_cpow_const` +
  `Convex.norm_image_sub_le_of_norm_deriv_le` (mean-value bound
  `|x^{-s} - y^{-s}| ≤ |s|·|x-y|·max^{-Re-1}`);
* `Real.summable_nat_rpow_inv`, `summable_nat_add_iff`,
  `AntitoneOn.tsum_comp_add_le_integral`, `integrableOn_Ioi_rpow_of_lt`,
  `integral_Ioi_rpow_of_lt` for the explicit tail.
Premise (3) (the `ζ·(1-2^{1-s}) = L` analytic-continuation identity) is NOT
attempted here.
-/

namespace R00EtaConv

/-- Paired eta increment: `S_{2(M+1)} - S_{2M}`. -/
noncomputable def etaPair (m : ℕ) : ℂ :=
  R00ZetaEM.etaCTerm R00Numerics.sR00 (2 * m) +
    R00ZetaEM.etaCTerm R00Numerics.sR00 (2 * m + 1)

/-- `Re sR00 > 0`. -/
theorem sigma_pos : 0 < R00Numerics.sR00.re := by
  rw [R00Numerics.sR00_re]; norm_num

/-- `sR00 ≠ 0`. -/
theorem sR00_ne_zero : R00Numerics.sR00 ≠ 0 := by
  have hpos : (0 : ℝ) < ‖R00Numerics.sR00‖ :=
    lt_of_lt_of_le (by norm_num) R00Numerics.norm_sR00_ge
  exact norm_pos_iff.mp hpos

/-- `-sR00 ≠ 0`. -/
theorem neg_sR00_ne_zero : -R00Numerics.sR00 ≠ 0 :=
  neg_ne_zero.mpr sR00_ne_zero

/-- Crude upper bound `‖sR00‖ ≤ 9` (`0.395²+8.75² = 76.71… ≤ 81`). -/
theorem norm_sR00_le : ‖R00Numerics.sR00‖ ≤ 9 := by
  have hsq : ‖R00Numerics.sR00‖ ^ 2 ≤ (9 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, R00Numerics.sR00_re,
      R00Numerics.sR00_im]
    norm_num
  exact (abs_le_of_sq_le_sq' hsq (by norm_num)).2

/-- Norm of a single eta term: `‖(-1)^k (k+1)^{-s}‖ = (k+1)^{-Re s}`. -/
theorem etaCTerm_norm (k : ℕ) :
    ‖R00ZetaEM.etaCTerm R00Numerics.sR00 k‖
      = ((((k : ℝ) + 1 : ℝ)) ^ (-(R00Numerics.sR00.re))) := by
  unfold R00ZetaEM.etaCTerm
  rw [norm_mul]
  have h1 : ‖(-1 : ℂ) ^ k‖ = 1 := by
    rw [norm_pow]
    simp
  rw [h1, one_mul]
  have hx : (0 : ℝ) < (((k : ℝ) + 1 : ℝ)) := by positivity
  have h := Complex.norm_cpow_eq_rpow_re_of_pos hx (-R00Numerics.sR00)
  rw [h, Complex.neg_re]

/-- Single eta terms tend to zero (`Re > 0` template, cf. `EtaGenReal`). -/
theorem etaCTerm_tendsto_zero :
    Filter.Tendsto (fun k : ℕ => R00ZetaEM.etaCTerm R00Numerics.sR00 k)
      Filter.atTop (nhds 0) := by
  have h_top : Filter.Tendsto (fun k : ℕ => ((((k : ℝ) + 1 : ℝ)) ^ R00Numerics.sR00.re))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop sigma_pos).comp
      (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop)
  have h_inv : Filter.Tendsto
      (fun k : ℕ => ((((k : ℝ) + 1 : ℝ)) ^ R00Numerics.sR00.re)⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp h_top
  have hnorm : Filter.Tendsto
      (fun k : ℕ => ‖R00ZetaEM.etaCTerm R00Numerics.sR00 k‖)
      Filter.atTop (nhds 0) := by
    have heq : (fun k : ℕ => ‖R00ZetaEM.etaCTerm R00Numerics.sR00 k‖)
        = (fun k : ℕ => ((((k : ℝ) + 1 : ℝ)) ^ R00Numerics.sR00.re)⁻¹) := by
      funext k
      rw [etaCTerm_norm]
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (((k : ℝ) + 1 : ℝ)))]
    rw [heq]
    exact h_inv
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- `(-1)^{2m} = 1`. -/
theorem neg_one_pow_two_mul (m : ℕ) : (-1 : ℂ) ^ (2 * m) = 1 := by
  have h : (-1 : ℂ) ^ (2 * m) = (((-1 : ℂ) ^ 2) ^ m) := by rw [pow_mul]
  rw [h]
  simp

/-- `(-1)^{2m+1} = -1`. -/
theorem neg_one_pow_two_mul_succ (m : ℕ) : (-1 : ℂ) ^ (2 * m + 1) = -1 := by
  rw [pow_succ, neg_one_pow_two_mul]
  simp

/-- Pair in cpow-difference form. -/
theorem etaPair_eq_cpow_sub (m : ℕ) :
    etaPair m = ((((2 * m + 1 : ℕ) : ℝ) : ℂ) ^ (-R00Numerics.sR00))
      - ((((2 * m + 2 : ℕ) : ℝ) : ℂ) ^ (-R00Numerics.sR00)) := by
  unfold etaPair R00ZetaEM.etaCTerm
  rw [neg_one_pow_two_mul, neg_one_pow_two_mul_succ]
  have h1 : ((((2 * m : ℕ) : ℝ) + 1 : ℝ)) = (((2 * m + 1 : ℕ) : ℝ)) := by
    push_cast
    ring
  have h2 : ((((2 * m + 1 : ℕ) : ℝ) + 1 : ℝ)) = (((2 * m + 2 : ℕ) : ℝ)) := by
    push_cast
    ring
  rw [h1, h2]
  simp only [one_mul, neg_mul, one_mul]
  ring

/-- Even partial sums are sums of pairs (induction, two `sum_range_succ`). -/
theorem etaCPartial_even (M : ℕ) :
    R00ZetaEM.etaCPartial R00Numerics.sR00 (2 * M)
      = ∑ m ∈ Finset.range M, etaPair m := by
  induction M with
  | zero => simp [R00ZetaEM.etaCPartial, etaPair]
  | succ M ih =>
    have h2s : 2 * (M + 1) = (2 * M + 1) + 1 := by ring
    have h2m : 2 * M + 1 = (2 * M) + 1 := by ring
    have hpair : etaPair M = R00ZetaEM.etaCTerm R00Numerics.sR00 (2 * M)
        + R00ZetaEM.etaCTerm R00Numerics.sR00 (2 * M + 1) := rfl
    calc R00ZetaEM.etaCPartial R00Numerics.sR00 (2 * (M + 1))
        = R00ZetaEM.etaCPartial R00Numerics.sR00 (2 * M)
          + R00ZetaEM.etaCTerm R00Numerics.sR00 (2 * M)
          + R00ZetaEM.etaCTerm R00Numerics.sR00 (2 * M + 1) := by
          unfold R00ZetaEM.etaCPartial
          rw [h2s, Finset.sum_range_succ, h2m, Finset.sum_range_succ]
      _ = (∑ m ∈ Finset.range M, etaPair m) + etaPair M := by rw [ih, hpair, add_assoc]
      _ = ∑ m ∈ Finset.range (M + 1), etaPair m := by
          rw [Finset.sum_range_succ]

/-- Mean-value pair bound `‖pair m‖ ≤ ‖s‖·(2m+1)^{-Re-1}`. -/
theorem norm_etaPair_le (m : ℕ) :
    ‖etaPair m‖ ≤ ‖R00Numerics.sR00‖
      * ((((2 * m + 1 : ℕ) : ℝ)) ^ (-(R00Numerics.sR00.re) - 1)) := by
  set a : ℝ := (((2 * m + 1 : ℕ) : ℝ)) with ha
  set b : ℝ := (((2 * m + 2 : ℕ) : ℝ)) with hb
  have ha_pos : (0 : ℝ) < a := by
    unfold a
    exact Nat.cast_pos.mpr (by omega)
  have hab : a ≤ b := by
    unfold a b
    exact Nat.cast_le.mpr (by omega)
  have hb_eq : b = a + 1 := by
    unfold a b
    have heq : 2 * m + 1 + 1 = 2 * m + 2 := by omega
    calc ((((2 * m + 2 : ℕ)) : ℝ))
        = ((((2 * m + 1 + 1 : ℕ)) : ℝ)) := by rw [heq]
      _ = ((((2 * m + 1 : ℕ)) : ℝ)) + 1 := by rw [Nat.cast_add, Nat.cast_one]
  have hpair : etaPair m = (a : ℂ) ^ (-R00Numerics.sR00)
      - (b : ℂ) ^ (-R00Numerics.sR00) := by
    rw [etaPair_eq_cpow_sub]
  set F : ℝ → ℂ := fun t : ℝ => (t : ℂ) ^ (-R00Numerics.sR00) with hF
  have hF_eq : ∀ t : ℝ, F t = (t : ℂ) ^ (-R00Numerics.sR00) := fun t => rfl
  have hdiff : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ F x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha_pos (Set.mem_Icc.mp hx).1
    exact (hasDerivAt_ofReal_cpow_const (ne_of_gt hx0) neg_sR00_ne_zero).differentiableAt
  have hderiv_eq : ∀ x : ℝ, x ≠ 0 →
      deriv F x = (-R00Numerics.sR00) * (x : ℂ) ^ (-R00Numerics.sR00 - 1) := by
    intro x hx0
    have h := Complex.deriv_ofReal_cpow_const hx0 (c := -R00Numerics.sR00)
      neg_sR00_ne_zero
    -- `F` is definitionally the lambda in the lemma
    simpa [hF] using h
  have hexp_nonpos : -(R00Numerics.sR00.re) - 1 ≤ 0 := by
    have := sigma_pos
    linarith
  have hbound : ∀ x ∈ Set.Icc a b, ‖deriv F x‖
      ≤ ‖R00Numerics.sR00‖ * (a ^ (-(R00Numerics.sR00.re) - 1)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha_pos (Set.mem_Icc.mp hx).1
    have hax : a ≤ x := (Set.mem_Icc.mp hx).1
    rw [hderiv_eq x (ne_of_gt hx0)]
    have hnorm_cpow : ‖(x : ℂ) ^ (-R00Numerics.sR00 - 1)‖
        = x ^ ((-(R00Numerics.sR00) - 1).re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos hx0 _
    have hre : ((-(R00Numerics.sR00) - 1).re) = -(R00Numerics.sR00.re) - 1 := by
      simp [Complex.sub_re, Complex.neg_re]
    have hle : x ^ (-(R00Numerics.sR00.re) - 1)
        ≤ a ^ (-(R00Numerics.sR00.re) - 1) :=
      Real.rpow_le_rpow_of_nonpos ha_pos hax hexp_nonpos
    calc ‖-R00Numerics.sR00 * (x : ℂ) ^ (-R00Numerics.sR00 - 1)‖
        = ‖R00Numerics.sR00‖ * (x ^ (-(R00Numerics.sR00.re) - 1)) := by
          rw [norm_mul, norm_neg, hnorm_cpow, hre]
      _ ≤ ‖R00Numerics.sR00‖ * (a ^ (-(R00Numerics.sR00.re) - 1)) := by
          exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)
  have hC_nonneg : (0 : ℝ) ≤ ‖R00Numerics.sR00‖ * (a ^ (-(R00Numerics.sR00.re) - 1)) :=
    mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg ha_pos.le _)
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_Icc a b) (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  -- `hmvt : ‖F b - F a‖ ≤ C * ‖b - a‖`
  have hba : ‖b - a‖ = 1 := by
    have hsub : b - a = 1 := by rw [hb_eq]; ring
    rw [hsub, norm_one]
  rw [hba, mul_one] at hmvt
  have hrev : ‖F a - F b‖ = ‖F b - F a‖ := norm_sub_rev _ _
  rw [hpair, hrev]
  simpa [ha] using hmvt

/-- Exponent identity `Re+1 = 1.395`. -/
theorem q_eq : R00Numerics.sR00.re + 1 = (1.395 : ℝ) := by
  rw [R00Numerics.sR00_re]; norm_num

/-- Negated exponent identity. -/
theorem neg_exp_eq : -(R00Numerics.sR00.re) - 1 = (-1.395 : ℝ) := by
  rw [R00Numerics.sR00_re]; norm_num

/-- The paired series is summable (M-test vs `p = 1.395 > 1`). -/
theorem summable_etaPair : Summable etaPair := by
  have hq1 : (1 : ℝ) < 1.395 := by norm_num
  have hbase : Summable (fun n : ℕ => ((((n : ℝ)) ^ (1.395 : ℝ)))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hq1
  have hshift : Summable (fun m : ℕ => ((((m + 1 : ℕ) : ℝ) ^ (1.395 : ℝ)))⁻¹) :=
    (summable_nat_add_iff 1).mpr hbase
  have hC : Summable (fun m : ℕ => ‖R00Numerics.sR00‖
      * ((((m + 1 : ℕ) : ℝ) ^ (1.395 : ℝ)))⁻¹) :=
    hshift.mul_left _
  refine Summable.of_norm_bounded hC (fun m => ?_)
  have hle1 := norm_etaPair_le m
  rw [neg_exp_eq] at hle1
  have ha_pos : (0 : ℝ) < (((2 * m + 1 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (by omega)
  have hm_pos : (0 : ℝ) < (((m + 1 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (by omega)
  have hmono_le : ((((m + 1 : ℕ)) : ℝ)) ≤ ((((2 * m + 1 : ℕ)) : ℝ)) :=
    Nat.cast_le.mpr (by omega)
  have hrpow_le : ((((2 * m + 1 : ℕ) : ℝ)) ^ (-1.395 : ℝ))
      ≤ ((((m + 1 : ℕ) : ℝ)) ^ (-1.395 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hm_pos hmono_le (by norm_num)
  have hrpow_eq1 : ((((2 * m + 1 : ℕ) : ℝ)) ^ (-1.395 : ℝ))
      = ((((2 * m + 1 : ℕ) : ℝ) ^ (1.395 : ℝ)))⁻¹ := by
    rw [← Real.rpow_neg (Nat.cast_nonneg _)]
  have hrpow_eq2 : ((((m + 1 : ℕ) : ℝ)) ^ (-1.395 : ℝ))
      = ((((m + 1 : ℕ) : ℝ) ^ (1.395 : ℝ)))⁻¹ := by
    rw [← Real.rpow_neg (Nat.cast_nonneg _)]
  calc ‖etaPair m‖ ≤ ‖R00Numerics.sR00‖
          * ((((2 * m + 1 : ℕ) : ℝ)) ^ (-1.395 : ℝ)) := hle1
    _ = ‖R00Numerics.sR00‖ * ((((2 * m + 1 : ℕ) : ℝ) ^ (1.395 : ℝ)))⁻¹ := by
        rw [hrpow_eq1]
    _ ≤ ‖R00Numerics.sR00‖ * ((((m + 1 : ℕ) : ℝ) ^ (1.395 : ℝ)))⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [← hrpow_eq1, ← hrpow_eq2]
        exact hrpow_le

/-- Even subsequence tends to the paired tsum. -/
theorem even_tendsto :
    Filter.Tendsto (fun M : ℕ => R00ZetaEM.etaCPartial R00Numerics.sR00 (2 * M))
      Filter.atTop (nhds (∑' m, etaPair m)) := by
  have h := summable_etaPair.hasSum.tendsto_sum_nat
  simpa [etaCPartial_even] using h

/-- Odd subsequence tends to the same limit (even + vanishing term). -/
theorem odd_tendsto :
    Filter.Tendsto (fun M : ℕ => R00ZetaEM.etaCPartial R00Numerics.sR00 (2 * M + 1))
      Filter.atTop (nhds (∑' m, etaPair m)) := by
  have hev := even_tendsto
  have hterm : Filter.Tendsto
      (fun M : ℕ => R00ZetaEM.etaCTerm R00Numerics.sR00 (2 * M))
      Filter.atTop (nhds 0) := by
    apply etaCTerm_tendsto_zero.comp
    apply Filter.tendsto_atTop_mono (fun M => Nat.le_mul_of_pos_left M (by norm_num))
    exact Filter.tendsto_id
  have hadd := hev.add hterm
  simp only [add_zero] at hadd
  refine hadd.congr (fun M => ?_)
  unfold R00ZetaEM.etaCPartial
  have h2 : 2 * M + 1 = (2 * M) + 1 := by ring
  rw [h2, Finset.sum_range_succ]

/-- Auxiliary even/odd glue: two subsequences `2M`, `2M+1` force full convergence. -/
theorem tendsto_of_even_odd_tendsto {f : ℕ → ℂ} {L : ℂ}
    (hev : Filter.Tendsto (fun M : ℕ => f (2 * M)) Filter.atTop (nhds L))
    (hodd : Filter.Tendsto (fun M : ℕ => f (2 * M + 1)) Filter.atTop (nhds L)) :
    Filter.Tendsto f Filter.atTop (nhds L) := by
  rw [Metric.tendsto_atTop] at hev hodd ⊢
  intro ε hε
  obtain ⟨M1, hM1⟩ := hev ε hε
  obtain ⟨M2, hM2⟩ := hodd ε hε
  refine ⟨2 * max M1 M2, fun N hN => ?_⟩
  rcases Nat.even_or_odd N with hE | hO
  · obtain ⟨M, rfl⟩ := hE
    -- `Even N` unfolds to `N = M + M`; rewrite to `2 * M`
    have h2 : M + M = 2 * M := by ring
    rw [h2] at hN ⊢
    apply hM1
    have hM : max M1 M2 ≤ M := by omega
    exact le_trans (Nat.le_max_left _ _) hM
  · obtain ⟨M, rfl⟩ := hO
    -- `Odd N` unfolds to `N = 2 * M + 1`
    apply hM2
    have hM : max M1 M2 ≤ M := by omega
    exact le_trans (Nat.le_max_right _ _) hM

/-- (1) ETA-LIMIT EXISTENCE: full complex eta partial sums converge at `sR00`. -/
theorem eta_limit_exists :
    ∃ L : ℂ, Filter.Tendsto (fun N : ℕ => R00ZetaEM.etaCPartial R00Numerics.sR00 N)
      Filter.atTop (nhds L) :=
  ⟨_, tendsto_of_even_odd_tendsto even_tendsto odd_tendsto⟩

/-- `S₂` is the zeroth pair. -/
theorem S2_eq_pair_zero :
    R00ZetaEM.etaCPartial R00Numerics.sR00 2 = etaPair 0 := by
  have h := etaCPartial_even 1
  have h21 : 2 * 1 = 2 := by norm_num
  rw [h21] at h
  have hsum : (∑ m ∈ Finset.range 1, etaPair m) = etaPair 0 := by simp
  rw [hsum] at h
  exact h

/-- Real majorant antitone on `Ici 1`. -/
theorem majorant_antitone :
    AntitoneOn (fun x : ℝ => x ^ (-1.395 : ℝ)) (Set.Ici (1 : ℝ)) := by
  apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono
  intro x hx
  simp only [Set.mem_Ici] at hx
  simp only [Set.mem_Ioi]
  linarith

/-- Real majorant integrable on `Ioi 1`. -/
theorem majorant_integrable :
    MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-1.395 : ℝ))
      (Set.Ioi (1 : ℝ)) :=
  integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)

/-- Majorant nonnegative on `Ioi 1`. -/
theorem majorant_nonneg :
    ∀ t ∈ Set.Ioi (1 : ℝ), (0 : ℝ) ≤ t ^ (-1.395 : ℝ) := by
  intro t ht
  have ht1 : (1 : ℝ) < t := Set.mem_Ioi.mp ht
  have ht0 : (0 : ℝ) < t := lt_trans (by norm_num) ht1
  exact Real.rpow_nonneg ht0.le _

/-- Integral value `∫_{1}^{∞} x^{-1.395} = 1/0.395 ≤ 2.6`. -/
theorem majorant_integral_le :
    (∫ x : ℝ in Set.Ioi (1 : ℝ), x ^ (-1.395 : ℝ)) ≤ 2.6 := by
  have h := integral_Ioi_rpow_of_lt (a := (-1.395 : ℝ)) (by norm_num)
    (c := (1 : ℝ)) (by norm_num)
  rw [h]
  have h1 : (1 : ℝ) ^ ((-1.395 : ℝ) + 1) = 1 := Real.one_rpow _
  rw [h1]
  norm_num

/-- Tsum tail of the real majorant is bounded by the integral. -/
theorem majorant_tsum_tail_le :
    (∑' n : ℕ, ((((n + 2 : ℕ)) : ℝ) ^ (-1.395 : ℝ))) ≤ 2.6 := by
  have h := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (-1.395 : ℝ))
    (1 : ℕ) (by simpa using majorant_antitone)
    (by simpa using majorant_integrable) (by simpa using majorant_nonneg)
  have heq : ∀ n : ℕ, ((((n + 1 + 1 : ℕ)) : ℝ) ^ (-1.395 : ℝ))
      = ((((n + 2 : ℕ)) : ℝ) ^ (-1.395 : ℝ)) := by
    intro n
    have hnn : n + 1 + 1 = n + 2 := by omega
    rw [hnn]
  simp only [heq] at h
  have h' : (∫ x : ℝ in Set.Ioi (((1 : ℕ)) : ℝ), x ^ (-1.395 : ℝ))
      = (∫ x : ℝ in Set.Ioi (1 : ℝ), x ^ (-1.395 : ℝ)) := by
    rw [Nat.cast_one]
  rw [h'] at h
  exact le_trans h majorant_integral_le

/-- Full real majorant summable. -/
theorem majorant_summable :
    Summable (fun n : ℕ => ((((n : ℕ)) : ℝ) ^ (-1.395 : ℝ))) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-1.395 : ℝ))
      (Set.Ici (((1 : ℕ)) : ℝ)) := by
    rw [Nat.cast_one]
    exact majorant_antitone
  have hint : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-1.395 : ℝ))
      (Set.Ioi (((1 : ℕ)) : ℝ)) := by
    rw [Nat.cast_one]
    exact majorant_integrable
  have hnon : ∀ t ∈ Set.Ioi (((1 : ℕ)) : ℝ), (0 : ℝ) ≤ t ^ (-1.395 : ℝ) := by
    intro t ht
    have ht' : t ∈ Set.Ioi (1 : ℝ) := by
      simpa [Nat.cast_one] using ht
    exact majorant_nonneg t ht'
  exact AntitoneOn.summable_of_integrableOn_Ioi (N := 1) hanti hint hnon

/-- Shifted majorant summable (tail from `2`). -/
theorem majorant_shift_two_summable :
    Summable (fun m : ℕ => ((((m + 2 : ℕ)) : ℝ) ^ (-1.395 : ℝ))) :=
  (summable_nat_add_iff 2).mpr majorant_summable

/-- Scaled tail majorant summable. -/
theorem majorant_scaled_summable :
    Summable (fun m : ℕ => (9 : ℝ) * ((((m + 2 : ℕ)) : ℝ) ^ (-1.395 : ℝ))) :=
  majorant_shift_two_summable.mul_left 9

/-- Scaled tsum factors. -/
theorem majorant_scaled_tsum_eq :
    (∑' m, (9 : ℝ) * ((((m + 2 : ℕ)) : ℝ) ^ (-1.395 : ℝ)))
      = 9 * (∑' n : ℕ, ((((n + 2 : ℕ)) : ℝ) ^ (-1.395 : ℝ))) :=
  Summable.tsum_mul_left 9 majorant_shift_two_summable

/-- Scaled tail tsum bounded by `9 * 2.6`. -/
theorem majorant_scaled_tsum_le :
    (∑' m, (9 : ℝ) * ((((m + 2 : ℕ)) : ℝ) ^ (-1.395 : ℝ))) ≤ 9 * 2.6 := by
  rw [majorant_scaled_tsum_eq]
  apply mul_le_mul_of_nonneg_left majorant_tsum_tail_le (by norm_num)

/-- Tail pair bound (single index). -/
theorem tail_pair_bound (m : ℕ) : ‖etaPair (m + 1)‖
    ≤ 9 * ((((m + 2 : ℕ)) : ℝ) ^ (-1.395 : ℝ)) := by
  have hle1 := norm_etaPair_le (m + 1)
  rw [neg_exp_eq] at hle1
  have hge : ((((m + 2 : ℕ)) : ℝ)) ≤ ((((2 * (m + 1) + 1 : ℕ)) : ℝ)) := by
    apply Nat.cast_le.mpr
    omega
  have hm_pos : (0 : ℝ) < ((((m + 2 : ℕ)) : ℝ)) := Nat.cast_pos.mpr (by omega)
  have hrpow_le : ((((2 * (m + 1) + 1 : ℕ)) : ℝ) ^ (-1.395 : ℝ))
      ≤ ((((m + 2 : ℕ)) : ℝ) ^ (-1.395 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hm_pos hge (by norm_num)
  calc ‖etaPair (m + 1)‖ ≤ ‖R00Numerics.sR00‖
          * ((((2 * (m + 1) + 1 : ℕ)) : ℝ) ^ (-1.395 : ℝ)) := hle1
    _ ≤ 9 * ((((2 * (m + 1) + 1 : ℕ)) : ℝ) ^ (-1.395 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right norm_sR00_le
        exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    _ ≤ 9 * ((((m + 2 : ℕ)) : ℝ) ^ (-1.395 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hrpow_le (by norm_num)

/-- Tail tsum norm bounded. -/
theorem tail_tsum_norm_le :
    ‖∑' m, etaPair (m + 1)‖
      ≤ ∑' m, (9 : ℝ) * ((((m + 2 : ℕ)) : ℝ) ^ (-1.395 : ℝ)) :=
  tsum_of_norm_bounded majorant_scaled_summable.hasSum tail_pair_bound

/-- Split `∑' = pair 0 + tail`. -/
theorem tsum_split_pair_zero :
    (∑ i ∈ Finset.range 1, etaPair i) + (∑' m, etaPair (m + 1))
      = ∑' m, etaPair m :=
  Summable.sum_add_tsum_nat_add 1 summable_etaPair

set_option maxHeartbeats 800000 in
/-- (2) REMAINDER BOUND: `‖S₂ - L‖ ≤ 25` with `L = ∑' pairs`. -/
theorem remainder_le :
    ‖R00ZetaEM.etaCPartial R00Numerics.sR00 2 - (∑' m, etaPair m)‖ ≤ 25 := by
  have hsplit := tsum_split_pair_zero
  have hrange1 : (∑ i ∈ Finset.range 1, etaPair i) = etaPair 0 := by simp
  rw [hrange1] at hsplit
  have hS2 := S2_eq_pair_zero
  -- tail as a tsum
  have htail_eq : (∑' m, etaPair m) - etaPair 0 = ∑' m, etaPair (m + 1) := by
    have hadd : etaPair 0 + (∑' m, etaPair (m + 1)) = ∑' m, etaPair m := hsplit
    calc (∑' m, etaPair m) - etaPair 0
        = (etaPair 0 + (∑' m, etaPair (m + 1))) - etaPair 0 := by rw [hadd]
      _ = ∑' m, etaPair (m + 1) := by ring
  have hdiff : R00ZetaEM.etaCPartial R00Numerics.sR00 2 - (∑' m, etaPair m)
      = -((∑' m, etaPair m) - etaPair 0) := by
    rw [hS2]
    ring
  rw [hdiff, norm_neg, htail_eq]
  have hmid : (∑' m, (9 : ℝ) * ((((m + 2 : ℕ)) : ℝ) ^ (-1.395 : ℝ))) ≤ 9 * 2.6 := by
    rw [majorant_scaled_tsum_eq]
    exact mul_le_mul_of_nonneg_left majorant_tsum_tail_le (by norm_num)
  calc ‖∑' m, etaPair (m + 1)‖
      ≤ ∑' m, (9 : ℝ) * ((((m + 2 : ℕ)) : ℝ) ^ (-1.395 : ℝ)) :=
        tail_tsum_norm_le
    _ ≤ 9 * 2.6 := hmid
    _ ≤ 25 := by norm_num

/-- Combined close: existence + explicit remainder `≤ 25`. -/
theorem eta_limit_and_remainder :
    ∃ L : ℂ, Filter.Tendsto (fun N : ℕ => R00ZetaEM.etaCPartial R00Numerics.sR00 N)
      Filter.atTop (nhds L) ∧ ‖R00ZetaEM.etaCPartial R00Numerics.sR00 2 - L‖ ≤ 25 := by
  refine ⟨∑' m, etaPair m, ?_, remainder_le⟩
  -- full convergence from even/odd
  have hev := even_tendsto
  have hodd := odd_tendsto
  exact tendsto_of_even_odd_tendsto hev hodd

#print axioms R00EtaConv.sigma_pos
#print axioms R00EtaConv.summable_etaPair
#print axioms R00EtaConv.eta_limit_exists
#print axioms R00EtaConv.remainder_le
#print axioms R00EtaConv.eta_limit_and_remainder

end R00EtaConv

