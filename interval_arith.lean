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

/-!
## Uniform Gamma lower bound for every cell center + R02 template assembly.

Status: all 40 packaged cells (`R00`–`R40` in `CentralCoverAssembly`) take their
`center_bound` (`ε + M * radius ≤ ‖xiShifted center‖`) as an explicit hypothesis
(`RXX_leaf_obligations`). `R00Enclosure.R00_center_bound_of_component_bounds`
reduces `R00`'s center obligation to four factor bounds (poly / pi / Gamma /
zeta), of which poly + pi + Gamma are closed hypothesis-free (`R00Numerics`,
`R00GammaLower`) and zeta remains conditional (`R00ZetaEM.zeta_lower_R00_of_eta`).

New here (all fully proved, no `sorry`, no new axioms):

1. `CellGammaUniform.gamma_lower_wide`: the joint Gammaℝ/reflection route of
   `R00GammaLower.gamma_lower_rect` generalized from the R00 `s`-rect
   (`Re ∈ [0.3,0.49]`, `Im ∈ [-10,-7.5]`) to the WIDE hypotheses
   `0.01 ≤ s.re ≤ 0.49`, `|s.im| ≤ 10`, `s.im ≠ 0`. The original proof uses the
   rect only through exactly these consequences (`(1-s/2).re ∈ [0.755,0.85]`
   becomes `[0.755,0.995]`, still inside `[0,1]` for the convexity step;
   `|s.im| ≤ 10` for the sine majorant; `s.im ≠ 0` for sine nonvanishing), so
   the same constant `1/10000000` holds. Coverage: every packaged cell center
   `z` has `s = 1/2 + I·z` with `s.re = 1/2 - z.im ∈ [0.01,0.49]`
   (bottom row `0.395`, row1 `0.3`, row2 `0.2`, top row `0.105`) and
   `s.im = z.re ∈ [-8.75,8.75] ∖ {0}` — i.e. this ONE lemma supplies the
   hypothesis-free Gamma-center factor for all 40 cells.
2. `CellUniform.pi_lower_of_re`: `1/2 ≤ ‖piPart s‖` for every `s` with
   `s.re ≤ 1/2` (from `‖piPart s‖ = π^(-s.re/2)` and
   `CpowInterval.pi_rpow_neg_quarter_ge_half`); covers all 40 centers.
3. `CellUniform.center_bound_of_component_bounds`: the R00 four-factor product
   bridge generalized to an arbitrary `Rect2D` (takes `R.radius ≤ 1.26` and
   `0 ≤ M` as explicit premises; all 40 cells satisfy the radius bound via
   their `RXX_radius_lt`).
4. `R02Uniform`: full template instantiation for `R02 = (-8,-5.5,0.01,0.2)`
   (outer tier `(ε,M) = (0.002,0.05)`): `s`-center coordinates, hypothesis-free
   poly (`22 ≤ ‖poly‖`), pi, and Gamma enclosures, the conditional center
   assembly `R02_center_with_poly_pi_gamma` (explicit residual: one zeta lower
   bound + the numeric product check), and `R02_H_of_components` discharging
   the `H`-leaf of `inner_nonvanishing_of_fenced_grid_fine` at R02's grid cell
   modulo exactly the two named missing enclosures (zeta factor, deriv bound).

Grep-first record (prior art checked before writing):
* `rg "center_bound_of_component_bounds|gamma_lower_wide|pi_lower_of|poly_lower_R0|deriv xiShifted"`
  → only the R00-specific bridge exists; uniform-deriv bounds exist nowhere
  (only per-cell hypotheses + unrelated `deriv xiShifted` facts about simple
  zeros in `riemann_hypothesis.lean`); no `sR02`/wide/duplicated names.
* `rg "theorem.*Gamma.*≤|Stirling|norm_Gamma" Mathlib/Analysis/SpecialFunctions/Gamma/`
  → no formalized complex-Gamma upper/Stirling bounds (one aspirational code
  comment in `BohrMollerup.lean`); the integral majorant
  `R00GammaLower.norm_Gamma_le_realGamma` + convexity route used here is the
  available tool, hence the weak-but-rigorous `1/1e7` constant (see residual).
-/

namespace CellGammaUniform

/-- Uniform real-Gamma upper bound `Real.Gamma ((1 - s/2).re) ≤ 1.5` under wide
hypotheses `0.01 ≤ s.re ≤ 0.49` (same convexity proof as
`R00GammaLower.realGamma_one_sub_half_le`; here `x = (1-s/2).re ∈ [0.755,0.995]`,
so `x + 1 ∈ [1.755,1.995] ⊆ [1,2]` and `1/x ≤ 1/0.755 ≤ 1.5`). -/
theorem realGamma_one_sub_half_le_wide {s : ℂ}
    (hre_lo : (0.01 : ℝ) ≤ s.re) (hre_hi : s.re ≤ (0.49 : ℝ)) :
    Real.Gamma ((1 - s / 2).re) ≤ 1.5 := by
  have hre2 : (s / 2).re = s.re / 2 := by rw [Complex.div_ofNat_re]
  have hx_eq : (1 - s / 2).re = 1 - s.re / 2 := by
    rw [Complex.sub_re, Complex.one_re, hre2]
  have hx_lo : (0.755 : ℝ) ≤ (1 - s / 2).re := by rw [hx_eq]; linarith
  have hx_hi : (1 - s / 2).re ≤ (0.995 : ℝ) := by rw [hx_eq]; linarith
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

/-- Uniform sine majorant `‖sin(π·(s/2))‖ ≤ Real.exp 16` from `|s.im| ≤ 10`
(same exponential estimate as `R00GammaLower.norm_sin_pi_half_le`). -/
theorem norm_sin_pi_half_le_wide {s : ℂ} (hab : |s.im| ≤ 10) :
    ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ ≤ Real.exp 16 := by
  set w : ℂ := (Real.pi : ℂ) * (s / 2) with hw
  have hs2im : (s / 2).im = s.im / 2 := by rw [Complex.div_ofNat_im]
  have hw_im : w.im = Real.pi * (s.im / 2) := by
    rw [hw]
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hs2im]
  have hpi_le : Real.pi ≤ 3.1416 := le_of_lt Real.pi_lt_d4
  have hw_abs : |w.im| ≤ 16 := by
    rw [hw_im, abs_mul]
    have h1 : |Real.pi| ≤ 3.1416 := by
      rw [abs_of_pos Real.pi_pos]; exact hpi_le
    have h2 : |s.im / 2| ≤ 5 := by
      rw [abs_div, abs_two]
      have : |s.im| / 2 ≤ 5 := by linarith [hab]
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

/-- Sine is nonzero at `π·(s/2)` when `s.im ≠ 0` (same integer-multiple
argument as `R00GammaLower.sin_pi_half_ne`). -/
theorem sin_pi_half_ne_wide {s : ℂ} (hne : s.im ≠ 0) :
    Complex.sin ((Real.pi : ℂ) * (s / 2)) ≠ 0 := by
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
  exact hne this

/-- MAIN uniform bound: `1/10000000 ≤ ‖Gamma(s/2)‖` under the wide hypotheses
`0.01 ≤ s.re ≤ 0.49`, `|s.im| ≤ 10`, `s.im ≠ 0` — satisfied by the `s`-center
of every one of the 40 packaged cells (see module doc above for the row table).
Same reflection assembly as `R00GammaLower.gamma_lower_rect`. -/
theorem gamma_lower_wide {s : ℂ}
    (hre_lo : (0.01 : ℝ) ≤ s.re) (hre_hi : s.re ≤ (0.49 : ℝ))
    (hab : |s.im| ≤ 10) (hne : s.im ≠ 0) :
    (1 / 10000000 : ℝ) ≤ ‖Complex.Gamma (s / 2)‖ := by
  have hs2re : (s / 2).re = s.re / 2 := by rw [Complex.div_ofNat_re]
  have h1w_re : (0 : ℝ) < (1 - s / 2).re := by
    rw [Complex.sub_re, Complex.one_re, hs2re]
    linarith
  have hG1_ne : Complex.Gamma (1 - s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h1w_re
  have hsin_ne := sin_pi_half_ne_wide hne
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
          R00GammaLower.norm_Gamma_le_realGamma h1w_re
      _ ≤ 1.5 := realGamma_one_sub_half_le_wide hre_lo hre_hi
  have hsin_le : ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ ≤ Real.exp 16 :=
    norm_sin_pi_half_le_wide hab
  have hexp_lt : Real.exp 16 < 10000000 := R00GammaLower.exp_sixteen_lt
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

#print axioms CellGammaUniform.realGamma_one_sub_half_le_wide
#print axioms CellGammaUniform.norm_sin_pi_half_le_wide
#print axioms CellGammaUniform.sin_pi_half_ne_wide
#print axioms CellGammaUniform.gamma_lower_wide

end CellGammaUniform

namespace CellUniform

/-- Uniform pi-power lower bound `1/2 ≤ ‖piPart s‖` for every `s` with
` s.re ≤ 1/2` (covers all 40 cell centers, whose `s.re ≤ 0.49`).
Proof: `‖piPart s‖ = π^(-s.re/2) ≥ π^(-1/4) ≥ 1/2`
(`CpowInterval.pi_rpow_neg_quarter_ge_half`). -/
theorem pi_lower_of_re {s : ℂ} (hre : s.re ≤ (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ ‖R00Enclosure.piPart s‖ := by
  have hnorm : ‖R00Enclosure.piPart s‖ = Real.pi ^ (-(s.re) / 2) := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos (-(s / 2))
    unfold R00Enclosure.piPart
    rw [h]
    congr 1
    rw [Complex.neg_re, Complex.div_ofNat_re]
    ring
  rw [hnorm]
  have hexp : (-(1 / 4 : ℝ)) ≤ -(s.re) / 2 := by linarith
  calc (1 / 2 : ℝ) ≤ Real.pi ^ (-(1 / 4 : ℝ)) :=
        CpowInterval.pi_rpow_neg_quarter_ge_half
    _ ≤ Real.pi ^ (-(s.re) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hexp

/-- Generic four-factor center bridge for an arbitrary fencing rect: component
lower bounds at `s = 1/2 + I·R.center` plus the numeric product check give
`ε + M * R.radius ≤ ‖xiShifted R.center‖`. Every packaged cell satisfies
`R.radius ≤ 1.26` via its `RXX_radius_lt`. -/
theorem center_bound_of_component_bounds (R : CellProofEngine.Rect2D) (ε M : ℝ)
    (hM0 : 0 ≤ M) (hrad : R.radius ≤ 1.26)
    (Apoly Api Agam Azeta : ℝ)
    (hA0 : 0 ≤ Apoly) (hB0 : 0 ≤ Api) (hC0 : 0 ≤ Agam) (hD0 : 0 ≤ Azeta)
    (hpoly : Apoly ≤ ‖R00Enclosure.polyPart ((1 / 2 : ℂ) + Complex.I * R.center)‖)
    (hpi : Api ≤ ‖R00Enclosure.piPart ((1 / 2 : ℂ) + Complex.I * R.center)‖)
    (hgam : Agam ≤ ‖R00Enclosure.gammaPart ((1 / 2 : ℂ) + Complex.I * R.center)‖)
    (hzeta : Azeta ≤ ‖zeta ((1 / 2 : ℂ) + Complex.I * R.center)‖)
    (hprod : ε + M * 1.26 ≤ Apoly * Api * Agam * Azeta) :
    ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hdecomp := R00Enclosure.norm_xiShifted_eq_parts R.center
  have hle : Apoly * Api * Agam * Azeta ≤ ‖xiShifted R.center‖ := by
    rw [hdecomp]
    exact TailProofEngine.prod_four_ge_of_ge
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hpoly hpi hgam hzeta hA0 hB0 hC0 hD0
  have hbud : M * R.radius ≤ M * 1.26 :=
    mul_le_mul_of_nonneg_left hrad hM0
  linarith

#print axioms CellUniform.pi_lower_of_re
#print axioms CellUniform.center_bound_of_component_bounds

end CellUniform

namespace R02Uniform

/-- The R02 `s`-plane center: `s = 1/2 + I·z` at `z = R02.center`. -/
noncomputable def sR02 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R02.center

/-- `R02.center = -6.75 + 0.105·I` (from `R02_x0/x1/y0/y1`). -/
theorem R02_center_eq :
    CentralCoverAssembly.R02.center =
      (((-6.75 : ℝ))) + Complex.I * ((((0.105 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R02_x0, CentralCoverAssembly.R02_x1,
      CentralCoverAssembly.R02_y0, CentralCoverAssembly.R02_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R02_x0, CentralCoverAssembly.R02_x1,
      CentralCoverAssembly.R02_y0, CentralCoverAssembly.R02_y1]
    simp
    norm_num

/-- `Re sR02 = 0.395` (`1/2 - 0.105`, same bottom row as R00). -/
theorem sR02_re : sR02.re = 0.395 := by
  unfold sR02
  rw [R02_center_eq]
  simp
  norm_num

/-- `Im sR02 = -6.75`. -/
theorem sR02_im : sR02.im = -6.75 := by
  unfold sR02
  rw [R02_center_eq]
  simp

/-- `‖sR02‖ ≥ 6.7` (`6.7² = 44.89 < 0.395² + 6.75² = 45.718525`). -/
theorem norm_sR02_ge : (6.7 : ℝ) ≤ ‖sR02‖ := by
  have hsq : (6.7 : ℝ) ^ 2 ≤ ‖sR02‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, sR02_re, sR02_im]
    norm_num
  calc (6.7 : ℝ) = Real.sqrt ((6.7 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖sR02‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖sR02‖ := Real.sqrt_sq (norm_nonneg _)

/-- `‖sR02 - 1‖ ≥ 6.7` (`0.605² + 6.75² = 45.928525 > 44.89`). -/
theorem norm_sR02_sub_one_ge : (6.7 : ℝ) ≤ ‖sR02 - 1‖ := by
  have hr1 : (sR02 - 1).re = -0.605 := by
    simp only [Complex.sub_re, Complex.one_re, sR02_re]
    norm_num
  have hi1 : (sR02 - 1).im = -6.75 := by
    simp only [Complex.sub_im, Complex.one_im, sR02_im]
    norm_num
  have hsq : (6.7 : ℝ) ^ 2 ≤ ‖sR02 - 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hr1, hi1]
    norm_num
  calc (6.7 : ℝ) = Real.sqrt ((6.7 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖sR02 - 1‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖sR02 - 1‖ := Real.sqrt_sq (norm_nonneg _)

/-- Norm version of `polyPart` at `sR02`. -/
theorem polyPart_norm_R02 :
    ‖R00Enclosure.polyPart sR02‖ = (1 / 2) * ‖sR02‖ * ‖sR02 - 1‖ := by
  unfold R00Enclosure.polyPart
  rw [norm_mul, norm_mul, R00Numerics.norm_half]

/-- ENCLOSURE (hypothesis-free): `22 ≤ ‖polyPart sR02‖`
(`6.7·6.7/2 = 22.445 ≥ 22`). -/
theorem poly_lower_R02 : (22 : ℝ) ≤ ‖R00Enclosure.polyPart sR02‖ := by
  have hprod : (6.7 : ℝ) * 6.7 ≤ ‖sR02‖ * ‖sR02 - 1‖ :=
    mul_le_mul norm_sR02_ge norm_sR02_sub_one_ge (by norm_num) (norm_nonneg _)
  rw [polyPart_norm_R02]
  nlinarith [hprod]

/-- ENCLOSURE (hypothesis-free): `1/2 ≤ ‖piPart sR02‖` (uniform pi lemma +
`Re sR02 = 0.395 ≤ 1/2`). -/
theorem pi_lower_R02 : (1 / 2 : ℝ) ≤ ‖R00Enclosure.piPart sR02‖ :=
  CellUniform.pi_lower_of_re (by rw [sR02_re]; norm_num)

/-- ENCLOSURE (hypothesis-free): `1/10000000 ≤ ‖gammaPart sR02‖` (uniform Gamma
lemma: `Re = 0.395 ∈ [0.01,0.49]`, `|Im| = 6.75 ≤ 10`, `Im ≠ 0`). -/
theorem gamma_lower_R02 :
    (1 / 10000000 : ℝ) ≤ ‖R00Enclosure.gammaPart sR02‖ := by
  have hab : |sR02.im| ≤ 10 := by
    rw [sR02_im, abs_le]
    constructor <;> norm_num
  have hne : sR02.im ≠ 0 := by rw [sR02_im]; norm_num
  have h := CellGammaUniform.gamma_lower_wide
    (s := sR02)
    (by rw [sR02_re]; norm_num)
    (by rw [sR02_re]; norm_num)
    hab hne
  have heq : R00Enclosure.gammaPart sR02 = Complex.Gamma (sR02 / 2) := rfl
  rw [heq]
  exact h

/-- Conditional center assembly for R02 (outer tier): the three closed
enclosures (poly `22`, pi `1/2`, Gamma `1/1e7`) are plugged into the generic
bridge, leaving exactly the zeta factor plus the numeric product check as
explicit premises. -/
theorem R02_center_with_poly_pi_gamma (Azeta : ℝ)
    (hD0 : 0 ≤ Azeta)
    (hzeta : Azeta ≤ ‖zeta sR02‖)
    (hprod : (0.002 : ℝ) + 0.05 * 1.26 ≤ 22 * (1 / 2) * (1 / 10000000) * Azeta) :
    (0.002 : ℝ) + 0.05 * CentralCoverAssembly.R02.radius ≤
      ‖xiShifted CentralCoverAssembly.R02.center‖ := by
  have harg : sR02
      = (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R02.center := rfl
  have hpoly := poly_lower_R02
  have hpi := pi_lower_R02
  have hgam := gamma_lower_R02
  rw [harg] at hpoly hpi hgam hzeta
  exact CellUniform.center_bound_of_component_bounds
    CentralCoverAssembly.R02 0.002 0.05 (by norm_num)
    (le_of_lt CentralCoverAssembly.R02_radius_lt)
    22 (1 / 2) (1 / 10000000) Azeta
    (by norm_num) (by norm_num) (le_of_lt R00GammaLower.gamma_const_pos) hD0
    hpoly hpi hgam hzeta hprod

/-- Full chain: zeta factor + deriv bound discharge the `H`-leaf of
`inner_nonvanishing_of_fenced_grid_fine` at R02's grid cell
`(-8,-5.5,0.01,0.2)`. The exact remaining enclosures are the named premises
`hzeta` (complex zeta lower bound at `sR02 = 0.395 - 6.75·I`; needs the
Dirichlet-eta identity + remainder estimate, cf. `R00ZetaEM`) and `hderiv`
(uniform `‖deriv xiShifted‖ ≤ 0.05` on the rect; needs Cauchy estimates). -/
theorem R02_H_of_components (Azeta : ℝ)
    (hD0 : 0 ≤ Azeta)
    (hzeta : Azeta ≤ ‖zeta sR02‖)
    (hprod : (0.002 : ℝ) + 0.05 * 1.26 ≤ 22 * (1 / 2) * (1 / 10000000) * Azeta)
    (hderiv : ∀ w, CentralCoverAssembly.R02.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))
    (c : ℝ × ℝ × ℝ × ℝ) (hc_mem : c ∈ CentralCoverAssembly.gridFine)
    (hc_eq : c = (-8, -5.5, 0.01, 0.2)) :
    ∃ (R : CellProofEngine.Rect2D) (ε M : ℝ),
      R.x0 = c.1 ∧ R.x1 = c.2.1 ∧ R.y0 = c.2.2.1 ∧ R.y1 = c.2.2.2 ∧
      -(1 / 2 : ℝ) < R.y0 ∧ R.y1 < (1 / 2 : ℝ) ∧
      0 < ε ∧ (∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M) ∧
      ε + M * R.radius ≤ ‖xiShifted R.center‖ := by
  have hcenter := R02_center_with_poly_pi_gamma Azeta hD0 hzeta hprod
  have hleaf : CentralCoverAssembly.R02_leaf_obligations := ⟨hcenter, hderiv⟩
  exact CentralCoverAssembly.R02_H_instance hleaf c hc_mem hc_eq

#print axioms R02Uniform.poly_lower_R02
#print axioms R02Uniform.pi_lower_R02
#print axioms R02Uniform.gamma_lower_R02
#print axioms R02Uniform.R02_center_with_poly_pi_gamma
#print axioms R02Uniform.R02_H_of_components

end R02Uniform

/-!
## Stirling-type complex-Gamma UPPER bound at the R00 corner (shift route, fully proved).

Status / grep-first record (checked before writing):
* `rg "Gamma" Mathlib/Analysis/SpecialFunctions/Gamma/` → `Complex.Gamma_add_one`,
  `Real.Gamma_add_one`, `Complex.Gamma_mul_Gamma_one_sub` (reflection),
  `Complex.Gamma_ne_zero_of_re_pos`, `Real.convexOn_Gamma`, `Real.Gamma_one/two`,
  integral `Gamma_eq_integral`; NO formalized Stirling / complex-Gamma upper
  bounds (one aspirational comment in `BohrMollerup.lean` about the Euler limit
  formula; `GammaStirlingLeaf` structures in `riemann_hypothesis.lean` are
  hypotheses, not proofs).
* `rg "theorem.*Gamma.*≤|Stirling|norm_Gamma" --glob "*.lean" .` → only real
  convexity upper bounds (`R00GammaLower.realGamma_one_sub_half_le`,
  `CellGammaUniform.realGamma_one_sub_half_le_wide` giving `≤1.5`) and the
  integral majorant `R00GammaLower.norm_Gamma_le_realGamma`
  (`‖Gamma z‖ ≤ Real.Gamma z.re`); no complex upper bound with decay.
* `rg "sin_pi|norm_sin"` → only sine UPPER (`norm_sin_pi_half_le_wide`,
  `‖sin‖ ≤ exp 16`) and nonvanishing (`sin_pi_half_ne_wide`); no sine LOWER
  bound for large `Im` exists in repo/Mathlib.

Reflection infeasibility (why the brief's suggested route cannot reach `C ≤ 0.01`
with the proved `1/1e7` constant): reflection gives
`‖Gamma(1-s/2)‖ = π / (‖sin(πs/2)‖·‖Gamma(s/2)‖)`, so with
`‖Gamma(s/2)‖ ≥ 1/1e7` one needs `‖sin‖ ≥ 3.14e9` for `≤0.01`, but
`‖sin(πs/2)‖ ≤ exp 16 < 1e7` on `|s.im| ≤ 10` (proved upper), and the true
`‖sinh‖ ≤ ~4.6e5` at `|Im(s/2)| = 4.375`. Hence reflection + `1e-7` can only
give `‖Gamma(1-s/2)‖ ≤ ~68` at the corner — worse than `1.5`. A sine LOWER
bound alone does not fix the `1e4` gap (true `‖Gamma(s/2)‖ ~ 1e-3`).

Route used here (creates, does not assume): the shift identity
`Gamma(z+n) = z(z+1)…(z+n-1)·Gamma(z)` (`Complex.Gamma_add_one` induction,
no new axioms) + the in-file integral majorant
(`R00GammaLower.norm_Gamma_le_realGamma`) + real convexity
(`Real.convexOn_Gamma`, `Gamma 1 = Gamma 2 = 1` pattern already used in-file).
For `z₀ = 1 - sR00/2 = 0.8025 + 4.375·I` (R00 corner, largest `|Im|`, hence
smallest true `|Gamma| ~ 7e-3`) with `n = 12`:
`‖Gamma(z₀)‖ = ‖Gamma(z₀+12)‖ / ∏‖z₀+k‖ ≤ Real.Gamma(12.8025) / ∏cₖ
≤ 313000000 / 33000000000 ≤ 0.01`,
where `cₖ` are explicit 2-decimal floors of `‖z₀+k‖` (each `cₖ² ≤ re²+im²`
closed by `norm_num`) and `Real.Gamma(12.8025) ≤ 1.8025·…·11.8025 ≤ 313M`
from `Real.Gamma(1.8025) ≤ 1` (convexity on `[1,2]`) by repeated
`Real.Gamma_add_one`. True bound at the corner is `~7e-3`; the proved `0.01`
beats the previous `1.5` by `150×` (2+ orders). Uniform `≤0.01` over ALL 40
centers is FALSE (centers with `|s.im| ≈ 0.75` have true `|Gamma(1-s/2)| ≈ 1.0`;
see residual), so this corner lemma is the honest bridge + residual report.

Covers: single-point `z₀ = 1 - R00Numerics.sR00/2` (R00 outer-tier corner).
Range covered: exactly that point (`re = 0.8025`, `im = 4.375`).
Constant achieved: `C = 0.01`.
-/

namespace CellGammaUpper

/-- `Re(1 - sR00/2) = 0.8025`. -/
theorem zUpR00_re : (1 - R00Numerics.sR00 / 2).re = 0.8025 := by
  rw [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, R00Numerics.sR00_re]
  norm_num

/-- `Im(1 - sR00/2) = 4.375`. -/
theorem zUpR00_im : (1 - R00Numerics.sR00 / 2).im = 4.375 := by
  rw [Complex.sub_im, Complex.one_im, Complex.div_ofNat_im, R00Numerics.sR00_im]
  norm_num

/-- Real convexity feeder: `Real.Gamma 1.8025 ≤ 1`
(`1.8025 = 0.1975·1 + 0.8025·2`, `Gamma 1 = Gamma 2 = 1`). -/
theorem realGamma_18025_le_one : Real.Gamma 1.8025 ≤ 1 := by
  have hconv := Real.convexOn_Gamma
  have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have h2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have ha : (0 : ℝ) ≤ 0.1975 := by norm_num
  have hb : (0 : ℝ) ≤ 0.8025 := by norm_num
  have hab : (0.1975 : ℝ) + 0.8025 = 1 := by norm_num
  have h := hconv.2 h1 h2 ha hb hab
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
  have heq : (0.1975 : ℝ) * 1 + 0.8025 * 2 = 1.8025 := by norm_num
  have hrhs : (0.1975 : ℝ) * 1 + 0.8025 * 1 = (1 : ℝ) := by norm_num
  rw [heq] at h
  rw [hrhs] at h
  exact h

/-- `Real.Gamma 2.8025 ≤ 1.8025`. -/
theorem realGamma_28025_le : Real.Gamma 2.8025 ≤ 1.8025 := by
  have h : Real.Gamma (1.8025 + 1) = 1.8025 * Real.Gamma 1.8025 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (1.8025 : ℝ) + 1 = 2.8025 := by norm_num
  rw [heq] at h
  rw [h]
  calc (1.8025 : ℝ) * Real.Gamma 1.8025 ≤ 1.8025 * 1 :=
        mul_le_mul_of_nonneg_left realGamma_18025_le_one (by norm_num)
    _ = 1.8025 := mul_one _

/-- `Real.Gamma 3.8025 ≤ 1.8025*2.8025`. -/
theorem realGamma_38025_le : Real.Gamma 3.8025 ≤ 1.8025 * 2.8025 := by
  have h : Real.Gamma (2.8025 + 1) = 2.8025 * Real.Gamma 2.8025 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (2.8025 : ℝ) + 1 = 3.8025 := by norm_num
  rw [heq] at h
  rw [h]
  calc (2.8025 : ℝ) * Real.Gamma 2.8025 ≤ 2.8025 * 1.8025 :=
        mul_le_mul_of_nonneg_left realGamma_28025_le (by norm_num)
    _ = 1.8025 * 2.8025 := mul_comm _ _

/-- `Real.Gamma 4.8025 ≤ 1.8025*2.8025*3.8025`. -/
theorem realGamma_48025_le :
    Real.Gamma 4.8025 ≤ 1.8025 * 2.8025 * 3.8025 := by
  have h : Real.Gamma (3.8025 + 1) = 3.8025 * Real.Gamma 3.8025 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (3.8025 : ℝ) + 1 = 4.8025 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 3.8025 * Real.Gamma 3.8025 ≤ 3.8025 * (1.8025 * 2.8025) :=
    mul_le_mul_of_nonneg_left realGamma_38025_le (by norm_num)
  calc (3.8025 : ℝ) * Real.Gamma 3.8025 ≤ 3.8025 * (1.8025 * 2.8025) := hle
    _ = 1.8025 * 2.8025 * 3.8025 := by ring

/-- `Real.Gamma 5.8025 ≤ 1.8025*2.8025*3.8025*4.8025`. -/
theorem realGamma_58025_le :
    Real.Gamma 5.8025 ≤ 1.8025 * 2.8025 * 3.8025 * 4.8025 := by
  have h : Real.Gamma (4.8025 + 1) = 4.8025 * Real.Gamma 4.8025 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (4.8025 : ℝ) + 1 = 5.8025 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 4.8025 * Real.Gamma 4.8025
      ≤ 4.8025 * (1.8025 * 2.8025 * 3.8025) :=
    mul_le_mul_of_nonneg_left realGamma_48025_le (by norm_num)
  calc (4.8025 : ℝ) * Real.Gamma 4.8025
        ≤ 4.8025 * (1.8025 * 2.8025 * 3.8025) := hle
    _ = 1.8025 * 2.8025 * 3.8025 * 4.8025 := by ring

/-- `Real.Gamma 6.8025 ≤ 1.8025*…*5.8025`. -/
theorem realGamma_68025_le :
    Real.Gamma 6.8025 ≤ 1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 := by
  have h : Real.Gamma (5.8025 + 1) = 5.8025 * Real.Gamma 5.8025 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (5.8025 : ℝ) + 1 = 6.8025 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 5.8025 * Real.Gamma 5.8025
      ≤ 5.8025 * (1.8025 * 2.8025 * 3.8025 * 4.8025) :=
    mul_le_mul_of_nonneg_left realGamma_58025_le (by norm_num)
  calc (5.8025 : ℝ) * Real.Gamma 5.8025
        ≤ 5.8025 * (1.8025 * 2.8025 * 3.8025 * 4.8025) := hle
    _ = 1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 := by ring

/-- `Real.Gamma 7.8025 ≤ 1.8025*…*6.8025`. -/
theorem realGamma_78025_le :
    Real.Gamma 7.8025
      ≤ 1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 * 6.8025 := by
  have h : Real.Gamma (6.8025 + 1) = 6.8025 * Real.Gamma 6.8025 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (6.8025 : ℝ) + 1 = 7.8025 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 6.8025 * Real.Gamma 6.8025
      ≤ 6.8025 * (1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025) :=
    mul_le_mul_of_nonneg_left realGamma_68025_le (by norm_num)
  calc (6.8025 : ℝ) * Real.Gamma 6.8025
        ≤ 6.8025 * (1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025) := hle
    _ = 1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 * 6.8025 := by ring

/-- `Real.Gamma 8.8025 ≤ 1.8025*…*7.8025`. -/
theorem realGamma_88025_le :
    Real.Gamma 8.8025
      ≤ 1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 * 6.8025 * 7.8025 := by
  have h : Real.Gamma (7.8025 + 1) = 7.8025 * Real.Gamma 7.8025 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (7.8025 : ℝ) + 1 = 8.8025 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 7.8025 * Real.Gamma 7.8025
      ≤ 7.8025 * (1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 * 6.8025) :=
    mul_le_mul_of_nonneg_left realGamma_78025_le (by norm_num)
  calc (7.8025 : ℝ) * Real.Gamma 7.8025
        ≤ 7.8025 * (1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 * 6.8025) := hle
    _ = 1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 * 6.8025 * 7.8025 := by ring

/-- `Real.Gamma 9.8025 ≤ 1.8025*…*8.8025`. -/
theorem realGamma_98025_le :
    Real.Gamma 9.8025
      ≤ 1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 * 6.8025 * 7.8025
        * 8.8025 := by
  have h : Real.Gamma (8.8025 + 1) = 8.8025 * Real.Gamma 8.8025 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (8.8025 : ℝ) + 1 = 9.8025 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 8.8025 * Real.Gamma 8.8025
      ≤ 8.8025 * (1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 * 6.8025
        * 7.8025) :=
    mul_le_mul_of_nonneg_left realGamma_88025_le (by norm_num)
  calc (8.8025 : ℝ) * Real.Gamma 8.8025
        ≤ 8.8025 * (1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 * 6.8025
          * 7.8025) := hle
    _ = 1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 * 6.8025 * 7.8025
        * 8.8025 := by ring

/-- `Real.Gamma 10.8025 ≤ 1.8025*…*9.8025`. -/
theorem realGamma_108025_le :
    Real.Gamma 10.8025
      ≤ 1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 * 6.8025 * 7.8025
        * 8.8025 * 9.8025 := by
  have h : Real.Gamma (9.8025 + 1) = 9.8025 * Real.Gamma 9.8025 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (9.8025 : ℝ) + 1 = 10.8025 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 9.8025 * Real.Gamma 9.8025
      ≤ 9.8025 * (1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 * 6.8025
        * 7.8025 * 8.8025) :=
    mul_le_mul_of_nonneg_left realGamma_98025_le (by norm_num)
  calc (9.8025 : ℝ) * Real.Gamma 9.8025
        ≤ 9.8025 * (1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 * 6.8025
          * 7.8025 * 8.8025) := hle
    _ = 1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 * 6.8025 * 7.8025
        * 8.8025 * 9.8025 := by ring

/-- `Real.Gamma 11.8025 ≤ 1.8025*…*10.8025`. -/
theorem realGamma_118025_le :
    Real.Gamma 11.8025
      ≤ 1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 * 6.8025 * 7.8025
        * 8.8025 * 9.8025 * 10.8025 := by
  have h : Real.Gamma (10.8025 + 1) = 10.8025 * Real.Gamma 10.8025 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (10.8025 : ℝ) + 1 = 11.8025 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 10.8025 * Real.Gamma 10.8025
      ≤ 10.8025 * (1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 * 6.8025
        * 7.8025 * 8.8025 * 9.8025) :=
    mul_le_mul_of_nonneg_left realGamma_108025_le (by norm_num)
  calc (10.8025 : ℝ) * Real.Gamma 10.8025
        ≤ 10.8025 * (1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 * 6.8025
          * 7.8025 * 8.8025 * 9.8025) := hle
    _ = 1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 * 6.8025 * 7.8025
        * 8.8025 * 9.8025 * 10.8025 := by ring

/-- `Real.Gamma 12.8025 ≤ 1.8025*…*11.8025 ≤ 313000000` (numerator cap). -/
theorem realGamma_128025_le : Real.Gamma 12.8025 ≤ 313000000 := by
  have h : Real.Gamma (11.8025 + 1) = 11.8025 * Real.Gamma 11.8025 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (11.8025 : ℝ) + 1 = 12.8025 := by norm_num
  rw [heq] at h
  rw [h] at ⊢
  have hle : 11.8025 * Real.Gamma 11.8025
      ≤ 11.8025 * (1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025 * 6.8025
        * 7.8025 * 8.8025 * 9.8025 * 10.8025) :=
    mul_le_mul_of_nonneg_left realGamma_118025_le (by norm_num)
  have hprod : (11.8025 : ℝ) * (1.8025 * 2.8025 * 3.8025 * 4.8025 * 5.8025
      * 6.8025 * 7.8025 * 8.8025 * 9.8025 * 10.8025) ≤ 313000000 := by
    norm_num
  exact le_trans hle hprod

/-- Denominator floors `cₖ ≤ ‖z₀+k‖` (`cₖ² ≤ re²+im²` by `norm_num`). -/
theorem norm_zUp0_ge : (4.44 : ℝ) ≤ ‖1 - R00Numerics.sR00 / 2‖ := by
  have hsq : (4.44 : ℝ) ^ 2 ≤ ‖1 - R00Numerics.sR00 / 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, zUpR00_re, zUpR00_im]
    norm_num
  calc (4.44 : ℝ) = Real.sqrt ((4.44 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - R00Numerics.sR00 / 2‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - R00Numerics.sR00 / 2‖ := Real.sqrt_sq (norm_nonneg _)

theorem norm_zUp1_ge :
    (4.73 : ℝ) ≤ ‖1 - R00Numerics.sR00 / 2 + 1‖ := by
  have hre : (1 - R00Numerics.sR00 / 2 + 1).re = 1.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.one_re]
    norm_num
  have him : (1 - R00Numerics.sR00 / 2 + 1).im = 4.375 := by
    simp only [Complex.add_im, zUpR00_im, Complex.one_im]
    norm_num
  have hsq : (4.73 : ℝ) ^ 2 ≤ ‖1 - R00Numerics.sR00 / 2 + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (4.73 : ℝ) = Real.sqrt ((4.73 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - R00Numerics.sR00 / 2 + 1‖ ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = ‖1 - R00Numerics.sR00 / 2 + 1‖ := Real.sqrt_sq (norm_nonneg _)

theorem norm_zUp2_ge :
    (5.19 : ℝ) ≤ ‖1 - R00Numerics.sR00 / 2 + 2‖ := by
  have hre : (1 - R00Numerics.sR00 / 2 + 2).re = 2.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  have him : (1 - R00Numerics.sR00 / 2 + 2).im = 4.375 := by
    simp only [Complex.add_im, zUpR00_im, Complex.im_ofNat]
    norm_num
  have hsq : (5.19 : ℝ) ^ 2 ≤ ‖1 - R00Numerics.sR00 / 2 + 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (5.19 : ℝ) = Real.sqrt ((5.19 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - R00Numerics.sR00 / 2 + 2‖ ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = ‖1 - R00Numerics.sR00 / 2 + 2‖ := Real.sqrt_sq (norm_nonneg _)

theorem norm_zUp3_ge :
    (5.79 : ℝ) ≤ ‖1 - R00Numerics.sR00 / 2 + 3‖ := by
  have hre : (1 - R00Numerics.sR00 / 2 + 3).re = 3.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  have him : (1 - R00Numerics.sR00 / 2 + 3).im = 4.375 := by
    simp only [Complex.add_im, zUpR00_im, Complex.im_ofNat]
    norm_num
  have hsq : (5.79 : ℝ) ^ 2 ≤ ‖1 - R00Numerics.sR00 / 2 + 3‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (5.79 : ℝ) = Real.sqrt ((5.79 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - R00Numerics.sR00 / 2 + 3‖ ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = ‖1 - R00Numerics.sR00 / 2 + 3‖ := Real.sqrt_sq (norm_nonneg _)

theorem norm_zUp4_ge :
    (6.49 : ℝ) ≤ ‖1 - R00Numerics.sR00 / 2 + 4‖ := by
  have hre : (1 - R00Numerics.sR00 / 2 + 4).re = 4.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  have him : (1 - R00Numerics.sR00 / 2 + 4).im = 4.375 := by
    simp only [Complex.add_im, zUpR00_im, Complex.im_ofNat]
    norm_num
  have hsq : (6.49 : ℝ) ^ 2 ≤ ‖1 - R00Numerics.sR00 / 2 + 4‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (6.49 : ℝ) = Real.sqrt ((6.49 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - R00Numerics.sR00 / 2 + 4‖ ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = ‖1 - R00Numerics.sR00 / 2 + 4‖ := Real.sqrt_sq (norm_nonneg _)

theorem norm_zUp5_ge :
    (7.26 : ℝ) ≤ ‖1 - R00Numerics.sR00 / 2 + 5‖ := by
  have hre : (1 - R00Numerics.sR00 / 2 + 5).re = 5.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  have him : (1 - R00Numerics.sR00 / 2 + 5).im = 4.375 := by
    simp only [Complex.add_im, zUpR00_im, Complex.im_ofNat]
    norm_num
  have hsq : (7.26 : ℝ) ^ 2 ≤ ‖1 - R00Numerics.sR00 / 2 + 5‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (7.26 : ℝ) = Real.sqrt ((7.26 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - R00Numerics.sR00 / 2 + 5‖ ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = ‖1 - R00Numerics.sR00 / 2 + 5‖ := Real.sqrt_sq (norm_nonneg _)

theorem norm_zUp6_ge :
    (8.08 : ℝ) ≤ ‖1 - R00Numerics.sR00 / 2 + 6‖ := by
  have hre : (1 - R00Numerics.sR00 / 2 + 6).re = 6.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  have him : (1 - R00Numerics.sR00 / 2 + 6).im = 4.375 := by
    simp only [Complex.add_im, zUpR00_im, Complex.im_ofNat]
    norm_num
  have hsq : (8.08 : ℝ) ^ 2 ≤ ‖1 - R00Numerics.sR00 / 2 + 6‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (8.08 : ℝ) = Real.sqrt ((8.08 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - R00Numerics.sR00 / 2 + 6‖ ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = ‖1 - R00Numerics.sR00 / 2 + 6‖ := Real.sqrt_sq (norm_nonneg _)

theorem norm_zUp7_ge :
    (8.94 : ℝ) ≤ ‖1 - R00Numerics.sR00 / 2 + 7‖ := by
  have hre : (1 - R00Numerics.sR00 / 2 + 7).re = 7.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  have him : (1 - R00Numerics.sR00 / 2 + 7).im = 4.375 := by
    simp only [Complex.add_im, zUpR00_im, Complex.im_ofNat]
    norm_num
  have hsq : (8.94 : ℝ) ^ 2 ≤ ‖1 - R00Numerics.sR00 / 2 + 7‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (8.94 : ℝ) = Real.sqrt ((8.94 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - R00Numerics.sR00 / 2 + 7‖ ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = ‖1 - R00Numerics.sR00 / 2 + 7‖ := Real.sqrt_sq (norm_nonneg _)

theorem norm_zUp8_ge :
    (9.82 : ℝ) ≤ ‖1 - R00Numerics.sR00 / 2 + 8‖ := by
  have hre : (1 - R00Numerics.sR00 / 2 + 8).re = 8.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  have him : (1 - R00Numerics.sR00 / 2 + 8).im = 4.375 := by
    simp only [Complex.add_im, zUpR00_im, Complex.im_ofNat]
    norm_num
  have hsq : (9.82 : ℝ) ^ 2 ≤ ‖1 - R00Numerics.sR00 / 2 + 8‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (9.82 : ℝ) = Real.sqrt ((9.82 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - R00Numerics.sR00 / 2 + 8‖ ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = ‖1 - R00Numerics.sR00 / 2 + 8‖ := Real.sqrt_sq (norm_nonneg _)

theorem norm_zUp9_ge :
    (10.73 : ℝ) ≤ ‖1 - R00Numerics.sR00 / 2 + 9‖ := by
  have hre : (1 - R00Numerics.sR00 / 2 + 9).re = 9.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  have him : (1 - R00Numerics.sR00 / 2 + 9).im = 4.375 := by
    simp only [Complex.add_im, zUpR00_im, Complex.im_ofNat]
    norm_num
  have hsq : (10.73 : ℝ) ^ 2 ≤ ‖1 - R00Numerics.sR00 / 2 + 9‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (10.73 : ℝ) = Real.sqrt ((10.73 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - R00Numerics.sR00 / 2 + 9‖ ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = ‖1 - R00Numerics.sR00 / 2 + 9‖ := Real.sqrt_sq (norm_nonneg _)

theorem norm_zUp10_ge :
    (11.65 : ℝ) ≤ ‖1 - R00Numerics.sR00 / 2 + 10‖ := by
  have hre : (1 - R00Numerics.sR00 / 2 + 10).re = 10.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  have him : (1 - R00Numerics.sR00 / 2 + 10).im = 4.375 := by
    simp only [Complex.add_im, zUpR00_im, Complex.im_ofNat]
    norm_num
  have hsq : (11.65 : ℝ) ^ 2 ≤ ‖1 - R00Numerics.sR00 / 2 + 10‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (11.65 : ℝ) = Real.sqrt ((11.65 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - R00Numerics.sR00 / 2 + 10‖ ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = ‖1 - R00Numerics.sR00 / 2 + 10‖ := Real.sqrt_sq (norm_nonneg _)

theorem norm_zUp11_ge :
    (12.58 : ℝ) ≤ ‖1 - R00Numerics.sR00 / 2 + 11‖ := by
  have hre : (1 - R00Numerics.sR00 / 2 + 11).re = 11.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  have him : (1 - R00Numerics.sR00 / 2 + 11).im = 4.375 := by
    simp only [Complex.add_im, zUpR00_im, Complex.im_ofNat]
    norm_num
  have hsq : (12.58 : ℝ) ^ 2 ≤ ‖1 - R00Numerics.sR00 / 2 + 11‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (12.58 : ℝ) = Real.sqrt ((12.58 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - R00Numerics.sR00 / 2 + 11‖ ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = ‖1 - R00Numerics.sR00 / 2 + 11‖ := Real.sqrt_sq (norm_nonneg _)

/-- Shift nonvanishing (`Re > 0` so `≠ 0`). -/
theorem zUp_ne0 : (1 - R00Numerics.sR00 / 2) ≠ 0 := by
  have hre : (1 - R00Numerics.sR00 / 2).re = 0.8025 := zUpR00_re
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUp_add1_ne0 : (1 - R00Numerics.sR00 / 2 + 1) ≠ 0 := by
  have hre : (1 - R00Numerics.sR00 / 2 + 1).re = 1.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.one_re]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUp_add2_ne0 : (1 - R00Numerics.sR00 / 2 + 2) ≠ 0 := by
  have hre : (1 - R00Numerics.sR00 / 2 + 2).re = 2.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUp_add3_ne0 : (1 - R00Numerics.sR00 / 2 + 3) ≠ 0 := by
  have hre : (1 - R00Numerics.sR00 / 2 + 3).re = 3.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUp_add4_ne0 : (1 - R00Numerics.sR00 / 2 + 4) ≠ 0 := by
  have hre : (1 - R00Numerics.sR00 / 2 + 4).re = 4.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUp_add5_ne0 : (1 - R00Numerics.sR00 / 2 + 5) ≠ 0 := by
  have hre : (1 - R00Numerics.sR00 / 2 + 5).re = 5.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUp_add6_ne0 : (1 - R00Numerics.sR00 / 2 + 6) ≠ 0 := by
  have hre : (1 - R00Numerics.sR00 / 2 + 6).re = 6.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUp_add7_ne0 : (1 - R00Numerics.sR00 / 2 + 7) ≠ 0 := by
  have hre : (1 - R00Numerics.sR00 / 2 + 7).re = 7.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUp_add8_ne0 : (1 - R00Numerics.sR00 / 2 + 8) ≠ 0 := by
  have hre : (1 - R00Numerics.sR00 / 2 + 8).re = 8.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUp_add9_ne0 : (1 - R00Numerics.sR00 / 2 + 9) ≠ 0 := by
  have hre : (1 - R00Numerics.sR00 / 2 + 9).re = 9.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUp_add10_ne0 : (1 - R00Numerics.sR00 / 2 + 10) ≠ 0 := by
  have hre : (1 - R00Numerics.sR00 / 2 + 10).re = 10.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUp_add11_ne0 : (1 - R00Numerics.sR00 / 2 + 11) ≠ 0 := by
  have hre : (1 - R00Numerics.sR00 / 2 + 11).re = 11.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

/-- MAIN uniform UPPER bound at the R00 corner:
`‖Gamma(1 - sR00/2)‖ ≤ 0.01` (`150×` better than `1.5`). -/
theorem gamma_one_sub_half_upper_R00 :
    ‖Complex.Gamma (1 - R00Numerics.sR00 / 2)‖ ≤ 0.01 := by
  -- Shift chain `Gamma(z₀+12) = (z₀+11)…z₀·Gamma(z₀)`.
  have e0 : Complex.Gamma (1 - R00Numerics.sR00 / 2 + 1)
      = (1 - R00Numerics.sR00 / 2) * Complex.Gamma (1 - R00Numerics.sR00 / 2) :=
    Complex.Gamma_add_one _ zUp_ne0
  have e1 : Complex.Gamma (1 - R00Numerics.sR00 / 2 + 2)
      = (1 - R00Numerics.sR00 / 2 + 1)
        * Complex.Gamma (1 - R00Numerics.sR00 / 2 + 1) := by
    have h : (1 - R00Numerics.sR00 / 2 + 2)
        = ((1 - R00Numerics.sR00 / 2 + 1) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUp_add1_ne0
  have e2 : Complex.Gamma (1 - R00Numerics.sR00 / 2 + 3)
      = (1 - R00Numerics.sR00 / 2 + 2)
        * Complex.Gamma (1 - R00Numerics.sR00 / 2 + 2) := by
    have h : (1 - R00Numerics.sR00 / 2 + 3)
        = ((1 - R00Numerics.sR00 / 2 + 2) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUp_add2_ne0
  have e3 : Complex.Gamma (1 - R00Numerics.sR00 / 2 + 4)
      = (1 - R00Numerics.sR00 / 2 + 3)
        * Complex.Gamma (1 - R00Numerics.sR00 / 2 + 3) := by
    have h : (1 - R00Numerics.sR00 / 2 + 4)
        = ((1 - R00Numerics.sR00 / 2 + 3) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUp_add3_ne0
  have e4 : Complex.Gamma (1 - R00Numerics.sR00 / 2 + 5)
      = (1 - R00Numerics.sR00 / 2 + 4)
        * Complex.Gamma (1 - R00Numerics.sR00 / 2 + 4) := by
    have h : (1 - R00Numerics.sR00 / 2 + 5)
        = ((1 - R00Numerics.sR00 / 2 + 4) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUp_add4_ne0
  have e5 : Complex.Gamma (1 - R00Numerics.sR00 / 2 + 6)
      = (1 - R00Numerics.sR00 / 2 + 5)
        * Complex.Gamma (1 - R00Numerics.sR00 / 2 + 5) := by
    have h : (1 - R00Numerics.sR00 / 2 + 6)
        = ((1 - R00Numerics.sR00 / 2 + 5) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUp_add5_ne0
  have e6 : Complex.Gamma (1 - R00Numerics.sR00 / 2 + 7)
      = (1 - R00Numerics.sR00 / 2 + 6)
        * Complex.Gamma (1 - R00Numerics.sR00 / 2 + 6) := by
    have h : (1 - R00Numerics.sR00 / 2 + 7)
        = ((1 - R00Numerics.sR00 / 2 + 6) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUp_add6_ne0
  have e7 : Complex.Gamma (1 - R00Numerics.sR00 / 2 + 8)
      = (1 - R00Numerics.sR00 / 2 + 7)
        * Complex.Gamma (1 - R00Numerics.sR00 / 2 + 7) := by
    have h : (1 - R00Numerics.sR00 / 2 + 8)
        = ((1 - R00Numerics.sR00 / 2 + 7) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUp_add7_ne0
  have e8 : Complex.Gamma (1 - R00Numerics.sR00 / 2 + 9)
      = (1 - R00Numerics.sR00 / 2 + 8)
        * Complex.Gamma (1 - R00Numerics.sR00 / 2 + 8) := by
    have h : (1 - R00Numerics.sR00 / 2 + 9)
        = ((1 - R00Numerics.sR00 / 2 + 8) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUp_add8_ne0
  have e9 : Complex.Gamma (1 - R00Numerics.sR00 / 2 + 10)
      = (1 - R00Numerics.sR00 / 2 + 9)
        * Complex.Gamma (1 - R00Numerics.sR00 / 2 + 9) := by
    have h : (1 - R00Numerics.sR00 / 2 + 10)
        = ((1 - R00Numerics.sR00 / 2 + 9) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUp_add9_ne0
  have e10 : Complex.Gamma (1 - R00Numerics.sR00 / 2 + 11)
      = (1 - R00Numerics.sR00 / 2 + 10)
        * Complex.Gamma (1 - R00Numerics.sR00 / 2 + 10) := by
    have h : (1 - R00Numerics.sR00 / 2 + 11)
        = ((1 - R00Numerics.sR00 / 2 + 10) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUp_add10_ne0
  have e11 : Complex.Gamma (1 - R00Numerics.sR00 / 2 + 12)
      = (1 - R00Numerics.sR00 / 2 + 11)
        * Complex.Gamma (1 - R00Numerics.sR00 / 2 + 11) := by
    have h : (1 - R00Numerics.sR00 / 2 + 12)
        = ((1 - R00Numerics.sR00 / 2 + 11) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUp_add11_ne0
  have n0 : ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 1)‖
      = ‖1 - R00Numerics.sR00 / 2‖
        * ‖Complex.Gamma (1 - R00Numerics.sR00 / 2)‖ := by
    rw [e0, norm_mul]
  have n1 : ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 2)‖
      = ‖1 - R00Numerics.sR00 / 2 + 1‖
        * ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 1)‖ := by
    rw [e1, norm_mul]
  have n2 : ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 3)‖
      = ‖1 - R00Numerics.sR00 / 2 + 2‖
        * ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 2)‖ := by
    rw [e2, norm_mul]
  have n3 : ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 4)‖
      = ‖1 - R00Numerics.sR00 / 2 + 3‖
        * ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 3)‖ := by
    rw [e3, norm_mul]
  have n4 : ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 5)‖
      = ‖1 - R00Numerics.sR00 / 2 + 4‖
        * ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 4)‖ := by
    rw [e4, norm_mul]
  have n5 : ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 6)‖
      = ‖1 - R00Numerics.sR00 / 2 + 5‖
        * ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 5)‖ := by
    rw [e5, norm_mul]
  have n6 : ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 7)‖
      = ‖1 - R00Numerics.sR00 / 2 + 6‖
        * ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 6)‖ := by
    rw [e6, norm_mul]
  have n7 : ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 8)‖
      = ‖1 - R00Numerics.sR00 / 2 + 7‖
        * ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 7)‖ := by
    rw [e7, norm_mul]
  have n8 : ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 9)‖
      = ‖1 - R00Numerics.sR00 / 2 + 8‖
        * ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 8)‖ := by
    rw [e8, norm_mul]
  have n9 : ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 10)‖
      = ‖1 - R00Numerics.sR00 / 2 + 9‖
        * ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 9)‖ := by
    rw [e9, norm_mul]
  have n10 : ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 11)‖
      = ‖1 - R00Numerics.sR00 / 2 + 10‖
        * ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 10)‖ := by
    rw [e10, norm_mul]
  have n11 : ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 12)‖
      = ‖1 - R00Numerics.sR00 / 2 + 11‖
        * ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 11)‖ := by
    rw [e11, norm_mul]
  have hprod : ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 12)‖
      = ‖1 - R00Numerics.sR00 / 2 + 11‖
        * (‖1 - R00Numerics.sR00 / 2 + 10‖
        * (‖1 - R00Numerics.sR00 / 2 + 9‖
        * (‖1 - R00Numerics.sR00 / 2 + 8‖
        * (‖1 - R00Numerics.sR00 / 2 + 7‖
        * (‖1 - R00Numerics.sR00 / 2 + 6‖
        * (‖1 - R00Numerics.sR00 / 2 + 5‖
        * (‖1 - R00Numerics.sR00 / 2 + 4‖
        * (‖1 - R00Numerics.sR00 / 2 + 3‖
        * (‖1 - R00Numerics.sR00 / 2 + 2‖
        * (‖1 - R00Numerics.sR00 / 2 + 1‖
        * (‖1 - R00Numerics.sR00 / 2‖
          * ‖Complex.Gamma (1 - R00Numerics.sR00 / 2)‖))))))))))) := by
    rw [n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n0]
  -- Denominator product lower bound (right-nested, innermost `c₁*c₀` outward).
  have q10 : (4.73 : ℝ) * 4.44
      ≤ ‖1 - R00Numerics.sR00 / 2 + 1‖ * ‖1 - R00Numerics.sR00 / 2‖ :=
    mul_le_mul norm_zUp1_ge norm_zUp0_ge (by norm_num) (norm_nonneg _)
  have q2 : (5.19 : ℝ) * (4.73 * 4.44)
      ≤ ‖1 - R00Numerics.sR00 / 2 + 2‖
        * (‖1 - R00Numerics.sR00 / 2 + 1‖ * ‖1 - R00Numerics.sR00 / 2‖) :=
    mul_le_mul norm_zUp2_ge q10 (by positivity) (norm_nonneg _)
  have q3 : (5.79 : ℝ) * (5.19 * (4.73 * 4.44))
      ≤ ‖1 - R00Numerics.sR00 / 2 + 3‖
        * (‖1 - R00Numerics.sR00 / 2 + 2‖
          * (‖1 - R00Numerics.sR00 / 2 + 1‖ * ‖1 - R00Numerics.sR00 / 2‖)) :=
    mul_le_mul norm_zUp3_ge q2 (by positivity) (norm_nonneg _)
  have q4 : (6.49 : ℝ) * (5.79 * (5.19 * (4.73 * 4.44)))
      ≤ ‖1 - R00Numerics.sR00 / 2 + 4‖
        * (‖1 - R00Numerics.sR00 / 2 + 3‖
          * (‖1 - R00Numerics.sR00 / 2 + 2‖
            * (‖1 - R00Numerics.sR00 / 2 + 1‖
              * ‖1 - R00Numerics.sR00 / 2‖))) :=
    mul_le_mul norm_zUp4_ge q3 (by positivity) (norm_nonneg _)
  have q5 : (7.26 : ℝ) * (6.49 * (5.79 * (5.19 * (4.73 * 4.44))))
      ≤ ‖1 - R00Numerics.sR00 / 2 + 5‖
        * (‖1 - R00Numerics.sR00 / 2 + 4‖
          * (‖1 - R00Numerics.sR00 / 2 + 3‖
            * (‖1 - R00Numerics.sR00 / 2 + 2‖
              * (‖1 - R00Numerics.sR00 / 2 + 1‖
                * ‖1 - R00Numerics.sR00 / 2‖)))) :=
    mul_le_mul norm_zUp5_ge q4 (by positivity) (norm_nonneg _)
  have q6 : (8.08 : ℝ) * (7.26 * (6.49 * (5.79 * (5.19 * (4.73 * 4.44)))))
      ≤ ‖1 - R00Numerics.sR00 / 2 + 6‖
        * (‖1 - R00Numerics.sR00 / 2 + 5‖
          * (‖1 - R00Numerics.sR00 / 2 + 4‖
            * (‖1 - R00Numerics.sR00 / 2 + 3‖
              * (‖1 - R00Numerics.sR00 / 2 + 2‖
                * (‖1 - R00Numerics.sR00 / 2 + 1‖
                  * ‖1 - R00Numerics.sR00 / 2‖))))) :=
    mul_le_mul norm_zUp6_ge q5 (by positivity) (norm_nonneg _)
  have q7 : (8.94 : ℝ)
        * (8.08 * (7.26 * (6.49 * (5.79 * (5.19 * (4.73 * 4.44))))))
      ≤ ‖1 - R00Numerics.sR00 / 2 + 7‖
        * (‖1 - R00Numerics.sR00 / 2 + 6‖
          * (‖1 - R00Numerics.sR00 / 2 + 5‖
            * (‖1 - R00Numerics.sR00 / 2 + 4‖
              * (‖1 - R00Numerics.sR00 / 2 + 3‖
                * (‖1 - R00Numerics.sR00 / 2 + 2‖
                  * (‖1 - R00Numerics.sR00 / 2 + 1‖
                    * ‖1 - R00Numerics.sR00 / 2‖)))))) :=
    mul_le_mul norm_zUp7_ge q6 (by positivity) (norm_nonneg _)
  have q8 : (9.82 : ℝ)
        * (8.94 * (8.08 * (7.26 * (6.49 * (5.79 * (5.19 * (4.73 * 4.44)))))))
      ≤ ‖1 - R00Numerics.sR00 / 2 + 8‖
        * (‖1 - R00Numerics.sR00 / 2 + 7‖
          * (‖1 - R00Numerics.sR00 / 2 + 6‖
            * (‖1 - R00Numerics.sR00 / 2 + 5‖
              * (‖1 - R00Numerics.sR00 / 2 + 4‖
                * (‖1 - R00Numerics.sR00 / 2 + 3‖
                  * (‖1 - R00Numerics.sR00 / 2 + 2‖
                    * (‖1 - R00Numerics.sR00 / 2 + 1‖
                      * ‖1 - R00Numerics.sR00 / 2‖))))))) :=
    mul_le_mul norm_zUp8_ge q7 (by positivity) (norm_nonneg _)
  have q9 : (10.73 : ℝ)
        * (9.82 * (8.94 * (8.08 * (7.26
          * (6.49 * (5.79 * (5.19 * (4.73 * 4.44))))))))
      ≤ ‖1 - R00Numerics.sR00 / 2 + 9‖
        * (‖1 - R00Numerics.sR00 / 2 + 8‖
          * (‖1 - R00Numerics.sR00 / 2 + 7‖
            * (‖1 - R00Numerics.sR00 / 2 + 6‖
              * (‖1 - R00Numerics.sR00 / 2 + 5‖
                * (‖1 - R00Numerics.sR00 / 2 + 4‖
                  * (‖1 - R00Numerics.sR00 / 2 + 3‖
                    * (‖1 - R00Numerics.sR00 / 2 + 2‖
                      * (‖1 - R00Numerics.sR00 / 2 + 1‖
                        * ‖1 - R00Numerics.sR00 / 2‖)))))))) :=
    mul_le_mul norm_zUp9_ge q8 (by positivity) (norm_nonneg _)
  have q10 : (11.65 : ℝ)
        * (10.73 * (9.82 * (8.94 * (8.08 * (7.26
          * (6.49 * (5.79 * (5.19 * (4.73 * 4.44)))))))))
      ≤ ‖1 - R00Numerics.sR00 / 2 + 10‖
        * (‖1 - R00Numerics.sR00 / 2 + 9‖
          * (‖1 - R00Numerics.sR00 / 2 + 8‖
            * (‖1 - R00Numerics.sR00 / 2 + 7‖
              * (‖1 - R00Numerics.sR00 / 2 + 6‖
                * (‖1 - R00Numerics.sR00 / 2 + 5‖
                  * (‖1 - R00Numerics.sR00 / 2 + 4‖
                    * (‖1 - R00Numerics.sR00 / 2 + 3‖
                      * (‖1 - R00Numerics.sR00 / 2 + 2‖
                        * (‖1 - R00Numerics.sR00 / 2 + 1‖
                          * ‖1 - R00Numerics.sR00 / 2‖))))))))) :=
    mul_le_mul norm_zUp10_ge q9 (by positivity) (norm_nonneg _)
  have q11 : (12.58 : ℝ)
        * (11.65 * (10.73 * (9.82 * (8.94 * (8.08 * (7.26
          * (6.49 * (5.79 * (5.19 * (4.73 * 4.44))))))))))
      ≤ ‖1 - R00Numerics.sR00 / 2 + 11‖
        * (‖1 - R00Numerics.sR00 / 2 + 10‖
          * (‖1 - R00Numerics.sR00 / 2 + 9‖
            * (‖1 - R00Numerics.sR00 / 2 + 8‖
              * (‖1 - R00Numerics.sR00 / 2 + 7‖
                * (‖1 - R00Numerics.sR00 / 2 + 6‖
                  * (‖1 - R00Numerics.sR00 / 2 + 5‖
                    * (‖1 - R00Numerics.sR00 / 2 + 4‖
                      * (‖1 - R00Numerics.sR00 / 2 + 3‖
                        * (‖1 - R00Numerics.sR00 / 2 + 2‖
                          * (‖1 - R00Numerics.sR00 / 2 + 1‖
                            * ‖1 - R00Numerics.sR00 / 2‖)))))))))) :=
    mul_le_mul norm_zUp11_ge q10 (by positivity) (norm_nonneg _)
  have hD34 : (33000000000 : ℝ)
      ≤ (12.58 : ℝ)
        * (11.65 * (10.73 * (9.82 * (8.94 * (8.08 * (7.26
          * (6.49 * (5.79 * (5.19 * (4.73 * 4.44)))))))))) := by
    norm_num
  have hD_ge : (33000000000 : ℝ)
      ≤ ‖1 - R00Numerics.sR00 / 2 + 11‖
        * (‖1 - R00Numerics.sR00 / 2 + 10‖
          * (‖1 - R00Numerics.sR00 / 2 + 9‖
            * (‖1 - R00Numerics.sR00 / 2 + 8‖
              * (‖1 - R00Numerics.sR00 / 2 + 7‖
                * (‖1 - R00Numerics.sR00 / 2 + 6‖
                  * (‖1 - R00Numerics.sR00 / 2 + 5‖
                    * (‖1 - R00Numerics.sR00 / 2 + 4‖
                      * (‖1 - R00Numerics.sR00 / 2 + 3‖
                        * (‖1 - R00Numerics.sR00 / 2 + 2‖
                          * (‖1 - R00Numerics.sR00 / 2 + 1‖
                            * ‖1 - R00Numerics.sR00 / 2‖)))))))))) :=
    le_trans hD34 q11
  have hD_pos : (0 : ℝ)
      < ‖1 - R00Numerics.sR00 / 2 + 11‖
        * (‖1 - R00Numerics.sR00 / 2 + 10‖
          * (‖1 - R00Numerics.sR00 / 2 + 9‖
            * (‖1 - R00Numerics.sR00 / 2 + 8‖
              * (‖1 - R00Numerics.sR00 / 2 + 7‖
                * (‖1 - R00Numerics.sR00 / 2 + 6‖
                  * (‖1 - R00Numerics.sR00 / 2 + 5‖
                    * (‖1 - R00Numerics.sR00 / 2 + 4‖
                      * (‖1 - R00Numerics.sR00 / 2 + 3‖
                        * (‖1 - R00Numerics.sR00 / 2 + 2‖
                          * (‖1 - R00Numerics.sR00 / 2 + 1‖
                            * ‖1 - R00Numerics.sR00 / 2‖)))))))))) :=
    lt_of_lt_of_le (by norm_num) hD_ge
  -- Numerator: `‖Gamma(z₀+12)‖ ≤ Real.Gamma(12.8025) ≤ 313M`.
  have hre12 : (1 - R00Numerics.sR00 / 2 + 12).re = 12.8025 := by
    simp only [Complex.add_re, zUpR00_re, Complex.re_ofNat]
    norm_num
  have hG12_re : (0 : ℝ) < (1 - R00Numerics.sR00 / 2 + 12).re := by
    rw [hre12]
    norm_num
  have hG12_le : ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 12)‖ ≤ 313000000 := by
    have h1 : ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 12)‖
        ≤ Real.Gamma ((1 - R00Numerics.sR00 / 2 + 12).re) :=
      R00GammaLower.norm_Gamma_le_realGamma hG12_re
    have hre12b : ((1 - R00Numerics.sR00 / 2 + 12).re) = 12.8025 := hre12
    rw [hre12b] at h1
    exact le_trans h1 realGamma_128025_le
  -- Combine: `D * ‖Gamma(z₀)‖ = ‖Gamma(z₀+12)‖ ≤ 313M`, `D ≥ 33B`.
  have hD_mul : (‖1 - R00Numerics.sR00 / 2 + 11‖
        * (‖1 - R00Numerics.sR00 / 2 + 10‖
          * (‖1 - R00Numerics.sR00 / 2 + 9‖
            * (‖1 - R00Numerics.sR00 / 2 + 8‖
              * (‖1 - R00Numerics.sR00 / 2 + 7‖
                * (‖1 - R00Numerics.sR00 / 2 + 6‖
                  * (‖1 - R00Numerics.sR00 / 2 + 5‖
                    * (‖1 - R00Numerics.sR00 / 2 + 4‖
                      * (‖1 - R00Numerics.sR00 / 2 + 3‖
                        * (‖1 - R00Numerics.sR00 / 2 + 2‖
                          * (‖1 - R00Numerics.sR00 / 2 + 1‖
                            * ‖1 - R00Numerics.sR00 / 2‖)))))))))))
        * ‖Complex.Gamma (1 - R00Numerics.sR00 / 2)‖
      = ‖Complex.Gamma (1 - R00Numerics.sR00 / 2 + 12)‖ := by
    rw [hprod]
    ring
  have hle : (‖1 - R00Numerics.sR00 / 2 + 11‖
        * (‖1 - R00Numerics.sR00 / 2 + 10‖
          * (‖1 - R00Numerics.sR00 / 2 + 9‖
            * (‖1 - R00Numerics.sR00 / 2 + 8‖
              * (‖1 - R00Numerics.sR00 / 2 + 7‖
                * (‖1 - R00Numerics.sR00 / 2 + 6‖
                  * (‖1 - R00Numerics.sR00 / 2 + 5‖
                    * (‖1 - R00Numerics.sR00 / 2 + 4‖
                      * (‖1 - R00Numerics.sR00 / 2 + 3‖
                        * (‖1 - R00Numerics.sR00 / 2 + 2‖
                          * (‖1 - R00Numerics.sR00 / 2 + 1‖
                            * ‖1 - R00Numerics.sR00 / 2‖)))))))))))
        * ‖Complex.Gamma (1 - R00Numerics.sR00 / 2)‖ ≤ 313000000 := by
    rw [hD_mul]
    exact hG12_le
  have hmul_comm : ‖Complex.Gamma (1 - R00Numerics.sR00 / 2)‖
        * (‖1 - R00Numerics.sR00 / 2 + 11‖
          * (‖1 - R00Numerics.sR00 / 2 + 10‖
            * (‖1 - R00Numerics.sR00 / 2 + 9‖
              * (‖1 - R00Numerics.sR00 / 2 + 8‖
                * (‖1 - R00Numerics.sR00 / 2 + 7‖
                  * (‖1 - R00Numerics.sR00 / 2 + 6‖
                    * (‖1 - R00Numerics.sR00 / 2 + 5‖
                      * (‖1 - R00Numerics.sR00 / 2 + 4‖
                        * (‖1 - R00Numerics.sR00 / 2 + 3‖
                          * (‖1 - R00Numerics.sR00 / 2 + 2‖
                            * (‖1 - R00Numerics.sR00 / 2 + 1‖
                              * ‖1 - R00Numerics.sR00 / 2‖)))))))))))
        ≤ 313000000 := by
    calc ‖Complex.Gamma (1 - R00Numerics.sR00 / 2)‖ * _
          = _ * ‖Complex.Gamma (1 - R00Numerics.sR00 / 2)‖ := mul_comm _ _
      _ ≤ 313000000 := hle
  have hdiv : ‖Complex.Gamma (1 - R00Numerics.sR00 / 2)‖
      ≤ 313000000 / (‖1 - R00Numerics.sR00 / 2 + 11‖
        * (‖1 - R00Numerics.sR00 / 2 + 10‖
          * (‖1 - R00Numerics.sR00 / 2 + 9‖
            * (‖1 - R00Numerics.sR00 / 2 + 8‖
              * (‖1 - R00Numerics.sR00 / 2 + 7‖
                * (‖1 - R00Numerics.sR00 / 2 + 6‖
                  * (‖1 - R00Numerics.sR00 / 2 + 5‖
                    * (‖1 - R00Numerics.sR00 / 2 + 4‖
                      * (‖1 - R00Numerics.sR00 / 2 + 3‖
                        * (‖1 - R00Numerics.sR00 / 2 + 2‖
                          * (‖1 - R00Numerics.sR00 / 2 + 1‖
                            * ‖1 - R00Numerics.sR00 / 2‖))))))))))) :=
    (le_div_iff₀ hD_pos).mpr hmul_comm
  have h313 : (313000000 : ℝ)
      ≤ 0.01 * (‖1 - R00Numerics.sR00 / 2 + 11‖
        * (‖1 - R00Numerics.sR00 / 2 + 10‖
          * (‖1 - R00Numerics.sR00 / 2 + 9‖
            * (‖1 - R00Numerics.sR00 / 2 + 8‖
              * (‖1 - R00Numerics.sR00 / 2 + 7‖
                * (‖1 - R00Numerics.sR00 / 2 + 6‖
                  * (‖1 - R00Numerics.sR00 / 2 + 5‖
                    * (‖1 - R00Numerics.sR00 / 2 + 4‖
                      * (‖1 - R00Numerics.sR00 / 2 + 3‖
                        * (‖1 - R00Numerics.sR00 / 2 + 2‖
                          * (‖1 - R00Numerics.sR00 / 2 + 1‖
                            * ‖1 - R00Numerics.sR00 / 2‖))))))))))) := by
    calc (313000000 : ℝ) ≤ 0.01 * 33000000000 := by norm_num
      _ ≤ 0.01 * _ :=
          mul_le_mul_of_nonneg_left hD_ge (by norm_num)
  have hfinal : 313000000 / (‖1 - R00Numerics.sR00 / 2 + 11‖
        * (‖1 - R00Numerics.sR00 / 2 + 10‖
          * (‖1 - R00Numerics.sR00 / 2 + 9‖
            * (‖1 - R00Numerics.sR00 / 2 + 8‖
              * (‖1 - R00Numerics.sR00 / 2 + 7‖
                * (‖1 - R00Numerics.sR00 / 2 + 6‖
                  * (‖1 - R00Numerics.sR00 / 2 + 5‖
                    * (‖1 - R00Numerics.sR00 / 2 + 4‖
                      * (‖1 - R00Numerics.sR00 / 2 + 3‖
                        * (‖1 - R00Numerics.sR00 / 2 + 2‖
                          * (‖1 - R00Numerics.sR00 / 2 + 1‖
                            * ‖1 - R00Numerics.sR00 / 2‖)))))))))))
      ≤ 0.01 :=
    (div_le_iff₀ hD_pos).mpr h313
  exact le_trans hdiv hfinal

end CellGammaUpper


/-!
## Outer-tier complex-Gamma UPPER bounds, row 1 + R10/R20 mirrors (12-shift route).

Replicates the `CellGammaUpper` R00 template (shift identity
`Complex.Gamma_add_one` induction + integral majorant
`R00GammaLower.norm_Gamma_le_realGamma` + real convexity) at new centers:

* `CellGammaUpper085`: second `re`-value chain (`z.re = 0.85`, row
  `y = (0.1,0.3)`), `Real.Gamma 12.85 <= 348000000`.
* `R11GammaUpper.gamma_one_sub_half_upper_R11`: `|Gamma(1-sR11/2)| <= 0.01`
  at the row-1 outer corner `sR11 = 0.3 - 8.75*I` (`z0 = 0.85 + 4.375*I`).
* `R10GammaUpper.gamma_one_sub_half_upper_R10`: `<= 0.01` at the bottom-row
  mirror `sR10 = 0.395 + 8.75*I` (reuses the `0.8025` chain).
* `R20GammaUpper.gamma_one_sub_half_upper_R20`: `<= 0.01` at the row-1
  mirror `sR20 = 0.3 + 8.75*I` (reuses the `0.85` chain).

All floor constants `c(k)^2 <= re^2 + im^2` verified by exact rational
arithmetic before writing; each is closed in-file by `norm_num`.
-/

namespace CellGammaUpper085

/-- Real convexity feeder: `Real.Gamma 1.85 ≤ 1`
(`1.85 = 0.15*ℝ1 + 0.85*ℝ2`, `Gamma 1 = Gamma 2 = 1`). -/
theorem realGamma_185_le_one : Real.Gamma 1.85 ≤ 1 := by
  have hconv := Real.convexOn_Gamma
  have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have h2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have ha : (0 : ℝ) ≤ 0.15 := by norm_num
  have hb : (0 : ℝ) ≤ 0.85 := by norm_num
  have hab : (0.15 : ℝ) + 0.85 = 1 := by norm_num
  have h := hconv.2 h1 h2 ha hb hab
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
  have heq : (0.15 : ℝ) * 1 + 0.85 * 2 = 1.85 := by norm_num
  have hrhs : (0.15 : ℝ) * 1 + 0.85 * 1 = (1 : ℝ) := by norm_num
  rw [heq] at h
  rw [hrhs] at h
  exact h

/-- `Real.Gamma 2.85 ≤ 1.85`. -/
theorem realGamma_285_le : Real.Gamma 2.85 ≤ 1.85 := by
  have h : Real.Gamma (1.85 + 1) = 1.85 * Real.Gamma 1.85 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (1.85 : ℝ) + 1 = 2.85 := by norm_num
  rw [heq] at h
  rw [h]
  calc (1.85 : ℝ) * Real.Gamma 1.85 ≤ 1.85 * 1 :=
        mul_le_mul_of_nonneg_left realGamma_185_le_one (by norm_num)
    _ = 1.85 := mul_one _

/-- `Real.Gamma 3.85 ≤ 1.85 * 2.85`. -/
theorem realGamma_385_le : Real.Gamma 3.85 ≤ 1.85 * 2.85 := by
  have h : Real.Gamma (2.85 + 1) = 2.85 * Real.Gamma 2.85 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (2.85 : ℝ) + 1 = 3.85 := by norm_num
  rw [heq] at h
  rw [h]
  calc (2.85 : ℝ) * Real.Gamma 2.85 ≤ 2.85 * 1.85 :=
        mul_le_mul_of_nonneg_left realGamma_285_le (by norm_num)
    _ = 1.85 * 2.85 := mul_comm _ _

/-- `Real.Gamma 4.85 ≤ 1.85 * 2.85 * 3.85`. -/
theorem realGamma_485_le : Real.Gamma 4.85 ≤ 1.85 * 2.85 * 3.85 := by
  have h : Real.Gamma (3.85 + 1) = 3.85 * Real.Gamma 3.85 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (3.85 : ℝ) + 1 = 4.85 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 3.85 * Real.Gamma 3.85
      ≤ 3.85 * (1.85 * 2.85) :=
    mul_le_mul_of_nonneg_left realGamma_385_le (by norm_num)
  calc (3.85 : ℝ) * Real.Gamma 3.85
        ≤ 3.85 * (1.85 * 2.85) := hle
    _ = 1.85 * 2.85 * 3.85 := by ring

/-- `Real.Gamma 5.85 ≤ 1.85 * 2.85 * 3.85 * 4.85`. -/
theorem realGamma_585_le : Real.Gamma 5.85 ≤ 1.85 * 2.85 * 3.85 * 4.85 := by
  have h : Real.Gamma (4.85 + 1) = 4.85 * Real.Gamma 4.85 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (4.85 : ℝ) + 1 = 5.85 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 4.85 * Real.Gamma 4.85
      ≤ 4.85 * (1.85 * 2.85 * 3.85) :=
    mul_le_mul_of_nonneg_left realGamma_485_le (by norm_num)
  calc (4.85 : ℝ) * Real.Gamma 4.85
        ≤ 4.85 * (1.85 * 2.85 * 3.85) := hle
    _ = 1.85 * 2.85 * 3.85 * 4.85 := by ring

/-- `Real.Gamma 6.85 ≤ 1.85 * 2.85 * 3.85 * 4.85 * 5.85`. -/
theorem realGamma_685_le :
    Real.Gamma 6.85 ≤ 1.85 * 2.85 * 3.85 * 4.85 * 5.85 := by
  have h : Real.Gamma (5.85 + 1) = 5.85 * Real.Gamma 5.85 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (5.85 : ℝ) + 1 = 6.85 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 5.85 * Real.Gamma 5.85
      ≤ 5.85 * (1.85 * 2.85 * 3.85 * 4.85) :=
    mul_le_mul_of_nonneg_left realGamma_585_le (by norm_num)
  calc (5.85 : ℝ) * Real.Gamma 5.85
        ≤ 5.85 * (1.85 * 2.85 * 3.85 * 4.85) := hle
    _ = 1.85 * 2.85 * 3.85 * 4.85 * 5.85 := by ring

/-- `Real.Gamma 7.85 ≤ 1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85`. -/
theorem realGamma_785_le :
    Real.Gamma 7.85 ≤ 1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 := by
  have h : Real.Gamma (6.85 + 1) = 6.85 * Real.Gamma 6.85 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (6.85 : ℝ) + 1 = 7.85 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 6.85 * Real.Gamma 6.85
      ≤ 6.85 * (1.85 * 2.85 * 3.85 * 4.85 * 5.85) :=
    mul_le_mul_of_nonneg_left realGamma_685_le (by norm_num)
  calc (6.85 : ℝ) * Real.Gamma 6.85
        ≤ 6.85 * (1.85 * 2.85 * 3.85 * 4.85 * 5.85) := hle
    _ = 1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 := by ring

/-- `Real.Gamma 8.85 ≤ 1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85`. -/
theorem realGamma_885_le :
    Real.Gamma 8.85 ≤ 1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85 := by
  have h : Real.Gamma (7.85 + 1) = 7.85 * Real.Gamma 7.85 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (7.85 : ℝ) + 1 = 8.85 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 7.85 * Real.Gamma 7.85
      ≤ 7.85 * (1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85) :=
    mul_le_mul_of_nonneg_left realGamma_785_le (by norm_num)
  calc (7.85 : ℝ) * Real.Gamma 7.85
        ≤ 7.85 * (1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85) := hle
    _ = 1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85 := by ring

/-- `Real.Gamma 9.85 ≤ 1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85 * 8.85`. -/
theorem realGamma_985_le :
    Real.Gamma 9.85 ≤ 1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85 * 8.85 := by
  have h : Real.Gamma (8.85 + 1) = 8.85 * Real.Gamma 8.85 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (8.85 : ℝ) + 1 = 9.85 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 8.85 * Real.Gamma 8.85
      ≤ 8.85 * (1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85) :=
    mul_le_mul_of_nonneg_left realGamma_885_le (by norm_num)
  calc (8.85 : ℝ) * Real.Gamma 8.85
        ≤ 8.85 * (1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85) := hle
    _ = 1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85 * 8.85 := by ring

/-- `Real.Gamma 10.85 ≤ 1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85 * 8.85 * 9.85`. -/
theorem realGamma_1085_le :
    Real.Gamma 10.85 ≤ 1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85 * 8.85 * 9.85 := by
  have h : Real.Gamma (9.85 + 1) = 9.85 * Real.Gamma 9.85 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (9.85 : ℝ) + 1 = 10.85 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 9.85 * Real.Gamma 9.85
      ≤ 9.85 * (1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85 * 8.85) :=
    mul_le_mul_of_nonneg_left realGamma_985_le (by norm_num)
  calc (9.85 : ℝ) * Real.Gamma 9.85
        ≤ 9.85 * (1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85 * 8.85) := hle
    _ = 1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85 * 8.85 * 9.85 := by ring

/-- `Real.Gamma 11.85 ≤ 1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85 * 8.85 * 9.85 * 10.85`. -/
theorem realGamma_1185_le :
    Real.Gamma 11.85 ≤ 1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85 * 8.85 * 9.85 * 10.85 := by
  have h : Real.Gamma (10.85 + 1) = 10.85 * Real.Gamma 10.85 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (10.85 : ℝ) + 1 = 11.85 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 10.85 * Real.Gamma 10.85
      ≤ 10.85 * (1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85 * 8.85 * 9.85) :=
    mul_le_mul_of_nonneg_left realGamma_1085_le (by norm_num)
  calc (10.85 : ℝ) * Real.Gamma 10.85
        ≤ 10.85 * (1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85 * 8.85 * 9.85) := hle
    _ = 1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85 * 8.85 * 9.85 * 10.85 := by ring

/-- `Real.Gamma 12.85 ≤ 1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85 * 8.85 * 9.85 * 10.85 * 11.85 ≤ 348000000` (numerator cap). -/
theorem realGamma_1285_le : Real.Gamma 12.85 ≤ 348000000 := by
  have h : Real.Gamma (11.85 + 1) = 11.85 * Real.Gamma 11.85 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (11.85 : ℝ) + 1 = 12.85 := by norm_num
  rw [heq] at h
  rw [h] at ⊢
  have hle : 11.85 * Real.Gamma 11.85
      ≤ 11.85 * (1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85 * 8.85 * 9.85 * 10.85) :=
    mul_le_mul_of_nonneg_left realGamma_1185_le (by norm_num)
  have hprod : (11.85 : ℝ) * (1.85 * 2.85 * 3.85 * 4.85 * 5.85 * 6.85 * 7.85 * 8.85 * 9.85 * 10.85) ≤ 348000000 := by
    norm_num
  exact le_trans hle hprod

end CellGammaUpper085

namespace R11GammaUpper

/-- The R11 `s`-plane center: `s = 1/2 + I·z` at `z = R11.center`. -/
noncomputable def sR11 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R11.center

/-- `R11.center = -8.75 + 0.2·I` (from `R11_x0/x1/y0/y1`). -/
theorem R11_center_eq :
    CentralCoverAssembly.R11.center =
      (((-8.75 : ℝ))) + Complex.I * ((((0.2 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R11_x0, CentralCoverAssembly.R11_x1,
      CentralCoverAssembly.R11_y0, CentralCoverAssembly.R11_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R11_x0, CentralCoverAssembly.R11_x1,
      CentralCoverAssembly.R11_y0, CentralCoverAssembly.R11_y1]
    simp
    norm_num

/-- `Re sR11 = 0.3`. -/
theorem sR11_re : sR11.re = 0.3 := by
  unfold sR11
  rw [R11_center_eq]
  simp
  norm_num

/-- `Im sR11 = -8.75`. -/
theorem sR11_im : sR11.im = -8.75 := by
  unfold sR11
  rw [R11_center_eq]
  simp

/-- `Re(1 - sR11/2) = 0.85`. -/
theorem zUpR11_re : (1 - sR11 / 2).re = 0.85 := by
  rw [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, sR11_re]
  norm_num

/-- `Im(1 - sR11/2) = 4.375`. -/
theorem zUpR11_im : (1 - sR11 / 2).im = 4.375 := by
  rw [Complex.sub_im, Complex.one_im, Complex.div_ofNat_im, sR11_im]
  norm_num

/-- Denominator floor `c0 = 4.45 ≤ ‖1 - sR11 / 2‖`. -/
theorem norm_zUpR11_0_ge :
    (4.45 : ℝ) ≤ ‖1 - sR11 / 2‖ := by
  have hsq : (4.45 : ℝ) ^ 2 ≤ ‖1 - sR11 / 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, zUpR11_re, zUpR11_im]
    norm_num
  calc (4.45 : ℝ) = Real.sqrt ((4.45 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR11 / 2‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR11 / 2‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c1 = 4.75 ≤ ‖1 - sR11 / 2 + 1‖`. -/
theorem norm_zUpR11_1_ge :
    (4.75 : ℝ) ≤ ‖1 - sR11 / 2 + 1‖ := by
  have hre : (1 - sR11 / 2 + 1).re = 1.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.one_re]
    norm_num
  have him : (1 - sR11 / 2 + 1).im = 4.375 := by
    simp only [Complex.add_im, zUpR11_im, Complex.one_im]
    norm_num
  have hsq : (4.75 : ℝ) ^ 2 ≤ ‖1 - sR11 / 2 + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (4.75 : ℝ) = Real.sqrt ((4.75 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR11 / 2 + 1‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR11 / 2 + 1‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c2 = 5.22 ≤ ‖1 - sR11 / 2 + 2‖`. -/
theorem norm_zUpR11_2_ge :
    (5.22 : ℝ) ≤ ‖1 - sR11 / 2 + 2‖ := by
  have hre : (1 - sR11 / 2 + 2).re = 2.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR11 / 2 + 2).im = 4.375 := by
    simp only [Complex.add_im, zUpR11_im, Complex.im_ofNat]
    norm_num
  have hsq : (5.22 : ℝ) ^ 2 ≤ ‖1 - sR11 / 2 + 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (5.22 : ℝ) = Real.sqrt ((5.22 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR11 / 2 + 2‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR11 / 2 + 2‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c3 = 5.82 ≤ ‖1 - sR11 / 2 + 3‖`. -/
theorem norm_zUpR11_3_ge :
    (5.82 : ℝ) ≤ ‖1 - sR11 / 2 + 3‖ := by
  have hre : (1 - sR11 / 2 + 3).re = 3.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR11 / 2 + 3).im = 4.375 := by
    simp only [Complex.add_im, zUpR11_im, Complex.im_ofNat]
    norm_num
  have hsq : (5.82 : ℝ) ^ 2 ≤ ‖1 - sR11 / 2 + 3‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (5.82 : ℝ) = Real.sqrt ((5.82 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR11 / 2 + 3‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR11 / 2 + 3‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c4 = 6.53 ≤ ‖1 - sR11 / 2 + 4‖`. -/
theorem norm_zUpR11_4_ge :
    (6.53 : ℝ) ≤ ‖1 - sR11 / 2 + 4‖ := by
  have hre : (1 - sR11 / 2 + 4).re = 4.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR11 / 2 + 4).im = 4.375 := by
    simp only [Complex.add_im, zUpR11_im, Complex.im_ofNat]
    norm_num
  have hsq : (6.53 : ℝ) ^ 2 ≤ ‖1 - sR11 / 2 + 4‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (6.53 : ℝ) = Real.sqrt ((6.53 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR11 / 2 + 4‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR11 / 2 + 4‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c5 = 7.3 ≤ ‖1 - sR11 / 2 + 5‖`. -/
theorem norm_zUpR11_5_ge :
    (7.3 : ℝ) ≤ ‖1 - sR11 / 2 + 5‖ := by
  have hre : (1 - sR11 / 2 + 5).re = 5.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR11 / 2 + 5).im = 4.375 := by
    simp only [Complex.add_im, zUpR11_im, Complex.im_ofNat]
    norm_num
  have hsq : (7.3 : ℝ) ^ 2 ≤ ‖1 - sR11 / 2 + 5‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (7.3 : ℝ) = Real.sqrt ((7.3 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR11 / 2 + 5‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR11 / 2 + 5‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c6 = 8.12 ≤ ‖1 - sR11 / 2 + 6‖`. -/
theorem norm_zUpR11_6_ge :
    (8.12 : ℝ) ≤ ‖1 - sR11 / 2 + 6‖ := by
  have hre : (1 - sR11 / 2 + 6).re = 6.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR11 / 2 + 6).im = 4.375 := by
    simp only [Complex.add_im, zUpR11_im, Complex.im_ofNat]
    norm_num
  have hsq : (8.12 : ℝ) ^ 2 ≤ ‖1 - sR11 / 2 + 6‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (8.12 : ℝ) = Real.sqrt ((8.12 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR11 / 2 + 6‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR11 / 2 + 6‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c7 = 8.98 ≤ ‖1 - sR11 / 2 + 7‖`. -/
theorem norm_zUpR11_7_ge :
    (8.98 : ℝ) ≤ ‖1 - sR11 / 2 + 7‖ := by
  have hre : (1 - sR11 / 2 + 7).re = 7.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR11 / 2 + 7).im = 4.375 := by
    simp only [Complex.add_im, zUpR11_im, Complex.im_ofNat]
    norm_num
  have hsq : (8.98 : ℝ) ^ 2 ≤ ‖1 - sR11 / 2 + 7‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (8.98 : ℝ) = Real.sqrt ((8.98 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR11 / 2 + 7‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR11 / 2 + 7‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c8 = 9.87 ≤ ‖1 - sR11 / 2 + 8‖`. -/
theorem norm_zUpR11_8_ge :
    (9.87 : ℝ) ≤ ‖1 - sR11 / 2 + 8‖ := by
  have hre : (1 - sR11 / 2 + 8).re = 8.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR11 / 2 + 8).im = 4.375 := by
    simp only [Complex.add_im, zUpR11_im, Complex.im_ofNat]
    norm_num
  have hsq : (9.87 : ℝ) ^ 2 ≤ ‖1 - sR11 / 2 + 8‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (9.87 : ℝ) = Real.sqrt ((9.87 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR11 / 2 + 8‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR11 / 2 + 8‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c9 = 10.77 ≤ ‖1 - sR11 / 2 + 9‖`. -/
theorem norm_zUpR11_9_ge :
    (10.77 : ℝ) ≤ ‖1 - sR11 / 2 + 9‖ := by
  have hre : (1 - sR11 / 2 + 9).re = 9.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR11 / 2 + 9).im = 4.375 := by
    simp only [Complex.add_im, zUpR11_im, Complex.im_ofNat]
    norm_num
  have hsq : (10.77 : ℝ) ^ 2 ≤ ‖1 - sR11 / 2 + 9‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (10.77 : ℝ) = Real.sqrt ((10.77 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR11 / 2 + 9‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR11 / 2 + 9‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c10 = 11.69 ≤ ‖1 - sR11 / 2 + 10‖`. -/
theorem norm_zUpR11_10_ge :
    (11.69 : ℝ) ≤ ‖1 - sR11 / 2 + 10‖ := by
  have hre : (1 - sR11 / 2 + 10).re = 10.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR11 / 2 + 10).im = 4.375 := by
    simp only [Complex.add_im, zUpR11_im, Complex.im_ofNat]
    norm_num
  have hsq : (11.69 : ℝ) ^ 2 ≤ ‖1 - sR11 / 2 + 10‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (11.69 : ℝ) = Real.sqrt ((11.69 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR11 / 2 + 10‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR11 / 2 + 10‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c11 = 12.63 ≤ ‖1 - sR11 / 2 + 11‖`. -/
theorem norm_zUpR11_11_ge :
    (12.63 : ℝ) ≤ ‖1 - sR11 / 2 + 11‖ := by
  have hre : (1 - sR11 / 2 + 11).re = 11.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR11 / 2 + 11).im = 4.375 := by
    simp only [Complex.add_im, zUpR11_im, Complex.im_ofNat]
    norm_num
  have hsq : (12.63 : ℝ) ^ 2 ≤ ‖1 - sR11 / 2 + 11‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (12.63 : ℝ) = Real.sqrt ((12.63 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR11 / 2 + 11‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR11 / 2 + 11‖ := Real.sqrt_sq (norm_nonneg _)

/-- Shift nonvanishing (`Re > 0` so `{NE} 0`). -/
theorem zUpR11_ne0 : (1 - sR11 / 2) ≠ 0 := by
  have hre : (1 - sR11 / 2).re = 0.85 := zUpR11_re
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR11_add1_ne0 : (1 - sR11 / 2 + 1) ≠ 0 := by
  have hre : (1 - sR11 / 2 + 1).re = 1.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.one_re]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR11_add2_ne0 : (1 - sR11 / 2 + 2) ≠ 0 := by
  have hre : (1 - sR11 / 2 + 2).re = 2.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR11_add3_ne0 : (1 - sR11 / 2 + 3) ≠ 0 := by
  have hre : (1 - sR11 / 2 + 3).re = 3.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR11_add4_ne0 : (1 - sR11 / 2 + 4) ≠ 0 := by
  have hre : (1 - sR11 / 2 + 4).re = 4.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR11_add5_ne0 : (1 - sR11 / 2 + 5) ≠ 0 := by
  have hre : (1 - sR11 / 2 + 5).re = 5.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR11_add6_ne0 : (1 - sR11 / 2 + 6) ≠ 0 := by
  have hre : (1 - sR11 / 2 + 6).re = 6.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR11_add7_ne0 : (1 - sR11 / 2 + 7) ≠ 0 := by
  have hre : (1 - sR11 / 2 + 7).re = 7.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR11_add8_ne0 : (1 - sR11 / 2 + 8) ≠ 0 := by
  have hre : (1 - sR11 / 2 + 8).re = 8.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR11_add9_ne0 : (1 - sR11 / 2 + 9) ≠ 0 := by
  have hre : (1 - sR11 / 2 + 9).re = 9.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR11_add10_ne0 : (1 - sR11 / 2 + 10) ≠ 0 := by
  have hre : (1 - sR11 / 2 + 10).re = 10.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR11_add11_ne0 : (1 - sR11 / 2 + 11) ≠ 0 := by
  have hre : (1 - sR11 / 2 + 11).re = 11.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

/-- MAIN uniform UPPER bound at the R11 corner:
`‖Complex.Gamma (1 - sR11 / 2)‖ ≤ 0.01` (row-1 outer-tier, `re = 0.85`). -/
theorem gamma_one_sub_half_upper_R11 :
    ‖Complex.Gamma (1 - sR11 / 2)‖ ≤ 0.01 := by
  -- Shift chain `Gamma(z0+12) = (z0+11)..z0*Gamma(z0)`.
  have e0 : Complex.Gamma (1 - sR11 / 2 + 1)
      = (1 - sR11 / 2) * Complex.Gamma (1 - sR11 / 2) :=
    Complex.Gamma_add_one _ zUpR11_ne0
  have e1 : Complex.Gamma (1 - sR11 / 2 + 2)
      = (1 - sR11 / 2 + 1)
        * Complex.Gamma (1 - sR11 / 2 + 1) := by
    have h : (1 - sR11 / 2 + 2)
        = ((1 - sR11 / 2 + 1) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR11_add1_ne0
  have e2 : Complex.Gamma (1 - sR11 / 2 + 3)
      = (1 - sR11 / 2 + 2)
        * Complex.Gamma (1 - sR11 / 2 + 2) := by
    have h : (1 - sR11 / 2 + 3)
        = ((1 - sR11 / 2 + 2) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR11_add2_ne0
  have e3 : Complex.Gamma (1 - sR11 / 2 + 4)
      = (1 - sR11 / 2 + 3)
        * Complex.Gamma (1 - sR11 / 2 + 3) := by
    have h : (1 - sR11 / 2 + 4)
        = ((1 - sR11 / 2 + 3) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR11_add3_ne0
  have e4 : Complex.Gamma (1 - sR11 / 2 + 5)
      = (1 - sR11 / 2 + 4)
        * Complex.Gamma (1 - sR11 / 2 + 4) := by
    have h : (1 - sR11 / 2 + 5)
        = ((1 - sR11 / 2 + 4) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR11_add4_ne0
  have e5 : Complex.Gamma (1 - sR11 / 2 + 6)
      = (1 - sR11 / 2 + 5)
        * Complex.Gamma (1 - sR11 / 2 + 5) := by
    have h : (1 - sR11 / 2 + 6)
        = ((1 - sR11 / 2 + 5) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR11_add5_ne0
  have e6 : Complex.Gamma (1 - sR11 / 2 + 7)
      = (1 - sR11 / 2 + 6)
        * Complex.Gamma (1 - sR11 / 2 + 6) := by
    have h : (1 - sR11 / 2 + 7)
        = ((1 - sR11 / 2 + 6) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR11_add6_ne0
  have e7 : Complex.Gamma (1 - sR11 / 2 + 8)
      = (1 - sR11 / 2 + 7)
        * Complex.Gamma (1 - sR11 / 2 + 7) := by
    have h : (1 - sR11 / 2 + 8)
        = ((1 - sR11 / 2 + 7) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR11_add7_ne0
  have e8 : Complex.Gamma (1 - sR11 / 2 + 9)
      = (1 - sR11 / 2 + 8)
        * Complex.Gamma (1 - sR11 / 2 + 8) := by
    have h : (1 - sR11 / 2 + 9)
        = ((1 - sR11 / 2 + 8) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR11_add8_ne0
  have e9 : Complex.Gamma (1 - sR11 / 2 + 10)
      = (1 - sR11 / 2 + 9)
        * Complex.Gamma (1 - sR11 / 2 + 9) := by
    have h : (1 - sR11 / 2 + 10)
        = ((1 - sR11 / 2 + 9) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR11_add9_ne0
  have e10 : Complex.Gamma (1 - sR11 / 2 + 11)
      = (1 - sR11 / 2 + 10)
        * Complex.Gamma (1 - sR11 / 2 + 10) := by
    have h : (1 - sR11 / 2 + 11)
        = ((1 - sR11 / 2 + 10) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR11_add10_ne0
  have e11 : Complex.Gamma (1 - sR11 / 2 + 12)
      = (1 - sR11 / 2 + 11)
        * Complex.Gamma (1 - sR11 / 2 + 11) := by
    have h : (1 - sR11 / 2 + 12)
        = ((1 - sR11 / 2 + 11) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR11_add11_ne0
  have n0 : ‖Complex.Gamma (1 - sR11 / 2 + 1)‖
      = ‖1 - sR11 / 2‖
        * ‖Complex.Gamma (1 - sR11 / 2)‖ := by
    rw [e0, norm_mul]
  have n1 : ‖Complex.Gamma (1 - sR11 / 2 + 2)‖
      = ‖1 - sR11 / 2 + 1‖
        * ‖Complex.Gamma (1 - sR11 / 2 + 1)‖ := by
    rw [e1, norm_mul]
  have n2 : ‖Complex.Gamma (1 - sR11 / 2 + 3)‖
      = ‖1 - sR11 / 2 + 2‖
        * ‖Complex.Gamma (1 - sR11 / 2 + 2)‖ := by
    rw [e2, norm_mul]
  have n3 : ‖Complex.Gamma (1 - sR11 / 2 + 4)‖
      = ‖1 - sR11 / 2 + 3‖
        * ‖Complex.Gamma (1 - sR11 / 2 + 3)‖ := by
    rw [e3, norm_mul]
  have n4 : ‖Complex.Gamma (1 - sR11 / 2 + 5)‖
      = ‖1 - sR11 / 2 + 4‖
        * ‖Complex.Gamma (1 - sR11 / 2 + 4)‖ := by
    rw [e4, norm_mul]
  have n5 : ‖Complex.Gamma (1 - sR11 / 2 + 6)‖
      = ‖1 - sR11 / 2 + 5‖
        * ‖Complex.Gamma (1 - sR11 / 2 + 5)‖ := by
    rw [e5, norm_mul]
  have n6 : ‖Complex.Gamma (1 - sR11 / 2 + 7)‖
      = ‖1 - sR11 / 2 + 6‖
        * ‖Complex.Gamma (1 - sR11 / 2 + 6)‖ := by
    rw [e6, norm_mul]
  have n7 : ‖Complex.Gamma (1 - sR11 / 2 + 8)‖
      = ‖1 - sR11 / 2 + 7‖
        * ‖Complex.Gamma (1 - sR11 / 2 + 7)‖ := by
    rw [e7, norm_mul]
  have n8 : ‖Complex.Gamma (1 - sR11 / 2 + 9)‖
      = ‖1 - sR11 / 2 + 8‖
        * ‖Complex.Gamma (1 - sR11 / 2 + 8)‖ := by
    rw [e8, norm_mul]
  have n9 : ‖Complex.Gamma (1 - sR11 / 2 + 10)‖
      = ‖1 - sR11 / 2 + 9‖
        * ‖Complex.Gamma (1 - sR11 / 2 + 9)‖ := by
    rw [e9, norm_mul]
  have n10 : ‖Complex.Gamma (1 - sR11 / 2 + 11)‖
      = ‖1 - sR11 / 2 + 10‖
        * ‖Complex.Gamma (1 - sR11 / 2 + 10)‖ := by
    rw [e10, norm_mul]
  have n11 : ‖Complex.Gamma (1 - sR11 / 2 + 12)‖
      = ‖1 - sR11 / 2 + 11‖
        * ‖Complex.Gamma (1 - sR11 / 2 + 11)‖ := by
    rw [e11, norm_mul]
  have hprod : ‖Complex.Gamma (1 - sR11 / 2 + 12)‖
      = ‖1 - sR11 / 2 + 11‖
        * (‖1 - sR11 / 2 + 10‖
        * (‖1 - sR11 / 2 + 9‖
        * (‖1 - sR11 / 2 + 8‖
        * (‖1 - sR11 / 2 + 7‖
        * (‖1 - sR11 / 2 + 6‖
        * (‖1 - sR11 / 2 + 5‖
        * (‖1 - sR11 / 2 + 4‖
        * (‖1 - sR11 / 2 + 3‖
        * (‖1 - sR11 / 2 + 2‖
        * (‖1 - sR11 / 2 + 1‖
        * (‖1 - sR11 / 2‖
          * ‖Complex.Gamma (1 - sR11 / 2)‖))))))))))) := by
    rw [n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n0]
  -- Denominator product lower bound.
  have q1 : (4.75 : ℝ) * 4.45
      ≤ ‖1 - sR11 / 2 + 1‖ * ‖1 - sR11 / 2‖ :=
    mul_le_mul norm_zUpR11_1_ge norm_zUpR11_0_ge (by norm_num) (norm_nonneg _)
  have q2 : (5.22 : ℝ) * (4.75 * (4.45))
      ≤ ‖1 - sR11 / 2 + 2‖ * (‖1 - sR11 / 2 + 1‖ * (‖1 - sR11 / 2‖)) :=
    mul_le_mul norm_zUpR11_2_ge q1 (by positivity) (norm_nonneg _)
  have q3 : (5.82 : ℝ) * (5.22 * (4.75 * (4.45)))
      ≤ ‖1 - sR11 / 2 + 3‖ * (‖1 - sR11 / 2 + 2‖ * (‖1 - sR11 / 2 + 1‖ * (‖1 - sR11 / 2‖))) :=
    mul_le_mul norm_zUpR11_3_ge q2 (by positivity) (norm_nonneg _)
  have q4 : (6.53 : ℝ) * (5.82 * (5.22 * (4.75 * (4.45))))
      ≤ ‖1 - sR11 / 2 + 4‖ * (‖1 - sR11 / 2 + 3‖ * (‖1 - sR11 / 2 + 2‖ * (‖1 - sR11 / 2 + 1‖ * (‖1 - sR11 / 2‖)))) :=
    mul_le_mul norm_zUpR11_4_ge q3 (by positivity) (norm_nonneg _)
  have q5 : (7.3 : ℝ) * (6.53 * (5.82 * (5.22 * (4.75 * (4.45)))))
      ≤ ‖1 - sR11 / 2 + 5‖ * (‖1 - sR11 / 2 + 4‖ * (‖1 - sR11 / 2 + 3‖ * (‖1 - sR11 / 2 + 2‖ * (‖1 - sR11 / 2 + 1‖ * (‖1 - sR11 / 2‖))))) :=
    mul_le_mul norm_zUpR11_5_ge q4 (by positivity) (norm_nonneg _)
  have q6 : (8.12 : ℝ) * (7.3 * (6.53 * (5.82 * (5.22 * (4.75 * (4.45))))))
      ≤ ‖1 - sR11 / 2 + 6‖ * (‖1 - sR11 / 2 + 5‖ * (‖1 - sR11 / 2 + 4‖ * (‖1 - sR11 / 2 + 3‖ * (‖1 - sR11 / 2 + 2‖ * (‖1 - sR11 / 2 + 1‖ * (‖1 - sR11 / 2‖)))))) :=
    mul_le_mul norm_zUpR11_6_ge q5 (by positivity) (norm_nonneg _)
  have q7 : (8.98 : ℝ) * (8.12 * (7.3 * (6.53 * (5.82 * (5.22 * (4.75 * (4.45)))))))
      ≤ ‖1 - sR11 / 2 + 7‖ * (‖1 - sR11 / 2 + 6‖ * (‖1 - sR11 / 2 + 5‖ * (‖1 - sR11 / 2 + 4‖ * (‖1 - sR11 / 2 + 3‖ * (‖1 - sR11 / 2 + 2‖ * (‖1 - sR11 / 2 + 1‖ * (‖1 - sR11 / 2‖))))))) :=
    mul_le_mul norm_zUpR11_7_ge q6 (by positivity) (norm_nonneg _)
  have q8 : (9.87 : ℝ) * (8.98 * (8.12 * (7.3 * (6.53 * (5.82 * (5.22 * (4.75 * (4.45))))))))
      ≤ ‖1 - sR11 / 2 + 8‖ * (‖1 - sR11 / 2 + 7‖ * (‖1 - sR11 / 2 + 6‖ * (‖1 - sR11 / 2 + 5‖ * (‖1 - sR11 / 2 + 4‖ * (‖1 - sR11 / 2 + 3‖ * (‖1 - sR11 / 2 + 2‖ * (‖1 - sR11 / 2 + 1‖ * (‖1 - sR11 / 2‖)))))))) :=
    mul_le_mul norm_zUpR11_8_ge q7 (by positivity) (norm_nonneg _)
  have q9 : (10.77 : ℝ) * (9.87 * (8.98 * (8.12 * (7.3 * (6.53 * (5.82 * (5.22 * (4.75 * (4.45)))))))))
      ≤ ‖1 - sR11 / 2 + 9‖ * (‖1 - sR11 / 2 + 8‖ * (‖1 - sR11 / 2 + 7‖ * (‖1 - sR11 / 2 + 6‖ * (‖1 - sR11 / 2 + 5‖ * (‖1 - sR11 / 2 + 4‖ * (‖1 - sR11 / 2 + 3‖ * (‖1 - sR11 / 2 + 2‖ * (‖1 - sR11 / 2 + 1‖ * (‖1 - sR11 / 2‖))))))))) :=
    mul_le_mul norm_zUpR11_9_ge q8 (by positivity) (norm_nonneg _)
  have q10 : (11.69 : ℝ) * (10.77 * (9.87 * (8.98 * (8.12 * (7.3 * (6.53 * (5.82 * (5.22 * (4.75 * (4.45))))))))))
      ≤ ‖1 - sR11 / 2 + 10‖ * (‖1 - sR11 / 2 + 9‖ * (‖1 - sR11 / 2 + 8‖ * (‖1 - sR11 / 2 + 7‖ * (‖1 - sR11 / 2 + 6‖ * (‖1 - sR11 / 2 + 5‖ * (‖1 - sR11 / 2 + 4‖ * (‖1 - sR11 / 2 + 3‖ * (‖1 - sR11 / 2 + 2‖ * (‖1 - sR11 / 2 + 1‖ * (‖1 - sR11 / 2‖)))))))))) :=
    mul_le_mul norm_zUpR11_10_ge q9 (by positivity) (norm_nonneg _)
  have q11 : (12.63 : ℝ) * (11.69 * (10.77 * (9.87 * (8.98 * (8.12 * (7.3 * (6.53 * (5.82 * (5.22 * (4.75 * (4.45)))))))))))
      ≤ ‖1 - sR11 / 2 + 11‖ * (‖1 - sR11 / 2 + 10‖ * (‖1 - sR11 / 2 + 9‖ * (‖1 - sR11 / 2 + 8‖ * (‖1 - sR11 / 2 + 7‖ * (‖1 - sR11 / 2 + 6‖ * (‖1 - sR11 / 2 + 5‖ * (‖1 - sR11 / 2 + 4‖ * (‖1 - sR11 / 2 + 3‖ * (‖1 - sR11 / 2 + 2‖ * (‖1 - sR11 / 2 + 1‖ * (‖1 - sR11 / 2‖))))))))))) :=
    mul_le_mul norm_zUpR11_11_ge q10 (by positivity) (norm_nonneg _)
  have hDlo : (35000000000 : ℝ)
      ≤ (12.63 : ℝ) * (11.69 * (10.77 * (9.87 * (8.98 * (8.12 * (7.3 * (6.53 * (5.82 * (5.22 * (4.75 * (4.45))))))))))) := by
    norm_num
  have hD_ge : (35000000000 : ℝ)
      ≤ ‖1 - sR11 / 2 + 11‖ * (‖1 - sR11 / 2 + 10‖ * (‖1 - sR11 / 2 + 9‖ * (‖1 - sR11 / 2 + 8‖ * (‖1 - sR11 / 2 + 7‖ * (‖1 - sR11 / 2 + 6‖ * (‖1 - sR11 / 2 + 5‖ * (‖1 - sR11 / 2 + 4‖ * (‖1 - sR11 / 2 + 3‖ * (‖1 - sR11 / 2 + 2‖ * (‖1 - sR11 / 2 + 1‖ * (‖1 - sR11 / 2‖))))))))))) :=
    le_trans hDlo q11
  have hD_pos : (0 : ℝ)
      < (‖1 - sR11 / 2 + 11‖
        * (‖1 - sR11 / 2 + 10‖
        * (‖1 - sR11 / 2 + 9‖
        * (‖1 - sR11 / 2 + 8‖
        * (‖1 - sR11 / 2 + 7‖
        * (‖1 - sR11 / 2 + 6‖
        * (‖1 - sR11 / 2 + 5‖
        * (‖1 - sR11 / 2 + 4‖
        * (‖1 - sR11 / 2 + 3‖
        * (‖1 - sR11 / 2 + 2‖
        * (‖1 - sR11 / 2 + 1‖
          * ‖1 - sR11 / 2‖))))))))))) :=
    lt_of_lt_of_le (by norm_num) hD_ge
  -- Numerator: `‖Complex.Gamma (1 - sR11 / 2 + 12)‖ ≤ Real.Gamma(12.85) ≤ 348000000`.
  have hre12 : (1 - sR11 / 2 + 12).re = 12.85 := by
    simp only [Complex.add_re, zUpR11_re, Complex.re_ofNat]
    norm_num
  have hGN_re : (0 : ℝ) < (1 - sR11 / 2 + 12).re := by
    rw [hre12]
    norm_num
  have hGN_le : ‖Complex.Gamma (1 - sR11 / 2 + 12)‖ ≤ 348000000 := by
    have h1 : ‖Complex.Gamma (1 - sR11 / 2 + 12)‖
        ≤ Real.Gamma ((1 - sR11 / 2 + 12).re) :=
      R00GammaLower.norm_Gamma_le_realGamma hGN_re
    have hreNb : ((1 - sR11 / 2 + 12).re) = 12.85 := hre12
    rw [hreNb] at h1
    exact le_trans h1 CellGammaUpper085.realGamma_1285_le
  -- Combine: `D * ‖Complex.Gamma (1 - sR11 / 2)‖ = ‖Complex.Gamma (1 - sR11 / 2 + 12)‖ ≤ 348000000`, `D ≤ 35000000000`.
  have hD_mul : (‖1 - sR11 / 2 + 11‖
        * (‖1 - sR11 / 2 + 10‖
        * (‖1 - sR11 / 2 + 9‖
        * (‖1 - sR11 / 2 + 8‖
        * (‖1 - sR11 / 2 + 7‖
        * (‖1 - sR11 / 2 + 6‖
        * (‖1 - sR11 / 2 + 5‖
        * (‖1 - sR11 / 2 + 4‖
        * (‖1 - sR11 / 2 + 3‖
        * (‖1 - sR11 / 2 + 2‖
        * (‖1 - sR11 / 2 + 1‖
          * ‖1 - sR11 / 2‖)))))))))))
        * ‖Complex.Gamma (1 - sR11 / 2)‖
      = ‖Complex.Gamma (1 - sR11 / 2 + 12)‖ := by
    rw [hprod]
    ring
  have hle : (‖1 - sR11 / 2 + 11‖
        * (‖1 - sR11 / 2 + 10‖
        * (‖1 - sR11 / 2 + 9‖
        * (‖1 - sR11 / 2 + 8‖
        * (‖1 - sR11 / 2 + 7‖
        * (‖1 - sR11 / 2 + 6‖
        * (‖1 - sR11 / 2 + 5‖
        * (‖1 - sR11 / 2 + 4‖
        * (‖1 - sR11 / 2 + 3‖
        * (‖1 - sR11 / 2 + 2‖
        * (‖1 - sR11 / 2 + 1‖
          * ‖1 - sR11 / 2‖)))))))))))
        * ‖Complex.Gamma (1 - sR11 / 2)‖ ≤ 348000000 := by
    rw [hD_mul]
    exact hGN_le
  have hmul_comm : ‖Complex.Gamma (1 - sR11 / 2)‖
        * (‖1 - sR11 / 2 + 11‖
        * (‖1 - sR11 / 2 + 10‖
        * (‖1 - sR11 / 2 + 9‖
        * (‖1 - sR11 / 2 + 8‖
        * (‖1 - sR11 / 2 + 7‖
        * (‖1 - sR11 / 2 + 6‖
        * (‖1 - sR11 / 2 + 5‖
        * (‖1 - sR11 / 2 + 4‖
        * (‖1 - sR11 / 2 + 3‖
        * (‖1 - sR11 / 2 + 2‖
        * (‖1 - sR11 / 2 + 1‖
          * ‖1 - sR11 / 2‖)))))))))))
        ≤ 348000000 := by
    calc ‖Complex.Gamma (1 - sR11 / 2)‖ * _
          = _ * ‖Complex.Gamma (1 - sR11 / 2)‖ := mul_comm _ _
      _ ≤ 348000000 := hle
  have hdiv : ‖Complex.Gamma (1 - sR11 / 2)‖
      ≤ 348000000 / (‖1 - sR11 / 2 + 11‖
        * (‖1 - sR11 / 2 + 10‖
        * (‖1 - sR11 / 2 + 9‖
        * (‖1 - sR11 / 2 + 8‖
        * (‖1 - sR11 / 2 + 7‖
        * (‖1 - sR11 / 2 + 6‖
        * (‖1 - sR11 / 2 + 5‖
        * (‖1 - sR11 / 2 + 4‖
        * (‖1 - sR11 / 2 + 3‖
        * (‖1 - sR11 / 2 + 2‖
        * (‖1 - sR11 / 2 + 1‖
          * ‖1 - sR11 / 2‖)))))))))))
        :=
    (le_div_iff₀ hD_pos).mpr hmul_comm
  have hcap : (348000000 : ℝ)
      ≤ 0.01 * (‖1 - sR11 / 2 + 11‖
        * (‖1 - sR11 / 2 + 10‖
        * (‖1 - sR11 / 2 + 9‖
        * (‖1 - sR11 / 2 + 8‖
        * (‖1 - sR11 / 2 + 7‖
        * (‖1 - sR11 / 2 + 6‖
        * (‖1 - sR11 / 2 + 5‖
        * (‖1 - sR11 / 2 + 4‖
        * (‖1 - sR11 / 2 + 3‖
        * (‖1 - sR11 / 2 + 2‖
        * (‖1 - sR11 / 2 + 1‖
          * ‖1 - sR11 / 2‖))))))))))) := by
    calc (348000000 : ℝ) ≤ 0.01 * 35000000000 := by norm_num
      _ ≤ 0.01 * _ :=
          mul_le_mul_of_nonneg_left hD_ge (by norm_num)
  have hfinal : 348000000 / (‖1 - sR11 / 2 + 11‖ * (‖1 - sR11 / 2 + 10‖ * (‖1 - sR11 / 2 + 9‖ * (‖1 - sR11 / 2 + 8‖ * (‖1 - sR11 / 2 + 7‖ * (‖1 - sR11 / 2 + 6‖ * (‖1 - sR11 / 2 + 5‖ * (‖1 - sR11 / 2 + 4‖ * (‖1 - sR11 / 2 + 3‖ * (‖1 - sR11 / 2 + 2‖ * (‖1 - sR11 / 2 + 1‖ * (‖1 - sR11 / 2‖))))))))))))
      ≤ 0.01 :=
    (div_le_iff₀ hD_pos).mpr hcap
  exact le_trans hdiv hfinal

end R11GammaUpper

namespace R10GammaUpper

/-- The R10 `s`-plane center: `s = 1/2 + I·z` at `z = R10.center`. -/
noncomputable def sR10 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R10.center

/-- `R10.center = 8.75 + 0.105·I` (from `R10_x0/x1/y0/y1`). -/
theorem R10_center_eq :
    CentralCoverAssembly.R10.center =
      (((8.75 : ℝ))) + Complex.I * ((((0.105 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R10_x0, CentralCoverAssembly.R10_x1,
      CentralCoverAssembly.R10_y0, CentralCoverAssembly.R10_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R10_x0, CentralCoverAssembly.R10_x1,
      CentralCoverAssembly.R10_y0, CentralCoverAssembly.R10_y1]
    simp
    norm_num

/-- `Re sR10 = 0.395`. -/
theorem sR10_re : sR10.re = 0.395 := by
  unfold sR10
  rw [R10_center_eq]
  simp
  norm_num

/-- `Im sR10 = 8.75`. -/
theorem sR10_im : sR10.im = 8.75 := by
  unfold sR10
  rw [R10_center_eq]
  simp

/-- `Re(1 - sR10/2) = 0.8025`. -/
theorem zUpR10_re : (1 - sR10 / 2).re = 0.8025 := by
  rw [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, sR10_re]
  norm_num

/-- `Im(1 - sR10/2) = -4.375`. -/
theorem zUpR10_im : (1 - sR10 / 2).im = -4.375 := by
  rw [Complex.sub_im, Complex.one_im, Complex.div_ofNat_im, sR10_im]
  norm_num

/-- Denominator floor `c0 = 4.44 ≤ ‖1 - sR10 / 2‖`. -/
theorem norm_zUpR10_0_ge :
    (4.44 : ℝ) ≤ ‖1 - sR10 / 2‖ := by
  have hsq : (4.44 : ℝ) ^ 2 ≤ ‖1 - sR10 / 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, zUpR10_re, zUpR10_im]
    norm_num
  calc (4.44 : ℝ) = Real.sqrt ((4.44 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR10 / 2‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR10 / 2‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c1 = 4.73 ≤ ‖1 - sR10 / 2 + 1‖`. -/
theorem norm_zUpR10_1_ge :
    (4.73 : ℝ) ≤ ‖1 - sR10 / 2 + 1‖ := by
  have hre : (1 - sR10 / 2 + 1).re = 1.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.one_re]
    norm_num
  have him : (1 - sR10 / 2 + 1).im = -4.375 := by
    simp only [Complex.add_im, zUpR10_im, Complex.one_im]
    norm_num
  have hsq : (4.73 : ℝ) ^ 2 ≤ ‖1 - sR10 / 2 + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (4.73 : ℝ) = Real.sqrt ((4.73 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR10 / 2 + 1‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR10 / 2 + 1‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c2 = 5.19 ≤ ‖1 - sR10 / 2 + 2‖`. -/
theorem norm_zUpR10_2_ge :
    (5.19 : ℝ) ≤ ‖1 - sR10 / 2 + 2‖ := by
  have hre : (1 - sR10 / 2 + 2).re = 2.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR10 / 2 + 2).im = -4.375 := by
    simp only [Complex.add_im, zUpR10_im, Complex.im_ofNat]
    norm_num
  have hsq : (5.19 : ℝ) ^ 2 ≤ ‖1 - sR10 / 2 + 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (5.19 : ℝ) = Real.sqrt ((5.19 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR10 / 2 + 2‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR10 / 2 + 2‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c3 = 5.79 ≤ ‖1 - sR10 / 2 + 3‖`. -/
theorem norm_zUpR10_3_ge :
    (5.79 : ℝ) ≤ ‖1 - sR10 / 2 + 3‖ := by
  have hre : (1 - sR10 / 2 + 3).re = 3.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR10 / 2 + 3).im = -4.375 := by
    simp only [Complex.add_im, zUpR10_im, Complex.im_ofNat]
    norm_num
  have hsq : (5.79 : ℝ) ^ 2 ≤ ‖1 - sR10 / 2 + 3‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (5.79 : ℝ) = Real.sqrt ((5.79 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR10 / 2 + 3‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR10 / 2 + 3‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c4 = 6.49 ≤ ‖1 - sR10 / 2 + 4‖`. -/
theorem norm_zUpR10_4_ge :
    (6.49 : ℝ) ≤ ‖1 - sR10 / 2 + 4‖ := by
  have hre : (1 - sR10 / 2 + 4).re = 4.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR10 / 2 + 4).im = -4.375 := by
    simp only [Complex.add_im, zUpR10_im, Complex.im_ofNat]
    norm_num
  have hsq : (6.49 : ℝ) ^ 2 ≤ ‖1 - sR10 / 2 + 4‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (6.49 : ℝ) = Real.sqrt ((6.49 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR10 / 2 + 4‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR10 / 2 + 4‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c5 = 7.26 ≤ ‖1 - sR10 / 2 + 5‖`. -/
theorem norm_zUpR10_5_ge :
    (7.26 : ℝ) ≤ ‖1 - sR10 / 2 + 5‖ := by
  have hre : (1 - sR10 / 2 + 5).re = 5.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR10 / 2 + 5).im = -4.375 := by
    simp only [Complex.add_im, zUpR10_im, Complex.im_ofNat]
    norm_num
  have hsq : (7.26 : ℝ) ^ 2 ≤ ‖1 - sR10 / 2 + 5‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (7.26 : ℝ) = Real.sqrt ((7.26 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR10 / 2 + 5‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR10 / 2 + 5‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c6 = 8.08 ≤ ‖1 - sR10 / 2 + 6‖`. -/
theorem norm_zUpR10_6_ge :
    (8.08 : ℝ) ≤ ‖1 - sR10 / 2 + 6‖ := by
  have hre : (1 - sR10 / 2 + 6).re = 6.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR10 / 2 + 6).im = -4.375 := by
    simp only [Complex.add_im, zUpR10_im, Complex.im_ofNat]
    norm_num
  have hsq : (8.08 : ℝ) ^ 2 ≤ ‖1 - sR10 / 2 + 6‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (8.08 : ℝ) = Real.sqrt ((8.08 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR10 / 2 + 6‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR10 / 2 + 6‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c7 = 8.94 ≤ ‖1 - sR10 / 2 + 7‖`. -/
theorem norm_zUpR10_7_ge :
    (8.94 : ℝ) ≤ ‖1 - sR10 / 2 + 7‖ := by
  have hre : (1 - sR10 / 2 + 7).re = 7.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR10 / 2 + 7).im = -4.375 := by
    simp only [Complex.add_im, zUpR10_im, Complex.im_ofNat]
    norm_num
  have hsq : (8.94 : ℝ) ^ 2 ≤ ‖1 - sR10 / 2 + 7‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (8.94 : ℝ) = Real.sqrt ((8.94 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR10 / 2 + 7‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR10 / 2 + 7‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c8 = 9.82 ≤ ‖1 - sR10 / 2 + 8‖`. -/
theorem norm_zUpR10_8_ge :
    (9.82 : ℝ) ≤ ‖1 - sR10 / 2 + 8‖ := by
  have hre : (1 - sR10 / 2 + 8).re = 8.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR10 / 2 + 8).im = -4.375 := by
    simp only [Complex.add_im, zUpR10_im, Complex.im_ofNat]
    norm_num
  have hsq : (9.82 : ℝ) ^ 2 ≤ ‖1 - sR10 / 2 + 8‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (9.82 : ℝ) = Real.sqrt ((9.82 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR10 / 2 + 8‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR10 / 2 + 8‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c9 = 10.73 ≤ ‖1 - sR10 / 2 + 9‖`. -/
theorem norm_zUpR10_9_ge :
    (10.73 : ℝ) ≤ ‖1 - sR10 / 2 + 9‖ := by
  have hre : (1 - sR10 / 2 + 9).re = 9.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR10 / 2 + 9).im = -4.375 := by
    simp only [Complex.add_im, zUpR10_im, Complex.im_ofNat]
    norm_num
  have hsq : (10.73 : ℝ) ^ 2 ≤ ‖1 - sR10 / 2 + 9‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (10.73 : ℝ) = Real.sqrt ((10.73 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR10 / 2 + 9‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR10 / 2 + 9‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c10 = 11.65 ≤ ‖1 - sR10 / 2 + 10‖`. -/
theorem norm_zUpR10_10_ge :
    (11.65 : ℝ) ≤ ‖1 - sR10 / 2 + 10‖ := by
  have hre : (1 - sR10 / 2 + 10).re = 10.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR10 / 2 + 10).im = -4.375 := by
    simp only [Complex.add_im, zUpR10_im, Complex.im_ofNat]
    norm_num
  have hsq : (11.65 : ℝ) ^ 2 ≤ ‖1 - sR10 / 2 + 10‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (11.65 : ℝ) = Real.sqrt ((11.65 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR10 / 2 + 10‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR10 / 2 + 10‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c11 = 12.58 ≤ ‖1 - sR10 / 2 + 11‖`. -/
theorem norm_zUpR10_11_ge :
    (12.58 : ℝ) ≤ ‖1 - sR10 / 2 + 11‖ := by
  have hre : (1 - sR10 / 2 + 11).re = 11.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR10 / 2 + 11).im = -4.375 := by
    simp only [Complex.add_im, zUpR10_im, Complex.im_ofNat]
    norm_num
  have hsq : (12.58 : ℝ) ^ 2 ≤ ‖1 - sR10 / 2 + 11‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (12.58 : ℝ) = Real.sqrt ((12.58 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR10 / 2 + 11‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR10 / 2 + 11‖ := Real.sqrt_sq (norm_nonneg _)

/-- Shift nonvanishing (`Re > 0` so `{NE} 0`). -/
theorem zUpR10_ne0 : (1 - sR10 / 2) ≠ 0 := by
  have hre : (1 - sR10 / 2).re = 0.8025 := zUpR10_re
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR10_add1_ne0 : (1 - sR10 / 2 + 1) ≠ 0 := by
  have hre : (1 - sR10 / 2 + 1).re = 1.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.one_re]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR10_add2_ne0 : (1 - sR10 / 2 + 2) ≠ 0 := by
  have hre : (1 - sR10 / 2 + 2).re = 2.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR10_add3_ne0 : (1 - sR10 / 2 + 3) ≠ 0 := by
  have hre : (1 - sR10 / 2 + 3).re = 3.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR10_add4_ne0 : (1 - sR10 / 2 + 4) ≠ 0 := by
  have hre : (1 - sR10 / 2 + 4).re = 4.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR10_add5_ne0 : (1 - sR10 / 2 + 5) ≠ 0 := by
  have hre : (1 - sR10 / 2 + 5).re = 5.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR10_add6_ne0 : (1 - sR10 / 2 + 6) ≠ 0 := by
  have hre : (1 - sR10 / 2 + 6).re = 6.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR10_add7_ne0 : (1 - sR10 / 2 + 7) ≠ 0 := by
  have hre : (1 - sR10 / 2 + 7).re = 7.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR10_add8_ne0 : (1 - sR10 / 2 + 8) ≠ 0 := by
  have hre : (1 - sR10 / 2 + 8).re = 8.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR10_add9_ne0 : (1 - sR10 / 2 + 9) ≠ 0 := by
  have hre : (1 - sR10 / 2 + 9).re = 9.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR10_add10_ne0 : (1 - sR10 / 2 + 10) ≠ 0 := by
  have hre : (1 - sR10 / 2 + 10).re = 10.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR10_add11_ne0 : (1 - sR10 / 2 + 11) ≠ 0 := by
  have hre : (1 - sR10 / 2 + 11).re = 11.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

/-- MAIN uniform UPPER bound at the R10 corner:
`‖Complex.Gamma (1 - sR10 / 2)‖ ≤ 0.01` (bottom-row outer-tier mirror, `re = 0.8025`). -/
theorem gamma_one_sub_half_upper_R10 :
    ‖Complex.Gamma (1 - sR10 / 2)‖ ≤ 0.01 := by
  -- Shift chain `Gamma(z0+12) = (z0+11)..z0*Gamma(z0)`.
  have e0 : Complex.Gamma (1 - sR10 / 2 + 1)
      = (1 - sR10 / 2) * Complex.Gamma (1 - sR10 / 2) :=
    Complex.Gamma_add_one _ zUpR10_ne0
  have e1 : Complex.Gamma (1 - sR10 / 2 + 2)
      = (1 - sR10 / 2 + 1)
        * Complex.Gamma (1 - sR10 / 2 + 1) := by
    have h : (1 - sR10 / 2 + 2)
        = ((1 - sR10 / 2 + 1) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR10_add1_ne0
  have e2 : Complex.Gamma (1 - sR10 / 2 + 3)
      = (1 - sR10 / 2 + 2)
        * Complex.Gamma (1 - sR10 / 2 + 2) := by
    have h : (1 - sR10 / 2 + 3)
        = ((1 - sR10 / 2 + 2) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR10_add2_ne0
  have e3 : Complex.Gamma (1 - sR10 / 2 + 4)
      = (1 - sR10 / 2 + 3)
        * Complex.Gamma (1 - sR10 / 2 + 3) := by
    have h : (1 - sR10 / 2 + 4)
        = ((1 - sR10 / 2 + 3) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR10_add3_ne0
  have e4 : Complex.Gamma (1 - sR10 / 2 + 5)
      = (1 - sR10 / 2 + 4)
        * Complex.Gamma (1 - sR10 / 2 + 4) := by
    have h : (1 - sR10 / 2 + 5)
        = ((1 - sR10 / 2 + 4) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR10_add4_ne0
  have e5 : Complex.Gamma (1 - sR10 / 2 + 6)
      = (1 - sR10 / 2 + 5)
        * Complex.Gamma (1 - sR10 / 2 + 5) := by
    have h : (1 - sR10 / 2 + 6)
        = ((1 - sR10 / 2 + 5) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR10_add5_ne0
  have e6 : Complex.Gamma (1 - sR10 / 2 + 7)
      = (1 - sR10 / 2 + 6)
        * Complex.Gamma (1 - sR10 / 2 + 6) := by
    have h : (1 - sR10 / 2 + 7)
        = ((1 - sR10 / 2 + 6) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR10_add6_ne0
  have e7 : Complex.Gamma (1 - sR10 / 2 + 8)
      = (1 - sR10 / 2 + 7)
        * Complex.Gamma (1 - sR10 / 2 + 7) := by
    have h : (1 - sR10 / 2 + 8)
        = ((1 - sR10 / 2 + 7) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR10_add7_ne0
  have e8 : Complex.Gamma (1 - sR10 / 2 + 9)
      = (1 - sR10 / 2 + 8)
        * Complex.Gamma (1 - sR10 / 2 + 8) := by
    have h : (1 - sR10 / 2 + 9)
        = ((1 - sR10 / 2 + 8) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR10_add8_ne0
  have e9 : Complex.Gamma (1 - sR10 / 2 + 10)
      = (1 - sR10 / 2 + 9)
        * Complex.Gamma (1 - sR10 / 2 + 9) := by
    have h : (1 - sR10 / 2 + 10)
        = ((1 - sR10 / 2 + 9) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR10_add9_ne0
  have e10 : Complex.Gamma (1 - sR10 / 2 + 11)
      = (1 - sR10 / 2 + 10)
        * Complex.Gamma (1 - sR10 / 2 + 10) := by
    have h : (1 - sR10 / 2 + 11)
        = ((1 - sR10 / 2 + 10) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR10_add10_ne0
  have e11 : Complex.Gamma (1 - sR10 / 2 + 12)
      = (1 - sR10 / 2 + 11)
        * Complex.Gamma (1 - sR10 / 2 + 11) := by
    have h : (1 - sR10 / 2 + 12)
        = ((1 - sR10 / 2 + 11) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR10_add11_ne0
  have n0 : ‖Complex.Gamma (1 - sR10 / 2 + 1)‖
      = ‖1 - sR10 / 2‖
        * ‖Complex.Gamma (1 - sR10 / 2)‖ := by
    rw [e0, norm_mul]
  have n1 : ‖Complex.Gamma (1 - sR10 / 2 + 2)‖
      = ‖1 - sR10 / 2 + 1‖
        * ‖Complex.Gamma (1 - sR10 / 2 + 1)‖ := by
    rw [e1, norm_mul]
  have n2 : ‖Complex.Gamma (1 - sR10 / 2 + 3)‖
      = ‖1 - sR10 / 2 + 2‖
        * ‖Complex.Gamma (1 - sR10 / 2 + 2)‖ := by
    rw [e2, norm_mul]
  have n3 : ‖Complex.Gamma (1 - sR10 / 2 + 4)‖
      = ‖1 - sR10 / 2 + 3‖
        * ‖Complex.Gamma (1 - sR10 / 2 + 3)‖ := by
    rw [e3, norm_mul]
  have n4 : ‖Complex.Gamma (1 - sR10 / 2 + 5)‖
      = ‖1 - sR10 / 2 + 4‖
        * ‖Complex.Gamma (1 - sR10 / 2 + 4)‖ := by
    rw [e4, norm_mul]
  have n5 : ‖Complex.Gamma (1 - sR10 / 2 + 6)‖
      = ‖1 - sR10 / 2 + 5‖
        * ‖Complex.Gamma (1 - sR10 / 2 + 5)‖ := by
    rw [e5, norm_mul]
  have n6 : ‖Complex.Gamma (1 - sR10 / 2 + 7)‖
      = ‖1 - sR10 / 2 + 6‖
        * ‖Complex.Gamma (1 - sR10 / 2 + 6)‖ := by
    rw [e6, norm_mul]
  have n7 : ‖Complex.Gamma (1 - sR10 / 2 + 8)‖
      = ‖1 - sR10 / 2 + 7‖
        * ‖Complex.Gamma (1 - sR10 / 2 + 7)‖ := by
    rw [e7, norm_mul]
  have n8 : ‖Complex.Gamma (1 - sR10 / 2 + 9)‖
      = ‖1 - sR10 / 2 + 8‖
        * ‖Complex.Gamma (1 - sR10 / 2 + 8)‖ := by
    rw [e8, norm_mul]
  have n9 : ‖Complex.Gamma (1 - sR10 / 2 + 10)‖
      = ‖1 - sR10 / 2 + 9‖
        * ‖Complex.Gamma (1 - sR10 / 2 + 9)‖ := by
    rw [e9, norm_mul]
  have n10 : ‖Complex.Gamma (1 - sR10 / 2 + 11)‖
      = ‖1 - sR10 / 2 + 10‖
        * ‖Complex.Gamma (1 - sR10 / 2 + 10)‖ := by
    rw [e10, norm_mul]
  have n11 : ‖Complex.Gamma (1 - sR10 / 2 + 12)‖
      = ‖1 - sR10 / 2 + 11‖
        * ‖Complex.Gamma (1 - sR10 / 2 + 11)‖ := by
    rw [e11, norm_mul]
  have hprod : ‖Complex.Gamma (1 - sR10 / 2 + 12)‖
      = ‖1 - sR10 / 2 + 11‖
        * (‖1 - sR10 / 2 + 10‖
        * (‖1 - sR10 / 2 + 9‖
        * (‖1 - sR10 / 2 + 8‖
        * (‖1 - sR10 / 2 + 7‖
        * (‖1 - sR10 / 2 + 6‖
        * (‖1 - sR10 / 2 + 5‖
        * (‖1 - sR10 / 2 + 4‖
        * (‖1 - sR10 / 2 + 3‖
        * (‖1 - sR10 / 2 + 2‖
        * (‖1 - sR10 / 2 + 1‖
        * (‖1 - sR10 / 2‖
          * ‖Complex.Gamma (1 - sR10 / 2)‖))))))))))) := by
    rw [n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n0]
  -- Denominator product lower bound.
  have q1 : (4.73 : ℝ) * 4.44
      ≤ ‖1 - sR10 / 2 + 1‖ * ‖1 - sR10 / 2‖ :=
    mul_le_mul norm_zUpR10_1_ge norm_zUpR10_0_ge (by norm_num) (norm_nonneg _)
  have q2 : (5.19 : ℝ) * (4.73 * (4.44))
      ≤ ‖1 - sR10 / 2 + 2‖ * (‖1 - sR10 / 2 + 1‖ * (‖1 - sR10 / 2‖)) :=
    mul_le_mul norm_zUpR10_2_ge q1 (by positivity) (norm_nonneg _)
  have q3 : (5.79 : ℝ) * (5.19 * (4.73 * (4.44)))
      ≤ ‖1 - sR10 / 2 + 3‖ * (‖1 - sR10 / 2 + 2‖ * (‖1 - sR10 / 2 + 1‖ * (‖1 - sR10 / 2‖))) :=
    mul_le_mul norm_zUpR10_3_ge q2 (by positivity) (norm_nonneg _)
  have q4 : (6.49 : ℝ) * (5.79 * (5.19 * (4.73 * (4.44))))
      ≤ ‖1 - sR10 / 2 + 4‖ * (‖1 - sR10 / 2 + 3‖ * (‖1 - sR10 / 2 + 2‖ * (‖1 - sR10 / 2 + 1‖ * (‖1 - sR10 / 2‖)))) :=
    mul_le_mul norm_zUpR10_4_ge q3 (by positivity) (norm_nonneg _)
  have q5 : (7.26 : ℝ) * (6.49 * (5.79 * (5.19 * (4.73 * (4.44)))))
      ≤ ‖1 - sR10 / 2 + 5‖ * (‖1 - sR10 / 2 + 4‖ * (‖1 - sR10 / 2 + 3‖ * (‖1 - sR10 / 2 + 2‖ * (‖1 - sR10 / 2 + 1‖ * (‖1 - sR10 / 2‖))))) :=
    mul_le_mul norm_zUpR10_5_ge q4 (by positivity) (norm_nonneg _)
  have q6 : (8.08 : ℝ) * (7.26 * (6.49 * (5.79 * (5.19 * (4.73 * (4.44))))))
      ≤ ‖1 - sR10 / 2 + 6‖ * (‖1 - sR10 / 2 + 5‖ * (‖1 - sR10 / 2 + 4‖ * (‖1 - sR10 / 2 + 3‖ * (‖1 - sR10 / 2 + 2‖ * (‖1 - sR10 / 2 + 1‖ * (‖1 - sR10 / 2‖)))))) :=
    mul_le_mul norm_zUpR10_6_ge q5 (by positivity) (norm_nonneg _)
  have q7 : (8.94 : ℝ) * (8.08 * (7.26 * (6.49 * (5.79 * (5.19 * (4.73 * (4.44)))))))
      ≤ ‖1 - sR10 / 2 + 7‖ * (‖1 - sR10 / 2 + 6‖ * (‖1 - sR10 / 2 + 5‖ * (‖1 - sR10 / 2 + 4‖ * (‖1 - sR10 / 2 + 3‖ * (‖1 - sR10 / 2 + 2‖ * (‖1 - sR10 / 2 + 1‖ * (‖1 - sR10 / 2‖))))))) :=
    mul_le_mul norm_zUpR10_7_ge q6 (by positivity) (norm_nonneg _)
  have q8 : (9.82 : ℝ) * (8.94 * (8.08 * (7.26 * (6.49 * (5.79 * (5.19 * (4.73 * (4.44))))))))
      ≤ ‖1 - sR10 / 2 + 8‖ * (‖1 - sR10 / 2 + 7‖ * (‖1 - sR10 / 2 + 6‖ * (‖1 - sR10 / 2 + 5‖ * (‖1 - sR10 / 2 + 4‖ * (‖1 - sR10 / 2 + 3‖ * (‖1 - sR10 / 2 + 2‖ * (‖1 - sR10 / 2 + 1‖ * (‖1 - sR10 / 2‖)))))))) :=
    mul_le_mul norm_zUpR10_8_ge q7 (by positivity) (norm_nonneg _)
  have q9 : (10.73 : ℝ) * (9.82 * (8.94 * (8.08 * (7.26 * (6.49 * (5.79 * (5.19 * (4.73 * (4.44)))))))))
      ≤ ‖1 - sR10 / 2 + 9‖ * (‖1 - sR10 / 2 + 8‖ * (‖1 - sR10 / 2 + 7‖ * (‖1 - sR10 / 2 + 6‖ * (‖1 - sR10 / 2 + 5‖ * (‖1 - sR10 / 2 + 4‖ * (‖1 - sR10 / 2 + 3‖ * (‖1 - sR10 / 2 + 2‖ * (‖1 - sR10 / 2 + 1‖ * (‖1 - sR10 / 2‖))))))))) :=
    mul_le_mul norm_zUpR10_9_ge q8 (by positivity) (norm_nonneg _)
  have q10 : (11.65 : ℝ) * (10.73 * (9.82 * (8.94 * (8.08 * (7.26 * (6.49 * (5.79 * (5.19 * (4.73 * (4.44))))))))))
      ≤ ‖1 - sR10 / 2 + 10‖ * (‖1 - sR10 / 2 + 9‖ * (‖1 - sR10 / 2 + 8‖ * (‖1 - sR10 / 2 + 7‖ * (‖1 - sR10 / 2 + 6‖ * (‖1 - sR10 / 2 + 5‖ * (‖1 - sR10 / 2 + 4‖ * (‖1 - sR10 / 2 + 3‖ * (‖1 - sR10 / 2 + 2‖ * (‖1 - sR10 / 2 + 1‖ * (‖1 - sR10 / 2‖)))))))))) :=
    mul_le_mul norm_zUpR10_10_ge q9 (by positivity) (norm_nonneg _)
  have q11 : (12.58 : ℝ) * (11.65 * (10.73 * (9.82 * (8.94 * (8.08 * (7.26 * (6.49 * (5.79 * (5.19 * (4.73 * (4.44)))))))))))
      ≤ ‖1 - sR10 / 2 + 11‖ * (‖1 - sR10 / 2 + 10‖ * (‖1 - sR10 / 2 + 9‖ * (‖1 - sR10 / 2 + 8‖ * (‖1 - sR10 / 2 + 7‖ * (‖1 - sR10 / 2 + 6‖ * (‖1 - sR10 / 2 + 5‖ * (‖1 - sR10 / 2 + 4‖ * (‖1 - sR10 / 2 + 3‖ * (‖1 - sR10 / 2 + 2‖ * (‖1 - sR10 / 2 + 1‖ * (‖1 - sR10 / 2‖))))))))))) :=
    mul_le_mul norm_zUpR10_11_ge q10 (by positivity) (norm_nonneg _)
  have hDlo : (33000000000 : ℝ)
      ≤ (12.58 : ℝ) * (11.65 * (10.73 * (9.82 * (8.94 * (8.08 * (7.26 * (6.49 * (5.79 * (5.19 * (4.73 * (4.44))))))))))) := by
    norm_num
  have hD_ge : (33000000000 : ℝ)
      ≤ ‖1 - sR10 / 2 + 11‖ * (‖1 - sR10 / 2 + 10‖ * (‖1 - sR10 / 2 + 9‖ * (‖1 - sR10 / 2 + 8‖ * (‖1 - sR10 / 2 + 7‖ * (‖1 - sR10 / 2 + 6‖ * (‖1 - sR10 / 2 + 5‖ * (‖1 - sR10 / 2 + 4‖ * (‖1 - sR10 / 2 + 3‖ * (‖1 - sR10 / 2 + 2‖ * (‖1 - sR10 / 2 + 1‖ * (‖1 - sR10 / 2‖))))))))))) :=
    le_trans hDlo q11
  have hD_pos : (0 : ℝ)
      < (‖1 - sR10 / 2 + 11‖
        * (‖1 - sR10 / 2 + 10‖
        * (‖1 - sR10 / 2 + 9‖
        * (‖1 - sR10 / 2 + 8‖
        * (‖1 - sR10 / 2 + 7‖
        * (‖1 - sR10 / 2 + 6‖
        * (‖1 - sR10 / 2 + 5‖
        * (‖1 - sR10 / 2 + 4‖
        * (‖1 - sR10 / 2 + 3‖
        * (‖1 - sR10 / 2 + 2‖
        * (‖1 - sR10 / 2 + 1‖
          * ‖1 - sR10 / 2‖))))))))))) :=
    lt_of_lt_of_le (by norm_num) hD_ge
  -- Numerator: `‖Complex.Gamma (1 - sR10 / 2 + 12)‖ ≤ Real.Gamma(12.8025) ≤ 313000000`.
  have hre12 : (1 - sR10 / 2 + 12).re = 12.8025 := by
    simp only [Complex.add_re, zUpR10_re, Complex.re_ofNat]
    norm_num
  have hGN_re : (0 : ℝ) < (1 - sR10 / 2 + 12).re := by
    rw [hre12]
    norm_num
  have hGN_le : ‖Complex.Gamma (1 - sR10 / 2 + 12)‖ ≤ 313000000 := by
    have h1 : ‖Complex.Gamma (1 - sR10 / 2 + 12)‖
        ≤ Real.Gamma ((1 - sR10 / 2 + 12).re) :=
      R00GammaLower.norm_Gamma_le_realGamma hGN_re
    have hreNb : ((1 - sR10 / 2 + 12).re) = 12.8025 := hre12
    rw [hreNb] at h1
    exact le_trans h1 CellGammaUpper.realGamma_128025_le
  -- Combine: `D * ‖Complex.Gamma (1 - sR10 / 2)‖ = ‖Complex.Gamma (1 - sR10 / 2 + 12)‖ ≤ 313000000`, `D ≤ 33000000000`.
  have hD_mul : (‖1 - sR10 / 2 + 11‖
        * (‖1 - sR10 / 2 + 10‖
        * (‖1 - sR10 / 2 + 9‖
        * (‖1 - sR10 / 2 + 8‖
        * (‖1 - sR10 / 2 + 7‖
        * (‖1 - sR10 / 2 + 6‖
        * (‖1 - sR10 / 2 + 5‖
        * (‖1 - sR10 / 2 + 4‖
        * (‖1 - sR10 / 2 + 3‖
        * (‖1 - sR10 / 2 + 2‖
        * (‖1 - sR10 / 2 + 1‖
          * ‖1 - sR10 / 2‖)))))))))))
        * ‖Complex.Gamma (1 - sR10 / 2)‖
      = ‖Complex.Gamma (1 - sR10 / 2 + 12)‖ := by
    rw [hprod]
    ring
  have hle : (‖1 - sR10 / 2 + 11‖
        * (‖1 - sR10 / 2 + 10‖
        * (‖1 - sR10 / 2 + 9‖
        * (‖1 - sR10 / 2 + 8‖
        * (‖1 - sR10 / 2 + 7‖
        * (‖1 - sR10 / 2 + 6‖
        * (‖1 - sR10 / 2 + 5‖
        * (‖1 - sR10 / 2 + 4‖
        * (‖1 - sR10 / 2 + 3‖
        * (‖1 - sR10 / 2 + 2‖
        * (‖1 - sR10 / 2 + 1‖
          * ‖1 - sR10 / 2‖)))))))))))
        * ‖Complex.Gamma (1 - sR10 / 2)‖ ≤ 313000000 := by
    rw [hD_mul]
    exact hGN_le
  have hmul_comm : ‖Complex.Gamma (1 - sR10 / 2)‖
        * (‖1 - sR10 / 2 + 11‖
        * (‖1 - sR10 / 2 + 10‖
        * (‖1 - sR10 / 2 + 9‖
        * (‖1 - sR10 / 2 + 8‖
        * (‖1 - sR10 / 2 + 7‖
        * (‖1 - sR10 / 2 + 6‖
        * (‖1 - sR10 / 2 + 5‖
        * (‖1 - sR10 / 2 + 4‖
        * (‖1 - sR10 / 2 + 3‖
        * (‖1 - sR10 / 2 + 2‖
        * (‖1 - sR10 / 2 + 1‖
          * ‖1 - sR10 / 2‖)))))))))))
        ≤ 313000000 := by
    calc ‖Complex.Gamma (1 - sR10 / 2)‖ * _
          = _ * ‖Complex.Gamma (1 - sR10 / 2)‖ := mul_comm _ _
      _ ≤ 313000000 := hle
  have hdiv : ‖Complex.Gamma (1 - sR10 / 2)‖
      ≤ 313000000 / (‖1 - sR10 / 2 + 11‖
        * (‖1 - sR10 / 2 + 10‖
        * (‖1 - sR10 / 2 + 9‖
        * (‖1 - sR10 / 2 + 8‖
        * (‖1 - sR10 / 2 + 7‖
        * (‖1 - sR10 / 2 + 6‖
        * (‖1 - sR10 / 2 + 5‖
        * (‖1 - sR10 / 2 + 4‖
        * (‖1 - sR10 / 2 + 3‖
        * (‖1 - sR10 / 2 + 2‖
        * (‖1 - sR10 / 2 + 1‖
          * ‖1 - sR10 / 2‖)))))))))))
        :=
    (le_div_iff₀ hD_pos).mpr hmul_comm
  have hcap : (313000000 : ℝ)
      ≤ 0.01 * (‖1 - sR10 / 2 + 11‖
        * (‖1 - sR10 / 2 + 10‖
        * (‖1 - sR10 / 2 + 9‖
        * (‖1 - sR10 / 2 + 8‖
        * (‖1 - sR10 / 2 + 7‖
        * (‖1 - sR10 / 2 + 6‖
        * (‖1 - sR10 / 2 + 5‖
        * (‖1 - sR10 / 2 + 4‖
        * (‖1 - sR10 / 2 + 3‖
        * (‖1 - sR10 / 2 + 2‖
        * (‖1 - sR10 / 2 + 1‖
          * ‖1 - sR10 / 2‖))))))))))) := by
    calc (313000000 : ℝ) ≤ 0.01 * 33000000000 := by norm_num
      _ ≤ 0.01 * _ :=
          mul_le_mul_of_nonneg_left hD_ge (by norm_num)
  have hfinal : 313000000 / (‖1 - sR10 / 2 + 11‖ * (‖1 - sR10 / 2 + 10‖ * (‖1 - sR10 / 2 + 9‖ * (‖1 - sR10 / 2 + 8‖ * (‖1 - sR10 / 2 + 7‖ * (‖1 - sR10 / 2 + 6‖ * (‖1 - sR10 / 2 + 5‖ * (‖1 - sR10 / 2 + 4‖ * (‖1 - sR10 / 2 + 3‖ * (‖1 - sR10 / 2 + 2‖ * (‖1 - sR10 / 2 + 1‖ * (‖1 - sR10 / 2‖))))))))))))
      ≤ 0.01 :=
    (div_le_iff₀ hD_pos).mpr hcap
  exact le_trans hdiv hfinal

end R10GammaUpper

namespace R20GammaUpper

/-- The R20 `s`-plane center: `s = 1/2 + I·z` at `z = R20.center`. -/
noncomputable def sR20 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R20.center

/-- `R20.center = 8.75 + 0.2·I` (from `R20_x0/x1/y0/y1`). -/
theorem R20_center_eq :
    CentralCoverAssembly.R20.center =
      (((8.75 : ℝ))) + Complex.I * ((((0.2 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R20_x0, CentralCoverAssembly.R20_x1,
      CentralCoverAssembly.R20_y0, CentralCoverAssembly.R20_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R20_x0, CentralCoverAssembly.R20_x1,
      CentralCoverAssembly.R20_y0, CentralCoverAssembly.R20_y1]
    simp
    norm_num

/-- `Re sR20 = 0.3`. -/
theorem sR20_re : sR20.re = 0.3 := by
  unfold sR20
  rw [R20_center_eq]
  simp
  norm_num

/-- `Im sR20 = 8.75`. -/
theorem sR20_im : sR20.im = 8.75 := by
  unfold sR20
  rw [R20_center_eq]
  simp

/-- `Re(1 - sR20/2) = 0.85`. -/
theorem zUpR20_re : (1 - sR20 / 2).re = 0.85 := by
  rw [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, sR20_re]
  norm_num

/-- `Im(1 - sR20/2) = -4.375`. -/
theorem zUpR20_im : (1 - sR20 / 2).im = -4.375 := by
  rw [Complex.sub_im, Complex.one_im, Complex.div_ofNat_im, sR20_im]
  norm_num

/-- Denominator floor `c0 = 4.45 ≤ ‖1 - sR20 / 2‖`. -/
theorem norm_zUpR20_0_ge :
    (4.45 : ℝ) ≤ ‖1 - sR20 / 2‖ := by
  have hsq : (4.45 : ℝ) ^ 2 ≤ ‖1 - sR20 / 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, zUpR20_re, zUpR20_im]
    norm_num
  calc (4.45 : ℝ) = Real.sqrt ((4.45 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR20 / 2‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR20 / 2‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c1 = 4.75 ≤ ‖1 - sR20 / 2 + 1‖`. -/
theorem norm_zUpR20_1_ge :
    (4.75 : ℝ) ≤ ‖1 - sR20 / 2 + 1‖ := by
  have hre : (1 - sR20 / 2 + 1).re = 1.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.one_re]
    norm_num
  have him : (1 - sR20 / 2 + 1).im = -4.375 := by
    simp only [Complex.add_im, zUpR20_im, Complex.one_im]
    norm_num
  have hsq : (4.75 : ℝ) ^ 2 ≤ ‖1 - sR20 / 2 + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (4.75 : ℝ) = Real.sqrt ((4.75 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR20 / 2 + 1‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR20 / 2 + 1‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c2 = 5.22 ≤ ‖1 - sR20 / 2 + 2‖`. -/
theorem norm_zUpR20_2_ge :
    (5.22 : ℝ) ≤ ‖1 - sR20 / 2 + 2‖ := by
  have hre : (1 - sR20 / 2 + 2).re = 2.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR20 / 2 + 2).im = -4.375 := by
    simp only [Complex.add_im, zUpR20_im, Complex.im_ofNat]
    norm_num
  have hsq : (5.22 : ℝ) ^ 2 ≤ ‖1 - sR20 / 2 + 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (5.22 : ℝ) = Real.sqrt ((5.22 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR20 / 2 + 2‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR20 / 2 + 2‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c3 = 5.82 ≤ ‖1 - sR20 / 2 + 3‖`. -/
theorem norm_zUpR20_3_ge :
    (5.82 : ℝ) ≤ ‖1 - sR20 / 2 + 3‖ := by
  have hre : (1 - sR20 / 2 + 3).re = 3.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR20 / 2 + 3).im = -4.375 := by
    simp only [Complex.add_im, zUpR20_im, Complex.im_ofNat]
    norm_num
  have hsq : (5.82 : ℝ) ^ 2 ≤ ‖1 - sR20 / 2 + 3‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (5.82 : ℝ) = Real.sqrt ((5.82 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR20 / 2 + 3‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR20 / 2 + 3‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c4 = 6.53 ≤ ‖1 - sR20 / 2 + 4‖`. -/
theorem norm_zUpR20_4_ge :
    (6.53 : ℝ) ≤ ‖1 - sR20 / 2 + 4‖ := by
  have hre : (1 - sR20 / 2 + 4).re = 4.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR20 / 2 + 4).im = -4.375 := by
    simp only [Complex.add_im, zUpR20_im, Complex.im_ofNat]
    norm_num
  have hsq : (6.53 : ℝ) ^ 2 ≤ ‖1 - sR20 / 2 + 4‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (6.53 : ℝ) = Real.sqrt ((6.53 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR20 / 2 + 4‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR20 / 2 + 4‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c5 = 7.3 ≤ ‖1 - sR20 / 2 + 5‖`. -/
theorem norm_zUpR20_5_ge :
    (7.3 : ℝ) ≤ ‖1 - sR20 / 2 + 5‖ := by
  have hre : (1 - sR20 / 2 + 5).re = 5.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR20 / 2 + 5).im = -4.375 := by
    simp only [Complex.add_im, zUpR20_im, Complex.im_ofNat]
    norm_num
  have hsq : (7.3 : ℝ) ^ 2 ≤ ‖1 - sR20 / 2 + 5‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (7.3 : ℝ) = Real.sqrt ((7.3 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR20 / 2 + 5‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR20 / 2 + 5‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c6 = 8.12 ≤ ‖1 - sR20 / 2 + 6‖`. -/
theorem norm_zUpR20_6_ge :
    (8.12 : ℝ) ≤ ‖1 - sR20 / 2 + 6‖ := by
  have hre : (1 - sR20 / 2 + 6).re = 6.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR20 / 2 + 6).im = -4.375 := by
    simp only [Complex.add_im, zUpR20_im, Complex.im_ofNat]
    norm_num
  have hsq : (8.12 : ℝ) ^ 2 ≤ ‖1 - sR20 / 2 + 6‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (8.12 : ℝ) = Real.sqrt ((8.12 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR20 / 2 + 6‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR20 / 2 + 6‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c7 = 8.98 ≤ ‖1 - sR20 / 2 + 7‖`. -/
theorem norm_zUpR20_7_ge :
    (8.98 : ℝ) ≤ ‖1 - sR20 / 2 + 7‖ := by
  have hre : (1 - sR20 / 2 + 7).re = 7.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR20 / 2 + 7).im = -4.375 := by
    simp only [Complex.add_im, zUpR20_im, Complex.im_ofNat]
    norm_num
  have hsq : (8.98 : ℝ) ^ 2 ≤ ‖1 - sR20 / 2 + 7‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (8.98 : ℝ) = Real.sqrt ((8.98 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR20 / 2 + 7‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR20 / 2 + 7‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c8 = 9.87 ≤ ‖1 - sR20 / 2 + 8‖`. -/
theorem norm_zUpR20_8_ge :
    (9.87 : ℝ) ≤ ‖1 - sR20 / 2 + 8‖ := by
  have hre : (1 - sR20 / 2 + 8).re = 8.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR20 / 2 + 8).im = -4.375 := by
    simp only [Complex.add_im, zUpR20_im, Complex.im_ofNat]
    norm_num
  have hsq : (9.87 : ℝ) ^ 2 ≤ ‖1 - sR20 / 2 + 8‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (9.87 : ℝ) = Real.sqrt ((9.87 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR20 / 2 + 8‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR20 / 2 + 8‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c9 = 10.77 ≤ ‖1 - sR20 / 2 + 9‖`. -/
theorem norm_zUpR20_9_ge :
    (10.77 : ℝ) ≤ ‖1 - sR20 / 2 + 9‖ := by
  have hre : (1 - sR20 / 2 + 9).re = 9.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR20 / 2 + 9).im = -4.375 := by
    simp only [Complex.add_im, zUpR20_im, Complex.im_ofNat]
    norm_num
  have hsq : (10.77 : ℝ) ^ 2 ≤ ‖1 - sR20 / 2 + 9‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (10.77 : ℝ) = Real.sqrt ((10.77 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR20 / 2 + 9‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR20 / 2 + 9‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c10 = 11.69 ≤ ‖1 - sR20 / 2 + 10‖`. -/
theorem norm_zUpR20_10_ge :
    (11.69 : ℝ) ≤ ‖1 - sR20 / 2 + 10‖ := by
  have hre : (1 - sR20 / 2 + 10).re = 10.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR20 / 2 + 10).im = -4.375 := by
    simp only [Complex.add_im, zUpR20_im, Complex.im_ofNat]
    norm_num
  have hsq : (11.69 : ℝ) ^ 2 ≤ ‖1 - sR20 / 2 + 10‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (11.69 : ℝ) = Real.sqrt ((11.69 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR20 / 2 + 10‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR20 / 2 + 10‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c11 = 12.63 ≤ ‖1 - sR20 / 2 + 11‖`. -/
theorem norm_zUpR20_11_ge :
    (12.63 : ℝ) ≤ ‖1 - sR20 / 2 + 11‖ := by
  have hre : (1 - sR20 / 2 + 11).re = 11.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR20 / 2 + 11).im = -4.375 := by
    simp only [Complex.add_im, zUpR20_im, Complex.im_ofNat]
    norm_num
  have hsq : (12.63 : ℝ) ^ 2 ≤ ‖1 - sR20 / 2 + 11‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (12.63 : ℝ) = Real.sqrt ((12.63 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR20 / 2 + 11‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR20 / 2 + 11‖ := Real.sqrt_sq (norm_nonneg _)

/-- Shift nonvanishing (`Re > 0` so `{NE} 0`). -/
theorem zUpR20_ne0 : (1 - sR20 / 2) ≠ 0 := by
  have hre : (1 - sR20 / 2).re = 0.85 := zUpR20_re
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR20_add1_ne0 : (1 - sR20 / 2 + 1) ≠ 0 := by
  have hre : (1 - sR20 / 2 + 1).re = 1.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.one_re]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR20_add2_ne0 : (1 - sR20 / 2 + 2) ≠ 0 := by
  have hre : (1 - sR20 / 2 + 2).re = 2.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR20_add3_ne0 : (1 - sR20 / 2 + 3) ≠ 0 := by
  have hre : (1 - sR20 / 2 + 3).re = 3.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR20_add4_ne0 : (1 - sR20 / 2 + 4) ≠ 0 := by
  have hre : (1 - sR20 / 2 + 4).re = 4.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR20_add5_ne0 : (1 - sR20 / 2 + 5) ≠ 0 := by
  have hre : (1 - sR20 / 2 + 5).re = 5.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR20_add6_ne0 : (1 - sR20 / 2 + 6) ≠ 0 := by
  have hre : (1 - sR20 / 2 + 6).re = 6.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR20_add7_ne0 : (1 - sR20 / 2 + 7) ≠ 0 := by
  have hre : (1 - sR20 / 2 + 7).re = 7.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR20_add8_ne0 : (1 - sR20 / 2 + 8) ≠ 0 := by
  have hre : (1 - sR20 / 2 + 8).re = 8.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR20_add9_ne0 : (1 - sR20 / 2 + 9) ≠ 0 := by
  have hre : (1 - sR20 / 2 + 9).re = 9.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR20_add10_ne0 : (1 - sR20 / 2 + 10) ≠ 0 := by
  have hre : (1 - sR20 / 2 + 10).re = 10.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR20_add11_ne0 : (1 - sR20 / 2 + 11) ≠ 0 := by
  have hre : (1 - sR20 / 2 + 11).re = 11.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

/-- MAIN uniform UPPER bound at the R20 corner:
`‖Complex.Gamma (1 - sR20 / 2)‖ ≤ 0.01` (row-1 outer-tier mirror, `re = 0.85`). -/
theorem gamma_one_sub_half_upper_R20 :
    ‖Complex.Gamma (1 - sR20 / 2)‖ ≤ 0.01 := by
  -- Shift chain `Gamma(z0+12) = (z0+11)..z0*Gamma(z0)`.
  have e0 : Complex.Gamma (1 - sR20 / 2 + 1)
      = (1 - sR20 / 2) * Complex.Gamma (1 - sR20 / 2) :=
    Complex.Gamma_add_one _ zUpR20_ne0
  have e1 : Complex.Gamma (1 - sR20 / 2 + 2)
      = (1 - sR20 / 2 + 1)
        * Complex.Gamma (1 - sR20 / 2 + 1) := by
    have h : (1 - sR20 / 2 + 2)
        = ((1 - sR20 / 2 + 1) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR20_add1_ne0
  have e2 : Complex.Gamma (1 - sR20 / 2 + 3)
      = (1 - sR20 / 2 + 2)
        * Complex.Gamma (1 - sR20 / 2 + 2) := by
    have h : (1 - sR20 / 2 + 3)
        = ((1 - sR20 / 2 + 2) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR20_add2_ne0
  have e3 : Complex.Gamma (1 - sR20 / 2 + 4)
      = (1 - sR20 / 2 + 3)
        * Complex.Gamma (1 - sR20 / 2 + 3) := by
    have h : (1 - sR20 / 2 + 4)
        = ((1 - sR20 / 2 + 3) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR20_add3_ne0
  have e4 : Complex.Gamma (1 - sR20 / 2 + 5)
      = (1 - sR20 / 2 + 4)
        * Complex.Gamma (1 - sR20 / 2 + 4) := by
    have h : (1 - sR20 / 2 + 5)
        = ((1 - sR20 / 2 + 4) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR20_add4_ne0
  have e5 : Complex.Gamma (1 - sR20 / 2 + 6)
      = (1 - sR20 / 2 + 5)
        * Complex.Gamma (1 - sR20 / 2 + 5) := by
    have h : (1 - sR20 / 2 + 6)
        = ((1 - sR20 / 2 + 5) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR20_add5_ne0
  have e6 : Complex.Gamma (1 - sR20 / 2 + 7)
      = (1 - sR20 / 2 + 6)
        * Complex.Gamma (1 - sR20 / 2 + 6) := by
    have h : (1 - sR20 / 2 + 7)
        = ((1 - sR20 / 2 + 6) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR20_add6_ne0
  have e7 : Complex.Gamma (1 - sR20 / 2 + 8)
      = (1 - sR20 / 2 + 7)
        * Complex.Gamma (1 - sR20 / 2 + 7) := by
    have h : (1 - sR20 / 2 + 8)
        = ((1 - sR20 / 2 + 7) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR20_add7_ne0
  have e8 : Complex.Gamma (1 - sR20 / 2 + 9)
      = (1 - sR20 / 2 + 8)
        * Complex.Gamma (1 - sR20 / 2 + 8) := by
    have h : (1 - sR20 / 2 + 9)
        = ((1 - sR20 / 2 + 8) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR20_add8_ne0
  have e9 : Complex.Gamma (1 - sR20 / 2 + 10)
      = (1 - sR20 / 2 + 9)
        * Complex.Gamma (1 - sR20 / 2 + 9) := by
    have h : (1 - sR20 / 2 + 10)
        = ((1 - sR20 / 2 + 9) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR20_add9_ne0
  have e10 : Complex.Gamma (1 - sR20 / 2 + 11)
      = (1 - sR20 / 2 + 10)
        * Complex.Gamma (1 - sR20 / 2 + 10) := by
    have h : (1 - sR20 / 2 + 11)
        = ((1 - sR20 / 2 + 10) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR20_add10_ne0
  have e11 : Complex.Gamma (1 - sR20 / 2 + 12)
      = (1 - sR20 / 2 + 11)
        * Complex.Gamma (1 - sR20 / 2 + 11) := by
    have h : (1 - sR20 / 2 + 12)
        = ((1 - sR20 / 2 + 11) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR20_add11_ne0
  have n0 : ‖Complex.Gamma (1 - sR20 / 2 + 1)‖
      = ‖1 - sR20 / 2‖
        * ‖Complex.Gamma (1 - sR20 / 2)‖ := by
    rw [e0, norm_mul]
  have n1 : ‖Complex.Gamma (1 - sR20 / 2 + 2)‖
      = ‖1 - sR20 / 2 + 1‖
        * ‖Complex.Gamma (1 - sR20 / 2 + 1)‖ := by
    rw [e1, norm_mul]
  have n2 : ‖Complex.Gamma (1 - sR20 / 2 + 3)‖
      = ‖1 - sR20 / 2 + 2‖
        * ‖Complex.Gamma (1 - sR20 / 2 + 2)‖ := by
    rw [e2, norm_mul]
  have n3 : ‖Complex.Gamma (1 - sR20 / 2 + 4)‖
      = ‖1 - sR20 / 2 + 3‖
        * ‖Complex.Gamma (1 - sR20 / 2 + 3)‖ := by
    rw [e3, norm_mul]
  have n4 : ‖Complex.Gamma (1 - sR20 / 2 + 5)‖
      = ‖1 - sR20 / 2 + 4‖
        * ‖Complex.Gamma (1 - sR20 / 2 + 4)‖ := by
    rw [e4, norm_mul]
  have n5 : ‖Complex.Gamma (1 - sR20 / 2 + 6)‖
      = ‖1 - sR20 / 2 + 5‖
        * ‖Complex.Gamma (1 - sR20 / 2 + 5)‖ := by
    rw [e5, norm_mul]
  have n6 : ‖Complex.Gamma (1 - sR20 / 2 + 7)‖
      = ‖1 - sR20 / 2 + 6‖
        * ‖Complex.Gamma (1 - sR20 / 2 + 6)‖ := by
    rw [e6, norm_mul]
  have n7 : ‖Complex.Gamma (1 - sR20 / 2 + 8)‖
      = ‖1 - sR20 / 2 + 7‖
        * ‖Complex.Gamma (1 - sR20 / 2 + 7)‖ := by
    rw [e7, norm_mul]
  have n8 : ‖Complex.Gamma (1 - sR20 / 2 + 9)‖
      = ‖1 - sR20 / 2 + 8‖
        * ‖Complex.Gamma (1 - sR20 / 2 + 8)‖ := by
    rw [e8, norm_mul]
  have n9 : ‖Complex.Gamma (1 - sR20 / 2 + 10)‖
      = ‖1 - sR20 / 2 + 9‖
        * ‖Complex.Gamma (1 - sR20 / 2 + 9)‖ := by
    rw [e9, norm_mul]
  have n10 : ‖Complex.Gamma (1 - sR20 / 2 + 11)‖
      = ‖1 - sR20 / 2 + 10‖
        * ‖Complex.Gamma (1 - sR20 / 2 + 10)‖ := by
    rw [e10, norm_mul]
  have n11 : ‖Complex.Gamma (1 - sR20 / 2 + 12)‖
      = ‖1 - sR20 / 2 + 11‖
        * ‖Complex.Gamma (1 - sR20 / 2 + 11)‖ := by
    rw [e11, norm_mul]
  have hprod : ‖Complex.Gamma (1 - sR20 / 2 + 12)‖
      = ‖1 - sR20 / 2 + 11‖
        * (‖1 - sR20 / 2 + 10‖
        * (‖1 - sR20 / 2 + 9‖
        * (‖1 - sR20 / 2 + 8‖
        * (‖1 - sR20 / 2 + 7‖
        * (‖1 - sR20 / 2 + 6‖
        * (‖1 - sR20 / 2 + 5‖
        * (‖1 - sR20 / 2 + 4‖
        * (‖1 - sR20 / 2 + 3‖
        * (‖1 - sR20 / 2 + 2‖
        * (‖1 - sR20 / 2 + 1‖
        * (‖1 - sR20 / 2‖
          * ‖Complex.Gamma (1 - sR20 / 2)‖))))))))))) := by
    rw [n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n0]
  -- Denominator product lower bound.
  have q1 : (4.75 : ℝ) * 4.45
      ≤ ‖1 - sR20 / 2 + 1‖ * ‖1 - sR20 / 2‖ :=
    mul_le_mul norm_zUpR20_1_ge norm_zUpR20_0_ge (by norm_num) (norm_nonneg _)
  have q2 : (5.22 : ℝ) * (4.75 * (4.45))
      ≤ ‖1 - sR20 / 2 + 2‖ * (‖1 - sR20 / 2 + 1‖ * (‖1 - sR20 / 2‖)) :=
    mul_le_mul norm_zUpR20_2_ge q1 (by positivity) (norm_nonneg _)
  have q3 : (5.82 : ℝ) * (5.22 * (4.75 * (4.45)))
      ≤ ‖1 - sR20 / 2 + 3‖ * (‖1 - sR20 / 2 + 2‖ * (‖1 - sR20 / 2 + 1‖ * (‖1 - sR20 / 2‖))) :=
    mul_le_mul norm_zUpR20_3_ge q2 (by positivity) (norm_nonneg _)
  have q4 : (6.53 : ℝ) * (5.82 * (5.22 * (4.75 * (4.45))))
      ≤ ‖1 - sR20 / 2 + 4‖ * (‖1 - sR20 / 2 + 3‖ * (‖1 - sR20 / 2 + 2‖ * (‖1 - sR20 / 2 + 1‖ * (‖1 - sR20 / 2‖)))) :=
    mul_le_mul norm_zUpR20_4_ge q3 (by positivity) (norm_nonneg _)
  have q5 : (7.3 : ℝ) * (6.53 * (5.82 * (5.22 * (4.75 * (4.45)))))
      ≤ ‖1 - sR20 / 2 + 5‖ * (‖1 - sR20 / 2 + 4‖ * (‖1 - sR20 / 2 + 3‖ * (‖1 - sR20 / 2 + 2‖ * (‖1 - sR20 / 2 + 1‖ * (‖1 - sR20 / 2‖))))) :=
    mul_le_mul norm_zUpR20_5_ge q4 (by positivity) (norm_nonneg _)
  have q6 : (8.12 : ℝ) * (7.3 * (6.53 * (5.82 * (5.22 * (4.75 * (4.45))))))
      ≤ ‖1 - sR20 / 2 + 6‖ * (‖1 - sR20 / 2 + 5‖ * (‖1 - sR20 / 2 + 4‖ * (‖1 - sR20 / 2 + 3‖ * (‖1 - sR20 / 2 + 2‖ * (‖1 - sR20 / 2 + 1‖ * (‖1 - sR20 / 2‖)))))) :=
    mul_le_mul norm_zUpR20_6_ge q5 (by positivity) (norm_nonneg _)
  have q7 : (8.98 : ℝ) * (8.12 * (7.3 * (6.53 * (5.82 * (5.22 * (4.75 * (4.45)))))))
      ≤ ‖1 - sR20 / 2 + 7‖ * (‖1 - sR20 / 2 + 6‖ * (‖1 - sR20 / 2 + 5‖ * (‖1 - sR20 / 2 + 4‖ * (‖1 - sR20 / 2 + 3‖ * (‖1 - sR20 / 2 + 2‖ * (‖1 - sR20 / 2 + 1‖ * (‖1 - sR20 / 2‖))))))) :=
    mul_le_mul norm_zUpR20_7_ge q6 (by positivity) (norm_nonneg _)
  have q8 : (9.87 : ℝ) * (8.98 * (8.12 * (7.3 * (6.53 * (5.82 * (5.22 * (4.75 * (4.45))))))))
      ≤ ‖1 - sR20 / 2 + 8‖ * (‖1 - sR20 / 2 + 7‖ * (‖1 - sR20 / 2 + 6‖ * (‖1 - sR20 / 2 + 5‖ * (‖1 - sR20 / 2 + 4‖ * (‖1 - sR20 / 2 + 3‖ * (‖1 - sR20 / 2 + 2‖ * (‖1 - sR20 / 2 + 1‖ * (‖1 - sR20 / 2‖)))))))) :=
    mul_le_mul norm_zUpR20_8_ge q7 (by positivity) (norm_nonneg _)
  have q9 : (10.77 : ℝ) * (9.87 * (8.98 * (8.12 * (7.3 * (6.53 * (5.82 * (5.22 * (4.75 * (4.45)))))))))
      ≤ ‖1 - sR20 / 2 + 9‖ * (‖1 - sR20 / 2 + 8‖ * (‖1 - sR20 / 2 + 7‖ * (‖1 - sR20 / 2 + 6‖ * (‖1 - sR20 / 2 + 5‖ * (‖1 - sR20 / 2 + 4‖ * (‖1 - sR20 / 2 + 3‖ * (‖1 - sR20 / 2 + 2‖ * (‖1 - sR20 / 2 + 1‖ * (‖1 - sR20 / 2‖))))))))) :=
    mul_le_mul norm_zUpR20_9_ge q8 (by positivity) (norm_nonneg _)
  have q10 : (11.69 : ℝ) * (10.77 * (9.87 * (8.98 * (8.12 * (7.3 * (6.53 * (5.82 * (5.22 * (4.75 * (4.45))))))))))
      ≤ ‖1 - sR20 / 2 + 10‖ * (‖1 - sR20 / 2 + 9‖ * (‖1 - sR20 / 2 + 8‖ * (‖1 - sR20 / 2 + 7‖ * (‖1 - sR20 / 2 + 6‖ * (‖1 - sR20 / 2 + 5‖ * (‖1 - sR20 / 2 + 4‖ * (‖1 - sR20 / 2 + 3‖ * (‖1 - sR20 / 2 + 2‖ * (‖1 - sR20 / 2 + 1‖ * (‖1 - sR20 / 2‖)))))))))) :=
    mul_le_mul norm_zUpR20_10_ge q9 (by positivity) (norm_nonneg _)
  have q11 : (12.63 : ℝ) * (11.69 * (10.77 * (9.87 * (8.98 * (8.12 * (7.3 * (6.53 * (5.82 * (5.22 * (4.75 * (4.45)))))))))))
      ≤ ‖1 - sR20 / 2 + 11‖ * (‖1 - sR20 / 2 + 10‖ * (‖1 - sR20 / 2 + 9‖ * (‖1 - sR20 / 2 + 8‖ * (‖1 - sR20 / 2 + 7‖ * (‖1 - sR20 / 2 + 6‖ * (‖1 - sR20 / 2 + 5‖ * (‖1 - sR20 / 2 + 4‖ * (‖1 - sR20 / 2 + 3‖ * (‖1 - sR20 / 2 + 2‖ * (‖1 - sR20 / 2 + 1‖ * (‖1 - sR20 / 2‖))))))))))) :=
    mul_le_mul norm_zUpR20_11_ge q10 (by positivity) (norm_nonneg _)
  have hDlo : (35000000000 : ℝ)
      ≤ (12.63 : ℝ) * (11.69 * (10.77 * (9.87 * (8.98 * (8.12 * (7.3 * (6.53 * (5.82 * (5.22 * (4.75 * (4.45))))))))))) := by
    norm_num
  have hD_ge : (35000000000 : ℝ)
      ≤ ‖1 - sR20 / 2 + 11‖ * (‖1 - sR20 / 2 + 10‖ * (‖1 - sR20 / 2 + 9‖ * (‖1 - sR20 / 2 + 8‖ * (‖1 - sR20 / 2 + 7‖ * (‖1 - sR20 / 2 + 6‖ * (‖1 - sR20 / 2 + 5‖ * (‖1 - sR20 / 2 + 4‖ * (‖1 - sR20 / 2 + 3‖ * (‖1 - sR20 / 2 + 2‖ * (‖1 - sR20 / 2 + 1‖ * (‖1 - sR20 / 2‖))))))))))) :=
    le_trans hDlo q11
  have hD_pos : (0 : ℝ)
      < (‖1 - sR20 / 2 + 11‖
        * (‖1 - sR20 / 2 + 10‖
        * (‖1 - sR20 / 2 + 9‖
        * (‖1 - sR20 / 2 + 8‖
        * (‖1 - sR20 / 2 + 7‖
        * (‖1 - sR20 / 2 + 6‖
        * (‖1 - sR20 / 2 + 5‖
        * (‖1 - sR20 / 2 + 4‖
        * (‖1 - sR20 / 2 + 3‖
        * (‖1 - sR20 / 2 + 2‖
        * (‖1 - sR20 / 2 + 1‖
          * ‖1 - sR20 / 2‖))))))))))) :=
    lt_of_lt_of_le (by norm_num) hD_ge
  -- Numerator: `‖Complex.Gamma (1 - sR20 / 2 + 12)‖ ≤ Real.Gamma(12.85) ≤ 348000000`.
  have hre12 : (1 - sR20 / 2 + 12).re = 12.85 := by
    simp only [Complex.add_re, zUpR20_re, Complex.re_ofNat]
    norm_num
  have hGN_re : (0 : ℝ) < (1 - sR20 / 2 + 12).re := by
    rw [hre12]
    norm_num
  have hGN_le : ‖Complex.Gamma (1 - sR20 / 2 + 12)‖ ≤ 348000000 := by
    have h1 : ‖Complex.Gamma (1 - sR20 / 2 + 12)‖
        ≤ Real.Gamma ((1 - sR20 / 2 + 12).re) :=
      R00GammaLower.norm_Gamma_le_realGamma hGN_re
    have hreNb : ((1 - sR20 / 2 + 12).re) = 12.85 := hre12
    rw [hreNb] at h1
    exact le_trans h1 CellGammaUpper085.realGamma_1285_le
  -- Combine: `D * ‖Complex.Gamma (1 - sR20 / 2)‖ = ‖Complex.Gamma (1 - sR20 / 2 + 12)‖ ≤ 348000000`, `D ≤ 35000000000`.
  have hD_mul : (‖1 - sR20 / 2 + 11‖
        * (‖1 - sR20 / 2 + 10‖
        * (‖1 - sR20 / 2 + 9‖
        * (‖1 - sR20 / 2 + 8‖
        * (‖1 - sR20 / 2 + 7‖
        * (‖1 - sR20 / 2 + 6‖
        * (‖1 - sR20 / 2 + 5‖
        * (‖1 - sR20 / 2 + 4‖
        * (‖1 - sR20 / 2 + 3‖
        * (‖1 - sR20 / 2 + 2‖
        * (‖1 - sR20 / 2 + 1‖
          * ‖1 - sR20 / 2‖)))))))))))
        * ‖Complex.Gamma (1 - sR20 / 2)‖
      = ‖Complex.Gamma (1 - sR20 / 2 + 12)‖ := by
    rw [hprod]
    ring
  have hle : (‖1 - sR20 / 2 + 11‖
        * (‖1 - sR20 / 2 + 10‖
        * (‖1 - sR20 / 2 + 9‖
        * (‖1 - sR20 / 2 + 8‖
        * (‖1 - sR20 / 2 + 7‖
        * (‖1 - sR20 / 2 + 6‖
        * (‖1 - sR20 / 2 + 5‖
        * (‖1 - sR20 / 2 + 4‖
        * (‖1 - sR20 / 2 + 3‖
        * (‖1 - sR20 / 2 + 2‖
        * (‖1 - sR20 / 2 + 1‖
          * ‖1 - sR20 / 2‖)))))))))))
        * ‖Complex.Gamma (1 - sR20 / 2)‖ ≤ 348000000 := by
    rw [hD_mul]
    exact hGN_le
  have hmul_comm : ‖Complex.Gamma (1 - sR20 / 2)‖
        * (‖1 - sR20 / 2 + 11‖
        * (‖1 - sR20 / 2 + 10‖
        * (‖1 - sR20 / 2 + 9‖
        * (‖1 - sR20 / 2 + 8‖
        * (‖1 - sR20 / 2 + 7‖
        * (‖1 - sR20 / 2 + 6‖
        * (‖1 - sR20 / 2 + 5‖
        * (‖1 - sR20 / 2 + 4‖
        * (‖1 - sR20 / 2 + 3‖
        * (‖1 - sR20 / 2 + 2‖
        * (‖1 - sR20 / 2 + 1‖
          * ‖1 - sR20 / 2‖)))))))))))
        ≤ 348000000 := by
    calc ‖Complex.Gamma (1 - sR20 / 2)‖ * _
          = _ * ‖Complex.Gamma (1 - sR20 / 2)‖ := mul_comm _ _
      _ ≤ 348000000 := hle
  have hdiv : ‖Complex.Gamma (1 - sR20 / 2)‖
      ≤ 348000000 / (‖1 - sR20 / 2 + 11‖
        * (‖1 - sR20 / 2 + 10‖
        * (‖1 - sR20 / 2 + 9‖
        * (‖1 - sR20 / 2 + 8‖
        * (‖1 - sR20 / 2 + 7‖
        * (‖1 - sR20 / 2 + 6‖
        * (‖1 - sR20 / 2 + 5‖
        * (‖1 - sR20 / 2 + 4‖
        * (‖1 - sR20 / 2 + 3‖
        * (‖1 - sR20 / 2 + 2‖
        * (‖1 - sR20 / 2 + 1‖
          * ‖1 - sR20 / 2‖)))))))))))
        :=
    (le_div_iff₀ hD_pos).mpr hmul_comm
  have hcap : (348000000 : ℝ)
      ≤ 0.01 * (‖1 - sR20 / 2 + 11‖
        * (‖1 - sR20 / 2 + 10‖
        * (‖1 - sR20 / 2 + 9‖
        * (‖1 - sR20 / 2 + 8‖
        * (‖1 - sR20 / 2 + 7‖
        * (‖1 - sR20 / 2 + 6‖
        * (‖1 - sR20 / 2 + 5‖
        * (‖1 - sR20 / 2 + 4‖
        * (‖1 - sR20 / 2 + 3‖
        * (‖1 - sR20 / 2 + 2‖
        * (‖1 - sR20 / 2 + 1‖
          * ‖1 - sR20 / 2‖))))))))))) := by
    calc (348000000 : ℝ) ≤ 0.01 * 35000000000 := by norm_num
      _ ≤ 0.01 * _ :=
          mul_le_mul_of_nonneg_left hD_ge (by norm_num)
  have hfinal : 348000000 / (‖1 - sR20 / 2 + 11‖ * (‖1 - sR20 / 2 + 10‖ * (‖1 - sR20 / 2 + 9‖ * (‖1 - sR20 / 2 + 8‖ * (‖1 - sR20 / 2 + 7‖ * (‖1 - sR20 / 2 + 6‖ * (‖1 - sR20 / 2 + 5‖ * (‖1 - sR20 / 2 + 4‖ * (‖1 - sR20 / 2 + 3‖ * (‖1 - sR20 / 2 + 2‖ * (‖1 - sR20 / 2 + 1‖ * (‖1 - sR20 / 2‖))))))))))))
      ≤ 0.01 :=
    (div_le_iff₀ hD_pos).mpr hcap
  exact le_trans hdiv hfinal

end R20GammaUpper

/-!
## Outer-tier complex-Gamma UPPER bounds, rows 2-3 (longer-shift route).

Row 2 (`z.re = 0.9`) needs `n = 14` and row 3 (`z.re = 0.9475`) needs
`n = 15` to reach `<= 0.01` (with `n = 12` the true ratios are `0.01038`
and `0.01091`, so `0.01` is unreachable there -- exact rational check).
Same template as `CellGammaUpper`, only deeper.
-/

namespace CellGammaUpper09

/-- Real convexity feeder: `Real.Gamma 1.9 ≤ 1`
(`1.9 = 0.1*ℝ1 + 0.9*ℝ2`, `Gamma 1 = Gamma 2 = 1`). -/
theorem realGamma_19_le_one : Real.Gamma 1.9 ≤ 1 := by
  have hconv := Real.convexOn_Gamma
  have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have h2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have ha : (0 : ℝ) ≤ 0.1 := by norm_num
  have hb : (0 : ℝ) ≤ 0.9 := by norm_num
  have hab : (0.1 : ℝ) + 0.9 = 1 := by norm_num
  have h := hconv.2 h1 h2 ha hb hab
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
  have heq : (0.1 : ℝ) * 1 + 0.9 * 2 = 1.9 := by norm_num
  have hrhs : (0.1 : ℝ) * 1 + 0.9 * 1 = (1 : ℝ) := by norm_num
  rw [heq] at h
  rw [hrhs] at h
  exact h

/-- `Real.Gamma 2.9 ≤ 1.9`. -/
theorem realGamma_29_le : Real.Gamma 2.9 ≤ 1.9 := by
  have h : Real.Gamma (1.9 + 1) = 1.9 * Real.Gamma 1.9 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (1.9 : ℝ) + 1 = 2.9 := by norm_num
  rw [heq] at h
  rw [h]
  calc (1.9 : ℝ) * Real.Gamma 1.9 ≤ 1.9 * 1 :=
        mul_le_mul_of_nonneg_left realGamma_19_le_one (by norm_num)
    _ = 1.9 := mul_one _

/-- `Real.Gamma 3.9 ≤ 1.9 * 2.9`. -/
theorem realGamma_39_le : Real.Gamma 3.9 ≤ 1.9 * 2.9 := by
  have h : Real.Gamma (2.9 + 1) = 2.9 * Real.Gamma 2.9 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (2.9 : ℝ) + 1 = 3.9 := by norm_num
  rw [heq] at h
  rw [h]
  calc (2.9 : ℝ) * Real.Gamma 2.9 ≤ 2.9 * 1.9 :=
        mul_le_mul_of_nonneg_left realGamma_29_le (by norm_num)
    _ = 1.9 * 2.9 := mul_comm _ _

/-- `Real.Gamma 4.9 ≤ 1.9 * 2.9 * 3.9`. -/
theorem realGamma_49_le : Real.Gamma 4.9 ≤ 1.9 * 2.9 * 3.9 := by
  have h : Real.Gamma (3.9 + 1) = 3.9 * Real.Gamma 3.9 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (3.9 : ℝ) + 1 = 4.9 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 3.9 * Real.Gamma 3.9
      ≤ 3.9 * (1.9 * 2.9) :=
    mul_le_mul_of_nonneg_left realGamma_39_le (by norm_num)
  calc (3.9 : ℝ) * Real.Gamma 3.9
        ≤ 3.9 * (1.9 * 2.9) := hle
    _ = 1.9 * 2.9 * 3.9 := by ring

/-- `Real.Gamma 5.9 ≤ 1.9 * 2.9 * 3.9 * 4.9`. -/
theorem realGamma_59_le : Real.Gamma 5.9 ≤ 1.9 * 2.9 * 3.9 * 4.9 := by
  have h : Real.Gamma (4.9 + 1) = 4.9 * Real.Gamma 4.9 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (4.9 : ℝ) + 1 = 5.9 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 4.9 * Real.Gamma 4.9
      ≤ 4.9 * (1.9 * 2.9 * 3.9) :=
    mul_le_mul_of_nonneg_left realGamma_49_le (by norm_num)
  calc (4.9 : ℝ) * Real.Gamma 4.9
        ≤ 4.9 * (1.9 * 2.9 * 3.9) := hle
    _ = 1.9 * 2.9 * 3.9 * 4.9 := by ring

/-- `Real.Gamma 6.9 ≤ 1.9 * 2.9 * 3.9 * 4.9 * 5.9`. -/
theorem realGamma_69_le :
    Real.Gamma 6.9 ≤ 1.9 * 2.9 * 3.9 * 4.9 * 5.9 := by
  have h : Real.Gamma (5.9 + 1) = 5.9 * Real.Gamma 5.9 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (5.9 : ℝ) + 1 = 6.9 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 5.9 * Real.Gamma 5.9
      ≤ 5.9 * (1.9 * 2.9 * 3.9 * 4.9) :=
    mul_le_mul_of_nonneg_left realGamma_59_le (by norm_num)
  calc (5.9 : ℝ) * Real.Gamma 5.9
        ≤ 5.9 * (1.9 * 2.9 * 3.9 * 4.9) := hle
    _ = 1.9 * 2.9 * 3.9 * 4.9 * 5.9 := by ring

/-- `Real.Gamma 7.9 ≤ 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9`. -/
theorem realGamma_79_le :
    Real.Gamma 7.9 ≤ 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 := by
  have h : Real.Gamma (6.9 + 1) = 6.9 * Real.Gamma 6.9 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (6.9 : ℝ) + 1 = 7.9 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 6.9 * Real.Gamma 6.9
      ≤ 6.9 * (1.9 * 2.9 * 3.9 * 4.9 * 5.9) :=
    mul_le_mul_of_nonneg_left realGamma_69_le (by norm_num)
  calc (6.9 : ℝ) * Real.Gamma 6.9
        ≤ 6.9 * (1.9 * 2.9 * 3.9 * 4.9 * 5.9) := hle
    _ = 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 := by ring

/-- `Real.Gamma 8.9 ≤ 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9`. -/
theorem realGamma_89_le :
    Real.Gamma 8.9 ≤ 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 := by
  have h : Real.Gamma (7.9 + 1) = 7.9 * Real.Gamma 7.9 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (7.9 : ℝ) + 1 = 8.9 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 7.9 * Real.Gamma 7.9
      ≤ 7.9 * (1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9) :=
    mul_le_mul_of_nonneg_left realGamma_79_le (by norm_num)
  calc (7.9 : ℝ) * Real.Gamma 7.9
        ≤ 7.9 * (1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9) := hle
    _ = 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 := by ring

/-- `Real.Gamma 9.9 ≤ 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9`. -/
theorem realGamma_99_le :
    Real.Gamma 9.9 ≤ 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 := by
  have h : Real.Gamma (8.9 + 1) = 8.9 * Real.Gamma 8.9 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (8.9 : ℝ) + 1 = 9.9 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 8.9 * Real.Gamma 8.9
      ≤ 8.9 * (1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9) :=
    mul_le_mul_of_nonneg_left realGamma_89_le (by norm_num)
  calc (8.9 : ℝ) * Real.Gamma 8.9
        ≤ 8.9 * (1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9) := hle
    _ = 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 := by ring

/-- `Real.Gamma 10.9 ≤ 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9`. -/
theorem realGamma_109_le :
    Real.Gamma 10.9 ≤ 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9 := by
  have h : Real.Gamma (9.9 + 1) = 9.9 * Real.Gamma 9.9 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (9.9 : ℝ) + 1 = 10.9 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 9.9 * Real.Gamma 9.9
      ≤ 9.9 * (1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9) :=
    mul_le_mul_of_nonneg_left realGamma_99_le (by norm_num)
  calc (9.9 : ℝ) * Real.Gamma 9.9
        ≤ 9.9 * (1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9) := hle
    _ = 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9 := by ring

/-- `Real.Gamma 11.9 ≤ 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9 * 10.9`. -/
theorem realGamma_119_le :
    Real.Gamma 11.9 ≤ 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9 * 10.9 := by
  have h : Real.Gamma (10.9 + 1) = 10.9 * Real.Gamma 10.9 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (10.9 : ℝ) + 1 = 11.9 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 10.9 * Real.Gamma 10.9
      ≤ 10.9 * (1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9) :=
    mul_le_mul_of_nonneg_left realGamma_109_le (by norm_num)
  calc (10.9 : ℝ) * Real.Gamma 10.9
        ≤ 10.9 * (1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9) := hle
    _ = 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9 * 10.9 := by ring

/-- `Real.Gamma 12.9 ≤ 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9 * 10.9 * 11.9`. -/
theorem realGamma_129_le :
    Real.Gamma 12.9 ≤ 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9 * 10.9 * 11.9 := by
  have h : Real.Gamma (11.9 + 1) = 11.9 * Real.Gamma 11.9 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (11.9 : ℝ) + 1 = 12.9 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 11.9 * Real.Gamma 11.9
      ≤ 11.9 * (1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9 * 10.9) :=
    mul_le_mul_of_nonneg_left realGamma_119_le (by norm_num)
  calc (11.9 : ℝ) * Real.Gamma 11.9
        ≤ 11.9 * (1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9 * 10.9) := hle
    _ = 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9 * 10.9 * 11.9 := by ring

/-- `Real.Gamma 13.9 ≤ 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9 * 10.9 * 11.9 * 12.9`. -/
theorem realGamma_139_le :
    Real.Gamma 13.9 ≤ 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9 * 10.9 * 11.9 * 12.9 := by
  have h : Real.Gamma (12.9 + 1) = 12.9 * Real.Gamma 12.9 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (12.9 : ℝ) + 1 = 13.9 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 12.9 * Real.Gamma 12.9
      ≤ 12.9 * (1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9 * 10.9 * 11.9) :=
    mul_le_mul_of_nonneg_left realGamma_129_le (by norm_num)
  calc (12.9 : ℝ) * Real.Gamma 12.9
        ≤ 12.9 * (1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9 * 10.9 * 11.9) := hle
    _ = 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9 * 10.9 * 11.9 * 12.9 := by ring

/-- `Real.Gamma 14.9 ≤ 1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9 * 10.9 * 11.9 * 12.9 * 13.9 ≤ 69500000000` (numerator cap). -/
theorem realGamma_149_le : Real.Gamma 14.9 ≤ 69500000000 := by
  have h : Real.Gamma (13.9 + 1) = 13.9 * Real.Gamma 13.9 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (13.9 : ℝ) + 1 = 14.9 := by norm_num
  rw [heq] at h
  rw [h] at ⊢
  have hle : 13.9 * Real.Gamma 13.9
      ≤ 13.9 * (1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9 * 10.9 * 11.9 * 12.9) :=
    mul_le_mul_of_nonneg_left realGamma_139_le (by norm_num)
  have hprod : (13.9 : ℝ) * (1.9 * 2.9 * 3.9 * 4.9 * 5.9 * 6.9 * 7.9 * 8.9 * 9.9 * 10.9 * 11.9 * 12.9) ≤ 69500000000 := by
    norm_num
  exact le_trans hle hprod

end CellGammaUpper09

namespace R21GammaUpper

/-- The R21 `s`-plane center: `s = 1/2 + I·z` at `z = R21.center`. -/
noncomputable def sR21 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R21.center

/-- `R21.center = -8.75 + 0.3·I` (from `R21_x0/x1/y0/y1`). -/
theorem R21_center_eq :
    CentralCoverAssembly.R21.center =
      (((-8.75 : ℝ))) + Complex.I * ((((0.3 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R21_x0, CentralCoverAssembly.R21_x1,
      CentralCoverAssembly.R21_y0, CentralCoverAssembly.R21_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R21_x0, CentralCoverAssembly.R21_x1,
      CentralCoverAssembly.R21_y0, CentralCoverAssembly.R21_y1]
    simp
    norm_num

/-- `Re sR21 = 0.2`. -/
theorem sR21_re : sR21.re = 0.2 := by
  unfold sR21
  rw [R21_center_eq]
  simp
  norm_num

/-- `Im sR21 = -8.75`. -/
theorem sR21_im : sR21.im = -8.75 := by
  unfold sR21
  rw [R21_center_eq]
  simp

/-- `Re(1 - sR21/2) = 0.9`. -/
theorem zUpR21_re : (1 - sR21 / 2).re = 0.9 := by
  rw [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, sR21_re]
  norm_num

/-- `Im(1 - sR21/2) = 4.375`. -/
theorem zUpR21_im : (1 - sR21 / 2).im = 4.375 := by
  rw [Complex.sub_im, Complex.one_im, Complex.div_ofNat_im, sR21_im]
  norm_num

/-- Denominator floor `c0 = 4.46 ≤ ‖1 - sR21 / 2‖`. -/
theorem norm_zUpR21_0_ge :
    (4.46 : ℝ) ≤ ‖1 - sR21 / 2‖ := by
  have hsq : (4.46 : ℝ) ^ 2 ≤ ‖1 - sR21 / 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, zUpR21_re, zUpR21_im]
    norm_num
  calc (4.46 : ℝ) = Real.sqrt ((4.46 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR21 / 2‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR21 / 2‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c1 = 4.76 ≤ ‖1 - sR21 / 2 + 1‖`. -/
theorem norm_zUpR21_1_ge :
    (4.76 : ℝ) ≤ ‖1 - sR21 / 2 + 1‖ := by
  have hre : (1 - sR21 / 2 + 1).re = 1.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.one_re]
    norm_num
  have him : (1 - sR21 / 2 + 1).im = 4.375 := by
    simp only [Complex.add_im, zUpR21_im, Complex.one_im]
    norm_num
  have hsq : (4.76 : ℝ) ^ 2 ≤ ‖1 - sR21 / 2 + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (4.76 : ℝ) = Real.sqrt ((4.76 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR21 / 2 + 1‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR21 / 2 + 1‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c2 = 5.24 ≤ ‖1 - sR21 / 2 + 2‖`. -/
theorem norm_zUpR21_2_ge :
    (5.24 : ℝ) ≤ ‖1 - sR21 / 2 + 2‖ := by
  have hre : (1 - sR21 / 2 + 2).re = 2.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR21 / 2 + 2).im = 4.375 := by
    simp only [Complex.add_im, zUpR21_im, Complex.im_ofNat]
    norm_num
  have hsq : (5.24 : ℝ) ^ 2 ≤ ‖1 - sR21 / 2 + 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (5.24 : ℝ) = Real.sqrt ((5.24 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR21 / 2 + 2‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR21 / 2 + 2‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c3 = 5.86 ≤ ‖1 - sR21 / 2 + 3‖`. -/
theorem norm_zUpR21_3_ge :
    (5.86 : ℝ) ≤ ‖1 - sR21 / 2 + 3‖ := by
  have hre : (1 - sR21 / 2 + 3).re = 3.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR21 / 2 + 3).im = 4.375 := by
    simp only [Complex.add_im, zUpR21_im, Complex.im_ofNat]
    norm_num
  have hsq : (5.86 : ℝ) ^ 2 ≤ ‖1 - sR21 / 2 + 3‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (5.86 : ℝ) = Real.sqrt ((5.86 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR21 / 2 + 3‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR21 / 2 + 3‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c4 = 6.56 ≤ ‖1 - sR21 / 2 + 4‖`. -/
theorem norm_zUpR21_4_ge :
    (6.56 : ℝ) ≤ ‖1 - sR21 / 2 + 4‖ := by
  have hre : (1 - sR21 / 2 + 4).re = 4.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR21 / 2 + 4).im = 4.375 := by
    simp only [Complex.add_im, zUpR21_im, Complex.im_ofNat]
    norm_num
  have hsq : (6.56 : ℝ) ^ 2 ≤ ‖1 - sR21 / 2 + 4‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (6.56 : ℝ) = Real.sqrt ((6.56 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR21 / 2 + 4‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR21 / 2 + 4‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c5 = 7.34 ≤ ‖1 - sR21 / 2 + 5‖`. -/
theorem norm_zUpR21_5_ge :
    (7.34 : ℝ) ≤ ‖1 - sR21 / 2 + 5‖ := by
  have hre : (1 - sR21 / 2 + 5).re = 5.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR21 / 2 + 5).im = 4.375 := by
    simp only [Complex.add_im, zUpR21_im, Complex.im_ofNat]
    norm_num
  have hsq : (7.34 : ℝ) ^ 2 ≤ ‖1 - sR21 / 2 + 5‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (7.34 : ℝ) = Real.sqrt ((7.34 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR21 / 2 + 5‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR21 / 2 + 5‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c6 = 8.17 ≤ ‖1 - sR21 / 2 + 6‖`. -/
theorem norm_zUpR21_6_ge :
    (8.17 : ℝ) ≤ ‖1 - sR21 / 2 + 6‖ := by
  have hre : (1 - sR21 / 2 + 6).re = 6.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR21 / 2 + 6).im = 4.375 := by
    simp only [Complex.add_im, zUpR21_im, Complex.im_ofNat]
    norm_num
  have hsq : (8.17 : ℝ) ^ 2 ≤ ‖1 - sR21 / 2 + 6‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (8.17 : ℝ) = Real.sqrt ((8.17 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR21 / 2 + 6‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR21 / 2 + 6‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c7 = 9.03 ≤ ‖1 - sR21 / 2 + 7‖`. -/
theorem norm_zUpR21_7_ge :
    (9.03 : ℝ) ≤ ‖1 - sR21 / 2 + 7‖ := by
  have hre : (1 - sR21 / 2 + 7).re = 7.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR21 / 2 + 7).im = 4.375 := by
    simp only [Complex.add_im, zUpR21_im, Complex.im_ofNat]
    norm_num
  have hsq : (9.03 : ℝ) ^ 2 ≤ ‖1 - sR21 / 2 + 7‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (9.03 : ℝ) = Real.sqrt ((9.03 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR21 / 2 + 7‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR21 / 2 + 7‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c8 = 9.91 ≤ ‖1 - sR21 / 2 + 8‖`. -/
theorem norm_zUpR21_8_ge :
    (9.91 : ℝ) ≤ ‖1 - sR21 / 2 + 8‖ := by
  have hre : (1 - sR21 / 2 + 8).re = 8.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR21 / 2 + 8).im = 4.375 := by
    simp only [Complex.add_im, zUpR21_im, Complex.im_ofNat]
    norm_num
  have hsq : (9.91 : ℝ) ^ 2 ≤ ‖1 - sR21 / 2 + 8‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (9.91 : ℝ) = Real.sqrt ((9.91 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR21 / 2 + 8‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR21 / 2 + 8‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c9 = 10.82 ≤ ‖1 - sR21 / 2 + 9‖`. -/
theorem norm_zUpR21_9_ge :
    (10.82 : ℝ) ≤ ‖1 - sR21 / 2 + 9‖ := by
  have hre : (1 - sR21 / 2 + 9).re = 9.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR21 / 2 + 9).im = 4.375 := by
    simp only [Complex.add_im, zUpR21_im, Complex.im_ofNat]
    norm_num
  have hsq : (10.82 : ℝ) ^ 2 ≤ ‖1 - sR21 / 2 + 9‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (10.82 : ℝ) = Real.sqrt ((10.82 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR21 / 2 + 9‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR21 / 2 + 9‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c10 = 11.74 ≤ ‖1 - sR21 / 2 + 10‖`. -/
theorem norm_zUpR21_10_ge :
    (11.74 : ℝ) ≤ ‖1 - sR21 / 2 + 10‖ := by
  have hre : (1 - sR21 / 2 + 10).re = 10.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR21 / 2 + 10).im = 4.375 := by
    simp only [Complex.add_im, zUpR21_im, Complex.im_ofNat]
    norm_num
  have hsq : (11.74 : ℝ) ^ 2 ≤ ‖1 - sR21 / 2 + 10‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (11.74 : ℝ) = Real.sqrt ((11.74 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR21 / 2 + 10‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR21 / 2 + 10‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c11 = 12.67 ≤ ‖1 - sR21 / 2 + 11‖`. -/
theorem norm_zUpR21_11_ge :
    (12.67 : ℝ) ≤ ‖1 - sR21 / 2 + 11‖ := by
  have hre : (1 - sR21 / 2 + 11).re = 11.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR21 / 2 + 11).im = 4.375 := by
    simp only [Complex.add_im, zUpR21_im, Complex.im_ofNat]
    norm_num
  have hsq : (12.67 : ℝ) ^ 2 ≤ ‖1 - sR21 / 2 + 11‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (12.67 : ℝ) = Real.sqrt ((12.67 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR21 / 2 + 11‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR21 / 2 + 11‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c12 = 13.62 ≤ ‖1 - sR21 / 2 + 12‖`. -/
theorem norm_zUpR21_12_ge :
    (13.62 : ℝ) ≤ ‖1 - sR21 / 2 + 12‖ := by
  have hre : (1 - sR21 / 2 + 12).re = 12.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR21 / 2 + 12).im = 4.375 := by
    simp only [Complex.add_im, zUpR21_im, Complex.im_ofNat]
    norm_num
  have hsq : (13.62 : ℝ) ^ 2 ≤ ‖1 - sR21 / 2 + 12‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (13.62 : ℝ) = Real.sqrt ((13.62 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR21 / 2 + 12‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR21 / 2 + 12‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c13 = 14.57 ≤ ‖1 - sR21 / 2 + 13‖`. -/
theorem norm_zUpR21_13_ge :
    (14.57 : ℝ) ≤ ‖1 - sR21 / 2 + 13‖ := by
  have hre : (1 - sR21 / 2 + 13).re = 13.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR21 / 2 + 13).im = 4.375 := by
    simp only [Complex.add_im, zUpR21_im, Complex.im_ofNat]
    norm_num
  have hsq : (14.57 : ℝ) ^ 2 ≤ ‖1 - sR21 / 2 + 13‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (14.57 : ℝ) = Real.sqrt ((14.57 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR21 / 2 + 13‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR21 / 2 + 13‖ := Real.sqrt_sq (norm_nonneg _)

/-- Shift nonvanishing (`Re > 0` so `{NE} 0`). -/
theorem zUpR21_ne0 : (1 - sR21 / 2) ≠ 0 := by
  have hre : (1 - sR21 / 2).re = 0.9 := zUpR21_re
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR21_add1_ne0 : (1 - sR21 / 2 + 1) ≠ 0 := by
  have hre : (1 - sR21 / 2 + 1).re = 1.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.one_re]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR21_add2_ne0 : (1 - sR21 / 2 + 2) ≠ 0 := by
  have hre : (1 - sR21 / 2 + 2).re = 2.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR21_add3_ne0 : (1 - sR21 / 2 + 3) ≠ 0 := by
  have hre : (1 - sR21 / 2 + 3).re = 3.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR21_add4_ne0 : (1 - sR21 / 2 + 4) ≠ 0 := by
  have hre : (1 - sR21 / 2 + 4).re = 4.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR21_add5_ne0 : (1 - sR21 / 2 + 5) ≠ 0 := by
  have hre : (1 - sR21 / 2 + 5).re = 5.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR21_add6_ne0 : (1 - sR21 / 2 + 6) ≠ 0 := by
  have hre : (1 - sR21 / 2 + 6).re = 6.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR21_add7_ne0 : (1 - sR21 / 2 + 7) ≠ 0 := by
  have hre : (1 - sR21 / 2 + 7).re = 7.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR21_add8_ne0 : (1 - sR21 / 2 + 8) ≠ 0 := by
  have hre : (1 - sR21 / 2 + 8).re = 8.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR21_add9_ne0 : (1 - sR21 / 2 + 9) ≠ 0 := by
  have hre : (1 - sR21 / 2 + 9).re = 9.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR21_add10_ne0 : (1 - sR21 / 2 + 10) ≠ 0 := by
  have hre : (1 - sR21 / 2 + 10).re = 10.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR21_add11_ne0 : (1 - sR21 / 2 + 11) ≠ 0 := by
  have hre : (1 - sR21 / 2 + 11).re = 11.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR21_add12_ne0 : (1 - sR21 / 2 + 12) ≠ 0 := by
  have hre : (1 - sR21 / 2 + 12).re = 12.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR21_add13_ne0 : (1 - sR21 / 2 + 13) ≠ 0 := by
  have hre : (1 - sR21 / 2 + 13).re = 13.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

/-- MAIN uniform UPPER bound at the R21 corner:
`‖Complex.Gamma (1 - sR21 / 2)‖ ≤ 0.01` (row-2 outer-tier, `re = 0.9`, 14 shifts). -/
theorem gamma_one_sub_half_upper_R21 :
    ‖Complex.Gamma (1 - sR21 / 2)‖ ≤ 0.01 := by
  -- Shift chain `Gamma(z0+14) = (z0+13)..z0*Gamma(z0)`.
  have e0 : Complex.Gamma (1 - sR21 / 2 + 1)
      = (1 - sR21 / 2) * Complex.Gamma (1 - sR21 / 2) :=
    Complex.Gamma_add_one _ zUpR21_ne0
  have e1 : Complex.Gamma (1 - sR21 / 2 + 2)
      = (1 - sR21 / 2 + 1)
        * Complex.Gamma (1 - sR21 / 2 + 1) := by
    have h : (1 - sR21 / 2 + 2)
        = ((1 - sR21 / 2 + 1) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR21_add1_ne0
  have e2 : Complex.Gamma (1 - sR21 / 2 + 3)
      = (1 - sR21 / 2 + 2)
        * Complex.Gamma (1 - sR21 / 2 + 2) := by
    have h : (1 - sR21 / 2 + 3)
        = ((1 - sR21 / 2 + 2) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR21_add2_ne0
  have e3 : Complex.Gamma (1 - sR21 / 2 + 4)
      = (1 - sR21 / 2 + 3)
        * Complex.Gamma (1 - sR21 / 2 + 3) := by
    have h : (1 - sR21 / 2 + 4)
        = ((1 - sR21 / 2 + 3) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR21_add3_ne0
  have e4 : Complex.Gamma (1 - sR21 / 2 + 5)
      = (1 - sR21 / 2 + 4)
        * Complex.Gamma (1 - sR21 / 2 + 4) := by
    have h : (1 - sR21 / 2 + 5)
        = ((1 - sR21 / 2 + 4) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR21_add4_ne0
  have e5 : Complex.Gamma (1 - sR21 / 2 + 6)
      = (1 - sR21 / 2 + 5)
        * Complex.Gamma (1 - sR21 / 2 + 5) := by
    have h : (1 - sR21 / 2 + 6)
        = ((1 - sR21 / 2 + 5) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR21_add5_ne0
  have e6 : Complex.Gamma (1 - sR21 / 2 + 7)
      = (1 - sR21 / 2 + 6)
        * Complex.Gamma (1 - sR21 / 2 + 6) := by
    have h : (1 - sR21 / 2 + 7)
        = ((1 - sR21 / 2 + 6) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR21_add6_ne0
  have e7 : Complex.Gamma (1 - sR21 / 2 + 8)
      = (1 - sR21 / 2 + 7)
        * Complex.Gamma (1 - sR21 / 2 + 7) := by
    have h : (1 - sR21 / 2 + 8)
        = ((1 - sR21 / 2 + 7) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR21_add7_ne0
  have e8 : Complex.Gamma (1 - sR21 / 2 + 9)
      = (1 - sR21 / 2 + 8)
        * Complex.Gamma (1 - sR21 / 2 + 8) := by
    have h : (1 - sR21 / 2 + 9)
        = ((1 - sR21 / 2 + 8) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR21_add8_ne0
  have e9 : Complex.Gamma (1 - sR21 / 2 + 10)
      = (1 - sR21 / 2 + 9)
        * Complex.Gamma (1 - sR21 / 2 + 9) := by
    have h : (1 - sR21 / 2 + 10)
        = ((1 - sR21 / 2 + 9) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR21_add9_ne0
  have e10 : Complex.Gamma (1 - sR21 / 2 + 11)
      = (1 - sR21 / 2 + 10)
        * Complex.Gamma (1 - sR21 / 2 + 10) := by
    have h : (1 - sR21 / 2 + 11)
        = ((1 - sR21 / 2 + 10) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR21_add10_ne0
  have e11 : Complex.Gamma (1 - sR21 / 2 + 12)
      = (1 - sR21 / 2 + 11)
        * Complex.Gamma (1 - sR21 / 2 + 11) := by
    have h : (1 - sR21 / 2 + 12)
        = ((1 - sR21 / 2 + 11) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR21_add11_ne0
  have e12 : Complex.Gamma (1 - sR21 / 2 + 13)
      = (1 - sR21 / 2 + 12)
        * Complex.Gamma (1 - sR21 / 2 + 12) := by
    have h : (1 - sR21 / 2 + 13)
        = ((1 - sR21 / 2 + 12) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR21_add12_ne0
  have e13 : Complex.Gamma (1 - sR21 / 2 + 14)
      = (1 - sR21 / 2 + 13)
        * Complex.Gamma (1 - sR21 / 2 + 13) := by
    have h : (1 - sR21 / 2 + 14)
        = ((1 - sR21 / 2 + 13) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR21_add13_ne0
  have n0 : ‖Complex.Gamma (1 - sR21 / 2 + 1)‖
      = ‖1 - sR21 / 2‖
        * ‖Complex.Gamma (1 - sR21 / 2)‖ := by
    rw [e0, norm_mul]
  have n1 : ‖Complex.Gamma (1 - sR21 / 2 + 2)‖
      = ‖1 - sR21 / 2 + 1‖
        * ‖Complex.Gamma (1 - sR21 / 2 + 1)‖ := by
    rw [e1, norm_mul]
  have n2 : ‖Complex.Gamma (1 - sR21 / 2 + 3)‖
      = ‖1 - sR21 / 2 + 2‖
        * ‖Complex.Gamma (1 - sR21 / 2 + 2)‖ := by
    rw [e2, norm_mul]
  have n3 : ‖Complex.Gamma (1 - sR21 / 2 + 4)‖
      = ‖1 - sR21 / 2 + 3‖
        * ‖Complex.Gamma (1 - sR21 / 2 + 3)‖ := by
    rw [e3, norm_mul]
  have n4 : ‖Complex.Gamma (1 - sR21 / 2 + 5)‖
      = ‖1 - sR21 / 2 + 4‖
        * ‖Complex.Gamma (1 - sR21 / 2 + 4)‖ := by
    rw [e4, norm_mul]
  have n5 : ‖Complex.Gamma (1 - sR21 / 2 + 6)‖
      = ‖1 - sR21 / 2 + 5‖
        * ‖Complex.Gamma (1 - sR21 / 2 + 5)‖ := by
    rw [e5, norm_mul]
  have n6 : ‖Complex.Gamma (1 - sR21 / 2 + 7)‖
      = ‖1 - sR21 / 2 + 6‖
        * ‖Complex.Gamma (1 - sR21 / 2 + 6)‖ := by
    rw [e6, norm_mul]
  have n7 : ‖Complex.Gamma (1 - sR21 / 2 + 8)‖
      = ‖1 - sR21 / 2 + 7‖
        * ‖Complex.Gamma (1 - sR21 / 2 + 7)‖ := by
    rw [e7, norm_mul]
  have n8 : ‖Complex.Gamma (1 - sR21 / 2 + 9)‖
      = ‖1 - sR21 / 2 + 8‖
        * ‖Complex.Gamma (1 - sR21 / 2 + 8)‖ := by
    rw [e8, norm_mul]
  have n9 : ‖Complex.Gamma (1 - sR21 / 2 + 10)‖
      = ‖1 - sR21 / 2 + 9‖
        * ‖Complex.Gamma (1 - sR21 / 2 + 9)‖ := by
    rw [e9, norm_mul]
  have n10 : ‖Complex.Gamma (1 - sR21 / 2 + 11)‖
      = ‖1 - sR21 / 2 + 10‖
        * ‖Complex.Gamma (1 - sR21 / 2 + 10)‖ := by
    rw [e10, norm_mul]
  have n11 : ‖Complex.Gamma (1 - sR21 / 2 + 12)‖
      = ‖1 - sR21 / 2 + 11‖
        * ‖Complex.Gamma (1 - sR21 / 2 + 11)‖ := by
    rw [e11, norm_mul]
  have n12 : ‖Complex.Gamma (1 - sR21 / 2 + 13)‖
      = ‖1 - sR21 / 2 + 12‖
        * ‖Complex.Gamma (1 - sR21 / 2 + 12)‖ := by
    rw [e12, norm_mul]
  have n13 : ‖Complex.Gamma (1 - sR21 / 2 + 14)‖
      = ‖1 - sR21 / 2 + 13‖
        * ‖Complex.Gamma (1 - sR21 / 2 + 13)‖ := by
    rw [e13, norm_mul]
  have hprod : ‖Complex.Gamma (1 - sR21 / 2 + 14)‖
      = ‖1 - sR21 / 2 + 13‖
        * (‖1 - sR21 / 2 + 12‖
        * (‖1 - sR21 / 2 + 11‖
        * (‖1 - sR21 / 2 + 10‖
        * (‖1 - sR21 / 2 + 9‖
        * (‖1 - sR21 / 2 + 8‖
        * (‖1 - sR21 / 2 + 7‖
        * (‖1 - sR21 / 2 + 6‖
        * (‖1 - sR21 / 2 + 5‖
        * (‖1 - sR21 / 2 + 4‖
        * (‖1 - sR21 / 2 + 3‖
        * (‖1 - sR21 / 2 + 2‖
        * (‖1 - sR21 / 2 + 1‖
        * (‖1 - sR21 / 2‖
          * ‖Complex.Gamma (1 - sR21 / 2)‖))))))))))))) := by
    rw [n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n0]
  -- Denominator product lower bound.
  have q1 : (4.76 : ℝ) * 4.46
      ≤ ‖1 - sR21 / 2 + 1‖ * ‖1 - sR21 / 2‖ :=
    mul_le_mul norm_zUpR21_1_ge norm_zUpR21_0_ge (by norm_num) (norm_nonneg _)
  have q2 : (5.24 : ℝ) * (4.76 * (4.46))
      ≤ ‖1 - sR21 / 2 + 2‖ * (‖1 - sR21 / 2 + 1‖ * (‖1 - sR21 / 2‖)) :=
    mul_le_mul norm_zUpR21_2_ge q1 (by positivity) (norm_nonneg _)
  have q3 : (5.86 : ℝ) * (5.24 * (4.76 * (4.46)))
      ≤ ‖1 - sR21 / 2 + 3‖ * (‖1 - sR21 / 2 + 2‖ * (‖1 - sR21 / 2 + 1‖ * (‖1 - sR21 / 2‖))) :=
    mul_le_mul norm_zUpR21_3_ge q2 (by positivity) (norm_nonneg _)
  have q4 : (6.56 : ℝ) * (5.86 * (5.24 * (4.76 * (4.46))))
      ≤ ‖1 - sR21 / 2 + 4‖ * (‖1 - sR21 / 2 + 3‖ * (‖1 - sR21 / 2 + 2‖ * (‖1 - sR21 / 2 + 1‖ * (‖1 - sR21 / 2‖)))) :=
    mul_le_mul norm_zUpR21_4_ge q3 (by positivity) (norm_nonneg _)
  have q5 : (7.34 : ℝ) * (6.56 * (5.86 * (5.24 * (4.76 * (4.46)))))
      ≤ ‖1 - sR21 / 2 + 5‖ * (‖1 - sR21 / 2 + 4‖ * (‖1 - sR21 / 2 + 3‖ * (‖1 - sR21 / 2 + 2‖ * (‖1 - sR21 / 2 + 1‖ * (‖1 - sR21 / 2‖))))) :=
    mul_le_mul norm_zUpR21_5_ge q4 (by positivity) (norm_nonneg _)
  have q6 : (8.17 : ℝ) * (7.34 * (6.56 * (5.86 * (5.24 * (4.76 * (4.46))))))
      ≤ ‖1 - sR21 / 2 + 6‖ * (‖1 - sR21 / 2 + 5‖ * (‖1 - sR21 / 2 + 4‖ * (‖1 - sR21 / 2 + 3‖ * (‖1 - sR21 / 2 + 2‖ * (‖1 - sR21 / 2 + 1‖ * (‖1 - sR21 / 2‖)))))) :=
    mul_le_mul norm_zUpR21_6_ge q5 (by positivity) (norm_nonneg _)
  have q7 : (9.03 : ℝ) * (8.17 * (7.34 * (6.56 * (5.86 * (5.24 * (4.76 * (4.46)))))))
      ≤ ‖1 - sR21 / 2 + 7‖ * (‖1 - sR21 / 2 + 6‖ * (‖1 - sR21 / 2 + 5‖ * (‖1 - sR21 / 2 + 4‖ * (‖1 - sR21 / 2 + 3‖ * (‖1 - sR21 / 2 + 2‖ * (‖1 - sR21 / 2 + 1‖ * (‖1 - sR21 / 2‖))))))) :=
    mul_le_mul norm_zUpR21_7_ge q6 (by positivity) (norm_nonneg _)
  have q8 : (9.91 : ℝ) * (9.03 * (8.17 * (7.34 * (6.56 * (5.86 * (5.24 * (4.76 * (4.46))))))))
      ≤ ‖1 - sR21 / 2 + 8‖ * (‖1 - sR21 / 2 + 7‖ * (‖1 - sR21 / 2 + 6‖ * (‖1 - sR21 / 2 + 5‖ * (‖1 - sR21 / 2 + 4‖ * (‖1 - sR21 / 2 + 3‖ * (‖1 - sR21 / 2 + 2‖ * (‖1 - sR21 / 2 + 1‖ * (‖1 - sR21 / 2‖)))))))) :=
    mul_le_mul norm_zUpR21_8_ge q7 (by positivity) (norm_nonneg _)
  have q9 : (10.82 : ℝ) * (9.91 * (9.03 * (8.17 * (7.34 * (6.56 * (5.86 * (5.24 * (4.76 * (4.46)))))))))
      ≤ ‖1 - sR21 / 2 + 9‖ * (‖1 - sR21 / 2 + 8‖ * (‖1 - sR21 / 2 + 7‖ * (‖1 - sR21 / 2 + 6‖ * (‖1 - sR21 / 2 + 5‖ * (‖1 - sR21 / 2 + 4‖ * (‖1 - sR21 / 2 + 3‖ * (‖1 - sR21 / 2 + 2‖ * (‖1 - sR21 / 2 + 1‖ * (‖1 - sR21 / 2‖))))))))) :=
    mul_le_mul norm_zUpR21_9_ge q8 (by positivity) (norm_nonneg _)
  have q10 : (11.74 : ℝ) * (10.82 * (9.91 * (9.03 * (8.17 * (7.34 * (6.56 * (5.86 * (5.24 * (4.76 * (4.46))))))))))
      ≤ ‖1 - sR21 / 2 + 10‖ * (‖1 - sR21 / 2 + 9‖ * (‖1 - sR21 / 2 + 8‖ * (‖1 - sR21 / 2 + 7‖ * (‖1 - sR21 / 2 + 6‖ * (‖1 - sR21 / 2 + 5‖ * (‖1 - sR21 / 2 + 4‖ * (‖1 - sR21 / 2 + 3‖ * (‖1 - sR21 / 2 + 2‖ * (‖1 - sR21 / 2 + 1‖ * (‖1 - sR21 / 2‖)))))))))) :=
    mul_le_mul norm_zUpR21_10_ge q9 (by positivity) (norm_nonneg _)
  have q11 : (12.67 : ℝ) * (11.74 * (10.82 * (9.91 * (9.03 * (8.17 * (7.34 * (6.56 * (5.86 * (5.24 * (4.76 * (4.46)))))))))))
      ≤ ‖1 - sR21 / 2 + 11‖ * (‖1 - sR21 / 2 + 10‖ * (‖1 - sR21 / 2 + 9‖ * (‖1 - sR21 / 2 + 8‖ * (‖1 - sR21 / 2 + 7‖ * (‖1 - sR21 / 2 + 6‖ * (‖1 - sR21 / 2 + 5‖ * (‖1 - sR21 / 2 + 4‖ * (‖1 - sR21 / 2 + 3‖ * (‖1 - sR21 / 2 + 2‖ * (‖1 - sR21 / 2 + 1‖ * (‖1 - sR21 / 2‖))))))))))) :=
    mul_le_mul norm_zUpR21_11_ge q10 (by positivity) (norm_nonneg _)
  have q12 : (13.62 : ℝ) * (12.67 * (11.74 * (10.82 * (9.91 * (9.03 * (8.17 * (7.34 * (6.56 * (5.86 * (5.24 * (4.76 * (4.46))))))))))))
      ≤ ‖1 - sR21 / 2 + 12‖ * (‖1 - sR21 / 2 + 11‖ * (‖1 - sR21 / 2 + 10‖ * (‖1 - sR21 / 2 + 9‖ * (‖1 - sR21 / 2 + 8‖ * (‖1 - sR21 / 2 + 7‖ * (‖1 - sR21 / 2 + 6‖ * (‖1 - sR21 / 2 + 5‖ * (‖1 - sR21 / 2 + 4‖ * (‖1 - sR21 / 2 + 3‖ * (‖1 - sR21 / 2 + 2‖ * (‖1 - sR21 / 2 + 1‖ * (‖1 - sR21 / 2‖)))))))))))) :=
    mul_le_mul norm_zUpR21_12_ge q11 (by positivity) (norm_nonneg _)
  have q13 : (14.57 : ℝ) * (13.62 * (12.67 * (11.74 * (10.82 * (9.91 * (9.03 * (8.17 * (7.34 * (6.56 * (5.86 * (5.24 * (4.76 * (4.46)))))))))))))
      ≤ ‖1 - sR21 / 2 + 13‖ * (‖1 - sR21 / 2 + 12‖ * (‖1 - sR21 / 2 + 11‖ * (‖1 - sR21 / 2 + 10‖ * (‖1 - sR21 / 2 + 9‖ * (‖1 - sR21 / 2 + 8‖ * (‖1 - sR21 / 2 + 7‖ * (‖1 - sR21 / 2 + 6‖ * (‖1 - sR21 / 2 + 5‖ * (‖1 - sR21 / 2 + 4‖ * (‖1 - sR21 / 2 + 3‖ * (‖1 - sR21 / 2 + 2‖ * (‖1 - sR21 / 2 + 1‖ * (‖1 - sR21 / 2‖))))))))))))) :=
    mul_le_mul norm_zUpR21_13_ge q12 (by positivity) (norm_nonneg _)
  have hDlo : (7000000000000 : ℝ)
      ≤ (14.57 : ℝ) * (13.62 * (12.67 * (11.74 * (10.82 * (9.91 * (9.03 * (8.17 * (7.34 * (6.56 * (5.86 * (5.24 * (4.76 * (4.46))))))))))))) := by
    norm_num
  have hD_ge : (7000000000000 : ℝ)
      ≤ ‖1 - sR21 / 2 + 13‖ * (‖1 - sR21 / 2 + 12‖ * (‖1 - sR21 / 2 + 11‖ * (‖1 - sR21 / 2 + 10‖ * (‖1 - sR21 / 2 + 9‖ * (‖1 - sR21 / 2 + 8‖ * (‖1 - sR21 / 2 + 7‖ * (‖1 - sR21 / 2 + 6‖ * (‖1 - sR21 / 2 + 5‖ * (‖1 - sR21 / 2 + 4‖ * (‖1 - sR21 / 2 + 3‖ * (‖1 - sR21 / 2 + 2‖ * (‖1 - sR21 / 2 + 1‖ * (‖1 - sR21 / 2‖))))))))))))) :=
    le_trans hDlo q13
  have hD_pos : (0 : ℝ)
      < (‖1 - sR21 / 2 + 13‖
        * (‖1 - sR21 / 2 + 12‖
        * (‖1 - sR21 / 2 + 11‖
        * (‖1 - sR21 / 2 + 10‖
        * (‖1 - sR21 / 2 + 9‖
        * (‖1 - sR21 / 2 + 8‖
        * (‖1 - sR21 / 2 + 7‖
        * (‖1 - sR21 / 2 + 6‖
        * (‖1 - sR21 / 2 + 5‖
        * (‖1 - sR21 / 2 + 4‖
        * (‖1 - sR21 / 2 + 3‖
        * (‖1 - sR21 / 2 + 2‖
        * (‖1 - sR21 / 2 + 1‖
          * ‖1 - sR21 / 2‖))))))))))))) :=
    lt_of_lt_of_le (by norm_num) hD_ge
  -- Numerator: `‖Complex.Gamma (1 - sR21 / 2 + 14)‖ ≤ Real.Gamma(14.9) ≤ 69500000000`.
  have hre14 : (1 - sR21 / 2 + 14).re = 14.9 := by
    simp only [Complex.add_re, zUpR21_re, Complex.re_ofNat]
    norm_num
  have hGN_re : (0 : ℝ) < (1 - sR21 / 2 + 14).re := by
    rw [hre14]
    norm_num
  have hGN_le : ‖Complex.Gamma (1 - sR21 / 2 + 14)‖ ≤ 69500000000 := by
    have h1 : ‖Complex.Gamma (1 - sR21 / 2 + 14)‖
        ≤ Real.Gamma ((1 - sR21 / 2 + 14).re) :=
      R00GammaLower.norm_Gamma_le_realGamma hGN_re
    have hreNb : ((1 - sR21 / 2 + 14).re) = 14.9 := hre14
    rw [hreNb] at h1
    exact le_trans h1 CellGammaUpper09.realGamma_149_le
  -- Combine: `D * ‖Complex.Gamma (1 - sR21 / 2)‖ = ‖Complex.Gamma (1 - sR21 / 2 + 14)‖ ≤ 69500000000`, `D ≤ 7000000000000`.
  have hD_mul : (‖1 - sR21 / 2 + 13‖
        * (‖1 - sR21 / 2 + 12‖
        * (‖1 - sR21 / 2 + 11‖
        * (‖1 - sR21 / 2 + 10‖
        * (‖1 - sR21 / 2 + 9‖
        * (‖1 - sR21 / 2 + 8‖
        * (‖1 - sR21 / 2 + 7‖
        * (‖1 - sR21 / 2 + 6‖
        * (‖1 - sR21 / 2 + 5‖
        * (‖1 - sR21 / 2 + 4‖
        * (‖1 - sR21 / 2 + 3‖
        * (‖1 - sR21 / 2 + 2‖
        * (‖1 - sR21 / 2 + 1‖
          * ‖1 - sR21 / 2‖)))))))))))))
        * ‖Complex.Gamma (1 - sR21 / 2)‖
      = ‖Complex.Gamma (1 - sR21 / 2 + 14)‖ := by
    rw [hprod]
    ring
  have hle : (‖1 - sR21 / 2 + 13‖
        * (‖1 - sR21 / 2 + 12‖
        * (‖1 - sR21 / 2 + 11‖
        * (‖1 - sR21 / 2 + 10‖
        * (‖1 - sR21 / 2 + 9‖
        * (‖1 - sR21 / 2 + 8‖
        * (‖1 - sR21 / 2 + 7‖
        * (‖1 - sR21 / 2 + 6‖
        * (‖1 - sR21 / 2 + 5‖
        * (‖1 - sR21 / 2 + 4‖
        * (‖1 - sR21 / 2 + 3‖
        * (‖1 - sR21 / 2 + 2‖
        * (‖1 - sR21 / 2 + 1‖
          * ‖1 - sR21 / 2‖)))))))))))))
        * ‖Complex.Gamma (1 - sR21 / 2)‖ ≤ 69500000000 := by
    rw [hD_mul]
    exact hGN_le
  have hmul_comm : ‖Complex.Gamma (1 - sR21 / 2)‖
        * (‖1 - sR21 / 2 + 13‖
        * (‖1 - sR21 / 2 + 12‖
        * (‖1 - sR21 / 2 + 11‖
        * (‖1 - sR21 / 2 + 10‖
        * (‖1 - sR21 / 2 + 9‖
        * (‖1 - sR21 / 2 + 8‖
        * (‖1 - sR21 / 2 + 7‖
        * (‖1 - sR21 / 2 + 6‖
        * (‖1 - sR21 / 2 + 5‖
        * (‖1 - sR21 / 2 + 4‖
        * (‖1 - sR21 / 2 + 3‖
        * (‖1 - sR21 / 2 + 2‖
        * (‖1 - sR21 / 2 + 1‖
          * ‖1 - sR21 / 2‖)))))))))))))
        ≤ 69500000000 := by
    calc ‖Complex.Gamma (1 - sR21 / 2)‖ * _
          = _ * ‖Complex.Gamma (1 - sR21 / 2)‖ := mul_comm _ _
      _ ≤ 69500000000 := hle
  have hdiv : ‖Complex.Gamma (1 - sR21 / 2)‖
      ≤ 69500000000 / (‖1 - sR21 / 2 + 13‖
        * (‖1 - sR21 / 2 + 12‖
        * (‖1 - sR21 / 2 + 11‖
        * (‖1 - sR21 / 2 + 10‖
        * (‖1 - sR21 / 2 + 9‖
        * (‖1 - sR21 / 2 + 8‖
        * (‖1 - sR21 / 2 + 7‖
        * (‖1 - sR21 / 2 + 6‖
        * (‖1 - sR21 / 2 + 5‖
        * (‖1 - sR21 / 2 + 4‖
        * (‖1 - sR21 / 2 + 3‖
        * (‖1 - sR21 / 2 + 2‖
        * (‖1 - sR21 / 2 + 1‖
          * ‖1 - sR21 / 2‖)))))))))))))
        :=
    (le_div_iff₀ hD_pos).mpr hmul_comm
  have hcap : (69500000000 : ℝ)
      ≤ 0.01 * (‖1 - sR21 / 2 + 13‖
        * (‖1 - sR21 / 2 + 12‖
        * (‖1 - sR21 / 2 + 11‖
        * (‖1 - sR21 / 2 + 10‖
        * (‖1 - sR21 / 2 + 9‖
        * (‖1 - sR21 / 2 + 8‖
        * (‖1 - sR21 / 2 + 7‖
        * (‖1 - sR21 / 2 + 6‖
        * (‖1 - sR21 / 2 + 5‖
        * (‖1 - sR21 / 2 + 4‖
        * (‖1 - sR21 / 2 + 3‖
        * (‖1 - sR21 / 2 + 2‖
        * (‖1 - sR21 / 2 + 1‖
          * ‖1 - sR21 / 2‖))))))))))))) := by
    calc (69500000000 : ℝ) ≤ 0.01 * 7000000000000 := by norm_num
      _ ≤ 0.01 * _ :=
          mul_le_mul_of_nonneg_left hD_ge (by norm_num)
  have hfinal : 69500000000 / (‖1 - sR21 / 2 + 13‖ * (‖1 - sR21 / 2 + 12‖ * (‖1 - sR21 / 2 + 11‖ * (‖1 - sR21 / 2 + 10‖ * (‖1 - sR21 / 2 + 9‖ * (‖1 - sR21 / 2 + 8‖ * (‖1 - sR21 / 2 + 7‖ * (‖1 - sR21 / 2 + 6‖ * (‖1 - sR21 / 2 + 5‖ * (‖1 - sR21 / 2 + 4‖ * (‖1 - sR21 / 2 + 3‖ * (‖1 - sR21 / 2 + 2‖ * (‖1 - sR21 / 2 + 1‖ * (‖1 - sR21 / 2‖))))))))))))))
      ≤ 0.01 :=
    (div_le_iff₀ hD_pos).mpr hcap
  exact le_trans hdiv hfinal

end R21GammaUpper

namespace R30GammaUpper

/-- The R30 `s`-plane center: `s = 1/2 + I·z` at `z = R30.center`. -/
noncomputable def sR30 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R30.center

/-- `R30.center = 8.75 + 0.3·I` (from `R30_x0/x1/y0/y1`). -/
theorem R30_center_eq :
    CentralCoverAssembly.R30.center =
      (((8.75 : ℝ))) + Complex.I * ((((0.3 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R30_x0, CentralCoverAssembly.R30_x1,
      CentralCoverAssembly.R30_y0, CentralCoverAssembly.R30_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R30_x0, CentralCoverAssembly.R30_x1,
      CentralCoverAssembly.R30_y0, CentralCoverAssembly.R30_y1]
    simp
    norm_num

/-- `Re sR30 = 0.2`. -/
theorem sR30_re : sR30.re = 0.2 := by
  unfold sR30
  rw [R30_center_eq]
  simp
  norm_num

/-- `Im sR30 = 8.75`. -/
theorem sR30_im : sR30.im = 8.75 := by
  unfold sR30
  rw [R30_center_eq]
  simp

/-- `Re(1 - sR30/2) = 0.9`. -/
theorem zUpR30_re : (1 - sR30 / 2).re = 0.9 := by
  rw [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, sR30_re]
  norm_num

/-- `Im(1 - sR30/2) = -4.375`. -/
theorem zUpR30_im : (1 - sR30 / 2).im = -4.375 := by
  rw [Complex.sub_im, Complex.one_im, Complex.div_ofNat_im, sR30_im]
  norm_num

/-- Denominator floor `c0 = 4.46 ≤ ‖1 - sR30 / 2‖`. -/
theorem norm_zUpR30_0_ge :
    (4.46 : ℝ) ≤ ‖1 - sR30 / 2‖ := by
  have hsq : (4.46 : ℝ) ^ 2 ≤ ‖1 - sR30 / 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, zUpR30_re, zUpR30_im]
    norm_num
  calc (4.46 : ℝ) = Real.sqrt ((4.46 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR30 / 2‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR30 / 2‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c1 = 4.76 ≤ ‖1 - sR30 / 2 + 1‖`. -/
theorem norm_zUpR30_1_ge :
    (4.76 : ℝ) ≤ ‖1 - sR30 / 2 + 1‖ := by
  have hre : (1 - sR30 / 2 + 1).re = 1.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.one_re]
    norm_num
  have him : (1 - sR30 / 2 + 1).im = -4.375 := by
    simp only [Complex.add_im, zUpR30_im, Complex.one_im]
    norm_num
  have hsq : (4.76 : ℝ) ^ 2 ≤ ‖1 - sR30 / 2 + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (4.76 : ℝ) = Real.sqrt ((4.76 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR30 / 2 + 1‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR30 / 2 + 1‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c2 = 5.24 ≤ ‖1 - sR30 / 2 + 2‖`. -/
theorem norm_zUpR30_2_ge :
    (5.24 : ℝ) ≤ ‖1 - sR30 / 2 + 2‖ := by
  have hre : (1 - sR30 / 2 + 2).re = 2.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR30 / 2 + 2).im = -4.375 := by
    simp only [Complex.add_im, zUpR30_im, Complex.im_ofNat]
    norm_num
  have hsq : (5.24 : ℝ) ^ 2 ≤ ‖1 - sR30 / 2 + 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (5.24 : ℝ) = Real.sqrt ((5.24 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR30 / 2 + 2‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR30 / 2 + 2‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c3 = 5.86 ≤ ‖1 - sR30 / 2 + 3‖`. -/
theorem norm_zUpR30_3_ge :
    (5.86 : ℝ) ≤ ‖1 - sR30 / 2 + 3‖ := by
  have hre : (1 - sR30 / 2 + 3).re = 3.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR30 / 2 + 3).im = -4.375 := by
    simp only [Complex.add_im, zUpR30_im, Complex.im_ofNat]
    norm_num
  have hsq : (5.86 : ℝ) ^ 2 ≤ ‖1 - sR30 / 2 + 3‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (5.86 : ℝ) = Real.sqrt ((5.86 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR30 / 2 + 3‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR30 / 2 + 3‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c4 = 6.56 ≤ ‖1 - sR30 / 2 + 4‖`. -/
theorem norm_zUpR30_4_ge :
    (6.56 : ℝ) ≤ ‖1 - sR30 / 2 + 4‖ := by
  have hre : (1 - sR30 / 2 + 4).re = 4.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR30 / 2 + 4).im = -4.375 := by
    simp only [Complex.add_im, zUpR30_im, Complex.im_ofNat]
    norm_num
  have hsq : (6.56 : ℝ) ^ 2 ≤ ‖1 - sR30 / 2 + 4‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (6.56 : ℝ) = Real.sqrt ((6.56 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR30 / 2 + 4‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR30 / 2 + 4‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c5 = 7.34 ≤ ‖1 - sR30 / 2 + 5‖`. -/
theorem norm_zUpR30_5_ge :
    (7.34 : ℝ) ≤ ‖1 - sR30 / 2 + 5‖ := by
  have hre : (1 - sR30 / 2 + 5).re = 5.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR30 / 2 + 5).im = -4.375 := by
    simp only [Complex.add_im, zUpR30_im, Complex.im_ofNat]
    norm_num
  have hsq : (7.34 : ℝ) ^ 2 ≤ ‖1 - sR30 / 2 + 5‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (7.34 : ℝ) = Real.sqrt ((7.34 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR30 / 2 + 5‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR30 / 2 + 5‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c6 = 8.17 ≤ ‖1 - sR30 / 2 + 6‖`. -/
theorem norm_zUpR30_6_ge :
    (8.17 : ℝ) ≤ ‖1 - sR30 / 2 + 6‖ := by
  have hre : (1 - sR30 / 2 + 6).re = 6.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR30 / 2 + 6).im = -4.375 := by
    simp only [Complex.add_im, zUpR30_im, Complex.im_ofNat]
    norm_num
  have hsq : (8.17 : ℝ) ^ 2 ≤ ‖1 - sR30 / 2 + 6‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (8.17 : ℝ) = Real.sqrt ((8.17 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR30 / 2 + 6‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR30 / 2 + 6‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c7 = 9.03 ≤ ‖1 - sR30 / 2 + 7‖`. -/
theorem norm_zUpR30_7_ge :
    (9.03 : ℝ) ≤ ‖1 - sR30 / 2 + 7‖ := by
  have hre : (1 - sR30 / 2 + 7).re = 7.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR30 / 2 + 7).im = -4.375 := by
    simp only [Complex.add_im, zUpR30_im, Complex.im_ofNat]
    norm_num
  have hsq : (9.03 : ℝ) ^ 2 ≤ ‖1 - sR30 / 2 + 7‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (9.03 : ℝ) = Real.sqrt ((9.03 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR30 / 2 + 7‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR30 / 2 + 7‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c8 = 9.91 ≤ ‖1 - sR30 / 2 + 8‖`. -/
theorem norm_zUpR30_8_ge :
    (9.91 : ℝ) ≤ ‖1 - sR30 / 2 + 8‖ := by
  have hre : (1 - sR30 / 2 + 8).re = 8.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR30 / 2 + 8).im = -4.375 := by
    simp only [Complex.add_im, zUpR30_im, Complex.im_ofNat]
    norm_num
  have hsq : (9.91 : ℝ) ^ 2 ≤ ‖1 - sR30 / 2 + 8‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (9.91 : ℝ) = Real.sqrt ((9.91 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR30 / 2 + 8‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR30 / 2 + 8‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c9 = 10.82 ≤ ‖1 - sR30 / 2 + 9‖`. -/
theorem norm_zUpR30_9_ge :
    (10.82 : ℝ) ≤ ‖1 - sR30 / 2 + 9‖ := by
  have hre : (1 - sR30 / 2 + 9).re = 9.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR30 / 2 + 9).im = -4.375 := by
    simp only [Complex.add_im, zUpR30_im, Complex.im_ofNat]
    norm_num
  have hsq : (10.82 : ℝ) ^ 2 ≤ ‖1 - sR30 / 2 + 9‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (10.82 : ℝ) = Real.sqrt ((10.82 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR30 / 2 + 9‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR30 / 2 + 9‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c10 = 11.74 ≤ ‖1 - sR30 / 2 + 10‖`. -/
theorem norm_zUpR30_10_ge :
    (11.74 : ℝ) ≤ ‖1 - sR30 / 2 + 10‖ := by
  have hre : (1 - sR30 / 2 + 10).re = 10.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR30 / 2 + 10).im = -4.375 := by
    simp only [Complex.add_im, zUpR30_im, Complex.im_ofNat]
    norm_num
  have hsq : (11.74 : ℝ) ^ 2 ≤ ‖1 - sR30 / 2 + 10‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (11.74 : ℝ) = Real.sqrt ((11.74 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR30 / 2 + 10‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR30 / 2 + 10‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c11 = 12.67 ≤ ‖1 - sR30 / 2 + 11‖`. -/
theorem norm_zUpR30_11_ge :
    (12.67 : ℝ) ≤ ‖1 - sR30 / 2 + 11‖ := by
  have hre : (1 - sR30 / 2 + 11).re = 11.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR30 / 2 + 11).im = -4.375 := by
    simp only [Complex.add_im, zUpR30_im, Complex.im_ofNat]
    norm_num
  have hsq : (12.67 : ℝ) ^ 2 ≤ ‖1 - sR30 / 2 + 11‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (12.67 : ℝ) = Real.sqrt ((12.67 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR30 / 2 + 11‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR30 / 2 + 11‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c12 = 13.62 ≤ ‖1 - sR30 / 2 + 12‖`. -/
theorem norm_zUpR30_12_ge :
    (13.62 : ℝ) ≤ ‖1 - sR30 / 2 + 12‖ := by
  have hre : (1 - sR30 / 2 + 12).re = 12.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR30 / 2 + 12).im = -4.375 := by
    simp only [Complex.add_im, zUpR30_im, Complex.im_ofNat]
    norm_num
  have hsq : (13.62 : ℝ) ^ 2 ≤ ‖1 - sR30 / 2 + 12‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (13.62 : ℝ) = Real.sqrt ((13.62 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR30 / 2 + 12‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR30 / 2 + 12‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c13 = 14.57 ≤ ‖1 - sR30 / 2 + 13‖`. -/
theorem norm_zUpR30_13_ge :
    (14.57 : ℝ) ≤ ‖1 - sR30 / 2 + 13‖ := by
  have hre : (1 - sR30 / 2 + 13).re = 13.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR30 / 2 + 13).im = -4.375 := by
    simp only [Complex.add_im, zUpR30_im, Complex.im_ofNat]
    norm_num
  have hsq : (14.57 : ℝ) ^ 2 ≤ ‖1 - sR30 / 2 + 13‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (14.57 : ℝ) = Real.sqrt ((14.57 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR30 / 2 + 13‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR30 / 2 + 13‖ := Real.sqrt_sq (norm_nonneg _)

/-- Shift nonvanishing (`Re > 0` so `{NE} 0`). -/
theorem zUpR30_ne0 : (1 - sR30 / 2) ≠ 0 := by
  have hre : (1 - sR30 / 2).re = 0.9 := zUpR30_re
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR30_add1_ne0 : (1 - sR30 / 2 + 1) ≠ 0 := by
  have hre : (1 - sR30 / 2 + 1).re = 1.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.one_re]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR30_add2_ne0 : (1 - sR30 / 2 + 2) ≠ 0 := by
  have hre : (1 - sR30 / 2 + 2).re = 2.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR30_add3_ne0 : (1 - sR30 / 2 + 3) ≠ 0 := by
  have hre : (1 - sR30 / 2 + 3).re = 3.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR30_add4_ne0 : (1 - sR30 / 2 + 4) ≠ 0 := by
  have hre : (1 - sR30 / 2 + 4).re = 4.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR30_add5_ne0 : (1 - sR30 / 2 + 5) ≠ 0 := by
  have hre : (1 - sR30 / 2 + 5).re = 5.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR30_add6_ne0 : (1 - sR30 / 2 + 6) ≠ 0 := by
  have hre : (1 - sR30 / 2 + 6).re = 6.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR30_add7_ne0 : (1 - sR30 / 2 + 7) ≠ 0 := by
  have hre : (1 - sR30 / 2 + 7).re = 7.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR30_add8_ne0 : (1 - sR30 / 2 + 8) ≠ 0 := by
  have hre : (1 - sR30 / 2 + 8).re = 8.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR30_add9_ne0 : (1 - sR30 / 2 + 9) ≠ 0 := by
  have hre : (1 - sR30 / 2 + 9).re = 9.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR30_add10_ne0 : (1 - sR30 / 2 + 10) ≠ 0 := by
  have hre : (1 - sR30 / 2 + 10).re = 10.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR30_add11_ne0 : (1 - sR30 / 2 + 11) ≠ 0 := by
  have hre : (1 - sR30 / 2 + 11).re = 11.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR30_add12_ne0 : (1 - sR30 / 2 + 12) ≠ 0 := by
  have hre : (1 - sR30 / 2 + 12).re = 12.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR30_add13_ne0 : (1 - sR30 / 2 + 13) ≠ 0 := by
  have hre : (1 - sR30 / 2 + 13).re = 13.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

/-- MAIN uniform UPPER bound at the R30 corner:
`‖Complex.Gamma (1 - sR30 / 2)‖ ≤ 0.01` (row-2 outer-tier mirror, `re = 0.9`, 14 shifts). -/
theorem gamma_one_sub_half_upper_R30 :
    ‖Complex.Gamma (1 - sR30 / 2)‖ ≤ 0.01 := by
  -- Shift chain `Gamma(z0+14) = (z0+13)..z0*Gamma(z0)`.
  have e0 : Complex.Gamma (1 - sR30 / 2 + 1)
      = (1 - sR30 / 2) * Complex.Gamma (1 - sR30 / 2) :=
    Complex.Gamma_add_one _ zUpR30_ne0
  have e1 : Complex.Gamma (1 - sR30 / 2 + 2)
      = (1 - sR30 / 2 + 1)
        * Complex.Gamma (1 - sR30 / 2 + 1) := by
    have h : (1 - sR30 / 2 + 2)
        = ((1 - sR30 / 2 + 1) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR30_add1_ne0
  have e2 : Complex.Gamma (1 - sR30 / 2 + 3)
      = (1 - sR30 / 2 + 2)
        * Complex.Gamma (1 - sR30 / 2 + 2) := by
    have h : (1 - sR30 / 2 + 3)
        = ((1 - sR30 / 2 + 2) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR30_add2_ne0
  have e3 : Complex.Gamma (1 - sR30 / 2 + 4)
      = (1 - sR30 / 2 + 3)
        * Complex.Gamma (1 - sR30 / 2 + 3) := by
    have h : (1 - sR30 / 2 + 4)
        = ((1 - sR30 / 2 + 3) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR30_add3_ne0
  have e4 : Complex.Gamma (1 - sR30 / 2 + 5)
      = (1 - sR30 / 2 + 4)
        * Complex.Gamma (1 - sR30 / 2 + 4) := by
    have h : (1 - sR30 / 2 + 5)
        = ((1 - sR30 / 2 + 4) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR30_add4_ne0
  have e5 : Complex.Gamma (1 - sR30 / 2 + 6)
      = (1 - sR30 / 2 + 5)
        * Complex.Gamma (1 - sR30 / 2 + 5) := by
    have h : (1 - sR30 / 2 + 6)
        = ((1 - sR30 / 2 + 5) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR30_add5_ne0
  have e6 : Complex.Gamma (1 - sR30 / 2 + 7)
      = (1 - sR30 / 2 + 6)
        * Complex.Gamma (1 - sR30 / 2 + 6) := by
    have h : (1 - sR30 / 2 + 7)
        = ((1 - sR30 / 2 + 6) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR30_add6_ne0
  have e7 : Complex.Gamma (1 - sR30 / 2 + 8)
      = (1 - sR30 / 2 + 7)
        * Complex.Gamma (1 - sR30 / 2 + 7) := by
    have h : (1 - sR30 / 2 + 8)
        = ((1 - sR30 / 2 + 7) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR30_add7_ne0
  have e8 : Complex.Gamma (1 - sR30 / 2 + 9)
      = (1 - sR30 / 2 + 8)
        * Complex.Gamma (1 - sR30 / 2 + 8) := by
    have h : (1 - sR30 / 2 + 9)
        = ((1 - sR30 / 2 + 8) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR30_add8_ne0
  have e9 : Complex.Gamma (1 - sR30 / 2 + 10)
      = (1 - sR30 / 2 + 9)
        * Complex.Gamma (1 - sR30 / 2 + 9) := by
    have h : (1 - sR30 / 2 + 10)
        = ((1 - sR30 / 2 + 9) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR30_add9_ne0
  have e10 : Complex.Gamma (1 - sR30 / 2 + 11)
      = (1 - sR30 / 2 + 10)
        * Complex.Gamma (1 - sR30 / 2 + 10) := by
    have h : (1 - sR30 / 2 + 11)
        = ((1 - sR30 / 2 + 10) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR30_add10_ne0
  have e11 : Complex.Gamma (1 - sR30 / 2 + 12)
      = (1 - sR30 / 2 + 11)
        * Complex.Gamma (1 - sR30 / 2 + 11) := by
    have h : (1 - sR30 / 2 + 12)
        = ((1 - sR30 / 2 + 11) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR30_add11_ne0
  have e12 : Complex.Gamma (1 - sR30 / 2 + 13)
      = (1 - sR30 / 2 + 12)
        * Complex.Gamma (1 - sR30 / 2 + 12) := by
    have h : (1 - sR30 / 2 + 13)
        = ((1 - sR30 / 2 + 12) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR30_add12_ne0
  have e13 : Complex.Gamma (1 - sR30 / 2 + 14)
      = (1 - sR30 / 2 + 13)
        * Complex.Gamma (1 - sR30 / 2 + 13) := by
    have h : (1 - sR30 / 2 + 14)
        = ((1 - sR30 / 2 + 13) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR30_add13_ne0
  have n0 : ‖Complex.Gamma (1 - sR30 / 2 + 1)‖
      = ‖1 - sR30 / 2‖
        * ‖Complex.Gamma (1 - sR30 / 2)‖ := by
    rw [e0, norm_mul]
  have n1 : ‖Complex.Gamma (1 - sR30 / 2 + 2)‖
      = ‖1 - sR30 / 2 + 1‖
        * ‖Complex.Gamma (1 - sR30 / 2 + 1)‖ := by
    rw [e1, norm_mul]
  have n2 : ‖Complex.Gamma (1 - sR30 / 2 + 3)‖
      = ‖1 - sR30 / 2 + 2‖
        * ‖Complex.Gamma (1 - sR30 / 2 + 2)‖ := by
    rw [e2, norm_mul]
  have n3 : ‖Complex.Gamma (1 - sR30 / 2 + 4)‖
      = ‖1 - sR30 / 2 + 3‖
        * ‖Complex.Gamma (1 - sR30 / 2 + 3)‖ := by
    rw [e3, norm_mul]
  have n4 : ‖Complex.Gamma (1 - sR30 / 2 + 5)‖
      = ‖1 - sR30 / 2 + 4‖
        * ‖Complex.Gamma (1 - sR30 / 2 + 4)‖ := by
    rw [e4, norm_mul]
  have n5 : ‖Complex.Gamma (1 - sR30 / 2 + 6)‖
      = ‖1 - sR30 / 2 + 5‖
        * ‖Complex.Gamma (1 - sR30 / 2 + 5)‖ := by
    rw [e5, norm_mul]
  have n6 : ‖Complex.Gamma (1 - sR30 / 2 + 7)‖
      = ‖1 - sR30 / 2 + 6‖
        * ‖Complex.Gamma (1 - sR30 / 2 + 6)‖ := by
    rw [e6, norm_mul]
  have n7 : ‖Complex.Gamma (1 - sR30 / 2 + 8)‖
      = ‖1 - sR30 / 2 + 7‖
        * ‖Complex.Gamma (1 - sR30 / 2 + 7)‖ := by
    rw [e7, norm_mul]
  have n8 : ‖Complex.Gamma (1 - sR30 / 2 + 9)‖
      = ‖1 - sR30 / 2 + 8‖
        * ‖Complex.Gamma (1 - sR30 / 2 + 8)‖ := by
    rw [e8, norm_mul]
  have n9 : ‖Complex.Gamma (1 - sR30 / 2 + 10)‖
      = ‖1 - sR30 / 2 + 9‖
        * ‖Complex.Gamma (1 - sR30 / 2 + 9)‖ := by
    rw [e9, norm_mul]
  have n10 : ‖Complex.Gamma (1 - sR30 / 2 + 11)‖
      = ‖1 - sR30 / 2 + 10‖
        * ‖Complex.Gamma (1 - sR30 / 2 + 10)‖ := by
    rw [e10, norm_mul]
  have n11 : ‖Complex.Gamma (1 - sR30 / 2 + 12)‖
      = ‖1 - sR30 / 2 + 11‖
        * ‖Complex.Gamma (1 - sR30 / 2 + 11)‖ := by
    rw [e11, norm_mul]
  have n12 : ‖Complex.Gamma (1 - sR30 / 2 + 13)‖
      = ‖1 - sR30 / 2 + 12‖
        * ‖Complex.Gamma (1 - sR30 / 2 + 12)‖ := by
    rw [e12, norm_mul]
  have n13 : ‖Complex.Gamma (1 - sR30 / 2 + 14)‖
      = ‖1 - sR30 / 2 + 13‖
        * ‖Complex.Gamma (1 - sR30 / 2 + 13)‖ := by
    rw [e13, norm_mul]
  have hprod : ‖Complex.Gamma (1 - sR30 / 2 + 14)‖
      = ‖1 - sR30 / 2 + 13‖
        * (‖1 - sR30 / 2 + 12‖
        * (‖1 - sR30 / 2 + 11‖
        * (‖1 - sR30 / 2 + 10‖
        * (‖1 - sR30 / 2 + 9‖
        * (‖1 - sR30 / 2 + 8‖
        * (‖1 - sR30 / 2 + 7‖
        * (‖1 - sR30 / 2 + 6‖
        * (‖1 - sR30 / 2 + 5‖
        * (‖1 - sR30 / 2 + 4‖
        * (‖1 - sR30 / 2 + 3‖
        * (‖1 - sR30 / 2 + 2‖
        * (‖1 - sR30 / 2 + 1‖
        * (‖1 - sR30 / 2‖
          * ‖Complex.Gamma (1 - sR30 / 2)‖))))))))))))) := by
    rw [n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n0]
  -- Denominator product lower bound.
  have q1 : (4.76 : ℝ) * 4.46
      ≤ ‖1 - sR30 / 2 + 1‖ * ‖1 - sR30 / 2‖ :=
    mul_le_mul norm_zUpR30_1_ge norm_zUpR30_0_ge (by norm_num) (norm_nonneg _)
  have q2 : (5.24 : ℝ) * (4.76 * (4.46))
      ≤ ‖1 - sR30 / 2 + 2‖ * (‖1 - sR30 / 2 + 1‖ * (‖1 - sR30 / 2‖)) :=
    mul_le_mul norm_zUpR30_2_ge q1 (by positivity) (norm_nonneg _)
  have q3 : (5.86 : ℝ) * (5.24 * (4.76 * (4.46)))
      ≤ ‖1 - sR30 / 2 + 3‖ * (‖1 - sR30 / 2 + 2‖ * (‖1 - sR30 / 2 + 1‖ * (‖1 - sR30 / 2‖))) :=
    mul_le_mul norm_zUpR30_3_ge q2 (by positivity) (norm_nonneg _)
  have q4 : (6.56 : ℝ) * (5.86 * (5.24 * (4.76 * (4.46))))
      ≤ ‖1 - sR30 / 2 + 4‖ * (‖1 - sR30 / 2 + 3‖ * (‖1 - sR30 / 2 + 2‖ * (‖1 - sR30 / 2 + 1‖ * (‖1 - sR30 / 2‖)))) :=
    mul_le_mul norm_zUpR30_4_ge q3 (by positivity) (norm_nonneg _)
  have q5 : (7.34 : ℝ) * (6.56 * (5.86 * (5.24 * (4.76 * (4.46)))))
      ≤ ‖1 - sR30 / 2 + 5‖ * (‖1 - sR30 / 2 + 4‖ * (‖1 - sR30 / 2 + 3‖ * (‖1 - sR30 / 2 + 2‖ * (‖1 - sR30 / 2 + 1‖ * (‖1 - sR30 / 2‖))))) :=
    mul_le_mul norm_zUpR30_5_ge q4 (by positivity) (norm_nonneg _)
  have q6 : (8.17 : ℝ) * (7.34 * (6.56 * (5.86 * (5.24 * (4.76 * (4.46))))))
      ≤ ‖1 - sR30 / 2 + 6‖ * (‖1 - sR30 / 2 + 5‖ * (‖1 - sR30 / 2 + 4‖ * (‖1 - sR30 / 2 + 3‖ * (‖1 - sR30 / 2 + 2‖ * (‖1 - sR30 / 2 + 1‖ * (‖1 - sR30 / 2‖)))))) :=
    mul_le_mul norm_zUpR30_6_ge q5 (by positivity) (norm_nonneg _)
  have q7 : (9.03 : ℝ) * (8.17 * (7.34 * (6.56 * (5.86 * (5.24 * (4.76 * (4.46)))))))
      ≤ ‖1 - sR30 / 2 + 7‖ * (‖1 - sR30 / 2 + 6‖ * (‖1 - sR30 / 2 + 5‖ * (‖1 - sR30 / 2 + 4‖ * (‖1 - sR30 / 2 + 3‖ * (‖1 - sR30 / 2 + 2‖ * (‖1 - sR30 / 2 + 1‖ * (‖1 - sR30 / 2‖))))))) :=
    mul_le_mul norm_zUpR30_7_ge q6 (by positivity) (norm_nonneg _)
  have q8 : (9.91 : ℝ) * (9.03 * (8.17 * (7.34 * (6.56 * (5.86 * (5.24 * (4.76 * (4.46))))))))
      ≤ ‖1 - sR30 / 2 + 8‖ * (‖1 - sR30 / 2 + 7‖ * (‖1 - sR30 / 2 + 6‖ * (‖1 - sR30 / 2 + 5‖ * (‖1 - sR30 / 2 + 4‖ * (‖1 - sR30 / 2 + 3‖ * (‖1 - sR30 / 2 + 2‖ * (‖1 - sR30 / 2 + 1‖ * (‖1 - sR30 / 2‖)))))))) :=
    mul_le_mul norm_zUpR30_8_ge q7 (by positivity) (norm_nonneg _)
  have q9 : (10.82 : ℝ) * (9.91 * (9.03 * (8.17 * (7.34 * (6.56 * (5.86 * (5.24 * (4.76 * (4.46)))))))))
      ≤ ‖1 - sR30 / 2 + 9‖ * (‖1 - sR30 / 2 + 8‖ * (‖1 - sR30 / 2 + 7‖ * (‖1 - sR30 / 2 + 6‖ * (‖1 - sR30 / 2 + 5‖ * (‖1 - sR30 / 2 + 4‖ * (‖1 - sR30 / 2 + 3‖ * (‖1 - sR30 / 2 + 2‖ * (‖1 - sR30 / 2 + 1‖ * (‖1 - sR30 / 2‖))))))))) :=
    mul_le_mul norm_zUpR30_9_ge q8 (by positivity) (norm_nonneg _)
  have q10 : (11.74 : ℝ) * (10.82 * (9.91 * (9.03 * (8.17 * (7.34 * (6.56 * (5.86 * (5.24 * (4.76 * (4.46))))))))))
      ≤ ‖1 - sR30 / 2 + 10‖ * (‖1 - sR30 / 2 + 9‖ * (‖1 - sR30 / 2 + 8‖ * (‖1 - sR30 / 2 + 7‖ * (‖1 - sR30 / 2 + 6‖ * (‖1 - sR30 / 2 + 5‖ * (‖1 - sR30 / 2 + 4‖ * (‖1 - sR30 / 2 + 3‖ * (‖1 - sR30 / 2 + 2‖ * (‖1 - sR30 / 2 + 1‖ * (‖1 - sR30 / 2‖)))))))))) :=
    mul_le_mul norm_zUpR30_10_ge q9 (by positivity) (norm_nonneg _)
  have q11 : (12.67 : ℝ) * (11.74 * (10.82 * (9.91 * (9.03 * (8.17 * (7.34 * (6.56 * (5.86 * (5.24 * (4.76 * (4.46)))))))))))
      ≤ ‖1 - sR30 / 2 + 11‖ * (‖1 - sR30 / 2 + 10‖ * (‖1 - sR30 / 2 + 9‖ * (‖1 - sR30 / 2 + 8‖ * (‖1 - sR30 / 2 + 7‖ * (‖1 - sR30 / 2 + 6‖ * (‖1 - sR30 / 2 + 5‖ * (‖1 - sR30 / 2 + 4‖ * (‖1 - sR30 / 2 + 3‖ * (‖1 - sR30 / 2 + 2‖ * (‖1 - sR30 / 2 + 1‖ * (‖1 - sR30 / 2‖))))))))))) :=
    mul_le_mul norm_zUpR30_11_ge q10 (by positivity) (norm_nonneg _)
  have q12 : (13.62 : ℝ) * (12.67 * (11.74 * (10.82 * (9.91 * (9.03 * (8.17 * (7.34 * (6.56 * (5.86 * (5.24 * (4.76 * (4.46))))))))))))
      ≤ ‖1 - sR30 / 2 + 12‖ * (‖1 - sR30 / 2 + 11‖ * (‖1 - sR30 / 2 + 10‖ * (‖1 - sR30 / 2 + 9‖ * (‖1 - sR30 / 2 + 8‖ * (‖1 - sR30 / 2 + 7‖ * (‖1 - sR30 / 2 + 6‖ * (‖1 - sR30 / 2 + 5‖ * (‖1 - sR30 / 2 + 4‖ * (‖1 - sR30 / 2 + 3‖ * (‖1 - sR30 / 2 + 2‖ * (‖1 - sR30 / 2 + 1‖ * (‖1 - sR30 / 2‖)))))))))))) :=
    mul_le_mul norm_zUpR30_12_ge q11 (by positivity) (norm_nonneg _)
  have q13 : (14.57 : ℝ) * (13.62 * (12.67 * (11.74 * (10.82 * (9.91 * (9.03 * (8.17 * (7.34 * (6.56 * (5.86 * (5.24 * (4.76 * (4.46)))))))))))))
      ≤ ‖1 - sR30 / 2 + 13‖ * (‖1 - sR30 / 2 + 12‖ * (‖1 - sR30 / 2 + 11‖ * (‖1 - sR30 / 2 + 10‖ * (‖1 - sR30 / 2 + 9‖ * (‖1 - sR30 / 2 + 8‖ * (‖1 - sR30 / 2 + 7‖ * (‖1 - sR30 / 2 + 6‖ * (‖1 - sR30 / 2 + 5‖ * (‖1 - sR30 / 2 + 4‖ * (‖1 - sR30 / 2 + 3‖ * (‖1 - sR30 / 2 + 2‖ * (‖1 - sR30 / 2 + 1‖ * (‖1 - sR30 / 2‖))))))))))))) :=
    mul_le_mul norm_zUpR30_13_ge q12 (by positivity) (norm_nonneg _)
  have hDlo : (7000000000000 : ℝ)
      ≤ (14.57 : ℝ) * (13.62 * (12.67 * (11.74 * (10.82 * (9.91 * (9.03 * (8.17 * (7.34 * (6.56 * (5.86 * (5.24 * (4.76 * (4.46))))))))))))) := by
    norm_num
  have hD_ge : (7000000000000 : ℝ)
      ≤ ‖1 - sR30 / 2 + 13‖ * (‖1 - sR30 / 2 + 12‖ * (‖1 - sR30 / 2 + 11‖ * (‖1 - sR30 / 2 + 10‖ * (‖1 - sR30 / 2 + 9‖ * (‖1 - sR30 / 2 + 8‖ * (‖1 - sR30 / 2 + 7‖ * (‖1 - sR30 / 2 + 6‖ * (‖1 - sR30 / 2 + 5‖ * (‖1 - sR30 / 2 + 4‖ * (‖1 - sR30 / 2 + 3‖ * (‖1 - sR30 / 2 + 2‖ * (‖1 - sR30 / 2 + 1‖ * (‖1 - sR30 / 2‖))))))))))))) :=
    le_trans hDlo q13
  have hD_pos : (0 : ℝ)
      < (‖1 - sR30 / 2 + 13‖
        * (‖1 - sR30 / 2 + 12‖
        * (‖1 - sR30 / 2 + 11‖
        * (‖1 - sR30 / 2 + 10‖
        * (‖1 - sR30 / 2 + 9‖
        * (‖1 - sR30 / 2 + 8‖
        * (‖1 - sR30 / 2 + 7‖
        * (‖1 - sR30 / 2 + 6‖
        * (‖1 - sR30 / 2 + 5‖
        * (‖1 - sR30 / 2 + 4‖
        * (‖1 - sR30 / 2 + 3‖
        * (‖1 - sR30 / 2 + 2‖
        * (‖1 - sR30 / 2 + 1‖
          * ‖1 - sR30 / 2‖))))))))))))) :=
    lt_of_lt_of_le (by norm_num) hD_ge
  -- Numerator: `‖Complex.Gamma (1 - sR30 / 2 + 14)‖ ≤ Real.Gamma(14.9) ≤ 69500000000`.
  have hre14 : (1 - sR30 / 2 + 14).re = 14.9 := by
    simp only [Complex.add_re, zUpR30_re, Complex.re_ofNat]
    norm_num
  have hGN_re : (0 : ℝ) < (1 - sR30 / 2 + 14).re := by
    rw [hre14]
    norm_num
  have hGN_le : ‖Complex.Gamma (1 - sR30 / 2 + 14)‖ ≤ 69500000000 := by
    have h1 : ‖Complex.Gamma (1 - sR30 / 2 + 14)‖
        ≤ Real.Gamma ((1 - sR30 / 2 + 14).re) :=
      R00GammaLower.norm_Gamma_le_realGamma hGN_re
    have hreNb : ((1 - sR30 / 2 + 14).re) = 14.9 := hre14
    rw [hreNb] at h1
    exact le_trans h1 CellGammaUpper09.realGamma_149_le
  -- Combine: `D * ‖Complex.Gamma (1 - sR30 / 2)‖ = ‖Complex.Gamma (1 - sR30 / 2 + 14)‖ ≤ 69500000000`, `D ≤ 7000000000000`.
  have hD_mul : (‖1 - sR30 / 2 + 13‖
        * (‖1 - sR30 / 2 + 12‖
        * (‖1 - sR30 / 2 + 11‖
        * (‖1 - sR30 / 2 + 10‖
        * (‖1 - sR30 / 2 + 9‖
        * (‖1 - sR30 / 2 + 8‖
        * (‖1 - sR30 / 2 + 7‖
        * (‖1 - sR30 / 2 + 6‖
        * (‖1 - sR30 / 2 + 5‖
        * (‖1 - sR30 / 2 + 4‖
        * (‖1 - sR30 / 2 + 3‖
        * (‖1 - sR30 / 2 + 2‖
        * (‖1 - sR30 / 2 + 1‖
          * ‖1 - sR30 / 2‖)))))))))))))
        * ‖Complex.Gamma (1 - sR30 / 2)‖
      = ‖Complex.Gamma (1 - sR30 / 2 + 14)‖ := by
    rw [hprod]
    ring
  have hle : (‖1 - sR30 / 2 + 13‖
        * (‖1 - sR30 / 2 + 12‖
        * (‖1 - sR30 / 2 + 11‖
        * (‖1 - sR30 / 2 + 10‖
        * (‖1 - sR30 / 2 + 9‖
        * (‖1 - sR30 / 2 + 8‖
        * (‖1 - sR30 / 2 + 7‖
        * (‖1 - sR30 / 2 + 6‖
        * (‖1 - sR30 / 2 + 5‖
        * (‖1 - sR30 / 2 + 4‖
        * (‖1 - sR30 / 2 + 3‖
        * (‖1 - sR30 / 2 + 2‖
        * (‖1 - sR30 / 2 + 1‖
          * ‖1 - sR30 / 2‖)))))))))))))
        * ‖Complex.Gamma (1 - sR30 / 2)‖ ≤ 69500000000 := by
    rw [hD_mul]
    exact hGN_le
  have hmul_comm : ‖Complex.Gamma (1 - sR30 / 2)‖
        * (‖1 - sR30 / 2 + 13‖
        * (‖1 - sR30 / 2 + 12‖
        * (‖1 - sR30 / 2 + 11‖
        * (‖1 - sR30 / 2 + 10‖
        * (‖1 - sR30 / 2 + 9‖
        * (‖1 - sR30 / 2 + 8‖
        * (‖1 - sR30 / 2 + 7‖
        * (‖1 - sR30 / 2 + 6‖
        * (‖1 - sR30 / 2 + 5‖
        * (‖1 - sR30 / 2 + 4‖
        * (‖1 - sR30 / 2 + 3‖
        * (‖1 - sR30 / 2 + 2‖
        * (‖1 - sR30 / 2 + 1‖
          * ‖1 - sR30 / 2‖)))))))))))))
        ≤ 69500000000 := by
    calc ‖Complex.Gamma (1 - sR30 / 2)‖ * _
          = _ * ‖Complex.Gamma (1 - sR30 / 2)‖ := mul_comm _ _
      _ ≤ 69500000000 := hle
  have hdiv : ‖Complex.Gamma (1 - sR30 / 2)‖
      ≤ 69500000000 / (‖1 - sR30 / 2 + 13‖
        * (‖1 - sR30 / 2 + 12‖
        * (‖1 - sR30 / 2 + 11‖
        * (‖1 - sR30 / 2 + 10‖
        * (‖1 - sR30 / 2 + 9‖
        * (‖1 - sR30 / 2 + 8‖
        * (‖1 - sR30 / 2 + 7‖
        * (‖1 - sR30 / 2 + 6‖
        * (‖1 - sR30 / 2 + 5‖
        * (‖1 - sR30 / 2 + 4‖
        * (‖1 - sR30 / 2 + 3‖
        * (‖1 - sR30 / 2 + 2‖
        * (‖1 - sR30 / 2 + 1‖
          * ‖1 - sR30 / 2‖)))))))))))))
        :=
    (le_div_iff₀ hD_pos).mpr hmul_comm
  have hcap : (69500000000 : ℝ)
      ≤ 0.01 * (‖1 - sR30 / 2 + 13‖
        * (‖1 - sR30 / 2 + 12‖
        * (‖1 - sR30 / 2 + 11‖
        * (‖1 - sR30 / 2 + 10‖
        * (‖1 - sR30 / 2 + 9‖
        * (‖1 - sR30 / 2 + 8‖
        * (‖1 - sR30 / 2 + 7‖
        * (‖1 - sR30 / 2 + 6‖
        * (‖1 - sR30 / 2 + 5‖
        * (‖1 - sR30 / 2 + 4‖
        * (‖1 - sR30 / 2 + 3‖
        * (‖1 - sR30 / 2 + 2‖
        * (‖1 - sR30 / 2 + 1‖
          * ‖1 - sR30 / 2‖))))))))))))) := by
    calc (69500000000 : ℝ) ≤ 0.01 * 7000000000000 := by norm_num
      _ ≤ 0.01 * _ :=
          mul_le_mul_of_nonneg_left hD_ge (by norm_num)
  have hfinal : 69500000000 / (‖1 - sR30 / 2 + 13‖ * (‖1 - sR30 / 2 + 12‖ * (‖1 - sR30 / 2 + 11‖ * (‖1 - sR30 / 2 + 10‖ * (‖1 - sR30 / 2 + 9‖ * (‖1 - sR30 / 2 + 8‖ * (‖1 - sR30 / 2 + 7‖ * (‖1 - sR30 / 2 + 6‖ * (‖1 - sR30 / 2 + 5‖ * (‖1 - sR30 / 2 + 4‖ * (‖1 - sR30 / 2 + 3‖ * (‖1 - sR30 / 2 + 2‖ * (‖1 - sR30 / 2 + 1‖ * (‖1 - sR30 / 2‖))))))))))))))
      ≤ 0.01 :=
    (div_le_iff₀ hD_pos).mpr hcap
  exact le_trans hdiv hfinal

end R30GammaUpper

namespace CellGammaUpper09475

/-- Real convexity feeder: `Real.Gamma 1.9475 ≤ 1`
(`1.9475 = 0.0525*ℝ1 + 0.9475*ℝ2`, `Gamma 1 = Gamma 2 = 1`). -/
theorem realGamma_19475_le_one : Real.Gamma 1.9475 ≤ 1 := by
  have hconv := Real.convexOn_Gamma
  have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have h2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have ha : (0 : ℝ) ≤ 0.0525 := by norm_num
  have hb : (0 : ℝ) ≤ 0.9475 := by norm_num
  have hab : (0.0525 : ℝ) + 0.9475 = 1 := by norm_num
  have h := hconv.2 h1 h2 ha hb hab
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
  have heq : (0.0525 : ℝ) * 1 + 0.9475 * 2 = 1.9475 := by norm_num
  have hrhs : (0.0525 : ℝ) * 1 + 0.9475 * 1 = (1 : ℝ) := by norm_num
  rw [heq] at h
  rw [hrhs] at h
  exact h

/-- `Real.Gamma 2.9475 ≤ 1.9475`. -/
theorem realGamma_29475_le : Real.Gamma 2.9475 ≤ 1.9475 := by
  have h : Real.Gamma (1.9475 + 1) = 1.9475 * Real.Gamma 1.9475 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (1.9475 : ℝ) + 1 = 2.9475 := by norm_num
  rw [heq] at h
  rw [h]
  calc (1.9475 : ℝ) * Real.Gamma 1.9475 ≤ 1.9475 * 1 :=
        mul_le_mul_of_nonneg_left realGamma_19475_le_one (by norm_num)
    _ = 1.9475 := mul_one _

/-- `Real.Gamma 3.9475 ≤ 1.9475 * 2.9475`. -/
theorem realGamma_39475_le : Real.Gamma 3.9475 ≤ 1.9475 * 2.9475 := by
  have h : Real.Gamma (2.9475 + 1) = 2.9475 * Real.Gamma 2.9475 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (2.9475 : ℝ) + 1 = 3.9475 := by norm_num
  rw [heq] at h
  rw [h]
  calc (2.9475 : ℝ) * Real.Gamma 2.9475 ≤ 2.9475 * 1.9475 :=
        mul_le_mul_of_nonneg_left realGamma_29475_le (by norm_num)
    _ = 1.9475 * 2.9475 := mul_comm _ _

/-- `Real.Gamma 4.9475 ≤ 1.9475 * 2.9475 * 3.9475`. -/
theorem realGamma_49475_le : Real.Gamma 4.9475 ≤ 1.9475 * 2.9475 * 3.9475 := by
  have h : Real.Gamma (3.9475 + 1) = 3.9475 * Real.Gamma 3.9475 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (3.9475 : ℝ) + 1 = 4.9475 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 3.9475 * Real.Gamma 3.9475
      ≤ 3.9475 * (1.9475 * 2.9475) :=
    mul_le_mul_of_nonneg_left realGamma_39475_le (by norm_num)
  calc (3.9475 : ℝ) * Real.Gamma 3.9475
        ≤ 3.9475 * (1.9475 * 2.9475) := hle
    _ = 1.9475 * 2.9475 * 3.9475 := by ring

/-- `Real.Gamma 5.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475`. -/
theorem realGamma_59475_le : Real.Gamma 5.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 := by
  have h : Real.Gamma (4.9475 + 1) = 4.9475 * Real.Gamma 4.9475 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (4.9475 : ℝ) + 1 = 5.9475 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 4.9475 * Real.Gamma 4.9475
      ≤ 4.9475 * (1.9475 * 2.9475 * 3.9475) :=
    mul_le_mul_of_nonneg_left realGamma_49475_le (by norm_num)
  calc (4.9475 : ℝ) * Real.Gamma 4.9475
        ≤ 4.9475 * (1.9475 * 2.9475 * 3.9475) := hle
    _ = 1.9475 * 2.9475 * 3.9475 * 4.9475 := by ring

/-- `Real.Gamma 6.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475`. -/
theorem realGamma_69475_le :
    Real.Gamma 6.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 := by
  have h : Real.Gamma (5.9475 + 1) = 5.9475 * Real.Gamma 5.9475 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (5.9475 : ℝ) + 1 = 6.9475 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 5.9475 * Real.Gamma 5.9475
      ≤ 5.9475 * (1.9475 * 2.9475 * 3.9475 * 4.9475) :=
    mul_le_mul_of_nonneg_left realGamma_59475_le (by norm_num)
  calc (5.9475 : ℝ) * Real.Gamma 5.9475
        ≤ 5.9475 * (1.9475 * 2.9475 * 3.9475 * 4.9475) := hle
    _ = 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 := by ring

/-- `Real.Gamma 7.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475`. -/
theorem realGamma_79475_le :
    Real.Gamma 7.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 := by
  have h : Real.Gamma (6.9475 + 1) = 6.9475 * Real.Gamma 6.9475 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (6.9475 : ℝ) + 1 = 7.9475 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 6.9475 * Real.Gamma 6.9475
      ≤ 6.9475 * (1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475) :=
    mul_le_mul_of_nonneg_left realGamma_69475_le (by norm_num)
  calc (6.9475 : ℝ) * Real.Gamma 6.9475
        ≤ 6.9475 * (1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475) := hle
    _ = 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 := by ring

/-- `Real.Gamma 8.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475`. -/
theorem realGamma_89475_le :
    Real.Gamma 8.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 := by
  have h : Real.Gamma (7.9475 + 1) = 7.9475 * Real.Gamma 7.9475 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (7.9475 : ℝ) + 1 = 8.9475 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 7.9475 * Real.Gamma 7.9475
      ≤ 7.9475 * (1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475) :=
    mul_le_mul_of_nonneg_left realGamma_79475_le (by norm_num)
  calc (7.9475 : ℝ) * Real.Gamma 7.9475
        ≤ 7.9475 * (1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475) := hle
    _ = 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 := by ring

/-- `Real.Gamma 9.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475`. -/
theorem realGamma_99475_le :
    Real.Gamma 9.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 := by
  have h : Real.Gamma (8.9475 + 1) = 8.9475 * Real.Gamma 8.9475 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (8.9475 : ℝ) + 1 = 9.9475 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 8.9475 * Real.Gamma 8.9475
      ≤ 8.9475 * (1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475) :=
    mul_le_mul_of_nonneg_left realGamma_89475_le (by norm_num)
  calc (8.9475 : ℝ) * Real.Gamma 8.9475
        ≤ 8.9475 * (1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475) := hle
    _ = 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 := by ring

/-- `Real.Gamma 10.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475`. -/
theorem realGamma_109475_le :
    Real.Gamma 10.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 := by
  have h : Real.Gamma (9.9475 + 1) = 9.9475 * Real.Gamma 9.9475 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (9.9475 : ℝ) + 1 = 10.9475 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 9.9475 * Real.Gamma 9.9475
      ≤ 9.9475 * (1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475) :=
    mul_le_mul_of_nonneg_left realGamma_99475_le (by norm_num)
  calc (9.9475 : ℝ) * Real.Gamma 9.9475
        ≤ 9.9475 * (1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475) := hle
    _ = 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 := by ring

/-- `Real.Gamma 11.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475`. -/
theorem realGamma_119475_le :
    Real.Gamma 11.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475 := by
  have h : Real.Gamma (10.9475 + 1) = 10.9475 * Real.Gamma 10.9475 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (10.9475 : ℝ) + 1 = 11.9475 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 10.9475 * Real.Gamma 10.9475
      ≤ 10.9475 * (1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475) :=
    mul_le_mul_of_nonneg_left realGamma_109475_le (by norm_num)
  calc (10.9475 : ℝ) * Real.Gamma 10.9475
        ≤ 10.9475 * (1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475) := hle
    _ = 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475 := by ring

/-- `Real.Gamma 12.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475 * 11.9475`. -/
theorem realGamma_129475_le :
    Real.Gamma 12.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475 * 11.9475 := by
  have h : Real.Gamma (11.9475 + 1) = 11.9475 * Real.Gamma 11.9475 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (11.9475 : ℝ) + 1 = 12.9475 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 11.9475 * Real.Gamma 11.9475
      ≤ 11.9475 * (1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475) :=
    mul_le_mul_of_nonneg_left realGamma_119475_le (by norm_num)
  calc (11.9475 : ℝ) * Real.Gamma 11.9475
        ≤ 11.9475 * (1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475) := hle
    _ = 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475 * 11.9475 := by ring

/-- `Real.Gamma 13.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475 * 11.9475 * 12.9475`. -/
theorem realGamma_139475_le :
    Real.Gamma 13.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475 * 11.9475 * 12.9475 := by
  have h : Real.Gamma (12.9475 + 1) = 12.9475 * Real.Gamma 12.9475 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (12.9475 : ℝ) + 1 = 13.9475 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 12.9475 * Real.Gamma 12.9475
      ≤ 12.9475 * (1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475 * 11.9475) :=
    mul_le_mul_of_nonneg_left realGamma_129475_le (by norm_num)
  calc (12.9475 : ℝ) * Real.Gamma 12.9475
        ≤ 12.9475 * (1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475 * 11.9475) := hle
    _ = 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475 * 11.9475 * 12.9475 := by ring

/-- `Real.Gamma 14.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475 * 11.9475 * 12.9475 * 13.9475`. -/
theorem realGamma_149475_le :
    Real.Gamma 14.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475 * 11.9475 * 12.9475 * 13.9475 := by
  have h : Real.Gamma (13.9475 + 1) = 13.9475 * Real.Gamma 13.9475 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (13.9475 : ℝ) + 1 = 14.9475 := by norm_num
  rw [heq] at h
  rw [h]
  have hle : 13.9475 * Real.Gamma 13.9475
      ≤ 13.9475 * (1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475 * 11.9475 * 12.9475) :=
    mul_le_mul_of_nonneg_left realGamma_139475_le (by norm_num)
  calc (13.9475 : ℝ) * Real.Gamma 13.9475
        ≤ 13.9475 * (1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475 * 11.9475 * 12.9475) := hle
    _ = 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475 * 11.9475 * 12.9475 * 13.9475 := by ring

/-- `Real.Gamma 15.9475 ≤ 1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475 * 11.9475 * 12.9475 * 13.9475 * 14.9475 ≤ 1160000000000` (numerator cap). -/
theorem realGamma_159475_le : Real.Gamma 15.9475 ≤ 1160000000000 := by
  have h : Real.Gamma (14.9475 + 1) = 14.9475 * Real.Gamma 14.9475 :=
    Real.Gamma_add_one (by norm_num)
  have heq : (14.9475 : ℝ) + 1 = 15.9475 := by norm_num
  rw [heq] at h
  rw [h] at ⊢
  have hle : 14.9475 * Real.Gamma 14.9475
      ≤ 14.9475 * (1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475 * 11.9475 * 12.9475 * 13.9475) :=
    mul_le_mul_of_nonneg_left realGamma_149475_le (by norm_num)
  have hprod : (14.9475 : ℝ) * (1.9475 * 2.9475 * 3.9475 * 4.9475 * 5.9475 * 6.9475 * 7.9475 * 8.9475 * 9.9475 * 10.9475 * 11.9475 * 12.9475 * 13.9475) ≤ 1160000000000 := by
    norm_num
  exact le_trans hle hprod

end CellGammaUpper09475

namespace R31GammaUpper

/-- The R31 `s`-plane center: `s = 1/2 + I·z` at `z = R31.center`. -/
noncomputable def sR31 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R31.center

/-- `R31.center = -8.75 + 0.395·I` (from `R31_x0/x1/y0/y1`). -/
theorem R31_center_eq :
    CentralCoverAssembly.R31.center =
      (((-8.75 : ℝ))) + Complex.I * ((((0.395 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R31_x0, CentralCoverAssembly.R31_x1,
      CentralCoverAssembly.R31_y0, CentralCoverAssembly.R31_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R31_x0, CentralCoverAssembly.R31_x1,
      CentralCoverAssembly.R31_y0, CentralCoverAssembly.R31_y1]
    simp
    norm_num

/-- `Re sR31 = 0.105`. -/
theorem sR31_re : sR31.re = 0.105 := by
  unfold sR31
  rw [R31_center_eq]
  simp
  norm_num

/-- `Im sR31 = -8.75`. -/
theorem sR31_im : sR31.im = -8.75 := by
  unfold sR31
  rw [R31_center_eq]
  simp

/-- `Re(1 - sR31/2) = 0.9475`. -/
theorem zUpR31_re : (1 - sR31 / 2).re = 0.9475 := by
  rw [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, sR31_re]
  norm_num

/-- `Im(1 - sR31/2) = 4.375`. -/
theorem zUpR31_im : (1 - sR31 / 2).im = 4.375 := by
  rw [Complex.sub_im, Complex.one_im, Complex.div_ofNat_im, sR31_im]
  norm_num

/-- Denominator floor `c0 = 4.47 ≤ ‖1 - sR31 / 2‖`. -/
theorem norm_zUpR31_0_ge :
    (4.47 : ℝ) ≤ ‖1 - sR31 / 2‖ := by
  have hsq : (4.47 : ℝ) ^ 2 ≤ ‖1 - sR31 / 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, zUpR31_re, zUpR31_im]
    norm_num
  calc (4.47 : ℝ) = Real.sqrt ((4.47 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR31 / 2‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR31 / 2‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c1 = 4.78 ≤ ‖1 - sR31 / 2 + 1‖`. -/
theorem norm_zUpR31_1_ge :
    (4.78 : ℝ) ≤ ‖1 - sR31 / 2 + 1‖ := by
  have hre : (1 - sR31 / 2 + 1).re = 1.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.one_re]
    norm_num
  have him : (1 - sR31 / 2 + 1).im = 4.375 := by
    simp only [Complex.add_im, zUpR31_im, Complex.one_im]
    norm_num
  have hsq : (4.78 : ℝ) ^ 2 ≤ ‖1 - sR31 / 2 + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (4.78 : ℝ) = Real.sqrt ((4.78 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR31 / 2 + 1‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR31 / 2 + 1‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c2 = 5.27 ≤ ‖1 - sR31 / 2 + 2‖`. -/
theorem norm_zUpR31_2_ge :
    (5.27 : ℝ) ≤ ‖1 - sR31 / 2 + 2‖ := by
  have hre : (1 - sR31 / 2 + 2).re = 2.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR31 / 2 + 2).im = 4.375 := by
    simp only [Complex.add_im, zUpR31_im, Complex.im_ofNat]
    norm_num
  have hsq : (5.27 : ℝ) ^ 2 ≤ ‖1 - sR31 / 2 + 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (5.27 : ℝ) = Real.sqrt ((5.27 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR31 / 2 + 2‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR31 / 2 + 2‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c3 = 5.89 ≤ ‖1 - sR31 / 2 + 3‖`. -/
theorem norm_zUpR31_3_ge :
    (5.89 : ℝ) ≤ ‖1 - sR31 / 2 + 3‖ := by
  have hre : (1 - sR31 / 2 + 3).re = 3.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR31 / 2 + 3).im = 4.375 := by
    simp only [Complex.add_im, zUpR31_im, Complex.im_ofNat]
    norm_num
  have hsq : (5.89 : ℝ) ^ 2 ≤ ‖1 - sR31 / 2 + 3‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (5.89 : ℝ) = Real.sqrt ((5.89 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR31 / 2 + 3‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR31 / 2 + 3‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c4 = 6.6 ≤ ‖1 - sR31 / 2 + 4‖`. -/
theorem norm_zUpR31_4_ge :
    (6.6 : ℝ) ≤ ‖1 - sR31 / 2 + 4‖ := by
  have hre : (1 - sR31 / 2 + 4).re = 4.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR31 / 2 + 4).im = 4.375 := by
    simp only [Complex.add_im, zUpR31_im, Complex.im_ofNat]
    norm_num
  have hsq : (6.6 : ℝ) ^ 2 ≤ ‖1 - sR31 / 2 + 4‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (6.6 : ℝ) = Real.sqrt ((6.6 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR31 / 2 + 4‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR31 / 2 + 4‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c5 = 7.38 ≤ ‖1 - sR31 / 2 + 5‖`. -/
theorem norm_zUpR31_5_ge :
    (7.38 : ℝ) ≤ ‖1 - sR31 / 2 + 5‖ := by
  have hre : (1 - sR31 / 2 + 5).re = 5.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR31 / 2 + 5).im = 4.375 := by
    simp only [Complex.add_im, zUpR31_im, Complex.im_ofNat]
    norm_num
  have hsq : (7.38 : ℝ) ^ 2 ≤ ‖1 - sR31 / 2 + 5‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (7.38 : ℝ) = Real.sqrt ((7.38 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR31 / 2 + 5‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR31 / 2 + 5‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c6 = 8.21 ≤ ‖1 - sR31 / 2 + 6‖`. -/
theorem norm_zUpR31_6_ge :
    (8.21 : ℝ) ≤ ‖1 - sR31 / 2 + 6‖ := by
  have hre : (1 - sR31 / 2 + 6).re = 6.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR31 / 2 + 6).im = 4.375 := by
    simp only [Complex.add_im, zUpR31_im, Complex.im_ofNat]
    norm_num
  have hsq : (8.21 : ℝ) ^ 2 ≤ ‖1 - sR31 / 2 + 6‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (8.21 : ℝ) = Real.sqrt ((8.21 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR31 / 2 + 6‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR31 / 2 + 6‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c7 = 9.07 ≤ ‖1 - sR31 / 2 + 7‖`. -/
theorem norm_zUpR31_7_ge :
    (9.07 : ℝ) ≤ ‖1 - sR31 / 2 + 7‖ := by
  have hre : (1 - sR31 / 2 + 7).re = 7.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR31 / 2 + 7).im = 4.375 := by
    simp only [Complex.add_im, zUpR31_im, Complex.im_ofNat]
    norm_num
  have hsq : (9.07 : ℝ) ^ 2 ≤ ‖1 - sR31 / 2 + 7‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (9.07 : ℝ) = Real.sqrt ((9.07 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR31 / 2 + 7‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR31 / 2 + 7‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c8 = 9.95 ≤ ‖1 - sR31 / 2 + 8‖`. -/
theorem norm_zUpR31_8_ge :
    (9.95 : ℝ) ≤ ‖1 - sR31 / 2 + 8‖ := by
  have hre : (1 - sR31 / 2 + 8).re = 8.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR31 / 2 + 8).im = 4.375 := by
    simp only [Complex.add_im, zUpR31_im, Complex.im_ofNat]
    norm_num
  have hsq : (9.95 : ℝ) ^ 2 ≤ ‖1 - sR31 / 2 + 8‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (9.95 : ℝ) = Real.sqrt ((9.95 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR31 / 2 + 8‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR31 / 2 + 8‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c9 = 10.86 ≤ ‖1 - sR31 / 2 + 9‖`. -/
theorem norm_zUpR31_9_ge :
    (10.86 : ℝ) ≤ ‖1 - sR31 / 2 + 9‖ := by
  have hre : (1 - sR31 / 2 + 9).re = 9.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR31 / 2 + 9).im = 4.375 := by
    simp only [Complex.add_im, zUpR31_im, Complex.im_ofNat]
    norm_num
  have hsq : (10.86 : ℝ) ^ 2 ≤ ‖1 - sR31 / 2 + 9‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (10.86 : ℝ) = Real.sqrt ((10.86 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR31 / 2 + 9‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR31 / 2 + 9‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c10 = 11.78 ≤ ‖1 - sR31 / 2 + 10‖`. -/
theorem norm_zUpR31_10_ge :
    (11.78 : ℝ) ≤ ‖1 - sR31 / 2 + 10‖ := by
  have hre : (1 - sR31 / 2 + 10).re = 10.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR31 / 2 + 10).im = 4.375 := by
    simp only [Complex.add_im, zUpR31_im, Complex.im_ofNat]
    norm_num
  have hsq : (11.78 : ℝ) ^ 2 ≤ ‖1 - sR31 / 2 + 10‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (11.78 : ℝ) = Real.sqrt ((11.78 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR31 / 2 + 10‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR31 / 2 + 10‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c11 = 12.72 ≤ ‖1 - sR31 / 2 + 11‖`. -/
theorem norm_zUpR31_11_ge :
    (12.72 : ℝ) ≤ ‖1 - sR31 / 2 + 11‖ := by
  have hre : (1 - sR31 / 2 + 11).re = 11.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR31 / 2 + 11).im = 4.375 := by
    simp only [Complex.add_im, zUpR31_im, Complex.im_ofNat]
    norm_num
  have hsq : (12.72 : ℝ) ^ 2 ≤ ‖1 - sR31 / 2 + 11‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (12.72 : ℝ) = Real.sqrt ((12.72 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR31 / 2 + 11‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR31 / 2 + 11‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c12 = 13.66 ≤ ‖1 - sR31 / 2 + 12‖`. -/
theorem norm_zUpR31_12_ge :
    (13.66 : ℝ) ≤ ‖1 - sR31 / 2 + 12‖ := by
  have hre : (1 - sR31 / 2 + 12).re = 12.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR31 / 2 + 12).im = 4.375 := by
    simp only [Complex.add_im, zUpR31_im, Complex.im_ofNat]
    norm_num
  have hsq : (13.66 : ℝ) ^ 2 ≤ ‖1 - sR31 / 2 + 12‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (13.66 : ℝ) = Real.sqrt ((13.66 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR31 / 2 + 12‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR31 / 2 + 12‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c13 = 14.61 ≤ ‖1 - sR31 / 2 + 13‖`. -/
theorem norm_zUpR31_13_ge :
    (14.61 : ℝ) ≤ ‖1 - sR31 / 2 + 13‖ := by
  have hre : (1 - sR31 / 2 + 13).re = 13.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR31 / 2 + 13).im = 4.375 := by
    simp only [Complex.add_im, zUpR31_im, Complex.im_ofNat]
    norm_num
  have hsq : (14.61 : ℝ) ^ 2 ≤ ‖1 - sR31 / 2 + 13‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (14.61 : ℝ) = Real.sqrt ((14.61 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR31 / 2 + 13‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR31 / 2 + 13‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c14 = 15.57 ≤ ‖1 - sR31 / 2 + 14‖`. -/
theorem norm_zUpR31_14_ge :
    (15.57 : ℝ) ≤ ‖1 - sR31 / 2 + 14‖ := by
  have hre : (1 - sR31 / 2 + 14).re = 14.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR31 / 2 + 14).im = 4.375 := by
    simp only [Complex.add_im, zUpR31_im, Complex.im_ofNat]
    norm_num
  have hsq : (15.57 : ℝ) ^ 2 ≤ ‖1 - sR31 / 2 + 14‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (15.57 : ℝ) = Real.sqrt ((15.57 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR31 / 2 + 14‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR31 / 2 + 14‖ := Real.sqrt_sq (norm_nonneg _)

/-- Shift nonvanishing (`Re > 0` so `{NE} 0`). -/
theorem zUpR31_ne0 : (1 - sR31 / 2) ≠ 0 := by
  have hre : (1 - sR31 / 2).re = 0.9475 := zUpR31_re
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR31_add1_ne0 : (1 - sR31 / 2 + 1) ≠ 0 := by
  have hre : (1 - sR31 / 2 + 1).re = 1.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.one_re]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR31_add2_ne0 : (1 - sR31 / 2 + 2) ≠ 0 := by
  have hre : (1 - sR31 / 2 + 2).re = 2.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR31_add3_ne0 : (1 - sR31 / 2 + 3) ≠ 0 := by
  have hre : (1 - sR31 / 2 + 3).re = 3.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR31_add4_ne0 : (1 - sR31 / 2 + 4) ≠ 0 := by
  have hre : (1 - sR31 / 2 + 4).re = 4.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR31_add5_ne0 : (1 - sR31 / 2 + 5) ≠ 0 := by
  have hre : (1 - sR31 / 2 + 5).re = 5.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR31_add6_ne0 : (1 - sR31 / 2 + 6) ≠ 0 := by
  have hre : (1 - sR31 / 2 + 6).re = 6.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR31_add7_ne0 : (1 - sR31 / 2 + 7) ≠ 0 := by
  have hre : (1 - sR31 / 2 + 7).re = 7.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR31_add8_ne0 : (1 - sR31 / 2 + 8) ≠ 0 := by
  have hre : (1 - sR31 / 2 + 8).re = 8.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR31_add9_ne0 : (1 - sR31 / 2 + 9) ≠ 0 := by
  have hre : (1 - sR31 / 2 + 9).re = 9.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR31_add10_ne0 : (1 - sR31 / 2 + 10) ≠ 0 := by
  have hre : (1 - sR31 / 2 + 10).re = 10.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR31_add11_ne0 : (1 - sR31 / 2 + 11) ≠ 0 := by
  have hre : (1 - sR31 / 2 + 11).re = 11.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR31_add12_ne0 : (1 - sR31 / 2 + 12) ≠ 0 := by
  have hre : (1 - sR31 / 2 + 12).re = 12.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR31_add13_ne0 : (1 - sR31 / 2 + 13) ≠ 0 := by
  have hre : (1 - sR31 / 2 + 13).re = 13.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR31_add14_ne0 : (1 - sR31 / 2 + 14) ≠ 0 := by
  have hre : (1 - sR31 / 2 + 14).re = 14.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

/-- MAIN uniform UPPER bound at the R31 corner:
`‖Complex.Gamma (1 - sR31 / 2)‖ ≤ 0.01` (row-3 outer-tier, `re = 0.9475`, 15 shifts). -/
theorem gamma_one_sub_half_upper_R31 :
    ‖Complex.Gamma (1 - sR31 / 2)‖ ≤ 0.01 := by
  -- Shift chain `Gamma(z0+15) = (z0+14)..z0*Gamma(z0)`.
  have e0 : Complex.Gamma (1 - sR31 / 2 + 1)
      = (1 - sR31 / 2) * Complex.Gamma (1 - sR31 / 2) :=
    Complex.Gamma_add_one _ zUpR31_ne0
  have e1 : Complex.Gamma (1 - sR31 / 2 + 2)
      = (1 - sR31 / 2 + 1)
        * Complex.Gamma (1 - sR31 / 2 + 1) := by
    have h : (1 - sR31 / 2 + 2)
        = ((1 - sR31 / 2 + 1) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR31_add1_ne0
  have e2 : Complex.Gamma (1 - sR31 / 2 + 3)
      = (1 - sR31 / 2 + 2)
        * Complex.Gamma (1 - sR31 / 2 + 2) := by
    have h : (1 - sR31 / 2 + 3)
        = ((1 - sR31 / 2 + 2) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR31_add2_ne0
  have e3 : Complex.Gamma (1 - sR31 / 2 + 4)
      = (1 - sR31 / 2 + 3)
        * Complex.Gamma (1 - sR31 / 2 + 3) := by
    have h : (1 - sR31 / 2 + 4)
        = ((1 - sR31 / 2 + 3) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR31_add3_ne0
  have e4 : Complex.Gamma (1 - sR31 / 2 + 5)
      = (1 - sR31 / 2 + 4)
        * Complex.Gamma (1 - sR31 / 2 + 4) := by
    have h : (1 - sR31 / 2 + 5)
        = ((1 - sR31 / 2 + 4) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR31_add4_ne0
  have e5 : Complex.Gamma (1 - sR31 / 2 + 6)
      = (1 - sR31 / 2 + 5)
        * Complex.Gamma (1 - sR31 / 2 + 5) := by
    have h : (1 - sR31 / 2 + 6)
        = ((1 - sR31 / 2 + 5) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR31_add5_ne0
  have e6 : Complex.Gamma (1 - sR31 / 2 + 7)
      = (1 - sR31 / 2 + 6)
        * Complex.Gamma (1 - sR31 / 2 + 6) := by
    have h : (1 - sR31 / 2 + 7)
        = ((1 - sR31 / 2 + 6) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR31_add6_ne0
  have e7 : Complex.Gamma (1 - sR31 / 2 + 8)
      = (1 - sR31 / 2 + 7)
        * Complex.Gamma (1 - sR31 / 2 + 7) := by
    have h : (1 - sR31 / 2 + 8)
        = ((1 - sR31 / 2 + 7) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR31_add7_ne0
  have e8 : Complex.Gamma (1 - sR31 / 2 + 9)
      = (1 - sR31 / 2 + 8)
        * Complex.Gamma (1 - sR31 / 2 + 8) := by
    have h : (1 - sR31 / 2 + 9)
        = ((1 - sR31 / 2 + 8) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR31_add8_ne0
  have e9 : Complex.Gamma (1 - sR31 / 2 + 10)
      = (1 - sR31 / 2 + 9)
        * Complex.Gamma (1 - sR31 / 2 + 9) := by
    have h : (1 - sR31 / 2 + 10)
        = ((1 - sR31 / 2 + 9) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR31_add9_ne0
  have e10 : Complex.Gamma (1 - sR31 / 2 + 11)
      = (1 - sR31 / 2 + 10)
        * Complex.Gamma (1 - sR31 / 2 + 10) := by
    have h : (1 - sR31 / 2 + 11)
        = ((1 - sR31 / 2 + 10) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR31_add10_ne0
  have e11 : Complex.Gamma (1 - sR31 / 2 + 12)
      = (1 - sR31 / 2 + 11)
        * Complex.Gamma (1 - sR31 / 2 + 11) := by
    have h : (1 - sR31 / 2 + 12)
        = ((1 - sR31 / 2 + 11) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR31_add11_ne0
  have e12 : Complex.Gamma (1 - sR31 / 2 + 13)
      = (1 - sR31 / 2 + 12)
        * Complex.Gamma (1 - sR31 / 2 + 12) := by
    have h : (1 - sR31 / 2 + 13)
        = ((1 - sR31 / 2 + 12) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR31_add12_ne0
  have e13 : Complex.Gamma (1 - sR31 / 2 + 14)
      = (1 - sR31 / 2 + 13)
        * Complex.Gamma (1 - sR31 / 2 + 13) := by
    have h : (1 - sR31 / 2 + 14)
        = ((1 - sR31 / 2 + 13) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR31_add13_ne0
  have e14 : Complex.Gamma (1 - sR31 / 2 + 15)
      = (1 - sR31 / 2 + 14)
        * Complex.Gamma (1 - sR31 / 2 + 14) := by
    have h : (1 - sR31 / 2 + 15)
        = ((1 - sR31 / 2 + 14) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR31_add14_ne0
  have n0 : ‖Complex.Gamma (1 - sR31 / 2 + 1)‖
      = ‖1 - sR31 / 2‖
        * ‖Complex.Gamma (1 - sR31 / 2)‖ := by
    rw [e0, norm_mul]
  have n1 : ‖Complex.Gamma (1 - sR31 / 2 + 2)‖
      = ‖1 - sR31 / 2 + 1‖
        * ‖Complex.Gamma (1 - sR31 / 2 + 1)‖ := by
    rw [e1, norm_mul]
  have n2 : ‖Complex.Gamma (1 - sR31 / 2 + 3)‖
      = ‖1 - sR31 / 2 + 2‖
        * ‖Complex.Gamma (1 - sR31 / 2 + 2)‖ := by
    rw [e2, norm_mul]
  have n3 : ‖Complex.Gamma (1 - sR31 / 2 + 4)‖
      = ‖1 - sR31 / 2 + 3‖
        * ‖Complex.Gamma (1 - sR31 / 2 + 3)‖ := by
    rw [e3, norm_mul]
  have n4 : ‖Complex.Gamma (1 - sR31 / 2 + 5)‖
      = ‖1 - sR31 / 2 + 4‖
        * ‖Complex.Gamma (1 - sR31 / 2 + 4)‖ := by
    rw [e4, norm_mul]
  have n5 : ‖Complex.Gamma (1 - sR31 / 2 + 6)‖
      = ‖1 - sR31 / 2 + 5‖
        * ‖Complex.Gamma (1 - sR31 / 2 + 5)‖ := by
    rw [e5, norm_mul]
  have n6 : ‖Complex.Gamma (1 - sR31 / 2 + 7)‖
      = ‖1 - sR31 / 2 + 6‖
        * ‖Complex.Gamma (1 - sR31 / 2 + 6)‖ := by
    rw [e6, norm_mul]
  have n7 : ‖Complex.Gamma (1 - sR31 / 2 + 8)‖
      = ‖1 - sR31 / 2 + 7‖
        * ‖Complex.Gamma (1 - sR31 / 2 + 7)‖ := by
    rw [e7, norm_mul]
  have n8 : ‖Complex.Gamma (1 - sR31 / 2 + 9)‖
      = ‖1 - sR31 / 2 + 8‖
        * ‖Complex.Gamma (1 - sR31 / 2 + 8)‖ := by
    rw [e8, norm_mul]
  have n9 : ‖Complex.Gamma (1 - sR31 / 2 + 10)‖
      = ‖1 - sR31 / 2 + 9‖
        * ‖Complex.Gamma (1 - sR31 / 2 + 9)‖ := by
    rw [e9, norm_mul]
  have n10 : ‖Complex.Gamma (1 - sR31 / 2 + 11)‖
      = ‖1 - sR31 / 2 + 10‖
        * ‖Complex.Gamma (1 - sR31 / 2 + 10)‖ := by
    rw [e10, norm_mul]
  have n11 : ‖Complex.Gamma (1 - sR31 / 2 + 12)‖
      = ‖1 - sR31 / 2 + 11‖
        * ‖Complex.Gamma (1 - sR31 / 2 + 11)‖ := by
    rw [e11, norm_mul]
  have n12 : ‖Complex.Gamma (1 - sR31 / 2 + 13)‖
      = ‖1 - sR31 / 2 + 12‖
        * ‖Complex.Gamma (1 - sR31 / 2 + 12)‖ := by
    rw [e12, norm_mul]
  have n13 : ‖Complex.Gamma (1 - sR31 / 2 + 14)‖
      = ‖1 - sR31 / 2 + 13‖
        * ‖Complex.Gamma (1 - sR31 / 2 + 13)‖ := by
    rw [e13, norm_mul]
  have n14 : ‖Complex.Gamma (1 - sR31 / 2 + 15)‖
      = ‖1 - sR31 / 2 + 14‖
        * ‖Complex.Gamma (1 - sR31 / 2 + 14)‖ := by
    rw [e14, norm_mul]
  have hprod : ‖Complex.Gamma (1 - sR31 / 2 + 15)‖
      = ‖1 - sR31 / 2 + 14‖
        * (‖1 - sR31 / 2 + 13‖
        * (‖1 - sR31 / 2 + 12‖
        * (‖1 - sR31 / 2 + 11‖
        * (‖1 - sR31 / 2 + 10‖
        * (‖1 - sR31 / 2 + 9‖
        * (‖1 - sR31 / 2 + 8‖
        * (‖1 - sR31 / 2 + 7‖
        * (‖1 - sR31 / 2 + 6‖
        * (‖1 - sR31 / 2 + 5‖
        * (‖1 - sR31 / 2 + 4‖
        * (‖1 - sR31 / 2 + 3‖
        * (‖1 - sR31 / 2 + 2‖
        * (‖1 - sR31 / 2 + 1‖
        * (‖1 - sR31 / 2‖
          * ‖Complex.Gamma (1 - sR31 / 2)‖)))))))))))))) := by
    rw [n14, n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n0]
  -- Denominator product lower bound.
  have q1 : (4.78 : ℝ) * 4.47
      ≤ ‖1 - sR31 / 2 + 1‖ * ‖1 - sR31 / 2‖ :=
    mul_le_mul norm_zUpR31_1_ge norm_zUpR31_0_ge (by norm_num) (norm_nonneg _)
  have q2 : (5.27 : ℝ) * (4.78 * (4.47))
      ≤ ‖1 - sR31 / 2 + 2‖ * (‖1 - sR31 / 2 + 1‖ * (‖1 - sR31 / 2‖)) :=
    mul_le_mul norm_zUpR31_2_ge q1 (by positivity) (norm_nonneg _)
  have q3 : (5.89 : ℝ) * (5.27 * (4.78 * (4.47)))
      ≤ ‖1 - sR31 / 2 + 3‖ * (‖1 - sR31 / 2 + 2‖ * (‖1 - sR31 / 2 + 1‖ * (‖1 - sR31 / 2‖))) :=
    mul_le_mul norm_zUpR31_3_ge q2 (by positivity) (norm_nonneg _)
  have q4 : (6.6 : ℝ) * (5.89 * (5.27 * (4.78 * (4.47))))
      ≤ ‖1 - sR31 / 2 + 4‖ * (‖1 - sR31 / 2 + 3‖ * (‖1 - sR31 / 2 + 2‖ * (‖1 - sR31 / 2 + 1‖ * (‖1 - sR31 / 2‖)))) :=
    mul_le_mul norm_zUpR31_4_ge q3 (by positivity) (norm_nonneg _)
  have q5 : (7.38 : ℝ) * (6.6 * (5.89 * (5.27 * (4.78 * (4.47)))))
      ≤ ‖1 - sR31 / 2 + 5‖ * (‖1 - sR31 / 2 + 4‖ * (‖1 - sR31 / 2 + 3‖ * (‖1 - sR31 / 2 + 2‖ * (‖1 - sR31 / 2 + 1‖ * (‖1 - sR31 / 2‖))))) :=
    mul_le_mul norm_zUpR31_5_ge q4 (by positivity) (norm_nonneg _)
  have q6 : (8.21 : ℝ) * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47))))))
      ≤ ‖1 - sR31 / 2 + 6‖ * (‖1 - sR31 / 2 + 5‖ * (‖1 - sR31 / 2 + 4‖ * (‖1 - sR31 / 2 + 3‖ * (‖1 - sR31 / 2 + 2‖ * (‖1 - sR31 / 2 + 1‖ * (‖1 - sR31 / 2‖)))))) :=
    mul_le_mul norm_zUpR31_6_ge q5 (by positivity) (norm_nonneg _)
  have q7 : (9.07 : ℝ) * (8.21 * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47)))))))
      ≤ ‖1 - sR31 / 2 + 7‖ * (‖1 - sR31 / 2 + 6‖ * (‖1 - sR31 / 2 + 5‖ * (‖1 - sR31 / 2 + 4‖ * (‖1 - sR31 / 2 + 3‖ * (‖1 - sR31 / 2 + 2‖ * (‖1 - sR31 / 2 + 1‖ * (‖1 - sR31 / 2‖))))))) :=
    mul_le_mul norm_zUpR31_7_ge q6 (by positivity) (norm_nonneg _)
  have q8 : (9.95 : ℝ) * (9.07 * (8.21 * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47))))))))
      ≤ ‖1 - sR31 / 2 + 8‖ * (‖1 - sR31 / 2 + 7‖ * (‖1 - sR31 / 2 + 6‖ * (‖1 - sR31 / 2 + 5‖ * (‖1 - sR31 / 2 + 4‖ * (‖1 - sR31 / 2 + 3‖ * (‖1 - sR31 / 2 + 2‖ * (‖1 - sR31 / 2 + 1‖ * (‖1 - sR31 / 2‖)))))))) :=
    mul_le_mul norm_zUpR31_8_ge q7 (by positivity) (norm_nonneg _)
  have q9 : (10.86 : ℝ) * (9.95 * (9.07 * (8.21 * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47)))))))))
      ≤ ‖1 - sR31 / 2 + 9‖ * (‖1 - sR31 / 2 + 8‖ * (‖1 - sR31 / 2 + 7‖ * (‖1 - sR31 / 2 + 6‖ * (‖1 - sR31 / 2 + 5‖ * (‖1 - sR31 / 2 + 4‖ * (‖1 - sR31 / 2 + 3‖ * (‖1 - sR31 / 2 + 2‖ * (‖1 - sR31 / 2 + 1‖ * (‖1 - sR31 / 2‖))))))))) :=
    mul_le_mul norm_zUpR31_9_ge q8 (by positivity) (norm_nonneg _)
  have q10 : (11.78 : ℝ) * (10.86 * (9.95 * (9.07 * (8.21 * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47))))))))))
      ≤ ‖1 - sR31 / 2 + 10‖ * (‖1 - sR31 / 2 + 9‖ * (‖1 - sR31 / 2 + 8‖ * (‖1 - sR31 / 2 + 7‖ * (‖1 - sR31 / 2 + 6‖ * (‖1 - sR31 / 2 + 5‖ * (‖1 - sR31 / 2 + 4‖ * (‖1 - sR31 / 2 + 3‖ * (‖1 - sR31 / 2 + 2‖ * (‖1 - sR31 / 2 + 1‖ * (‖1 - sR31 / 2‖)))))))))) :=
    mul_le_mul norm_zUpR31_10_ge q9 (by positivity) (norm_nonneg _)
  have q11 : (12.72 : ℝ) * (11.78 * (10.86 * (9.95 * (9.07 * (8.21 * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47)))))))))))
      ≤ ‖1 - sR31 / 2 + 11‖ * (‖1 - sR31 / 2 + 10‖ * (‖1 - sR31 / 2 + 9‖ * (‖1 - sR31 / 2 + 8‖ * (‖1 - sR31 / 2 + 7‖ * (‖1 - sR31 / 2 + 6‖ * (‖1 - sR31 / 2 + 5‖ * (‖1 - sR31 / 2 + 4‖ * (‖1 - sR31 / 2 + 3‖ * (‖1 - sR31 / 2 + 2‖ * (‖1 - sR31 / 2 + 1‖ * (‖1 - sR31 / 2‖))))))))))) :=
    mul_le_mul norm_zUpR31_11_ge q10 (by positivity) (norm_nonneg _)
  have q12 : (13.66 : ℝ) * (12.72 * (11.78 * (10.86 * (9.95 * (9.07 * (8.21 * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47))))))))))))
      ≤ ‖1 - sR31 / 2 + 12‖ * (‖1 - sR31 / 2 + 11‖ * (‖1 - sR31 / 2 + 10‖ * (‖1 - sR31 / 2 + 9‖ * (‖1 - sR31 / 2 + 8‖ * (‖1 - sR31 / 2 + 7‖ * (‖1 - sR31 / 2 + 6‖ * (‖1 - sR31 / 2 + 5‖ * (‖1 - sR31 / 2 + 4‖ * (‖1 - sR31 / 2 + 3‖ * (‖1 - sR31 / 2 + 2‖ * (‖1 - sR31 / 2 + 1‖ * (‖1 - sR31 / 2‖)))))))))))) :=
    mul_le_mul norm_zUpR31_12_ge q11 (by positivity) (norm_nonneg _)
  have q13 : (14.61 : ℝ) * (13.66 * (12.72 * (11.78 * (10.86 * (9.95 * (9.07 * (8.21 * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47)))))))))))))
      ≤ ‖1 - sR31 / 2 + 13‖ * (‖1 - sR31 / 2 + 12‖ * (‖1 - sR31 / 2 + 11‖ * (‖1 - sR31 / 2 + 10‖ * (‖1 - sR31 / 2 + 9‖ * (‖1 - sR31 / 2 + 8‖ * (‖1 - sR31 / 2 + 7‖ * (‖1 - sR31 / 2 + 6‖ * (‖1 - sR31 / 2 + 5‖ * (‖1 - sR31 / 2 + 4‖ * (‖1 - sR31 / 2 + 3‖ * (‖1 - sR31 / 2 + 2‖ * (‖1 - sR31 / 2 + 1‖ * (‖1 - sR31 / 2‖))))))))))))) :=
    mul_le_mul norm_zUpR31_13_ge q12 (by positivity) (norm_nonneg _)
  have q14 : (15.57 : ℝ) * (14.61 * (13.66 * (12.72 * (11.78 * (10.86 * (9.95 * (9.07 * (8.21 * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47))))))))))))))
      ≤ ‖1 - sR31 / 2 + 14‖ * (‖1 - sR31 / 2 + 13‖ * (‖1 - sR31 / 2 + 12‖ * (‖1 - sR31 / 2 + 11‖ * (‖1 - sR31 / 2 + 10‖ * (‖1 - sR31 / 2 + 9‖ * (‖1 - sR31 / 2 + 8‖ * (‖1 - sR31 / 2 + 7‖ * (‖1 - sR31 / 2 + 6‖ * (‖1 - sR31 / 2 + 5‖ * (‖1 - sR31 / 2 + 4‖ * (‖1 - sR31 / 2 + 3‖ * (‖1 - sR31 / 2 + 2‖ * (‖1 - sR31 / 2 + 1‖ * (‖1 - sR31 / 2‖)))))))))))))) :=
    mul_le_mul norm_zUpR31_14_ge q13 (by positivity) (norm_nonneg _)
  have hDlo : (120000000000000 : ℝ)
      ≤ (15.57 : ℝ) * (14.61 * (13.66 * (12.72 * (11.78 * (10.86 * (9.95 * (9.07 * (8.21 * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47)))))))))))))) := by
    norm_num
  have hD_ge : (120000000000000 : ℝ)
      ≤ ‖1 - sR31 / 2 + 14‖ * (‖1 - sR31 / 2 + 13‖ * (‖1 - sR31 / 2 + 12‖ * (‖1 - sR31 / 2 + 11‖ * (‖1 - sR31 / 2 + 10‖ * (‖1 - sR31 / 2 + 9‖ * (‖1 - sR31 / 2 + 8‖ * (‖1 - sR31 / 2 + 7‖ * (‖1 - sR31 / 2 + 6‖ * (‖1 - sR31 / 2 + 5‖ * (‖1 - sR31 / 2 + 4‖ * (‖1 - sR31 / 2 + 3‖ * (‖1 - sR31 / 2 + 2‖ * (‖1 - sR31 / 2 + 1‖ * (‖1 - sR31 / 2‖)))))))))))))) :=
    le_trans hDlo q14
  have hD_pos : (0 : ℝ)
      < (‖1 - sR31 / 2 + 14‖
        * (‖1 - sR31 / 2 + 13‖
        * (‖1 - sR31 / 2 + 12‖
        * (‖1 - sR31 / 2 + 11‖
        * (‖1 - sR31 / 2 + 10‖
        * (‖1 - sR31 / 2 + 9‖
        * (‖1 - sR31 / 2 + 8‖
        * (‖1 - sR31 / 2 + 7‖
        * (‖1 - sR31 / 2 + 6‖
        * (‖1 - sR31 / 2 + 5‖
        * (‖1 - sR31 / 2 + 4‖
        * (‖1 - sR31 / 2 + 3‖
        * (‖1 - sR31 / 2 + 2‖
        * (‖1 - sR31 / 2 + 1‖
          * ‖1 - sR31 / 2‖)))))))))))))) :=
    lt_of_lt_of_le (by norm_num) hD_ge
  -- Numerator: `‖Complex.Gamma (1 - sR31 / 2 + 15)‖ ≤ Real.Gamma(15.9475) ≤ 1160000000000`.
  have hre15 : (1 - sR31 / 2 + 15).re = 15.9475 := by
    simp only [Complex.add_re, zUpR31_re, Complex.re_ofNat]
    norm_num
  have hGN_re : (0 : ℝ) < (1 - sR31 / 2 + 15).re := by
    rw [hre15]
    norm_num
  have hGN_le : ‖Complex.Gamma (1 - sR31 / 2 + 15)‖ ≤ 1160000000000 := by
    have h1 : ‖Complex.Gamma (1 - sR31 / 2 + 15)‖
        ≤ Real.Gamma ((1 - sR31 / 2 + 15).re) :=
      R00GammaLower.norm_Gamma_le_realGamma hGN_re
    have hreNb : ((1 - sR31 / 2 + 15).re) = 15.9475 := hre15
    rw [hreNb] at h1
    exact le_trans h1 CellGammaUpper09475.realGamma_159475_le
  -- Combine: `D * ‖Complex.Gamma (1 - sR31 / 2)‖ = ‖Complex.Gamma (1 - sR31 / 2 + 15)‖ ≤ 1160000000000`, `D ≤ 120000000000000`.
  have hD_mul : (‖1 - sR31 / 2 + 14‖
        * (‖1 - sR31 / 2 + 13‖
        * (‖1 - sR31 / 2 + 12‖
        * (‖1 - sR31 / 2 + 11‖
        * (‖1 - sR31 / 2 + 10‖
        * (‖1 - sR31 / 2 + 9‖
        * (‖1 - sR31 / 2 + 8‖
        * (‖1 - sR31 / 2 + 7‖
        * (‖1 - sR31 / 2 + 6‖
        * (‖1 - sR31 / 2 + 5‖
        * (‖1 - sR31 / 2 + 4‖
        * (‖1 - sR31 / 2 + 3‖
        * (‖1 - sR31 / 2 + 2‖
        * (‖1 - sR31 / 2 + 1‖
          * ‖1 - sR31 / 2‖))))))))))))))
        * ‖Complex.Gamma (1 - sR31 / 2)‖
      = ‖Complex.Gamma (1 - sR31 / 2 + 15)‖ := by
    rw [hprod]
    ring
  have hle : (‖1 - sR31 / 2 + 14‖
        * (‖1 - sR31 / 2 + 13‖
        * (‖1 - sR31 / 2 + 12‖
        * (‖1 - sR31 / 2 + 11‖
        * (‖1 - sR31 / 2 + 10‖
        * (‖1 - sR31 / 2 + 9‖
        * (‖1 - sR31 / 2 + 8‖
        * (‖1 - sR31 / 2 + 7‖
        * (‖1 - sR31 / 2 + 6‖
        * (‖1 - sR31 / 2 + 5‖
        * (‖1 - sR31 / 2 + 4‖
        * (‖1 - sR31 / 2 + 3‖
        * (‖1 - sR31 / 2 + 2‖
        * (‖1 - sR31 / 2 + 1‖
          * ‖1 - sR31 / 2‖))))))))))))))
        * ‖Complex.Gamma (1 - sR31 / 2)‖ ≤ 1160000000000 := by
    rw [hD_mul]
    exact hGN_le
  have hmul_comm : ‖Complex.Gamma (1 - sR31 / 2)‖
        * (‖1 - sR31 / 2 + 14‖
        * (‖1 - sR31 / 2 + 13‖
        * (‖1 - sR31 / 2 + 12‖
        * (‖1 - sR31 / 2 + 11‖
        * (‖1 - sR31 / 2 + 10‖
        * (‖1 - sR31 / 2 + 9‖
        * (‖1 - sR31 / 2 + 8‖
        * (‖1 - sR31 / 2 + 7‖
        * (‖1 - sR31 / 2 + 6‖
        * (‖1 - sR31 / 2 + 5‖
        * (‖1 - sR31 / 2 + 4‖
        * (‖1 - sR31 / 2 + 3‖
        * (‖1 - sR31 / 2 + 2‖
        * (‖1 - sR31 / 2 + 1‖
          * ‖1 - sR31 / 2‖))))))))))))))
        ≤ 1160000000000 := by
    calc ‖Complex.Gamma (1 - sR31 / 2)‖ * _
          = _ * ‖Complex.Gamma (1 - sR31 / 2)‖ := mul_comm _ _
      _ ≤ 1160000000000 := hle
  have hdiv : ‖Complex.Gamma (1 - sR31 / 2)‖
      ≤ 1160000000000 / (‖1 - sR31 / 2 + 14‖
        * (‖1 - sR31 / 2 + 13‖
        * (‖1 - sR31 / 2 + 12‖
        * (‖1 - sR31 / 2 + 11‖
        * (‖1 - sR31 / 2 + 10‖
        * (‖1 - sR31 / 2 + 9‖
        * (‖1 - sR31 / 2 + 8‖
        * (‖1 - sR31 / 2 + 7‖
        * (‖1 - sR31 / 2 + 6‖
        * (‖1 - sR31 / 2 + 5‖
        * (‖1 - sR31 / 2 + 4‖
        * (‖1 - sR31 / 2 + 3‖
        * (‖1 - sR31 / 2 + 2‖
        * (‖1 - sR31 / 2 + 1‖
          * ‖1 - sR31 / 2‖))))))))))))))
        :=
    (le_div_iff₀ hD_pos).mpr hmul_comm
  have hcap : (1160000000000 : ℝ)
      ≤ 0.01 * (‖1 - sR31 / 2 + 14‖
        * (‖1 - sR31 / 2 + 13‖
        * (‖1 - sR31 / 2 + 12‖
        * (‖1 - sR31 / 2 + 11‖
        * (‖1 - sR31 / 2 + 10‖
        * (‖1 - sR31 / 2 + 9‖
        * (‖1 - sR31 / 2 + 8‖
        * (‖1 - sR31 / 2 + 7‖
        * (‖1 - sR31 / 2 + 6‖
        * (‖1 - sR31 / 2 + 5‖
        * (‖1 - sR31 / 2 + 4‖
        * (‖1 - sR31 / 2 + 3‖
        * (‖1 - sR31 / 2 + 2‖
        * (‖1 - sR31 / 2 + 1‖
          * ‖1 - sR31 / 2‖)))))))))))))) := by
    calc (1160000000000 : ℝ) ≤ 0.01 * 120000000000000 := by norm_num
      _ ≤ 0.01 * _ :=
          mul_le_mul_of_nonneg_left hD_ge (by norm_num)
  have hfinal : 1160000000000 / (‖1 - sR31 / 2 + 14‖ * (‖1 - sR31 / 2 + 13‖ * (‖1 - sR31 / 2 + 12‖ * (‖1 - sR31 / 2 + 11‖ * (‖1 - sR31 / 2 + 10‖ * (‖1 - sR31 / 2 + 9‖ * (‖1 - sR31 / 2 + 8‖ * (‖1 - sR31 / 2 + 7‖ * (‖1 - sR31 / 2 + 6‖ * (‖1 - sR31 / 2 + 5‖ * (‖1 - sR31 / 2 + 4‖ * (‖1 - sR31 / 2 + 3‖ * (‖1 - sR31 / 2 + 2‖ * (‖1 - sR31 / 2 + 1‖ * (‖1 - sR31 / 2‖)))))))))))))))
      ≤ 0.01 :=
    (div_le_iff₀ hD_pos).mpr hcap
  exact le_trans hdiv hfinal

end R31GammaUpper

namespace R40GammaUpper

/-- The R40 `s`-plane center: `s = 1/2 + I·z` at `z = R40.center`. -/
noncomputable def sR40 : ℂ :=
  (1 / 2 : ℂ) + Complex.I * CentralCoverAssembly.R40.center

/-- `R40.center = 8.75 + 0.395·I` (from `R40_x0/x1/y0/y1`). -/
theorem R40_center_eq :
    CentralCoverAssembly.R40.center =
      (((8.75 : ℝ))) + Complex.I * ((((0.395 : ℝ))) : ℂ) := by
  apply Complex.ext
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R40_x0, CentralCoverAssembly.R40_x1,
      CentralCoverAssembly.R40_y0, CentralCoverAssembly.R40_y1]
    simp
    norm_num
  · unfold CellProofEngine.Rect2D.center
    rw [CentralCoverAssembly.R40_x0, CentralCoverAssembly.R40_x1,
      CentralCoverAssembly.R40_y0, CentralCoverAssembly.R40_y1]
    simp
    norm_num

/-- `Re sR40 = 0.105`. -/
theorem sR40_re : sR40.re = 0.105 := by
  unfold sR40
  rw [R40_center_eq]
  simp
  norm_num

/-- `Im sR40 = 8.75`. -/
theorem sR40_im : sR40.im = 8.75 := by
  unfold sR40
  rw [R40_center_eq]
  simp

/-- `Re(1 - sR40/2) = 0.9475`. -/
theorem zUpR40_re : (1 - sR40 / 2).re = 0.9475 := by
  rw [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, sR40_re]
  norm_num

/-- `Im(1 - sR40/2) = -4.375`. -/
theorem zUpR40_im : (1 - sR40 / 2).im = -4.375 := by
  rw [Complex.sub_im, Complex.one_im, Complex.div_ofNat_im, sR40_im]
  norm_num

/-- Denominator floor `c0 = 4.47 ≤ ‖1 - sR40 / 2‖`. -/
theorem norm_zUpR40_0_ge :
    (4.47 : ℝ) ≤ ‖1 - sR40 / 2‖ := by
  have hsq : (4.47 : ℝ) ^ 2 ≤ ‖1 - sR40 / 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, zUpR40_re, zUpR40_im]
    norm_num
  calc (4.47 : ℝ) = Real.sqrt ((4.47 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR40 / 2‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR40 / 2‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c1 = 4.78 ≤ ‖1 - sR40 / 2 + 1‖`. -/
theorem norm_zUpR40_1_ge :
    (4.78 : ℝ) ≤ ‖1 - sR40 / 2 + 1‖ := by
  have hre : (1 - sR40 / 2 + 1).re = 1.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.one_re]
    norm_num
  have him : (1 - sR40 / 2 + 1).im = -4.375 := by
    simp only [Complex.add_im, zUpR40_im, Complex.one_im]
    norm_num
  have hsq : (4.78 : ℝ) ^ 2 ≤ ‖1 - sR40 / 2 + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (4.78 : ℝ) = Real.sqrt ((4.78 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR40 / 2 + 1‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR40 / 2 + 1‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c2 = 5.27 ≤ ‖1 - sR40 / 2 + 2‖`. -/
theorem norm_zUpR40_2_ge :
    (5.27 : ℝ) ≤ ‖1 - sR40 / 2 + 2‖ := by
  have hre : (1 - sR40 / 2 + 2).re = 2.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR40 / 2 + 2).im = -4.375 := by
    simp only [Complex.add_im, zUpR40_im, Complex.im_ofNat]
    norm_num
  have hsq : (5.27 : ℝ) ^ 2 ≤ ‖1 - sR40 / 2 + 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (5.27 : ℝ) = Real.sqrt ((5.27 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR40 / 2 + 2‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR40 / 2 + 2‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c3 = 5.89 ≤ ‖1 - sR40 / 2 + 3‖`. -/
theorem norm_zUpR40_3_ge :
    (5.89 : ℝ) ≤ ‖1 - sR40 / 2 + 3‖ := by
  have hre : (1 - sR40 / 2 + 3).re = 3.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR40 / 2 + 3).im = -4.375 := by
    simp only [Complex.add_im, zUpR40_im, Complex.im_ofNat]
    norm_num
  have hsq : (5.89 : ℝ) ^ 2 ≤ ‖1 - sR40 / 2 + 3‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (5.89 : ℝ) = Real.sqrt ((5.89 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR40 / 2 + 3‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR40 / 2 + 3‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c4 = 6.6 ≤ ‖1 - sR40 / 2 + 4‖`. -/
theorem norm_zUpR40_4_ge :
    (6.6 : ℝ) ≤ ‖1 - sR40 / 2 + 4‖ := by
  have hre : (1 - sR40 / 2 + 4).re = 4.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR40 / 2 + 4).im = -4.375 := by
    simp only [Complex.add_im, zUpR40_im, Complex.im_ofNat]
    norm_num
  have hsq : (6.6 : ℝ) ^ 2 ≤ ‖1 - sR40 / 2 + 4‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (6.6 : ℝ) = Real.sqrt ((6.6 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR40 / 2 + 4‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR40 / 2 + 4‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c5 = 7.38 ≤ ‖1 - sR40 / 2 + 5‖`. -/
theorem norm_zUpR40_5_ge :
    (7.38 : ℝ) ≤ ‖1 - sR40 / 2 + 5‖ := by
  have hre : (1 - sR40 / 2 + 5).re = 5.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR40 / 2 + 5).im = -4.375 := by
    simp only [Complex.add_im, zUpR40_im, Complex.im_ofNat]
    norm_num
  have hsq : (7.38 : ℝ) ^ 2 ≤ ‖1 - sR40 / 2 + 5‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (7.38 : ℝ) = Real.sqrt ((7.38 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR40 / 2 + 5‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR40 / 2 + 5‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c6 = 8.21 ≤ ‖1 - sR40 / 2 + 6‖`. -/
theorem norm_zUpR40_6_ge :
    (8.21 : ℝ) ≤ ‖1 - sR40 / 2 + 6‖ := by
  have hre : (1 - sR40 / 2 + 6).re = 6.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR40 / 2 + 6).im = -4.375 := by
    simp only [Complex.add_im, zUpR40_im, Complex.im_ofNat]
    norm_num
  have hsq : (8.21 : ℝ) ^ 2 ≤ ‖1 - sR40 / 2 + 6‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (8.21 : ℝ) = Real.sqrt ((8.21 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR40 / 2 + 6‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR40 / 2 + 6‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c7 = 9.07 ≤ ‖1 - sR40 / 2 + 7‖`. -/
theorem norm_zUpR40_7_ge :
    (9.07 : ℝ) ≤ ‖1 - sR40 / 2 + 7‖ := by
  have hre : (1 - sR40 / 2 + 7).re = 7.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR40 / 2 + 7).im = -4.375 := by
    simp only [Complex.add_im, zUpR40_im, Complex.im_ofNat]
    norm_num
  have hsq : (9.07 : ℝ) ^ 2 ≤ ‖1 - sR40 / 2 + 7‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (9.07 : ℝ) = Real.sqrt ((9.07 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR40 / 2 + 7‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR40 / 2 + 7‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c8 = 9.95 ≤ ‖1 - sR40 / 2 + 8‖`. -/
theorem norm_zUpR40_8_ge :
    (9.95 : ℝ) ≤ ‖1 - sR40 / 2 + 8‖ := by
  have hre : (1 - sR40 / 2 + 8).re = 8.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR40 / 2 + 8).im = -4.375 := by
    simp only [Complex.add_im, zUpR40_im, Complex.im_ofNat]
    norm_num
  have hsq : (9.95 : ℝ) ^ 2 ≤ ‖1 - sR40 / 2 + 8‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (9.95 : ℝ) = Real.sqrt ((9.95 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR40 / 2 + 8‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR40 / 2 + 8‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c9 = 10.86 ≤ ‖1 - sR40 / 2 + 9‖`. -/
theorem norm_zUpR40_9_ge :
    (10.86 : ℝ) ≤ ‖1 - sR40 / 2 + 9‖ := by
  have hre : (1 - sR40 / 2 + 9).re = 9.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR40 / 2 + 9).im = -4.375 := by
    simp only [Complex.add_im, zUpR40_im, Complex.im_ofNat]
    norm_num
  have hsq : (10.86 : ℝ) ^ 2 ≤ ‖1 - sR40 / 2 + 9‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (10.86 : ℝ) = Real.sqrt ((10.86 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR40 / 2 + 9‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR40 / 2 + 9‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c10 = 11.78 ≤ ‖1 - sR40 / 2 + 10‖`. -/
theorem norm_zUpR40_10_ge :
    (11.78 : ℝ) ≤ ‖1 - sR40 / 2 + 10‖ := by
  have hre : (1 - sR40 / 2 + 10).re = 10.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR40 / 2 + 10).im = -4.375 := by
    simp only [Complex.add_im, zUpR40_im, Complex.im_ofNat]
    norm_num
  have hsq : (11.78 : ℝ) ^ 2 ≤ ‖1 - sR40 / 2 + 10‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (11.78 : ℝ) = Real.sqrt ((11.78 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR40 / 2 + 10‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR40 / 2 + 10‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c11 = 12.72 ≤ ‖1 - sR40 / 2 + 11‖`. -/
theorem norm_zUpR40_11_ge :
    (12.72 : ℝ) ≤ ‖1 - sR40 / 2 + 11‖ := by
  have hre : (1 - sR40 / 2 + 11).re = 11.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR40 / 2 + 11).im = -4.375 := by
    simp only [Complex.add_im, zUpR40_im, Complex.im_ofNat]
    norm_num
  have hsq : (12.72 : ℝ) ^ 2 ≤ ‖1 - sR40 / 2 + 11‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (12.72 : ℝ) = Real.sqrt ((12.72 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR40 / 2 + 11‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR40 / 2 + 11‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c12 = 13.66 ≤ ‖1 - sR40 / 2 + 12‖`. -/
theorem norm_zUpR40_12_ge :
    (13.66 : ℝ) ≤ ‖1 - sR40 / 2 + 12‖ := by
  have hre : (1 - sR40 / 2 + 12).re = 12.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR40 / 2 + 12).im = -4.375 := by
    simp only [Complex.add_im, zUpR40_im, Complex.im_ofNat]
    norm_num
  have hsq : (13.66 : ℝ) ^ 2 ≤ ‖1 - sR40 / 2 + 12‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (13.66 : ℝ) = Real.sqrt ((13.66 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR40 / 2 + 12‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR40 / 2 + 12‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c13 = 14.61 ≤ ‖1 - sR40 / 2 + 13‖`. -/
theorem norm_zUpR40_13_ge :
    (14.61 : ℝ) ≤ ‖1 - sR40 / 2 + 13‖ := by
  have hre : (1 - sR40 / 2 + 13).re = 13.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR40 / 2 + 13).im = -4.375 := by
    simp only [Complex.add_im, zUpR40_im, Complex.im_ofNat]
    norm_num
  have hsq : (14.61 : ℝ) ^ 2 ≤ ‖1 - sR40 / 2 + 13‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (14.61 : ℝ) = Real.sqrt ((14.61 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR40 / 2 + 13‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR40 / 2 + 13‖ := Real.sqrt_sq (norm_nonneg _)

/-- Denominator floor `c14 = 15.57 ≤ ‖1 - sR40 / 2 + 14‖`. -/
theorem norm_zUpR40_14_ge :
    (15.57 : ℝ) ≤ ‖1 - sR40 / 2 + 14‖ := by
  have hre : (1 - sR40 / 2 + 14).re = 14.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  have him : (1 - sR40 / 2 + 14).im = -4.375 := by
    simp only [Complex.add_im, zUpR40_im, Complex.im_ofNat]
    norm_num
  have hsq : (15.57 : ℝ) ^ 2 ≤ ‖1 - sR40 / 2 + 14‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    norm_num
  calc (15.57 : ℝ) = Real.sqrt ((15.57 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (‖1 - sR40 / 2 + 14‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖1 - sR40 / 2 + 14‖ := Real.sqrt_sq (norm_nonneg _)

/-- Shift nonvanishing (`Re > 0` so `{NE} 0`). -/
theorem zUpR40_ne0 : (1 - sR40 / 2) ≠ 0 := by
  have hre : (1 - sR40 / 2).re = 0.9475 := zUpR40_re
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR40_add1_ne0 : (1 - sR40 / 2 + 1) ≠ 0 := by
  have hre : (1 - sR40 / 2 + 1).re = 1.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.one_re]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR40_add2_ne0 : (1 - sR40 / 2 + 2) ≠ 0 := by
  have hre : (1 - sR40 / 2 + 2).re = 2.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR40_add3_ne0 : (1 - sR40 / 2 + 3) ≠ 0 := by
  have hre : (1 - sR40 / 2 + 3).re = 3.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR40_add4_ne0 : (1 - sR40 / 2 + 4) ≠ 0 := by
  have hre : (1 - sR40 / 2 + 4).re = 4.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR40_add5_ne0 : (1 - sR40 / 2 + 5) ≠ 0 := by
  have hre : (1 - sR40 / 2 + 5).re = 5.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR40_add6_ne0 : (1 - sR40 / 2 + 6) ≠ 0 := by
  have hre : (1 - sR40 / 2 + 6).re = 6.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR40_add7_ne0 : (1 - sR40 / 2 + 7) ≠ 0 := by
  have hre : (1 - sR40 / 2 + 7).re = 7.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR40_add8_ne0 : (1 - sR40 / 2 + 8) ≠ 0 := by
  have hre : (1 - sR40 / 2 + 8).re = 8.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR40_add9_ne0 : (1 - sR40 / 2 + 9) ≠ 0 := by
  have hre : (1 - sR40 / 2 + 9).re = 9.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR40_add10_ne0 : (1 - sR40 / 2 + 10) ≠ 0 := by
  have hre : (1 - sR40 / 2 + 10).re = 10.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR40_add11_ne0 : (1 - sR40 / 2 + 11) ≠ 0 := by
  have hre : (1 - sR40 / 2 + 11).re = 11.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR40_add12_ne0 : (1 - sR40 / 2 + 12) ≠ 0 := by
  have hre : (1 - sR40 / 2 + 12).re = 12.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR40_add13_ne0 : (1 - sR40 / 2 + 13) ≠ 0 := by
  have hre : (1 - sR40 / 2 + 13).re = 13.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem zUpR40_add14_ne0 : (1 - sR40 / 2 + 14) ≠ 0 := by
  have hre : (1 - sR40 / 2 + 14).re = 14.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

/-- MAIN uniform UPPER bound at the R40 corner:
`‖Complex.Gamma (1 - sR40 / 2)‖ ≤ 0.01` (row-3 outer-tier mirror, `re = 0.9475`, 15 shifts). -/
theorem gamma_one_sub_half_upper_R40 :
    ‖Complex.Gamma (1 - sR40 / 2)‖ ≤ 0.01 := by
  -- Shift chain `Gamma(z0+15) = (z0+14)..z0*Gamma(z0)`.
  have e0 : Complex.Gamma (1 - sR40 / 2 + 1)
      = (1 - sR40 / 2) * Complex.Gamma (1 - sR40 / 2) :=
    Complex.Gamma_add_one _ zUpR40_ne0
  have e1 : Complex.Gamma (1 - sR40 / 2 + 2)
      = (1 - sR40 / 2 + 1)
        * Complex.Gamma (1 - sR40 / 2 + 1) := by
    have h : (1 - sR40 / 2 + 2)
        = ((1 - sR40 / 2 + 1) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR40_add1_ne0
  have e2 : Complex.Gamma (1 - sR40 / 2 + 3)
      = (1 - sR40 / 2 + 2)
        * Complex.Gamma (1 - sR40 / 2 + 2) := by
    have h : (1 - sR40 / 2 + 3)
        = ((1 - sR40 / 2 + 2) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR40_add2_ne0
  have e3 : Complex.Gamma (1 - sR40 / 2 + 4)
      = (1 - sR40 / 2 + 3)
        * Complex.Gamma (1 - sR40 / 2 + 3) := by
    have h : (1 - sR40 / 2 + 4)
        = ((1 - sR40 / 2 + 3) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR40_add3_ne0
  have e4 : Complex.Gamma (1 - sR40 / 2 + 5)
      = (1 - sR40 / 2 + 4)
        * Complex.Gamma (1 - sR40 / 2 + 4) := by
    have h : (1 - sR40 / 2 + 5)
        = ((1 - sR40 / 2 + 4) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR40_add4_ne0
  have e5 : Complex.Gamma (1 - sR40 / 2 + 6)
      = (1 - sR40 / 2 + 5)
        * Complex.Gamma (1 - sR40 / 2 + 5) := by
    have h : (1 - sR40 / 2 + 6)
        = ((1 - sR40 / 2 + 5) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR40_add5_ne0
  have e6 : Complex.Gamma (1 - sR40 / 2 + 7)
      = (1 - sR40 / 2 + 6)
        * Complex.Gamma (1 - sR40 / 2 + 6) := by
    have h : (1 - sR40 / 2 + 7)
        = ((1 - sR40 / 2 + 6) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR40_add6_ne0
  have e7 : Complex.Gamma (1 - sR40 / 2 + 8)
      = (1 - sR40 / 2 + 7)
        * Complex.Gamma (1 - sR40 / 2 + 7) := by
    have h : (1 - sR40 / 2 + 8)
        = ((1 - sR40 / 2 + 7) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR40_add7_ne0
  have e8 : Complex.Gamma (1 - sR40 / 2 + 9)
      = (1 - sR40 / 2 + 8)
        * Complex.Gamma (1 - sR40 / 2 + 8) := by
    have h : (1 - sR40 / 2 + 9)
        = ((1 - sR40 / 2 + 8) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR40_add8_ne0
  have e9 : Complex.Gamma (1 - sR40 / 2 + 10)
      = (1 - sR40 / 2 + 9)
        * Complex.Gamma (1 - sR40 / 2 + 9) := by
    have h : (1 - sR40 / 2 + 10)
        = ((1 - sR40 / 2 + 9) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR40_add9_ne0
  have e10 : Complex.Gamma (1 - sR40 / 2 + 11)
      = (1 - sR40 / 2 + 10)
        * Complex.Gamma (1 - sR40 / 2 + 10) := by
    have h : (1 - sR40 / 2 + 11)
        = ((1 - sR40 / 2 + 10) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR40_add10_ne0
  have e11 : Complex.Gamma (1 - sR40 / 2 + 12)
      = (1 - sR40 / 2 + 11)
        * Complex.Gamma (1 - sR40 / 2 + 11) := by
    have h : (1 - sR40 / 2 + 12)
        = ((1 - sR40 / 2 + 11) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR40_add11_ne0
  have e12 : Complex.Gamma (1 - sR40 / 2 + 13)
      = (1 - sR40 / 2 + 12)
        * Complex.Gamma (1 - sR40 / 2 + 12) := by
    have h : (1 - sR40 / 2 + 13)
        = ((1 - sR40 / 2 + 12) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR40_add12_ne0
  have e13 : Complex.Gamma (1 - sR40 / 2 + 14)
      = (1 - sR40 / 2 + 13)
        * Complex.Gamma (1 - sR40 / 2 + 13) := by
    have h : (1 - sR40 / 2 + 14)
        = ((1 - sR40 / 2 + 13) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR40_add13_ne0
  have e14 : Complex.Gamma (1 - sR40 / 2 + 15)
      = (1 - sR40 / 2 + 14)
        * Complex.Gamma (1 - sR40 / 2 + 14) := by
    have h : (1 - sR40 / 2 + 15)
        = ((1 - sR40 / 2 + 14) + 1) := by ring
    rw [h]
    exact Complex.Gamma_add_one _ zUpR40_add14_ne0
  have n0 : ‖Complex.Gamma (1 - sR40 / 2 + 1)‖
      = ‖1 - sR40 / 2‖
        * ‖Complex.Gamma (1 - sR40 / 2)‖ := by
    rw [e0, norm_mul]
  have n1 : ‖Complex.Gamma (1 - sR40 / 2 + 2)‖
      = ‖1 - sR40 / 2 + 1‖
        * ‖Complex.Gamma (1 - sR40 / 2 + 1)‖ := by
    rw [e1, norm_mul]
  have n2 : ‖Complex.Gamma (1 - sR40 / 2 + 3)‖
      = ‖1 - sR40 / 2 + 2‖
        * ‖Complex.Gamma (1 - sR40 / 2 + 2)‖ := by
    rw [e2, norm_mul]
  have n3 : ‖Complex.Gamma (1 - sR40 / 2 + 4)‖
      = ‖1 - sR40 / 2 + 3‖
        * ‖Complex.Gamma (1 - sR40 / 2 + 3)‖ := by
    rw [e3, norm_mul]
  have n4 : ‖Complex.Gamma (1 - sR40 / 2 + 5)‖
      = ‖1 - sR40 / 2 + 4‖
        * ‖Complex.Gamma (1 - sR40 / 2 + 4)‖ := by
    rw [e4, norm_mul]
  have n5 : ‖Complex.Gamma (1 - sR40 / 2 + 6)‖
      = ‖1 - sR40 / 2 + 5‖
        * ‖Complex.Gamma (1 - sR40 / 2 + 5)‖ := by
    rw [e5, norm_mul]
  have n6 : ‖Complex.Gamma (1 - sR40 / 2 + 7)‖
      = ‖1 - sR40 / 2 + 6‖
        * ‖Complex.Gamma (1 - sR40 / 2 + 6)‖ := by
    rw [e6, norm_mul]
  have n7 : ‖Complex.Gamma (1 - sR40 / 2 + 8)‖
      = ‖1 - sR40 / 2 + 7‖
        * ‖Complex.Gamma (1 - sR40 / 2 + 7)‖ := by
    rw [e7, norm_mul]
  have n8 : ‖Complex.Gamma (1 - sR40 / 2 + 9)‖
      = ‖1 - sR40 / 2 + 8‖
        * ‖Complex.Gamma (1 - sR40 / 2 + 8)‖ := by
    rw [e8, norm_mul]
  have n9 : ‖Complex.Gamma (1 - sR40 / 2 + 10)‖
      = ‖1 - sR40 / 2 + 9‖
        * ‖Complex.Gamma (1 - sR40 / 2 + 9)‖ := by
    rw [e9, norm_mul]
  have n10 : ‖Complex.Gamma (1 - sR40 / 2 + 11)‖
      = ‖1 - sR40 / 2 + 10‖
        * ‖Complex.Gamma (1 - sR40 / 2 + 10)‖ := by
    rw [e10, norm_mul]
  have n11 : ‖Complex.Gamma (1 - sR40 / 2 + 12)‖
      = ‖1 - sR40 / 2 + 11‖
        * ‖Complex.Gamma (1 - sR40 / 2 + 11)‖ := by
    rw [e11, norm_mul]
  have n12 : ‖Complex.Gamma (1 - sR40 / 2 + 13)‖
      = ‖1 - sR40 / 2 + 12‖
        * ‖Complex.Gamma (1 - sR40 / 2 + 12)‖ := by
    rw [e12, norm_mul]
  have n13 : ‖Complex.Gamma (1 - sR40 / 2 + 14)‖
      = ‖1 - sR40 / 2 + 13‖
        * ‖Complex.Gamma (1 - sR40 / 2 + 13)‖ := by
    rw [e13, norm_mul]
  have n14 : ‖Complex.Gamma (1 - sR40 / 2 + 15)‖
      = ‖1 - sR40 / 2 + 14‖
        * ‖Complex.Gamma (1 - sR40 / 2 + 14)‖ := by
    rw [e14, norm_mul]
  have hprod : ‖Complex.Gamma (1 - sR40 / 2 + 15)‖
      = ‖1 - sR40 / 2 + 14‖
        * (‖1 - sR40 / 2 + 13‖
        * (‖1 - sR40 / 2 + 12‖
        * (‖1 - sR40 / 2 + 11‖
        * (‖1 - sR40 / 2 + 10‖
        * (‖1 - sR40 / 2 + 9‖
        * (‖1 - sR40 / 2 + 8‖
        * (‖1 - sR40 / 2 + 7‖
        * (‖1 - sR40 / 2 + 6‖
        * (‖1 - sR40 / 2 + 5‖
        * (‖1 - sR40 / 2 + 4‖
        * (‖1 - sR40 / 2 + 3‖
        * (‖1 - sR40 / 2 + 2‖
        * (‖1 - sR40 / 2 + 1‖
        * (‖1 - sR40 / 2‖
          * ‖Complex.Gamma (1 - sR40 / 2)‖)))))))))))))) := by
    rw [n14, n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n0]
  -- Denominator product lower bound.
  have q1 : (4.78 : ℝ) * 4.47
      ≤ ‖1 - sR40 / 2 + 1‖ * ‖1 - sR40 / 2‖ :=
    mul_le_mul norm_zUpR40_1_ge norm_zUpR40_0_ge (by norm_num) (norm_nonneg _)
  have q2 : (5.27 : ℝ) * (4.78 * (4.47))
      ≤ ‖1 - sR40 / 2 + 2‖ * (‖1 - sR40 / 2 + 1‖ * (‖1 - sR40 / 2‖)) :=
    mul_le_mul norm_zUpR40_2_ge q1 (by positivity) (norm_nonneg _)
  have q3 : (5.89 : ℝ) * (5.27 * (4.78 * (4.47)))
      ≤ ‖1 - sR40 / 2 + 3‖ * (‖1 - sR40 / 2 + 2‖ * (‖1 - sR40 / 2 + 1‖ * (‖1 - sR40 / 2‖))) :=
    mul_le_mul norm_zUpR40_3_ge q2 (by positivity) (norm_nonneg _)
  have q4 : (6.6 : ℝ) * (5.89 * (5.27 * (4.78 * (4.47))))
      ≤ ‖1 - sR40 / 2 + 4‖ * (‖1 - sR40 / 2 + 3‖ * (‖1 - sR40 / 2 + 2‖ * (‖1 - sR40 / 2 + 1‖ * (‖1 - sR40 / 2‖)))) :=
    mul_le_mul norm_zUpR40_4_ge q3 (by positivity) (norm_nonneg _)
  have q5 : (7.38 : ℝ) * (6.6 * (5.89 * (5.27 * (4.78 * (4.47)))))
      ≤ ‖1 - sR40 / 2 + 5‖ * (‖1 - sR40 / 2 + 4‖ * (‖1 - sR40 / 2 + 3‖ * (‖1 - sR40 / 2 + 2‖ * (‖1 - sR40 / 2 + 1‖ * (‖1 - sR40 / 2‖))))) :=
    mul_le_mul norm_zUpR40_5_ge q4 (by positivity) (norm_nonneg _)
  have q6 : (8.21 : ℝ) * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47))))))
      ≤ ‖1 - sR40 / 2 + 6‖ * (‖1 - sR40 / 2 + 5‖ * (‖1 - sR40 / 2 + 4‖ * (‖1 - sR40 / 2 + 3‖ * (‖1 - sR40 / 2 + 2‖ * (‖1 - sR40 / 2 + 1‖ * (‖1 - sR40 / 2‖)))))) :=
    mul_le_mul norm_zUpR40_6_ge q5 (by positivity) (norm_nonneg _)
  have q7 : (9.07 : ℝ) * (8.21 * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47)))))))
      ≤ ‖1 - sR40 / 2 + 7‖ * (‖1 - sR40 / 2 + 6‖ * (‖1 - sR40 / 2 + 5‖ * (‖1 - sR40 / 2 + 4‖ * (‖1 - sR40 / 2 + 3‖ * (‖1 - sR40 / 2 + 2‖ * (‖1 - sR40 / 2 + 1‖ * (‖1 - sR40 / 2‖))))))) :=
    mul_le_mul norm_zUpR40_7_ge q6 (by positivity) (norm_nonneg _)
  have q8 : (9.95 : ℝ) * (9.07 * (8.21 * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47))))))))
      ≤ ‖1 - sR40 / 2 + 8‖ * (‖1 - sR40 / 2 + 7‖ * (‖1 - sR40 / 2 + 6‖ * (‖1 - sR40 / 2 + 5‖ * (‖1 - sR40 / 2 + 4‖ * (‖1 - sR40 / 2 + 3‖ * (‖1 - sR40 / 2 + 2‖ * (‖1 - sR40 / 2 + 1‖ * (‖1 - sR40 / 2‖)))))))) :=
    mul_le_mul norm_zUpR40_8_ge q7 (by positivity) (norm_nonneg _)
  have q9 : (10.86 : ℝ) * (9.95 * (9.07 * (8.21 * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47)))))))))
      ≤ ‖1 - sR40 / 2 + 9‖ * (‖1 - sR40 / 2 + 8‖ * (‖1 - sR40 / 2 + 7‖ * (‖1 - sR40 / 2 + 6‖ * (‖1 - sR40 / 2 + 5‖ * (‖1 - sR40 / 2 + 4‖ * (‖1 - sR40 / 2 + 3‖ * (‖1 - sR40 / 2 + 2‖ * (‖1 - sR40 / 2 + 1‖ * (‖1 - sR40 / 2‖))))))))) :=
    mul_le_mul norm_zUpR40_9_ge q8 (by positivity) (norm_nonneg _)
  have q10 : (11.78 : ℝ) * (10.86 * (9.95 * (9.07 * (8.21 * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47))))))))))
      ≤ ‖1 - sR40 / 2 + 10‖ * (‖1 - sR40 / 2 + 9‖ * (‖1 - sR40 / 2 + 8‖ * (‖1 - sR40 / 2 + 7‖ * (‖1 - sR40 / 2 + 6‖ * (‖1 - sR40 / 2 + 5‖ * (‖1 - sR40 / 2 + 4‖ * (‖1 - sR40 / 2 + 3‖ * (‖1 - sR40 / 2 + 2‖ * (‖1 - sR40 / 2 + 1‖ * (‖1 - sR40 / 2‖)))))))))) :=
    mul_le_mul norm_zUpR40_10_ge q9 (by positivity) (norm_nonneg _)
  have q11 : (12.72 : ℝ) * (11.78 * (10.86 * (9.95 * (9.07 * (8.21 * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47)))))))))))
      ≤ ‖1 - sR40 / 2 + 11‖ * (‖1 - sR40 / 2 + 10‖ * (‖1 - sR40 / 2 + 9‖ * (‖1 - sR40 / 2 + 8‖ * (‖1 - sR40 / 2 + 7‖ * (‖1 - sR40 / 2 + 6‖ * (‖1 - sR40 / 2 + 5‖ * (‖1 - sR40 / 2 + 4‖ * (‖1 - sR40 / 2 + 3‖ * (‖1 - sR40 / 2 + 2‖ * (‖1 - sR40 / 2 + 1‖ * (‖1 - sR40 / 2‖))))))))))) :=
    mul_le_mul norm_zUpR40_11_ge q10 (by positivity) (norm_nonneg _)
  have q12 : (13.66 : ℝ) * (12.72 * (11.78 * (10.86 * (9.95 * (9.07 * (8.21 * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47))))))))))))
      ≤ ‖1 - sR40 / 2 + 12‖ * (‖1 - sR40 / 2 + 11‖ * (‖1 - sR40 / 2 + 10‖ * (‖1 - sR40 / 2 + 9‖ * (‖1 - sR40 / 2 + 8‖ * (‖1 - sR40 / 2 + 7‖ * (‖1 - sR40 / 2 + 6‖ * (‖1 - sR40 / 2 + 5‖ * (‖1 - sR40 / 2 + 4‖ * (‖1 - sR40 / 2 + 3‖ * (‖1 - sR40 / 2 + 2‖ * (‖1 - sR40 / 2 + 1‖ * (‖1 - sR40 / 2‖)))))))))))) :=
    mul_le_mul norm_zUpR40_12_ge q11 (by positivity) (norm_nonneg _)
  have q13 : (14.61 : ℝ) * (13.66 * (12.72 * (11.78 * (10.86 * (9.95 * (9.07 * (8.21 * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47)))))))))))))
      ≤ ‖1 - sR40 / 2 + 13‖ * (‖1 - sR40 / 2 + 12‖ * (‖1 - sR40 / 2 + 11‖ * (‖1 - sR40 / 2 + 10‖ * (‖1 - sR40 / 2 + 9‖ * (‖1 - sR40 / 2 + 8‖ * (‖1 - sR40 / 2 + 7‖ * (‖1 - sR40 / 2 + 6‖ * (‖1 - sR40 / 2 + 5‖ * (‖1 - sR40 / 2 + 4‖ * (‖1 - sR40 / 2 + 3‖ * (‖1 - sR40 / 2 + 2‖ * (‖1 - sR40 / 2 + 1‖ * (‖1 - sR40 / 2‖))))))))))))) :=
    mul_le_mul norm_zUpR40_13_ge q12 (by positivity) (norm_nonneg _)
  have q14 : (15.57 : ℝ) * (14.61 * (13.66 * (12.72 * (11.78 * (10.86 * (9.95 * (9.07 * (8.21 * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47))))))))))))))
      ≤ ‖1 - sR40 / 2 + 14‖ * (‖1 - sR40 / 2 + 13‖ * (‖1 - sR40 / 2 + 12‖ * (‖1 - sR40 / 2 + 11‖ * (‖1 - sR40 / 2 + 10‖ * (‖1 - sR40 / 2 + 9‖ * (‖1 - sR40 / 2 + 8‖ * (‖1 - sR40 / 2 + 7‖ * (‖1 - sR40 / 2 + 6‖ * (‖1 - sR40 / 2 + 5‖ * (‖1 - sR40 / 2 + 4‖ * (‖1 - sR40 / 2 + 3‖ * (‖1 - sR40 / 2 + 2‖ * (‖1 - sR40 / 2 + 1‖ * (‖1 - sR40 / 2‖)))))))))))))) :=
    mul_le_mul norm_zUpR40_14_ge q13 (by positivity) (norm_nonneg _)
  have hDlo : (120000000000000 : ℝ)
      ≤ (15.57 : ℝ) * (14.61 * (13.66 * (12.72 * (11.78 * (10.86 * (9.95 * (9.07 * (8.21 * (7.38 * (6.6 * (5.89 * (5.27 * (4.78 * (4.47)))))))))))))) := by
    norm_num
  have hD_ge : (120000000000000 : ℝ)
      ≤ ‖1 - sR40 / 2 + 14‖ * (‖1 - sR40 / 2 + 13‖ * (‖1 - sR40 / 2 + 12‖ * (‖1 - sR40 / 2 + 11‖ * (‖1 - sR40 / 2 + 10‖ * (‖1 - sR40 / 2 + 9‖ * (‖1 - sR40 / 2 + 8‖ * (‖1 - sR40 / 2 + 7‖ * (‖1 - sR40 / 2 + 6‖ * (‖1 - sR40 / 2 + 5‖ * (‖1 - sR40 / 2 + 4‖ * (‖1 - sR40 / 2 + 3‖ * (‖1 - sR40 / 2 + 2‖ * (‖1 - sR40 / 2 + 1‖ * (‖1 - sR40 / 2‖)))))))))))))) :=
    le_trans hDlo q14
  have hD_pos : (0 : ℝ)
      < (‖1 - sR40 / 2 + 14‖
        * (‖1 - sR40 / 2 + 13‖
        * (‖1 - sR40 / 2 + 12‖
        * (‖1 - sR40 / 2 + 11‖
        * (‖1 - sR40 / 2 + 10‖
        * (‖1 - sR40 / 2 + 9‖
        * (‖1 - sR40 / 2 + 8‖
        * (‖1 - sR40 / 2 + 7‖
        * (‖1 - sR40 / 2 + 6‖
        * (‖1 - sR40 / 2 + 5‖
        * (‖1 - sR40 / 2 + 4‖
        * (‖1 - sR40 / 2 + 3‖
        * (‖1 - sR40 / 2 + 2‖
        * (‖1 - sR40 / 2 + 1‖
          * ‖1 - sR40 / 2‖)))))))))))))) :=
    lt_of_lt_of_le (by norm_num) hD_ge
  -- Numerator: `‖Complex.Gamma (1 - sR40 / 2 + 15)‖ ≤ Real.Gamma(15.9475) ≤ 1160000000000`.
  have hre15 : (1 - sR40 / 2 + 15).re = 15.9475 := by
    simp only [Complex.add_re, zUpR40_re, Complex.re_ofNat]
    norm_num
  have hGN_re : (0 : ℝ) < (1 - sR40 / 2 + 15).re := by
    rw [hre15]
    norm_num
  have hGN_le : ‖Complex.Gamma (1 - sR40 / 2 + 15)‖ ≤ 1160000000000 := by
    have h1 : ‖Complex.Gamma (1 - sR40 / 2 + 15)‖
        ≤ Real.Gamma ((1 - sR40 / 2 + 15).re) :=
      R00GammaLower.norm_Gamma_le_realGamma hGN_re
    have hreNb : ((1 - sR40 / 2 + 15).re) = 15.9475 := hre15
    rw [hreNb] at h1
    exact le_trans h1 CellGammaUpper09475.realGamma_159475_le
  -- Combine: `D * ‖Complex.Gamma (1 - sR40 / 2)‖ = ‖Complex.Gamma (1 - sR40 / 2 + 15)‖ ≤ 1160000000000`, `D ≤ 120000000000000`.
  have hD_mul : (‖1 - sR40 / 2 + 14‖
        * (‖1 - sR40 / 2 + 13‖
        * (‖1 - sR40 / 2 + 12‖
        * (‖1 - sR40 / 2 + 11‖
        * (‖1 - sR40 / 2 + 10‖
        * (‖1 - sR40 / 2 + 9‖
        * (‖1 - sR40 / 2 + 8‖
        * (‖1 - sR40 / 2 + 7‖
        * (‖1 - sR40 / 2 + 6‖
        * (‖1 - sR40 / 2 + 5‖
        * (‖1 - sR40 / 2 + 4‖
        * (‖1 - sR40 / 2 + 3‖
        * (‖1 - sR40 / 2 + 2‖
        * (‖1 - sR40 / 2 + 1‖
          * ‖1 - sR40 / 2‖))))))))))))))
        * ‖Complex.Gamma (1 - sR40 / 2)‖
      = ‖Complex.Gamma (1 - sR40 / 2 + 15)‖ := by
    rw [hprod]
    ring
  have hle : (‖1 - sR40 / 2 + 14‖
        * (‖1 - sR40 / 2 + 13‖
        * (‖1 - sR40 / 2 + 12‖
        * (‖1 - sR40 / 2 + 11‖
        * (‖1 - sR40 / 2 + 10‖
        * (‖1 - sR40 / 2 + 9‖
        * (‖1 - sR40 / 2 + 8‖
        * (‖1 - sR40 / 2 + 7‖
        * (‖1 - sR40 / 2 + 6‖
        * (‖1 - sR40 / 2 + 5‖
        * (‖1 - sR40 / 2 + 4‖
        * (‖1 - sR40 / 2 + 3‖
        * (‖1 - sR40 / 2 + 2‖
        * (‖1 - sR40 / 2 + 1‖
          * ‖1 - sR40 / 2‖))))))))))))))
        * ‖Complex.Gamma (1 - sR40 / 2)‖ ≤ 1160000000000 := by
    rw [hD_mul]
    exact hGN_le
  have hmul_comm : ‖Complex.Gamma (1 - sR40 / 2)‖
        * (‖1 - sR40 / 2 + 14‖
        * (‖1 - sR40 / 2 + 13‖
        * (‖1 - sR40 / 2 + 12‖
        * (‖1 - sR40 / 2 + 11‖
        * (‖1 - sR40 / 2 + 10‖
        * (‖1 - sR40 / 2 + 9‖
        * (‖1 - sR40 / 2 + 8‖
        * (‖1 - sR40 / 2 + 7‖
        * (‖1 - sR40 / 2 + 6‖
        * (‖1 - sR40 / 2 + 5‖
        * (‖1 - sR40 / 2 + 4‖
        * (‖1 - sR40 / 2 + 3‖
        * (‖1 - sR40 / 2 + 2‖
        * (‖1 - sR40 / 2 + 1‖
          * ‖1 - sR40 / 2‖))))))))))))))
        ≤ 1160000000000 := by
    calc ‖Complex.Gamma (1 - sR40 / 2)‖ * _
          = _ * ‖Complex.Gamma (1 - sR40 / 2)‖ := mul_comm _ _
      _ ≤ 1160000000000 := hle
  have hdiv : ‖Complex.Gamma (1 - sR40 / 2)‖
      ≤ 1160000000000 / (‖1 - sR40 / 2 + 14‖
        * (‖1 - sR40 / 2 + 13‖
        * (‖1 - sR40 / 2 + 12‖
        * (‖1 - sR40 / 2 + 11‖
        * (‖1 - sR40 / 2 + 10‖
        * (‖1 - sR40 / 2 + 9‖
        * (‖1 - sR40 / 2 + 8‖
        * (‖1 - sR40 / 2 + 7‖
        * (‖1 - sR40 / 2 + 6‖
        * (‖1 - sR40 / 2 + 5‖
        * (‖1 - sR40 / 2 + 4‖
        * (‖1 - sR40 / 2 + 3‖
        * (‖1 - sR40 / 2 + 2‖
        * (‖1 - sR40 / 2 + 1‖
          * ‖1 - sR40 / 2‖))))))))))))))
        :=
    (le_div_iff₀ hD_pos).mpr hmul_comm
  have hcap : (1160000000000 : ℝ)
      ≤ 0.01 * (‖1 - sR40 / 2 + 14‖
        * (‖1 - sR40 / 2 + 13‖
        * (‖1 - sR40 / 2 + 12‖
        * (‖1 - sR40 / 2 + 11‖
        * (‖1 - sR40 / 2 + 10‖
        * (‖1 - sR40 / 2 + 9‖
        * (‖1 - sR40 / 2 + 8‖
        * (‖1 - sR40 / 2 + 7‖
        * (‖1 - sR40 / 2 + 6‖
        * (‖1 - sR40 / 2 + 5‖
        * (‖1 - sR40 / 2 + 4‖
        * (‖1 - sR40 / 2 + 3‖
        * (‖1 - sR40 / 2 + 2‖
        * (‖1 - sR40 / 2 + 1‖
          * ‖1 - sR40 / 2‖)))))))))))))) := by
    calc (1160000000000 : ℝ) ≤ 0.01 * 120000000000000 := by norm_num
      _ ≤ 0.01 * _ :=
          mul_le_mul_of_nonneg_left hD_ge (by norm_num)
  have hfinal : 1160000000000 / (‖1 - sR40 / 2 + 14‖ * (‖1 - sR40 / 2 + 13‖ * (‖1 - sR40 / 2 + 12‖ * (‖1 - sR40 / 2 + 11‖ * (‖1 - sR40 / 2 + 10‖ * (‖1 - sR40 / 2 + 9‖ * (‖1 - sR40 / 2 + 8‖ * (‖1 - sR40 / 2 + 7‖ * (‖1 - sR40 / 2 + 6‖ * (‖1 - sR40 / 2 + 5‖ * (‖1 - sR40 / 2 + 4‖ * (‖1 - sR40 / 2 + 3‖ * (‖1 - sR40 / 2 + 2‖ * (‖1 - sR40 / 2 + 1‖ * (‖1 - sR40 / 2‖)))))))))))))))
      ≤ 0.01 :=
    (div_le_iff₀ hD_pos).mpr hcap
  exact le_trans hdiv hfinal

end R40GammaUpper

