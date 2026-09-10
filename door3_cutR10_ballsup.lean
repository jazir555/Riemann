import Mathlib
import central_cover_assembly

/-! # Door-3 CutR10 closed-ball sup enclosure (real-arc lane, premise (b))

Goal: the closed-ball sup enclosure
  `∀ z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1), ‖xiShiftedEntire z‖ ≤ 0.04`,
consumed by `Door3ZetaCutoff.cutR10_derivRemainder_of_closedBall_sup`
(`door3_zeta_cutoff.lean:404`) via `Door3RHWiring.cutR10_deriv_of_ballSup`
(`door3_rh_wiring.lean:44`). This file attempts premise (b) of the door-3 capstone.

## Recon (read-only sources, exact shapes)

* Consumer `hC` shape (`door3_zeta_cutoff.lean:404-407`):
  `(hC : ∀ z ∈ Metric.closedBall CentralCoverAssembly.CutR10.center
  (CentralCoverAssembly.CutR10.radius + 1),
  ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ (0.04 : ℝ))`.
* Geometry (`central_cover_assembly.lean`): `CutR10 = ⟨9.75, 10.25, -0.49, 0.49⟩`
  (`CutR10_x0/x1/y0/y1`), `CutR10.center = ((10 : ℝ) : ℂ)` (`cutR10_center_eq`,
  `Door3CutR10Center`, ~line 16642), `CutR10.radius = sqrt (0.25^2 + 0.49^2)`
  (`CutR10_radius_eq`, ~line 6864) with `CutR10.radius < 0.56`
  (`CutR10_radius_lt` via `cutoff_radius_bound`).
* Entire extension (`central_cover_assembly.lean:823`):
  `xiShiftedEntire z = 1/2 - (z^2 + 1/4)/2 * completedRiemannZeta₀ (1/2 + I*z)`.
* Factoring template (`cutR10_center_bound_of_gamma_zeta`, ~line 16707-16759):
  `classicalXiPrefactor s = ((1/2) * s * (s-1)) * pi^(-(s/2)) * Gamma (s/2)`
  (`hpref`), `xiShifted center = prefactor * zeta` (`hxi`), assembled with
  `mul_le_mul` chains (`g1/g2/g3`) and `Complex.norm_cpow_eq_rpow_re_of_pos`.
  Here `zeta = riemannZeta` definitionally (`riemann_hypothesis.lean:16`).
* Banked Gamma remainder (cite read-only, NOT reused):
  `Door3GammaCutoff.cutR10_gammaRemainder : Door3CutR10Center.cutR10_gammaRemainder`
  (`door3_gamma_cutoff.lean:122`), i.e.
  `(1/2000 : ℝ) ≤ ‖Complex.Gamma (((1/2:ℂ) + I*CutR10.center)/2)‖`.
  This is a LOWER bound at the single center point; the ball sup needs an UPPER
  bound over a region, so it does not transfer (different direction and domain).
* Euler-product bounds (`TailZetaUpper.riemannZeta_norm_le_const_of_re_ge` /
  `zeta_norm_le_const_of_re_ge`: `‖ζ‖ ≤ 1 + 1/δ` on `1 + δ ≤ Re`;
  `zeta_rightEdge_B3`/`zeta_rightEdge_B2`, cf. `riemann_hypothesis_newsection`):
  these apply only on the right sliver `Re ∈ [1.5, 2.06]` of our region, NOT on
  the bulk `Re < 1`. Hence the zeta factor stays an explicit strip hypothesis.

## s-plane region (ball image under `s = 1/2 + I*z`)

`CutR10.radius + 1 ≤ 1.56`, so for `z` in the ball, `z.re ∈ [8.44, 11.56]` and
`z.im ∈ [-1.56, 1.56]`. With `s = shiftedS z = 1/2 + I*z` (`shiftedS_re`,
`shiftedS_im_eq`: `s.re = 1/2 - z.im`, `s.im = z.re`):
  `s.re ∈ [-1.06, 2.06]`, `s.im ∈ [8.44, 11.56]`.
The zeta argument lies in the strip (never `Re ≥ 1 + δ` uniformly).

## Proof plan and status

* PROVED (from Mathlib + banked lemmas): ball radius cap, `z.re`/`z.im` bounds,
  `s`-region bounds, `shiftedS z ≠ 0, 1`, poly-factor upper `≤ 67`
  (via exact transfer `(1/2)*s*(s-1) = -((z^2+1/4)/2)`), pi-factor upper
  `≤ 16/5` (via `Complex.norm_cpow_eq_rpow_re_of_pos`, `Real.pi_lt_d2`,
  `Real.rpow_le_rpow_of_exponent_le`, mirroring `cutR10_pi_norm_lower`).
* HYPOTHESIS premises (explicit Props, sorry-free): global product identity
  `hProd` (discharged by `completedRiemannZeta₀_eq_polar_plus_xi`
  (`riemann_hypothesis.lean:1668`) + `Gammaℝ` def
  (`Mathlib/Analysis/SpecialFunctions/Γ/Deligne.lean:43`) + `zeta = riemannZeta`
  (`rfl`) + `s ≠ 0, 1` proved here), zeta-factor sup `hZetaSup` (strip wall:
  FE + Stirling + convexity; true center value `≈ 1.549` per
  `central_cover_assembly.lean:16789`), Gamma-factor sup `hGammaSup`
  (Stirling upper; true region sup `≈ 0.0071` at the `(1.03 + 4.22*I)` corner,
  true center value `≈ 0.000651` per `:16782`).
* The factor-separated assembly honestly reaches only `≤ 12.87`
  (`ballSup_of_factorSups`), NOT `0.04`: at the in-ball endpoint
  `z = 10 - (radius+1)` the poly·pi·Gamma factors alone give `≈ 0.062 > 0.04`,
  so premise (b) as stated needs `|ζ(1/2 + 8.45*I)| ≤ 0.64` there and may be
  FALSE (see feasibility note before `cutR10_closedBall_sup`). The exact `0.04`
  shape is therefore conditional on one explicit joint-sup premise `hJoint`.
-/

open CentralCoverAssembly

noncomputable section

namespace Door3CutR10BallSup

/-! ## Ball geometry (PROVED): radius cap and coordinate bounds. -/

/-- Ball radius cap from the banked `CutR10.radius < 0.56`. -/
theorem cutR10_ball_radius_le : CutR10.radius + 1 ≤ (1.56 : ℝ) := by
  have h := CutR10_radius_lt
  linarith

/-- Distance from the center, in norm form (`cutR10_center_eq` + `dist_eq_norm`). -/
theorem mem_ball_norm_le {z : ℂ}
    (hz : z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1)) :
    ‖z - ((((10 : ℝ)) : ℂ))‖ ≤ (1.56 : ℝ) := by
  have hmem : dist z CutR10.center ≤ CutR10.radius + 1 :=
    Metric.mem_closedBall.mp hz
  rw [Door3CutR10Center.cutR10_center_eq, dist_eq_norm] at hmem
  exact le_trans hmem cutR10_ball_radius_le

/-- Real parts on the ball: `z.re ∈ [8.44, 11.56]`.
Mirrors the `abs_re_le_norm` + `sub_re` pattern at
`central_cover_assembly.lean:6273-6278`. -/
theorem mem_ball_re_bounds {z : ℂ}
    (hz : z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1)) :
    (8.44 : ℝ) ≤ z.re ∧ z.re ≤ (11.56 : ℝ) := by
  have hd := mem_ball_norm_le hz
  have hre : |(z - ((((10 : ℝ)) : ℂ))).re| ≤ (1.56 : ℝ) := by
    calc |(z - ((((10 : ℝ)) : ℂ))).re| ≤ ‖z - ((((10 : ℝ)) : ℂ))‖ :=
          Complex.abs_re_le_norm _
      _ ≤ (1.56 : ℝ) := hd
  have here : (z - ((((10 : ℝ)) : ℂ))).re = z.re - 10 := by
    simp [Complex.sub_re]
  rw [here] at hre
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  constructor <;> linarith

/-- Imaginary parts on the ball: `z.im ∈ [-1.56, 1.56]` (same pattern, `sub_im`). -/
theorem mem_ball_im_bounds {z : ℂ}
    (hz : z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1)) :
    (-1.56 : ℝ) ≤ z.im ∧ z.im ≤ (1.56 : ℝ) := by
  have hd := mem_ball_norm_le hz
  have him : |(z - ((((10 : ℝ)) : ℂ))).im| ≤ (1.56 : ℝ) := by
    calc |(z - ((((10 : ℝ)) : ℂ))).im| ≤ ‖z - ((((10 : ℝ)) : ℂ))‖ :=
          Complex.abs_im_le_norm _
      _ ≤ (1.56 : ℝ) := hd
  have heim : (z - ((((10 : ℝ)) : ℂ))).im = z.im := by
    simp [Complex.sub_im]
  rw [heim] at him
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  constructor <;> linarith

/-- Absolute norm cap on the ball: `‖z‖ ≤ 11.56` (triangle via `10`). -/
theorem mem_ball_abs_norm_le {z : ℂ}
    (hz : z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1)) :
    ‖z‖ ≤ (11.56 : ℝ) := by
  have hd := mem_ball_norm_le hz
  have h10 : ‖((((10 : ℝ)) : ℂ))‖ = (10 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hdecomp : z = (z - ((((10 : ℝ)) : ℂ))) + ((((10 : ℝ)) : ℂ)) := by abel
  calc ‖z‖ = ‖(z - ((((10 : ℝ)) : ℂ))) + ((((10 : ℝ)) : ℂ))‖ := by rw [hdecomp]
    _ ≤ ‖z - ((((10 : ℝ)) : ℂ))‖ + ‖((((10 : ℝ)) : ℂ))‖ := norm_add_le _ _
    _ ≤ (11.56 : ℝ) := by rw [h10]; linarith

/-! ## s-plane region (PROVED): `shiftedS` coordinate bounds. -/

/-- `s.re = 1/2 - z.im ∈ [-1.06, 2.06]` on the ball (`shiftedS_re`). -/
theorem mem_ball_shiftedS_re_bounds {z : ℂ}
    (hz : z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1)) :
    (-1.06 : ℝ) ≤ (shiftedS z).re ∧ (shiftedS z).re ≤ (2.06 : ℝ) := by
  rw [shiftedS_re]
  obtain ⟨hlo, hhi⟩ := mem_ball_im_bounds hz
  constructor <;> linarith

/-- `s.im = z.re ∈ [8.44, 11.56]` on the ball (`shiftedS_im_eq`). -/
theorem mem_ball_shiftedS_im_bounds {z : ℂ}
    (hz : z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1)) :
    (8.44 : ℝ) ≤ (shiftedS z).im ∧ (shiftedS z).im ≤ (11.56 : ℝ) := by
  rw [shiftedS_im_eq]
  exact mem_ball_re_bounds hz

/-- The shifted point avoids `0` (its imaginary part is `≥ 8.44`). -/
theorem mem_ball_shiftedS_ne_zero {z : ℂ}
    (hz : z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1)) :
    shiftedS z ≠ 0 := by
  intro h0
  have him : z.re = 0 := by
    have hcon := congrArg Complex.im h0
    rw [shiftedS_im_eq] at hcon
    simpa using hcon
  linarith [(mem_ball_re_bounds hz).1]

/-- The shifted point avoids `1` (same imaginary-part argument). -/
theorem mem_ball_shiftedS_ne_one {z : ℂ}
    (hz : z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1)) :
    shiftedS z ≠ 1 := by
  intro h0
  have him : z.re = 0 := by
    have hcon := congrArg Complex.im h0
    rw [shiftedS_im_eq] at hcon
    simpa using hcon
  linarith [(mem_ball_re_bounds hz).1]

/-! ## Poly factor (PROVED): exact transfer plus the `≤ 67` upper. -/

/-- Exact transfer `(1/2)*s*(s-1) = -((z^2+1/4)/2)` for `s = shiftedS z`
(`I*I = -1` via `linear_combination`; the cross terms cancel). -/
theorem ballPoly_eq (z : ℂ) :
    (1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)
      = -((z ^ 2 + (1 / 4 : ℂ)) / 2) := by
  have hI : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
  unfold shiftedS
  linear_combination (z ^ 2 / 2) * hI

/-- Poly-factor upper `≤ 67` on the ball
(`‖z‖ ≤ 11.56`, so `‖z^2+1/4‖/2 ≤ (11.56^2+1/4)/2 = 66.9418`). -/
theorem ballPoly_upper {z : ℂ}
    (hz : z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1)) :
    ‖(1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)‖ ≤ (67 : ℝ) := by
  have hz2 := mem_ball_abs_norm_le hz
  have h14 : ‖((1 / 4 : ℂ))‖ = ((1 / 4 : ℝ)) := by
    have hcast : ((1 / 4 : ℂ)) = ((((1 / 4 : ℝ)) : ℂ)) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have h2 : ‖((2 : ℂ))‖ = (2 : ℝ) := by norm_num
  have hsq : ‖z ^ 2‖ = ‖z‖ ^ 2 := norm_pow z 2
  have hpow : ‖z‖ ^ 2 ≤ (11.56 : ℝ) ^ 2 := by
    have h1 : ‖z‖ * ‖z‖ ≤ (11.56 : ℝ) * (11.56 : ℝ) :=
      mul_le_mul hz2 hz2 (norm_nonneg _) (by norm_num)
    rw [pow_two, pow_two]
    exact h1
  rw [ballPoly_eq, norm_neg, norm_div, h2]
  have hle : ‖z ^ 2 + (1 / 4 : ℂ)‖ ≤ (133.8836 : ℝ) := by
    calc ‖z ^ 2 + (1 / 4 : ℂ)‖ ≤ ‖z ^ 2‖ + ‖((1 / 4 : ℂ))‖ := norm_add_le _ _
      _ = ‖z‖ ^ 2 + 1 / 4 := by rw [hsq, h14]
      _ ≤ (133.8836 : ℝ) := by
        have hnum : (11.56 : ℝ) ^ 2 + 1 / 4 = (133.8836 : ℝ) := by norm_num
        linarith
  linarith

/-! ## Pi factor (PROVED): upper `≤ 16/5`, mirroring `cutR10_pi_norm_lower`. -/

/-- Pi-power upper on the ball: `‖π^(-(s/2))‖ = π^(-(s.re)/2) ≤ π^1 ≤ 16/5`,
since `s.re ≥ -1.06` gives exponent `≤ 0.53 ≤ 1`. Uses
`Complex.norm_cpow_eq_rpow_re_of_pos`, `Real.rpow_le_rpow_of_exponent_le`
(with `Real.pi_gt_three`, as at `central_cover_assembly.lean:9704`), and
`Real.pi_lt_d2` (as at `:16684-16687`). -/
theorem ballPi_upper {z : ℂ}
    (hz : z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1)) :
    ‖((Real.pi : ℂ) ^ (-(shiftedS z / 2)))‖ ≤ (16 / 5 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have hre : (-(shiftedS z / 2)).re = -(shiftedS z).re / 2 := by
    have hdiv : ((shiftedS z / 2 : ℂ)).re = (shiftedS z).re / 2 := by
      simp [Complex.div_ofNat]
    rw [Complex.neg_re, hdiv]
  rw [hre]
  have hslo := (mem_ball_shiftedS_re_bounds hz).1
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

/-! ## Conditional assembly.

`hProd` is the global product identity on the ball (the `1/2` in
`xiShiftedEntire` cancels against the polar part of `completedRiemannZeta₀`,
leaving poly × pi × Gamma × zeta — the same shape as `hpref`/`hxi` in
`cutR10_center_bound_of_gamma_zeta`). It is discharged by
`completedRiemannZeta₀_eq_polar_plus_xi` (`riemann_hypothesis.lean:1668`) plus
the `Gammaℝ` definition (`Mathlib/Analysis/SpecialFunctions/Γ/Deligne.lean:43`)
plus `zeta = riemannZeta` (`rfl`) plus `s ≠ 0, 1` (proved above as
`mem_ball_shiftedS_ne_zero/one`).
-/

/-- Factor-separated sup: honest numerals reach `≤ 12.87`
(`67 * (16/5) * (1/100) * 6 = 12.864`, `by norm_num`), NOT `0.04`.
Premises: `hProd` (product identity above);
`hZetaSup` (strip zeta upper, TRUE order `O(1)`–`O(5)`; center `≈ 1.549`);
`hGammaSup` (Stirling Gamma upper on `s/2`, TRUE sup `≈ 0.0071`).
Assembly mirrors the `g1/g2/g3` `mul_le_mul` chains of
`cutR10_center_bound_of_gamma_zeta`, in upper-bound direction. -/
theorem ballSup_of_factorSups
    (hProd : ∀ z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1),
      xiShiftedEntire z = ((1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1))
        * ((Real.pi : ℂ) ^ (-(shiftedS z / 2)))
        * (Complex.Gamma (shiftedS z / 2)) * (zeta (shiftedS z)))
    (hZetaSup : ∀ s : ℂ, (-1.06 : ℝ) ≤ s.re → s.re ≤ (2.06 : ℝ) →
      (8.44 : ℝ) ≤ s.im → s.im ≤ (11.56 : ℝ) → ‖zeta s‖ ≤ (6 : ℝ))
    (hGammaSup : ∀ s : ℂ, (-1.06 : ℝ) ≤ s.re → s.re ≤ (2.06 : ℝ) →
      (8.44 : ℝ) ≤ s.im → s.im ≤ (11.56 : ℝ) →
      ‖Complex.Gamma (s / 2)‖ ≤ (1 / 100 : ℝ)) :
    ∀ z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1),
      ‖xiShiftedEntire z‖ ≤ (12.87 : ℝ) := by
  intro z hz
  rw [hProd z hz, norm_mul, norm_mul, norm_mul]
  have hpoly := ballPoly_upper hz
  have hpi := ballPi_upper hz
  have hre := mem_ball_shiftedS_re_bounds hz
  have him := mem_ball_shiftedS_im_bounds hz
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

/-! ## Exact-shape goal (premise (b)).

FEASIBILITY FLAG (could not determine — needs fix-wave numerics): the exact
`0.04` cap is TIGHT even at the center (four-factor product there is
`≈ 0.03797`: `50.125 * 0.7512 * 0.000651 * 1.549`). At the in-ball real
endpoint `z = 10 - (radius+1)` (`s = 1/2 + 8.45*I`, Stirling estimate)
poly·pi·Gamma alone give `≈ 0.062 > 0.04`, so `0.04` would need
`‖ζ(1/2 + 8.45*I)‖ ≤ 0.64` there — implausible this far below the first zeta
zero (`t ≈ 14.13`). Premise (b) as stated may be FALSE; the fix-wave must check
the joint sup numerically before attempting to discharge `hJoint`. The
`12.87` assembly above is the honest factor-separated reach.
-/

/-- Exact premise-(b) shape, conditional on the joint pointwise product sup
`hJoint` (HYPOTHESIS premise for the fix-wave) plus the product identity
`hProd`. Conclusion is byte-for-byte the `hC` consumed at
`door3_zeta_cutoff.lean:404` (hence by `door3_rh_wiring.lean:44`). -/
theorem cutR10_closedBall_sup
    (hProd : ∀ z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1),
      xiShiftedEntire z = ((1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1))
        * ((Real.pi : ℂ) ^ (-(shiftedS z / 2)))
        * (Complex.Gamma (shiftedS z / 2)) * (zeta (shiftedS z)))
    (hJoint : ∀ z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1),
      ‖(1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)‖
        * ‖((Real.pi : ℂ) ^ (-(shiftedS z / 2)))‖
        * ‖Complex.Gamma (shiftedS z / 2)‖ * ‖zeta (shiftedS z)‖
        ≤ (0.04 : ℝ)) :
    ∀ z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1),
      ‖xiShiftedEntire z‖ ≤ (0.04 : ℝ) := by
  intro z hz
  rw [hProd z hz, norm_mul, norm_mul, norm_mul]
  exact hJoint z hz

end Door3CutR10BallSup

#print axioms Door3CutR10BallSup.cutR10_ball_radius_le
#print axioms Door3CutR10BallSup.mem_ball_re_bounds
#print axioms Door3CutR10BallSup.mem_ball_im_bounds
#print axioms Door3CutR10BallSup.mem_ball_shiftedS_re_bounds
#print axioms Door3CutR10BallSup.ballPoly_eq
#print axioms Door3CutR10BallSup.ballPoly_upper
#print axioms Door3CutR10BallSup.ballPi_upper
#print axioms Door3CutR10BallSup.ballSup_of_factorSups
#print axioms Door3CutR10BallSup.cutR10_closedBall_sup
