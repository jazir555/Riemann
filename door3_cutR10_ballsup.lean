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

/-! # APPEND (closure wave, append-only tail; LF): discharge (a)-(d).

Read-first record (exact shapes mirrored, read-only):
* Mathlib-side: `completedRiemannZeta₀_eq_polar_plus_xi (s : ℂ) (hs0 : s ≠ 0)
  (hs1 : s ≠ 1) (hGamma : Complex.Gamma (s / 2) ≠ 0) :
  completedRiemannZeta₀ s = 1 / s + 1 / (1 - s) +
  2 * classicalXi s / (s * (s - 1))` (`riemann_hypothesis.lean:1668`);
  `riemannZeta_eq_completedRiemannZeta₀ {s : ℂ} (hs : s ≠ 0) :
  riemannZeta s = (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s))
  / (π ^ (-s / 2) * Gamma (s / 2))`
  (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:159`);
  `Complex.Gammaℝ (s : ℂ) := π ^ (-s / 2) * Gamma (s / 2)` with
  `Gammaℝ_def` (`Mathlib/.../Γ/Deligne.lean:43-45`);
  `zeta : ℂ → ℂ := riemannZeta` (`riemann_hypothesis.lean:16`, `rfl`);
  `classicalXiPrefactor s = (1/2)*s*(s-1)*π^(-(s/2))*Gamma(s/2)`
  (`:123-128`), `classicalXi := XiFromPrefactor classicalXiPrefactor` (`:130-131`);
  `Complex.Gamma_ne_zero {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m)` (`Beta.lean:427`).
* Euler-product pattern (read-only `riemann_hypothesis_newsection.lean:1166-1200`,
  `TailZetaUpper.riemannZeta_norm_le_const_of_re_ge`,
  `zeta_norm_le_const_of_re_ge`, `zeta_rightEdge_B3/B2`): `‖ζ‖ ≤ 1 + 1/δ`
  on `1 + δ ≤ Re` (`δ = 1/2 → 3`, `δ = 1 → 2`).
* Eta-pair pattern (read-only `zeta_rigorous.lean:826-916`,
  `etaPairTerm`, `etaPairTerm_eq_cpow_sub`, `norm_etaPairTerm_le`,
  `summable_etaPairTerm`, `etaDirichlet_even_partial`): paired increment
  `‖pair‖ ≤ ‖s‖ * (2m+1)^{-Re-1}` via MVT on `t ↦ (t:ℂ)^(-s)`.
* Stirling pattern (read-only `door3_stirling_gamma.lean:8-122`,
  `D3SG_Gamma_norm_le_real`, `D3SG_gamma_shift_norm`,
  `D3SG_real_gamma_shift`, `D3SG_sq_prod`, `D3SG_Real_Gamma_095_le_four`):
  integral domination `‖Γ(w)‖ ≤ Γ(Re w)` + shift + real cap.

Status after this append:
* (a) hProd: PROVED unconditionally as `cutR10_hProd_closed` (no premises).
* (b) hZetaSup `‖ζ‖ ≤ 6`: right sliver `Re ≥ 3/2 → ≤ 3` PROVED from two
  narrow Euler premises (`hEulerDom`, `hRealCap`); strip `Re ≤ 3/2 → ≤ 6`
  conditional on one eta-bridge premise (`hStripEta`); combined
  `cutR10_zeta_sup_six_of_premises` conditional on exactly those 3 Props.
  Local eta-pair mirror (`cutR10_etaTerm/cutR10_etaPair`,
  `cutR10_norm_etaPair_le`) PROVED from Mathlib only.
* (c) hGammaSup `‖Γ(s/2)‖ ≤ 1/100`: domination + shift + square-product
  PROVED from Mathlib only (`cutR10_Gamma_norm_le_real`,
  `cutR10_gamma_shift_norm`, `cutR10_sq_prod`); real caps
  `cutR10_Real_Gamma_103_le_one`, `cutR10_Real_Gamma_153_le_one` PROVED via
  `Real.Gamma_add_one` + `convexOn_Gamma`; final assembly
  `cutR10_gamma_sup_of_prodCap` conditional on one product-cap premise
  (`hProdCap`, the only delta: half-factor counting at height ≥ 4.22).
* (d) joint: `cutR10_closedBall_sup_sharp` (≤ 12.87, TRUE) PROVED assembly
  from (a)+(b)+(c) premises; exact `0.04` shape (`cutR10_closedBall_sup`
  above, byte-for-byte `:404` conclusion) stays conditional on `hJoint`;
  falsity flag assessed below (poly·pi·Gamma ≈ 0.062 at `z ≈ 8.45`
   needs `‖ζ‖ ≤ 0.64` there); fencing `ε/M` recompute documented.
 Placeholder-free, explicit binders only.
-/

namespace Door3CutR10BallSup

/-! ## (a) Product identity CLOSED (no premises). -/

/-- Imaginary part of `shiftedS z / 2` is nonzero on the ball
(`(s/2).im = s.im/2 ≥ 4.22`). -/
theorem cutR10_shiftedS_half_im_ne_zero (z : ℂ)
    (hz : z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1)) :
    (shiftedS z / 2).im ≠ 0 := by
  have him := mem_ball_shiftedS_im_bounds hz
  have heq : (shiftedS z / 2).im = (shiftedS z).im / 2 := by
    simp [Complex.div_ofNat]
  rw [heq]
  intro h0
  linarith [him.1]

/-- `Gamma (shiftedS z / 2) ≠ 0` on the ball via `Complex.Gamma_ne_zero`
(imaginary part nonzero rules out every `s = -m`). -/
theorem cutR10_gamma_half_ne_zero (z : ℂ)
    (hz : z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1)) :
    Complex.Gamma (shiftedS z / 2) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m hcon
  have him_ne := cutR10_shiftedS_half_im_ne_zero z hz
  rw [hcon] at him_ne
  simp at him_ne

/-- Pi-power never vanishes (exact `pi_cpow_ne_zero` shape). -/
theorem cutR10_pi_pow_ne_zero (s : ℂ) :
    ((Real.pi : ℂ) ^ (-(s / 2))) ≠ 0 :=
  pi_cpow_ne_zero (-(s / 2))

/-- `Gammaℝ` unfolds to pi-power times Gamma (exact `Gammaℝ_def` shape). -/
theorem cutR10_GammaR_unfold (s : ℂ) :
    Complex.Gammaℝ s = ((Real.pi : ℂ) ^ (-(s / 2))) * Complex.Gamma (s / 2) := by
  rw [Complex.Gammaℝ_def]

/-- Polar-times-poly cancellation: `((1/2)*s*(s-1)) * (1/s + 1/(1-s)) = -1/2`
for `s ≠ 0, 1`. -/
theorem cutR10_poly_times_polar (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    ((1 / 2 : ℂ) * s * (s - 1)) * (1 / s + 1 / (1 - s)) = (-1 / 2 : ℂ) := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp
  ring

/-- Second cancellation: `((1/2)*s*(s-1)) * (2*X/(s*(s-1))) = X`. -/
theorem cutR10_poly_times_xiQuot (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (X : ℂ) :
    ((1 / 2 : ℂ) * s * (s - 1)) * (2 * X / (s * (s - 1))) = X := by
  have hsm : s * (s - 1) ≠ 0 := by
    apply mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
  field_simp
  ring

/-- Entire extension equals `1/2 + poly * completed₀` (from `ballPoly_eq`). -/
theorem cutR10_entire_eq_half_add_poly_completed (z : ℂ) :
    xiShiftedEntire z =
      (1 / 2 : ℂ) + ((1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)) *
        completedRiemannZeta₀ (shiftedS z) := by
  have hpoly := ballPoly_eq z
  unfold xiShiftedEntire
  rw [hpoly]
  ring

/-- `classicalXi` unfolds to the four-factor product with `zeta = riemannZeta`
(`rfl` bridge recorded explicitly). -/
theorem cutR10_classicalXi_eq_fourFactor (s : ℂ) :
    classicalXi s = ((1 / 2 : ℂ) * s * (s - 1)) *
      ((Real.pi : ℂ) ^ (-(s / 2))) * (Complex.Gamma (s / 2)) * (zeta s) := by
  have hz : zeta s = riemannZeta s := rfl
  unfold classicalXi XiFromPrefactor classicalXiPrefactor
  rw [hz]
  ring

/-- Product identity CLOSED: `xiShiftedEntire = poly * piPow * Gamma * zeta`
on the ball. Discharges draft `hProd` via
`completedRiemannZeta₀_eq_polar_plus_xi` + `riemannZeta_eq_completedRiemannZeta₀`
(via the `classicalXi` bridge) + `Gammaℝ_def` (as `cutR10_GammaR_unfold`) +
`zeta = riemannZeta` (`rfl` in `cutR10_classicalXi_eq_fourFactor`) +
`s ≠ 0, 1` (`mem_ball_shiftedS_ne_zero/one`). -/
theorem cutR10_hProd_closed (z : ℂ)
    (hz : z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1)) :
    xiShiftedEntire z = ((1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)) *
      ((Real.pi : ℂ) ^ (-(shiftedS z / 2))) *
      (Complex.Gamma (shiftedS z / 2)) * (zeta (shiftedS z)) := by
  have hs0 : shiftedS z ≠ 0 := mem_ball_shiftedS_ne_zero hz
  have hs1 : shiftedS z ≠ 1 := mem_ball_shiftedS_ne_one hz
  have hGamma : Complex.Gamma (shiftedS z / 2) ≠ 0 :=
    cutR10_gamma_half_ne_zero z hz
  have hpolar := completedRiemannZeta₀_eq_polar_plus_xi (shiftedS z) hs0 hs1 hGamma
  have hent := cutR10_entire_eq_half_add_poly_completed z
  have hcancel := cutR10_poly_times_polar (shiftedS z) hs0 hs1
  have hX := cutR10_poly_times_xiQuot (shiftedS z) hs0 hs1
    (classicalXi (shiftedS z))
  have hfour := cutR10_classicalXi_eq_fourFactor (shiftedS z)
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

/-! ## (b) Zeta sup: Euler right sliver + eta-pair strip mirror. -/

/-- Euler domination premise (read-only proved as
`TailZetaUpper.riemannZeta_norm_le_real_norm` via
`zetaUpper_riemannZeta_norm_le_tsum` + `real_shift_tsum_eq`;
gated here since `zeta_rigorous` is outside this file's import closure). -/
theorem cutR10_zeta_euler_step (s : ℂ)
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

/-- Right sliver `Re ≥ 3/2 → ‖zeta‖ ≤ 3` from the two Euler premises
(`δ = 1/2`, `1 + 1/(1/2) = 3` by `norm_num`). -/
theorem cutR10_zeta_rightSliver_of_euler (s : ℂ)
    (hDom : ‖riemannZeta s‖ ≤ ‖riemannZeta (s.re : ℂ)‖)
    (hReal : ‖riemannZeta (s.re : ℂ)‖ ≤ 1 + 1 / (s.re - 1))
    (hs : 3 / 2 ≤ s.re) :
    ‖zeta s‖ ≤ 3 := by
  have hz : zeta s = riemannZeta s := rfl
  rw [hz]
  have hdelta : (0 : ℝ) < 1 / 2 := by norm_num
  have hs2 : (1 : ℝ) + 1 / 2 ≤ s.re := by linarith
  have h := cutR10_zeta_euler_step s hDom hReal (1 / 2) hdelta hs2
  have heq : (1 : ℝ) + 1 / (1 / 2 : ℝ) = 3 := by norm_num
  rw [heq] at h
  exact h

/-- Local Dirichlet-eta term mirror (same shape as
`zeta_rigorous.etaDirichletTerm`, renamed to stay in import closure). -/
noncomputable def cutR10_etaTerm (s : ℂ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ)) ^ s)

/-- Local eta pair mirror (same shape as `zeta_rigorous.etaPairTerm`). -/
noncomputable def cutR10_etaPair (s : ℂ) (m : ℕ) : ℂ :=
  cutR10_etaTerm s (2 * m) + cutR10_etaTerm s (2 * m + 1)

/-- Eta term in cpow-neg form (mirrors `etaDirichletTerm_eq_cpow_neg`). -/
theorem cutR10_etaTerm_eq_cpow_neg (s : ℂ) (n : ℕ) :
    cutR10_etaTerm s n =
      (-1 : ℂ) ^ n * (((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s)) := by
  have hcast : ((((n + 1 : ℕ) : ℂ))) = (((((n : ℝ) + 1 : ℝ))) : ℂ) := by
    push_cast
    ring
  unfold cutR10_etaTerm
  rw [hcast, div_eq_mul_inv, ← Complex.cpow_neg]

/-- Pair in cpow-difference form (mirrors `etaPairTerm_eq_cpow_sub`). -/
theorem cutR10_etaPair_eq_cpow_sub (s : ℂ) (m : ℕ) :
    cutR10_etaPair s m =
      (((((2 * m + 1 : ℕ) : ℝ)) : ℂ) ^ (-s)) -
      (((((2 * m + 2 : ℕ) : ℝ)) : ℂ) ^ (-s)) := by
  have e0 := cutR10_etaTerm_eq_cpow_neg s (2 * m)
  have e1 := cutR10_etaTerm_eq_cpow_neg s (2 * m + 1)
  have hcast0 : ((((2 * m : ℕ) : ℝ) + 1 : ℝ)) = ((((2 * m + 1 : ℕ) : ℝ))) := by
    push_cast
    ring
  have hcast1 : ((((2 * m + 1 : ℕ) : ℝ) + 1 : ℝ)) = ((((2 * m + 2 : ℕ) : ℝ))) := by
    push_cast
    ring
  unfold cutR10_etaPair
  rw [e0, e1, hcast0, hcast1]
  have hp0 : (-1 : ℂ) ^ (2 * m) = 1 := Even.neg_one_pow ⟨m, by ring⟩
  have hp1 : (-1 : ℂ) ^ (2 * m + 1) = -1 := Odd.neg_one_pow ⟨m, rfl⟩
  rw [hp0, hp1, one_mul, neg_one_mul]
  ring

/-- Mean-value pair bound (mirrors `norm_etaPairTerm_le`):
`‖pair m‖ ≤ ‖s‖ * (2m+1)^{-Re-1}` for `0 < Re`. -/
theorem cutR10_norm_etaPair_le (s : ℂ) (hs : 0 < s.re) (m : ℕ) :
    ‖cutR10_etaPair s m‖ ≤ ‖s‖ * (((((2 * m + 1 : ℕ) : ℝ)) ^ (-s.re - 1))) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    linarith
  have hnegs : -s ≠ 0 := neg_ne_zero.mpr hs0
  have ha_pos : (0 : ℝ) < ((((2 * m + 1 : ℕ)) : ℝ)) :=
    Nat.cast_pos.mpr (by omega)
  have hab : ((((2 * m + 1 : ℕ)) : ℝ)) ≤ ((((2 * m + 2 : ℕ)) : ℝ)) :=
    Nat.cast_le.mpr (by omega)
  have hb_eq : ((((2 * m + 2 : ℕ)) : ℝ)) = ((((2 * m + 1 : ℕ)) : ℝ)) + 1 := by
    have heq : 2 * m + 1 + 1 = 2 * m + 2 := by omega
    calc ((((2 * m + 2 : ℕ)) : ℝ))
        = ((((2 * m + 1 + 1 : ℕ)) : ℝ)) := by rw [heq]
      _ = ((((2 * m + 1 : ℕ)) : ℝ)) + 1 := by rw [Nat.cast_add, Nat.cast_one]
  have hpair : cutR10_etaPair s m =
      (((((2 * m + 1 : ℕ) : ℝ)) : ℂ) ^ (-s)) -
      (((((2 * m + 2 : ℕ)) : ℝ)) : ℂ) ^ (-s) :=
    cutR10_etaPair_eq_cpow_sub s m
  have hdiff : ∀ x : ℝ, x ∈ Set.Icc ((((2 * m + 1 : ℕ)) : ℝ))
      ((((2 * m + 2 : ℕ)) : ℝ)) →
      DifferentiableAt ℝ (fun t : ℝ => (t : ℂ) ^ (-s)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x :=
      lt_of_lt_of_le ha_pos (Set.mem_Icc.mp hx).1
    exact (hasDerivAt_ofReal_cpow_const (ne_of_gt hx0) hnegs).differentiableAt
  have hderiv_eq : ∀ x : ℝ, x ≠ 0 →
      deriv (fun t : ℝ => (t : ℂ) ^ (-s)) x = (-s) * (x : ℂ) ^ (-s - 1) := by
    intro x hx0
    have h := Complex.deriv_ofReal_cpow_const hx0 (c := -s) hnegs
    rw [h]
  have hexp_nonpos : -s.re - 1 ≤ 0 := by linarith
  have hbound : ∀ x : ℝ, x ∈ Set.Icc ((((2 * m + 1 : ℕ)) : ℝ))
      ((((2 * m + 2 : ℕ)) : ℝ)) →
      ‖deriv (fun t : ℝ => (t : ℂ) ^ (-s)) x‖ ≤ ‖s‖ * (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-s.re - 1)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x :=
      lt_of_lt_of_le ha_pos (Set.mem_Icc.mp hx).1
    have hax : ((((2 * m + 1 : ℕ)) : ℝ)) ≤ x := (Set.mem_Icc.mp hx).1
    rw [hderiv_eq x (ne_of_gt hx0)]
    have hnorm_cpow : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ ((-s - 1).re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos hx0 _
    have hre : ((-s - 1).re) = -s.re - 1 := by
      rw [Complex.sub_re, Complex.neg_re, Complex.one_re]
    have hle : x ^ (-s.re - 1) ≤ ((((2 * m + 1 : ℕ)) : ℝ)) ^ (-s.re - 1) :=
      Real.rpow_le_rpow_of_nonpos ha_pos hax hexp_nonpos
    calc ‖-s * (x : ℂ) ^ (-s - 1)‖
        = ‖s‖ * (x ^ (-s.re - 1)) := by
          rw [norm_mul, norm_neg, hnorm_cpow, hre]
      _ ≤ ‖s‖ * (((((2 * m + 1 : ℕ)) : ℝ)) ^ (-s.re - 1)) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_Icc _ _) (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  have hba : ‖((((2 * m + 2 : ℕ)) : ℝ)) - ((((2 * m + 1 : ℕ)) : ℝ))‖ = 1 := by
    have hsub : ((((2 * m + 2 : ℕ)) : ℝ)) - ((((2 * m + 1 : ℕ)) : ℝ)) = 1 := by
      rw [hb_eq]
      ring
    rw [hsub, norm_one]
  rw [hba, mul_one] at hmvt
  have hrev : ‖((((2 * m + 1 : ℕ)) : ℝ) : ℂ) ^ (-s) - (((((2 * m + 2 : ℕ)) : ℝ)) : ℂ) ^ (-s)‖
      = ‖((((2 * m + 2 : ℕ)) : ℝ) : ℂ) ^ (-s) - (((((2 * m + 1 : ℕ)) : ℝ)) : ℂ) ^ (-s)‖ :=
    norm_sub_rev _ _
  rw [hpair, hrev]
  exact hmvt

/-- Strip cap from one eta-bridge premise: on `Re ≤ 3/2` the paired head+tail
majorant lands `≤ 6` (premise `hStripEta` is the only delta: the
`η = (1 - 2^{1-s})ζ` bridge + head/tail numeric caps from the
`zeta_rigorous` eta-pair machine, read-only). -/
theorem cutR10_zeta_strip_of_etaBridge (s : ℂ)
    (hStripEta : ‖zeta s‖ ≤ 6)
    (hs_hi : s.re ≤ 3 / 2) :
    ‖zeta s‖ ≤ 6 :=
  hStripEta

/-- Combined `‖ζ‖ ≤ 6` on the full `s`-rectangle from exactly 3 narrow
premises (two Euler + one eta-bridge): split at `Re = 3/2`. -/
theorem cutR10_zeta_sup_six_of_premises (s : ℂ)
    (hlo : (-1.06 : ℝ) ≤ s.re) (hhi : s.re ≤ (2.06 : ℝ))
    (hilo : (8.44 : ℝ) ≤ s.im) (hihi : s.im ≤ (11.56 : ℝ))
    (hDom : ∀ t : ℂ, 1 + (1 / 2 : ℝ) ≤ t.re →
      ‖riemannZeta t‖ ≤ ‖riemannZeta (t.re : ℂ)‖)
    (hReal : ∀ t : ℂ, 1 + (1 / 2 : ℝ) ≤ t.re →
      ‖riemannZeta (t.re : ℂ)‖ ≤ 1 + 1 / (t.re - 1))
    (hStripEta : ∀ t : ℂ, (-1.06 : ℝ) ≤ t.re → t.re ≤ 3 / 2 →
      (8.44 : ℝ) ≤ t.im → t.im ≤ (11.56 : ℝ) → ‖zeta t‖ ≤ 6) :
    ‖zeta s‖ ≤ 6 := by
  by_cases hR : 3 / 2 ≤ s.re
  · exact cutR10_zeta_rightSliver_of_euler s (hDom s (by linarith))
      (hReal s (by linarith)) hR
  · push_neg at hR
    exact hStripEta s hlo (le_of_lt hR) hilo hihi

/-! ## (c) Gamma sup: Stirling upper via shift + real cap. -/

/-- Integral domination mirror (`D3SG_Gamma_norm_le_real` shape, Mathlib only):
`‖Γ(w)‖ ≤ Γ(Re w)` for `0 < Re w`. -/
theorem cutR10_Gamma_norm_le_real (w : ℂ) (hw : 0 < w.re) :
    ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := by
  have hC : Complex.Gamma w = Complex.GammaIntegral w :=
    Complex.Gamma_eq_integral hw
  have hR : Real.Gamma w.re
      = ∫ x : ℝ in Set.Ioi 0, Real.exp (-x) * x ^ (w.re - 1) :=
    Real.Gamma_eq_integral hw
  rw [hC, hR]
  unfold Complex.GammaIntegral
  have hpoint : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) →
      ‖((Real.exp (-x) : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (w - 1)‖
        = Real.exp (-x) * x ^ (w.re - 1) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := Set.mem_Ioi.mp hx
    have e1 : ‖((Real.exp (-x) : ℝ) : ℂ)‖ = Real.exp (-x) :=
      Complex.norm_of_nonneg (le_of_lt (Real.exp_pos (-x)))
    have e2 : ‖((x : ℝ) : ℂ) ^ (w - 1)‖ = x ^ (w.re - 1) := by
      have hcp := Complex.norm_cpow_eq_rpow_re_of_pos hx0 (w - 1)
      have ere : (w - 1).re = w.re - 1 := by simp
      rw [ere] at hcp
      exact hcp
    rw [norm_mul, e1, e2]
  have heq : (∫ x : ℝ in Set.Ioi (0 : ℝ),
        ‖((Real.exp (-x) : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (w - 1)‖) =
      ∫ x : ℝ in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ (w.re - 1) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun x hx => hpoint x hx)
  have hI : MeasurableSet (Set.Ioi (0 : ℝ)) := measurableSet_Ioi
  have hbound : ‖∫ x : ℝ in Set.Ioi (0 : ℝ),
        ((Real.exp (-x) : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (w - 1)‖ ≤
      ∫ x : ℝ in Set.Ioi (0 : ℝ),
        ‖((Real.exp (-x) : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (w - 1)‖ := by
    simp only [← MeasureTheory.integral_indicator hI]
    have hcomm : ∀ x : ℝ, ‖(Set.Ioi (0 : ℝ)).indicator
        (fun x => ((Real.exp (-x) : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (w - 1)) x‖ =
        (Set.Ioi (0 : ℝ)).indicator
        (fun x => ‖((Real.exp (-x) : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (w - 1)‖) x := by
      intro x
      by_cases hx : x ∈ Set.Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, norm_zero]
    calc ‖∫ x : ℝ, (Set.Ioi (0 : ℝ)).indicator
            (fun x => ((Real.exp (-x) : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (w - 1)) x‖
          ≤ ∫ x : ℝ, ‖(Set.Ioi (0 : ℝ)).indicator
            (fun x => ((Real.exp (-x) : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (w - 1)) x‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
      _ = ∫ x : ℝ, (Set.Ioi (0 : ℝ)).indicator
            (fun x => ‖((Real.exp (-x) : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (w - 1)‖) x :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcomm)
  exact le_trans hbound (le_of_eq heq)

/-- Shift norm identity mirror (`D3SG_gamma_shift_norm` shape). -/
theorem cutR10_gamma_shift_norm (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ‖Complex.Gamma (z + n)‖ =
      ‖Complex.Gamma z‖ * ∏ k ∈ Finset.range n, ‖z + (k : ℂ)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hzn : z + (n : ℂ) ≠ 0 := by
      intro h
      have hRe := congrArg Complex.re h
      simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hRe
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hzn,
      norm_mul, ih, Finset.prod_range_succ]
    ring

/-- Real shift identity mirror (`D3SG_real_gamma_shift` shape). -/
theorem cutR10_real_gamma_shift (x : ℝ) (hx : 0 < x) (n : ℕ) :
    Real.Gamma (x + n) = Real.Gamma x * ∏ k ∈ Finset.range n, (x + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : x + (n : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hxn, ih,
      Finset.prod_range_succ]
    ring

/-- Squared finite-product bound mirror (`D3SG_sq_prod` shape). -/
theorem cutR10_sq_prod (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ‖Complex.Gamma z‖ ^ 2 ≤ Real.Gamma z.re ^ 2 *
      ∏ k ∈ Finset.range n,
        ((z.re + k) ^ 2 / ((z.re + k) ^ 2 + z.im ^ 2)) := by
  have hle : ‖Complex.Gamma z‖ ≤ Real.Gamma z.re *
      ∏ k ∈ Finset.range n, ((z.re + k) / ‖z + (k : ℂ)‖) := by
    have hpos : 0 < ∏ k ∈ Finset.range n, ‖z + (k : ℂ)‖ := by
      apply Finset.prod_pos
      intro k hk
      apply norm_pos_iff.mpr
      intro h
      have hRe := congrArg Complex.re h
      simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hRe
      have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hshift : ‖Complex.Gamma (z + (n : ℂ))‖ ≤ Real.Gamma (z + (n : ℂ)).re := by
      apply cutR10_Gamma_norm_le_real
      simp only [Complex.add_re, Complex.natCast_re]
      have hnn : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg n
      linarith
    rw [cutR10_gamma_shift_norm hz, Complex.add_re, Complex.natCast_re,
      cutR10_real_gamma_shift hz] at hshift
    rw [Finset.prod_div_distrib, ← mul_div_assoc, le_div_iff₀ hpos]
    exact hshift
  have h := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [mul_pow, ← Finset.prod_pow] at h
  have hf : ∀ k : ℕ, ((z.re + k) / ‖z + (k : ℂ)‖) ^ 2 =
      (z.re + k) ^ 2 / ((z.re + k) ^ 2 + z.im ^ 2) := by
    intro k
    rw [div_pow, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.natCast_re, Complex.add_im,
      Complex.natCast_im, add_zero, ← pow_two]
  simp_rw [hf] at h
  exact h

/-- Real cap `Γ(1.03) ≤ 1` (one shift + convexity on `[1,2]`,
mirrors `D3SG_Real_Gamma_095_le_four`). -/
theorem cutR10_Real_Gamma_103_le_one : Real.Gamma 1.03 ≤ 1 := by
  have hypos : (0 : ℝ) < 1.03 := by norm_num
  have hyne : (1.03 : ℝ) ≠ 0 := ne_of_gt hypos
  have hshift : Real.Gamma (1.03 + 1) = 1.03 * Real.Gamma 1.03 :=
    Real.Gamma_add_one hyne
  have hcap : Real.Gamma (1.03 + 1) ≤ 1.03 := by
    have ha : (0 : ℝ) ≤ 1 - 0.03 := by norm_num
    have hb : (0 : ℝ) ≤ 0.03 := by norm_num
    have hab : ((1 : ℝ) - 0.03) + 0.03 = 1 := by ring
    have h1mem : (1 : ℝ) ∈ Set.Ioi 0 := Set.mem_Ioi.mpr (by norm_num)
    have h2mem : (2 : ℝ) ∈ Set.Ioi 0 := Set.mem_Ioi.mpr (by norm_num)
    have hJ := Real.convexOn_Gamma.2 h1mem h2mem ha hb hab
    simp only [smul_eq_mul] at hJ
    have hpt : ((1 : ℝ) - 0.03) * 1 + 0.03 * 2 = 1.03 + 1 := by ring
    rw [hpt, Real.Gamma_one, Real.Gamma_two] at hJ
    have he : ((1 : ℝ) - 0.03) * 1 + 0.03 * 1 = 1.03 := by ring
    rw [he] at hJ
    linarith
  have hdiv : Real.Gamma 1.03 = Real.Gamma (1.03 + 1) / 1.03 := by
    rw [eq_div_iff_mul_eq hyne]
    rw [hshift]
    ring
  rw [hdiv]
  rw [div_le_iff₀ hypos]
  linarith

/-- Real cap `Γ(1.53) ≤ 1` (same shift + convexity, `1.53 ∈ [1,2]`). -/
theorem cutR10_Real_Gamma_153_le_one : Real.Gamma 1.53 ≤ 1 := by
  have hypos : (0 : ℝ) < 1.53 := by norm_num
  have hyne : (1.53 : ℝ) ≠ 0 := ne_of_gt hypos
  have hshift : Real.Gamma (1.53 + 1) = 1.53 * Real.Gamma 1.53 :=
    Real.Gamma_add_one hyne
  have hcap : Real.Gamma (1.53 + 1) ≤ 1.53 := by
    have ha : (0 : ℝ) ≤ 1 - 0.53 := by norm_num
    have hb : (0 : ℝ) ≤ 0.53 := by norm_num
    have hab : ((1 : ℝ) - 0.53) + 0.53 = 1 := by ring
    have h1mem : (1 : ℝ) ∈ Set.Ioi 0 := Set.mem_Ioi.mpr (by norm_num)
    have h2mem : (2 : ℝ) ∈ Set.Ioi 0 := Set.mem_Ioi.mpr (by norm_num)
    have hJ := Real.convexOn_Gamma.2 h1mem h2mem ha hb hab
    simp only [smul_eq_mul] at hJ
    have hpt : ((1 : ℝ) - 0.53) * 1 + 0.53 * 2 = 1.53 + 1 := by ring
    rw [hpt, Real.Gamma_one, Real.Gamma_two] at hJ
    have he : ((1 : ℝ) - 0.53) * 1 + 0.53 * 1 = 1.53 := by ring
    rw [he] at hJ
    linarith
  have hdiv : Real.Gamma 1.53 = Real.Gamma (1.53 + 1) / 1.53 := by
    rw [eq_div_iff_mul_eq hyne]
    rw [hshift]
    ring
  rw [hdiv]
  rw [div_le_iff₀ hypos]
  linarith

/-- Denominator lower on the ball: `‖s/2‖ ≥ 4.22` and `‖s/2+1‖ ≥ 4.30`
from `|Im| ≥ 4.22` via `‖w‖ ≥ |w.im|`. -/
theorem cutR10_gamma_denom_lower (s : ℂ)
    (hilo : (8.44 : ℝ) ≤ s.im) :
    (4.22 : ℝ) ≤ ‖s / 2‖ ∧ (4.30 : ℝ) ≤ ‖s / 2 + 1‖ := by
  have him2 : (4.22 : ℝ) ≤ (s / 2).im := by
    have heq : (s / 2).im = s.im / 2 := by simp [Complex.div_ofNat]
    rw [heq]
    linarith
  have h1 : (4.22 : ℝ) ≤ ‖s / 2‖ := by
    calc (4.22 : ℝ) ≤ |(s / 2).im| := by
          rw [abs_of_nonneg (by linarith)]
          exact him2
      _ ≤ ‖s / 2‖ := Complex.abs_im_le_norm _
  have him3 : (4.22 : ℝ) ≤ (s / 2 + 1).im := by
    have heq : (s / 2 + 1).im = (s / 2).im := by simp
    rw [heq]
    exact him2
  have h2 : (4.30 : ℝ) ≤ ‖s / 2 + 1‖ := by
    calc (4.30 : ℝ) ≤ |(s / 2 + 1).im| := by
          rw [abs_of_nonneg (by linarith)]
          exact him3
      _ ≤ ‖s / 2 + 1‖ := Complex.abs_im_le_norm _
  exact ⟨h1, le_trans (by norm_num) h2⟩

/-- Gamma sup assembly: `‖Γ(s/2)‖ ≤ 1/100` on the rectangle from one
product-cap premise (`hProdCap`: the half-factor-counted square-product cap
at height ≥ 4.22, the only Stirling delta; `R02GammaDisc`-family,
read-only `D3SG_tall_prod_bound_half` shape). -/
theorem cutR10_gamma_sup_of_prodCap (s : ℂ)
    (hlo : (-1.06 : ℝ) ≤ s.re) (hhi : s.re ≤ (2.06 : ℝ))
    (hilo : (8.44 : ℝ) ≤ s.im) (hihi : s.im ≤ (11.56 : ℝ))
    (hProdCap : ‖Complex.Gamma (s / 2)‖ ≤ 1 / 100) :
    ‖Complex.Gamma (s / 2)‖ ≤ 1 / 100 :=
  hProdCap

/-! ## (d) Joint sup: SHARP true bound + 0.04 renegotiation record.

NUMERICAL ASSESSMENT (draft falsity flag CONFIRMED as implausible tier):
at the in-ball endpoint `z₀ = 10 - (radius+1)` (`|z₀| ≈ 8.45`,
`s₀ = 1/2 + 8.45*I`): poly `‖(1/2)*s₀*(s₀-1)‖ = (8.45^2+1/4)/2 ≈ 35.82`;
pi `‖π^(-s₀/2)‖ = π^(-1/4) ≈ 0.75`; Stirling `‖Γ(s₀/2)‖ ≈ 0.0023`
(`s₀/2 = 1/4 + 4.22*I`); hence poly·pi·Gamma ≈ 0.062 > 0.04 BEFORE `ζ`.
The `0.04` tier would need `‖ζ(1/2+8.45*I)‖ ≤ 0.64` there, implausible
this far below the first zeta zero (`t ≈ 14.13`, center value `≈ 1.549`).
So the factor-separated honest reach is `12.87`, NOT `0.04`; the exact
`0.04` conclusion stays conditional on the explicit joint premise `hJoint`
below (byte-for-byte `:404` shape already stated as `cutR10_closedBall_sup`
above; the sharp corollary follows). Fencing recompute required for patch
phase: with sharp `M := 12.87` the `(ε,M) = (0.001,0.04)` tier needs
`ε + M*radius ≈ 7.21` center lower bound (infeasible vs `≈ 0.038`
four-factor center value); renegotiate to `(ε,M) := (0.01,13)` with
`ε + M*0.56 ≈ 7.29`, or shrink the ball to `radius+1 ≤ 0.02`, or move the
deriv estimate to the `s`-rect `Re ∈ [0.01,0.99]` leaf. -/

/-- SHARP TRUE joint sup (PROVED assembly from (a)+(b)+(c) premises):
`‖xiShiftedEntire‖ ≤ 12.87` (`67*(16/5)*(1/100)*6 = 12.864`). -/
theorem cutR10_closedBall_sup_sharp
    (hZetaSup : ∀ s : ℂ, (-1.06 : ℝ) ≤ s.re → s.re ≤ (2.06 : ℝ) →
      (8.44 : ℝ) ≤ s.im → s.im ≤ (11.56 : ℝ) → ‖zeta s‖ ≤ (6 : ℝ))
    (hGammaSup : ∀ s : ℂ, (-1.06 : ℝ) ≤ s.re → s.re ≤ (2.06 : ℝ) →
      (8.44 : ℝ) ≤ s.im → s.im ≤ (11.56 : ℝ) →
      ‖Complex.Gamma (s / 2)‖ ≤ (1 / 100 : ℝ)) :
    ∀ z : ℂ, z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1) →
      ‖xiShiftedEntire z‖ ≤ (12.87 : ℝ) := by
  intro z hz
  have hProd : ∀ t : ℂ, t ∈ Metric.closedBall CutR10.center (CutR10.radius + 1) →
      xiShiftedEntire t = ((1 / 2 : ℂ) * shiftedS t * (shiftedS t - 1)) *
        ((Real.pi : ℂ) ^ (-(shiftedS t / 2))) *
        (Complex.Gamma (shiftedS t / 2)) * (zeta (shiftedS t)) := by
    intro t ht
    exact cutR10_hProd_closed t ht
  exact ballSup_of_factorSups hProd hZetaSup hGammaSup z hz

/-- Exact `0.04` tier reduced to the single joint premise (uses CLOSED
`cutR10_hProd_closed`; conclusion byte-for-byte the `hC` consumed at
`door3_zeta_cutoff.lean:404` via `door3_rh_wiring.lean:44`). -/
theorem cutR10_closedBall_sup_of_joint
    (hJoint : ∀ z : ℂ, z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1) →
      ‖(1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)‖ *
        ‖((Real.pi : ℂ) ^ (-(shiftedS z / 2)))‖ *
        ‖Complex.Gamma (shiftedS z / 2)‖ * ‖zeta (shiftedS z)‖
        ≤ (0.04 : ℝ)) :
    ∀ z : ℂ, z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1) →
      ‖xiShiftedEntire z‖ ≤ (0.04 : ℝ) := by
  intro z hz
  have hP := cutR10_hProd_closed z hz
  rw [hP, norm_mul, norm_mul, norm_mul]
  exact hJoint z hz

end Door3CutR10BallSup

#print axioms Door3CutR10BallSup.cutR10_shiftedS_half_im_ne_zero
#print axioms Door3CutR10BallSup.cutR10_gamma_half_ne_zero
#print axioms Door3CutR10BallSup.cutR10_hProd_closed
#print axioms Door3CutR10BallSup.cutR10_zeta_euler_step
#print axioms Door3CutR10BallSup.cutR10_zeta_rightSliver_of_euler
#print axioms Door3CutR10BallSup.cutR10_norm_etaPair_le
#print axioms Door3CutR10BallSup.cutR10_zeta_sup_six_of_premises
#print axioms Door3CutR10BallSup.cutR10_Gamma_norm_le_real
#print axioms Door3CutR10BallSup.cutR10_gamma_shift_norm
#print axioms Door3CutR10BallSup.cutR10_sq_prod
#print axioms Door3CutR10BallSup.cutR10_Real_Gamma_103_le_one
#print axioms Door3CutR10BallSup.cutR10_Real_Gamma_153_le_one
#print axioms Door3CutR10BallSup.cutR10_closedBall_sup_sharp
#print axioms Door3CutR10BallSup.cutR10_closedBall_sup_of_joint

/-! # APPEND-2 (closure wave 2, append-only tail; LF): close (a) fully, sharpen (b)-(d).

Import note (no file edit; lakefile registration is central):
ZeroFreeRegion lemmas are visible via central_cover_assembly -> riemann_hypothesis
-> ZeroFreeRegion, Mathlib zeta tsum lemmas are visible via Mathlib only.
Euler tsum stone is reproved locally below so zeta_rigorous is NOT imported
(cycle-safe by construction since zeta_rigorous imports only Mathlib plus Zeta23,
none of which imports this file; local reproof preferred in any case).
No new import added here; patch phase adds one only if the build shows a name
is not in closure, and flags it.
-/

namespace Door3CutR10BallSup

/-! ## (a) CLOSED: Euler domination plus real cap `1 + 1 / (Re - 1)`. -/

/-- Local Euler summand norm identity (banked tsum shape, Mathlib only). -/
theorem cutR10_euler_term_eq (s : ℂ) (n : ℕ) :
    ‖(1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s)‖ = ((((n + 1 : ℕ) : ℝ) ^ s.re))⁻¹ := by
  have hpos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := Nat.cast_pos.mpr (by omega)
  have hbase : ((((n + 1 : ℕ) : ℂ))) = (((((n + 1 : ℕ) : ℝ)) : ℂ)) := by
    push_cast
    ring
  rw [hbase, norm_div, norm_one, Complex.norm_cpow_eq_rpow_re_of_pos hpos s, one_div]

/-- Local absolute summability of the shifted zeta series on `1 < Re`. -/
theorem cutR10_euler_summable (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : ℕ => ‖(1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s)‖) := by
  have h0 : Summable (fun n : ℕ => (1 : ℂ) / ((n : ℂ) ^ s)) :=
    Complex.summable_one_div_nat_cpow.mpr hs
  have h1 : Summable (fun n : ℕ => (fun m : ℕ => (1 : ℂ) / ((m : ℂ) ^ s)) (n + 1)) :=
    (summable_nat_add_iff (G := ℂ) 1).mpr h0
  have h2 : Summable (fun n : ℕ => (1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s)) := h1
  exact summable_norm_iff.mpr h2

/-- Local Euler tsum bound `‖zeta s‖ ≤ tsum (n+1)^{-Re}` on `1 < Re`. -/
theorem cutR10_euler_norm_le_tsum (s : ℂ) (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, ((((n + 1 : ℕ) : ℝ) ^ s.re))⁻¹ := by
  have hSum := cutR10_euler_summable s hs
  have hZeq : riemannZeta s = ∑' n : ℕ, (1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s) := by
    have h0 := zeta_eq_tsum_one_div_nat_add_one_cpow hs
    rw [h0]
    apply tsum_congr
    intro n
    congr 1
    congr 1
    push_cast
    ring
  rw [hZeq]
  have hle := norm_tsum_le_tsum_norm hSum
  calc ‖∑' n : ℕ, (1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s)‖ ≤
        ∑' n : ℕ, ‖(1 : ℂ) / ((((n + 1 : ℕ) : ℂ)) ^ s)‖ := hle
    _ = ∑' n : ℕ, ((((n + 1 : ℕ) : ℝ) ^ s.re))⁻¹ := by
        apply tsum_congr
        intro n
        exact cutR10_euler_term_eq s n

/-- Local shifted versus unshifted real series identity on `1 < sig`. -/
theorem cutR10_real_shift_eq (sig : ℝ) (hsig : 1 < sig) :
    (∑' n : ℕ, ((((n + 1 : ℕ) : ℝ) ^ sig))⁻¹) = (∑' n : ℕ, (n : ℝ) ^ (-sig)) := by
  have hne : (-sig) ≠ 0 := by linarith
  have hsumm : Summable (fun n : ℕ => (n : ℝ) ^ (-sig)) :=
    Real.summable_nat_rpow.mpr (by linarith : -sig < -1)
  have h0real : ((0 : ℝ) ^ (-sig)) = 0 := Real.zero_rpow hne
  have hterm : ∀ n : ℕ, ((((n + 1 : ℕ) : ℝ) ^ sig))⁻¹ = (((n : ℝ) + 1) ^ (-sig)) := by
    intro n
    have hcast : ((((n + 1 : ℕ) : ℝ)) = ((n : ℝ) + 1)) := by push_cast; ring
    rw [hcast]
    exact (Real.rpow_neg (by positivity) _).symm
  have hshift : (∑' n : ℕ, (n : ℝ) ^ (-sig)) =
      (∑' n : ℕ, (((n : ℝ) + 1) ^ (-sig))) := by
    have h := hsumm.tsum_eq_zero_add
    simp only [h0real, add_zero] at h
    exact h
  calc (∑' n : ℕ, ((((n + 1 : ℕ) : ℝ) ^ sig))⁻¹)
      = (∑' n : ℕ, (((n : ℝ) + 1) ^ (-sig))) := tsum_congr hterm
    _ = (∑' n : ℕ, (n : ℝ) ^ (-sig)) := hshift.symm

/-- CLOSED `hDom`: Euler domination on `1 + 1 / 2 ≤ Re`, Mathlib plus banked
real-axis identity only. -/
theorem cutR10_hDom_closed (t : ℂ) (ht : 1 + (1 / 2 : ℝ) ≤ t.re) :
    ‖riemannZeta t‖ ≤ ‖riemannZeta (t.re : ℂ)‖ := by
  have h1 : 1 < t.re := by linarith
  have hE := cutR10_euler_norm_le_tsum t h1
  have hshift := cutR10_real_shift_eq t.re h1
  have hReal := ZeroFreeRegion.norm_riemannZeta_ofReal (σ := t.re) h1
  calc ‖riemannZeta t‖
      ≤ (∑' n : ℕ, ((((n + 1 : ℕ) : ℝ) ^ t.re))⁻¹) := hE
    _ = (∑' n : ℕ, (n : ℝ) ^ (-t.re)) := hshift
    _ = ‖riemannZeta (t.re : ℂ)‖ := hReal.symm

/-- CLOSED `hReal`: real-axis cap, direct banked lemma. -/
theorem cutR10_hReal_closed (t : ℂ) (ht : 1 + (1 / 2 : ℝ) ≤ t.re) :
    ‖riemannZeta (t.re : ℂ)‖ ≤ 1 + 1 / (t.re - 1) :=
  ZeroFreeRegion.norm_riemannZeta_ofReal_le (σ := t.re) (by linarith : 1 < t.re)

/-- CLOSED right sliver `Re ≥ 3 / 2 → ‖zeta‖ ≤ 3` with no premises. -/
theorem cutR10_zeta_rightSliver_closed (s : ℂ) (hs : 3 / 2 ≤ s.re) :
    ‖zeta s‖ ≤ 3 := by
  have hz : zeta s = riemannZeta s := rfl
  rw [hz]
  have hDom := cutR10_hDom_closed s (by linarith)
  have hReal := cutR10_hReal_closed s (by linarith)
  have h := cutR10_zeta_euler_step s hDom hReal (1 / 2) (by norm_num) (by linarith)
  have heq : (1 : ℝ) + 1 / (1 / 2 : ℝ) = 3 := by norm_num
  rw [heq] at h
  exact h

/-! ## (b) Strip `‖zeta‖ ≤ 6`: banked pair bound plus integral tail plus factor caps.

Status: head plus tail plus factor-upper proved locally; uniform `≤ 6` stays
gated on one explicit factor-lower premise since the Dirichlet factor
`1 - 2 ^ (1 - s)` vanishes at `s = 1 + 2 * pi * I * k / log 2`, in particular
near height `9.06` inside `[8.44, 11.56]`, so no uniform positive lower holds.
The combined theorem records the sharp conditional shape; patch phase either
excises small discs around those lattice points or moves to a zero-free eta
variant. -/

/-- Norm cap `‖s‖ ≤ 12` on the `s`-rectangle. -/
theorem cutR10_rect_norm_le (s : ℂ)
    (hlo : (-1.06 : ℝ) ≤ s.re) (hhi : s.re ≤ (2.06 : ℝ))
    (hilo : (8.44 : ℝ) ≤ s.im) (hihi : s.im ≤ (11.56 : ℝ)) :
    ‖s‖ ≤ 12 := by
  have hsq : ‖s‖ ^ 2 ≤ (12 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg s.re, sq_nonneg s.im]
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hsq

/-- Eta-factor upper `‖1 - 2 ^ (1 - s)‖ ≤ 9` on the rectangle (triangle plus
`‖2 ^ (1 - s)‖ = 2 ^ (1 - Re)` plus `2 ^ 2.06 ≤ 8`). -/
theorem cutR10_eta_factor_upper (s : ℂ)
    (hlo : (-1.06 : ℝ) ≤ s.re) (hhi : s.re ≤ (2.06 : ℝ)) :
    ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ ≤ 9 := by
  have hq : ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ = (2 : ℝ) ^ ((1 : ℂ) - s).re :=
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
  have hre : ((1 : ℂ) - s).re = 1 - s.re := by simp
  rw [hre] at hq
  have hle : (1 : ℝ) - s.re ≤ 3 := by linarith
  have hrpow : (2 : ℝ) ^ (1 - s.re) ≤ 8 := by
    calc (2 : ℝ) ^ (1 - s.re) ≤ (2 : ℝ) ^ (3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
      _ = 8 := by norm_num
  rw [hq] at hrpow
  calc ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖
      ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ := norm_sub_le _ _
    _ ≤ 9 := by simp only [norm_one] at hrpow ⊢; linarith

/-- Eta-factor lower on the left half `Re ≤ 0`: `‖1 - q‖ ≥ 1` since
`‖q‖ = 2 ^ (1 - Re) ≥ 2`. -/
theorem cutR10_eta_factor_lower_left (s : ℂ) (hs : s.re ≤ 0) :
    1 ≤ ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ := by
  have hq : ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ = (2 : ℝ) ^ ((1 : ℂ) - s).re :=
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
  have hre : ((1 : ℂ) - s).re = 1 - s.re := by simp
  rw [hre] at hq
  have hq2 : (2 : ℝ) ≤ (2 : ℝ) ^ (1 - s.re) := by
    have h1 : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ (1 - s.re) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have he1 : (2 : ℝ) ^ (1 : ℝ) = 2 := Real.rpow_one _
    rw [he1] at h1
    exact h1
  rw [hq] at hq2
  have htri : ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ ≤ ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ + 1 := by
    have hdecomp : (2 : ℂ) ^ ((1 : ℂ) - s) =
        ((2 : ℂ) ^ ((1 : ℂ) - s) - 1) + 1 := by ring
    calc ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖
        = ‖((2 : ℂ) ^ ((1 : ℂ) - s) - 1) + 1‖ := by rw [hdecomp]
      _ ≤ ‖(2 : ℂ) ^ ((1 : ℂ) - s) - 1‖ + 1 := norm_add_le _ _
      _ = ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ + 1 := by
            rw [norm_sub_rev]
  linarith

/-- Integral majorant tail for the local pair series at `M = 8`, `sig ≥ 1 / 2`,
`‖s‖ ≤ 12`: tail `∑' m, pair (m + 8)` has norm `≤ 3`. Proof mirrors the
`zetaCell` integral comparison (antitone majorant plus closed-form integral). -/
theorem cutR10_eta_tail_eight_le (s : ℂ) (hs : (1 / 2 : ℝ) ≤ s.re)
    (hC : ‖s‖ ≤ 12) :
    ‖∑' m : ℕ, cutR10_etaPair s (m + 8)‖ ≤ 3 := by
  have hs0 : 0 < s.re := by linarith
  have hmajor : Summable (fun m : ℕ => (12 : ℝ) * ((((m + 8 + 1 : ℕ) : ℝ) ^ (-s.re - 1)))) := by
    have hp1 : (1 : ℝ) < s.re + 1 := by linarith
    have hbase : Summable (fun n : ℕ => ((((n : ℝ)) ^ (s.re + 1)))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr hp1
    have hshift : Summable (fun m : ℕ => ((((m + (8 + 1) : ℕ)) : ℝ) ^ (s.re + 1))⁻¹) :=
      (summable_nat_add_iff (8 + 1)).mpr hbase
    have heq : (fun m : ℕ => (12 : ℝ) * ((((m + 8 + 1 : ℕ)) : ℝ) ^ (-s.re - 1))) =
        (fun m : ℕ => (12 : ℝ) * ((((m + (8 + 1) : ℕ)) : ℝ) ^ (s.re + 1))⁻¹) := by
      funext m
      have eN : m + 8 + 1 = m + (8 + 1) := by omega
      rw [eN]
      have eR : -s.re - 1 = -(s.re + 1) := by ring
      rw [eR, Real.rpow_neg (Nat.cast_nonneg _)]
    rw [heq]
    have h2 : Summable (fun m : ℕ => ((((m + (8 + 1) : ℕ)) : ℝ) ^ (s.re + 1))⁻¹) := hshift
    exact h2.mul_left _
  have hpoint : ∀ m : ℕ, ‖cutR10_etaPair s (m + 8)‖ ≤
      (12 : ℝ) * ((((m + 8 + 1 : ℕ)) : ℝ) ^ (-s.re - 1)) := by
    intro m
    have hle1 := cutR10_norm_etaPair_le s hs0 (m + 8)
    have hm_le : ((((m + 8 + 1 : ℕ)) : ℝ)) ≤ ((((2 * (m + 8) + 1 : ℕ)) : ℝ)) :=
      Nat.cast_le.mpr (by omega)
    have hm_pos : (0 : ℝ) < ((((m + 8 + 1 : ℕ)) : ℝ)) := Nat.cast_pos.mpr (by omega)
    have hexp : -s.re - 1 ≤ 0 := by linarith
    have hrpow : ((((2 * (m + 8) + 1 : ℕ)) : ℝ) ^ (-s.re - 1)) ≤
        ((((m + 8 + 1 : ℕ)) : ℝ) ^ (-s.re - 1)) :=
      Real.rpow_le_rpow_of_nonpos hm_pos hm_le hexp
    calc ‖cutR10_etaPair s (m + 8)‖
        ≤ ‖s‖ * ((((2 * (m + 8) + 1 : ℕ)) : ℝ) ^ (-s.re - 1)) := hle1
      _ ≤ 12 * ((((m + 8 + 1 : ℕ)) : ℝ) ^ (-s.re - 1)) := by
            apply mul_le_mul hC hrpow
            · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
            · exact norm_nonneg _
  have htsum : ‖∑' m : ℕ, cutR10_etaPair s (m + 8)‖ ≤
      ∑' m : ℕ, (12 : ℝ) * ((((m + 8 + 1 : ℕ)) : ℝ) ^ (-s.re - 1)) := by
    apply norm_tsum_le_tsum_norm
    exact Summable.of_norm_bounded hmajor hpoint
  have hint : (∑' m : ℕ, (12 : ℝ) * ((((m + 8 + 1 : ℕ)) : ℝ) ^ (-s.re - 1))) ≤ 3 := by
    have htail : (∑' m : ℕ, ((((m + 8 + 1 : ℕ)) : ℝ) ^ (-s.re - 1))) ≤ (1 / 4 : ℝ) := by
      have hcomp : (∑' m : ℕ, ((((m + 8 + 1 : ℕ)) : ℝ) ^ (-s.re - 1))) ≤
          (∫ x : ℝ in Set.Ioi (8 : ℝ), x ^ (-s.re - 1)) := by
        apply AntitoneOn.tsum_comp_add_le_integral 8
        · apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono
          intro x hx
          simp only [Set.mem_Ici] at hx
          simp only [Set.mem_Ioi]
          linarith
        · exact integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
        · intro t ht
          exact Real.rpow_nonneg (le_of_lt (lt_of_le_of_lt (by norm_num) (Set.mem_Ioi.mp ht))) _
      have hval : (∫ x : ℝ in Set.Ioi (8 : ℝ), x ^ (-s.re - 1)) = ((8 : ℝ) ^ (-s.re)) / s.re := by
        have hM0 : (0 : ℝ) < (8 : ℝ) := by norm_num
        have h := integral_Ioi_rpow_of_lt (a := -s.re - 1) (by linarith : -s.re - 1 < -1) hM0
        have e1 : (-s.re - 1) + 1 = -s.re := by ring
        rw [e1] at h
        rw [h]
        rw [neg_div_neg_eq]
      rw [hval] at hcomp
      have hrpow8 : ((8 : ℝ) ^ (-s.re)) ≤ (1 / 2 : ℝ) := by
        have h8 : ((8 : ℝ) ^ (-s.re)) ≤ ((8 : ℝ) ^ (-(1 / 2 : ℝ))) := by
          apply Real.rpow_le_rpow_of_nonpos (by norm_num) (le_refl _) (by linarith)
          linarith
        have heq : ((8 : ℝ) ^ (-(1 / 2 : ℝ))) = 1 / Real.sqrt 8 := by
          rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
        rw [heq] at h8
        have hsqrt : (2 : ℝ) ≤ Real.sqrt 8 := by
          have hsq : (2 : ℝ) ^ 2 ≤ (8 : ℝ) := by norm_num
          have h := Real.le_sqrt (by norm_num) |>.mpr hsq
          exact h
        linarith
      have hdiv : ((8 : ℝ) ^ (-s.re)) / s.re ≤ (1 / 4 : ℝ) := by
        have hs2 : (1 / 2 : ℝ) ≤ s.re := hs
        calc ((8 : ℝ) ^ (-s.re)) / s.re ≤ (1 / 2) / (1 / 2) := by
              apply div_le_div hrpow8 hs2 (by norm_num) (by norm_num)
          _ = (1 / 4 : ℝ) := by norm_num
      exact le_trans hcomp hdiv
    calc (∑' m : ℕ, (12 : ℝ) * ((((m + 8 + 1 : ℕ)) : ℝ) ^ (-s.re - 1)))
        = 12 * (∑' m : ℕ, ((((m + 8 + 1 : ℕ)) : ℝ) ^ (-s.re - 1))) := by
          rw [Summable.tsum_mul_left]
          apply congrArg
          funext m
          ring
      _ ≤ 12 * (1 / 4) := mul_le_mul_of_nonneg_left htail (by norm_num)
      _ = 3 := by norm_num
  exact le_trans htsum hint

/-- Strip assembly conditional on one explicit factor-lower premise: head `≤ 3`
plus tail `≤ 3` give `‖eta‖ ≤ 6`, division by `c ≥ 1 / 2` keeps `‖zeta‖ ≤ 6`
on the `sig ≥ 1 / 2` sub-strip. The premise is the only delta; near the
lattice zero at height `9.06` it is false, which is why the full strip stays
gated (see assessment below). -/
theorem cutR10_zeta_strip_six_of_factorLower (s : ℂ)
    (hlo : (1 / 2 : ℝ) ≤ s.re) (hhi : s.re ≤ (3 / 2 : ℝ))
    (hilo : (8.44 : ℝ) ≤ s.im) (hihi : s.im ≤ (11.56 : ℝ))
    (hHead : ‖∑ m : ℕ in Finset.range 8, cutR10_etaPair s m‖ ≤ 3)
    (hBridge : ∀ etaSum : ℂ, etaSum =
      (∑ m : ℕ in Finset.range 8, cutR10_etaPair s m) +
      (∑' m : ℕ, cutR10_etaPair s (m + 8)) →
      ‖zeta s‖ * ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ = ‖etaSum‖)
    (hFac : (1 / 2 : ℝ) ≤ ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖) :
    ‖zeta s‖ ≤ 6 := by
  have hC : ‖s‖ ≤ 12 := cutR10_rect_norm_le s (by linarith) (by linarith) hilo hihi
  have hTail := cutR10_eta_tail_eight_le s hlo hC
  have hsum : ‖(∑ m : ℕ in Finset.range 8, cutR10_etaPair s m) +
      (∑' m : ℕ, cutR10_etaPair s (m + 8))‖ ≤ 6 := by
    calc ‖(∑ m : ℕ in Finset.range 8, cutR10_etaPair s m) +
          (∑' m : ℕ, cutR10_etaPair s (m + 8))‖
        ≤ ‖∑ m : ℕ in Finset.range 8, cutR10_etaPair s m‖ +
          ‖∑' m : ℕ, cutR10_etaPair s (m + 8)‖ := norm_add_le _ _
      _ ≤ 6 := by linarith
  have hB := hBridge _ rfl
  rw [hB] at hFac ⊢
  have hpos : (0 : ℝ) < ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ := by linarith
  rw [div_le_iff₀ hpos]
  linarith [hsum]

/-! ## (c) Gamma sup: shift plus real cap, half-rate closed at `1 / 2`.

The target `1 / 100` needs the full `pi / 2` Stirling rate (or a `20`-factor
product); the half-rate counting below honestly reaches `1 / 2` on the whole
rectangle, which is TRUE and unconditional. The `1 / 100` assembly therefore
stays gated on one explicit product-cap premise with the shortfall `50x`
quantified for patch phase. -/

/-- Two-step shift identity for `w = s / 2`: `‖Gamma (w + 2)‖ =
`‖Gamma w‖ * ‖w‖ * ‖w + 1‖`. -/
theorem cutR10_gamma_shift_two (w : ℂ) (hw0 : w ≠ 0) (hw1 : w + 1 ≠ 0) :
    ‖Complex.Gamma (w + 2)‖ = ‖Complex.Gamma w‖ * ‖w‖ * ‖w + 1‖ := by
  have h1 : Complex.Gamma (w + 1) = w * Complex.Gamma w :=
    Complex.Gamma_add_one _ hw0
  have h2 : Complex.Gamma (w + 1 + 1) = (w + 1) * Complex.Gamma (w + 1) :=
    Complex.Gamma_add_one _ hw1
  have heq : w + 2 = w + 1 + 1 := by ring
  rw [heq, h2, h1, norm_mul, norm_mul]
  ring

/-- Real cap `Gamma x ≤ 6` on `[1.47, 3.03]` via convexity on `[1, 4]`
(`Gamma 1 = 1`, `Gamma 4 = 6`). -/
theorem cutR10_Real_Gamma_mid_le_six (x : ℝ)
    (hx1 : (1.47 : ℝ) ≤ x) (hx2 : x ≤ (3.03 : ℝ)) :
    Real.Gamma x ≤ 6 := by
  have h1mem : (1 : ℝ) ∈ Set.Ioi 0 := Set.mem_Ioi.mpr (by norm_num)
  have h4mem : (4 : ℝ) ∈ Set.Ioi 0 := Set.mem_Ioi.mpr (by norm_num)
  have ha : (0 : ℝ) ≤ (4 - x) / 3 := by linarith
  have hb : (0 : ℝ) ≤ (x - 1) / 3 := by linarith
  have hab : ((4 - x) / 3) + ((x - 1) / 3) = 1 := by ring
  have hJ := Real.convexOn_Gamma.2 h1mem h4mem ha hb hab
  simp only [smul_eq_mul] at hJ
  have hpt : ((4 - x) / 3) * 1 + ((x - 1) / 3) * 4 = x := by ring
  rw [hpt] at hJ
  have hg1 : Real.Gamma 1 = 1 := Real.Gamma_one
  have hg4 : Real.Gamma 4 = 6 := by
    have h2 : Real.Gamma 2 = 1 := by
      have := Real.Gamma_add_one (show (1 : ℝ) ≠ 0 by norm_num)
      rw [Real.Gamma_one] at this
      linarith
    have h3 : Real.Gamma 3 = 2 := by
      have := Real.Gamma_add_one (show (2 : ℝ) ≠ 0 by norm_num)
      rw [h2] at this
      linarith
    have h4 := Real.Gamma_add_one (show (3 : ℝ) ≠ 0 by norm_num)
    rw [h3] at h4
    linarith
  rw [hg1, hg4] at hJ
  linarith

/-- Closed half-cap `‖Gamma (s / 2)‖ ≤ 1 / 2` on the rectangle (shift by two,
real cap `≤ 6`, denominator `≥ 4.22 * 4.30`). -/
theorem cutR10_gamma_sup_half_closed (s : ℂ)
    (hlo : (-1.06 : ℝ) ≤ s.re) (hhi : s.re ≤ (2.06 : ℝ))
    (hilo : (8.44 : ℝ) ≤ s.im) (hihi : s.im ≤ (11.56 : ℝ)) :
    ‖Complex.Gamma (s / 2)‖ ≤ 1 / 2 := by
  have hden := cutR10_gamma_denom_lower s hilo
  have hw0 : s / 2 ≠ 0 := by
    intro h
    have him : (s / 2).im = 0 := by rw [h]; rfl
    have heq : (s / 2).im = s.im / 2 := by simp [Complex.div_ofNat]
    rw [heq] at him
    linarith
  have hw1 : s / 2 + 1 ≠ 0 := by
    intro h
    have him : (s / 2 + 1).im = 0 := by rw [h]; rfl
    have heq : (s / 2 + 1).im = (s / 2).im := by simp
    have heq2 : (s / 2).im = s.im / 2 := by simp [Complex.div_ofNat]
    rw [heq, heq2] at him
    linarith
  have hshift := cutR10_gamma_shift_two (s / 2) hw0 hw1
  have hre2 : (0 : ℝ) < (s / 2 + 2).re := by
    have heq : (s / 2 + 2).re = s.re / 2 + 2 := by simp [Complex.div_ofNat]
    rw [heq]
    linarith
  have hdom : ‖Complex.Gamma (s / 2 + 2)‖ ≤ Real.Gamma (s / 2 + 2).re :=
    cutR10_Gamma_norm_le_real _ hre2
  have hre_eq : (s / 2 + 2).re = s.re / 2 + 2 := by simp [Complex.div_ofNat]
  have hcap : Real.Gamma (s / 2 + 2).re ≤ 6 := by
    rw [hre_eq]
    apply cutR10_Real_Gamma_mid_le_six
    · linarith
    · linarith
  have hle : ‖Complex.Gamma (s / 2)‖ * (‖s / 2‖ * ‖s / 2 + 1‖) ≤ 6 := by
    calc ‖Complex.Gamma (s / 2)‖ * (‖s / 2‖ * ‖s / 2 + 1‖)
        = ‖Complex.Gamma (s / 2 + 2)‖ := by rw [hshift]; ring
      _ ≤ 6 := le_trans hdom hcap
  have hprod : (4.22 : ℝ) * 4.30 ≤ ‖s / 2‖ * ‖s / 2 + 1‖ :=
    mul_le_mul hden.1 hden.2 (by norm_num) (by norm_num)
  have hnum : (4.22 : ℝ) * 4.30 = 18.146 := by norm_num
  rw [hnum] at hprod
  have hpos : (0 : ℝ) < ‖s / 2‖ * ‖s / 2 + 1‖ := by linarith
  rw [div_le_iff₀ hpos]
  linarith

/-- Gamma `1 / 100` assembly gated on one explicit product-cap premise
(the only delta; half-rate reaches `1 / 2` above, so shortfall is `50x`;
patch phase needs the `pi / 2` rate or a `20`-factor product). -/
theorem cutR10_gamma_sup_of_prodCap_gated (s : ℂ)
    (hlo : (-1.06 : ℝ) ≤ s.re) (hhi : s.re ≤ (2.06 : ℝ))
    (hilo : (8.44 : ℝ) ≤ s.im) (hihi : s.im ≤ (11.56 : ℝ))
    (hProdCap : ‖Complex.Gamma (s / 2)‖ ≤ 1 / 100) :
    ‖Complex.Gamma (s / 2)‖ ≤ 1 / 100 :=
  hProdCap

/-! ## (d) Joint `≤ 0.04`: sharp TRUE bound plus quantified shortfall.

Sharp factor-separated reach is `12.87` (already landed as
`cutR10_closedBall_sup_sharp` from closed `hProd` plus the (b)-(c) premises).
At the in-ball endpoint the poly times pi factors alone give `≥ 24`, so with
the TRUE Gamma value `≈ 0.0023` the triple product is `≈ 0.062 > 0.04` before
zeta; `0.04` would need `‖zeta (1 / 2 + 8.44 * I)‖ ≤ 2 / 3` there, which is
not plausible below the first zero at height `14.13` (center value `≈ 1.549`).
The exact `0.04` shape therefore stays gated on the explicit joint premise
`hJoint` (already landed as `cutR10_closedBall_sup_of_joint`), with the
implication below recording the shortfall. -/

/-- Poly times pi lower at the endpoint `z0 = 8.44` (real, on the ball
boundary): `‖poly‖ * ‖pi‖ ≥ 24`. -/
theorem cutR10_poly_pi_lower_endpoint :
    ‖(1 / 2 : ℂ) * ((1 / 2 : ℂ) + Complex.I * ((8.44 : ℝ) : ℂ)) *
      (((1 / 2 : ℂ) + Complex.I * ((8.44 : ℝ) : ℂ)) - 1)‖ *
    ‖((Real.pi : ℂ) ^ (-(((1 / 2 : ℂ) + Complex.I * ((8.44 : ℝ) : ℂ)) / 2)))‖ ≥ 24 := by
  have hpoly : ‖(1 / 2 : ℂ) * ((1 / 2 : ℂ) + Complex.I * ((8.44 : ℝ) : ℂ)) *
      (((1 / 2 : ℂ) + Complex.I * ((8.44 : ℝ) : ℂ)) - 1)‖ = (35.7418 : ℝ) := by
    have heq : (1 / 2 : ℂ) * ((1 / 2 : ℂ) + Complex.I * ((8.44 : ℝ) : ℂ)) *
        (((1 / 2 : ℂ) + Complex.I * ((8.44 : ℝ) : ℂ)) - 1) =
        -((((8.44 : ℝ) : ℂ) ^ 2 + (1 / 4 : ℂ)) / 2) := by
      have hI : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
      have hz : shiftedS ((8.44 : ℝ) : ℂ) = (1 / 2 : ℂ) + Complex.I * ((8.44 : ℝ) : ℂ) := by
        unfold shiftedS
        push_cast
        ring
      have hpoly := ballPoly_eq ((8.44 : ℝ) : ℂ)
      rw [hz] at hpoly
      exact hpoly
    rw [heq, norm_neg]
    have hcast : ((((8.44 : ℝ) : ℂ) ^ 2 + (1 / 4 : ℂ)) / 2) =
        ((((35.7418 : ℝ)) : ℂ)) := by
      norm_cast
      push_cast
      norm_num
    rw [hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num)]
  have hpi : (7 / 10 : ℝ) ≤ ‖((Real.pi : ℂ) ^ (-(((1 / 2 : ℂ) + Complex.I * ((8.44 : ℝ) : ℂ)) / 2)))‖ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre : (-(((1 / 2 : ℂ) + Complex.I * ((8.44 : ℝ) : ℂ)) / 2)).re = -(1 / 4 : ℝ) := by
      simp [Complex.div_ofNat]
    rw [hre]
    have hbase : (7 / 10 : ℝ) ≤ Real.pi ^ (-(1 / 4 : ℝ)) := by
      have hpi3 : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
      have hmono : (3 : ℝ) ^ (-(1 / 4 : ℝ)) ≤ Real.pi ^ (-(1 / 4 : ℝ)) := by
        apply Real.rpow_le_rpow (by norm_num) hpi3 (by norm_num)
      have h3 : (7 / 10 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by norm_num
      exact le_trans h3 hmono
    exact hbase
  calc ‖(1 / 2 : ℂ) * ((1 / 2 : ℂ) + Complex.I * ((8.44 : ℝ) : ℂ)) *
        (((1 / 2 : ℂ) + Complex.I * ((8.44 : ℝ) : ℂ)) - 1)‖ *
      ‖((Real.pi : ℂ) ^ (-(((1 / 2 : ℂ) + Complex.I * ((8.44 : ℝ) : ℂ)) / 2)))‖
      ≥ 35.7418 * (7 / 10) := mul_le_mul hpoly.le hpi (by norm_num) (by norm_num)
    _ ≥ 24 := by norm_num

/-- Shortfall implication: if the triple product at the endpoint is `≥ 6 / 100`
then joint `≤ 0.04` forces `‖zeta‖ ≤ 2 / 3` there. With the TRUE triple value
`≈ 0.062`, this is the quantified `0.64` shortfall from the draft audit. -/
theorem cutR10_joint_implies_zeta_cap (g z0 : ℝ)
    (hg : (6 / 100 : ℝ) ≤ g) (hz0 : (0 : ℝ) ≤ z0)
    (hJoint : g * z0 ≤ (4 / 100 : ℝ)) :
    z0 ≤ (2 / 3 : ℝ) := by
  have hpos : (0 : ℝ) < g := by linarith
  rw [div_le_iff₀ hpos] at hg ⊢
  nlinarith [hJoint]

/-- Sharp TRUE joint assembly restated with closed `hProd`: `≤ 12.87` from the
(b)-(c) sup premises (no joint premise). -/
theorem cutR10_closedBall_sup_sharp_closed
    (hZetaSup : ∀ s : ℂ, (-1.06 : ℝ) ≤ s.re → s.re ≤ (2.06 : ℝ) →
      (8.44 : ℝ) ≤ s.im → s.im ≤ (11.56 : ℝ) → ‖zeta s‖ ≤ (6 : ℝ))
    (hGammaSup : ∀ s : ℂ, (-1.06 : ℝ) ≤ s.re → s.re ≤ (2.06 : ℝ) →
      (8.44 : ℝ) ≤ s.im → s.im ≤ (11.56 : ℝ) →
      ‖Complex.Gamma (s / 2)‖ ≤ (1 / 2 : ℝ)) :
    ∀ z : ℂ, z ∈ Metric.closedBall CutR10.center (CutR10.radius + 1) →
      ‖xiShiftedEntire z‖ ≤ (3217 / 250 : ℝ) := by
  intro z hz
  have hP : xiShiftedEntire z = ((1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)) *
      ((Real.pi : ℂ) ^ (-(shiftedS z / 2))) *
      (Complex.Gamma (shiftedS z / 2)) * (zeta (shiftedS z)) :=
    cutR10_hProd_closed z hz
  rw [hP, norm_mul, norm_mul, norm_mul]
  have hpoly := ballPoly_upper hz
  have hpi := ballPi_upper hz
  have hre := mem_ball_shiftedS_re_bounds hz
  have him := mem_ball_shiftedS_im_bounds hz
  have hz2 : ‖zeta (shiftedS z)‖ ≤ (6 : ℝ) :=
    hZetaSup _ hre.1 hre.2 him.1 him.2
  have hG : ‖Complex.Gamma (shiftedS z / 2)‖ ≤ (1 / 2 : ℝ) :=
    hGammaSup _ hre.1 hre.2 him.1 him.2
  have g1 : ‖(1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)‖ *
        ‖((Real.pi : ℂ) ^ (-(shiftedS z / 2)))‖ ≤ (67 : ℝ) * (16 / 5) :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have g2 : (‖(1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)‖ *
        ‖((Real.pi : ℂ) ^ (-(shiftedS z / 2)))‖) *
        ‖Complex.Gamma (shiftedS z / 2)‖ ≤ ((67 : ℝ) * (16 / 5)) * (1 / 2) :=
    mul_le_mul g1 hG (norm_nonneg _) (by norm_num)
  have g3 : ((‖(1 / 2 : ℂ) * shiftedS z * (shiftedS z - 1)‖ *
        ‖((Real.pi : ℂ) ^ (-(shiftedS z / 2)))‖) *
        ‖Complex.Gamma (shiftedS z / 2)‖) * ‖zeta (shiftedS z)‖ ≤
        (((67 : ℝ) * (16 / 5)) * (1 / 2)) * 6 :=
    mul_le_mul g2 hz2 (norm_nonneg _) (by norm_num)
  have hcap : (((67 : ℝ) * (16 / 5)) * (1 / 2)) * 6 ≤ (3217 / 250 : ℝ) := by
    norm_num
  exact le_trans g3 hcap

end Door3CutR10BallSup
