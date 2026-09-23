import Mathlib

/-!
# Door-3 local derivative enclosures (deriv lane)

This file owns the **second conjunct** (`deriv_bound`) of the per-cell leaf
obligations, for all cells. Read-only sources quoted:

* Leaf shape (`central_cover_assembly.lean:124-126`, `CellData`):
  `deriv_bound : ∀ z, x0 ≤ z.re → z.re ≤ x1 → y0 ≤ z.im → z.im ≤ y1 →
    ‖deriv xiShifted z‖ ≤ M`.
* `R00_leaf_obligations` (`central_cover_assembly.lean:1175-1177`):
  `((0.002 : ℝ) + 0.05 * R00.radius ≤ ‖xiShifted R00.center‖) ∧
    (∀ w, R00.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))`,
  outer tier `(ε, M) = (0.002, 0.05)`.
* `R00` geometry (`central_cover_assembly.lean:1132-1139`,
  `rh_certificate_infra.lean:21-26,35-36`): `R00 = ⟨-10, -7.5, 0.01, 0.2⟩`,
  center `((-10 + -7.5) / 2, (0.01 + 0.2) / 2) = (-8.75, 0.105)`,
  radius `√(1.25 ^ 2 + 0.095 ^ 2) < 1.26`.
* Cauchy machine: `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`
  (`Mathlib/Analysis/Complex/Liouville.lean`): from a norm bound `C` on the
  boundary sphere of `ball c R`, `‖deriv f c‖ ≤ C / R` (no completeness
  hypothesis needed).
* Restriction: `DiffContOnCl.mono`
  (`Mathlib/Analysis/Calculus/DiffContOnCl.lean`).

What is banked here (sorry-free):

1. `deriv_bound_of_sphere_sup_on_ball`: local Cauchy-estimate rule — a sup
   bound `B` on `closedBall c R` gives `‖deriv f w‖ ≤ B / r` at any off-center
   `w` with `‖w - c‖ + r ≤ R`.
2. `deriv_bound_rat_of_sup`: the same rule with rational endpoints
   (`qR`, `qr`, `qB : ℚ`, cast to `ℝ`). No `Float` anywhere.
3. `R00_deriv_bound_of_sup`: first-cell (`R00`, outer tier shape) theorem —
   every `w` in the `R00` rectangle satisfies `‖deriv f w‖ ≤ 2 * qB` under an
   explicit sup hypothesis on `ball R00c 2`.
4. `R00_deriv_meets_outer_tier` / `R00_deriv_tier_threshold`: margin vs the
   leaf tier `M = 0.05` — the banked bound meets the tier exactly at
   `qB = 1 / 40`.

Scope note: `f` is general (`ℂ → ℂ`) and the sup hypothesis is explicit.
Specializing `f := xiShifted` needs the uniform `ξ`-sup enclosure on
`ball R00c 2` (rigorous `ξ`-bounds, absent from Mathlib — the missing lemma,
see residual), plus the one-line rewrite `R00Rect ↔ R00.mem` once
`central_cover_assembly` is imported (deliberately not imported here to keep
this lane self-contained and cycle-safe).
-/

open Metric Set

/-- **Local Cauchy estimate (disc version).** If `f` is complex-differentiable
with continuous extension to the closure of `ball c R`, and `‖f‖ ≤ B` on the
closed ball, then at any `w` with margin `‖w - c‖ + r ≤ R`,
`‖deriv f w‖ ≤ B / r`.

Proof: restrict to `ball w r` (`DiffContOnCl.mono`), transport the sup bound
to `sphere w r` (triangle inequality), and apply
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` at center `w`. -/
theorem deriv_bound_of_sphere_sup_on_ball {f : ℂ → ℂ} {c : ℂ} {R B : ℝ}
    (hd : DiffContOnCl ℂ f (ball c R))
    (hB : ∀ z ∈ closedBall c R, ‖f z‖ ≤ B)
    {w : ℂ} {r : ℝ} (hr : 0 < r) (hw : ‖w - c‖ + r ≤ R) :
    ‖deriv f w‖ ≤ B / r := by
  have hball : ball w r ⊆ ball c R := by
    intro z hz
    have hzw : ‖z - w‖ < r := by rw [← dist_eq_norm]; exact hz
    show dist z c < R
    calc dist z c ≤ dist z w + dist w c := dist_triangle _ _ _
      _ = ‖z - w‖ + ‖w - c‖ := by rw [dist_eq_norm, dist_eq_norm]
      _ < r + ‖w - c‖ := add_lt_add_of_lt_of_le hzw le_rfl
      _ = ‖w - c‖ + r := add_comm _ _
      _ ≤ R := hw
  have hsph : sphere w r ⊆ closedBall c R := by
    intro z hz
    have h1 : ‖z - w‖ = r := by rw [← dist_eq_norm]; exact hz
    show dist z c ≤ R
    calc dist z c = ‖(z - w) + (w - c)‖ := by rw [dist_eq_norm]; congr 1; abel
      _ ≤ ‖z - w‖ + ‖w - c‖ := norm_add_le _ _
      _ = r + ‖w - c‖ := by rw [h1]
      _ = ‖w - c‖ + r := add_comm _ _
      _ ≤ R := hw
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr (hd.mono hball)
    (fun z hz => hB z (hsph hz))

/-- **Rational-endpoint wrapper.** Same Cauchy rule with `ℚ` endpoints
(`qR` outer radius, `qr` margin, `qB` sup bound). No `Float`. -/
theorem deriv_bound_rat_of_sup {f : ℂ → ℂ} {c : ℂ} {qR qB qr : ℚ}
    (hr : 0 < qr)
    (hd : DiffContOnCl ℂ f (ball c (qR : ℝ)))
    (hB : ∀ z ∈ closedBall c (qR : ℝ), ‖f z‖ ≤ (qB : ℝ))
    {w : ℂ} (hw : ‖w - c‖ + (qr : ℝ) ≤ (qR : ℝ)) :
    ‖deriv f w‖ ≤ ((qB / qr : ℚ) : ℝ) := by
  have hr' : (0 : ℝ) < (qr : ℝ) := by exact_mod_cast hr
  have h := deriv_bound_of_sphere_sup_on_ball hd hB hr' hw
  rwa [Rat.cast_div]

/-- `R00` center `(-8.75, 0.105)`, matching `Rect2D.center`
(`rh_certificate_infra.lean:25-26`) at `(-10, -7.5, 0.01, 0.2)`. -/
def R00c : ℂ := ⟨-8.75, 0.105⟩

/-- `R00` rectangle membership, matching `Rect2D.mem`
(`rh_certificate_infra.lean:21-22`) at `R00`'s coordinates
(`central_cover_assembly.lean:1132-1134`). -/
def R00Rect (w : ℂ) : Prop :=
  (-10 : ℝ) ≤ w.re ∧ w.re ≤ -7.5 ∧ (0.01 : ℝ) ≤ w.im ∧ w.im ≤ 0.2

/-- Every point of the `R00` rectangle is within `1.26` of `R00c`
(half-diagonal `√(1.25 ^ 2 + 0.095 ^ 2) = √1.571525 ≤ 1.26`, cf.
`R00_radius_eq` / `R00_radius_lt`). -/
theorem R00Rect_norm_sub_le (w : ℂ) (hw : R00Rect w) : ‖w - R00c‖ ≤ 1.26 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have hcre : R00c.re = (-8.75 : ℝ) := rfl
  have hcim : R00c.im = (0.105 : ℝ) := rfl
  have hre : (w - R00c).re = w.re + 8.75 := by
    rw [Complex.sub_re, hcre]; ring
  have him : (w - R00c).im = w.im - 0.105 := by
    rw [Complex.sub_im, hcim]
  have ha : (w.re + 8.75) ^ 2 ≤ (1.25 : ℝ) ^ 2 := by
    have h1 : |w.re + 8.75| ≤ 1.25 := by
      rw [abs_le]; constructor <;> linarith
    calc (w.re + 8.75) ^ 2 = |w.re + 8.75| ^ 2 := (sq_abs _).symm
      _ ≤ (1.25 : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hb : (w.im - 0.105) ^ 2 ≤ (0.095 : ℝ) ^ 2 := by
    have h1 : |w.im - 0.105| ≤ 0.095 := by
      rw [abs_le]; constructor <;> linarith
    calc (w.im - 0.105) ^ 2 = |w.im - 0.105| ^ 2 := (sq_abs _).symm
      _ ≤ (0.095 : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hnum : (1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2 ≤ (1.26 : ℝ) ^ 2 := by norm_num
  have hsq : ‖w - R00c‖ ^ 2 ≤ (1.26 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    have e1 : (w.re + 8.75) * (w.re + 8.75) = (w.re + 8.75) ^ 2 := by ring
    have e2 : (w.im - 0.105) * (w.im - 0.105) = (w.im - 0.105) ^ 2 := by ring
    rw [e1, e2]; linarith [ha, hb, hnum]
  have hnn : (0 : ℝ) ≤ ‖w - R00c‖ := norm_nonneg _
  calc ‖w - R00c‖ = Real.sqrt (‖w - R00c‖ ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((1.26 : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 1.26 := Real.sqrt_sq (by norm_num)

/-- The `R00` rectangle lies in `closedBall R00c 1.26`. -/
theorem R00Rect_subset_closedBall (w : ℂ) (hw : R00Rect w) :
    w ∈ closedBall R00c 1.26 := by
  rw [mem_closedBall, dist_eq_norm]
  exact R00Rect_norm_sub_le w hw

/-- **First-cell theorem (`R00`, outer-tier shape).** Under an explicit
rational sup hypothesis on `ball R00c 2`, every `w` in the `R00` rectangle
satisfies `‖deriv f w‖ ≤ 2 * qB` (margin `r = 1/2`: `1.26 + 1/2 = 1.76 ≤ 2`). -/
theorem R00_deriv_bound_of_sup {f : ℂ → ℂ} {qB : ℚ}
    (hd : DiffContOnCl ℂ f (ball R00c ((2 : ℚ) : ℝ)))
    (hB : ∀ z ∈ closedBall R00c ((2 : ℚ) : ℝ), ‖f z‖ ≤ (qB : ℝ))
    {w : ℂ} (hw : R00Rect w) :
    ‖deriv f w‖ ≤ 2 * (qB : ℝ) := by
  have hsub : ‖w - R00c‖ ≤ 1.26 := R00Rect_norm_sub_le w hw
  have e1 : ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) := by norm_num
  have e2 : ((2 : ℚ) : ℝ) = (2 : ℝ) := by norm_num
  have hw' : ‖w - R00c‖ + ((1 / 2 : ℚ) : ℝ) ≤ ((2 : ℚ) : ℝ) := by
    rw [e1, e2]; linarith
  have h := deriv_bound_rat_of_sup (f := f) (c := R00c) (qR := 2) (qr := 1 / 2)
    (qB := qB) (by norm_num) hd hB hw'
  rw [Rat.cast_div, e1] at h
  have hval : (qB : ℝ) / (1 / 2 : ℝ) = 2 * (qB : ℝ) := by ring
  rw [hval] at h
  exact h

/-- **Margin vs the `R00` leaf tier `M = 0.05`.** The banked bound `2 * qB`
meets the tier whenever `qB ≤ 1 / 40`. -/
theorem R00_deriv_meets_outer_tier (qB : ℚ) (hB : qB ≤ 1 / 40) :
    2 * ((qB : ℚ) : ℝ) ≤ (0.05 : ℝ) := by
  have h3 : ((qB : ℚ) : ℝ) ≤ ((1 / 40 : ℚ) : ℝ) := by exact_mod_cast hB
  have h2 : ((1 / 40 : ℚ) : ℝ) = (1 / 40 : ℝ) := by norm_num
  rw [h2] at h3
  linarith

/-- Threshold equality: at `qB = 1 / 40` the banked bound is exactly the tier
(zero margin; `qB < 1 / 40` gives positive margin). -/
theorem R00_deriv_tier_threshold :
    2 * (((1 / 40 : ℚ)) : ℝ) = (0.05 : ℝ) := by norm_num

#print axioms deriv_bound_of_sphere_sup_on_ball
#print axioms deriv_bound_rat_of_sup
#print axioms R00Rect_norm_sub_le
#print axioms R00Rect_subset_closedBall
#print axioms R00_deriv_bound_of_sup
#print axioms R00_deriv_meets_outer_tier
#print axioms R00_deriv_tier_threshold

/-!
## Door-3 ξ-sup bridge (deriv-lane tail): per-factor enclosures on `closedBall R00c 2`

Goal (missing lemma): uniform `‖xiShifted z‖ ≤ qB` with `qB ≤ 1 / 40` on
`closedBall R00c 2`, to discharge the sup hypothesis of `R00_deriv_bound_of_sup`.

Import decision (deliberate, verified cycle-safe but build-costly): `central_cover_assembly`
imports `Mathlib + riemann_hypothesis + rh_certificate_infra` (lines 1-3) and nothing
imports `door3_deriv_certs` (only `lakefile.lean` registers it as a `RootScratch` root),
so importing the assembly would be cycle-safe — but it would drag the whole
`riemann_hypothesis` build into this lane and re-expose the totalized-`Gamma` /
`riemannZeta` boundary poles documented at `central_cover_assembly.lean:13-24,774-802`.
This tail therefore stays import-free (`import Mathlib` only) and banks the ξ-factor
shapes **explicitly**, quoting the read-only definitions:

* `shiftedS z = (1 / 2 : ℂ) + I * z` (`rh_certificate_infra.lean:159-161`),
* `fPoly s = (1 / 2 : ℂ) * s * (s - 1)` (`rh_certificate_infra.lean:163-165`),
* `classicalXi s = fPoly s * fPi s * fGamma s * fZeta s`
  (`rh_certificate_infra.lean:179-181`),
* `xiShifted z = classicalXi (shiftedS z)` (`rh_certificate_infra.lean:183-185`,
  `riemann hypothesis.lean:228-229`),
* `xiShiftedEntire z = 1 / 2 - (z ^ 2 + 1 / 4) / 2 * completedRiemannZeta₀ ((1/2:ℂ)+I*z)`
  (`central_cover_assembly.lean:821-824`).

Banked here (sorry-free): `R00c_norm_le`, `mem_closedBall_R00c_norm_le`,
`poly_prefactor_sup_on_ball` + `poly_prefactor_half_sup_on_ball` (entire-shape prefactor
`(z ^ 2 + 1 / 4) / 2 ≤ 58.02`), `shiftedS_norm_sup_on_ball`,
`shiftedS_sub_one_norm_sup_on_ball`, `fPoly_shape_eq`,
`shiftedS_poly_shape_sup_on_ball` (`fPoly ∘ shiftedS` shape `≤ 63.4`), generic two- and
four-factor sup composition, `R00_poly_times_remaining_gap`, and the numeric gap
`R00_remaining_threshold_for_tier` (with the poly factor banked at `63.4`, the remaining
`fPi * fGamma * fZeta` product needs sup `≤ 0.0004` to reach `1 / 40`).

Residual: rigorous `‖fPi‖`, `‖fGamma‖`, `‖fZeta‖` sups on the `s`-image of the ball
(`s.re ∈ [-1.61, 2.40]`, `s.im ∈ [-10.75, -6.75]`) need Stirling / `ζ` majorants absent
from Mathlib. Note the triangle route via `xiShiftedEntire` (`1 / 2 + 58.02 * R`) can
never reach `1 / 40` (the `1 / 2` constant alone exceeds it); the four-factor product
route above is the live one.
-/

/-- `‖R00c‖ ≤ 8.76` (`‖R00c‖ ^ 2 = 76.573525 ≤ 8.76 ^ 2`). -/
theorem R00c_norm_le : ‖R00c‖ ≤ 8.76 := by
  have hsq : ‖R00c‖ ^ 2 ≤ (8.76 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have h1 : R00c.re = (-8.75 : ℝ) := rfl
    have h2 : R00c.im = (0.105 : ℝ) := rfl
    rw [h1, h2]
    norm_num
  have hnn : (0 : ℝ) ≤ ‖R00c‖ := norm_nonneg _
  calc ‖R00c‖ = Real.sqrt (‖R00c‖ ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((8.76 : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 8.76 := Real.sqrt_sq (by norm_num)

/-- Every `z ∈ closedBall R00c 2` satisfies `‖z‖ ≤ 10.76`. -/
theorem mem_closedBall_R00c_norm_le {z : ℂ} (hz : z ∈ closedBall R00c 2) :
    ‖z‖ ≤ 10.76 := by
  rw [mem_closedBall, dist_eq_norm] at hz
  calc ‖z‖ = ‖(z - R00c) + R00c‖ := by congr 1; abel
    _ ≤ ‖z - R00c‖ + ‖R00c‖ := norm_add_le _ _
    _ ≤ 2 + 8.76 := add_le_add hz R00c_norm_le
    _ = 10.76 := by norm_num

/-- Entire-shape polynomial prefactor: `‖z ^ 2 + 1 / 4‖ ≤ 116.03` on the ball
(`10.76 ^ 2 + 1 / 4 = 116.0276 ≤ 116.03`). -/
theorem poly_prefactor_sup_on_ball (z : ℂ) (hz : z ∈ closedBall R00c 2) :
    ‖z ^ 2 + (1 / 4 : ℂ)‖ ≤ 116.03 := by
  have hn : ‖z‖ ≤ 10.76 := mem_closedBall_R00c_norm_le hz
  have h2 : ‖z ^ 2‖ ≤ (10.76 : ℝ) ^ 2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  have h14 : ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) := by
    simp [Complex.norm_div, Complex.norm_ofNat]
  have hv : (10.76 : ℝ) ^ 2 + 1 / 4 ≤ 116.03 := by norm_num
  calc ‖z ^ 2 + (1 / 4 : ℂ)‖ ≤ ‖z ^ 2‖ + ‖(1 / 4 : ℂ)‖ := norm_add_le _ _
    _ ≤ (10.76 : ℝ) ^ 2 + 1 / 4 := by rw [h14]; exact add_le_add h2 le_rfl
    _ ≤ 116.03 := hv

/-- Halved entire-shape prefactor: `‖(z ^ 2 + 1 / 4) / 2‖ ≤ 58.02` on the ball. -/
theorem poly_prefactor_half_sup_on_ball (z : ℂ) (hz : z ∈ closedBall R00c 2) :
    ‖(z ^ 2 + (1 / 4 : ℂ)) / 2‖ ≤ 58.02 := by
  have h := poly_prefactor_sup_on_ball z hz
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by simp [Complex.norm_ofNat]
  rw [Complex.norm_div, h2]
  linarith

/-- `s`-coordinate sup: `‖(1 / 2 : ℂ) + I * z‖ ≤ 11.26` on the ball
(`0.5 + 10.76`, matching `shiftedS`). -/
theorem shiftedS_norm_sup_on_ball (z : ℂ) (hz : z ∈ closedBall R00c 2) :
    ‖(1 / 2 : ℂ) + Complex.I * z‖ ≤ 11.26 := by
  have hn : ‖z‖ ≤ 10.76 := mem_closedBall_R00c_norm_le hz
  have hIz : ‖Complex.I * z‖ = ‖z‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have h12 : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    simp [Complex.norm_div, Complex.norm_ofNat]
  calc ‖(1 / 2 : ℂ) + Complex.I * z‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖Complex.I * z‖ :=
        norm_add_le _ _
    _ = 1 / 2 + ‖z‖ := by rw [hIz, h12]
    _ ≤ 1 / 2 + 10.76 := add_le_add le_rfl hn
    _ = 11.26 := by norm_num

/-- Shifted `s - 1` sup: `‖((1 / 2 : ℂ) + I * z) - 1‖ ≤ 11.26` on the ball. -/
theorem shiftedS_sub_one_norm_sup_on_ball (z : ℂ) (hz : z ∈ closedBall R00c 2) :
    ‖((1 / 2 : ℂ) + Complex.I * z) - 1‖ ≤ 11.26 := by
  have hn : ‖z‖ ≤ 10.76 := mem_closedBall_R00c_norm_le hz
  have hIz : ‖Complex.I * z‖ = ‖z‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have h12 : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    simp [Complex.norm_div, Complex.norm_ofNat]
  have e : ((1 / 2 : ℂ) + Complex.I * z) - 1 = Complex.I * z - (1 / 2 : ℂ) := by
    ring
  rw [e]
  calc ‖Complex.I * z - (1 / 2 : ℂ)‖ ≤ ‖Complex.I * z‖ + ‖(1 / 2 : ℂ)‖ :=
        norm_sub_le _ _
    _ = ‖z‖ + 1 / 2 := by rw [hIz, h12]
    _ ≤ 10.76 + 1 / 2 := add_le_add hn le_rfl
    _ = 11.26 := by norm_num

/-- Shape match: `s * (s - 1) / 2 = (1 / 2 : ℂ) * s * (s - 1)` (the `fPoly` form). -/
theorem fPoly_shape_eq (s : ℂ) : s * (s - 1) / 2 = (1 / 2 : ℂ) * s * (s - 1) := by
  ring

/-- `fPoly ∘ shiftedS` shape sup: `‖s * (s - 1) / 2‖ ≤ 63.4` on the ball
(`11.26 * 11.26 / 2 = 63.3938 ≤ 63.4`). -/
theorem shiftedS_poly_shape_sup_on_ball (z : ℂ) (hz : z ∈ closedBall R00c 2) :
    ‖((1 / 2 : ℂ) + Complex.I * z) * (((1 / 2 : ℂ) + Complex.I * z) - 1) / 2‖ ≤
      63.4 := by
  have hs := shiftedS_norm_sup_on_ball z hz
  have hs1 := shiftedS_sub_one_norm_sup_on_ball z hz
  have hmul : ‖(1 / 2 : ℂ) + Complex.I * z‖ *
      ‖((1 / 2 : ℂ) + Complex.I * z) - 1‖ ≤ 11.26 * 11.26 :=
    mul_le_mul hs hs1 (norm_nonneg _) (by norm_num)
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by simp [Complex.norm_ofNat]
  have hv : (11.26 : ℝ) * 11.26 / 2 ≤ 63.4 := by norm_num
  rw [Complex.norm_div, norm_mul, h2]
  linarith

/-- Generic two-factor sup composition (upper-bound mirror of
`TailProofEngine.prod_four_ge_of_ge` in `rh_certificate_infra.lean`). -/
theorem norm_sup_mul_of_factor_sups {S : Set ℂ} {a b : ℂ → ℂ} {A B : ℝ}
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (ha : ∀ z ∈ S, ‖a z‖ ≤ A) (hb : ∀ z ∈ S, ‖b z‖ ≤ B) (z : ℂ) (hz : z ∈ S) :
    ‖a z * b z‖ ≤ A * B := by
  have _hB := hB0
  rw [norm_mul]
  exact mul_le_mul (ha z hz) (hb z hz) (norm_nonneg _) hA0

/-- Generic four-factor sup composition (upper-bound mirror of
`TailProofEngine.prod_four_ge_of_ge` in `rh_certificate_infra.lean`). -/
theorem norm_sup_four_mul_of_factor_sups {S : Set ℂ} {a b c d : ℂ → ℂ}
    {A B C D : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C) (hD0 : 0 ≤ D)
    (ha : ∀ z ∈ S, ‖a z‖ ≤ A) (hb : ∀ z ∈ S, ‖b z‖ ≤ B)
    (hc : ∀ z ∈ S, ‖c z‖ ≤ C) (hd : ∀ z ∈ S, ‖d z‖ ≤ D) (z : ℂ) (hz : z ∈ S) :
    ‖a z * b z * c z * d z‖ ≤ A * B * C * D := by
  have h1 : ‖a z‖ * ‖b z‖ ≤ A * B :=
    mul_le_mul (ha z hz) (hb z hz) (norm_nonneg _) hA0
  have hAB : 0 ≤ A * B := mul_nonneg hA0 hB0
  have h2 : ‖a z‖ * ‖b z‖ * ‖c z‖ ≤ A * B * C :=
    mul_le_mul h1 (hc z hz) (norm_nonneg _) hAB
  have hABC : 0 ≤ A * B * C := mul_nonneg hAB hC0
  have h3 : ‖a z‖ * ‖b z‖ * ‖c z‖ * ‖d z‖ ≤ A * B * C * D :=
    mul_le_mul h2 (hd z hz) (norm_nonneg _) hABC
  have _hD := hD0
  calc ‖a z * b z * c z * d z‖
      = ‖a z‖ * ‖b z‖ * ‖c z‖ * ‖d z‖ := by rw [norm_mul, norm_mul, norm_mul]
    _ ≤ A * B * C * D := h3

/-- Banked poly factor times a general remaining factor: if the rest of the ξ product
has sup `R` on the ball, the poly-inclusive product has sup `63.4 * R`. -/
theorem R00_poly_times_remaining_gap {r : ℂ → ℂ} {R : ℝ} (hR0 : 0 ≤ R)
    (hr : ∀ z ∈ closedBall R00c 2, ‖r z‖ ≤ R) (z : ℂ)
    (hz : z ∈ closedBall R00c 2) :
    ‖(((1 / 2 : ℂ) + Complex.I * z) * (((1 / 2 : ℂ) + Complex.I * z) - 1) / 2) *
      r z‖ ≤ 63.4 * R := by
  have hpoly : ∀ w ∈ closedBall R00c 2,
      ‖((1 / 2 : ℂ) + Complex.I * w) * (((1 / 2 : ℂ) + Complex.I * w) - 1) / 2‖ ≤
        63.4 :=
    fun w hw => shiftedS_poly_shape_sup_on_ball w hw
  exact norm_sup_mul_of_factor_sups (by norm_num) hR0 hpoly hr z hz

/-- Quantified product gap: with the poly factor banked at `63.4`, reaching the outer
tier (`63.4 * R ≤ 1 / 40`) forces the remaining `fPi * fGamma * fZeta` product sup
`R ≤ 0.0004` (`63.4 * 0.0004 = 0.02536 > 1 / 40`). -/
theorem R00_remaining_threshold_for_tier {R : ℝ} (h : 63.4 * R ≤ 1 / 40) :
    R ≤ 0.0004 := by
  by_contra hc
  push_neg at hc
  have hpos : (0 : ℝ) < 63.4 := by norm_num
  have h2 : (63.4 : ℝ) * 0.0004 < 63.4 * R := mul_lt_mul_of_pos_left hc hpos
  norm_num at h2
  linarith

#print axioms R00c_norm_le
#print axioms mem_closedBall_R00c_norm_le
#print axioms poly_prefactor_sup_on_ball
#print axioms poly_prefactor_half_sup_on_ball
#print axioms shiftedS_norm_sup_on_ball
#print axioms shiftedS_sub_one_norm_sup_on_ball
#print axioms fPoly_shape_eq
#print axioms shiftedS_poly_shape_sup_on_ball
#print axioms norm_sup_mul_of_factor_sups
#print axioms norm_sup_four_mul_of_factor_sups
#print axioms R00_poly_times_remaining_gap
#print axioms R00_remaining_threshold_for_tier

/-!
## Door-3 s-image factor sups (deriv-lane tail: zeta/Gamma/pi)

Quoted read-only shapes (`rh_certificate_infra.lean:159-181`):

* `shiftedS z = (1 / 2 : ℂ) + I * z`,
* `fPoly s = (1 / 2 : ℂ) * s * (s - 1)`,
* `fPi s = (Real.pi : ℂ) ^ (-(s / 2))`,
* `fGamma s = Complex.Gamma (s / 2)`,
* `fZeta s = riemannZeta s`,
* `classicalXi s = fPoly s * fPi s * fGamma s * fZeta s`.

The `s`-image of `closedBall R00c 2` is banked here as the rectangle
`s.re ∈ [-1.61, 2.40]`, `s.im ∈ [-10.75, -6.75]` (from `R00c = (-8.75, 0.105)`,
radius `2`: `z.re ∈ [-10.75, -6.75]`, `z.im ∈ [-1.895, 2.105]`, so
`s.re = 1 / 2 - z.im ∈ [-1.605, 2.395]`, `s.im = z.re`).

Banked here (sorry-free): `fPi` cpow majorant `≤ 4` on the `s`-image
(elementary: `‖π ^ (-(s/2))‖ = π ^ (-s.re/2) ≤ π ^ 0.805 ≤ π ≤ 4`),
explicit conditional props `GammaSupCond` / `ZetaSupCond` for the two
out-of-reach factors (Stirling / `ζ` majorants absent from Mathlib),
the four-factor product sup `63.4 * 4 * G * Z`, the quantified gap
`G * Z ≤ 0.0001`, and the conditional deriv closure feeding
`norm_sup_four_mul_of_factor_sups` + `deriv_bound_of_sphere_sup_on_ball`.
-/

/-- `shiftedS` shape (quote of `TailProofEngine.shiftedS`). -/
noncomputable def shiftedS_shape (z : ℂ) : ℂ := (1 / 2 : ℂ) + Complex.I * z

/-- `fPi` shape (quote of `TailProofEngine.fPi`). -/
noncomputable def fPi_shape (s : ℂ) : ℂ := (Real.pi : ℂ) ^ (-(s / 2))

/-- `fGamma` shape (quote of `TailProofEngine.fGamma`). -/
noncomputable def fGamma_shape (s : ℂ) : ℂ := Complex.Gamma (s / 2)

/-- `fZeta` shape (quote of `TailProofEngine.fZeta`). -/
noncomputable def fZeta_shape (s : ℂ) : ℂ := riemannZeta s

/-- `s`-image rectangle for `closedBall R00c 2`. -/
def sImageRect (s : ℂ) : Prop :=
  (-1.61 : ℝ) ≤ s.re ∧ s.re ≤ 2.40 ∧ (-10.75 : ℝ) ≤ s.im ∧ s.im ≤ (-6.75 : ℝ)

/-- `(shiftedS_shape z).re = 1 / 2 - z.im`. -/
theorem shiftedS_shape_re_eq (z : ℂ) : (shiftedS_shape z).re = 1 / 2 - z.im := by
  unfold shiftedS_shape
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  have h12 : ((1 / 2 : ℂ)).re = (1 / 2 : ℝ) := by simp [Complex.div_ofNat]
  have h12i : ((1 / 2 : ℂ)).im = (0 : ℝ) := by simp [Complex.div_ofNat]
  rw [h12]
  ring

/-- `(shiftedS_shape z).im = z.re`. -/
theorem shiftedS_shape_im_eq (z : ℂ) : (shiftedS_shape z).im = z.re := by
  unfold shiftedS_shape
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  have h12i : ((1 / 2 : ℂ)).im = (0 : ℝ) := by simp
  rw [h12i]
  ring

/-- `z.re` bounds on `closedBall R00c 2`. -/
theorem mem_closedBall_R00c_re_bounds {z : ℂ} (hz : z ∈ closedBall R00c 2) :
    (-10.75 : ℝ) ≤ z.re ∧ z.re ≤ (-6.75 : ℝ) := by
  have hdist : ‖z - R00c‖ ≤ 2 := by
    rw [mem_closedBall, dist_eq_norm] at hz
    exact hz
  have hre : |(z - R00c).re| ≤ 2 := le_trans (Complex.abs_re_le_norm _) hdist
  have heq : (z - R00c).re = z.re + 8.75 := by
    have hcre : R00c.re = (-8.75 : ℝ) := rfl
    rw [Complex.sub_re, hcre]
    ring
  rw [heq, abs_le] at hre
  constructor <;> linarith

/-- Loose `z.im` bounds on `closedBall R00c 2` (true `[-1.895, 2.105]`
rounded out to `[-1.90, 2.11]` so the `s.re` image lands exactly on
`[-1.61, 2.40]`). -/
theorem mem_closedBall_R00c_im_bounds_loose {z : ℂ} (hz : z ∈ closedBall R00c 2) :
    (-1.90 : ℝ) ≤ z.im ∧ z.im ≤ 2.11 := by
  have hdist : ‖z - R00c‖ ≤ 2 := by
    rw [mem_closedBall, dist_eq_norm] at hz
    exact hz
  have him : |(z - R00c).im| ≤ 2 := le_trans (Complex.abs_im_le_norm _) hdist
  have heq : (z - R00c).im = z.im - 0.105 := by
    have hcim : R00c.im = (0.105 : ℝ) := rfl
    rw [Complex.sub_im, hcim]
  rw [heq, abs_le] at him
  constructor <;> linarith

/-- The `shiftedS` shape maps the ball into the `s`-image rectangle. -/
theorem shiftedS_shape_mem_sImage_of_mem_ball {z : ℂ}
    (hz : z ∈ closedBall R00c 2) : sImageRect (shiftedS_shape z) := by
  obtain ⟨hre_lo, hre_hi⟩ := mem_closedBall_R00c_re_bounds hz
  obtain ⟨him_lo, him_hi⟩ := mem_closedBall_R00c_im_bounds_loose hz
  have hre := shiftedS_shape_re_eq z
  have him := shiftedS_shape_im_eq z
  unfold sImageRect
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre]; linarith
  · rw [hre]; linarith
  · rw [him]; linarith
  · rw [him]; linarith

/-- Norm of the `fPi` shape: `‖π ^ (-(s/2))‖ = π ^ (-s.re/2)`. -/
theorem fPi_shape_norm_eq (s : ℂ) : ‖fPi_shape s‖ = Real.pi ^ (-(s.re) / 2) := by
  unfold fPi_shape
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have hre : (-(s / 2 : ℂ)).re = -(s.re) / 2 := by
    have hdiv : ((s / 2 : ℂ)).re = s.re / 2 := by simp [Complex.div_ofNat]
    rw [Complex.neg_re, hdiv]
    ring
  rw [hre]

/-- `fPi` sup on the `s`-image: `‖fPi‖ ≤ 4`
(`e = -s.re/2 ≤ 0.805`, `π ^ e ≤ π ^ 0.805 ≤ π ^ 1 = π ≤ 4`). -/
theorem fPi_shape_sup_on_sImage (s : ℂ) (hs : sImageRect s) :
    ‖fPi_shape s‖ ≤ 4 := by
  obtain ⟨hlo, _, _, _⟩ := hs
  rw [fPi_shape_norm_eq]
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have he : -(s.re) / 2 ≤ (0.805 : ℝ) := by linarith
  have hle1 : Real.pi ^ (-(s.re) / 2) ≤ Real.pi ^ (0.805 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hpi1 he
  have hle2 : Real.pi ^ (0.805 : ℝ) ≤ Real.pi ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hpi1 (by norm_num)
  have h1 : Real.pi ^ (1 : ℝ) = Real.pi := Real.rpow_one _
  calc Real.pi ^ (-(s.re) / 2) ≤ Real.pi ^ (0.805 : ℝ) := hle1
    _ ≤ Real.pi ^ (1 : ℝ) := hle2
    _ = Real.pi := h1
    _ ≤ 4 := Real.pi_le_four

/-- Conditional `Gamma` sup on the `s`-image (Stirling majorant absent
from Mathlib; banked as an explicit hypothesis, no `sorry`). -/
def GammaSupCond (G : ℝ) : Prop :=
  ∀ s : ℂ, sImageRect s → ‖fGamma_shape s‖ ≤ G

/-- Conditional `zeta` sup on the `s`-image (`s.re` can be negative, so the
Dirichlet-eta head-plus-tail route needs a functional-equation-free rigorous
majorant absent from Mathlib; banked as an explicit hypothesis, no `sorry`). -/
def ZetaSupCond (Z : ℝ) : Prop :=
  ∀ s : ℂ, sImageRect s → ‖fZeta_shape s‖ ≤ Z

/-- Four-factor product sup on the ball from the banked poly `63.4`, the proved
`fPi ≤ 4`, and the two conditional sups. -/
theorem R00_xi_four_factor_sup_of_conds {G Z : ℝ} (hG0 : 0 ≤ G) (hZ0 : 0 ≤ Z)
    (hG : GammaSupCond G) (hZ : ZetaSupCond Z) (z : ℂ)
    (hz : z ∈ closedBall R00c 2) :
    ‖(((1 / 2 : ℂ) + Complex.I * z) * (((1 / 2 : ℂ) + Complex.I * z) - 1) / 2) *
      fPi_shape (shiftedS_shape z) * fGamma_shape (shiftedS_shape z) *
      fZeta_shape (shiftedS_shape z)‖ ≤ 63.4 * 4 * G * Z := by
  have hpoly : ∀ w ∈ closedBall R00c 2,
      ‖((1 / 2 : ℂ) + Complex.I * w) * (((1 / 2 : ℂ) + Complex.I * w) - 1) / 2‖ ≤
        63.4 :=
    fun w hw => shiftedS_poly_shape_sup_on_ball w hw
  have hpi : ∀ w ∈ closedBall R00c 2, ‖fPi_shape (shiftedS_shape w)‖ ≤ 4 :=
    fun w hw => fPi_shape_sup_on_sImage _ (shiftedS_shape_mem_sImage_of_mem_ball hw)
  have hg : ∀ w ∈ closedBall R00c 2, ‖fGamma_shape (shiftedS_shape w)‖ ≤ G :=
    fun w hw => hG _ (shiftedS_shape_mem_sImage_of_mem_ball hw)
  have hz2 : ∀ w ∈ closedBall R00c 2, ‖fZeta_shape (shiftedS_shape w)‖ ≤ Z :=
    fun w hw => hZ _ (shiftedS_shape_mem_sImage_of_mem_ball hw)
  exact norm_sup_four_mul_of_factor_sups (by norm_num) (by norm_num) hG0 hZ0
    hpoly hpi hg hz2 z hz

/-- Four-factor `ξ` shape at `z` (poly `s*(s-1)/2` form, matching
`fPoly_shape_eq`, times the three quoted shapes at `shiftedS_shape z`). -/
noncomputable def xiFourShapeAt (z : ℂ) : ℂ :=
  (((1 / 2 : ℂ) + Complex.I * z) * (((1 / 2 : ℂ) + Complex.I * z) - 1) / 2) *
    fPi_shape (shiftedS_shape z) * fGamma_shape (shiftedS_shape z) *
    fZeta_shape (shiftedS_shape z)

/-- `ξ`-shape sup on the ball under the two conditional sups. -/
theorem xiFourShapeAt_sup_of_conds {G Z : ℝ} (hG0 : 0 ≤ G) (hZ0 : 0 ≤ Z)
    (hG : GammaSupCond G) (hZ : ZetaSupCond Z) (z : ℂ)
    (hz : z ∈ closedBall R00c 2) : ‖xiFourShapeAt z‖ ≤ 63.4 * 4 * G * Z := by
  unfold xiFourShapeAt
  exact R00_xi_four_factor_sup_of_conds hG0 hZ0 hG hZ z hz

/-- Quantified product gap: reaching the outer tier forces `G * Z ≤ 0.0001`
(`63.4 * 4 * 0.0001 = 0.02536 > 1 / 40`). -/
theorem R00_PGZ_threshold_for_tier {G Z : ℝ} (h : 63.4 * 4 * G * Z ≤ 1 / 40) :
    G * Z ≤ 0.0001 := by
  by_contra hc
  push_neg at hc
  have hpos : (0 : ℝ) < 63.4 * 4 := by norm_num
  have h2 : (63.4 * 4 : ℝ) * 0.0001 < (63.4 * 4) * (G * Z) :=
    mul_lt_mul_of_pos_left hc hpos
  have e1 : (63.4 * 4 : ℝ) * 0.0001 = 0.02536 := by norm_num
  have e2 : (63.4 * 4 : ℝ) * (G * Z) = 63.4 * 4 * G * Z := by ring
  rw [e1, e2] at h2
  linarith

/-- Conditional deriv bound for the four-factor `ξ` shape (real-`B` Cauchy
rule with margin `r = 1 / 2`). -/
theorem R00_deriv_bound_of_xi_conds {G Z : ℝ} (hG0 : 0 ≤ G) (hZ0 : 0 ≤ Z)
    (hG : GammaSupCond G) (hZ : ZetaSupCond Z)
    (hd : DiffContOnCl ℂ xiFourShapeAt (ball R00c 2)) {w : ℂ} (hw : R00Rect w) :
    ‖deriv xiFourShapeAt w‖ ≤ 2 * (63.4 * 4 * G * Z) := by
  have hB : ∀ z ∈ closedBall R00c 2, ‖xiFourShapeAt z‖ ≤ 63.4 * 4 * G * Z :=
    fun z hz => xiFourShapeAt_sup_of_conds hG0 hZ0 hG hZ z hz
  have hsub : ‖w - R00c‖ ≤ 1.26 := R00Rect_norm_sub_le w hw
  have hw' : ‖w - R00c‖ + (1 / 2 : ℝ) ≤ 2 := by linarith
  have h := deriv_bound_of_sphere_sup_on_ball hd hB (show (0 : ℝ) < 1 / 2 by norm_num) hw'
  have heq : (63.4 * 4 * G * Z) / (1 / 2 : ℝ) = 2 * (63.4 * 4 * G * Z) := by ring
  rwa [heq] at h

/-- Conditional tier closure: `63.4 * 4 * G * Z ≤ 1 / 40` gives the leaf tier
`‖deriv‖ ≤ 0.05` on `R00`. -/
theorem R00_deriv_meets_tier_of_xi_conds {G Z : ℝ} (hG0 : 0 ≤ G) (hZ0 : 0 ≤ Z)
    (hG : GammaSupCond G) (hZ : ZetaSupCond Z)
    (hd : DiffContOnCl ℂ xiFourShapeAt (ball R00c 2)) {w : ℂ} (hw : R00Rect w)
    (hTier : 63.4 * 4 * G * Z ≤ 1 / 40) :
    ‖deriv xiFourShapeAt w‖ ≤ 0.05 := by
  have h := R00_deriv_bound_of_xi_conds hG0 hZ0 hG hZ hd hw
  linarith

#print axioms shiftedS_shape_re_eq
#print axioms shiftedS_shape_im_eq
#print axioms mem_closedBall_R00c_re_bounds
#print axioms mem_closedBall_R00c_im_bounds_loose
#print axioms shiftedS_shape_mem_sImage_of_mem_ball
#print axioms fPi_shape_norm_eq
#print axioms fPi_shape_sup_on_sImage
#print axioms R00_xi_four_factor_sup_of_conds
#print axioms xiFourShapeAt_sup_of_conds
#print axioms R00_PGZ_threshold_for_tier
#print axioms R00_deriv_bound_of_xi_conds
#print axioms R00_deriv_meets_tier_of_xi_conds

/-!
## Door-3 Gamma sup (deriv-lane tail: V4 Gamma bridge)

Banks `GammaSupCond 1.52` (Stirling-free, elementary): for `s ∈ sImageRect`
(`s.re ∈ [-1.61, 2.40]`, `s.im ∈ [-10.75, -6.75]`), `w := s / 2` has
`w.re ∈ [-0.805, 1.20]` and `‖w‖ ≥ 3.375` (from `|w.im| = |s.im| / 2 ≥ 3.375`),
so one recurrence step `Γ(w) = Γ(w + 1) / w` shifts into
`Re (w + 1) ∈ [0.195, 2.20]`, where the Euler-integral majorant
`‖Γ‖ ≤ Real.Gamma` plus convexity (`Real.Gamma ≤ 1` on `[1, 2]`) give
`Real.Gamma ≤ 5.13`; hence `‖Γ(w)‖ ≤ 5.13 / 3.375 = 1.52`.

Also banked: the quantified tier gap (`1.52` forces `Z ≤ 0.00007`, i.e. the
`ξ`-product route needs a zeta sup far below the true `|ζ| ~ 1` scale on this
rectangle) and the instantiated four-factor sup `385.472 * Z`.

Numerals used (all ≤ 6 digits): `1.52`, `5.13`, `3.375`, `0.195`, `2.20`,
`0.00007`, `385.472`, `0.02536`, `0.0001`.
-/

/-- Integral majorant `‖Γ z‖ ≤ Real.Gamma z.re` for `0 < z.re` (triangle
inequality for the Euler integral; same proof as
`DerivCauchyBridge.norm_Gamma_le_realGamma` in `central_cover_assembly.lean`,
restated here to keep this lane import-free). -/
theorem deriv_norm_Gamma_le_realGamma {z : ℂ} (hz : 0 < z.re) :
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

/-- Real-Gamma cap `Real.Gamma y ≤ 1` for `y ∈ [1, 2]` (convexity with
`Gamma 1 = Gamma 2 = 1`; same pattern as `realGamma_le_40_of_mem` in
`central_cover_assembly.lean`). -/
theorem deriv_realGamma_le_one_of_mem_12 {y : ℝ} (h1 : (1 : ℝ) ≤ y) (h2 : y ≤ 2) :
    Real.Gamma y ≤ 1 := by
  have hy1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have hy2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by norm_num)
  have ha : (0 : ℝ) ≤ 2 - y := by linarith
  have hb : (0 : ℝ) ≤ y - 1 := by linarith
  have hab : (2 - y) + (y - 1) = 1 := by ring
  have h := Real.convexOn_Gamma.2 hy1 hy2 ha hb hab
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
  have heq : (2 - y) * 1 + (y - 1) * 2 = y := by ring
  rw [heq] at h
  have hrhs : (2 - y) * 1 + (y - 1) * 1 = (1 : ℝ) := by ring
  rw [hrhs] at h
  exact h

/-- Real-Gamma cap `Real.Gamma x ≤ 5.13` for `x ∈ [0.195, 2.20]`: below `1`
shift up (`Γ(x) = Γ(x+1)/x ≤ 1/0.195 ≤ 5.13`), on `[1, 2]` use the unit cap,
above `2` shift down (`Γ(x) = (x-1)Γ(x-1) ≤ 1.2`). -/
theorem deriv_realGamma_le_513 {x : ℝ} (hlo : (0.195 : ℝ) ≤ x) (hhi : x ≤ 2.20) :
    Real.Gamma x ≤ 5.13 := by
  rcases le_total x 1 with hx1 | hx1
  · have hx_pos : (0 : ℝ) < x := by linarith
    have hne : x ≠ 0 := ne_of_gt hx_pos
    have hy1 : (1 : ℝ) ≤ x + 1 := by linarith
    have hy2 : x + 1 ≤ (2 : ℝ) := by linarith
    have h1 : Real.Gamma (x + 1) ≤ 1 := deriv_realGamma_le_one_of_mem_12 hy1 hy2
    have hadd := Real.Gamma_add_one hne
    rw [hadd] at h1
    have hfin : Real.Gamma x ≤ 1 / x := by
      rw [le_div_iff₀ hx_pos, mul_comm]
      exact h1
    have hfrac : (1 : ℝ) / x ≤ 5.13 := by
      have h1d : (1 : ℝ) / x ≤ 1 / 0.195 :=
        one_div_le_one_div_of_le (by norm_num) hlo
      have h2d : (1 : ℝ) / 0.195 ≤ 5.13 := by norm_num
      exact le_trans h1d h2d
    exact le_trans hfin hfrac
  · rcases le_total x 2 with hx2 | hx2
    · calc Real.Gamma x ≤ 1 := deriv_realGamma_le_one_of_mem_12 hx1 hx2
        _ ≤ 5.13 := by norm_num
    · have hm1 : (1 : ℝ) ≤ x - 1 := by linarith
      have hm2 : x - 1 ≤ (2 : ℝ) := by linarith
      have h1 : Real.Gamma (x - 1) ≤ 1 := deriv_realGamma_le_one_of_mem_12 hm1 hm2
      have hne : x - 1 ≠ 0 := ne_of_gt (by linarith)
      have hadd := Real.Gamma_add_one hne
      have hxeq : x - 1 + 1 = x := by ring
      rw [hxeq] at hadd
      have hpos : (0 : ℝ) ≤ Real.Gamma (x - 1) :=
        le_of_lt (Real.Gamma_pos_of_pos (by linarith))
      calc Real.Gamma x = (x - 1) * Real.Gamma (x - 1) := hadd
        _ ≤ 1.2 * 1 := mul_le_mul (by linarith) h1 hpos (by norm_num)
        _ = 1.2 := by norm_num
        _ ≤ 5.13 := by norm_num

/-- One-step recurrence solved for `Γ(w)`: `Γ(w) = Γ(w + 1) / w` for `w ≠ 0`
(from `Complex.Gamma_add_one`). -/
theorem deriv_Gamma_shift_one (w : ℂ) (hw : w ≠ 0) :
    Complex.Gamma w = Complex.Gamma (w + 1) / w := by
  have h := Complex.Gamma_add_one w hw
  rw [eq_div_iff_mul_eq hw, h]
  ring

/-- Denominator floor: `‖s / 2‖ ≥ 3.375` on `sImageRect`
(`|s.im| ≥ 6.75`, halved). Bounds taken explicitly so callers may `obtain`. -/
theorem deriv_shifted_half_norm_ge (s : ℂ) (_ : (-1.61 : ℝ) ≤ s.re) (_ : s.re ≤ 2.40)
    (_ : (-10.75 : ℝ) ≤ s.im) (him_hi : s.im ≤ (-6.75 : ℝ)) :
    (3.375 : ℝ) ≤ ‖s / 2‖ := by
  have him : |(s / 2).im| ≤ ‖s / 2‖ := Complex.abs_im_le_norm _
  have heim : (s / 2).im = s.im / 2 := Complex.div_ofNat_im _ _
  have habs : (6.75 : ℝ) ≤ |s.im| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have h2 : |(s / 2).im| = |s.im| / 2 := by
    rw [heim]
    simp [abs_div]
  linarith

/-- **Gamma sup on the `s`-image: `GammaSupCond 1.52`.** One recurrence step
moves `s / 2` (`Re ∈ [-0.805, 1.20]`) into `Re ∈ [0.195, 2.20]` where
`Real.Gamma ≤ 5.13`; dividing by `‖s / 2‖ ≥ 3.375` gives
`5.13 / 3.375 = 1.52`. -/
theorem deriv_GammaSupCond_152 : GammaSupCond 1.52 := by
  intro s hs
  obtain ⟨hre_lo, hre_hi, him_lo, him_hi⟩ := hs
  unfold fGamma_shape
  have hre2 : (s / 2).re = s.re / 2 := Complex.div_ofNat_re _ _
  have hsh : (s / 2 + 1).re = s.re / 2 + 1 := by
    rw [Complex.add_re, Complex.one_re, hre2]
  have hlo : (0.195 : ℝ) ≤ (s / 2 + 1).re := by rw [hsh]; linarith
  have hhi : (s / 2 + 1).re ≤ (2.20 : ℝ) := by rw [hsh]; linarith
  have hpos : (0 : ℝ) < (s / 2 + 1).re := by linarith
  have hle : ‖Complex.Gamma (s / 2 + 1)‖ ≤ Real.Gamma (s / 2 + 1).re :=
    deriv_norm_Gamma_le_realGamma hpos
  have hR : Real.Gamma (s / 2 + 1).re ≤ 5.13 := deriv_realGamma_le_513 hlo hhi
  have hG : ‖Complex.Gamma (s / 2 + 1)‖ ≤ 5.13 := le_trans hle hR
  have hden : (3.375 : ℝ) ≤ ‖s / 2‖ :=
    deriv_shifted_half_norm_ge s hre_lo hre_hi him_lo him_hi
  have hwpos : (0 : ℝ) < ‖s / 2‖ := lt_of_lt_of_le (by norm_num) hden
  have hwnez : s / 2 ≠ 0 := by
    intro hcon
    rw [hcon, norm_zero] at hden
    norm_num at hden
  have hrec : Complex.Gamma (s / 2) = Complex.Gamma (s / 2 + 1) / (s / 2) :=
    deriv_Gamma_shift_one _ hwnez
  have h152 : (1.52 : ℝ) = 5.13 / 3.375 := by norm_num
  rw [hrec, norm_div, h152, div_le_iff₀ hwpos]
  calc ‖Complex.Gamma (s / 2 + 1)‖ ≤ 5.13 := hG
    _ = 5.13 / 3.375 * 3.375 := by
        rw [div_mul_cancel₀ _ (by norm_num : (3.375 : ℝ) ≠ 0)]
    _ ≤ 5.13 / 3.375 * ‖s / 2‖ :=
        mul_le_mul_of_nonneg_left hden (by norm_num)
    _ = 5.13 / 3.375 * ‖s / 2‖ := rfl

/-- Quantified gap at `G = 1.52`: reaching `G * Z ≤ 0.0001` forces
`Z ≤ 0.00007` (`1.52 * 0.00007 = 0.0001064 > 0.0001`). -/
theorem deriv_GZ_gap_152 {Z : ℝ} (h : (1.52 : ℝ) * Z ≤ 0.0001) : Z ≤ 0.00007 := by
  by_contra hc
  push_neg at hc
  have h2 : (1.52 : ℝ) * 0.00007 < 1.52 * Z :=
    mul_lt_mul_of_pos_left hc (by norm_num)
  norm_num at h2
  linarith

/-- Tier gap with the banked Gamma numeral: the four-factor tier hypothesis
`63.4 * 4 * 1.52 * Z ≤ 1 / 40` forces `Z ≤ 0.00007` (via the banked
`R00_PGZ_threshold_for_tier`, i.e. `G * Z ≤ 0.0001`). -/
theorem deriv_tier_gap_of_gamma152 {Z : ℝ} (h : 63.4 * 4 * 1.52 * Z ≤ 1 / 40) :
    Z ≤ 0.00007 :=
  deriv_GZ_gap_152 (R00_PGZ_threshold_for_tier h)

/-- Four-factor `ξ`-shape sup with the banked Gamma numeral:
`‖xiFourShapeAt z‖ ≤ 385.472 * Z` (`63.4 * 4 * 1.52 = 385.472`) under any
`ZetaSupCond Z`. -/
theorem deriv_xiFourShapeAt_sup_of_gamma152 {Z : ℝ} (hZ0 : 0 ≤ Z) (hZ : ZetaSupCond Z)
    (z : ℂ) (hz : z ∈ closedBall R00c 2) : ‖xiFourShapeAt z‖ ≤ 385.472 * Z := by
  have h := xiFourShapeAt_sup_of_conds (G := 1.52) (Z := Z) (by norm_num) hZ0
    deriv_GammaSupCond_152 hZ z hz
  have e : (63.4 * 4 * 1.52 * Z : ℝ) = 385.472 * Z := by ring
  rwa [e] at h

#print axioms deriv_norm_Gamma_le_realGamma
#print axioms deriv_realGamma_le_one_of_mem_12
#print axioms deriv_realGamma_le_513
#print axioms deriv_Gamma_shift_one
#print axioms deriv_shifted_half_norm_ge
#print axioms deriv_GammaSupCond_152
#print axioms deriv_GZ_gap_152
#print axioms deriv_tier_gap_of_gamma152
#print axioms deriv_xiFourShapeAt_sup_of_gamma152

/-!
## Door-3 joint-sup / smaller-ball tier route (V5 bridge)

Tier route that does NOT factor through `G * Z ≤ 0.0001`:

* (a) JOINT sup: `JointGZSupCond J` bounds `‖fGamma * fZeta‖ ≤ J` directly on
  the `s`-image. With poly `63.4` and `fPi ≤ 4` banked above,
  `‖xiFourShapeAt z‖ ≤ 63.4 * 4 * J` on `closedBall R00c 2`, so the Cauchy
  rule (margin `r = 1/2`) gives `‖deriv‖ ≤ 2 * (63.4 * 4 * J)`. Tier
  `63.4 * 4 * J ≤ 1/40` forces `J ≤ 0.0001` (`R00_joint_threshold_for_tier`).
* (b) SMALLER BALL: triple `(center R00c, R = 1.5, r = 0.24)` with poly sup
  `57.89` (`10.76 ^ 2 / 2`). `B / r` is WORSE than the `R = 2` baseline
  (`57.89*4/0.24 > 63.4*4/0.5`, i.e. `964.83 > 507.2`), and the joint tier
  threshold tightens to `J ≤ 0.00006`. Smaller ball is a quantified no-go.
* (c) LOCALIZE: `sImageRect = Lo ∪ Hi` split at `s.re = 0.39/0.40` with
  per-piece joint sups combining to `max J1 J2`.

Verdict vs `0.05`: at the mpmath-suggestive scale `J = 0.03`,
`63.4*4*0.03 = 7.608 > 1/40` and the deriv bound `2*7.608 = 15.216 > 0.05`
(`R00_joint_dead_at_003`) — the joint route misses the tier by ~300x, the
smaller ball by ~600x. No route clears `0.05`; the factorization gap is
confirmed, not bypassed.

Numerals used (all ≤ 6 digits): `57.89`, `10.26`, `10.76`, `0.24`, `1.5`,
`0.40`, `0.39`, `0.0001`, `0.00006`, `0.03`, `0.02536`, `0.05789`.
-/

/-- Joint Gamma-zeta product sup on the `s`-image (no factorization). -/
def JointGZSupCond (J : ℝ) : Prop :=
  ∀ s : ℂ, sImageRect s → ‖fGamma_shape s * fZeta_shape s‖ ≤ J

/-- Poly-times-pi sup on the ball: `‖poly * fPi‖ ≤ 63.4 * 4`. -/
theorem R00_poly_pi_sup_on_ball (z : ℂ) (hz : z ∈ closedBall R00c 2) :
    ‖(((1 / 2 : ℂ) + Complex.I * z) * (((1 / 2 : ℂ) + Complex.I * z) - 1) / 2) *
      fPi_shape (shiftedS_shape z)‖ ≤ 63.4 * 4 := by
  have hpoly : ∀ w ∈ closedBall R00c 2,
      ‖((1 / 2 : ℂ) + Complex.I * w) * (((1 / 2 : ℂ) + Complex.I * w) - 1) / 2‖ ≤
        63.4 :=
    fun w hw => shiftedS_poly_shape_sup_on_ball w hw
  have hpi : ∀ w ∈ closedBall R00c 2, ‖fPi_shape (shiftedS_shape w)‖ ≤ 4 :=
    fun w hw => fPi_shape_sup_on_sImage _ (shiftedS_shape_mem_sImage_of_mem_ball hw)
  exact norm_sup_mul_of_factor_sups (by norm_num) (by norm_num) hpoly hpi z hz

/-- Joint four-factor `ξ` sup on the ball: `‖xiFourShapeAt z‖ ≤ 63.4 * 4 * J`
under `JointGZSupCond J` (regrouped as `(poly * pi) * (Gamma * zeta)`). -/
theorem R00_xi_joint_sup_of_conds {J : ℝ} (hJ0 : 0 ≤ J) (hJ : JointGZSupCond J)
    (z : ℂ) (hz : z ∈ closedBall R00c 2) :
    ‖xiFourShapeAt z‖ ≤ 63.4 * 4 * J := by
  have hPP : ∀ w ∈ closedBall R00c 2,
      ‖(((1 / 2 : ℂ) + Complex.I * w) * (((1 / 2 : ℂ) + Complex.I * w) - 1) / 2) *
        fPi_shape (shiftedS_shape w)‖ ≤ 63.4 * 4 :=
    fun w hw => R00_poly_pi_sup_on_ball w hw
  have hJJ : ∀ w ∈ closedBall R00c 2,
      ‖fGamma_shape (shiftedS_shape w) * fZeta_shape (shiftedS_shape w)‖ ≤ J :=
    fun w hw => hJ _ (shiftedS_shape_mem_sImage_of_mem_ball hw)
  have h := norm_sup_mul_of_factor_sups (by norm_num : (0 : ℝ) ≤ 63.4 * 4) hJ0
    hPP hJJ z hz
  have e : xiFourShapeAt z =
      ((((1 / 2 : ℂ) + Complex.I * z) * (((1 / 2 : ℂ) + Complex.I * z) - 1) / 2) *
        fPi_shape (shiftedS_shape z)) *
      (fGamma_shape (shiftedS_shape z) * fZeta_shape (shiftedS_shape z)) := by
    unfold xiFourShapeAt
    ring
  rw [e]
  exact h

/-- Joint tier threshold: `63.4 * 4 * J ≤ 1 / 40` forces `J ≤ 0.0001`
(`63.4 * 4 * 0.0001 = 0.02536 > 1 / 40`). -/
theorem R00_joint_threshold_for_tier {J : ℝ} (h : 63.4 * 4 * J ≤ 1 / 40) :
    J ≤ 0.0001 := by
  by_contra hc
  push_neg at hc
  have hpos : (0 : ℝ) < 63.4 * 4 := by norm_num
  have h2 : (63.4 * 4 : ℝ) * 0.0001 < (63.4 * 4) * J :=
    mul_lt_mul_of_pos_left hc hpos
  have e1 : (63.4 * 4 : ℝ) * 0.0001 = 0.02536 := by norm_num
  have e2 : (63.4 * 4 : ℝ) * J = 63.4 * 4 * J := by ring
  rw [e1, e2] at h2
  linarith

/-- Conditional deriv bound for the joint route (margin `r = 1 / 2`). -/
theorem R00_deriv_bound_of_joint_conds {J : ℝ} (hJ0 : 0 ≤ J)
    (hJ : JointGZSupCond J)
    (hd : DiffContOnCl ℂ xiFourShapeAt (ball R00c 2)) {w : ℂ} (hw : R00Rect w) :
    ‖deriv xiFourShapeAt w‖ ≤ 2 * (63.4 * 4 * J) := by
  have hB : ∀ z ∈ closedBall R00c 2, ‖xiFourShapeAt z‖ ≤ 63.4 * 4 * J :=
    fun z hz => R00_xi_joint_sup_of_conds hJ0 hJ z hz
  have hsub : ‖w - R00c‖ ≤ 1.26 := R00Rect_norm_sub_le w hw
  have hw' : ‖w - R00c‖ + (1 / 2 : ℝ) ≤ 2 := by linarith
  have h := deriv_bound_of_sphere_sup_on_ball hd hB (show (0 : ℝ) < 1 / 2 by norm_num) hw'
  have heq : (63.4 * 4 * J) / (1 / 2 : ℝ) = 2 * (63.4 * 4 * J) := by ring
  rwa [heq] at h

/-- Conditional joint tier closure: `63.4 * 4 * J ≤ 1 / 40` gives `‖deriv‖ ≤ 0.05`. -/
theorem R00_deriv_meets_tier_of_joint_conds {J : ℝ} (hJ0 : 0 ≤ J)
    (hJ : JointGZSupCond J)
    (hd : DiffContOnCl ℂ xiFourShapeAt (ball R00c 2)) {w : ℂ} (hw : R00Rect w)
    (hTier : 63.4 * 4 * J ≤ 1 / 40) :
    ‖deriv xiFourShapeAt w‖ ≤ 0.05 := by
  have h := R00_deriv_bound_of_joint_conds hJ0 hJ hd hw
  linarith

/-- Numeric verdict at the suggestive scale `J = 0.03`:
`63.4*4*0.03 = 7.608` exceeds `1/40` (~300x) and the deriv bound `15.216`
exceeds `0.05` (~300x). The joint route does not clear the tier. -/
theorem R00_joint_dead_at_003 :
    (1 / 40 : ℝ) < 63.4 * 4 * 0.03 ∧ (0.05 : ℝ) < 2 * (63.4 * 4 * 0.03) := by
  constructor <;> norm_num

/-- Every `z ∈ closedBall R00c 1.5` satisfies `‖z‖ ≤ 10.26`. -/
theorem mem_closedBall15_norm_le {z : ℂ} (hz : z ∈ closedBall R00c 1.5) :
    ‖z‖ ≤ 10.26 := by
  rw [mem_closedBall, dist_eq_norm] at hz
  calc ‖z‖ = ‖(z - R00c) + R00c‖ := by congr 1; abel
    _ ≤ ‖z - R00c‖ + ‖R00c‖ := norm_add_le _ _
    _ ≤ 1.5 + 8.76 := add_le_add hz R00c_norm_le
    _ = 10.26 := by norm_num

/-- Smaller-ball poly sup: `‖s * (s - 1) / 2‖ ≤ 57.89` on `closedBall R00c 1.5`
(`10.76 * 10.76 / 2 = 57.8888 ≤ 57.89`). -/
theorem R00_smallball_poly_sup_15 (z : ℂ) (hz : z ∈ closedBall R00c 1.5) :
    ‖((1 / 2 : ℂ) + Complex.I * z) * (((1 / 2 : ℂ) + Complex.I * z) - 1) / 2‖ ≤
      57.89 := by
  have hn : ‖z‖ ≤ 10.26 := mem_closedBall15_norm_le hz
  have hIz : ‖Complex.I * z‖ = ‖z‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have h12 : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    simp [Complex.norm_div, Complex.norm_ofNat]
  have hs : ‖(1 / 2 : ℂ) + Complex.I * z‖ ≤ 10.76 := by
    calc ‖(1 / 2 : ℂ) + Complex.I * z‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖Complex.I * z‖ :=
          norm_add_le _ _
      _ = 1 / 2 + ‖z‖ := by rw [hIz, h12]
      _ ≤ 1 / 2 + 10.26 := add_le_add le_rfl hn
      _ = 10.76 := by norm_num
  have hs1 : ‖((1 / 2 : ℂ) + Complex.I * z) - 1‖ ≤ 10.76 := by
    have e : ((1 / 2 : ℂ) + Complex.I * z) - 1 = Complex.I * z - (1 / 2 : ℂ) := by
      ring
    rw [e]
    calc ‖Complex.I * z - (1 / 2 : ℂ)‖ ≤ ‖Complex.I * z‖ + ‖(1 / 2 : ℂ)‖ :=
          norm_sub_le _ _
      _ = ‖z‖ + 1 / 2 := by rw [hIz, h12]
      _ ≤ 10.26 + 1 / 2 := add_le_add hn le_rfl
      _ = 10.76 := by norm_num
  have hmul : ‖(1 / 2 : ℂ) + Complex.I * z‖ *
      ‖((1 / 2 : ℂ) + Complex.I * z) - 1‖ ≤ 10.76 * 10.76 :=
    mul_le_mul hs hs1 (norm_nonneg _) (by norm_num)
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by simp [Complex.norm_ofNat]
  have hv : (10.76 : ℝ) * 10.76 / 2 ≤ 57.89 := by norm_num
  rw [Complex.norm_div, norm_mul, h2]
  linarith

/-- Smaller-ball no-go: `B / r` at `(R, r) = (1.5, 0.24)` is strictly worse
than the `R = 2` baseline (`964.83 > 507.2`). Shrinking the ball loses. -/
theorem R00_smallball_factor_no_go :
    (63.4 * 4 / 0.5 : ℝ) < 57.89 * 4 / 0.24 := by
  norm_num

/-- Smaller-ball conditional deriv bound for the joint route
(`R = 1.5`, margin `r = 0.24`: `1.26 + 0.24 = 1.50`). -/
theorem R00_smallball_deriv_bound_of_joint {J : ℝ} (hJ0 : 0 ≤ J)
    (hJ : JointGZSupCond J)
    (hd : DiffContOnCl ℂ xiFourShapeAt (ball R00c 1.5)) {w : ℂ} (hw : R00Rect w) :
    ‖deriv xiFourShapeAt w‖ ≤ (57.89 * 4 * J) / 0.24 := by
  have hsub : ‖w - R00c‖ ≤ 1.26 := R00Rect_norm_sub_le w hw
  have hw' : ‖w - R00c‖ + (0.24 : ℝ) ≤ 1.5 := by linarith
  have hB : ∀ z ∈ closedBall R00c 1.5, ‖xiFourShapeAt z‖ ≤ 57.89 * 4 * J := by
    intro z hz
    have hz2 : z ∈ closedBall R00c 2 := by
      have h1 : dist z R00c ≤ 1.5 := mem_closedBall.mp hz
      have h2 : dist z R00c ≤ (2 : ℝ) := le_trans h1 (by norm_num)
      exact mem_closedBall.mpr h2
    have h1 := R00_smallball_poly_sup_15 z hz
    have h2 := fPi_shape_sup_on_sImage _ (shiftedS_shape_mem_sImage_of_mem_ball hz2)
    have hPP : ‖(((1 / 2 : ℂ) + Complex.I * z) *
        (((1 / 2 : ℂ) + Complex.I * z) - 1) / 2) *
        fPi_shape (shiftedS_shape z)‖ ≤ 57.89 * 4 := by
      rw [norm_mul]
      exact mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
    have hJJ : ‖fGamma_shape (shiftedS_shape z) * fZeta_shape (shiftedS_shape z)‖ ≤ J :=
      hJ _ (shiftedS_shape_mem_sImage_of_mem_ball hz2)
    have e : xiFourShapeAt z =
        ((((1 / 2 : ℂ) + Complex.I * z) * (((1 / 2 : ℂ) + Complex.I * z) - 1) / 2) *
          fPi_shape (shiftedS_shape z)) *
        (fGamma_shape (shiftedS_shape z) * fZeta_shape (shiftedS_shape z)) := by
      unfold xiFourShapeAt
      ring
    rw [e, norm_mul]
    exact mul_le_mul hPP hJJ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 57.89 * 4)
  exact deriv_bound_of_sphere_sup_on_ball hd hB (show (0 : ℝ) < 0.24 by norm_num) hw'

/-- Smaller-ball joint threshold: `(57.89*4*J)/0.24 ≤ 0.05` forces
`J ≤ 0.00006` (strictly tighter than the `R = 2` threshold `0.0001`). -/
theorem R00_smallball_joint_threshold {J : ℝ} (h : (57.89 * 4 * J) / 0.24 ≤ 0.05) :
    J ≤ 0.00006 := by
  by_contra hc
  push_neg at hc
  have hpos : (0 : ℝ) < 57.89 * 4 / 0.24 := by norm_num
  have h2 : (57.89 * 4 / 0.24 : ℝ) * 0.00006 < (57.89 * 4 / 0.24) * J :=
    mul_lt_mul_of_pos_left hc hpos
  have e1 : (57.89 * 4 / 0.24 : ℝ) * 0.00006 = 0.05789 := by norm_num
  have e2 : (57.89 * 4 / 0.24 : ℝ) * J = (57.89 * 4 * J) / 0.24 := by ring
  rw [e1, e2] at h2
  linarith

/-- Lower half of the `s`-image split (`s.re ≤ 0.40`). -/
def sImageRectLo (s : ℂ) : Prop :=
  (-1.61 : ℝ) ≤ s.re ∧ s.re ≤ 0.40 ∧ (-10.75 : ℝ) ≤ s.im ∧ s.im ≤ (-6.75 : ℝ)

/-- Upper half of the `s`-image split (`0.39 ≤ s.re`, overlapping `Lo`). -/
def sImageRectHi (s : ℂ) : Prop :=
  (0.39 : ℝ) ≤ s.re ∧ s.re ≤ 2.40 ∧ (-10.75 : ℝ) ≤ s.im ∧ s.im ≤ (-6.75 : ℝ)

/-- The `s`-image rectangle is covered by the two halves. -/
theorem sImageRect_cover_lo_hi {s : ℂ} (hs : sImageRect s) :
    sImageRectLo s ∨ sImageRectHi s := by
  obtain ⟨hlo, hhi, himlo, himhi⟩ := hs
  unfold sImageRectLo sImageRectHi
  by_cases hc : s.re ≤ 0.40
  · left
    exact ⟨hlo, hc, himlo, himhi⟩
  · right
    push_neg at hc
    exact ⟨by linarith, hhi, himlo, himhi⟩

/-- Localization: per-half joint sups combine to `max J1 J2` on the whole image. -/
theorem joint_sup_of_split {J1 J2 : ℝ}
    (h1 : ∀ s : ℂ, sImageRectLo s → ‖fGamma_shape s * fZeta_shape s‖ ≤ J1)
    (h2 : ∀ s : ℂ, sImageRectHi s → ‖fGamma_shape s * fZeta_shape s‖ ≤ J2) :
    JointGZSupCond (max J1 J2) := by
  intro s hs
  rcases sImageRect_cover_lo_hi hs with h | h
  · exact le_trans (h1 s h) (le_max_left _ _)
  · exact le_trans (h2 s h) (le_max_right _ _)

#print axioms JointGZSupCond
#print axioms R00_poly_pi_sup_on_ball
#print axioms R00_xi_joint_sup_of_conds
#print axioms R00_joint_threshold_for_tier
#print axioms R00_deriv_bound_of_joint_conds
#print axioms R00_deriv_meets_tier_of_joint_conds
#print axioms R00_joint_dead_at_003
#print axioms mem_closedBall15_norm_le
#print axioms R00_smallball_poly_sup_15
#print axioms R00_smallball_factor_no_go
#print axioms R00_smallball_deriv_bound_of_joint
#print axioms R00_smallball_joint_threshold
#print axioms sImageRect_cover_lo_hi
#print axioms joint_sup_of_split

/-!
## Door-3 bottom-strip supplier (deriv-lane tail: BottomStripObligations bridge)

Quoted obligation shapes (`central_cover_assembly.lean:2208-2217`):
* `StripBaseBounds x e0 M1 := 0 < e0 ∧ 0 < M1 ∧
    e0 ≤ ‖xiShiftedEntire (x : ℂ)‖ ∧
    (∀ y ∈ Set.Icc 0 0.02,
      ‖deriv xiShiftedEntire ((x : ℂ) + Complex.I * ((y : ℝ) : ℂ))‖ ≤ M1) ∧
    0.01 < e0 / M1`
* `BottomStripObligations :=
    ∀ x : ℝ, -10 < x → x < 10 → ∃ e0 M1 : ℝ, StripBaseBounds x e0 M1`
Consumer: `bottom_strip_covered` (~2250) via the feeder
`BoundaryProofEngine.boundary_strip_nonvanishing_of_nonzero_base`
(`rh_certificate_infra.lean:254`, with `η := 0.02`).

This lane stays import-free (`import Mathlib` only), so the entire extension is
a parameter `f : ℂ → ℂ`; set `f := xiShiftedEntire` after importing the assembly
downstream. Banked here (sorry-free): the segment-point shape `stripSeg` (exact
quote of the obligation's point expression), its per-point distance cap to the
midpoint center, the segment deriv bound from the banked Cauchy rule
(`deriv_bound_of_sphere_sup_on_ball`, called — not redone), the margin
constructor plus a concrete margin instance, and the full-shape assembler
`stripBaseBoundsShape_of_explicit` mirroring the obligation conjuncts.

Residual: the base lower bound `e0 ≤ ‖xiShiftedEntire (x : ℂ)‖` for
`-10 < x < 10` (needs a rigorous `ξ`-minorant on the real axis, absent from
Mathlib); it is taken as the explicit hypothesis `hb` below.
-/

/-- Bottom-strip segment point, exact quote of the obligation's point
expression (`central_cover_assembly.lean:2211-2212`). -/
def stripSeg (x : ℝ) (y : ℝ) : ℂ := (x : ℂ) + Complex.I * ((y : ℝ) : ℂ)

/-- Midpoint center of the `0 ≤ y ≤ 0.02` segment at fixed `x`. -/
def stripSegCenter (x : ℝ) : ℂ := (x : ℂ) + Complex.I * ((0.01 : ℝ) : ℂ)

/-- The segment point is definitionally the obligation's point expression. -/
theorem stripSeg_eq_assembly_point (x : ℝ) (y : ℝ) :
    stripSeg x y = (x : ℂ) + Complex.I * ((y : ℝ) : ℂ) := rfl

/-- Segment displacement factors through `I`. -/
theorem stripSeg_sub_center_eq (x : ℝ) (y : ℝ) :
    stripSeg x y - stripSegCenter x =
      Complex.I * (((y : ℝ) : ℂ) - ((0.01 : ℝ) : ℂ)) := by
  unfold stripSeg stripSegCenter
  ring

/-- Every segment point is within `0.01` of the midpoint center
(`|y - 0.01| ≤ 0.01` for `y ∈ [0, 0.02]`). -/
theorem stripSeg_dist_center_le (x : ℝ) (y : ℝ) (hy0 : (0 : ℝ) ≤ y)
    (hy1 : y ≤ (0.02 : ℝ)) :
    ‖stripSeg x y - stripSegCenter x‖ ≤ (0.01 : ℝ) := by
  have heq := stripSeg_sub_center_eq x y
  have hfold : ((y : ℝ) : ℂ) - ((0.01 : ℝ) : ℂ) = (((y - 0.01 : ℝ)) : ℂ) := by
    push_cast
    ring
  have hnorm : ‖(((y - 0.01 : ℝ)) : ℂ)‖ = |y - 0.01| := RCLike.norm_ofReal _
  have habs : |y - 0.01| ≤ (0.01 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  calc ‖stripSeg x y - stripSegCenter x‖
      = ‖Complex.I * ((((y - 0.01 : ℝ)) : ℂ))‖ := by rw [heq, hfold]
    _ = ‖(((y - 0.01 : ℝ)) : ℂ)‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
    _ = |y - 0.01| := hnorm
    _ ≤ 0.01 := habs

/-- **Segment deriv bound (obligation conjunct 4).** A sup bound `B` on
`closedBall (stripSegCenter x) 1` gives `‖deriv f‖ ≤ M1` at every
`y ∈ Icc 0 0.02` (margin `r = 1 / 2`: `0.01 + 1 / 2 ≤ 1`), via the banked
Cauchy rule `deriv_bound_of_sphere_sup_on_ball`. Set `f := xiShiftedEntire`. -/
theorem bottomSeg_deriv_bound_of_ballSup {f : ℂ → ℂ} {x : ℝ} {B M1 : ℝ}
    (hd : DiffContOnCl ℂ f (ball (stripSegCenter x) 1))
    (hB : ∀ z ∈ closedBall (stripSegCenter x) 1, ‖f z‖ ≤ B)
    (hM : B / (1 / 2 : ℝ) ≤ M1)
    (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) (0.02 : ℝ)) :
    ‖deriv f (stripSeg x y)‖ ≤ M1 := by
  obtain ⟨hy0, hy1⟩ := hy
  have hdist : ‖stripSeg x y - stripSegCenter x‖ ≤ (0.01 : ℝ) :=
    stripSeg_dist_center_le x y hy0 hy1
  have hw : ‖stripSeg x y - stripSegCenter x‖ + (1 / 2 : ℝ) ≤ 1 := by linarith
  have h := deriv_bound_of_sphere_sup_on_ball hd hB
    (show (0 : ℝ) < 1 / 2 by norm_num) hw
  exact le_trans h hM

/-- **Margin constructor (obligation conjunct 5):** `0.01 * M1 < e0` gives
`0.01 < e0 / M1`. -/
theorem bottomStrip_margin_of_mul_lt {e0 M1 : ℝ} (hM1 : (0 : ℝ) < M1)
    (h : (0.01 : ℝ) * M1 < e0) : (0.01 : ℝ) < e0 / M1 := by
  have hiff : (0.01 : ℝ) < e0 / M1 ↔ (0.01 : ℝ) * M1 < e0 :=
    lt_div_iff₀ hM1
  rw [hiff]
  exact h

/-- Concrete margin instance: `e0 = 0.025`, `M1 = 1` clears `0.01`. -/
theorem bottomStrip_margin_example : (0.01 : ℝ) < (0.025 : ℝ) / (1 : ℝ) := by
  norm_num

/-- Local mirror of `StripBaseBounds` (`central_cover_assembly.lean:2208-2213`)
for a general `f`; set `f := xiShiftedEntire` downstream. Conjunct order matches
exactly so the supplier rewrites into the obligation. -/
def StripBaseBoundsShape (f : ℂ → ℂ) (x : ℝ) (e0 M1 : ℝ) : Prop :=
  0 < e0 ∧ 0 < M1 ∧
  e0 ≤ ‖f (x : ℂ)‖ ∧
  (∀ y ∈ Set.Icc (0 : ℝ) (0.02 : ℝ),
    ‖deriv f ((x : ℂ) + Complex.I * ((y : ℝ) : ℂ))‖ ≤ M1) ∧
  (0.01 : ℝ) < e0 / M1

/-- Full-shape assembler from the three explicit supplier components (base lower
bound taken as hypothesis `hb` — the residual xi-minorant; segment deriv bound
supplied by `bottomSeg_deriv_bound_of_ballSup`; margin by
`bottomStrip_margin_of_mul_lt`). -/
theorem stripBaseBoundsShape_of_explicit {f : ℂ → ℂ} {x : ℝ} {e0 M1 : ℝ}
    (hE0 : (0 : ℝ) < e0) (hM1 : (0 : ℝ) < M1)
    (hb : e0 ≤ ‖f (x : ℂ)‖)
    (hd : ∀ y ∈ Set.Icc (0 : ℝ) (0.02 : ℝ),
      ‖deriv f ((x : ℂ) + Complex.I * ((y : ℝ) : ℂ))‖ ≤ M1)
    (hm : (0.01 : ℝ) < e0 / M1) :
    StripBaseBoundsShape f x e0 M1 :=
  ⟨hE0, hM1, hb, hd, hm⟩

/-- The banked segment bound feeds the assembler's deriv conjunct directly
(`stripSeg x y` is the obligation's point by `rfl`). -/
theorem stripBaseBoundsShape_deriv_of_ballSup {f : ℂ → ℂ} {x : ℝ} {B M1 : ℝ}
    (hd : DiffContOnCl ℂ f (ball (stripSegCenter x) 1))
    (hB : ∀ z ∈ closedBall (stripSegCenter x) 1, ‖f z‖ ≤ B)
    (hM : B / (1 / 2 : ℝ) ≤ M1)
    (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) (0.02 : ℝ)) :
    ‖deriv f ((x : ℂ) + Complex.I * ((y : ℝ) : ℂ))‖ ≤ M1 :=
  bottomSeg_deriv_bound_of_ballSup hd hB hM y hy

#print axioms stripSeg_eq_assembly_point
#print axioms stripSeg_sub_center_eq
#print axioms stripSeg_dist_center_le
#print axioms bottomSeg_deriv_bound_of_ballSup
#print axioms bottomStrip_margin_of_mul_lt
#print axioms bottomStrip_margin_example
#print axioms stripBaseBoundsShape_of_explicit
#print axioms stripBaseBoundsShape_deriv_of_ballSup

/-!
## Door-3 remainder 2 final conjunct: real-axis minorant (explicit numerals)

Import-free bridge (`import Mathlib` only): the unconditional
`ε0 ≤ ‖xiShiftedEntire (x : ℂ)‖` minorant on `-10 < x < 10` needs a uniform
critical-line `ξ` lower bound (`s = 1 / 2 + I * x`, `|x| < 10`), absent from
Mathlib. The banked real-`s`-axis / imaginary-axis feeders
(`door3_real_center_bounds`, `door3_boundary_real`, `door3_imag_axis_strip`)
are a different slice (`z = I * y`, i.e. `s` real) and do not transfer.

Banked here (sorry-free, explicit numerals only, all `≤ 6` digits): the
margin-compatible pair `ε0 = 0.025`, `M1 = 1` with `0.01 * M1 < ε0` proved by
`norm_num`, its margin via a `bottomStrip_margin_of_mul_lt` CALL (not redone),
the full-shape instance from explicit base/deriv hypotheses, the positivity
corollary `0 < ‖f (x : ℂ)‖`, the `M1 = 1` deriv specialization of the banked
segment rule, and the per-`x` existential closure
`∃ ε0 M1, StripBaseBoundsShape f x ε0 M1` for handoff to `bottom_strip_covered`
(`central_cover_assembly.lean:2250`) after setting `f := xiShiftedEntire`.

Residual (exact): supply `hb : (0.025 : ℝ) ≤ ‖xiShiftedEntire (x : ℂ)‖` and
`hB : ∀ z ∈ closedBall (stripSegCenter x) 1, ‖xiShiftedEntire z‖ ≤ B` with
`B / (1 / 2) ≤ 1`, uniformly for `-10 < x < 10` (critical-line lower bound plus
ball sup on the strip tube; the `|Im| ∈ [10, 11]` tail numerals are a disjoint
height band and do not transfer).
-/

/-- Margin compatibility in `*` form: `0.01 * 1 < 0.025`. -/
theorem bottomStrip_mul_lt_example : (0.01 : ℝ) * (1 : ℝ) < (0.025 : ℝ) := by
  norm_num

/-- Margin via the banked constructor (CALL, not redone). -/
theorem bottomStrip_margin_via_mul_lt :
    (0.01 : ℝ) < (0.025 : ℝ) / (1 : ℝ) :=
  bottomStrip_margin_of_mul_lt (by norm_num) bottomStrip_mul_lt_example

/-- Full-shape instance at the explicit pair `(0.025, 1)` from explicit
base/deriv hypotheses (base lower bound is the residual real-axis minorant). -/
theorem stripBaseBoundsShape_explicit_of_bounds {f : ℂ → ℂ} {x : ℝ}
    (hb : (0.025 : ℝ) ≤ ‖f (x : ℂ)‖)
    (hd : ∀ (y : ℝ), y ∈ Set.Icc (0 : ℝ) (0.02 : ℝ) →
      ‖deriv f ((x : ℂ) + Complex.I * ((y : ℝ) : ℂ))‖ ≤ (1 : ℝ)) :
    StripBaseBoundsShape f x (0.025 : ℝ) (1 : ℝ) :=
  stripBaseBoundsShape_of_explicit (by norm_num) (by norm_num) hb hd
    bottomStrip_margin_via_mul_lt

/-- Positivity corollary of the explicit base hypothesis. -/
theorem stripBaseBoundsShape_base_pos_of_explicit {f : ℂ → ℂ} {x : ℝ}
    (hb : (0.025 : ℝ) ≤ ‖f (x : ℂ)‖) : (0 : ℝ) < ‖f (x : ℂ)‖ :=
  lt_of_lt_of_le (by norm_num) hb

/-- `M1 = 1` deriv specialization of the banked segment rule. -/
theorem stripBaseBoundsShape_deriv_explicit_of_ballSup {f : ℂ → ℂ} {x : ℝ}
    {B : ℝ}
    (hd : DiffContOnCl ℂ f (ball (stripSegCenter x) 1))
    (hB : ∀ (z : ℂ), z ∈ closedBall (stripSegCenter x) 1 → ‖f z‖ ≤ B)
    (hM : B / (1 / 2 : ℝ) ≤ (1 : ℝ))
    (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) (0.02 : ℝ)) :
    ‖deriv f ((x : ℂ) + Complex.I * ((y : ℝ) : ℂ))‖ ≤ (1 : ℝ) :=
  stripBaseBoundsShape_deriv_of_ballSup hd hB hM y hy

/-- Per-`x` existential closure at explicit numerals, for handoff to
`bottom_strip_covered` after `f := xiShiftedEntire`. -/
theorem stripBaseBoundsShape_exists_of_explicit_bounds {f : ℂ → ℂ} {x : ℝ}
    (hb : (0.025 : ℝ) ≤ ‖f (x : ℂ)‖)
    (hd : ∀ (y : ℝ), y ∈ Set.Icc (0 : ℝ) (0.02 : ℝ) →
      ‖deriv f ((x : ℂ) + Complex.I * ((y : ℝ) : ℂ))‖ ≤ (1 : ℝ)) :
    ∃ (e0 : ℝ), ∃ (M1 : ℝ), StripBaseBoundsShape f x e0 M1 :=
  ⟨(0.025 : ℝ), (1 : ℝ), stripBaseBoundsShape_explicit_of_bounds hb hd⟩

#print axioms bottomStrip_mul_lt_example
#print axioms bottomStrip_margin_via_mul_lt
#print axioms stripBaseBoundsShape_explicit_of_bounds
#print axioms stripBaseBoundsShape_base_pos_of_explicit
#print axioms stripBaseBoundsShape_deriv_explicit_of_ballSup
#print axioms stripBaseBoundsShape_exists_of_explicit_bounds

/-!
## Door-3 generic-f tier closure (SUP tail: single sup premise)

Grep shapes (verified before append):
* `R00_deriv_bound_of_sup` (`door3_deriv_certs.lean:148-163`): generic `f`,
  sup `qB` on `ball R00c 2` gives `‖deriv f w‖ ≤ 2 * qB` on `R00Rect`.
* `R00_deriv_meets_outer_tier` (`door3_deriv_certs.lean:167-172`): `qB ≤ 1/40`
  gives `2 * qB ≤ 0.05`.

Honest sup-premise attempt (ONE premise, chained from banked sups):
* Banked on `closedBall R00c 2`: poly `63.4` (`shiftedS_poly_shape_sup_on_ball`),
  `fPi ≤ 4` (`fPi_shape_sup_on_sImage`), `GammaSupCond 1.52`
  (`deriv_GammaSupCond_152`), hence `‖xiFourShapeAt z‖ ≤ 385.472 * Z` under any
  `ZetaSupCond Z` (`deriv_xiFourShapeAt_sup_of_gamma152`).
* Missing (grep-clean, no unconditional instance in repo): any `ZetaSupCond Z`
  or `JointGZSupCond J` with `Z`/`J` small enough for `1/40`. Repo grep for
  `ZetaSupCond`/`JointGZSupCond` numeral instances and for
  `‖xiShifted‖` sups on `closedBall R00c 2` returns only the conditional
  shapes above — no banked zeta sup. So the `qB ≤ 1/40` premise cannot be
  discharged unconditionally; it is filed below as the exact spec `R00SupSpec`
  (generic `f`) with `ZetaSupCond`/`JointGZSupCond` as the xi-shape instances.

Banked here (sorry-free, no `simpa`):
* `R00SupSpec`: exact generic spec (`DiffContOnCl` + ball sup `qB` + `qB ≤ 1/40`).
* `R00_deriv_tier_of_sup`: generic closure CALLING (not redoing)
  `R00_deriv_bound_of_sup` + `R00_deriv_meets_outer_tier`.
* `R00_xi_deriv_of_gamma152_zeta`: xi-shape chain CALLING
  `deriv_xiFourShapeAt_sup_of_gamma152` + `deriv_bound_of_sphere_sup_on_ball`
  (`385.472 * Z / (1/2) = 770.944 * Z`).
* `R00_xi_tier_needs_zeta007`: quantified gap (`770.944 * Z ≤ 0.05` forces
  `Z ≤ 0.00007`; `770.944 * 0.00007 = 0.05396608 > 0.05`).

Value-or-gap: VALUE = conditional closures above; GAP = unconditional
`qB ≤ 1/40` sup (needs `ZetaSupCond Z` with `Z ≤ 0.00007`, i.e. a zeta majorant
far below the true `|ζ| ~ 1` scale on this rectangle — absent from Mathlib).
Residual (exact): supply `ZetaSupCond Z` (or `JointGZSupCond J` with
`J ≤ 0.0001` via `R00_deriv_meets_tier_of_joint_conds`) plus
`DiffContOnCl ℂ xiFourShapeAt (ball R00c 2)`.
-/

/-- Exact generic sup spec for the `R00` outer tier: differentiability +
sup `qB` on `ball R00c 2` + the tier threshold `qB ≤ 1 / 40`. -/
def R00SupSpec (f : ℂ → ℂ) (qB : ℚ) : Prop :=
  DiffContOnCl ℂ f (ball R00c ((2 : ℚ) : ℝ)) ∧
  (∀ z ∈ closedBall R00c ((2 : ℚ) : ℝ), ‖f z‖ ≤ (qB : ℝ)) ∧
  qB ≤ 1 / 40

/-- **Generic-f tier closure (single sup premise).** Under `R00SupSpec f qB`,
every `w ∈ R00Rect` satisfies the leaf tier `‖deriv f w‖ ≤ 0.05`
(by CALLING `R00_deriv_bound_of_sup` + `R00_deriv_meets_outer_tier`). -/
theorem R00_deriv_tier_of_sup {f : ℂ → ℂ} {qB : ℚ}
    (h : R00SupSpec f qB) {w : ℂ} (hw : R00Rect w) :
    ‖deriv f w‖ ≤ 0.05 := by
  obtain ⟨hd, hB, hle⟩ := h
  have hb := R00_deriv_bound_of_sup hd hB hw
  have hm := R00_deriv_meets_outer_tier qB hle
  linarith

/-- Xi-shape deriv chain with the banked Gamma numeral: under any
`ZetaSupCond Z`, `‖deriv xiFourShapeAt w‖ ≤ 770.944 * Z` on `R00Rect`
(`385.472 * Z` sup via `deriv_xiFourShapeAt_sup_of_gamma152`, margin `1/2`
via `deriv_bound_of_sphere_sup_on_ball`). -/
theorem R00_xi_deriv_of_gamma152_zeta {Z : ℝ} (hZ0 : 0 ≤ Z) (hZ : ZetaSupCond Z)
    (hd : DiffContOnCl ℂ xiFourShapeAt (ball R00c 2)) {w : ℂ} (hw : R00Rect w) :
    ‖deriv xiFourShapeAt w‖ ≤ 770.944 * Z := by
  have hB : ∀ z ∈ closedBall R00c 2, ‖xiFourShapeAt z‖ ≤ 385.472 * Z :=
    fun z hz => deriv_xiFourShapeAt_sup_of_gamma152 hZ0 hZ z hz
  have hsub : ‖w - R00c‖ ≤ 1.26 := R00Rect_norm_sub_le w hw
  have hw' : ‖w - R00c‖ + (1 / 2 : ℝ) ≤ 2 := by linarith
  have h := deriv_bound_of_sphere_sup_on_ball hd hB
    (show (0 : ℝ) < 1 / 2 by norm_num) hw'
  have heq : (385.472 * Z) / (1 / 2 : ℝ) = 770.944 * Z := by ring
  rw [heq] at h
  exact h

/-- Quantified xi gap: reaching the deriv tier (`770.944 * Z ≤ 0.05`) forces
`Z ≤ 0.00007` (`770.944 * 0.00007 = 0.05396608 > 0.05`). -/
theorem R00_xi_tier_needs_zeta007 {Z : ℝ} (h : 770.944 * Z ≤ 0.05) :
    Z ≤ 0.00007 := by
  by_contra hc
  push_neg at hc
  have hpos : (0 : ℝ) < 770.944 := by norm_num
  have h2 : (770.944 : ℝ) * 0.00007 < 770.944 * Z :=
    mul_lt_mul_of_pos_left hc hpos
  norm_num at h2
  linarith

#print axioms R00SupSpec
#print axioms R00_deriv_tier_of_sup
#print axioms R00_xi_deriv_of_gamma152_zeta
#print axioms R00_xi_tier_needs_zeta007

/-!
## Door-3 ZETA007 tail (exact Z spec for the xi-shape tier)

Grep shapes (verified before append):
* `R00SupSpec` (`door3_deriv_certs.lean:1321-1324`): generic spec
  (`DiffContOnCl` + ball sup `qB` + `qB ≤ 1 / 40`).
* `R00_deriv_tier_of_sup` (`1329-1335`): generic closure CALLING
  `R00_deriv_bound_of_sup` + `R00_deriv_meets_outer_tier`.
* `R00_xi_deriv_of_gamma152_zeta` (`1341-1352`): xi-shape chain
  (`385.472 * Z` sup via `deriv_xiFourShapeAt_sup_of_gamma152`, margin `1/2`
  gives `385.472 * Z / (1/2) = 770.944 * Z`).
* `R00_xi_tier_needs_zeta007` (`1356-1364`): necessary gap
  (`770.944 * Z ≤ 0.05` forces `Z ≤ 0.00007`).
* `ZetaSupCond` (`527-528`) / `JointGZSupCond` (`843-844`): conditional props only.
  Repo-wide grep for numeral instances (`ZetaSupCond <num>`,
  `JointGZSupCond <num>`) returns no unconditional zeta sup on `sImageRect`;
  the only banked zeta uppers elsewhere are `O(1)`-to-`O(1000)` scale
  (conditional `≤ 10`, unconditional `≤ 934` / `≤ 1012` on disjoint rects),
  and the true `|ζ| ~ 1` scale on this rectangle exceeds the tier need by
  ~5 orders. So the Z premise cannot be chained from banked sups.

Banked here (placeholder-free, direct tactics only):
* `R00_xi_tier_needs_zeta0065`: tightened necessary gap
  (`770.944 * Z ≤ 0.05` forces `Z ≤ 0.000065`;
  `770.944 * 0.000065 = 0.05011136 > 0.05`).
* `R00_xi_tier_sufficient_of_zeta0064`: sufficient cap
  (`Z ≤ 0.000064` gives `770.944 * Z ≤ 0.05`;
  `770.944 * 0.000064 = 0.049340416 ≤ 0.05`).
* `R00XiTierZetaSpec`: exact missing xi-tier zeta spec
  (`ZetaSupCond Z ∧ Z ≤ 0.000064`).
* `R00_xi_tier_of_zeta0064`: conditional tier closure CALLING
  `R00_xi_deriv_of_gamma152_zeta` + `R00_xi_tier_sufficient_of_zeta0064`.

Value-or-gap: VALUE = tightened necessary `0.000065` + sufficient `0.000064`
  + conditional closure above; GAP = unconditional `ZetaSupCond Z` with
  `Z ≤ 0.000064` (zeta majorant ~5 orders below the true `|ζ| ~ 1` scale,
  absent from Mathlib).
Residual (exact): supply `ZetaSupCond Z` with `Z ≤ 0.000064` (or
  `JointGZSupCond J` with `J ≤ 0.0001` via
  `R00_deriv_meets_tier_of_joint_conds`) plus
  `DiffContOnCl ℂ xiFourShapeAt (ball R00c 2)`.
-/

/-- Tightened necessary xi gap: the deriv tier (`770.944 * Z ≤ 0.05`) forces
`Z ≤ 0.000065` (`770.944 * 0.000065 = 0.05011136 > 0.05`). -/
theorem R00_xi_tier_needs_zeta0065 {Z : ℝ} (h : 770.944 * Z ≤ 0.05) :
    Z ≤ 0.000065 := by
  by_contra hc
  push_neg at hc
  have hpos : (0 : ℝ) < 770.944 := by norm_num
  have h2 : (770.944 : ℝ) * 0.000065 < 770.944 * Z :=
    mul_lt_mul_of_pos_left hc hpos
  norm_num at h2
  linarith

/-- Sufficient xi cap: `Z ≤ 0.000064` gives `770.944 * Z ≤ 0.05`
(`770.944 * 0.000064 = 0.049340416 ≤ 0.05`). -/
theorem R00_xi_tier_sufficient_of_zeta0064 {Z : ℝ} (h : Z ≤ 0.000064) :
    770.944 * Z ≤ 0.05 := by
  have hpos : (0 : ℝ) ≤ 770.944 := by norm_num
  have h2 : (770.944 : ℝ) * Z ≤ 770.944 * 0.000064 :=
    mul_le_mul_of_nonneg_left h hpos
  have e : (770.944 : ℝ) * 0.000064 ≤ 0.05 := by norm_num
  linarith

/-- Exact missing xi-tier zeta spec: a `ZetaSupCond Z` numeral at or below
the sufficient cap `0.000064`. -/
def R00XiTierZetaSpec (Z : ℝ) : Prop :=
  ZetaSupCond Z ∧ Z ≤ 0.000064

/-- Conditional xi-tier closure at the sufficient cap: under any
`ZetaSupCond Z` with `Z ≤ 0.000064`, `‖deriv xiFourShapeAt w‖ ≤ 0.05` on
`R00Rect` (by CALLING `R00_xi_deriv_of_gamma152_zeta` +
`R00_xi_tier_sufficient_of_zeta0064`). -/
theorem R00_xi_tier_of_zeta0064 {Z : ℝ} (hZ0 : 0 ≤ Z) (hZ : ZetaSupCond Z)
    (hb : Z ≤ 0.000064)
    (hd : DiffContOnCl ℂ xiFourShapeAt (ball R00c 2)) {w : ℂ} (hw : R00Rect w) :
    ‖deriv xiFourShapeAt w‖ ≤ 0.05 := by
  have hderiv := R00_xi_deriv_of_gamma152_zeta hZ0 hZ hd hw
  have hle : (770.944 : ℝ) * Z ≤ 0.05 := R00_xi_tier_sufficient_of_zeta0064 hb
  linarith

#print axioms R00_xi_tier_needs_zeta0065
#print axioms R00_xi_tier_sufficient_of_zeta0064
#print axioms R00XiTierZetaSpec
#print axioms R00_xi_tier_of_zeta0064

/-!
## Door-3 ZETA0064 close attempt (banked-sups rebuild → exact residual)

Grep chain tail (verified before append):
* `R00_xi_tier_sufficient_of_zeta0064` (`door3_deriv_certs.lean:1428-1434`):
  `Z ≤ 0.000064 → 770.944 * Z ≤ 0.05`
  (`770.944 * 0.000064 = 0.049340416 ≤ 0.05`).
* `R00XiTierZetaSpec` (`1438-1439`): `ZetaSupCond Z ∧ Z ≤ 0.000064`.
* `R00_xi_tier_of_zeta0064` (`1445-1451`): conditional closure CALLING
  `R00_xi_deriv_of_gamma152_zeta` + `R00_xi_tier_sufficient_of_zeta0064`.
* `ZetaSupCond` (`527-528`) / `JointGZSupCond` (`843-844`): conditional props
  only; no numeral instance in this file.
* Banked zeta uppers elsewhere are `O(1)`-to-`O(1000)` scale on disjoint rects
  (conditional `≤ 10`, unconditional `≤ 934` / `≤ 1012`) versus the sufficient cap
  `0.000064`; the true `|ζ| ~ 1` scale on `sImageRect` exceeds the cap by more
  than four orders. So no banked sup discharges `R00XiTierZetaSpec`.

Banked here (direct tactics only):
* `R00_banked_zeta_scale_above_cap`: the banked `10` / `934` / `1012` scales
  all exceed `0.000064`.
* `R00_zeta0064_cap_excludes_banked_scale`: any `Z ≥ 10` cannot satisfy
  `Z ≤ 0.000064`.
* `R00_zeta0064_cap_excludes_true_scale`: any `Z ≥ 1` cannot satisfy
  `Z ≤ 0.000064` (true-scale wall).
* `R00Zeta0064CloseResidual`: exact missing unconditional premise
  (`∃ Z, 0 ≤ Z ∧ ZetaSupCond Z ∧ Z ≤ 0.000064 ∧ DiffContOnCl`).
* `R00_xi_tier_of_zeta0064_residual`: tier closure rebuilt by CALLING
  `R00_xi_tier_of_zeta0064` under the residual.

Value-or-gap: VALUE = scale-gap numerals + residual closure above;
  GAP = unconditional `ZetaSupCond Z` with `Z ≤ 0.000064`.
Residual (exact): supply `R00Zeta0064CloseResidual`.
-/

/-- Banked zeta scales sit far above the sufficient cap `0.000064`. -/
theorem R00_banked_zeta_scale_above_cap :
    (0.000064 : ℝ) < 10 ∧ (0.000064 : ℝ) < 934 ∧ (0.000064 : ℝ) < 1012 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- Any zeta sup at the banked `10` scale cannot meet the `0.000064` cap. -/
theorem R00_zeta0064_cap_excludes_banked_scale {Z : ℝ} (h : 10 ≤ Z) :
    ¬ Z ≤ 0.000064 := by
  intro hcap
  linarith

/-- Any zeta sup at the true `|ζ| ~ 1` scale cannot meet the `0.000064` cap. -/
theorem R00_zeta0064_cap_excludes_true_scale {Z : ℝ} (h : 1 ≤ Z) :
    ¬ Z ≤ 0.000064 := by
  intro hcap
  linarith

/-- Exact missing unconditional premise for the `zeta0064` tier closure. -/
def R00Zeta0064CloseResidual : Prop :=
  ∃ Z : ℝ, 0 ≤ Z ∧ ZetaSupCond Z ∧ Z ≤ 0.000064 ∧
    DiffContOnCl ℂ xiFourShapeAt (ball R00c 2)

/-- Tier closure rebuilt from the exact residual (by CALLING
`R00_xi_tier_of_zeta0064`). -/
theorem R00_xi_tier_of_zeta0064_residual (h : R00Zeta0064CloseResidual)
    {w : ℂ} (hw : R00Rect w) : ‖deriv xiFourShapeAt w‖ ≤ 0.05 := by
  obtain ⟨Z, hZ0, hZ, hb, hd⟩ := h
  exact R00_xi_tier_of_zeta0064 hZ0 hZ hb hd hw

#print axioms R00_banked_zeta_scale_above_cap
#print axioms R00_zeta0064_cap_excludes_banked_scale
#print axioms R00_zeta0064_cap_excludes_true_scale
#print axioms R00Zeta0064CloseResidual
#print axioms R00_xi_tier_of_zeta0064_residual

/-!
## Door-3 R01 sup spec mirror attempt (R00 chain closed-conditional; zeta0064 cap impossible)

Grep R00 chain tail (verified before append):
* `R00_xi_tier_needs_zeta0065` (`door3_deriv_certs.lean:1416-1424`): necessary
  gap `770.944 * Z ≤ 0.05 → Z ≤ 0.000065`.
* `R00_xi_tier_sufficient_of_zeta0064` (`1428-1434`): sufficient cap
  `Z ≤ 0.000064 → 770.944 * Z ≤ 0.05`
  (`770.944 * 0.000064 = 0.049340416 ≤ 0.05`).
* `R00XiTierZetaSpec` (`1438-1439`): `ZetaSupCond Z ∧ Z ≤ 0.000064`.
* `R00_xi_tier_of_zeta0064` (`1445-1451`): conditional closure CALLING
  `R00_xi_deriv_of_gamma152_zeta` + `R00_xi_tier_sufficient_of_zeta0064`.
* `R00_banked_zeta_scale_above_cap` (`1493-1495`): `10` / `934` / `1012`
  all exceed `0.000064`.
* `R00_zeta0064_cap_excludes_banked_scale` (`1498-1501`):
  `10 ≤ Z → ¬ Z ≤ 0.000064`.
* `R00_zeta0064_cap_excludes_true_scale` (`1504-1507`):
  `1 ≤ Z → ¬ Z ≤ 0.000064` (true-scale wall).
* `R00Zeta0064CloseResidual` (`1510-1512`): exact missing unconditional premise.
* `R00_xi_tier_of_zeta0064_residual` (`1516-1519`): tier closure rebuilt by CALLING
  `R00_xi_tier_of_zeta0064` under the residual.
* R01 grep in this file: no matches (`R01c` / `R01Rect` / R01 s-image absent
  locally); no banked R01 chain to call.

Mirror attempt (honest, banked chains only, no invented coordinates):
* Generic tier rule `deriv_bound_of_sphere_sup_on_ball` (`59-83`) is
  center-independent, so the R01 generic tier closes conditionally below by
  CALLING it with explicit `R01c` / `R01Rect` hypotheses (parameters, not
  asserted geometry).
* R01-specific geometry (center/rect/ball inclusion) and R01 s-image
  Gamma/Zeta sups are absent locally; R00 numerals (`63.4 * 4 * 1.52`,
  `770.944`, cap `0.000064`) are reused only as conditional arithmetic shape,
  not as R01 facts.
* zeta0064 cap impossibility carries over arithmetically at the same cap.

Banked here (direct tactics only):
* `R01_deriv_bound_of_sup_given`: R01-shape generic bound CALLING the banked
  Cauchy rule under explicit hypotheses.
* `R01_deriv_tier_of_sup_given`: generic tier closure (`2 * B ≤ 0.05` gives
  `‖deriv‖ ≤ 0.05`).
* `R01_zeta0064_cap_excludes_banked_scale` / `R01_zeta0064_cap_excludes_true_scale`:
  cap impossibility at banked/true scales (same shape as R00).
* `R01_xi_tier_sufficient_of_zeta0064_given`: sufficient arithmetic
  (`Z ≤ 0.000064 → 770.944 * Z ≤ 0.05`), R00-shape numeral, conditional.
* `R01MirrorCloseResidual`: exact missing R01 premises (parameters, not invented).
* `R01_tier_of_mirror_residual`: closure rebuilt by CALLING the generic bound.

Value-or-gap: VALUE = conditional R01 mirror + cap impossibility above;
  GAP = unconditional R01 geometry + R01 s-image zeta sup (absent locally).
Residual (exact): supply `R01MirrorCloseResidual`.
-/

/-- R01-shape generic deriv bound under explicit hypotheses (by CALLING the
banked Cauchy rule; `R01c` / `R01Rect` are parameters, no coordinates invented). -/
theorem R01_deriv_bound_of_sup_given {f : ℂ → ℂ} {R01c : ℂ} {R01Rect : ℂ → Prop}
    {B : ℝ} (hd : DiffContOnCl ℂ f (ball R01c 2))
    (hB : ∀ z ∈ closedBall R01c 2, ‖f z‖ ≤ B)
    (hsub : ∀ w : ℂ, R01Rect w → ‖w - R01c‖ ≤ 1.26)
    {w : ℂ} (hw : R01Rect w) :
    ‖deriv f w‖ ≤ 2 * B := by
  have hle : ‖w - R01c‖ ≤ 1.26 := hsub w hw
  have hw' : ‖w - R01c‖ + (1 / 2 : ℝ) ≤ 2 := by linarith
  have h := deriv_bound_of_sphere_sup_on_ball hd hB
    (show (0 : ℝ) < 1 / 2 by norm_num) hw'
  have heq : B / (1 / 2 : ℝ) = 2 * B := by ring
  rwa [heq] at h

/-- R01-shape generic tier closure (`2 * B ≤ 0.05` gives the leaf tier). -/
theorem R01_deriv_tier_of_sup_given {f : ℂ → ℂ} {R01c : ℂ} {R01Rect : ℂ → Prop}
    {B : ℝ} (hd : DiffContOnCl ℂ f (ball R01c 2))
    (hB : ∀ z ∈ closedBall R01c 2, ‖f z‖ ≤ B)
    (hsub : ∀ w : ℂ, R01Rect w → ‖w - R01c‖ ≤ 1.26)
    {w : ℂ} (hw : R01Rect w) (hTier : 2 * B ≤ 0.05) :
    ‖deriv f w‖ ≤ 0.05 := by
  have h := R01_deriv_bound_of_sup_given hd hB hsub hw
  linarith

/-- R01 cap wall at the banked scale: any `Z ≥ 10` cannot meet `0.000064`. -/
theorem R01_zeta0064_cap_excludes_banked_scale {Z : ℝ} (h : 10 ≤ Z) :
    ¬ Z ≤ 0.000064 := by
  intro hcap
  linarith

/-- R01 cap wall at the true `|ζ| ~ 1` scale: any `Z ≥ 1` cannot meet `0.000064`. -/
theorem R01_zeta0064_cap_excludes_true_scale {Z : ℝ} (h : 1 ≤ Z) :
    ¬ Z ≤ 0.000064 := by
  intro hcap
  linarith

/-- R01-shape sufficient arithmetic at the R00 numeral (conditional only):
`Z ≤ 0.000064 → 770.944 * Z ≤ 0.05`. -/
theorem R01_xi_tier_sufficient_of_zeta0064_given {Z : ℝ} (h : Z ≤ 0.000064) :
    770.944 * Z ≤ 0.05 := by
  have hpos : (0 : ℝ) ≤ 770.944 := by norm_num
  have h2 : (770.944 : ℝ) * Z ≤ 770.944 * 0.000064 :=
    mul_le_mul_of_nonneg_left h hpos
  have e : (770.944 : ℝ) * 0.000064 ≤ 0.05 := by norm_num
  linarith

/-- Exact missing R01 mirror premises (parameters; nothing asserted about the
true R01 cell — that geometry plus R01 s-image sups are absent locally). -/
def R01MirrorCloseResidual (R01c : ℂ) (R01Rect : ℂ → Prop) (B : ℝ) : Prop :=
  (∀ w : ℂ, R01Rect w → w ∈ closedBall R01c 2) ∧
  (∀ z ∈ closedBall R01c 2, ‖xiFourShapeAt z‖ ≤ B) ∧
  2 * B ≤ 0.05 ∧ DiffContOnCl ℂ xiFourShapeAt (ball R01c 2)

/-- R01 tier closure rebuilt from the exact residual (by CALLING the generic
bound above). -/
theorem R01_tier_of_mirror_residual {R01c : ℂ} {R01Rect : ℂ → Prop} {B : ℝ}
    (h : R01MirrorCloseResidual R01c R01Rect B)
    {w : ℂ} (hw : R01Rect w) : ‖deriv xiFourShapeAt w‖ ≤ 0.05 := by
  obtain ⟨hmem, hB, hTier, hd⟩ := h
  have hsub : ∀ u : ℂ, R01Rect u → ‖u - R01c‖ ≤ 1.26 := by
    intro u hu
    have h2 := hmem u hu
    rw [mem_closedBall, dist_eq_norm] at h2
    linarith
  exact R01_deriv_tier_of_sup_given hd hB hsub hw hTier

#print axioms R01_deriv_bound_of_sup_given
#print axioms R01_deriv_tier_of_sup_given
#print axioms R01_zeta0064_cap_excludes_banked_scale
#print axioms R01_zeta0064_cap_excludes_true_scale
#print axioms R01_xi_tier_sufficient_of_zeta0064_given
#print axioms R01MirrorCloseResidual
#print axioms R01_tier_of_mirror_residual
