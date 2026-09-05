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
