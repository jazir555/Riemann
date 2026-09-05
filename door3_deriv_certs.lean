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
