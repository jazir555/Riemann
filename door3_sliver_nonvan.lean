import Mathlib
import central_cover_assembly
import door3_top_edge

/-! # Door-3 sliver nonvanishing (premise (d) of the door-3 capstone)

TARGET (quoted verbatim from `door3_rh_wiring.lean:88-94`,
`Door3RHWiring.xiCutoffLines10_of_cutR10_and_leftLine`):

```
    (hSliver : ∀ z : ℂ, (z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) →
      -(1 / 2 : ℝ) < z.im → z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      (0.49 ≤ z.im ∨ z.im ≤ -0.49) → xiShifted z ≠ 0) :
```

Region: BOTH cutoff lines `Re = ±10`, band `-(1/2) < Im < 1/2`, off the
real axis (`Im ≠ 0`), sliver `0.49 ≤ |Im|` (i.e. `0.49 ≤ Im ∨ Im ≤ -0.49`).
Conclusion: `xiShifted z ≠ 0`.

How `cutoffLines_either` splits rect-vs-sliver
(`central_cover_assembly.lean:6908-6911`):
`CentralCoverAssembly.cutoffLines_either` sends every cutoff point
(`Re = ±10`, `|Im| < 1/2`) to EITHER a thin rect
(`CutL10.mem z ∨ CutR10.mem z`, covering `|Im| ≤ 0.49` via
`CutL10_mem_of_line` :6898 / `CutR10_mem_of_line` :6888) OR the sliver
disjunct (`0.49 ≤ Im ∨ Im ≤ -0.49`). The rect arm is already wired
(`cutR10_rect_nonvanishing` for `CutR10`; `CutL10` is premise (c), another
lane). This file owns the sliver arm: the theorem
`sliver_nonvanishing_of_topBotRects` below has EXACTLY the `hSliver` shape,
so `xiCutoffLines10_of_cutR10_and_leftLine` consumes it directly
(`· exact hSliver z heq hgt' hlt hne hs`, wiring line 106).

Banked pieces cited (all qualitative; exact names):
* `Door3TopEdge.exists_top_edge_uniform_strip` (`door3_top_edge.lean:294`):
  for every closed `[a,b]` there is a uniform `δ > 0` with the open strip
  `1/2 - δ < y < 1/2` above `[a,b]` zero-free for `_root_.xiShifted`.
  Backed by `Door3TopEdge.exists_top_edge_lower_bound` (:61, compact edge
  minimum via `xiShiftedEntire_ne_zero_top`, endpoint `x = 0` repaired by the
  entire value) + `BoundaryProofEngine.upper_boundary_nonvanishing_from_outer_bound`
  (`rh_certificate_infra.lean:459`, Theorem 3). NOTE: gives NO numeric width;
  `δ ≥ 0.01` stays open (guide § "Top-edge compact lower-bound feeder").
* `Door3TopEdge.exists_bottom_edge_uniform_strip` (`door3_top_edge.lean:445`):
  mirror qualitative strip above the bottom edge; same numeric-width caveat.
  (Alternative lower route, NOT used here: `Door3TopEdge.lower_boundary_nonvanishing_from_outer_bound`
  (:397), or upper→lower via `Door3ResidualScout.door3_conj_transfer`
  (`central_cover_assembly.lean:16576`, `classicalXi_symmetry.conj_symm`).)
* `CentralCoverAssembly.xiShifted_eq_entire_on_strip` (entire↔totalized transfer
  inside the open strip; already consumed inside the two uniform-strip lemmas).
* `Door3ResidualScout.door3_cutoffLine_mem_of_abs_le`
  (`central_cover_assembly.lean:16557`): `|Im| ≤ 0.49` on either line lands in
  a thin rect (rect arm, not this file).
* `RHProofScaffold.XiCutoffLines10` (`riemann_hypothesis.lean:12165`) and
  `XiCentralEdgeStrips10` (:12157): the capstone Props this feeds.

Why the sliver avoids the top-edge endpoint trap: sliver points have
`Re = ±10 ≠ 0`, so the `x ≠ 0` side condition of
`Door3TopEdge.xiShiftedEntire_eq_xiShifted_top` (:12) always holds on the
lines; the separately-recorded totalization zero
`_root_.xiShifted (I/2) = 0` (`door3_boundary_endpoints.lean`) is off the lines.

Structure (no `sorry`/`admit`/`axiom` anywhere):
§1 banked-lemma assembly — all PROVED (pure logic + Mathlib + cited banked certs
  taken as explicit hypotheses);
§2 residual quantitative core — the ONLY unclosable numerics
  (`hwidthT : 1/2 - δT < 0.49`, `hwidthB : -0.49 < -1/2 + δB`, i.e. the
  `δ ≥ 0.01` obligation) isolated as EXPLICIT hypothesis Props;
§3 final `hSliver`-shaped theorem, PROVED conditional on the premises.
-/

namespace Door3SliverNonvan

open CentralCoverAssembly

/-! ### §1 Banked-lemma assembly (proved) -/

/-- Pure split: the sliver disjunct inside the band is an upper sliver
`0.49 ≤ Im < 1/2` or a lower sliver `-1/2 < Im ≤ -0.49`. -/
theorem sliver_upper_or_lower {z : ℂ}
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ))
    (hs : (0.49 : ℝ) ≤ z.im ∨ z.im ≤ -0.49) :
    ((0.49 : ℝ) ≤ z.im ∧ z.im < 1 / 2) ∨
      (-(1 / 2 : ℝ) < z.im ∧ z.im ≤ -0.49) := by
  rcases hs with h | h
  · exact Or.inl ⟨h, hlt⟩
  · exact Or.inr ⟨hgt, h⟩

/-- Sliver points (`Re = ±10`) lie in the closed interval `[-10, 10]` fed to
the uniform-strip banked lemmas. -/
theorem sliver_re_mem_Icc {z : ℂ}
    (heq : z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) :
    z.re ∈ Set.Icc (-10 : ℝ) (10 : ℝ) := by
  rw [Set.mem_Icc]
  rcases heq with h | h <;> rw [h] <;> constructor <;> norm_num

/-- Every complex point is its vertical-line coordinate form
`↑Re + I * ↑Im`, matching the `((x : ℂ) + Complex.I * (y : ℂ))` shape of the
banked uniform-strip conclusions. -/
theorem sliver_point_eq_vertical (z : ℂ) :
    (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by
  apply Complex.ext
  · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]

/-- Routing wrapper around the banked rect-vs-sliver split: on the cutoff
lines, ruling out both thin rects leaves exactly the sliver disjunct that
`xiCutoffLines10_of_cutR10_and_leftLine` feeds to `hSliver` (wiring line 106).
Proved from `CentralCoverAssembly.cutoffLines_either` by pure logic. -/
theorem sliver_of_cutoffLines_either {z : ℂ}
    (heq : z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ))
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ))
    (hnotrect : ¬ (CutL10.mem z ∨ CutR10.mem z)) :
    (0.49 : ℝ) ≤ z.im ∨ z.im ≤ -0.49 := by
  rcases CentralCoverAssembly.cutoffLines_either heq hgt hlt with h | hs
  · exact absurd h hnotrect
  · exact hs

/-- Upper sliver rect from a uniform-strip certificate plus an explicit width
inequality. The certificate `hstripT` is discharged by
`Door3TopEdge.exists_top_edge_uniform_strip` at `a = -10, b = 10`; only
`hwidthT` (the `δ ≥ 0.01` numeral) is a genuine fix-wave premise. -/
theorem top_sliver_of_uniform_strip {δT : ℝ}
    (hstripT : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      (1 / 2 : ℝ) - δT < y → y < (1 / 2 : ℝ) →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0)
    (hwidthT : (1 / 2 : ℝ) - δT < 0.49)
    {z : ℂ} (heq : z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ))
    (hlo : (0.49 : ℝ) ≤ z.im) (hhi : z.im < (1 / 2 : ℝ)) :
    xiShifted z ≠ 0 := by
  have hx : z.re ∈ Set.Icc (-10 : ℝ) (10 : ℝ) := sliver_re_mem_Icc heq
  have hlow : (1 / 2 : ℝ) - δT < z.im := lt_of_lt_of_le hwidthT hlo
  have h := hstripT z.re hx z.im hlow hhi
  have hpoint : ((z.re : ℂ) + Complex.I * (z.im : ℂ)) = z :=
    sliver_point_eq_vertical z
  rw [hpoint] at h
  exact h

/-- Lower sliver rect from a uniform-strip certificate plus an explicit width
inequality. Mirror of `top_sliver_of_uniform_strip`; the certificate `hstripB`
is discharged by `Door3TopEdge.exists_bottom_edge_uniform_strip`. -/
theorem bottom_sliver_of_uniform_strip {δB : ℝ}
    (hstripB : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      -(1 / 2 : ℝ) < y → y < -(1 / 2 : ℝ) + δB →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0)
    (hwidthB : (-0.49 : ℝ) < -(1 / 2 : ℝ) + δB)
    {z : ℂ} (heq : z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ))
    (hgt : -(1 / 2 : ℝ) < z.im) (hhi : z.im ≤ (-0.49 : ℝ)) :
    xiShifted z ≠ 0 := by
  have hx : z.re ∈ Set.Icc (-10 : ℝ) (10 : ℝ) := sliver_re_mem_Icc heq
  have hhigh : z.im < -(1 / 2 : ℝ) + δB := lt_of_le_of_lt hhi hwidthB
  have h := hstripB z.re hx z.im hgt hhigh
  have hpoint : ((z.re : ℂ) + Complex.I * (z.im : ℂ)) = z :=
    sliver_point_eq_vertical z
  rw [hpoint] at h
  exact h

/-! ### §2 Residual quantitative core (premise-gated, sorry-free) -/

/-- Upper sliver rect packaged from uniform data: the off-axis hypothesis
`hne` is kept (unused) so the statement feeds the `hSliver` shape directly. -/
theorem sliverTopRect_of_uniform_plus_width {δT : ℝ}
    (hstripT : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      (1 / 2 : ℝ) - δT < y → y < (1 / 2 : ℝ) →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0)
    (hwidthT : (1 / 2 : ℝ) - δT < 0.49) :
    ∀ z : ℂ, (z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) →
      (0.49 : ℝ) ≤ z.im → z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      xiShifted z ≠ 0 := by
  intro z heq hlo hhi _
  exact top_sliver_of_uniform_strip hstripT hwidthT heq hlo hhi

/-- Lower sliver rect packaged from uniform data (mirror). -/
theorem sliverBotRect_of_uniform_plus_width {δB : ℝ}
    (hstripB : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      -(1 / 2 : ℝ) < y → y < -(1 / 2 : ℝ) + δB →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0)
    (hwidthB : (-0.49 : ℝ) < -(1 / 2 : ℝ) + δB) :
    ∀ z : ℂ, (z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) →
      -(1 / 2 : ℝ) < z.im → z.im ≤ (-0.49 : ℝ) → z.im ≠ 0 →
      xiShifted z ≠ 0 := by
  intro z heq hgt hhi _
  exact bottom_sliver_of_uniform_strip hstripB hwidthB heq hgt hhi

/-! ### §3 Final `hSliver`-shaped theorem (premise (d)) -/

/-- The exact `hSliver` premise shape of
`Door3RHWiring.xiCutoffLines10_of_cutR10_and_leftLine`
(`door3_rh_wiring.lean:92-94`), proved conditional on the two sliver-rect
premises (upper `0.49 ≤ Im < 1/2`, lower `-1/2 < Im ≤ -0.49`). -/
theorem sliver_nonvanishing_of_topBotRects
    (hTop : ∀ z : ℂ, (z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) →
      (0.49 : ℝ) ≤ z.im → z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      xiShifted z ≠ 0)
    (hBot : ∀ z : ℂ, (z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) →
      -(1 / 2 : ℝ) < z.im → z.im ≤ (-0.49 : ℝ) → z.im ≠ 0 →
      xiShifted z ≠ 0)
    (z : ℂ) (heq : z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ))
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ))
    (hne : z.im ≠ 0) (hs : (0.49 : ℝ) ≤ z.im ∨ z.im ≤ -0.49) :
    xiShifted z ≠ 0 := by
  rcases hs with h | h
  · exact hTop z heq h hlt hne
  · exact hBot z heq hgt h hne

/-- End-to-end sliver supply: banked uniform-strip certificates + the two
numeric width premises discharge the exact `hSliver` shape. Fix-wave recipe
for the certificate premises: `obtain ⟨δT, _, hT⟩ :=
Door3TopEdge.exists_top_edge_uniform_strip (show (-10:ℝ) ≤ 10 by norm_num)`
(and the bottom mirror); the ONLY genuinely new obligations are `hwidthT`
and `hwidthB` below. -/
theorem hSliver_of_uniformData {δT δB : ℝ}
    (hstripT : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      (1 / 2 : ℝ) - δT < y → y < (1 / 2 : ℝ) →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0)
    (hwidthT : (1 / 2 : ℝ) - δT < 0.49)
    (hstripB : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      -(1 / 2 : ℝ) < y → y < -(1 / 2 : ℝ) + δB →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0)
    (hwidthB : (-0.49 : ℝ) < -(1 / 2 : ℝ) + δB)
    (z : ℂ) (heq : z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ))
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ))
    (hne : z.im ≠ 0) (hs : (0.49 : ℝ) ≤ z.im ∨ z.im ≤ -0.49) :
    xiShifted z ≠ 0 := by
  have hTop := sliverTopRect_of_uniform_plus_width hstripT hwidthT
  have hBot := sliverBotRect_of_uniform_plus_width hstripB hwidthB
  exact sliver_nonvanishing_of_topBotRects hTop hBot z heq hgt hlt hne hs

end Door3SliverNonvan

/-! ### §4 Quantitative width machinery (proved, generic)

Route documented here (all read-only sources):
* edge lower numerals: mirror `door3_center_bounds.lean` / `door3_real_center_bounds.lean`
  real-axis pattern (`s ^ 2 / 4`-style lower from zeta-re plus prefactor), applied at the
  top-edge points `(x : ℂ) + Complex.I / 2` and bottom points `(x : ℂ) - Complex.I / 2`;
* Cauchy derivative sup: mirror `DerivCauchyBridge.uniform_deriv_of_closedBall_bound`
  (`central_cover_assembly.lean:6233`) and `Door3TopEdge.exists_deriv_bound_on_closedBall`
  (`door3_top_edge.lean:666`); the helper `sliver_entire_deriv_le_of_sphere_bound` below
  re-proves the pointwise Cauchy step with a distinct name;
* fencing: `BoundaryProofEngine.upper_boundary_nonvanishing_from_outer_bound`
  (`rh_certificate_infra.lean:459`, width `ε / M`) for the top and
  `Door3TopEdge.lower_boundary_nonvanishing_from_outer_bound`
  (`door3_top_edge.lean:397`) for the bottom;
* transfer back to `xiShifted` inside the open strip via
  `CentralCoverAssembly.xiShifted_eq_entire_on_strip`.

Strict-`<` form is kept throughout (`y < 1 / 2` on top, `-(1 / 2) < y` on bottom) so the
open-strip agreement applies.
-/

namespace Door3SliverNonvan

open CentralCoverAssembly

/-- Top width gate as an explicit iff: `1 / 2 - d < 0.49` holds exactly when `0.01 < d`. -/
theorem sliver_width_gate_top_iff (d : ℝ) :
    (1 / 2 : ℝ) - d < 0.49 ↔ (0.01 : ℝ) < d := by
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- Bottom width gate as an explicit iff: `-0.49 < -(1 / 2) + d` holds exactly when `0.01 < d`. -/
theorem sliver_width_gate_bottom_iff (d : ℝ) :
    (-0.49 : ℝ) < -(1 / 2 : ℝ) + d ↔ (0.01 : ℝ) < d := by
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- Ratio form of the top gate: `1 / 2 - r < 0.49` iff `0.01 < r`. Sharpest true-width
characterization; no numerics assumed. -/
theorem sliver_gate_ratio_iff (r : ℝ) :
    (1 / 2 : ℝ) - r < 0.49 ↔ (0.01 : ℝ) < r := by
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- Ratio form of the bottom gate. -/
theorem sliver_gate_ratio_bottom_iff (r : ℝ) :
    (-0.49 : ℝ) < -(1 / 2 : ℝ) + r ↔ (0.01 : ℝ) < r := by
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- Pointwise Cauchy step for the entire extension, mirroring
`DerivCauchyBridge.deriv_xiShifted_le_of_entire_sphere_bound` with a distinct name:
a sup `C` on `sphere w r` gives `‖deriv‖ ≤ C / r` at `w`. -/
theorem sliver_entire_deriv_le_of_sphere_bound (w : ℂ) (r : ℝ) (C : ℝ) (hr : 0 < r)
    (hC : ∀ z ∈ Metric.sphere w r,
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ‖deriv CentralCoverAssembly.xiShiftedEntire w‖ ≤ C / r := by
  have hDC : DiffContOnCl ℂ CentralCoverAssembly.xiShiftedEntire (Metric.ball w r) :=
    CentralCoverAssembly.xiShiftedEntire_differentiable.diffContOnCl
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hDC hC

/-- Generic top strip from explicit entire data. `mT` is the edge lower numeral,
`MT` the vertical derivative sup; the fenced width is `mT / MT`. The side condition
`mT / MT ≤ 1` keeps the strip inside `(-(1 / 2), 1 / 2)` for the transfer. -/
theorem sliver_top_strip_of_entire_data (mT : ℝ) (MT : ℝ) (hmT : 0 < mT) (hMT : 0 < MT)
    (hTop : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      mT ≤ ‖CentralCoverAssembly.xiShiftedEntire ((x : ℂ) + Complex.I * (1 / 2 : ℂ))‖)
    (hDeriv : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      ∀ y ∈ Set.Icc ((1 / 2 : ℝ) - mT / MT) (1 / 2 : ℝ),
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ MT)
    (hδle : mT / MT ≤ 1)
    (x : ℝ) (hx : x ∈ Set.Icc (-10 : ℝ) (10 : ℝ)) (y : ℝ)
    (hy_low : (1 / 2 : ℝ) - mT / MT < y) (hy_top : y < (1 / 2 : ℝ)) :
    xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
  have htopbound : mT ≤ ‖CentralCoverAssembly.xiShiftedEntire
      ((x : ℂ) + Complex.I * (1 / 2 : ℂ))‖ :=
    hTop x hx
  have hderiv : ∀ v ∈ Set.Icc ((1 / 2 : ℝ) - mT / MT) (1 / 2 : ℝ),
      ‖deriv CentralCoverAssembly.xiShiftedEntire
        ((x : ℂ) + Complex.I * (v : ℂ))‖ ≤ MT := by
    intro v hv
    exact hDeriv x hx v hv
  have hne_ent : CentralCoverAssembly.xiShiftedEntire
      ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
    have hres := BoundaryProofEngine.upper_boundary_nonvanishing_from_outer_bound
      CentralCoverAssembly.xiShiftedEntire
      CentralCoverAssembly.xiShiftedEntire_differentiable x mT MT hmT hMT htopbound
      hderiv y hy_low (le_of_lt hy_top)
    exact hres
  have hpos : 0 < mT / MT := div_pos hmT hMT
  have hstrip_lo : -(1 / 2 : ℝ) < y := by linarith
  have him : (((x : ℂ) + Complex.I * (y : ℂ))).im = y := by simp
  have hgt : -(1 / 2 : ℝ) < (((x : ℂ) + Complex.I * (y : ℂ))).im := by
    rw [him]
    exact hstrip_lo
  have hlt : (((x : ℂ) + Complex.I * (y : ℂ))).im < (1 / 2 : ℝ) := by
    rw [him]
    exact hy_top
  have hagree : xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) =
      CentralCoverAssembly.xiShiftedEntire ((x : ℂ) + Complex.I * (y : ℂ)) :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip _ hgt hlt
  rw [hagree]
  exact hne_ent

/-- Generic bottom strip from explicit entire data (mirror via
`Door3TopEdge.lower_boundary_nonvanishing_from_outer_bound`). -/
theorem sliver_bottom_strip_of_entire_data (mB : ℝ) (MB : ℝ) (hmB : 0 < mB) (hMB : 0 < MB)
    (hBot : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      mB ≤ ‖CentralCoverAssembly.xiShiftedEntire
        ((x : ℂ) - Complex.I * (1 / 2 : ℂ))‖)
    (hDeriv : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      ∀ y ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + mB / MB),
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ MB)
    (hδle : mB / MB ≤ 1)
    (x : ℝ) (hx : x ∈ Set.Icc (-10 : ℝ) (10 : ℝ)) (y : ℝ)
    (hy_lo : -(1 / 2 : ℝ) < y) (hy_hi : y < -(1 / 2 : ℝ) + mB / MB) :
    xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
  have hbotbound : mB ≤ ‖CentralCoverAssembly.xiShiftedEntire
      ((x : ℂ) - Complex.I * (1 / 2 : ℂ))‖ :=
    hBot x hx
  have hderiv : ∀ v ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + mB / MB),
      ‖deriv CentralCoverAssembly.xiShiftedEntire
        ((x : ℂ) + Complex.I * (v : ℂ))‖ ≤ MB := by
    intro v hv
    exact hDeriv x hx v hv
  have hne_ent : CentralCoverAssembly.xiShiftedEntire
      ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
    have hres := Door3TopEdge.lower_boundary_nonvanishing_from_outer_bound
      CentralCoverAssembly.xiShiftedEntire
      CentralCoverAssembly.xiShiftedEntire_differentiable x mB MB hmB hMB hbotbound
      hderiv y hy_lo hy_hi
    exact hres
  have hpos : 0 < mB / MB := div_pos hmB hMB
  have hstrip_hi : y < (1 / 2 : ℝ) := by linarith
  have him : (((x : ℂ) + Complex.I * (y : ℂ))).im = y := by simp
  have hgt : -(1 / 2 : ℝ) < (((x : ℂ) + Complex.I * (y : ℂ))).im := by
    rw [him]
    exact hy_lo
  have hlt : (((x : ℂ) + Complex.I * (y : ℂ))).im < (1 / 2 : ℝ) := by
    rw [him]
    exact hstrip_hi
  have hagree : xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) =
      CentralCoverAssembly.xiShiftedEntire ((x : ℂ) + Complex.I * (y : ℂ)) :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip _ hgt hlt
  rw [hagree]
  exact hne_ent

/-- Vertical-line conjugation identity (proved, not assumed). -/
theorem sliver_star_vertical (x : ℝ) (y : ℝ) :
    star (((x : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ)) =
      ((x : ℝ) : ℂ) + Complex.I * (((-y : ℝ)) : ℂ) := by
  apply Complex.ext
  · simp
  · simp

/-- General conjugation transfer for `xiShifted` inside the strip (proved from the
banked `Door3ResidualScout.door3_conj_transfer`, i.e. `classicalXi_symmetry.conj_symm`). -/
theorem sliver_conj_transfer_general (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ))
    (hz : xiShifted z ≠ 0) :
    xiShifted (star z) ≠ 0 :=
  Door3ResidualScout.door3_conj_transfer (by linarith : (-1 / 2 : ℝ) < z.im) hlt hz

/-- Bottom strip derived from a top strip via proved conjugation (allowed route).
Needs `d ≤ 1` so the mirror point stays in the strip. -/
theorem sliver_bottom_of_top_via_conj (d : ℝ) (hd : 0 < d) (hdle : d ≤ 1)
    (hTop : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      (1 / 2 : ℝ) - d < y → y < (1 / 2 : ℝ) →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0)
    (x : ℝ) (hx : x ∈ Set.Icc (-10 : ℝ) (10 : ℝ)) (y : ℝ)
    (hy_lo : -(1 / 2 : ℝ) < y) (hy_hi : y < -(1 / 2 : ℝ) + d) :
    xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
  have hy_neg_lo : (1 / 2 : ℝ) - d < -y := by linarith
  have hy_neg_hi : -y < (1 / 2 : ℝ) := by linarith
  have hne_mirror : xiShifted ((x : ℂ) + Complex.I * (((-y : ℝ)) : ℂ)) ≠ 0 :=
    hTop x hx (-y) hy_neg_lo hy_neg_hi
  have him : ((((x : ℝ) : ℂ) + Complex.I * (((-y : ℝ)) : ℂ))).im = -y := by simp
  have him_lo : -(1 / 2 : ℝ) < ((((x : ℝ) : ℂ) + Complex.I * (((-y : ℝ)) : ℂ))).im := by
    rw [him]
    linarith
  have him_hi : ((((x : ℝ) : ℂ) + Complex.I * (((-y : ℝ)) : ℂ))).im < (1 / 2 : ℝ) := by
    rw [him]
    linarith
  have him_lo' : (-1 / 2 : ℝ) < ((((x : ℝ) : ℂ) + Complex.I * (((-y : ℝ)) : ℂ))).im := by
    linarith
  have hstar : xiShifted
      (star (((x : ℝ) : ℂ) + Complex.I * (((-y : ℝ)) : ℂ))) ≠ 0 :=
    Door3ResidualScout.door3_conj_transfer him_lo' him_hi hne_mirror
  have hbase : star (((x : ℝ) : ℂ) + Complex.I * (((-y : ℝ)) : ℂ)) =
      ((x : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ) := by
    have h := sliver_star_vertical x (-y)
    have hcast : (((-(-y : ℝ) : ℝ)) : ℂ) = ((y : ℝ) : ℂ) := by
      rw [neg_neg]
    rw [hcast] at h
    exact h
  rw [hbase] at hstar
  exact hstar

/-! ### §5 Landed widths, sharpest form, and shortfall

Status: the two `0.01` gates are closed CONDITIONAL on explicit numeric lower / deriv
premises (the genuinely unclosable supplier obligations). No numerals are faked:
the arithmetic `0.011 > 0.01` examples below are proved by `norm_num`, while the
supplier bounds `mT / MT > 0.01` remain explicit hypotheses. The sharpest true width
from given data is `m / M` (any smaller width also works; §5 mono lemmas), and the
shortfall identity quantifies the miss when `m / M ≤ 0.01`.
-/

/-- Proved arithmetic: the example width `11 / 1000 = 0.011` clears the top gate. -/
theorem sliver_example_width_arith_top :
    (1 / 2 : ℝ) - 11 / 1000 < 0.49 := by norm_num

/-- Proved arithmetic: the example width `11 / 1000 = 0.011` clears the bottom gate. -/
theorem sliver_example_width_arith_bottom :
    (-0.49 : ℝ) < -(1 / 2 : ℝ) + 11 / 1000 := by norm_num

/-- Proved arithmetic: `0.011` strictly exceeds `0.01`. -/
theorem sliver_example_gate_top :
    (0.01 : ℝ) < 11 / 1000 := by norm_num

/-- Sharpest-width monotonicity on top: any `d ≤ mT / MT` inherits the fenced strip,
so `mT / MT` is the largest width the data yield. -/
theorem sliver_sharp_mono_top (mT : ℝ) (MT : ℝ) (hmT : 0 < mT) (hMT : 0 < MT)
    (hTop : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      mT ≤ ‖CentralCoverAssembly.xiShiftedEntire ((x : ℂ) + Complex.I * (1 / 2 : ℂ))‖)
    (hDeriv : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      ∀ y ∈ Set.Icc ((1 / 2 : ℝ) - mT / MT) (1 / 2 : ℝ),
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ MT)
    (hδle : mT / MT ≤ 1)
    (d : ℝ) (hdle : d ≤ mT / MT)
    (x : ℝ) (hx : x ∈ Set.Icc (-10 : ℝ) (10 : ℝ)) (y : ℝ)
    (hy_low : (1 / 2 : ℝ) - d < y) (hy_top : y < (1 / 2 : ℝ)) :
    xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
  have hy_low2 : (1 / 2 : ℝ) - mT / MT < y := by linarith
  exact sliver_top_strip_of_entire_data mT MT hmT hMT hTop hDeriv hδle x hx y hy_low2 hy_top

/-- Sharpest-width monotonicity on bottom (mirror). -/
theorem sliver_sharp_mono_bottom (mB : ℝ) (MB : ℝ) (hmB : 0 < mB) (hMB : 0 < MB)
    (hBot : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      mB ≤ ‖CentralCoverAssembly.xiShiftedEntire
        ((x : ℂ) - Complex.I * (1 / 2 : ℂ))‖)
    (hDeriv : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      ∀ y ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + mB / MB),
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ MB)
    (hδle : mB / MB ≤ 1)
    (d : ℝ) (hdle : d ≤ mB / MB)
    (x : ℝ) (hx : x ∈ Set.Icc (-10 : ℝ) (10 : ℝ)) (y : ℝ)
    (hy_lo : -(1 / 2 : ℝ) < y) (hy_hi : y < -(1 / 2 : ℝ) + d) :
    xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
  have hy_hi2 : y < -(1 / 2 : ℝ) + mB / MB := by linarith
  exact sliver_bottom_strip_of_entire_data mB MB hmB hMB hBot hDeriv hδle x hx y hy_lo hy_hi2

/-- Shortfall on top: if `mT / MT ≤ 0.01` then the fenced edge sits at or above `0.49`. -/
theorem sliver_shortfall_top (mT : ℝ) (MT : ℝ) (hshort : mT / MT ≤ 0.01) :
    (0.49 : ℝ) ≤ (1 / 2 : ℝ) - mT / MT := by linarith

/-- Shortfall on bottom (mirror). -/
theorem sliver_shortfall_bottom (mB : ℝ) (MB : ℝ) (hshort : mB / MB ≤ 0.01) :
    -(1 / 2 : ℝ) + mB / MB ≤ (-0.49 : ℝ) := by linarith

/-- Miss identity on top: the numeric miss `0.01 - mT / MT` equals the edge gap. -/
theorem sliver_miss_top (mT : ℝ) (MT : ℝ) :
    (0.01 : ℝ) - mT / MT = ((1 / 2 : ℝ) - mT / MT) - (0.49 : ℝ) := by ring

/-- Miss identity on bottom (mirror). -/
theorem sliver_miss_bottom (mB : ℝ) (MB : ℝ) :
    (0.01 : ℝ) - mB / MB = (-0.49 : ℝ) - (-(1 / 2 : ℝ) + mB / MB) := by ring

/-- End-to-end `hSliver` supply from explicit numeric edge data (both edges direct).
Residual premises (genuinely unclosable suppliers): `hTopLower`, `hTopDeriv`,
`hBotLower`, `hBotDeriv` plus the two ratio gates `hGateT`, `hGateB` and the
`≤ 1` side conditions. Width premises are DERIVED via `linarith`, not assumed. -/
theorem sliver_hSliver_of_numericData (mT : ℝ) (MT : ℝ) (mB : ℝ) (MB : ℝ)
    (hmT : 0 < mT) (hMT : 0 < MT) (hmB : 0 < mB) (hMB : 0 < MB)
    (hδTle : mT / MT ≤ 1) (hδBle : mB / MB ≤ 1)
    (hTopLower : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      mT ≤ ‖CentralCoverAssembly.xiShiftedEntire ((x : ℂ) + Complex.I * (1 / 2 : ℂ))‖)
    (hTopDeriv : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      ∀ y ∈ Set.Icc ((1 / 2 : ℝ) - mT / MT) (1 / 2 : ℝ),
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ MT)
    (hGateT : (0.01 : ℝ) < mT / MT)
    (hBotLower : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      mB ≤ ‖CentralCoverAssembly.xiShiftedEntire
        ((x : ℂ) - Complex.I * (1 / 2 : ℂ))‖)
    (hBotDeriv : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      ∀ y ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + mB / MB),
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ MB)
    (hGateB : (0.01 : ℝ) < mB / MB)
    (z : ℂ) (heq : z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ))
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ))
    (hne : z.im ≠ 0) (hs : (0.49 : ℝ) ≤ z.im ∨ z.im ≤ -0.49) :
    xiShifted z ≠ 0 := by
  have hwidthT : (1 / 2 : ℝ) - mT / MT < 0.49 := by linarith
  have hwidthB : (-0.49 : ℝ) < -(1 / 2 : ℝ) + mB / MB := by linarith
  have hstripT : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      (1 / 2 : ℝ) - mT / MT < y → y < (1 / 2 : ℝ) →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
    intro x hx y hy_low hy_top
    exact sliver_top_strip_of_entire_data mT MT hmT hMT hTopLower hTopDeriv hδTle x hx y
      hy_low hy_top
  have hstripB : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      -(1 / 2 : ℝ) < y → y < -(1 / 2 : ℝ) + mB / MB →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
    intro x hx y hy_lo hy_hi
    exact sliver_bottom_strip_of_entire_data mB MB hmB hMB hBotLower hBotDeriv hδBle x hx y
      hy_lo hy_hi
  exact Door3SliverNonvan.hSliver_of_uniformData hstripT hwidthT hstripB hwidthB z heq hgt
    hlt hne hs

/-- End-to-end `hSliver` supply from TOP numeric data only, bottom via proved
conjugation. Residual premises: `hTopLower`, `hTopDeriv`, `hGateT`, `hδTle`. -/
theorem sliver_hSliver_of_topNumericData_via_conj (mT : ℝ) (MT : ℝ)
    (hmT : 0 < mT) (hMT : 0 < MT)
    (hδTle : mT / MT ≤ 1)
    (hTopLower : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      mT ≤ ‖CentralCoverAssembly.xiShiftedEntire ((x : ℂ) + Complex.I * (1 / 2 : ℂ))‖)
    (hTopDeriv : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      ∀ y ∈ Set.Icc ((1 / 2 : ℝ) - mT / MT) (1 / 2 : ℝ),
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ MT)
    (hGateT : (0.01 : ℝ) < mT / MT)
    (z : ℂ) (heq : z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ))
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ))
    (hne : z.im ≠ 0) (hs : (0.49 : ℝ) ≤ z.im ∨ z.im ≤ -0.49) :
    xiShifted z ≠ 0 := by
  have hpos : 0 < mT / MT := div_pos hmT hMT
  have hwidth : (1 / 2 : ℝ) - mT / MT < 0.49 := by linarith
  have hwidthB : (-0.49 : ℝ) < -(1 / 2 : ℝ) + mT / MT := by linarith
  have hstripT : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      (1 / 2 : ℝ) - mT / MT < y → y < (1 / 2 : ℝ) →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
    intro x hx y hy_low hy_top
    exact sliver_top_strip_of_entire_data mT MT hmT hMT hTopLower hTopDeriv hδTle x hx y
      hy_low hy_top
  have hstripB : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      -(1 / 2 : ℝ) < y → y < -(1 / 2 : ℝ) + mT / MT →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
    intro x hx y hy_lo hy_hi
    exact sliver_bottom_of_top_via_conj (mT / MT) hpos hδTle hstripT x hx y hy_lo hy_hi
  exact Door3SliverNonvan.hSliver_of_uniformData hstripT hwidth hstripB hwidthB z heq hgt
    hlt hne hs

/-- `hSliver` from TOP numeric data at feasible `mT = 1/2`, `MT = 40`, bottom via
proved conjugation. Mirrors `hSliver_of_topNumericData_011_via_conj`
(`door3_rh_wiring.lean:251`) with `mT` fixed at the maximal closable uniform value;
the gate `(0.01 < (1/2)/40)` and side conditions close by `norm_num`, leaving only
the two supplier bounds (`hTopLower`/`hTopDeriv`) as residual premises. -/
theorem sliver_hSliver_of_topHalf_M40_via_conj
    (hTopLower : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      (1 / 2 : ℝ) ≤ ‖CentralCoverAssembly.xiShiftedEntire ((x : ℂ) + Complex.I * (1 / 2 : ℂ))‖)
    (hTopDeriv : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      ∀ y ∈ Set.Icc ((1 / 2 : ℝ) - (1 / 2 : ℝ) / (40 : ℝ)) (1 / 2 : ℝ),
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ (40 : ℝ)) :
    ∀ z : ℂ, (z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) →
      -(1 / 2 : ℝ) < z.im → z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      (0.49 ≤ z.im ∨ z.im ≤ -0.49) → xiShifted z ≠ 0 :=
  Door3SliverNonvan.sliver_hSliver_of_topNumericData_via_conj (1 / 2 : ℝ) (40 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    hTopLower hTopDeriv (by norm_num)

/-- Top strip derived from a bottom strip via proved conjugation (mirror of
`sliver_bottom_of_top_via_conj`, `Im → -Im` flipped). Needs `d ≤ 1` so the
mirror point stays in the strip. Proved from the same banked
`Door3ResidualScout.door3_conj_transfer` + `sliver_star_vertical`. -/
theorem sliver_top_of_bottom_via_conj (d : ℝ) (hd : 0 < d) (hdle : d ≤ 1)
    (hBot : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      -(1 / 2 : ℝ) < y → y < -(1 / 2 : ℝ) + d →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0)
    (x : ℝ) (hx : x ∈ Set.Icc (-10 : ℝ) (10 : ℝ)) (y : ℝ)
    (hy_low : (1 / 2 : ℝ) - d < y) (hy_hi : y < (1 / 2 : ℝ)) :
    xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
  have hy_neg_lo : -(1 / 2 : ℝ) < -y := by linarith
  have hy_neg_hi : -y < -(1 / 2 : ℝ) + d := by linarith
  have hne_mirror : xiShifted ((x : ℂ) + Complex.I * (((-y : ℝ)) : ℂ)) ≠ 0 :=
    hBot x hx (-y) hy_neg_lo hy_neg_hi
  have him : ((((x : ℝ) : ℂ) + Complex.I * (((-y : ℝ)) : ℂ))).im = -y := by simp
  have him_lo : -(1 / 2 : ℝ) < ((((x : ℝ) : ℂ) + Complex.I * (((-y : ℝ)) : ℂ))).im := by
    rw [him]
    linarith
  have him_hi : ((((x : ℝ) : ℂ) + Complex.I * (((-y : ℝ)) : ℂ))).im < (1 / 2 : ℝ) := by
    rw [him]
    linarith
  have him_lo' : (-1 / 2 : ℝ) < ((((x : ℝ) : ℂ) + Complex.I * (((-y : ℝ)) : ℂ))).im := by
    linarith
  have hstar : xiShifted
      (star (((x : ℝ) : ℂ) + Complex.I * (((-y : ℝ)) : ℂ))) ≠ 0 :=
    Door3ResidualScout.door3_conj_transfer him_lo' him_hi hne_mirror
  have hbase : star (((x : ℝ) : ℂ) + Complex.I * (((-y : ℝ)) : ℂ)) =
      ((x : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ) := by
    have h := sliver_star_vertical x (-y)
    have hcast : (((-(-y : ℝ) : ℝ)) : ℂ) = ((y : ℝ) : ℂ) := by
      rw [neg_neg]
    rw [hcast] at h
    exact h
  rw [hbase] at hstar
  exact hstar

/-- End-to-end `hSliver` supply from BOTTOM numeric data only, top via proved
conjugation. Mirror of `sliver_hSliver_of_topNumericData_via_conj`
(`Im → -Im`, `mB`/`MB` symmetric). Residual premises: `hBotLower`, `hBotDeriv`,
`hGateB`, `hδBle`. -/
theorem sliver_hSliver_of_botNumericData_via_conj (mB : ℝ) (MB : ℝ)
    (hmB : 0 < mB) (hMB : 0 < MB)
    (hδBle : mB / MB ≤ 1)
    (hBotLower : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      mB ≤ ‖CentralCoverAssembly.xiShiftedEntire ((x : ℂ) - Complex.I * (1 / 2 : ℂ))‖)
    (hBotDeriv : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      ∀ y ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + mB / MB),
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ MB)
    (hGateB : (0.01 : ℝ) < mB / MB)
    (z : ℂ) (heq : z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ))
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ))
    (hne : z.im ≠ 0) (hs : (0.49 : ℝ) ≤ z.im ∨ z.im ≤ -0.49) :
    xiShifted z ≠ 0 := by
  have hpos : 0 < mB / MB := div_pos hmB hMB
  have hwidth : (1 / 2 : ℝ) - mB / MB < 0.49 := by linarith
  have hwidthB : (-0.49 : ℝ) < -(1 / 2 : ℝ) + mB / MB := by linarith
  have hstripB : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      -(1 / 2 : ℝ) < y → y < -(1 / 2 : ℝ) + mB / MB →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
    intro x hx y hy_lo hy_hi
    exact sliver_bottom_strip_of_entire_data mB MB hmB hMB hBotLower hBotDeriv hδBle x hx y
      hy_lo hy_hi
  have hstripT : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ), ∀ y : ℝ,
      (1 / 2 : ℝ) - mB / MB < y → y < (1 / 2 : ℝ) →
        xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
    intro x hx y hy_low hy_top
    exact sliver_top_of_bottom_via_conj (mB / MB) hpos hδBle hstripB x hx y hy_low hy_top
  exact Door3SliverNonvan.hSliver_of_uniformData hstripT hwidth hstripB hwidthB z heq hgt
    hlt hne hs

/-- `hSliver` from BOTTOM numeric data at feasible `mB = 1/2`, `MB = 40`, top via
proved conjugation. Mirror of `sliver_hSliver_of_topHalf_M40_via_conj` (`:594`)
token-for-token with bottom data + conj direction flipped;
the gate `(0.01 < (1/2)/40)` and side conditions close by `norm_num`, leaving only
the two supplier bounds (`hBotLower`/`hBotDeriv`) as residual premises. -/
theorem sliver_hSliver_of_botHalf_M40_via_conj
    (hBotLower : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      (1 / 2 : ℝ) ≤ ‖CentralCoverAssembly.xiShiftedEntire ((x : ℂ) - Complex.I * (1 / 2 : ℂ))‖)
    (hBotDeriv : ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
      ∀ y ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + (1 / 2 : ℝ) / (40 : ℝ)),
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ (40 : ℝ)) :
    ∀ z : ℂ, (z.re = (10 : ℝ) ∨ z.re = (-10 : ℝ)) →
      -(1 / 2 : ℝ) < z.im → z.im < (1 / 2 : ℝ) → z.im ≠ 0 →
      (0.49 ≤ z.im ∨ z.im ≤ -0.49) → xiShifted z ≠ 0 :=
  Door3SliverNonvan.sliver_hSliver_of_botNumericData_via_conj (1 / 2 : ℝ) (40 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    hBotLower hBotDeriv (by norm_num)

end Door3SliverNonvan

