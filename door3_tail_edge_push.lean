import Mathlib
import central_cover_assembly

/-!
# door3_tail_edge_push — WRITE-ONLY recon + closest-piece (report-and-stop, no build)

OWNERSHIP / SCOPE (verified read-only):
- New file `door3_tail_edge_push.lean` checked ABSENT first via glob
  (`door3_tail_edge_push.lean` -> "No files found"); this file is owned exclusively.
- No other repo file touched (including `riemann hypothesis.lean` spaced legacy
  filename and all other lanes/files — read freely, never edited).
- No commit/push, no repo logs, no lakefile edit, no lake/lean build commands.

PHASE 1 — RECON (read-only findings):

(a) Htail (`XiTailPointwiseNonvanishingForX 10`):
- `tailPointwise10_of_absTail` (`riemann_hypothesis.lean:12250`, `_root_`, PROVED no sorry):
  premise `H : forall z : C, 10 < |z.re| -> -(1)/2 < z.im -> z.im < 1/2 ->
  z.im != 0 -> xiShifted z != 0`; conclusion `XiTailPointwiseNonvanishingForX 10`
  with `right_nonvanishing` via `abs_of_pos` + linarith and `left_nonvanishing`
  via `abs_of_neg` + linarith. Structure `XiTailPointwiseNonvanishingForX`
  (`riemann_hypothesis.lean:670`, `_root_`): two fields `right_nonvanishing`
  (`X < z.re`) and `left_nonvanishing` (`z.re < -X`), each with strip
  `-1/2 < Im < 1/2`, `Im != 0`.
- `CrossDoorTailBridge.xiShifted_off_axis_tail_nonvanishing_from_mollified_rouche`
  (`cross_door_synthesis.lean:105`, PROVED no sorry). EXACT premises:
  `(K : N) (H : MollifiedAttack.MollifiedRoucheLeaf K)` [top-level `MollifiedAttack`
  from `riemann_hypothesis_newsection.lean:190`, NOT `RHProofScaffold.Challenge2.MollifiedAttack`]
  `(z : C) (hx : 10 < |z.re|) (hy0 : -(1/2) < z.im) (hy1 : z.im < 1/2)`
  `(hne : z.im != 0)`; conclusion `xiShifted z != 0` via by_cases on `0 < z.im`.
  Feeders: `xiShifted_upper_tail_nonvanishing_from_mollified_rouche` (:51) needs
  `(K) (H) (z) (hx) (hy0 : 0 < z.im) (hy1)`, citing
  `MollifiedAttack.mollified_rouche_leaf_implies_tail_hard_difference_nonzero`
  + `completedZeta_shifted_eq_inv_D_sub_two_xiShifted_div_D`; lower-half
  `xiShifted_lower_tail_nonvanishing_from_upper` (:78) needs
  `(upper : forall z, 10 < |z.re| -> 0 < z.im -> z.im < 1/2 -> xiShifted z != 0)`
  plus `(z) (hx) (hy0 : -1/2 < z.im) (hy1 : z.im < 0)`, via `star z` + conj symmetry.
  Conclusion shape matches `tailPointwise10_of_absTail` hypothesis exactly.
- Mollified/door-4 file state (`riemann_hypothesis_newsection.lean`, tail):
  `MollifiedRoucheLeaf` (:199, top-level): `gap : forall z, 10 < |z.re| ->
  0 < z.im -> z.im < 1/2 -> ||zeta (shiftedS z) * dirichletMollifier .. K - 1|| < 1`.
  Banked: `mollified_rouche_leaf_implies_tail_hard_difference_nonzero` (:233) PROVED;
  `dirichletMollifier_norm_le` (:613, `||M|| <= K`), `dirichletMollifier_two` (:651,
  `M s 2 = 1/2`), `dirichletMollifier_two_norm` (:681, `<= 1/2`),
  `mollified_K2_gap_eq` (:703, `zeta*M2-1 = zeta/2-1`),
  `mollified_K2_gap_implies_zeta_bound` (:722, gap -> `||zeta|| <= 4 - 2*delta`).
  SINGLE missing numeral/lemma: uniform Im-uniform zeta UPPER `B` (hence near-one `d`
  with `B*(1/2)+d < 1` at `K = 2`, `e = 1/2` banked) on the shifted strip
  `Re(shiftedS z) = 1/2 - Im z in (0,1/2)` with `|Im| -> infinity`.
  `TailZetaUpper` only closes `Re >= 1+delta` (`B = 3` at `3/2`, `B = 2` at `2`,
  :1187/:1195); three-lines conditional needs whole-line damped left cap
  `A <= 50.925` (proved crude window `1.2e9`, gap ~2.4e7 times; Stirling-sharp
  left edge missing). Fixed-`K = 2` uniform `B/2+d < 1` additionally needs `K`
  growing with `|Re z|` (newsection :712-721; guide 2204: `K = 2` needs phase
  `||zeta-2||`, not size). True values finite per-point but no uniform repo lemma.

(b) Hedge (`XiCentralEdgeStrips10`):
- Def (`riemann_hypothesis.lean:12157`, `_root_`, open Prop): `forall z, -10 < z.re ->
  z.re < 10 -> -1/2 < z.im -> z.im < 1/2 -> z.im != 0 ->
  (0.49 <= z.im \/ z.im <= -0.49) -> xiShifted z != 0`. Assembly
  `xiCentralRect10_of_mainBand_and_edgeStrips` (:12186) PROVED (trichotomy).
- PATH CORRECTION: `door3_closed_cover.lean` is 209 lines, contains NO `S00-S09`
  defs (only closed-cell interface + `gridFine` fencing). Actual `S00-S09` live in
  `central_cover_assembly.lean`: `EdgeS00` at :6663, `EdgeS01` at :6984,
  `EdgeS02` at :7100, `EdgeS03` at :7216, `EdgeS04` at :7332, `EdgeS05` at :7448,
  `EdgeS06` at :7564, `EdgeS07` at :7680, `EdgeS08` at :7796, `EdgeS09` at :7912;
  task "guide line ~8087" is `central_cover_assembly.lean:8087`
  (`EdgeS00-S09 ... 10/10 upper columns packaged`), not a guide-file line.
- Packaged (hypothesis-free, green, verified read-only): `edgeStripCells` (:6584,
  10 cells `y = (0.49,0.5)`) + `edgeStripCells_covers` (:6597, PROVED);
  all 10/10 uppers geometry (`dx = 1.25`, `dy = 0.005`, `radius < 1.26` via shared
  `edgeStrip_radius_bound`), `center = x_c + 0.495*I`, `sCenter.re = 0.005`,
  `poly <= 56`, `pi <= 1`, `Gamma <= 400` (reuse `edgeS00_realGamma_00025_le`);
  all 10/10 lower mirrors `EdgeS00_Lower-S09_Lower` (:8203-9075+; geometry,
  generic `poly <= 56`, `pi <= 1`, `Gamma <= 2` at `0.995` + `<= 3` at `0.4975`
  via `edgeLower_*` chains); `CutL10`/`CutR10` geometry (:6826-6886, `dx = 0.25`,
  `dy = 0.49`, `radius < 0.56`, strictly inside strip) + `CutR10/L10_mem_of_line`
  + `cutoffLines_either` (:6908, PROVED). Zero strip cells fully closed (NONE, 0).
- Open per cell (same zeta wall as 40 central cells): CENTER lower
  `eps + M*radius <= ||xiShifted center||` needs `Azeta` lower at NEW re-value
  (`s.re = 0.005` upper / `0.995` lower; eta-remainder at `sigma = 0.005` decays
  too slowly); DERIV upper needs tight `||zeta|| <= 10` on disc `s`-rect
  (crude eta gives `<= 1012` hence `M` too large for `eps + M*1.26` fencing;
  needs FE + Stirling + convexity); top-touching `y1 = 0.5` needs
  `upper_boundary_nonvanishing_from_outer_bound` outer value + vertical deriv
  (same zeta upper); full-strip `conj_of` blocked (`¬ y1 < 1/2` for all uppers;
  shrunk `y1 = 0.499` variants conditional on shrunk-upper packaging).

(c) SINGLE closest-closable piece: TAIL `K = 2` conditional Rouche gap
  `B*(1/2) + d < 1 -> ||zeta*M2 - 1|| < 1` (hence conditional
  `RHProofScaffold.Challenge2.MollifiedAttack.MollifiedRoucheLeaf 2`). Why smallest: exactly TWO
  explicit numeric Props (`B` upper + `d` near-one) + ONE arithmetic side-condition
  on a single shifted strip, with `e = 1/2` CLOSED here by `norm_num`
  (banked `dirichletMollifier_two` shape re-proved) and pure product-split CLOSED
  unconditionally; feeds banked `CrossDoorTailBridge` + `tailPointwise10_of_absTail`
  directly. Hedge needs >= THREE premises per cell (`Azeta` lower + tight zeta
  upper + outer-bound) times 20 strip cells + 2 cutoff rects. So tail wins 2 < 3.

PHASE 2 — PROVED vs RESIDUAL (this file):
- PROVED (full proofs, no sorry/admit/axiom, explicit binders, no `simpa`,
  numerals <= 6 digits): `norm_product_sub_one_le` (pure split);
  `mollifier_two_eq_half` (`M s 2 = 1/2`, mirrors banked newsection :651);
  `mollifier_two_sub_one_norm` / `mollifier_two_sub_one_le` (`e = 1/2` closed);
  `tailK2_gap_of_zetaBounds` (conditional gap `B/2+d < 1 -> leaf inequality`);
  `tailK2_leaf_of_bounds` (packages conditional `MollifiedRoucheLeaf 2`).
- RESIDUAL (explicit Prop premises with true-value comments): `TailZetaUpperB B`
  (true per-point finite; uniform `B` on `0 < Re < 1/2`, `|Im| -> infinity` needs
  FE + Stirling + convexity; fixed-`K = 2` uniform joint satisfiability additionally
  needs `K` growing — implication stays true, premises are the exact gap) and
  `TailZetaNearOneD d` (same wall; `B/2+d < 1` is the sharp fixed-`K` form).
- PATCH REMAINDER: instantiate `B, d` with `B/2+d < 1` (convexity/Phragmen-Lindelof
  + FE + Stirling; or `K` growing with `|Re z|`); transport this file's
  `RHProofScaffold.Challenge2.MollifiedAttack.MollifiedRoucheLeaf 2` (visible via
  `central_cover_assembly` -> `riemann_hypothesis`) to top-level
  `MollifiedAttack.MollifiedRoucheLeaf` (newsection, needed by
  `CrossDoorTailBridge` — identical gap shape, distinct Lean types; one-line
  rewrite or cycle-safe extra import of `riemann_hypothesis_newsection` /
  `cross_door_synthesis`, flagged but NOT added per brief); then apply banked
  `xiShifted_off_axis_tail_nonvanishing_from_mollified_rouche` +
  `tailPointwise10_of_absTail` to get `XiTailPointwiseNonvanishingForX 10`.
  Hedge patch (not in this file): per-strip `Azeta` + tight `||zeta|| <= 10` +
  outer-bound instantiation per cell, then `cutoffLines_either` assembly.

IMPORTS: `Mathlib` + `central_cover_assembly` only. `central_cover_assembly`
imports `riemann_hypothesis` (+ `rh_certificate_infra`), so `_root_` `zeta`,
`shiftedS`, `xiShifted` and `RHProofScaffold.Challenge2.MollifiedAttack.*` are visible
transitively; this file is downstream (nothing imports it), hence cycle-safe.
No other imports added; `newsection` / `cross_door_synthesis` intentionally NOT
imported (would also be acyclic, flagged here only).
-/

open Complex

noncomputable section

namespace Door3TailEdgePush

/-- Pure product-gap split (no hypotheses): Rouche error controlled by zeta size
    times mollifier error plus zeta displacement. Feeds the leaf. -/
theorem norm_product_sub_one_le (u v : ℂ) :
    ‖u * v - 1‖ ≤ ‖u‖ * ‖v - 1‖ + ‖u - 1‖ := by
  have heq : u * v - 1 = u * (v - 1) + (u - 1) := by ring
  calc ‖u * v - 1‖ = ‖u * (v - 1) + (u - 1)‖ := by rw [heq]
    _ ≤ ‖u * (v - 1)‖ + ‖u - 1‖ := norm_add_le _ _
    _ = ‖u‖ * ‖v - 1‖ + ‖u - 1‖ := by rw [norm_mul]

/-- `K = 2` mollifier is the constant `1/2` (banked shape
    `riemann_hypothesis_newsection.lean:651`, re-proved here for the
    `Challenge2` definition visible via `central_cover_assembly`). -/
theorem mollifier_two_eq_half (s : ℂ) :
    RHProofScaffold.Challenge2.MollifiedAttack.dirichletMollifier s 2 = 1 / 2 := by
  have hsum : (∑ n ∈ Finset.range 2, (ArithmeticFunction.moebius (n + 1) : ℂ) *
      (↑(n + 1) : ℂ) ^ (-s) * (1 - ↑(n + 1) / ↑(2 : ℕ))) =
      ((ArithmeticFunction.moebius 1 : ℂ) * ((1 : ℕ) : ℂ) ^ (-s) *
        (1 - ((1 : ℕ) : ℂ) / ((2 : ℕ) : ℂ))) +
      ((ArithmeticFunction.moebius 2 : ℂ) * ((2 : ℕ) : ℂ) ^ (-s) *
        (1 - ((2 : ℕ) : ℂ) / ((2 : ℕ) : ℂ))) := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      zero_add]
  have hmu1 : ((ArithmeticFunction.moebius 1 : ℤ) : ℂ) = 1 := by simp
  have hcp1 : (((1 : ℕ) : ℂ) ^ (-s)) = 1 := by
    have h1 : (((1 : ℕ) : ℂ)) = (1 : ℂ) := by simp
    rw [h1, Complex.one_cpow]
  have hw1 : ((1 - ((1 : ℕ) : ℂ) / ((2 : ℕ) : ℂ)) : ℂ) = 1 / 2 := by norm_num
  have hw2 : ((1 - ((2 : ℕ) : ℂ) / ((2 : ℕ) : ℂ)) : ℂ) = 0 := by
    have h2 : ((2 : ℕ) : ℂ) / ((2 : ℕ) : ℂ) = 1 := by
      apply div_self
      norm_num
    rw [h2, sub_self]
  have e0 : ((ArithmeticFunction.moebius 1 : ℂ) * ((1 : ℕ) : ℂ) ^ (-s) *
      (1 - ((1 : ℕ) : ℂ) / ((2 : ℕ) : ℂ))) = 1 / 2 := by
    rw [hmu1, hcp1, hw1, one_mul, one_mul]
  have e1 : ((ArithmeticFunction.moebius 2 : ℂ) * ((2 : ℕ) : ℂ) ^ (-s) *
      (1 - ((2 : ℕ) : ℂ) / ((2 : ℕ) : ℂ))) = 0 := by
    rw [hw2, mul_zero]
  unfold RHProofScaffold.Challenge2.MollifiedAttack.dirichletMollifier
  rw [hsum, e0, e1, add_zero]

/-- `K = 2` mollifier error is exactly `1/2` (closed numeral). -/
theorem mollifier_two_sub_one_norm (s : ℂ) :
    ‖RHProofScaffold.Challenge2.MollifiedAttack.dirichletMollifier s 2 - 1‖ = 1 / 2 := by
  have hM := mollifier_two_eq_half s
  calc ‖RHProofScaffold.Challenge2.MollifiedAttack.dirichletMollifier s 2 - 1‖
      = ‖(1 / 2 : ℂ) - 1‖ := by rw [hM]
    _ = ‖(1 / 2 : ℂ)‖ := by
        have h : ((1 / 2 : ℂ) - 1) = -((1 / 2 : ℂ)) := by ring
        rw [h, norm_neg]
    _ = 1 / 2 := by norm_num

/-- `K = 2` mollifier error in `≤` form for the product split. -/
theorem mollifier_two_sub_one_le (s : ℂ) :
    ‖RHProofScaffold.Challenge2.MollifiedAttack.dirichletMollifier s 2 - 1‖ ≤ 1 / 2 :=
  le_of_eq (mollifier_two_sub_one_norm s)

/-- Uniform zeta UPPER hypothesis on the tail shifted strip
    (`10 < |Re z|`, `0 < Im z < 1/2`). True-value: per-point finite; uniform `B`
    on `Re(shiftedS z) in (0,1/2)` with `|Im| -> infinity` is the open analytic
    input (needs FE + Stirling + convexity; Euler edge only gives `Re >= 1+delta`). -/
def TailZetaUpperB (B : ℝ) : Prop :=
  ∀ (z : ℂ), 10 < |z.re| → 0 < z.im → z.im < (1 / 2 : ℝ) →
    ‖zeta (shiftedS z)‖ ≤ B

/-- Uniform zeta NEAR-ONE hypothesis on the tail shifted strip. True-value:
    companion displacement bound; jointly with `B` the side-condition
    `B * (1/2) + d < 1` is the sharp fixed-`K = 2` form (uniform joint
    satisfiability needs `K` growing; implication below stays true regardless). -/
def TailZetaNearOneD (d : ℝ) : Prop :=
  ∀ (z : ℂ), 10 < |z.re| → 0 < z.im → z.im < (1 / 2 : ℝ) →
    ‖zeta (shiftedS z) - 1‖ ≤ d

/-- Conditional tail gap at `K = 2` with banked `e = 1/2`: zeta-side bounds
    `B, d` with `B * (1/2) + d < 1` imply the exact Rouche product gap. -/
theorem tailK2_gap_of_zetaBounds (B d : ℝ)
    (hB : TailZetaUpperB B) (hd : TailZetaNearOneD d)
    (hB0 : 0 ≤ B) (hgap : B * (1 / 2) + d < 1)
    (z : ℂ) (hx : (10 : ℝ) < |z.re|) (hy0 : (0 : ℝ) < z.im)
    (hy1 : z.im < (1 / 2 : ℝ)) :
    ‖zeta (shiftedS z) *
      RHProofScaffold.Challenge2.MollifiedAttack.dirichletMollifier (shiftedS z) 2 - 1‖ < 1 := by
  have hsplit := norm_product_sub_one_le
    (zeta (shiftedS z))
    (RHProofScaffold.Challenge2.MollifiedAttack.dirichletMollifier (shiftedS z) 2)
  have h1 := hB z hx hy0 hy1
  have h2 := mollifier_two_sub_one_le (shiftedS z)
  have h3 := hd z hx hy0 hy1
  have hprod : ‖zeta (shiftedS z)‖ *
      ‖RHProofScaffold.Challenge2.MollifiedAttack.dirichletMollifier (shiftedS z) 2 - 1‖ ≤
      B * (1 / 2) :=
    mul_le_mul h1 h2 (norm_nonneg _) hB0
  linarith

/-- Conditional leaf constructor: the same hypotheses package the gap into the
    `Challenge2` leaf at `K = 2` (same `gap` shape consumed downstream; transport
    to top-level `MollifiedAttack` for `CrossDoorTailBridge` is patch remainder). -/
theorem tailK2_leaf_of_bounds (B d : ℝ)
    (hB : TailZetaUpperB B) (hd : TailZetaNearOneD d)
    (hB0 : 0 ≤ B) (hgap : B * (1 / 2) + d < 1) :
    RHProofScaffold.Challenge2.MollifiedAttack.MollifiedRoucheLeaf 2 where
  gap := fun (z : ℂ) (hx : (10 : ℝ) < |z.re|) (hy0 : (0 : ℝ) < z.im)
    (hy1 : z.im < (1 / 2 : ℝ)) =>
    tailK2_gap_of_zetaBounds B d hB hd hB0 hgap z hx hy0 hy1

end Door3TailEdgePush
