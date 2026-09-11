/-!
# door3_cutoff_rouche — qualitative cutoff Rouché bypass (WRITE-ONLY delivery)

ROUTE STATUS: obstruction PROVED (the K=2 Rouché gap does NOT close from
zeta-uppers alone). No zeta-lower, no ball-sup `0.04`, no fencing used or
imported. A proved obstruction is the successful delivery: no false gap is
forced.

WHAT THIS FILE DOES (all full proofs, no `sorry`/`admit`/`axiom`, explicit
binders, no `simpa`, numerals ≤ 6 digits):
1. Conj-mirror (`cutLBox_upper_of_cutRBox`): the file takes ONE right-box
   zeta-upper premise `CutRBoxUpper B` (Im ∈ [8.44, 11.56]) and derives the
   left-box upper (Im ∈ [-11.56, -8.44]) inside the file via the unconditional
   Mathlib lemma `riemannZeta_conj` (conj-form, `ZetaAsymp.lean:458`).
   One premise proves both boxes.
2. Gap-or-obstruction (HONEST): the K=2 product margin on the bounded cutoff
   box genuinely fails with uppers alone. Three proved obstruction theorems:
   - `k2_crude_margin_fails`: the crude margin `‖ζ/2-1‖ ≤ ‖ζ‖/2+1 ≤ 6/2+1 = 4`
     never drops below 1 (`norm_num` on the exact failing inequality).
   - `k2_split_side_condition_impossible`: the tail-K2 side condition
     `B*(1/2)+d < 1` at `B = 6` needs `d < -2`, impossible for `d ≥ 0`.
   - `k2_upper_only_witness`: information-theoretic block — the witness
     `w = 6` satisfies `‖w‖ ≤ 6` yet `‖w/2-1‖ = 2 ≥ 1`, so NO argument using
     only `‖ζ‖ ≤ 6` can certify the leaf gap `‖ζ/2-1‖ < 1`.
3. Conditional chain (open-input → ζ ≠ 0, no fencing): from ONE weak two-sided
   disc enclosure `CutBoxZetaDisc c r lo hi` plus margin
   `‖c/2-1‖ + r/2 < κ < 1`, the half-gap `‖ζ(s)/2-1‖ < 1` follows
   (`half_gap_of_disc`), hence `ζ(s) ≠ 0` (`zeta_ne_zero_of_half_gap`), hence
   `ζ ≠ 0` on both thin-rect s-images (`rightLine_zeta_ne_zero_of_disc`,
   `leftLine_zeta_ne_zero_of_disc` via `shiftedS_of_rightLine_mem_box` /
   `shiftedS_of_leftLine_mem_box`).

PREMISE SHOPPING LIST with TRUE values:
- HAVE (sibling discharges in parallel): `CutRBoxUpper 6`, i.e.
  `‖zeta t‖ ≤ 6` on the right s-box `Re ∈ [-1.06, 2.06]`, `Im ∈ [8.44, 11.56]`
  (FE-route box shape from `door3_cutR10_ballsup.lean:1611-1612`; generous
  upper — true center value `|ζ(1/2+10*I)| ≈ 1.549` per
  `central_cover_assembly.lean:16789`).
- PROVED HERE: left-box mirror of the above (no second premise needed).
- WOULD-SUFFICE (open analytic input, one premise): a uniform disc enclosure
  `CutBoxZetaDisc c r lo hi` with `‖c/2-1‖ + r/2 < κ < 1` for explicit
  `(c, r, κ)` with TRUE containment on the box. True-value anchor:
  `|ζ(1/2+10*I)| ≈ 1.549`; the uniform disc (covering `Re ∈ [-1.06, 2.06]`
  variation) is NOT banked anywhere in the repo — certifying one `(c, r, κ)`
  triple is the exact remainder. Note the true `ζ` is NOT near 1 on the box
  (centre modulus ≈ 1.549), so a `TailZetaNearOneD`-style near-one premise is
  false here; the disc centre must sit near the true values, not near 1.
- FEED REMAINDER (patch phase): the conditional `ζ ≠ 0` on the box becomes
  `xiShifted ≠ 0` on both thin rects via prefactor-nonzero (poly/pi/Gamma
  factors from banked `xiShifted_eq_parts`, `central_cover_assembly.lean:6339`)
  plus `xiShifted = xiShiftedEntire` on the strip; then feed
  `Door3RHWiring.xiCutoffLines10_of_cutR10_and_leftLine`
  (`door3_rh_wiring.lean:88-106`) whose fencing hypothesis `H` belongs to a
  different lane (this file supplies the `hLeft`-shaped zeta input, not `H`).

RECON (read-only sources):
- Conditional K=2 pattern: `door3_tail_edge_push.lean:211-230`
  (`tailK2_gap_of_zetaBounds`, premises `TailZetaUpperB B`,
  `TailZetaNearOneD d`, `B/2+d < 1`) — mirrored here as
  `half_gap_of_disc` with a disc premise instead of near-one.
- Banked Rouché shapes: `riemann_hypothesis_newsection.lean:276-310`
  (`hardDifference_eq_zero_iff`), `:457-464` (`rouche_margin_lower_bound`),
  `:467` (`rouche_gap_ne_zero`, re-proved locally as `half_gap_ne_zero_aux`
  to avoid the import), `:503-516`, `:529-548`.
- FEroute box shape: `door3_cutR10_ballsup.lean:1611-1612`, `:1627-1628`
  (copied exactly for `CutRBoxUpper` / `CutBoxZetaDisc` bounds).
- Cutoff geometry: `CutR10 = ⟨9.75, 10.25, -0.49, 0.49⟩`,
  `CutL10 = ⟨-10.25, -9.75, -0.49, 0.49⟩`, `radius < 0.56`
  (`central_cover_assembly.lean:6826-6880`), `cutoffLines_either` (`:6908`);
  `xiShifted z = classicalXi (1/2 + I*z)` (`riemann_hypothesis.lean:228`),
  `shiftedS z = 1/2 + I*z` (`:2793-2794`), `zeta := riemannZeta` (`:16`).

IMPORT CYCLE CHECK (read-only): `door3_cutR10_ballsup.lean:1-2` imports only
`Mathlib` + `central_cover_assembly`; `door3_cutL10_remainders.lean:1-2`
imports only `central_cover_assembly` + `zeta_rigorous`; neither imports the
other, so both WOULD be cycle-safe to import — but this route needs neither
(no fencing, no ball-sup, no eta), so imports stay `Mathlib` +
`central_cover_assembly` only. This file is downstream (nothing imports it).
-/

import Mathlib
import central_cover_assembly

noncomputable section

namespace Door3CutoffRouche

/-- Right cutoff s-box zeta UPPER (single premise of this file).
    Box = ball-image bounds from the FEroute
    (`door3_cutR10_ballsup.lean:1611`): `Re ∈ [-1.06, 2.06]`,
    `Im ∈ [8.44, 11.56]`. TRUE VALUE: `B = 6` is true and generous
    (χ-cap 3 times reflected Euler cap 2; true centre modulus ≈ 1.549).
    A sibling agent discharges this in parallel; it is NOT proved here. -/
def CutRBoxUpper (B : ℝ) : Prop :=
  ∀ t : ℂ, (-1.06 : ℝ) ≤ t.re → t.re ≤ (2.06 : ℝ) →
    (8.44 : ℝ) ≤ t.im → t.im ≤ (11.56 : ℝ) → ‖zeta t‖ ≤ B

/-- Conj norm transport for `zeta` via unconditional Mathlib
    `riemannZeta_conj` (`ZetaAsymp.lean:458`,
    `riemannZeta (conj s) = conj (riemannZeta s)` for all `s`). -/
theorem zeta_norm_conj (s : ℂ) :
    ‖zeta (Complex.conj s)‖ = ‖zeta s‖ := by
  have h : zeta (Complex.conj s) = Complex.conj (zeta s) := by
    show riemannZeta (Complex.conj s) = Complex.conj (riemannZeta s)
    exact riemannZeta_conj s
  rw [h, Complex.norm_conj]

/-- Conj-mirror: the ONE right-box premise yields the left-box upper
    (`Im ∈ [-11.56, -8.44]`) inside this file. Both boxes covered. -/
theorem cutLBox_upper_of_cutRBox (B : ℝ) (hR : CutRBoxUpper B) (t : ℂ)
    (hlo : (-1.06 : ℝ) ≤ t.re) (hhi : t.re ≤ (2.06 : ℝ))
    (hilo : (-11.56 : ℝ) ≤ t.im) (hihi : t.im ≤ (-8.44 : ℝ)) :
    ‖zeta t‖ ≤ B := by
  have hre : (Complex.conj t).re = t.re := Complex.conj_re t
  have him : (Complex.conj t).im = -t.im := Complex.conj_im t
  have h1 : (-1.06 : ℝ) ≤ (Complex.conj t).re := by
    rw [hre]
    exact hlo
  have h2 : (Complex.conj t).re ≤ (2.06 : ℝ) := by
    rw [hre]
    exact hhi
  have h3 : (8.44 : ℝ) ≤ (Complex.conj t).im := by
    rw [him]
    linarith
  have h4 : (Complex.conj t).im ≤ (11.56 : ℝ) := by
    rw [him]
    linarith
  have hB := hR (Complex.conj t) h1 h2 h3 h4
  rw [zeta_norm_conj t] at hB
  exact hB

/-- OBSTRUCTION 1 (proved, `norm_num`): the crude K=2 margin
    `‖ζ/2-1‖ ≤ ‖ζ‖/2+1 ≤ 6/2+1 = 4` never drops below the Rouché
    threshold 1. Exact failing inequality. -/
theorem k2_crude_margin_fails : ¬ ((6 : ℝ) / 2 + 1 < 1) := by
  norm_num

/-- OBSTRUCTION 2 (proved): the tail-K2 side condition `B*(1/2)+d < 1`
    at box-upper `B = 6` would need `d < -2`, impossible for `d ≥ 0`.
    So the `tailK2_gap_of_zetaBounds` splitting cannot fire here; moreover
    the true `ζ` (≈ 1.549 at centre) is NOT near 1, so a near-one premise
    would be false, not merely open. -/
theorem k2_split_side_condition_impossible (d : ℝ) (hd : 0 ≤ d) :
    ¬ ((6 : ℝ) * (1 / 2) + d < 1) := by
  intro hcon
  linarith

/-- OBSTRUCTION 3 (proved): information-theoretic block. The witness `w = 6`
    meets the box-upper yet violates the leaf gap (`‖6/2-1‖ = 2 ≥ 1`), so NO
    proof from `‖ζ‖ ≤ 6` alone can conclude `‖ζ/2-1‖ < 1`. -/
theorem k2_upper_only_witness :
    ∃ w : ℂ, ‖w‖ ≤ (6 : ℝ) ∧ (1 : ℝ) ≤ ‖w / 2 - 1‖ := by
  refine ⟨6, by norm_num, ?_⟩
  have hw : (6 : ℂ) / 2 - 1 = 2 := by
    norm_num
  rw [hw]
  norm_num

/-- Minimal sufficient premise (OPEN analytic input): weak two-sided uniform
    disc enclosure of `zeta` on one cutoff s-box (`lo/hi = 8.44/11.56` right,
    `-11.56, -8.44` left). Instantiating `(c, r)` with TRUE containment plus a
    margin `‖c/2-1‖ + r/2 < κ < 1` is the exact remainder. -/
def CutBoxZetaDisc (c : ℂ) (r lo hi : ℝ) : Prop :=
  ∀ s : ℂ, (-1.06 : ℝ) ≤ s.re → s.re ≤ (2.06 : ℝ) →
    lo ≤ s.im → s.im ≤ hi → ‖zeta s - c‖ ≤ r

/-- Conditional half-gap: the disc enclosure plus margin certifies the K=2
    Rouché quantity `‖ζ(s)/2-1‖ < 1` (pure triangle inequality; the
    `mollified_K2_gap_eq` shape `ζ*M₂-1 = ζ/2-1` with `M₂ = 1/2`). -/
theorem half_gap_of_disc (c : ℂ) (r κ lo hi : ℝ)
    (hE : CutBoxZetaDisc c r lo hi)
    (hmarg : ‖c / 2 - 1‖ + r / 2 < κ) (hκ : κ < 1)
    (s : ℂ)
    (hlo : (-1.06 : ℝ) ≤ s.re) (hhi : s.re ≤ (2.06 : ℝ))
    (hilo : lo ≤ s.im) (hihi : s.im ≤ hi) :
    ‖zeta s / 2 - 1‖ < 1 := by
  have henc := hE s hlo hhi hilo hihi
  have heq : zeta s / 2 - 1 = (zeta s - c) / 2 + (c / 2 - 1) := by
    rw [sub_div]
    abel
  have hn2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    norm_num
  have hle : ‖zeta s / 2 - 1‖ ≤ ‖zeta s - c‖ / 2 + ‖c / 2 - 1‖ := by
    calc ‖zeta s / 2 - 1‖
        = ‖(zeta s - c) / 2 + (c / 2 - 1)‖ := by rw [heq]
      _ ≤ ‖(zeta s - c) / 2‖ + ‖c / 2 - 1‖ := norm_add_le _ _
      _ = ‖zeta s - c‖ / ‖(2 : ℂ)‖ + ‖c / 2 - 1‖ := by rw [norm_div]
      _ = ‖zeta s - c‖ / 2 + ‖c / 2 - 1‖ := by rw [hn2]
  linarith

/-- Qualitative Rouché corollary, re-proved locally (banked shape
    `riemann_hypothesis_newsection.lean:467`, not imported): the gap forces
    nonvanishing. -/
theorem half_gap_ne_zero_aux {u : ℂ} (h : ‖u - 1‖ < 1) : u ≠ 0 := by
  intro hz
  rw [hz, zero_sub, norm_neg, norm_one] at h
  linarith

/-- The half-gap gives `ζ(s) ≠ 0` (via `M₂ = 1/2 ≠ 0`). -/
theorem zeta_ne_zero_of_half_gap {s : ℂ}
    (h : ‖zeta s / 2 - 1‖ < 1) : zeta s ≠ 0 := by
  have hM : zeta s / 2 ≠ 0 := half_gap_ne_zero_aux h
  intro hz
  apply hM
  rw [hz, zero_div]

/-- The right thin-rect line (`Re = 10`, `|Im| ≤ 0.49`) maps under `shiftedS`
    into the right s-box (`(shiftedS z).re = 1/2 - z.im`,
    `(shiftedS z).im = z.re`). -/
theorem shiftedS_of_rightLine_mem_box {z : ℂ} (hx : z.re = (10 : ℝ))
    (hlo : (-0.49 : ℝ) ≤ z.im) (hhi : z.im ≤ (0.49 : ℝ)) :
    (-1.06 : ℝ) ≤ (shiftedS z).re ∧ (shiftedS z).re ≤ (2.06 : ℝ) ∧
      (8.44 : ℝ) ≤ (shiftedS z).im ∧ (shiftedS z).im ≤ (11.56 : ℝ) := by
  have hre : (shiftedS z).re = (1 / 2 : ℝ) - z.im := shiftedS_re z
  have him : (shiftedS z).im = z.re := shiftedS_im_eq z
  rw [hre, him, hx]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The left thin-rect line (`Re = -10`, `|Im| ≤ 0.49`) maps under `shiftedS`
    into the left s-box. -/
theorem shiftedS_of_leftLine_mem_box {z : ℂ} (hx : z.re = (-10 : ℝ))
    (hlo : (-0.49 : ℝ) ≤ z.im) (hhi : z.im ≤ (0.49 : ℝ)) :
    (-1.06 : ℝ) ≤ (shiftedS z).re ∧ (shiftedS z).re ≤ (2.06 : ℝ) ∧
      (-11.56 : ℝ) ≤ (shiftedS z).im ∧ (shiftedS z).im ≤ (-8.44 : ℝ) := by
  have hre : (shiftedS z).re = (1 / 2 : ℝ) - z.im := shiftedS_re z
  have him : (shiftedS z).im = z.re := shiftedS_im_eq z
  rw [hre, him, hx]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Conditional `ζ ≠ 0` on the right thin rect from the right disc. -/
theorem rightLine_zeta_ne_zero_of_disc (c : ℂ) (r κ : ℝ)
    (hE : CutBoxZetaDisc c r (8.44 : ℝ) (11.56 : ℝ))
    (hmarg : ‖c / 2 - 1‖ + r / 2 < κ) (hκ : κ < 1)
    {z : ℂ} (hx : z.re = (10 : ℝ))
    (hlo : (-0.49 : ℝ) ≤ z.im) (hhi : z.im ≤ (0.49 : ℝ)) :
    zeta (shiftedS z) ≠ 0 := by
  have hmem := shiftedS_of_rightLine_mem_box hx hlo hhi
  have hgap := half_gap_of_disc c r κ (8.44 : ℝ) (11.56 : ℝ) hE hmarg hκ
    (shiftedS z) hmem.1 hmem.2.1 hmem.2.2.1 hmem.2.2.2
  exact zeta_ne_zero_of_half_gap hgap

/-- Conditional `ζ ≠ 0` on the left thin rect from the left disc (mirror
    image of the right-disc input under `conj`; same TRUE-value status). -/
theorem leftLine_zeta_ne_zero_of_disc (c : ℂ) (r κ : ℝ)
    (hE : CutBoxZetaDisc c r (-11.56 : ℝ) (-8.44 : ℝ))
    (hmarg : ‖c / 2 - 1‖ + r / 2 < κ) (hκ : κ < 1)
    {z : ℂ} (hx : z.re = (-10 : ℝ))
    (hlo : (-0.49 : ℝ) ≤ z.im) (hhi : z.im ≤ (0.49 : ℝ)) :
    zeta (shiftedS z) ≠ 0 := by
  have hmem := shiftedS_of_leftLine_mem_box hx hlo hhi
  have hgap := half_gap_of_disc c r κ (-11.56 : ℝ) (-8.44 : ℝ) hE hmarg hκ
    (shiftedS z) hmem.1 hmem.2.1 hmem.2.2.1 hmem.2.2.2
  exact zeta_ne_zero_of_half_gap hgap

#print axioms Door3CutoffRouche.cutLBox_upper_of_cutRBox
#print axioms Door3CutoffRouche.k2_upper_only_witness
#print axioms Door3CutoffRouche.rightLine_zeta_ne_zero_of_disc

end Door3CutoffRouche
