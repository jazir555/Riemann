import Mathlib

open BigOperators Complex

/-!
# TailLaguerreScratch

Narrow scratch extraction of `TailCanonicalLaguerrePositivityLeaf` and
`MollifiedRoucheLeaf` from `riemannhypothesis.lean`.

The heavy RH machinery (`xiShiftedLaguerreCoefficient`, `zeta`, `shiftedS`,
`dirichletMollifier`) is re-declared here only as a *minimal interface stub* so
the two structures compile without importing the 133k-line source file. The
stubs are not proofs and are not placeholder admissions; they are placeholders for the
orchestrator to replace with the real definitions.

The only genuinely proven results here are two small, finite, analytic
sub-lemmas that feed the leaves:
* `geomTailDecay`  — a plain real tail-decay bound (geometric series).
* `rectNormBound`  — an explicit squared-modulus bound on a finite rectangle
  (`Complex.normSq z ≤ 2`, i.e. `|z| ≤ √2`, on `|Re z|,|Im z| ≤ 1`).
-/

-- Minimal interface stubs (placeholders; replace with real defs later).
noncomputable def xiShiftedLaguerreCoefficient (_n : ℕ) (_r : ℝ) : ℝ := 0
noncomputable def zeta (_s : ℂ) : ℂ := 0
def shiftedS (s : ℂ) : ℂ := s
def dirichletMollifier (_s : ℂ) (_K : ℕ) : ℂ := 1

/-- Extracted from `riemannhypothesis.lean` (structure at line 12269). -/
structure TailCanonicalLaguerrePositivityLeaf where
  coefficient_nonneg :
    ∀ n : ℕ, ∀ r : ℝ,
      10 < r →
      0 ≤ xiShiftedLaguerreCoefficient n r
  coefficient_exists_pos :
    ∀ r : ℝ,
      10 < r →
      ∃ n : ℕ, 0 < xiShiftedLaguerreCoefficient n r

/-- Extracted from `riemannhypothesis.lean` (structure at line 13731). -/
structure MollifiedRoucheLeaf (K : ℕ) where
  gap : ∀ (z : ℂ), 10 < |z.re| → 0 < z.im → z.im < (1 / 2 : ℝ) →
    ‖zeta (shiftedS z) * dirichletMollifier (shiftedS z) K - 1‖ < 1

/-- **Finite tail-decay estimate.** For `1 < r` the truncated tail
`∑_{i=0}^{N-1} r^{-(i+1)}` is strictly bounded by the convergent geometric sum
`1/(r-1)`. This is a plain real inequality and feeds any tail estimate in the
Laguerre / Rouché machinery. -/
theorem geomTailDecay {r : ℝ} (hr : 1 < r) (N : ℕ) :
    (∑ i ∈ Finset.range N, (r⁻¹) ^ (i + 1)) < 1 / (r - 1) := by
  let a := r⁻¹
  have hr' : 0 < r := by linarith
  have ha : 0 < a := by positivity
  have ha1 : a < 1 := by
    rw [show a = r⁻¹ by rfl]
    field_simp [ne_of_gt hr']
    linarith
  cases N with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty]
    exact div_pos zero_lt_one (sub_pos.mpr hr)
  | succ n =>
    have hsum : (∑ i ∈ Finset.range (n + 1), a ^ (i + 1)) =
        a * (1 - a ^ (n + 1)) / (1 - a) := by
      calc
        (∑ i ∈ Finset.range (n + 1), a ^ (i + 1))
            = (∑ i ∈ Finset.range (n + 1), a ^ i * a) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact pow_succ a i
        _ = (∑ i ∈ Finset.range (n + 1), a ^ i) * a := by rw [Finset.sum_mul]
        _ = a * (∑ i ∈ Finset.range (n + 1), a ^ i) := by rw [mul_comm]
        _ = a * ((a ^ (n + 1) - 1) / (a - 1)) := by rw [geom_sum_eq (ne_of_lt ha1) (n + 1)]
        _ = a * (1 - a ^ (n + 1)) / (1 - a) := by
              have h1 : (a ^ (n + 1) - 1) / (a - 1) = (1 - a ^ (n + 1)) / (1 - a) := by
                field_simp [sub_ne_zero.mpr (ne_of_lt ha1), sub_ne_zero.mpr (ne_of_lt ha1).symm]
                ring_nf
              rw [h1, mul_div_assoc]
    rw [hsum]
    have hlt : a * (1 - a ^ (n + 1)) < a := by
      nlinarith [mul_pos ha (pow_pos ha (n + 1))]
    have hden : 0 < 1 - a := by linarith
    have hmain : a * (1 - a ^ (n + 1)) / (1 - a) < a / (1 - a) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_lt_mul_of_pos_right hlt (inv_pos.mpr hden)
    have hfinal : a / (1 - a) = 1 / (r - 1) := by
      rw [show a = r⁻¹ by rfl]
      field_simp [ne_of_gt hr']
    exact hmain.trans_eq hfinal

/-- **Explicit bound on a finite rectangle.** On the box `|Re z| ≤ 1`,
`|Im z| ≤ 1` the squared complex modulus satisfies `Complex.normSq z ≤ 2`
(equivalently `|z| ≤ √2`). A plain real inequality via
`Complex.normSq z = Re(z)² + Im(z)²`; it is the elementary geometry behind any
finite-rectangle estimate feeding the leaves. -/
theorem rectNormBound (z : ℂ) (hre : |z.re| ≤ 1) (him : |z.im| ≤ 1) :
    z.re ^ 2 + z.im ^ 2 ≤ 2 := by
  rw [pow_two, pow_two]
  calc
    z.re * z.re + z.im * z.im ≤ 1 + 1 :=
      add_le_add (abs_le_one_iff_mul_self_le_one.mp hre) (abs_le_one_iff_mul_self_le_one.mp him)
    _ ≤ 2 := by norm_num

/-!
## Door-4 tail-leaf bridge (append-only, 2026-09-05)

Target leaf obligation (upper half; the lower half follows by conjugation via
`CrossDoorTailBridge.xiShifted_lower_tail_nonvanishing_from_upper`):
`MollifiedRoucheLeaf.gap` —
`∀ z, 10 < |z.re| → 0 < z.im → z.im < 1/2 →
‖zeta (shiftedS z) * dirichletMollifier (shiftedS z) K - 1‖ < 1`,
which via
`CrossDoorTailBridge.xiShifted_off_axis_tail_nonvanishing_from_mollified_rouche`
supplies exactly the hypothesis of `tailPointwise10_of_absTail`.

Below: three proved analytic feeders at tail parameters plus quantified gap
(see trailing comment for what remains open).
-/

/-- Geometric tail at the concrete tail ratio `r = 11`: uniform `< 1/10` bound.
Instantiation of `geomTailDecay` for the `|Re z| > 10` tail regime. -/
theorem tailGeomBound_at11 (N : ℕ) :
    (∑ i ∈ Finset.range N, ((11 : ℝ)⁻¹) ^ (i + 1)) < 1 / 10 := by
  have h := geomTailDecay (r := (11 : ℝ)) (by norm_num) N
  have heq : (1 : ℝ) / ((11 : ℝ) - 1) = 1 / 10 := by norm_num
  rw [heq] at h
  exact h

/-- Tail points lie outside the radius-10 ball: `10 < |Re z| → 10 < ‖z‖`.
Geometric fact placing the `|Re z| > 10` tail outside every radius-10 estimate. -/
theorem tailNormLower_of_absRe (z : ℂ) (hx : (10 : ℝ) < |z.re|) :
    (10 : ℝ) < ‖z‖ := by
  have h1 : |z.re| ≤ ‖z‖ :=
    Complex.abs_re_le_norm z
  linarith

/-- Squared-modulus complement of `rectNormBound`: on the tail,
`100 < Re(z)² + Im(z)²`. -/
theorem tailSqLower_of_absRe (z : ℂ) (hx : (10 : ℝ) < |z.re|) :
    (100 : ℝ) < z.re ^ 2 + z.im ^ 2 := by
  have hpos1 : (0 : ℝ) < |z.re| - 10 := sub_pos.mpr hx
  have hpos2 : (0 : ℝ) < |z.re| + 10 := by
    have hnn : (0 : ℝ) ≤ |z.re| := abs_nonneg z.re
    linarith
  have hmul : (0 : ℝ) < (|z.re| - 10) * (|z.re| + 10) := mul_pos hpos1 hpos2
  have hkey : |z.re| ^ 2 = 100 + (|z.re| - 10) * (|z.re| + 10) := by ring
  have hsq : (100 : ℝ) < |z.re| ^ 2 := by linarith
  have habs : |z.re| ^ 2 = z.re ^ 2 := sq_abs z.re
  have hle : z.re ^ 2 ≤ z.re ^ 2 + z.im ^ 2 :=
    le_add_of_nonneg_right (sq_nonneg z.im)
  linarith

/- Quantified gap to the full door-4 tail leaf: the feeders above give
uniform geometric decay (`tailGeomBound_at11`) and the tail-norm floor
(`tailNormLower_of_absRe`, `tailSqLower_of_absRe`), but the leaf conclusion
`‖zeta (shiftedS z) * dirichletMollifier (shiftedS z) K - 1‖ < 1` still needs
(a) the real `zeta`/`shiftedS`/`dirichletMollifier` definitions substituted for
this file's stubs, (b) a zeta upper bound uniform in `‖shiftedS z‖ > 10`, and
(c) a mollifier approximation bound `< 1 - (zeta-error)` on the strip
`0 < z.im < 1/2`. Next agent: instantiate (b)+(c) and compose with
`CrossDoorTailBridge.xiShifted_off_axis_tail_nonvanishing_from_mollified_rouche`
into `tailPointwise10_of_absTail`. -/

/-!
## Door-4 tail leaf: zeta-upper + mollifier-error bridge (2026-09-05, append-only)

GREP VERDICT (read-only, no import added):
* real `zeta := riemannZeta` at `riemann_hypothesis.lean:16`;
  real `shiftedS z = 1/2 + I*z` at `riemann_hypothesis.lean:2793`;
  real `dirichletMollifier` (truncated smoothed Mobius sum) at
  `riemann_hypothesis.lean:11984`; stub `MollifiedRoucheLeaf.gap` shape matches
  `riemann_hypothesis_newsection.lean:45-47`.
* `riemann_hypothesis.lean` imports only `Mathlib, TestAnalytic, ZeroFreeRegion`
  (no cycle back to this file), so importing it here would be logically
  acyclic — but it pulls the full 133k-line core file plus `newsection` pulls
  `riemann_hypothesis + zeta_rigorous + central_cover_assembly +
  ZeroFreeRegionHadamard`, which blows the tail-lane build budget (hang-guard
  15 min). Hence the cycle-safe conditional route below: the needed real-side
  estimates are stated as explicit stub-assumption Props
  (`TailStubZetaUpper`, `TailStubMollifierNearOne`, `TailStubZetaNearOne`),
  and every theorem is a FULLY PROVED implication (no sorry/admit/axiom)
  discharging `‖zeta*M-1‖ < 1` from those Props plus an explicit numeric
  side condition. Instantiating the Props for the real definitions is the
  quantified remainder.
-/

/-- Stub-conditional zeta UPPER hypothesis, bridge (b):
uniform `‖zeta (shiftedS z)‖ ≤ B` on the tail strip
`10 < |Re z|, 0 < Im z < 1/2`. For the REAL zeta this is the open analytic
input; for this file's `zeta = 0` stub it is trivially true for any `0 ≤ B`. -/
def TailStubZetaUpper (B : ℝ) : Prop :=
  ∀ z : ℂ, 10 < |z.re| → 0 < z.im → z.im < (1 / 2 : ℝ) →
    ‖zeta (shiftedS z)‖ ≤ B

/-- Stub-conditional mollifier ERROR hypothesis, bridge (c):
uniform `‖M - 1‖ ≤ e` on the tail strip. For the REAL mollifier this is the
open approximation input; for this file's `M = 1` stub it holds with `e = 0`. -/
def TailStubMollifierNearOne (e : ℝ) (K : ℕ) : Prop :=
  ∀ z : ℂ, 10 < |z.re| → 0 < z.im → z.im < (1 / 2 : ℝ) →
    ‖dirichletMollifier (shiftedS z) K - 1‖ ≤ e

/-- Stub-conditional zeta NEAR-ONE hypothesis: uniform `‖zeta - 1‖ ≤ d` on the
tail strip. Companion to the upper bound; together with the mollifier error
it yields the Rouche product gap via the triangle split below. -/
def TailStubZetaNearOne (d : ℝ) : Prop :=
  ∀ z : ℂ, 10 < |z.re| → 0 < z.im → z.im < (1 / 2 : ℝ) →
    ‖zeta (shiftedS z) - 1‖ ≤ d

/-- Pure product-gap split (no stubs, no hypotheses): the Rouche product
error is controlled by the zeta size times the mollifier error plus the
zeta displacement. This is the quantitative form feeding the leaf. -/
theorem norm_product_sub_one_le (u v : ℂ) :
    ‖u * v - 1‖ ≤ ‖u‖ * ‖v - 1‖ + ‖u - 1‖ := by
  have heq : u * v - 1 = u * (v - 1) + (u - 1) := by ring
  calc ‖u * v - 1‖ = ‖u * (v - 1) + (u - 1)‖ := by rw [heq]
    _ ≤ ‖u * (v - 1)‖ + ‖u - 1‖ := norm_add_le _ _
    _ = ‖u‖ * ‖v - 1‖ + ‖u - 1‖ := by rw [norm_mul]

/-- Conditional tail Rouche gap from stub bounds: under
`TailStubZetaUpper B` (b) + `TailStubMollifierNearOne e K` (c) +
`TailStubZetaNearOne d`, the explicit numeric side condition
`B * e + d < 1` implies the exact leaf inequality
`‖zeta*M - 1‖ < 1` at every tail point. -/
theorem tailLeafGap_of_stubBounds {B e d : ℝ} {K : ℕ}
    (hZ : TailStubZetaUpper B) (hM : TailStubMollifierNearOne e K)
    (hZ1 : TailStubZetaNearOne d)
    (hB : 0 ≤ B) (_he : 0 ≤ e)
    (hgap : B * e + d < 1) (z : ℂ)
    (hx : (10 : ℝ) < |z.re|) (hy0 : (0 : ℝ) < z.im) (hy1 : z.im < (1 / 2 : ℝ)) :
    ‖zeta (shiftedS z) * dirichletMollifier (shiftedS z) K - 1‖ < 1 := by
  have h1 := hZ z hx hy0 hy1
  have h2 := hM z hx hy0 hy1
  have h3 := hZ1 z hx hy0 hy1
  have hsplit := norm_product_sub_one_le
    (zeta (shiftedS z)) (dirichletMollifier (shiftedS z) K)
  have hprod : ‖zeta (shiftedS z)‖ * ‖dirichletMollifier (shiftedS z) K - 1‖ ≤ B * e :=
    mul_le_mul h1 h2 (norm_nonneg _) hB
  linarith

/-- Conditional leaf constructor: the same hypotheses package the gap into
this file's `MollifiedRoucheLeaf K` (same `gap` shape as
`riemann_hypothesis_newsection.lean:45-47`). -/
theorem tailMollifiedRoucheLeaf_of_stubBounds {B e d : ℝ} {K : ℕ}
    (hZ : TailStubZetaUpper B) (hM : TailStubMollifierNearOne e K)
    (hZ1 : TailStubZetaNearOne d)
    (hB : 0 ≤ B) (he : 0 ≤ e)
    (hgap : B * e + d < 1) : MollifiedRoucheLeaf K where
  gap := fun z hx hy0 hy1 => tailLeafGap_of_stubBounds hZ hM hZ1 hB he hgap z hx hy0 hy1

/- Quantified remainder after this bridge: the implication chain
`TailStubZetaUpper + TailStubMollifierNearOne + TailStubZetaNearOne +
(B*e+d<1) => MollifiedRoucheLeaf.gap` is fully proved above. What remains is
instantiating the three Props for the REAL `zeta/shiftedS/dirichletMollifier`
(`riemann_hypothesis.lean:16,2793,11984`): a uniform zeta upper `B` on the
shifted strip plus mollifier/zeta near-one errors `e,d` with `B*e+d<1`.
Note the stub values themselves (`zeta=0`, `M=1`) do NOT satisfy the package
with `<1` (stub `‖zeta-1‖=1`), so no vacuous closure is claimed. Next agent:
prove the real-side (b)+(c) estimates (functional equation / Dirichlet-series
majorant on the shifted strip) and rewrite this file's stub Props. -/

/-!
## Door-4 tail leaf: real triple component (c) + shifted geometry (2026-09-05, append-only)

Real definitions (mirroring `riemann_hypothesis.lean`, read-only, no import added):
* `tailShiftedSReal z = 1/2 + I*z` (cf. `shiftedS`, `riemann_hypothesis.lean:2793`);
* `tailMollifierReal s K` = truncated smoothed Moebius sum
  (cf. `dirichletMollifier`, `riemann_hypothesis.lean:11984`);
* the zeta side uses Mathlib `riemannZeta` directly
  (cf. `zeta := riemannZeta`, `riemann_hypothesis.lean:16`).

Banked here (FULLY PROVED, no sorry/admit/axiom):
* shifted geometry: Re/Im formulas, `0 < Re < 1/2` on the regime,
  `‖tailShiftedSReal z‖ > 10`, `≠ 1` (so `differentiableAt_riemannZeta` applies);
* component (c): at `K = 2` the real mollifier is the constant `1/2`
  (`tailMollifierReal_two`), hence uniform error `e = 1/2`
  (`tailMollifierReal_nearOne_two`);
* real conditional gap `tailRealGap_of_zetaBounds_two`: reuses T2's
  `norm_product_sub_one_le` with the banked `e = 1/2`, reducing the leaf to
  zeta-side bounds `B,d` with `B * (1/2) + d < 1`.

Why the Dirichlet-series majorant cannot supply (b)/(d) here:
`tailShiftedSReal_re_range` gives `Re ∈ (0,1/2)`, i.e. `Re < 1`, so
`zeta_eq_tsum_one_div_nat_add_one_cpow` (needs `1 < Re`) does NOT apply.
(b) and (d) need functional-equation / Lindeloef-type input (or a compact-cell
argument); see the quantified remainder at the end of this block.
-/

/-- Real shifted coordinate (cf. `shiftedS`, `riemann_hypothesis.lean:2793`). -/
noncomputable def tailShiftedSReal (z : ℂ) : ℂ := (1 / 2 : ℂ) + Complex.I * z

/-- Real truncated smoothed Moebius mollifier
(cf. `dirichletMollifier`, `riemann_hypothesis.lean:11984`). -/
noncomputable def tailMollifierReal (s : ℂ) (K : ℕ) : ℂ :=
  ∑ n ∈ Finset.range K, (((ArithmeticFunction.moebius (n + 1) : ℤ) : ℂ) *
    (((n + 1 : ℕ) : ℂ) ^ (-s)) * (1 - ((n + 1 : ℕ) : ℂ) / ((K : ℕ) : ℂ)))

/-- Real shifted real part: `Re = 1/2 - Im z`. -/
theorem tailShiftedSReal_re (z : ℂ) :
    (tailShiftedSReal z).re = 1 / 2 - z.im := by
  unfold tailShiftedSReal
  simp only [Complex.add_re, Complex.I_mul_re]
  norm_num <;> ring

/-- Real shifted imaginary part: `Im = Re z`. -/
theorem tailShiftedSReal_im (z : ℂ) :
    (tailShiftedSReal z).im = z.re := by
  unfold tailShiftedSReal
  simp only [Complex.add_im, Complex.I_mul_im]
  norm_num <;> simp

/-- On the tail regime the shifted real part lies in `(0,1/2)`
(hence `Re < 1`: the `Re > 1` Dirichlet majorant does not apply). -/
theorem tailShiftedSReal_re_range (z : ℂ) (hy0 : 0 < z.im) (hy1 : z.im < 1 / 2) :
    0 < (tailShiftedSReal z).re ∧ (tailShiftedSReal z).re < 1 / 2 := by
  rw [tailShiftedSReal_re]
  constructor <;> linarith

/-- Shifted points lie outside the radius-10 ball on the tail regime. -/
theorem tailShiftedSReal_norm_gt10 (z : ℂ) (hx : 10 < |z.re|) :
    10 < ‖tailShiftedSReal z‖ := by
  have him : |(tailShiftedSReal z).im| = |z.re| := by rw [tailShiftedSReal_im]
  have hle : |(tailShiftedSReal z).im| ≤ ‖tailShiftedSReal z‖ :=
    Complex.abs_im_le_norm _
  linarith

/-- Shifted tail points avoid the zeta pole at `1`. -/
theorem tailShiftedSReal_ne_one (z : ℂ) (hy0 : 0 < z.im) (hy1 : z.im < 1 / 2) :
    tailShiftedSReal z ≠ 1 := by
  intro h
  have hre : (tailShiftedSReal z).re = (1 : ℂ).re := congrArg Complex.re h
  rw [tailShiftedSReal_re, Complex.one_re] at hre
  linarith

/-- Component (c), exact value: at `K = 2` the real mollifier is the constant
`1/2` (the `n = 1` term carries the factor `1 - 2/2 = 0`; the `n = 0` term is
`mu 1 * 1^{-s} * (1 - 1/2) = 1/2`). -/
theorem tailMollifierReal_two (s : ℂ) :
    tailMollifierReal s 2 = 1 / 2 := by
  have hmu : ArithmeticFunction.moebius 1 = 1 :=
    ArithmeticFunction.moebius_apply_one
  have h01 : ((0 + 1 : ℕ) : ℂ) = (1 : ℂ) := by push_cast; norm_num
  have h11 : ((1 + 1 : ℕ) : ℂ) = (2 : ℂ) := by push_cast; norm_num
  have h2c : ((2 : ℕ) : ℂ) = (2 : ℂ) := by norm_cast
  have h01' : (0 + 1 : ℕ) = 1 := by norm_num
  have hF1 : (((ArithmeticFunction.moebius (1 + 1) : ℤ) : ℂ) *
      ((((1 + 1 : ℕ)) : ℂ) ^ (-s)) *
      (1 - ((((1 + 1 : ℕ))) : ℂ) / ((((2 : ℕ))) : ℂ))) = 0 := by
    have hfactor : (1 : ℂ) - ((((1 + 1 : ℕ))) : ℂ) / ((((2 : ℕ))) : ℂ) = 0 := by
      rw [h11]
      norm_num
    rw [hfactor, mul_zero]
  have hF0 : (((ArithmeticFunction.moebius (0 + 1) : ℤ) : ℂ) *
      ((((0 + 1 : ℕ)) : ℂ) ^ (-s)) *
      (1 - ((((0 + 1 : ℕ))) : ℂ) / ((((2 : ℕ))) : ℂ))) = 1 / 2 := by
    have hmoeb : (((ArithmeticFunction.moebius (0 + 1) : ℤ) : ℂ) = (1 : ℂ)) := by
      rw [h01', hmu]
      norm_cast
    have hcpow : ((((0 + 1 : ℕ))) : ℂ) ^ (-s) = (1 : ℂ) := by
      rw [h01]
      exact Complex.one_cpow _
    have hfrac : (1 : ℂ) - ((((0 + 1 : ℕ))) : ℂ) / ((((2 : ℕ))) : ℂ) = 1 / 2 := by
      rw [h01, h2c]
      norm_num
    calc (((ArithmeticFunction.moebius (0 + 1) : ℤ) : ℂ) *
          ((((0 + 1 : ℕ)) : ℂ) ^ (-s)) *
          (1 - ((((0 + 1 : ℕ))) : ℂ) / ((((2 : ℕ))) : ℂ)))
        = 1 * 1 * (1 / 2 : ℂ) := by rw [hmoeb, hcpow, hfrac]
      _ = 1 / 2 := by ring
  unfold tailMollifierReal
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hF0, hF1]
  simp

/-- Component (c), uniform error: the `K = 2` real mollifier is `1/2` away
from `1` at every shifted tail point. -/
theorem tailMollifierReal_nearOne_two (z : ℂ) :
    ‖tailMollifierReal (tailShiftedSReal z) 2 - 1‖ = 1 / 2 := by
  have hM := tailMollifierReal_two (tailShiftedSReal z)
  calc ‖tailMollifierReal (tailShiftedSReal z) 2 - 1‖
      = ‖(1 / 2 : ℂ) - 1‖ := by rw [hM]
    _ = ‖(1 / 2 : ℂ)‖ := by
        have h : ((1 / 2 : ℂ) - 1) = -((1 / 2 : ℂ)) := by ring
        rw [h, norm_neg]
    _ = 1 / 2 := by norm_num

/-- Component (c) in `≤` form for the product split. -/
theorem tailMollifierReal_nearOne_two_le (z : ℂ) :
    ‖tailMollifierReal (tailShiftedSReal z) 2 - 1‖ ≤ 1 / 2 :=
  le_of_eq (tailMollifierReal_nearOne_two z)

/-- Real conditional tail gap at `K = 2` (reuses T2's `norm_product_sub_one_le`):
with the banked `e = 1/2`, zeta-side bounds `‖zeta‖ ≤ B`, `‖zeta - 1‖ ≤ d`
and `B * (1/2) + d < 1` imply the exact Rouche product gap. -/
theorem tailRealGap_of_zetaBounds_two {B d : ℝ}
    (hB : ∀ z : ℂ, 10 < |z.re| → 0 < z.im → z.im < 1 / 2 →
      ‖riemannZeta (tailShiftedSReal z)‖ ≤ B)
    (hd : ∀ z : ℂ, 10 < |z.re| → 0 < z.im → z.im < 1 / 2 →
      ‖riemannZeta (tailShiftedSReal z) - 1‖ ≤ d)
    (hB0 : 0 ≤ B)
    (hgap : B * (1 / 2) + d < 1)
    (z : ℂ) (hx : 10 < |z.re|) (hy0 : 0 < z.im) (hy1 : z.im < 1 / 2) :
    ‖riemannZeta (tailShiftedSReal z) * tailMollifierReal (tailShiftedSReal z) 2 - 1‖ < 1 := by
  have hsplit := norm_product_sub_one_le
    (riemannZeta (tailShiftedSReal z)) (tailMollifierReal (tailShiftedSReal z) 2)
  have h1 := hB z hx hy0 hy1
  have h2 := tailMollifierReal_nearOne_two_le z
  have h3 := hd z hx hy0 hy1
  have hprod : ‖riemannZeta (tailShiftedSReal z)‖ *
      ‖tailMollifierReal (tailShiftedSReal z) 2 - 1‖ ≤ B * (1 / 2) :=
    mul_le_mul h1 h2 (norm_nonneg _) hB0
  linarith

#print axioms tailShiftedSReal_re
#print axioms tailShiftedSReal_im
#print axioms tailShiftedSReal_re_range
#print axioms tailShiftedSReal_norm_gt10
#print axioms tailShiftedSReal_ne_one
#print axioms tailMollifierReal_two
#print axioms tailMollifierReal_nearOne_two
#print axioms tailRealGap_of_zetaBounds_two

/- Quantified remainder after this block (2026-09-05): CLOSED for the REAL
definitions — shifted geometry (`tailShiftedSReal_re/im/re_range/norm_gt10/
ne_one`), mollifier component (c) `e = 1/2` at `K = 2`
(`tailMollifierReal_two`, `tailMollifierReal_nearOne_two`), and the real
conditional gap `tailRealGap_of_zetaBounds_two` (T2's `norm_product_sub_one_le`
instantiated with the banked `e`). OPEN — the zeta-side triple remainder:
uniform `B` with `‖riemannZeta (tailShiftedSReal z)‖ ≤ B` (b) and uniform `d`
with `‖riemannZeta (tailShiftedSReal z) - 1‖ ≤ d` (d) on the unbounded regime
`10 < |Re z|, 0 < Im z < 1/2`, with `B * (1/2) + d < 1`. The Dirichlet-series
majorant is PROVABLY inapplicable (`tailShiftedSReal_re_range` gives
`Re ∈ (0,1/2)`, while `zeta_eq_tsum_one_div_nat_add_one_cpow` needs `1 < Re`).
Exact next-agent task: on a BOUNDED tail cell (e.g. `10 < |Re z| ≤ 11`,
`0 < Im z < 1/2`) prove `∃ Bcell, ∀ z in cell,
‖riemannZeta (tailShiftedSReal z)‖ ≤ Bcell` via
`IsCompact.image_of_continuousOn` applied to `riemannZeta` (continuous by
`differentiableAt_riemannZeta` + `tailShiftedSReal_ne_one`) over the compact
shifted image, and likewise `∃ dcell` for `‖zeta - 1‖`; then test the numeric
side condition `Bcell * (1/2) + dcell < 1` (expected to fail on first attempt
— that failure value is the next quantified remainder). -/

/-!
## Door-4 tail leaf: compact-cell zeta bounds (tail lane, 2026-09-05, append-only)

Bounded tail cell (two-sided, closed so compact):
`10 ≤ |Re z| ≤ 11`, `0 ≤ Im z ≤ 1/2`. The strict regime
`10 < |Re z| ≤ 11`, `0 < Im z < 1/2` embeds into it
(`tailCellBounded_mem_of_regime`).

Banked here (FULLY PROVED, no sorry/admit/axiom):
* `tailCellBounded_isCompact` via Heine–Borel
  (`isCompact_iff_isClosed_bounded`: closed preimage of `Icc` under
  `Complex.continuous_re/im + continuous_abs`, bounded inside
  `Metric.closedBall 0 12` via `‖z‖^2 = re^2+im^2`);
* `tailShiftedSReal_continuous` + `tailShiftedSReal_ne_one_of_cell`
  (closed-cell pole avoidance, so `differentiableAt_riemannZeta` applies);
* `tailZetaContinuousOnCell` / `tailZetaSubOneContinuousOnCell` by composition
  (`DifferentiableAt.continuousAt.comp'`);
* `exists_tailCell_zetaUpper` (`∃ Bcell`) + `exists_tailCell_zetaNearOne`
  (`∃ dcell`) via `IsCompact.exists_bound_of_continuousOn`;
* `tailCellGap_of_cellBounds_two`: the numeric test as an implication —
  cell bounds `Bcell,dcell` with `Bcell*(1/2)+dcell<1` imply the exact
  Rouché product gap at `K=2` (reuses T2 `norm_product_sub_one_le` +
  banked `tailMollifierReal_nearOne_two_le`).

Existence-only status: `Bcell,dcell` are existential (compactness gives no
numerals), so `Bcell*(1/2)+dcell<1` cannot yet be discharged numerically.
Explicit numerals are the follow-up (functional-equation / Lindelöf-type
input or certified cell evaluation).
-/

/-- Bounded two-sided tail cell (closed, hence compact):
`10 ≤ |Re z| ≤ 11`, `0 ≤ Im z ≤ 1/2`. -/
def tailCellBounded : Set ℂ :=
  Complex.re ⁻¹' ((fun x : ℝ => |x|) ⁻¹' Set.Icc (10 : ℝ) 11) ∩
    Complex.im ⁻¹' Set.Icc (0 : ℝ) (1 / 2)

/-- Strict bounded regime embeds into the closed cell. -/
theorem tailCellBounded_mem_of_regime (z : ℂ) (hx : (10 : ℝ) < |z.re|)
    (hle : |z.re| ≤ 11) (hy0 : (0 : ℝ) < z.im) (hy1 : z.im < 1 / 2) :
    z ∈ tailCellBounded := by
  simp only [tailCellBounded, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc]
  exact ⟨⟨hx.le, hle⟩, hy0.le, hy1.le⟩

/-- The bounded tail cell is closed. -/
theorem tailCellBounded_isClosed : IsClosed tailCellBounded := by
  unfold tailCellBounded
  exact (IsClosed.preimage Complex.continuous_re
    (IsClosed.preimage continuous_abs isClosed_Icc)).inter
    (IsClosed.preimage Complex.continuous_im isClosed_Icc)

/-- The bounded tail cell lies in `closedBall 0 12`, hence is bounded. -/
theorem tailCellBounded_isBounded : Bornology.IsBounded tailCellBounded := by
  apply Metric.isBounded_closedBall.subset
  intro z hz
  obtain ⟨⟨h10, h11⟩, h0, h12⟩ := hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have habs_re : |z.re| ≤ 11 := h11
  have habs_im : |z.im| ≤ 1 / 2 := by
    rw [abs_of_nonneg h0]
    exact h12
  have hre2 : z.re * z.re ≤ (11 : ℝ) * 11 := by
    have h := mul_le_mul habs_re habs_re (abs_nonneg _) (show (0 : ℝ) ≤ 11 by norm_num)
    rwa [abs_mul_abs_self] at h
  have him2 : z.im * z.im ≤ (1 / 2 : ℝ) * (1 / 2) := by
    have h := mul_le_mul habs_im habs_im (abs_nonneg _)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rwa [abs_mul_abs_self] at h
  have hnorm : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hle : ‖z‖ ^ 2 ≤ (12 : ℝ) ^ 2 := by
    rw [hnorm]
    have hsum := add_le_add hre2 him2
    have h144 : (11 : ℝ) * 11 + (1 / 2) * (1 / 2) ≤ 12 ^ 2 := by norm_num
    exact le_trans hsum h144
  exact le_of_sq_le_sq hle (by norm_num)

/-- The bounded tail cell is compact (Heine–Borel). -/
theorem tailCellBounded_isCompact : IsCompact tailCellBounded := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨tailCellBounded_isClosed, tailCellBounded_isBounded⟩

/-- The real shifted coordinate is globally continuous. -/
theorem tailShiftedSReal_continuous : Continuous tailShiftedSReal := by
  unfold tailShiftedSReal
  exact continuous_const.add (continuous_const.mul continuous_id)

/-- Closed-cell pole avoidance: shifted cell points are never `1`. -/
theorem tailShiftedSReal_ne_one_of_cell (z : ℂ) (hz : z ∈ tailCellBounded) :
    tailShiftedSReal z ≠ 1 := by
  intro h
  have hre : (tailShiftedSReal z).re = (1 : ℂ).re := congrArg Complex.re h
  rw [tailShiftedSReal_re, Complex.one_re] at hre
  obtain ⟨⟨_, _⟩, h0, h12⟩ := hz
  linarith

/-- Zeta pulled back through the shift is continuous on the cell
(by `differentiableAt_riemannZeta` + closed-cell pole avoidance). -/
theorem tailZetaContinuousOnCell :
    ContinuousOn (fun z => riemannZeta (tailShiftedSReal z)) tailCellBounded := by
  intro x hx
  have hne : tailShiftedSReal x ≠ 1 := tailShiftedSReal_ne_one_of_cell x hx
  have hdiff : DifferentiableAt ℂ riemannZeta (tailShiftedSReal x) :=
    differentiableAt_riemannZeta hne
  exact (hdiff.continuousAt.comp' tailShiftedSReal_continuous.continuousAt).continuousWithinAt

/-- Shifted zeta-minus-one is continuous on the cell. -/
theorem tailZetaSubOneContinuousOnCell :
    ContinuousOn (fun z => riemannZeta (tailShiftedSReal z) - 1) tailCellBounded :=
  tailZetaContinuousOnCell.sub continuousOn_const

/-- Compact-cell zeta upper bound (existential): `∃ Bcell` uniform on the cell. -/
theorem exists_tailCell_zetaUpper :
    ∃ Bcell : ℝ, ∀ z ∈ tailCellBounded,
      ‖riemannZeta (tailShiftedSReal z)‖ ≤ Bcell :=
  tailCellBounded_isCompact.exists_bound_of_continuousOn tailZetaContinuousOnCell

/-- Compact-cell zeta-near-one bound (existential): `∃ dcell` uniform on the cell. -/
theorem exists_tailCell_zetaNearOne :
    ∃ dcell : ℝ, ∀ z ∈ tailCellBounded,
      ‖riemannZeta (tailShiftedSReal z) - 1‖ ≤ dcell :=
  tailCellBounded_isCompact.exists_bound_of_continuousOn tailZetaSubOneContinuousOnCell

/-- Cell-gap test as an implication: cell bounds with `Bcell*(1/2)+dcell<1`
imply the exact `K=2` Rouché product gap on the strict bounded regime. -/
theorem tailCellGap_of_cellBounds_two {Bcell dcell : ℝ}
    (hB : ∀ z ∈ tailCellBounded, ‖riemannZeta (tailShiftedSReal z)‖ ≤ Bcell)
    (hd : ∀ z ∈ tailCellBounded, ‖riemannZeta (tailShiftedSReal z) - 1‖ ≤ dcell)
    (hB0 : 0 ≤ Bcell) (hgap : Bcell * (1 / 2) + dcell < 1)
    (z : ℂ) (hx : (10 : ℝ) < |z.re|) (hle : |z.re| ≤ 11)
    (hy0 : (0 : ℝ) < z.im) (hy1 : z.im < 1 / 2) :
    ‖riemannZeta (tailShiftedSReal z) * tailMollifierReal (tailShiftedSReal z) 2 - 1‖ < 1 := by
  have hzmem : z ∈ tailCellBounded := tailCellBounded_mem_of_regime z hx hle hy0 hy1
  have hsplit := norm_product_sub_one_le
    (riemannZeta (tailShiftedSReal z)) (tailMollifierReal (tailShiftedSReal z) 2)
  have h1 := hB z hzmem
  have h2 := tailMollifierReal_nearOne_two_le z
  have h3 := hd z hzmem
  have hprod : ‖riemannZeta (tailShiftedSReal z)‖ *
      ‖tailMollifierReal (tailShiftedSReal z) 2 - 1‖ ≤ Bcell * (1 / 2) :=
    mul_le_mul h1 h2 (norm_nonneg _) hB0
  linarith

#print axioms tailCellBounded_isCompact
#print axioms tailZetaContinuousOnCell
#print axioms exists_tailCell_zetaUpper
#print axioms exists_tailCell_zetaNearOne
#print axioms tailCellGap_of_cellBounds_two

/- Quantified remainder after this block (2026-09-05): BANKED existence-only
cell bounds `exists_tailCell_zetaUpper` (`∃ Bcell`) + `exists_tailCell_zetaNearOne`
(`∃ dcell`) on `tailCellBounded` (`10 ≤ |Re| ≤ 11`, `0 ≤ Im ≤ 1/2`), plus the
conditional test `tailCellGap_of_cellBounds_two`
(`Bcell*(1/2)+dcell<1 ⇒ K=2 product gap` on the strict bounded regime).
The numeric side condition is NOT yet discharged (no numerals for
`Bcell,dcell` — compactness is non-explicit). Exact next-agent task: produce
EXPLICIT numerals `Bnum,dnum` with proved
`∀ z ∈ tailCellBounded, ‖riemannZeta (tailShiftedSReal z)‖ ≤ Bnum` and
`‖zeta-1‖ ≤ dnum` (functional-equation / Lindelöf-type estimate or certified
cell evaluation with ≤6-digit numerals), then `norm_num`-check
`Bnum*(1/2)+dnum<1` and compose via `tailCellGap_of_cellBounds_two`. -/

/-!
## Door-4 tail leaf: explicit Bnum/dnum numerals (tail lane, 2026-09-05, append-only)

Explicit-numeral bridge for the T4 cell `tailCellBounded`
(`10 ≤ |Re| ≤ 11`, `0 ≤ Im ≤ 1/2`; shifted `s = 1/2 + I*z` has
`Re(s) ∈ [0,1/2]`, `|Im(s)| ∈ [10,11]`).

Numeral source (Temp-only, no repo logs):
* `C:\Users\mmeadow\AppData\Local\Temp\kilo\tail_zeta_est.py` — Dirichlet-eta
  partial sums (`zeta = eta/(1-2^(1-s))`, `N = 5000/15000`) on the shifted
  strip give `|zeta| ~ 1.5-1.9`, `|zeta-1| ~ 0.55-0.9`; ceilings
  `Bnum = 2`, `dnum = 1` are the realistic optimistic numerals.
* `C:\Users\mmeadow\AppData\Local\Temp\kilo\tail_bnum_cert.py` (`Fraction`) —
  exact `Bnum*(1/2)+dnum = 2` and `(1/2)^2+11^2 = 485/4 ≤ 144`.

Banked here (FULLY PROVED, no sorry/admit/axiom):
* `tailShiftedSReal_re_mem_cell` / `tailShiftedSReal_im_abs_mem_cell` /
  `tailShiftedSReal_norm_le12_cell` — unconditional explicit s-image rect
  (`Re ∈ [0,1/2]`, `|Im| ∈ [10,11]`, `‖s‖ ≤ 12`) for the FE route.
* `tailBnum`/`tailDnum` (`2`/`1`, ≤6 digits) + `tailNumerals_cert_arith`
  (`Bnum*(1/2)+dnum = 2` by `norm_num`) + `tailNumerals_test_fail`
  (`¬ Bnum*(1/2)+dnum<1`): the `B*e+d<1` sufficient test FAILS at `K=2`
  (`e=1/2`), so `tailCellGap_of_cellBounds_two` cannot discharge with
  realistic bounds — the split is too coarse (true `|zeta|~1.5` already
  forces `B*0.5+d ~ 1.35 > 1`).
* `tailCellGap_of_explicitBounds` — conditional composition specialized to
  the numerals (reuses T4 `tailCellGap_of_cellBounds_two`).
* `tailK2_product_eq` / `tailK2_gap_iff_norm_sub_two` — direct `K=2`
  reformulation (`M=1/2` via `tailMollifierReal_two`): product gap `<1`
  iff `‖zeta-2‖<2`, a strictly weaker target than `B*0.5+d<1` that may
  still hold (`|zeta|~1.5 ⇒ |zeta-2|~0.5<2`).

Unconditional `∀ z ∈ cell, ‖zeta‖ ≤ Bnum` / `‖zeta-1‖ ≤ dnum` are NOT
claimed (would need FE/Stirling/convexity absent from Mathlib with
`import Mathlib` only); the numerals are realistic ceilings with a proved
FAIL verdict, not proved zeta bounds.
-/

/-- s-image real part on the closed cell: `Re ∈ [0,1/2]`. -/
theorem tailShiftedSReal_re_mem_cell (z : ℂ) (hz : z ∈ tailCellBounded) :
    0 ≤ (tailShiftedSReal z).re ∧ (tailShiftedSReal z).re ≤ 1 / 2 := by
  obtain ⟨⟨_, _⟩, h0, h12⟩ := hz
  rw [tailShiftedSReal_re]
  constructor <;> linarith

/-- s-image imaginary modulus on the closed cell: `|Im| ∈ [10,11]`. -/
theorem tailShiftedSReal_im_abs_mem_cell (z : ℂ) (hz : z ∈ tailCellBounded) :
    10 ≤ |(tailShiftedSReal z).im| ∧ |(tailShiftedSReal z).im| ≤ 11 := by
  have him : (tailShiftedSReal z).im = z.re := tailShiftedSReal_im z
  rw [him]
  obtain ⟨⟨h10, h11⟩, _, _⟩ := hz
  exact ⟨h10, h11⟩

/-- s-image norm cap on the closed cell: `‖s‖ ≤ 12`
(`(1/2)^2+11^2 = 485/4 ≤ 144`, cf. Temp `tail_bnum_cert.py`). -/
theorem tailShiftedSReal_norm_le12_cell (z : ℂ) (hz : z ∈ tailCellBounded) :
    ‖tailShiftedSReal z‖ ≤ 12 := by
  have hre := tailShiftedSReal_re_mem_cell z hz
  have him := tailShiftedSReal_im_abs_mem_cell z hz
  have habs_re : |(tailShiftedSReal z).re| ≤ 1 / 2 := by
    obtain ⟨h0, h12⟩ := hre
    rw [abs_of_nonneg h0]
    exact h12
  have habs_im : |(tailShiftedSReal z).im| ≤ 11 := him.2
  have hre2 : (tailShiftedSReal z).re * (tailShiftedSReal z).re ≤
      (1 / 2 : ℝ) * (1 / 2) := by
    have h := mul_le_mul habs_re habs_re (abs_nonneg _)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rwa [abs_mul_abs_self] at h
  have him2 : (tailShiftedSReal z).im * (tailShiftedSReal z).im ≤
      (11 : ℝ) * 11 := by
    have h := mul_le_mul habs_im habs_im (abs_nonneg _)
      (show (0 : ℝ) ≤ 11 by norm_num)
    rwa [abs_mul_abs_self] at h
  have hnorm : ‖tailShiftedSReal z‖ ^ 2 =
      (tailShiftedSReal z).re * (tailShiftedSReal z).re +
      (tailShiftedSReal z).im * (tailShiftedSReal z).im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hle : ‖tailShiftedSReal z‖ ^ 2 ≤ (12 : ℝ) ^ 2 := by
    rw [hnorm]
    have hsum := add_le_add hre2 him2
    have h144 : (1 / 2 : ℝ) * (1 / 2) + 11 * 11 ≤ 12 ^ 2 := by norm_num
    exact le_trans hsum h144
  exact le_of_sq_le_sq hle (by norm_num)

/-- Explicit zeta-upper numeral (realistic ceiling from Temp `tail_zeta_est.py`;
unconditional `∀ z ∈ cell` bound NOT claimed — see header). -/
def tailBnum : ℝ := 2

/-- Explicit zeta-near-one numeral (realistic ceiling from Temp `tail_zeta_est.py`;
unconditional `∀ z ∈ cell` bound NOT claimed — see header). -/
def tailDnum : ℝ := 1

/-- Certificate arithmetic (exact `Fraction` in Temp `tail_bnum_cert.py`):
`Bnum*(1/2)+dnum = 2`. -/
theorem tailNumerals_cert_arith : tailBnum * (1 / 2) + tailDnum = 2 := by
  unfold tailBnum tailDnum
  norm_num

/-- Test verdict: the `B*e+d<1` sufficient condition FAILS for the explicit
numerals (`2<1` is false), so the T4 split cannot close `K=2` with realistic
bounds. -/
theorem tailNumerals_test_fail : ¬ (tailBnum * (1 / 2) + tailDnum < 1) := by
  rw [tailNumerals_cert_arith]
  norm_num

/-- Conditional composition specialized to the explicit numerals
(reuses T4 `tailCellGap_of_cellBounds_two`). -/
theorem tailCellGap_of_explicitBounds
    (hB : ∀ z ∈ tailCellBounded, ‖riemannZeta (tailShiftedSReal z)‖ ≤ tailBnum)
    (hd : ∀ z ∈ tailCellBounded, ‖riemannZeta (tailShiftedSReal z) - 1‖ ≤ tailDnum)
    (hgap : tailBnum * (1 / 2) + tailDnum < 1)
    (z : ℂ) (hx : (10 : ℝ) < |z.re|) (hle : |z.re| ≤ 11)
    (hy0 : (0 : ℝ) < z.im) (hy1 : z.im < 1 / 2) :
    ‖riemannZeta (tailShiftedSReal z) * tailMollifierReal (tailShiftedSReal z) 2 - 1‖ < 1 := by
  have hB0 : 0 ≤ tailBnum := by unfold tailBnum; norm_num
  exact tailCellGap_of_cellBounds_two hB hd hB0 hgap z hx hle hy0 hy1

/-- Direct `K=2` product shape (`M=1/2` via `tailMollifierReal_two`). -/
theorem tailK2_product_eq (z : ℂ) :
    riemannZeta (tailShiftedSReal z) * tailMollifierReal (tailShiftedSReal z) 2 - 1 =
    riemannZeta (tailShiftedSReal z) / 2 - 1 := by
  rw [tailMollifierReal_two]
  ring

/-- Direct `K=2` gap reformulation: product gap `<1` iff `‖zeta-2‖<2`
(`(zeta-2)/2`, strictly weaker than `B*0.5+d<1`). -/
theorem tailK2_gap_iff_norm_sub_two (z : ℂ) :
    ‖riemannZeta (tailShiftedSReal z) * tailMollifierReal (tailShiftedSReal z) 2 - 1‖ < 1 ↔
    ‖riemannZeta (tailShiftedSReal z) - 2‖ < 2 := by
  have heq : riemannZeta (tailShiftedSReal z) * tailMollifierReal (tailShiftedSReal z) 2 - 1 =
      (riemannZeta (tailShiftedSReal z) - 2) / 2 := by
    rw [tailMollifierReal_two]
    ring
  rw [heq, norm_div]
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by simp
  rw [h2]
  constructor <;> intro h <;> linarith

#print axioms tailShiftedSReal_re_mem_cell
#print axioms tailShiftedSReal_im_abs_mem_cell
#print axioms tailShiftedSReal_norm_le12_cell
#print axioms tailNumerals_cert_arith
#print axioms tailNumerals_test_fail
#print axioms tailCellGap_of_explicitBounds
#print axioms tailK2_product_eq
#print axioms tailK2_gap_iff_norm_sub_two

/- Quantified remainder after this block (2026-09-05): BANKED explicit numerals
`tailBnum = 2` / `tailDnum = 1` (realistic ceilings from Temp eta estimates,
`Fraction`-certified `Bnum*(1/2)+dnum = 2`) with proved FAIL verdict
`tailNumerals_test_fail` (`¬ Bnum*(1/2)+dnum<1`), conditional composition
`tailCellGap_of_explicitBounds` (via T4), s-image rect
`tailShiftedSReal_re_mem_cell` / `im_abs_mem_cell` / `norm_le12_cell`
(`Re ∈ [0,1/2]`, `|Im| ∈ [10,11]`, `‖s‖ ≤ 12`), and direct `K=2` reduction
`tailK2_product_eq` / `tailK2_gap_iff_norm_sub_two` (`gap<1 ↔ ‖zeta-2‖<2`).
RESIDUAL: unconditional `∀ z ∈ tailCellBounded, ‖zeta‖ ≤ 2` /
`‖zeta-1‖ ≤ 1` remain OPEN (need FE/Stirling/convexity); moreover the
`B*e+d<1` split is PROVED too coarse at `K=2`/`e=1/2` (true `|zeta|~1.5`
forces `~1.35>1`). Exact next-agent task: prove `‖riemannZeta s - 2‖ < 2`
on the banked s-rect (`Re ∈ [0,1/2]`, `|Im| ∈ [10,11]`, `‖s‖ ≤ 12`) or switch
to `K>2` (smaller mollifier error), then close via `tailK2_gap_iff_norm_sub_two`. -/

/-!
## Door-4 tail leaf: K=3,4 mollifier errors (tail lane, 2026-09-05, append-only)

K>2 route verdict (Temp `tail_k34_cert.py`, `Fraction`): the smoothed
Mollifier does NOT get closer to 1 as K grows — triangle errors grow
`e(2)=1/2 < e(3)=2/3 < e(4)=1`, so `B*e+d` with `B=2,d=1` gives
`2, 7/3, 3` (all `>1`). K=2 is minimal among {2,3,4}; no K>2 closes.

Banked here (FULLY PROVED, no sorry/admit/axiom), mirroring
`tailMollifierReal_two` read-only:
* `tailNatCpowNeg_norm_le_one` — `‖(n:ℂ)^{-s}‖ ≤ 1` for `1 ≤ n`, `0 ≤ Re s`
  (via `Complex.norm_natCast_cpow_of_pos` + `Real.rpow_le_one_of_one_le_of_nonpos`);
* `tailMollifierReal_three` (`2/3 - (1/3)*2^{-s}`) + `tailMollifierReal_nearOne_three_le`
  (`≤ 2/3` on `0 ≤ Re s`);
* `tailMollifierReal_four` (`3/4 - (1/2)*2^{-s} - (1/4)*3^{-s}`) +
  `tailMollifierReal_nearOne_four_le` (`≤ 1` on `0 ≤ Re s`);
* `tailRealGap_of_zetaBounds_three/four` — conditional gaps with `e=2/3,1`;
* `tailNumerals_three/four_cert_arith` + `test_fail` (`7/3`, `3`, both `¬ <1`);
* `tailMollifierError_order` (`1/2 < 2/3 < 1`).
-/

/-- Cpow-norm cap: `‖(n:ℂ)^{-s}‖ ≤ 1` when `1 ≤ n` and `0 ≤ Re s`. -/
theorem tailNatCpowNeg_norm_le_one (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hre : 0 ≤ s.re) :
    ‖((n : ℂ) ^ (-s))‖ ≤ 1 := by
  have hn0 : 0 < n := by omega
  rw [Complex.norm_natCast_cpow_of_pos hn0 (-s), Complex.neg_re]
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2 : -s.re ≤ 0 := by linarith
  exact Real.rpow_le_one_of_one_le_of_nonpos h1 h2

/-- Component (c) at `K = 3`: `M = 2/3 - (1/3)*2^{-s}`
(the `n = 2` term carries `1 - 3/3 = 0`). -/
theorem tailMollifierReal_three (s : ℂ) :
    tailMollifierReal s 3 =
      (2 / 3 : ℂ) - (1 / 3 : ℂ) * ((((2 : ℕ) : ℂ)) ^ (-s)) := by
  have hmu1 : ArithmeticFunction.moebius 1 = 1 :=
    ArithmeticFunction.moebius_apply_one
  have hmu2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h01 : ((0 + 1 : ℕ) : ℂ) = (1 : ℂ) := by push_cast; norm_num
  have h11 : ((1 + 1 : ℕ) : ℂ) = (2 : ℂ) := by push_cast; norm_num
  have h21 : ((2 + 1 : ℕ) : ℂ) = (3 : ℂ) := by push_cast; norm_num
  have h3c : ((3 : ℕ) : ℂ) = (3 : ℂ) := by norm_cast
  have h01N : (0 + 1 : ℕ) = 1 := by norm_num
  have h11N : (1 + 1 : ℕ) = 2 := by norm_num
  have hF0 : (((ArithmeticFunction.moebius (0 + 1) : ℤ) : ℂ) *
      ((((0 + 1 : ℕ)) : ℂ) ^ (-s)) *
      (1 - ((((0 + 1 : ℕ))) : ℂ) / ((((3 : ℕ))) : ℂ))) = (2 / 3 : ℂ) := by
    have hmoeb : (((ArithmeticFunction.moebius (0 + 1) : ℤ) : ℂ) = (1 : ℂ)) := by
      rw [h01N, hmu1]
      norm_cast
    have hcpow : ((((0 + 1 : ℕ))) : ℂ) ^ (-s) = (1 : ℂ) := by
      rw [h01]
      exact Complex.one_cpow _
    have hfrac : (1 : ℂ) - ((((0 + 1 : ℕ))) : ℂ) / ((((3 : ℕ))) : ℂ) = (2 / 3 : ℂ) := by
      rw [h01, h3c]
      norm_num
    rw [hmoeb, hcpow, hfrac]
    ring
  have hF1 : (((ArithmeticFunction.moebius (1 + 1) : ℤ) : ℂ) *
      ((((1 + 1 : ℕ)) : ℂ) ^ (-s)) *
      (1 - ((((1 + 1 : ℕ))) : ℂ) / ((((3 : ℕ))) : ℂ))) =
      -((1 / 3 : ℂ) * ((((2 : ℕ) : ℂ)) ^ (-s))) := by
    have hmoeb : (((ArithmeticFunction.moebius (1 + 1) : ℤ) : ℂ) = (-1 : ℂ)) := by
      rw [h11N, hmu2]
      norm_cast
    have hbase : ((((1 + 1 : ℕ))) : ℂ) ^ (-s) = ((((2 : ℕ) : ℂ)) ^ (-s)) := by
      have hcast : ((((1 + 1 : ℕ))) : ℂ) = ((((2 : ℕ) : ℂ))) := by norm_cast
      rw [hcast]
    have hfrac : (1 : ℂ) - ((((1 + 1 : ℕ))) : ℂ) / ((((3 : ℕ))) : ℂ) = (1 / 3 : ℂ) := by
      rw [h11, h3c]
      norm_num
    rw [hmoeb, hbase, hfrac]
    ring
  have hF2 : (((ArithmeticFunction.moebius (2 + 1) : ℤ) : ℂ) *
      ((((2 + 1 : ℕ)) : ℂ) ^ (-s)) *
      (1 - ((((2 + 1 : ℕ))) : ℂ) / ((((3 : ℕ))) : ℂ))) = 0 := by
    have hfactor : (1 : ℂ) - ((((2 + 1 : ℕ))) : ℂ) / ((((3 : ℕ))) : ℂ) = 0 := by
      have heq : ((((2 + 1 : ℕ))) : ℂ) = ((((3 : ℕ))) : ℂ) := by norm_cast
      have hne : ((((3 : ℕ))) : ℂ) ≠ 0 := by exact_mod_cast (by norm_num : (3 : ℕ) ≠ 0)
      rw [heq, div_self hne, sub_self]
    rw [hfactor, mul_zero]
  unfold tailMollifierReal
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hF0, hF1, hF2]
  ring

/-- Uniform `K = 3` mollifier error `e = 2/3` when `0 ≤ Re s`. -/
theorem tailMollifierReal_nearOne_three_le (s : ℂ) (hre : 0 ≤ s.re) :
    ‖tailMollifierReal s 3 - 1‖ ≤ 2 / 3 := by
  have hM := tailMollifierReal_three s
  have h2 := tailNatCpowNeg_norm_le_one 2 (by norm_num) s hre
  have h2c : ((((2 : ℕ) : ℂ)) ^ (-s)) = ((((1 + 1 : ℕ)) : ℂ) ^ (-s)) := by norm_cast
  rw [hM]
  have heq : (2 / 3 : ℂ) - (1 / 3 : ℂ) * ((((2 : ℕ) : ℂ)) ^ (-s)) - 1 =
      (-(1 / 3 : ℂ)) + (-(1 / 3 : ℂ)) * ((((2 : ℕ) : ℂ)) ^ (-s)) := by ring
  rw [heq]
  calc ‖(-(1 / 3 : ℂ)) + (-(1 / 3 : ℂ)) * ((((2 : ℕ) : ℂ)) ^ (-s))‖
      ≤ ‖(-(1 / 3 : ℂ))‖ + ‖(-(1 / 3 : ℂ)) * ((((2 : ℕ) : ℂ)) ^ (-s))‖ :=
        norm_add_le _ _
    _ = 1 / 3 + (1 / 3) * ‖((((2 : ℕ) : ℂ)) ^ (-s))‖ := by
        rw [norm_neg, norm_mul, norm_neg]
        norm_num
    _ ≤ 1 / 3 + (1 / 3) * 1 := by
        have := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 1 / 3 by norm_num)
        linarith
    _ = 2 / 3 := by norm_num

/-- Component (c) at `K = 4`: `M = 3/4 - (1/2)*2^{-s} - (1/4)*3^{-s}`
(the `n = 3` term carries `1 - 4/4 = 0`). -/
theorem tailMollifierReal_four (s : ℂ) :
    tailMollifierReal s 4 =
      (3 / 4 : ℂ) - (1 / 2 : ℂ) * ((((2 : ℕ) : ℂ)) ^ (-s)) -
        (1 / 4 : ℂ) * ((((3 : ℕ) : ℂ)) ^ (-s)) := by
  have hmu1 : ArithmeticFunction.moebius 1 = 1 :=
    ArithmeticFunction.moebius_apply_one
  have hmu2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have hmu3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h01 : ((0 + 1 : ℕ) : ℂ) = (1 : ℂ) := by push_cast; norm_num
  have h11 : ((1 + 1 : ℕ) : ℂ) = (2 : ℂ) := by push_cast; norm_num
  have h21 : ((2 + 1 : ℕ) : ℂ) = (3 : ℂ) := by push_cast; norm_num
  have h31 : ((3 + 1 : ℕ) : ℂ) = (4 : ℂ) := by push_cast; norm_num
  have h4c : ((4 : ℕ) : ℂ) = (4 : ℂ) := by norm_cast
  have h01N : (0 + 1 : ℕ) = 1 := by norm_num
  have h11N : (1 + 1 : ℕ) = 2 := by norm_num
  have h21N : (2 + 1 : ℕ) = 3 := by norm_num
  have hF0 : (((ArithmeticFunction.moebius (0 + 1) : ℤ) : ℂ) *
      ((((0 + 1 : ℕ)) : ℂ) ^ (-s)) *
      (1 - ((((0 + 1 : ℕ))) : ℂ) / ((((4 : ℕ))) : ℂ))) = (3 / 4 : ℂ) := by
    have hmoeb : (((ArithmeticFunction.moebius (0 + 1) : ℤ) : ℂ) = (1 : ℂ)) := by
      rw [h01N, hmu1]
      norm_cast
    have hcpow : ((((0 + 1 : ℕ))) : ℂ) ^ (-s) = (1 : ℂ) := by
      rw [h01]
      exact Complex.one_cpow _
    have hfrac : (1 : ℂ) - ((((0 + 1 : ℕ))) : ℂ) / ((((4 : ℕ))) : ℂ) = (3 / 4 : ℂ) := by
      rw [h01, h4c]
      norm_num
    rw [hmoeb, hcpow, hfrac]
    ring
  have hF1 : (((ArithmeticFunction.moebius (1 + 1) : ℤ) : ℂ) *
      ((((1 + 1 : ℕ)) : ℂ) ^ (-s)) *
      (1 - ((((1 + 1 : ℕ))) : ℂ) / ((((4 : ℕ))) : ℂ))) =
      -((1 / 2 : ℂ) * ((((2 : ℕ) : ℂ)) ^ (-s))) := by
    have hmoeb : (((ArithmeticFunction.moebius (1 + 1) : ℤ) : ℂ) = (-1 : ℂ)) := by
      rw [h11N, hmu2]
      norm_cast
    have hbase : ((((1 + 1 : ℕ))) : ℂ) ^ (-s) = ((((2 : ℕ) : ℂ)) ^ (-s)) := by
      have hcast : ((((1 + 1 : ℕ))) : ℂ) = ((((2 : ℕ) : ℂ))) := by norm_cast
      rw [hcast]
    have hfrac : (1 : ℂ) - ((((1 + 1 : ℕ))) : ℂ) / ((((4 : ℕ))) : ℂ) = (1 / 2 : ℂ) := by
      rw [h11, h4c]
      norm_num
    rw [hmoeb, hbase, hfrac]
    ring
  have hF2 : (((ArithmeticFunction.moebius (2 + 1) : ℤ) : ℂ) *
      ((((2 + 1 : ℕ)) : ℂ) ^ (-s)) *
      (1 - ((((2 + 1 : ℕ))) : ℂ) / ((((4 : ℕ))) : ℂ))) =
      -((1 / 4 : ℂ) * ((((3 : ℕ) : ℂ)) ^ (-s))) := by
    have hmoeb : (((ArithmeticFunction.moebius (2 + 1) : ℤ) : ℂ) = (-1 : ℂ)) := by
      rw [h21N, hmu3]
      norm_cast
    have hbase : ((((2 + 1 : ℕ))) : ℂ) ^ (-s) = ((((3 : ℕ) : ℂ)) ^ (-s)) := by
      have hcast : ((((2 + 1 : ℕ))) : ℂ) = ((((3 : ℕ) : ℂ))) := by norm_cast
      rw [hcast]
    have hfrac : (1 : ℂ) - ((((2 + 1 : ℕ))) : ℂ) / ((((4 : ℕ))) : ℂ) = (1 / 4 : ℂ) := by
      rw [h21, h4c]
      norm_num
    rw [hmoeb, hbase, hfrac]
    ring
  have hF3 : (((ArithmeticFunction.moebius (3 + 1) : ℤ) : ℂ) *
      ((((3 + 1 : ℕ)) : ℂ) ^ (-s)) *
      (1 - ((((3 + 1 : ℕ))) : ℂ) / ((((4 : ℕ))) : ℂ))) = 0 := by
    have hfactor : (1 : ℂ) - ((((3 + 1 : ℕ))) : ℂ) / ((((4 : ℕ))) : ℂ) = 0 := by
      have heq : ((((3 + 1 : ℕ))) : ℂ) = ((((4 : ℕ))) : ℂ) := by norm_cast
      have hne : ((((4 : ℕ))) : ℂ) ≠ 0 := by exact_mod_cast (by norm_num : (4 : ℕ) ≠ 0)
      rw [heq, div_self hne, sub_self]
    rw [hfactor, mul_zero]
  unfold tailMollifierReal
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hF0, hF1, hF2, hF3]
  ring

/-- Uniform `K = 4` mollifier error `e = 1` when `0 ≤ Re s`. -/
theorem tailMollifierReal_nearOne_four_le (s : ℂ) (hre : 0 ≤ s.re) :
    ‖tailMollifierReal s 4 - 1‖ ≤ 1 := by
  have hM := tailMollifierReal_four s
  have h2 := tailNatCpowNeg_norm_le_one 2 (by norm_num) s hre
  have h3 := tailNatCpowNeg_norm_le_one 3 (by norm_num) s hre
  rw [hM]
  have heq : (3 / 4 : ℂ) - (1 / 2 : ℂ) * ((((2 : ℕ) : ℂ)) ^ (-s)) -
      (1 / 4 : ℂ) * ((((3 : ℕ) : ℂ)) ^ (-s)) - 1 =
      (-(1 / 4 : ℂ)) + (-(1 / 2 : ℂ)) * ((((2 : ℕ) : ℂ)) ^ (-s)) +
        (-(1 / 4 : ℂ)) * ((((3 : ℕ) : ℂ)) ^ (-s)) := by ring
  rw [heq]
  have htri : ‖(-(1 / 4 : ℂ)) + (-(1 / 2 : ℂ)) * ((((2 : ℕ) : ℂ)) ^ (-s)) +
      (-(1 / 4 : ℂ)) * ((((3 : ℕ) : ℂ)) ^ (-s))‖ ≤
      ‖(-(1 / 4 : ℂ))‖ + ‖(-(1 / 2 : ℂ)) * ((((2 : ℕ) : ℂ)) ^ (-s))‖ +
        ‖(-(1 / 4 : ℂ)) * ((((3 : ℕ) : ℂ)) ^ (-s))‖ := by
    calc ‖(-(1 / 4 : ℂ)) + (-(1 / 2 : ℂ)) * ((((2 : ℕ) : ℂ)) ^ (-s)) +
        (-(1 / 4 : ℂ)) * ((((3 : ℕ) : ℂ)) ^ (-s))‖
        = ‖((-(1 / 4 : ℂ)) + (-(1 / 2 : ℂ)) * ((((2 : ℕ) : ℂ)) ^ (-s))) +
          (-(1 / 4 : ℂ)) * ((((3 : ℕ) : ℂ)) ^ (-s))‖ := by ring_nf
      _ ≤ ‖(-(1 / 4 : ℂ)) + (-(1 / 2 : ℂ)) * ((((2 : ℕ) : ℂ)) ^ (-s))‖ +
          ‖(-(1 / 4 : ℂ)) * ((((3 : ℕ) : ℂ)) ^ (-s))‖ := norm_add_le _ _
      _ ≤ (‖(-(1 / 4 : ℂ))‖ + ‖(-(1 / 2 : ℂ)) * ((((2 : ℕ) : ℂ)) ^ (-s))‖) +
          ‖(-(1 / 4 : ℂ)) * ((((3 : ℕ) : ℂ)) ^ (-s))‖ := by
          gcongr
          exact norm_add_le _ _
  have e1 : ‖(-(1 / 4 : ℂ))‖ = (1 / 4 : ℝ) := by norm_num
  have e2 : ‖(-(1 / 2 : ℂ)) * ((((2 : ℕ) : ℂ)) ^ (-s))‖ =
      (1 / 2) * ‖((((2 : ℕ) : ℂ)) ^ (-s))‖ := by
    rw [norm_mul, norm_neg]
    norm_num
  have e3 : ‖(-(1 / 4 : ℂ)) * ((((3 : ℕ) : ℂ)) ^ (-s))‖ =
      (1 / 4) * ‖((((3 : ℕ) : ℂ)) ^ (-s))‖ := by
    rw [norm_mul, norm_neg]
    norm_num
  rw [e1, e2, e3] at htri
  have hle : (1 / 4 : ℝ) + (1 / 2) * ‖((((2 : ℕ) : ℂ)) ^ (-s))‖ +
      (1 / 4) * ‖((((3 : ℕ) : ℂ)) ^ (-s))‖ ≤ 1 := by
    have h2' : (1 / 2 : ℝ) * ‖((((2 : ℕ) : ℂ)) ^ (-s))‖ ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      linarith
    have h3' : (1 / 4 : ℝ) * ‖((((3 : ℕ) : ℂ)) ^ (-s))‖ ≤ 1 / 4 := by
      have := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ 1 / 4 by norm_num)
      linarith
    linarith
  linarith

/-- Real conditional tail gap at `K = 3` with banked `e = 2/3`. -/
theorem tailRealGap_of_zetaBounds_three {B d : ℝ}
    (hB : ∀ z : ℂ, z ∈ tailCellBounded →
      ‖riemannZeta (tailShiftedSReal z)‖ ≤ B)
    (hd : ∀ z : ℂ, z ∈ tailCellBounded →
      ‖riemannZeta (tailShiftedSReal z) - 1‖ ≤ d)
    (hB0 : 0 ≤ B)
    (hgap : B * (2 / 3) + d < 1)
    (z : ℂ) (hz : z ∈ tailCellBounded) :
    ‖riemannZeta (tailShiftedSReal z) * tailMollifierReal (tailShiftedSReal z) 3 - 1‖ < 1 := by
  have hsplit := norm_product_sub_one_le
    (riemannZeta (tailShiftedSReal z)) (tailMollifierReal (tailShiftedSReal z) 3)
  have h1 := hB z hz
  have hre : 0 ≤ (tailShiftedSReal z).re := (tailShiftedSReal_re_mem_cell z hz).1
  have h2 := tailMollifierReal_nearOne_three_le (tailShiftedSReal z) hre
  have h3 := hd z hz
  have hprod : ‖riemannZeta (tailShiftedSReal z)‖ *
      ‖tailMollifierReal (tailShiftedSReal z) 3 - 1‖ ≤ B * (2 / 3) :=
    mul_le_mul h1 h2 (norm_nonneg _) hB0
  linarith

/-- Real conditional tail gap at `K = 4` with banked `e = 1`. -/
theorem tailRealGap_of_zetaBounds_four {B d : ℝ}
    (hB : ∀ z : ℂ, z ∈ tailCellBounded →
      ‖riemannZeta (tailShiftedSReal z)‖ ≤ B)
    (hd : ∀ z : ℂ, z ∈ tailCellBounded →
      ‖riemannZeta (tailShiftedSReal z) - 1‖ ≤ d)
    (hB0 : 0 ≤ B)
    (hgap : B * 1 + d < 1)
    (z : ℂ) (hz : z ∈ tailCellBounded) :
    ‖riemannZeta (tailShiftedSReal z) * tailMollifierReal (tailShiftedSReal z) 4 - 1‖ < 1 := by
  have hsplit := norm_product_sub_one_le
    (riemannZeta (tailShiftedSReal z)) (tailMollifierReal (tailShiftedSReal z) 4)
  have h1 := hB z hz
  have hre : 0 ≤ (tailShiftedSReal z).re := (tailShiftedSReal_re_mem_cell z hz).1
  have h2 := tailMollifierReal_nearOne_four_le (tailShiftedSReal z) hre
  have h3 := hd z hz
  have hprod : ‖riemannZeta (tailShiftedSReal z)‖ *
      ‖tailMollifierReal (tailShiftedSReal z) 4 - 1‖ ≤ B * 1 :=
    mul_le_mul h1 h2 (norm_nonneg _) hB0
  linarith

/-- Certificate arithmetic at `K = 3` (exact `Fraction` in Temp `tail_k34_cert.py`):
`Bnum*(2/3)+dnum = 7/3`. -/
theorem tailNumerals_three_cert_arith : tailBnum * (2 / 3) + tailDnum = 7 / 3 := by
  unfold tailBnum tailDnum
  norm_num

/-- Test verdict at `K = 3`: `B*e+d<1` FAILS (`7/3<1` false). -/
theorem tailNumerals_three_test_fail : ¬ (tailBnum * (2 / 3) + tailDnum < 1) := by
  rw [tailNumerals_three_cert_arith]
  norm_num

/-- Certificate arithmetic at `K = 4`: `Bnum*1+dnum = 3`. -/
theorem tailNumerals_four_cert_arith : tailBnum * 1 + tailDnum = 3 := by
  unfold tailBnum tailDnum
  norm_num

/-- Test verdict at `K = 4`: `B*e+d<1` FAILS (`3<1` false). -/
theorem tailNumerals_four_test_fail : ¬ (tailBnum * 1 + tailDnum < 1) := by
  rw [tailNumerals_four_cert_arith]
  norm_num

/-- Error ordering: `K=2` minimal among `{2,3,4}` (`1/2 < 2/3 < 1`). -/
theorem tailMollifierError_order : (1 / 2 : ℝ) < 2 / 3 ∧ (2 / 3 : ℝ) < 1 := by
  constructor <;> norm_num

#print axioms tailNatCpowNeg_norm_le_one
#print axioms tailMollifierReal_three
#print axioms tailMollifierReal_nearOne_three_le
#print axioms tailMollifierReal_four
#print axioms tailMollifierReal_nearOne_four_le
#print axioms tailRealGap_of_zetaBounds_three
#print axioms tailRealGap_of_zetaBounds_four
#print axioms tailNumerals_three_cert_arith
#print axioms tailNumerals_three_test_fail
#print axioms tailNumerals_four_cert_arith
#print axioms tailNumerals_four_test_fail
#print axioms tailMollifierError_order

/- Quantified remainder after this block (2026-09-05): BANKED `K=3,4` real
mollifier evaluations + triangle errors (`e=2/3,1`), conditional gaps
`tailRealGap_of_zetaBounds_three/four`, `Fraction`-certified FAIL verdicts
(`7/3`, `3`, both `¬ <1`), and ordering `1/2<2/3<1` (K=2 minimal). K>2 does
NOT improve the split — errors grow, so `B*e+d<1` with `B=2,d=1` is dead at
`K=2,3,4`. RESIDUAL: the direct `‖zeta-2‖<2` target
(`tailK2_gap_iff_norm_sub_two`) and any `K≥5` (same growth pattern; top term
always zero, triangle sum `∑(1-n/K) ~ K/2` grows) remain the only tail-lane
options. Exact next-agent task: prove `‖riemannZeta s - 2‖ < 2` on the banked
s-rect (`Re∈[0,1/2]`, `|Im|∈[10,11]`, `‖s‖≤12`) via stated FE/convexity input,
or push `K≥5` evaluations only to confirm growth (no closure expected). -/

/-!
## Door-4 tail leaf: LAST route `‖ζ-2‖<2` bridge (tail lane, 2026-09-05, append-only)

Verified-green context (read-only reuse, no redefinition):
* ALL split routes dead: `B*e+d<1` fails at K=2,3,4 with K=2 minimal
  (`tailNumerals_test_fail`, `tailNumerals_three/four_test_fail`,
  `tailMollifierError_order`: `e=1/2<2/3<1` proved).
* Banked s-rect (read-only): `tailShiftedSReal_re_mem_cell` (`Re∈[0,1/2]`),
  `tailShiftedSReal_im_abs_mem_cell` (`|Im|∈[10,11]`),
  `tailShiftedSReal_norm_le12_cell` (`‖s‖≤12`).
* Closer (read-only): `tailK2_gap_iff_norm_sub_two`
  (`K=2` product gap `<1 ↔ ‖ζ-2‖<2`).

Why a zeta-UPPER bound alone can never close: `‖ζ-2‖ ≤ ‖ζ‖+2` is vacuous
for the `<2` target (e.g. `ζ=-B` gives `B+2`). The single operative input is
a zeta-NEAR-ONE bound `‖ζ-1‖ ≤ d` with `d<1` (then `‖ζ-2‖ ≤ d+1 <2`), or
directly `‖ζ-2‖ ≤ r` with `r<2`.

Banked here (FULLY PROVED, no sorry/admit/axiom):
* `TailStripZetaNearOne d` / `TailStripZetaSubTwo r` — clearly-named
  FE/convexity hypothesis Props (Mathlib with `import Mathlib` only supplies
  the FE identity `riemannZeta_one_sub` but no explicit critical-strip
  numeral; the numerical input is isolated here).
* `tailZetaSubTwo_of_nearOne_le` / `tailZetaSubTwo_lt_two_of_nearOne_lt_one`
  — unconditional triangle step `d → d+1` (strict `<2` when `d<1`).
* `tailK2_gap_of_nearOne_lt_one` / `tailK2_gap_of_subTwo_lt_two` — conditional
  CLOSURE of the exact `K=2` Rouché gap via `tailK2_gap_iff_norm_sub_two`.
* `tailZetaSubTwoContinuousOnCell` + `exists_tailCell_zetaSubTwo` —
  STRONGEST unconditional partial bound: `∃ B2` with
  `∀ z ∈ cell, ‖ζ-2‖ ≤ B2` (compactness; numeral-free, so gap open).
* `tailInvSub_norm_le_tenth_cell` — unconditional EXPLICIT polar cap
  `‖(s-1)⁻¹‖ ≤ 1/10` on the cell (the `(s-1)⁻¹` piece of
  `riemannZeta_eq_inv_sub_add`; residual is the entire `ζ₀` part).
-/

/-- FE/convexity hypothesis (near-one form): uniform `‖ζ-1‖ ≤ d` on the cell.
This is the isolated analytic input (functional equation + convexity /
certified evaluation would supply it); with `d < 1` it closes the leaf via
`tailK2_gap_of_nearOne_lt_one` below. -/
def TailStripZetaNearOne (d : ℝ) : Prop :=
  ∀ z ∈ tailCellBounded, ‖riemannZeta (tailShiftedSReal z) - 1‖ ≤ d

/-- FE/convexity hypothesis (direct form): uniform `‖ζ-2‖ ≤ r` on the cell.
With `r < 2` it closes the leaf via `tailK2_gap_of_subTwo_lt_two` below. -/
def TailStripZetaSubTwo (r : ℝ) : Prop :=
  ∀ z ∈ tailCellBounded, ‖riemannZeta (tailShiftedSReal z) - 2‖ ≤ r

/-- Unconditional triangle step: `‖ζ-1‖ ≤ d → ‖ζ-2‖ ≤ d+1`. -/
theorem tailZetaSubTwo_of_nearOne_le {d : ℝ} (z : ℂ)
    (h : ‖riemannZeta (tailShiftedSReal z) - 1‖ ≤ d) :
    ‖riemannZeta (tailShiftedSReal z) - 2‖ ≤ d + 1 := by
  have heq : riemannZeta (tailShiftedSReal z) - 2 =
      (riemannZeta (tailShiftedSReal z) - 1) - 1 := by ring
  calc ‖riemannZeta (tailShiftedSReal z) - 2‖
      = ‖(riemannZeta (tailShiftedSReal z) - 1) - 1‖ := by rw [heq]
    _ ≤ ‖riemannZeta (tailShiftedSReal z) - 1‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = ‖riemannZeta (tailShiftedSReal z) - 1‖ + 1 := by rw [norm_one]
    _ ≤ d + 1 := by linarith

/-- Strict form: `‖ζ-1‖ < 1 → ‖ζ-2‖ < 2`. -/
theorem tailZetaSubTwo_lt_two_of_nearOne_lt_one (z : ℂ)
    (h : ‖riemannZeta (tailShiftedSReal z) - 1‖ < 1) :
    ‖riemannZeta (tailShiftedSReal z) - 2‖ < 2 := by
  have hle := tailZetaSubTwo_of_nearOne_le
    (d := ‖riemannZeta (tailShiftedSReal z) - 1‖) z le_rfl
  linarith

/-- Conditional CLOSURE from near-one input: `TailStripZetaNearOne d` with
`d < 1` implies the exact `K=2` Rouché product gap on the strict regime. -/
theorem tailK2_gap_of_nearOne_lt_one {d : ℝ}
    (hd : TailStripZetaNearOne d) (hdl : d < 1)
    (z : ℂ) (hx : (10 : ℝ) < |z.re|) (hle : |z.re| ≤ 11)
    (hy0 : (0 : ℝ) < z.im) (hy1 : z.im < 1 / 2) :
    ‖riemannZeta (tailShiftedSReal z) * tailMollifierReal (tailShiftedSReal z) 2 - 1‖ < 1 := by
  have hzmem : z ∈ tailCellBounded := tailCellBounded_mem_of_regime z hx hle hy0 hy1
  have h1 := hd z hzmem
  have h2 : ‖riemannZeta (tailShiftedSReal z) - 2‖ < 2 := by
    have hle2 := tailZetaSubTwo_of_nearOne_le z h1
    linarith
  exact (tailK2_gap_iff_norm_sub_two z).mpr h2

/-- Conditional CLOSURE from direct input: `TailStripZetaSubTwo r` with
`r < 2` implies the exact `K=2` Rouché product gap on the strict regime. -/
theorem tailK2_gap_of_subTwo_lt_two {r : ℝ}
    (hr : TailStripZetaSubTwo r) (hrl : r < 2)
    (z : ℂ) (hx : (10 : ℝ) < |z.re|) (hle : |z.re| ≤ 11)
    (hy0 : (0 : ℝ) < z.im) (hy1 : z.im < 1 / 2) :
    ‖riemannZeta (tailShiftedSReal z) * tailMollifierReal (tailShiftedSReal z) 2 - 1‖ < 1 := by
  have hzmem : z ∈ tailCellBounded := tailCellBounded_mem_of_regime z hx hle hy0 hy1
  have h2 : ‖riemannZeta (tailShiftedSReal z) - 2‖ ≤ r := hr z hzmem
  have hlt : ‖riemannZeta (tailShiftedSReal z) - 2‖ < 2 := lt_of_le_of_lt h2 hrl
  exact (tailK2_gap_iff_norm_sub_two z).mpr hlt

/-- Shifted zeta-minus-two is continuous on the cell (companion to
`tailZetaSubOneContinuousOnCell` read-only). -/
theorem tailZetaSubTwoContinuousOnCell :
    ContinuousOn (fun z => riemannZeta (tailShiftedSReal z) - 2) tailCellBounded :=
  tailZetaContinuousOnCell.sub continuousOn_const

/-- STRONGEST unconditional partial bound: `∃ B2` uniform for `‖ζ-2‖` on the
cell (compactness; numeral-free — the quantified gap is `B2 < 2`). -/
theorem exists_tailCell_zetaSubTwo :
    ∃ B2 : ℝ, ∀ z ∈ tailCellBounded,
      ‖riemannZeta (tailShiftedSReal z) - 2‖ ≤ B2 :=
  tailCellBounded_isCompact.exists_bound_of_continuousOn tailZetaSubTwoContinuousOnCell

/-- Shifted pole displacement imaginary part: `(s-1).im = s.im`. -/
theorem tailShiftedSubOne_im (z : ℂ) :
    (tailShiftedSReal z - 1).im = (tailShiftedSReal z).im := by
  simp

/-- Pole distance floor on the cell: `10 ≤ ‖s-1‖` (via `|Im| ≥ 10`). -/
theorem tailShiftedSubOne_norm_ge10_cell (z : ℂ) (hz : z ∈ tailCellBounded) :
    (10 : ℝ) ≤ ‖tailShiftedSReal z - 1‖ := by
  have him := tailShiftedSReal_im_abs_mem_cell z hz
  have hle : |((tailShiftedSReal z - 1).im)| ≤ ‖tailShiftedSReal z - 1‖ :=
    Complex.abs_im_le_norm _
  rw [tailShiftedSubOne_im] at hle
  linarith

/-- Unconditional EXPLICIT polar cap: `‖(s-1)⁻¹‖ ≤ 1/10` on the cell.
This is the `(s-1)⁻¹` piece of `riemannZeta_eq_inv_sub_add`
(`ζ = (s-1)⁻¹ + ζ₀`); the residual is an explicit bound on the entire part
`‖ζ₀‖` (or `‖ζ₀-2‖`) on the s-rect. -/
theorem tailInvSub_norm_le_tenth_cell (z : ℂ) (hz : z ∈ tailCellBounded) :
    ‖((tailShiftedSReal z - 1)⁻¹ : ℂ)‖ ≤ 1 / 10 := by
  have h10 : (10 : ℝ) ≤ ‖tailShiftedSReal z - 1‖ :=
    tailShiftedSubOne_norm_ge10_cell z hz
  rw [norm_inv]
  have hinv : (‖tailShiftedSReal z - 1‖)⁻¹ ≤ (10 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) h10
  calc (‖tailShiftedSReal z - 1‖)⁻¹ ≤ (10 : ℝ)⁻¹ := hinv
    _ = 1 / 10 := by norm_num

#print axioms TailStripZetaNearOne
#print axioms TailStripZetaSubTwo
#print axioms tailZetaSubTwo_of_nearOne_le
#print axioms tailZetaSubTwo_lt_two_of_nearOne_lt_one
#print axioms tailK2_gap_of_nearOne_lt_one
#print axioms tailK2_gap_of_subTwo_lt_two
#print axioms tailZetaSubTwoContinuousOnCell
#print axioms exists_tailCell_zetaSubTwo
#print axioms tailShiftedSubOne_im
#print axioms tailShiftedSubOne_norm_ge10_cell
#print axioms tailInvSub_norm_le_tenth_cell

/- Quantified remainder after this block (2026-09-05, Door-4 LAST tail route):
BANKED the full `‖ζ-2‖<2` bridge EXCEPT the single analytic numeral —
`tailZetaSubTwo_of_nearOne_le` (`d→d+1`), strict `<2` from `d<1`,
conditional closures `tailK2_gap_of_nearOne_lt_one` /
`tailK2_gap_of_subTwo_lt_two` (via read-only `tailK2_gap_iff_norm_sub_two`),
strongest unconditional partial `exists_tailCell_zetaSubTwo` (`∃ B2`,
numeral-free), and explicit polar cap `tailInvSub_norm_le_tenth_cell`
(`‖(s-1)⁻¹‖≤1/10`; Temp-checked `|s-1|≥10` from `|Im|≥10`).
QUANTIFIED GAP: `B*e+d<1` dead at K=2,3,4 (`2`, `7/3`, `3` all `>1`);
upper-only `B` can never close (`‖ζ-2‖≤B+2` vacuous).
SINGLE LEMMA TO CLOSE (exact next-agent task): prove ONE of
`TailStripZetaNearOne d` with explicit `d<1` (e.g. `d=9/10`: needs FE +
convexity / certified eta evaluation on `Re∈[0,1/2]`, `|Im|∈[10,11]`) or
`TailStripZetaSubTwo r` with explicit `r<2` (e.g. `r=19/10`), or explicit
`‖ζ₀‖`/`‖ζ₀-2‖` cap combining with `1/10` via `riemannZeta_eq_inv_sub_add`
to get `r<2`; then compose via `tailK2_gap_of_nearOne_lt_one` /
`tailK2_gap_of_subTwo_lt_two`. -/

/-!
## Door-3 remainder 5: real-axis segment certificate (tail lane, 2026-09-07, append-only)

Target (Authoritative Door-3 state, "Real-axis segment"): the central cover
deliberately excludes `z.im = 0`; the proved imaginary-axis results
(`z = I*y`) are a different slice. Required: a nonvanishing/lower-bound
certificate for real `z` with `-10 < z.re < 10`.

Slice audit (read-only, no import added — `import Mathlib` only here):
* `door3_boundary_real.lean` / `door3_real_center_bounds.lean`
  (`D3_real_zeta_norm_lower`, `D3_imag_axis_explicit_center_lower_le`,
  `zetaRealNonzeroInCritical_proved`) concern `z = I*y` (shifted `s` real in
  `(0,1)`) or the top edge — a different slice; no bound on `z.im = 0`.
* `door3_boundary_endpoints.lean` records totalized-product endpoint zeros at
  `±I/2` — boundary data, not a real-segment bound.
* `door3_imag_axis_strip.lean` gives a positive-width strip around the
  imaginary axis — again not the real segment.
* Real-`s`-axis xi values (`D3_explicit_center_lower_0`,
  `1/16 ≤ ‖xiShifted 0‖`) sit at the single point `z = 0` only.

Banked here (FULLY PROVED, no sorry/admit/axiom), in Mathlib-`riemannZeta` +
`tailShiftedSReal` coordinates, CALLING tail feeders `tailShiftedSReal_re`,
`tailShiftedSReal_im`, `tailShiftedSReal_continuous` and the T4 compact-bound
pattern (`tailCellBounded_isCompact` +
`IsCompact.exists_bound_of_continuousOn`, as in `exists_tailCell_zetaUpper`):
* explicit compact real sub-segment `door3RealSeg` (`-1 ≤ Re ≤ 1`, `Im = 0`;
  `door3RealSeg_in_open_strip` places it inside `-10 < Re < 10, Im = 0`);
* unconditional shifted image on the critical line (`door3RealShift_re/im`:
  `Re s = 1/2`, `Im s = Re z`), pole avoidance
  (`door3RealShift_ne_one_of_seg`, so `differentiableAt_riemannZeta` applies),
  continuity (`door3RealZetaContinuousOnSeg`);
* conditional certificate pair: uniform lower bound implies pointwise
  nonvanishing (`door3RealNonvan_of_lower`), and pointwise nonvanishing
  implies a uniform positive lower bound (`door3RealUniform_of_nonvan`, via
  the reciprocal bound capped by `IsCompact.exists_bound_of_continuousOn`).

The remaining analytic input is ONE explicit numeral: a `c > 0` with
`∀ z ∈ door3RealSeg, c ≤ ‖riemannZeta (tailShiftedSReal z)‖`
(critical-line zeta lower bound on `1/2 + I * [-1,1]`; the
`|Im| ∈ [10,11]` tail numerals do not transfer — disjoint height band).
-/

/-- Explicit compact real sub-segment of the Door-3 remainder-5 slice:
`-1 ≤ Re z ≤ 1`, `Im z = 0` (well inside `-10 < Re < 10`). -/
def door3RealSeg : Set ℂ :=
  Complex.re ⁻¹' Set.Icc (-1 : ℝ) 1 ∩ Complex.im ⁻¹' Set.Icc (0 : ℝ) 0

/-- Closed-rectangle membership for the real sub-segment. -/
theorem door3RealSeg_mem_of_reim (z : ℂ) (hre1 : (-1 : ℝ) ≤ z.re)
    (hre2 : z.re ≤ 1) (hlo : (0 : ℝ) ≤ z.im) (hhi : z.im ≤ 0) :
    z ∈ door3RealSeg := by
  simp only [door3RealSeg, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc]
  exact ⟨⟨hre1, hre2⟩, hlo, hhi⟩

/-- Open-interval points with `Im = 0` land in the closed sub-segment. -/
theorem door3RealSeg_mem_of_open (z : ℂ) (hx1 : (-1 : ℝ) < z.re)
    (hx2 : z.re < 1) (him : z.im = 0) :
    z ∈ door3RealSeg := by
  have hlo : (0 : ℝ) ≤ z.im := by simp [him]
  have hhi : z.im ≤ (0 : ℝ) := by simp [him]
  exact door3RealSeg_mem_of_reim z hx1.le hx2.le hlo hhi

/-- The origin lies in the real sub-segment (nonempty witness). -/
theorem door3RealSeg_zero_mem : (0 : ℂ) ∈ door3RealSeg := by
  apply door3RealSeg_mem_of_reim
  · norm_num [Complex.zero_re]
  · norm_num [Complex.zero_re]
  · norm_num [Complex.zero_im]
  · norm_num [Complex.zero_im]

/-- The real sub-segment is closed. -/
theorem door3RealSeg_isClosed : IsClosed door3RealSeg := by
  unfold door3RealSeg
  exact (IsClosed.preimage Complex.continuous_re isClosed_Icc).inter
    (IsClosed.preimage Complex.continuous_im isClosed_Icc)

/-- The real sub-segment lies in `closedBall 0 2`, hence is bounded. -/
theorem door3RealSeg_isBounded : Bornology.IsBounded door3RealSeg := by
  apply Metric.isBounded_closedBall.subset
  intro z hz
  obtain ⟨⟨h1, h2⟩, hlo, hhi⟩ := hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have him : z.im = 0 := le_antisymm hhi hlo
  have habs : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith, h2⟩
  have hre2 : z.re * z.re ≤ (1 : ℝ) * 1 := by
    have h := mul_le_mul habs habs (abs_nonneg _) (show (0 : ℝ) ≤ 1 by norm_num)
    rwa [abs_mul_abs_self] at h
  have him2 : z.im * z.im ≤ (0 : ℝ) := by
    rw [him]
    norm_num
  have hnorm : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hle : ‖z‖ ^ 2 ≤ (2 : ℝ) ^ 2 := by
    rw [hnorm]
    have hsum := add_le_add hre2 him2
    have h4 : (1 : ℝ) * 1 + 0 ≤ 2 ^ 2 := by norm_num
    exact le_trans hsum h4
  exact le_of_sq_le_sq hle (by norm_num)

/-- The real sub-segment is compact (Heine–Borel). -/
theorem door3RealSeg_isCompact : IsCompact door3RealSeg := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨door3RealSeg_isClosed, door3RealSeg_isBounded⟩

/-- The sub-segment sits inside the required open slice
`-10 < Re < 10, Im = 0`. -/
theorem door3RealSeg_in_open_strip (z : ℂ) (hz : z ∈ door3RealSeg) :
    (-10 : ℝ) < z.re ∧ z.re < 10 ∧ z.im = 0 := by
  obtain ⟨⟨h1, h2⟩, hlo, hhi⟩ := hz
  exact ⟨by linarith, by linarith, le_antisymm hhi hlo⟩

/-- Shifted real part on the real sub-segment: `Re s = 1/2`
(critical line; CALLS `tailShiftedSReal_re`). -/
theorem door3RealShift_re (z : ℂ) (hz : z ∈ door3RealSeg) :
    (tailShiftedSReal z).re = 1 / 2 := by
  obtain ⟨_, hlo, hhi⟩ := hz
  have him : z.im = 0 := le_antisymm hhi hlo
  rw [tailShiftedSReal_re, him]
  norm_num

/-- Shifted imaginary part on the real sub-segment: `Im s = Re z`
(CALLS `tailShiftedSReal_im`). -/
theorem door3RealShift_im (z : ℂ) :
    (tailShiftedSReal z).im = z.re :=
  tailShiftedSReal_im z

/-- Pole avoidance on the real sub-segment (so
`differentiableAt_riemannZeta` applies). -/
theorem door3RealShift_ne_one_of_seg (z : ℂ) (hz : z ∈ door3RealSeg) :
    tailShiftedSReal z ≠ 1 := by
  intro h
  have hre : (tailShiftedSReal z).re = (1 : ℂ).re := congrArg Complex.re h
  rw [door3RealShift_re z hz, Complex.one_re] at hre
  norm_num at hre

/-- Zeta pulled back through the shift is continuous on the real sub-segment
(CALLS `tailShiftedSReal_continuous`; same shape as
`tailZetaContinuousOnCell`). -/
theorem door3RealZetaContinuousOnSeg :
    ContinuousOn (fun z => riemannZeta (tailShiftedSReal z)) door3RealSeg := by
  intro x hx
  have hne : tailShiftedSReal x ≠ 1 := door3RealShift_ne_one_of_seg x hx
  have hdiff : DifferentiableAt ℂ riemannZeta (tailShiftedSReal x) :=
    differentiableAt_riemannZeta hne
  exact (hdiff.continuousAt.comp' tailShiftedSReal_continuous.continuousAt).continuousWithinAt

/-- Conditional certificate, lower bound to nonvanishing: an explicit uniform
`c > 0` with `c ≤ ‖ζ‖` on the sub-segment gives `ζ ≠ 0` at every
sub-segment point. -/
theorem door3RealNonvan_of_lower {c : ℝ}
    (h : ∀ z ∈ door3RealSeg, c ≤ ‖riemannZeta (tailShiftedSReal z)‖)
    (hc : 0 < c) (z : ℂ) (hz : z ∈ door3RealSeg) :
    riemannZeta (tailShiftedSReal z) ≠ 0 := by
  intro hzero
  have h1 := h z hz
  rw [hzero, norm_zero] at h1
  linarith

/-- Conditional certificate, nonvanishing to uniform bound: pointwise `ζ ≠ 0`
on the compact sub-segment upgrades to an explicit-uniform `∃ c > 0`
lower bound (reciprocal bound via `IsCompact.exists_bound_of_continuousOn`,
the same lemma as the T4 feeders `exists_tailCell_zetaUpper`). -/
theorem door3RealUniform_of_nonvan
    (h : ∀ z ∈ door3RealSeg, riemannZeta (tailShiftedSReal z) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ door3RealSeg,
      c ≤ ‖riemannZeta (tailShiftedSReal z)‖ := by
  have hcont := door3RealZetaContinuousOnSeg.inv₀ h
  obtain ⟨B, hB⟩ := door3RealSeg_isCompact.exists_bound_of_continuousOn hcont
  have hz0 : (0 : ℂ) ∈ door3RealSeg := door3RealSeg_zero_mem
  have hB0 := hB _ hz0
  rw [Pi.inv_apply] at hB0
  have hpos0 : 0 < ‖(riemannZeta (tailShiftedSReal 0))⁻¹‖ :=
    norm_pos_iff.mpr (inv_ne_zero (h _ hz0))
  have hBpos : 0 < B := lt_of_lt_of_le hpos0 hB0
  refine ⟨B⁻¹, inv_pos.mpr hBpos, fun z hz => ?_⟩
  have h1 := hB z hz
  rw [Pi.inv_apply] at h1
  have e1 : (1 : ℂ) = (riemannZeta (tailShiftedSReal z))⁻¹ *
      (riemannZeta (tailShiftedSReal z)) := by
    rw [inv_mul_cancel₀ (h z hz)]
  have e2 : ‖(1 : ℂ)‖ =
      ‖(riemannZeta (tailShiftedSReal z))⁻¹ * (riemannZeta (tailShiftedSReal z))‖ := by
    rw [e1]
  have e3 : ‖(riemannZeta (tailShiftedSReal z))⁻¹ * (riemannZeta (tailShiftedSReal z))‖ =
      ‖(riemannZeta (tailShiftedSReal z))⁻¹‖ * ‖riemannZeta (tailShiftedSReal z)‖ :=
    Complex.norm_mul _ _
  have e4 : (1 : ℝ) ≤
      ‖(riemannZeta (tailShiftedSReal z))⁻¹‖ * ‖riemannZeta (tailShiftedSReal z)‖ := by
    have n1 : (1 : ℝ) = ‖(1 : ℂ)‖ := (norm_one).symm
    rw [n1, e2, e3]
  have e5 : (1 : ℝ) ≤ B * ‖riemannZeta (tailShiftedSReal z)‖ := by
    have m1 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (riemannZeta (tailShiftedSReal z)))
    exact e4.trans m1
  have hmul : B⁻¹ * (B * ‖riemannZeta (tailShiftedSReal z)‖) =
      ‖riemannZeta (tailShiftedSReal z)‖ := by
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hBpos), one_mul]
  have hle : B⁻¹ * 1 ≤ B⁻¹ * (B * ‖riemannZeta (tailShiftedSReal z)‖) :=
    mul_le_mul_of_nonneg_left e5 (le_of_lt (inv_pos.mpr hBpos))
  rw [mul_one] at hle
  rw [hmul] at hle
  exact hle

#print axioms door3RealSeg_isCompact
#print axioms door3RealShift_re
#print axioms door3RealShift_im
#print axioms door3RealShift_ne_one_of_seg
#print axioms door3RealZetaContinuousOnSeg
#print axioms door3RealNonvan_of_lower
#print axioms door3RealUniform_of_nonvan

/- Quantified remainder after this block (2026-09-07, Door-3 remainder 5):
BANKED the full real-axis sub-segment bridge EXCEPT the single analytic
numeral — compact `door3RealSeg` (`-1 ≤ Re ≤ 1`, `Im = 0`,
`door3RealSeg_isCompact` via Heine–Borel), open-slice placement
(`door3RealSeg_in_open_strip`: inside `-10 < Re < 10, Im = 0`), critical-line
image (`door3RealShift_re/im`: `Re s = 1/2`), pole avoidance
(`door3RealShift_ne_one_of_seg`), continuity
(`door3RealZetaContinuousOnSeg`), and the conditional certificate pair
(`door3RealNonvan_of_lower`, `door3RealUniform_of_nonvan`).
SINGLE NUMERAL TO CLOSE (exact next-agent task): prove an explicit `c > 0`
with `∀ z ∈ door3RealSeg, c ≤ ‖riemannZeta (tailShiftedSReal z)‖`
(critical-line zeta lower bound on `1/2 + I * [-1,1]`, e.g. via a
kernel-checked zeta enclosure at height `|t| ≤ 1`), then compose via
`door3RealNonvan_of_lower`. Note `D3_real_zeta_norm_lower`
(`s/(1-s) ≤ ‖ζ(s)‖` on real `(0,1)`) does NOT transfer (different slice:
real `s` vs `s = 1/2 + I*t`). -/

/-!
## Door-3 remainder 5 final numeral: height-0 pointwise bound + next tile (2026-09-08, append-only)

Slice audit (read-only, no import added — `import Mathlib` only here):
* `door3_zeta_cutoff.lean:472` (`Door3ZetaCutoff.zeta_half_norm_lower_one`:
  `1 ≤ ‖riemannZeta (((1/2:ℝ)):ℂ)‖`, mirror of
  `door3_real_center_bounds.lean:44` `D3_real_zeta_norm_lower` at `s = 1/2`)
  is the ONE committed bound whose slice matches `door3RealSeg` at height
  `t = 0`: `tailShiftedSReal 0 = ((1/2:ℝ):ℂ)` (proved below as
  `door3RealShift_at_zero`), i.e. `z.im = 0, z.re = 0 ↦ 1/2 + I*0`.
* `D3_real_zeta_norm_lower` for `t ≠ 0`, `D3_imag_axis_*` (`z = I*y` slice),
  `door3_boundary_endpoints` (±I/2 zeros), `door3_imag_axis_strip`,
  `zeta_rigorous.lean` eta positivity — all different slices; NOT called.
* The analytic identity behind the `s = 1/2` instance is
  `TestAnalytic.lean:497` (`riemannZeta₀_eq_one_sub_mul_termTSum_on`,
  Mathlib-transitively-visible via `riemann_hypothesis`/`door3_*` but NOT
  in this file's `import Mathlib` closure). Per task direction (CALL, don't
  redo) it is isolated as the single explicit hypothesis `Door3HalfRealHyp`
  below — already proved unconditionally in committed files — and composed
  here with a proved slice rewrite plus `door3RealSeg_zero_mem`.

Banked here (FULLY PROVED, no sorry/admit/axiom, Mathlib-only given the
explicit hypothesis):
* `door3RealShift_at_zero` / `door3RealShift_re_at_zero` /
  `door3RealShift_im_at_zero` — unconditional slice verification at `0`;
* `door3RealPointwiseOne_at_zero_of_hyp` (`1 ≤ ‖ζ‖` at `tailShiftedSReal 0`),
  `door3RealC0` (`= 1`, `≤6` digits) + `door3RealC0_pos` +
  `door3RealC0_le_at_zero_of_hyp`, `door3RealNonvan_at_zero_of_hyp`
  (`ζ ≠ 0` at height 0), `door3RealSeg_pointwiseC0_of_hyp` (point on seg);
* next tile toward `(-10,10)`: `door3RealSegNext` (`1 ≤ Re ≤ 2`, `Im = 0`)
  with `mem_of_reim`, `witness` (`3/2`), `isClosed/isBounded/isCompact`,
  `in_open_strip`, `shift_re`, `ne_one`, `continuousOn`, and the
  `meet` point (`1` in both tiles) chaining `[-1,1]` to `[-1,2]`.
-/

/-- Slice verification: the shift at the origin is the real `1/2`. -/
theorem door3RealShift_at_zero :
    tailShiftedSReal 0 = (((1 / 2 : ℝ)) : ℂ) := by
  unfold tailShiftedSReal
  simp

/-- Slice verification: shifted real part at the origin. -/
theorem door3RealShift_re_at_zero :
    (tailShiftedSReal 0).re = 1 / 2 := by
  rw [door3RealShift_at_zero]
  simp

/-- Slice verification: shifted imaginary part at the origin. -/
theorem door3RealShift_im_at_zero :
    (tailShiftedSReal 0).im = 0 := by
  rw [door3RealShift_at_zero]
  simp

/-- Single explicit analytic input at `s = 1/2`, already proved in committed
files (`door3_zeta_cutoff.lean:472`, via `door3_real_center_bounds.lean:44`
and `TestAnalytic.lean:497`); isolated here as a hypothesis (CALL, don't
redo). -/
def Door3HalfRealHyp : Prop :=
  (1 : ℝ) ≤ ‖riemannZeta (((1 / 2 : ℝ)) : ℂ)‖

/-- Pointwise numeral at height 0: `1 ≤ ‖ζ‖` at `tailShiftedSReal 0`. -/
theorem door3RealPointwiseOne_at_zero_of_hyp (h : Door3HalfRealHyp) :
    (1 : ℝ) ≤ ‖riemannZeta (tailShiftedSReal 0)‖ := by
  rw [door3RealShift_at_zero]
  unfold Door3HalfRealHyp at h
  exact h

/-- Explicit `c > 0` numeral at one height (`≤6` digits). -/
def door3RealC0 : ℝ := 1

/-- Positivity of the explicit numeral. -/
theorem door3RealC0_pos : 0 < door3RealC0 := by
  unfold door3RealC0
  norm_num

/-- The explicit numeral bounds zeta at height 0. -/
theorem door3RealC0_le_at_zero_of_hyp (h : Door3HalfRealHyp) :
    door3RealC0 ≤ ‖riemannZeta (tailShiftedSReal 0)‖ := by
  unfold door3RealC0
  exact door3RealPointwiseOne_at_zero_of_hyp h

/-- Pointwise nonvanishing at height 0 from the numeral. -/
theorem door3RealNonvan_at_zero_of_hyp (h : Door3HalfRealHyp) :
    riemannZeta (tailShiftedSReal 0) ≠ 0 := by
  have h1 := door3RealPointwiseOne_at_zero_of_hyp h
  intro hzero
  rw [hzero, norm_zero] at h1
  norm_num at h1

/-- The height-0 point lies on the segment with the numeral bound. -/
theorem door3RealSeg_pointwiseC0_of_hyp (h : Door3HalfRealHyp) :
    door3RealC0 ≤ ‖riemannZeta (tailShiftedSReal (0 : ℂ))‖ ∧
      (0 : ℂ) ∈ door3RealSeg := by
  exact ⟨door3RealC0_le_at_zero_of_hyp h, door3RealSeg_zero_mem⟩

/-- Next compact tile toward `(-10,10)`: `1 ≤ Re z ≤ 2`, `Im z = 0`. -/
def door3RealSegNext : Set ℂ :=
  Complex.re ⁻¹' Set.Icc (1 : ℝ) 2 ∩ Complex.im ⁻¹' Set.Icc (0 : ℝ) 0

/-- Closed-rectangle membership for the next tile. -/
theorem door3RealSegNext_mem_of_reim (z : ℂ) (hre1 : (1 : ℝ) ≤ z.re)
    (hre2 : z.re ≤ 2) (hlo : (0 : ℝ) ≤ z.im) (hhi : z.im ≤ 0) :
    z ∈ door3RealSegNext := by
  simp only [door3RealSegNext, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc]
  exact ⟨⟨hre1, hre2⟩, hlo, hhi⟩

/-- Witness: `3/2` lies in the next tile. -/
theorem door3RealSegNext_witness : ((((3 / 2 : ℝ))) : ℂ) ∈ door3RealSegNext := by
  simp only [door3RealSegNext, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num

/-- The next tile is closed. -/
theorem door3RealSegNext_isClosed : IsClosed door3RealSegNext := by
  unfold door3RealSegNext
  exact (IsClosed.preimage Complex.continuous_re isClosed_Icc).inter
    (IsClosed.preimage Complex.continuous_im isClosed_Icc)

/-- The next tile lies in `closedBall 0 3`, hence is bounded. -/
theorem door3RealSegNext_isBounded : Bornology.IsBounded door3RealSegNext := by
  apply Metric.isBounded_closedBall.subset
  intro z hz
  obtain ⟨⟨h1, h2⟩, hlo, hhi⟩ := hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have him : z.im = 0 := le_antisymm hhi hlo
  have habs : |z.re| ≤ 2 := by
    rw [abs_le]
    constructor
    · linarith
    · exact h2
  have hre2 : z.re * z.re ≤ (2 : ℝ) * 2 := by
    have h := mul_le_mul habs habs (abs_nonneg _) (show (0 : ℝ) ≤ 2 by norm_num)
    rwa [abs_mul_abs_self] at h
  have him2 : z.im * z.im ≤ (0 : ℝ) := by
    rw [him]
    norm_num
  have hnorm : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hle : ‖z‖ ^ 2 ≤ (3 : ℝ) ^ 2 := by
    rw [hnorm]
    have hsum := add_le_add hre2 him2
    have h9 : (2 : ℝ) * 2 + 0 ≤ 3 ^ 2 := by norm_num
    exact le_trans hsum h9
  exact le_of_sq_le_sq hle (by norm_num)

/-- The next tile is compact (Heine–Borel). -/
theorem door3RealSegNext_isCompact : IsCompact door3RealSegNext := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨door3RealSegNext_isClosed, door3RealSegNext_isBounded⟩

/-- The next tile sits inside the required open slice `-10 < Re < 10`. -/
theorem door3RealSegNext_in_open_strip (z : ℂ) (hz : z ∈ door3RealSegNext) :
    (-10 : ℝ) < z.re ∧ z.re < 10 ∧ z.im = 0 := by
  obtain ⟨⟨h1, h2⟩, hlo, hhi⟩ := hz
  exact ⟨by linarith, by linarith, le_antisymm hhi hlo⟩

/-- Shifted real part on the next tile: `Re s = 1/2` (critical line). -/
theorem door3RealNextShift_re (z : ℂ) (hz : z ∈ door3RealSegNext) :
    (tailShiftedSReal z).re = 1 / 2 := by
  obtain ⟨_, hlo, hhi⟩ := hz
  have him : z.im = 0 := le_antisymm hhi hlo
  rw [tailShiftedSReal_re, him]
  norm_num

/-- Pole avoidance on the next tile. -/
theorem door3RealNextShift_ne_one_of_seg (z : ℂ) (hz : z ∈ door3RealSegNext) :
    tailShiftedSReal z ≠ 1 := by
  intro hcon
  have hre : (tailShiftedSReal z).re = (1 : ℂ).re := congrArg Complex.re hcon
  rw [door3RealNextShift_re z hz, Complex.one_re] at hre
  norm_num at hre

/-- Zeta pulled back through the shift is continuous on the next tile. -/
theorem door3RealNextZetaContinuousOnSeg :
    ContinuousOn (fun z => riemannZeta (tailShiftedSReal z)) door3RealSegNext := by
  intro x hx
  have hne : tailShiftedSReal x ≠ 1 := door3RealNextShift_ne_one_of_seg x hx
  have hdiff : DifferentiableAt ℂ riemannZeta (tailShiftedSReal x) :=
    differentiableAt_riemannZeta hne
  exact (hdiff.continuousAt.comp' tailShiftedSReal_continuous.continuousAt).continuousWithinAt

/-- Chaining point: `1` lies in both tiles, so `[-1,1] ∪ [1,2] = [-1,2]`. -/
theorem door3RealSeg_next_meet :
    ((((1 : ℝ))) : ℂ) ∈ door3RealSeg ∧
      ((((1 : ℝ))) : ℂ) ∈ door3RealSegNext := by
  simp only [door3RealSeg, door3RealSegNext, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_Icc, Complex.ofReal_re, Complex.ofReal_im]
  norm_num

#print axioms door3RealShift_at_zero
#print axioms door3RealShift_re_at_zero
#print axioms door3RealShift_im_at_zero
#print axioms door3RealPointwiseOne_at_zero_of_hyp
#print axioms door3RealC0_pos
#print axioms door3RealC0_le_at_zero_of_hyp
#print axioms door3RealNonvan_at_zero_of_hyp
#print axioms door3RealSeg_pointwiseC0_of_hyp
#print axioms door3RealSegNext_isCompact
#print axioms door3RealNextShift_re
#print axioms door3RealNextShift_ne_one_of_seg
#print axioms door3RealNextZetaContinuousOnSeg
#print axioms door3RealSeg_next_meet

/- Quantified remainder after this block (2026-09-08, Door-3 remainder 5):
BANKED the tightest proved step short of the uniform numeral: an explicit
`c = door3RealC0 = 1` pointwise lower bound at height `t = 0`
(`door3RealPointwiseOne_at_zero_of_hyp` / `door3RealC0_le_at_zero_of_hyp`,
conditional on the single committed `s = 1/2` instance `Door3HalfRealHyp`
=`Door3ZetaCutoff.zeta_half_norm_lower_one`, slice-verified by
`door3RealShift_at_zero/re/im_at_zero`), composed to pointwise nonvanishing
(`door3RealNonvan_at_zero_of_hyp`) on `door3RealSeg` at `0`
(`door3RealSeg_pointwiseC0_of_hyp`), plus one more tile toward `(-10,10)`:
compact `door3RealSegNext` (`1 ≤ Re ≤ 2`, `Im = 0`, chained by
`door3RealSeg_next_meet`) with the same critical-line pattern
(`door3RealNextShift_re/ne_one/continuousOn`).
RESIDUAL: discharge `Door3HalfRealHyp` inside this file's `import Mathlib`
closure (needs `TestAnalytic.lean:497` continuation at `s = 1/2`, absent from
Mathlib alone), then lift the height-0 `c = 1` to uniform `c > 0` over
`door3RealSeg` (`1/2 + I*[-1,1]`, needs height `|t| ≤ 1` enclosure, not the
`|Im| ∈ [10,11]` tail numerals) via `door3RealNonvan_of_lower`, and tile
`[-1,2]` onward toward `(-10,10)` by repeating the `door3RealSegNext`
pattern. -/

/-!
## Door-3 remainder 5: discharge of `Door3HalfRealHyp` up to one analytic lemma (2026-09-08, append-only)

Slice audit (read-only, no import added — `import Mathlib` only here):
* `door3_zeta_cutoff.lean:472` (`zeta_half_norm_lower_one`) and
  `door3_real_center_bounds.lean:44` (`D3_real_zeta_norm_lower`) prove
  `1 ≤ ‖ζ(1/2)‖` via `TestAnalytic.lean:497`
  (`riemannZeta₀_eq_one_sub_mul_termTSum_on`), which sits outside this
  file's `import Mathlib` closure — NOT called (calling it needs a
  top-of-file import edit, outside tail ownership; per task direction a
  prior agent succeeded by reproving in-file, which is what is done here).
* Reproved here from Mathlib-visible lemmas only
  (`riemannZeta_eq_inv_sub_add`,
  `zeta_eq_tsum_one_div_nat_add_one_cpow`,
  `ZetaAsymptotics.zeta_limit_aux1`, `ZetaAsymptotics.term_nonneg`,
  `differentiable_riemannZeta₀`,
  `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`): the
  Euler–Maclaurin identity for `1 < s` (`door3EM_of_gt`), left-side
  real-analyticity on `(0,∞)` (`door3EM_left_analytic`), and the identity
  theorem packaging (`door3EM_eqOn_of_rightAnalytic`).

Banked here (FULLY PROVED, no sorry/admit/axiom): everything EXCEPT the
real-analyticity of the explicit RHS `g(s) = 1 - s * termTSum s` on
`(0,∞)`, isolated as the single hypothesis `Door3EMRightAnalytic`
(proved from Mathlib alone in `TestAnalytic.lean:455` via the complex
extension `termTSumC` — the one lemma left to mirror). Given it: the
identity at `s = 1/2` (`door3HalfIdentity_of_EM`), `Re ≤ 1`
(`door3HalfRe_le_one_of_EM`), `1 ≤ ‖ζ(1/2)‖`
(`door3HalfNorm_ge_one_of_EM`), discharge of the old `Door3HalfRealHyp`
(`door3HalfRealHyp_of_EM`), and the height-0 lift
(`door3RealPointwiseOne_at_zero_of_EM`, `door3RealNonvan_at_zero_of_EM`,
`door3RealSeg_pointwiseC0_of_EM`), composable with committed
`door3RealNonvan_of_lower`.
-/

open scoped Topology

/-- Single remaining analytic input: real-analyticity of the explicit
Euler–Maclaurin RHS on `(0,∞)` (proved in `TestAnalytic.lean:455`). -/
def Door3EMRightAnalytic : Prop :=
  AnalyticOnNhd ℝ (fun s : ℝ => 1 - s * ZetaAsymptotics.termTSum s) (Set.Ioi 0)

/-- Real-part formula for `riemannZeta₀` at real `s ≠ 1`
(mirror of `TestAnalytic.lean:465`, Mathlib-only). -/
theorem door3RealZeta0_re_of_real (s : ℝ) (hs : s ≠ 1) :
    (riemannZeta₀ (s : ℂ)).re = (riemannZeta (s : ℂ)).re - 1 / (s - 1) := by
  unfold riemannZeta₀
  rw [if_neg (by exact_mod_cast hs : (s : ℂ) ≠ 1)]
  simp only [Complex.sub_re, Complex.inv_re, Complex.ofReal_re, Complex.one_re]
  rw [show (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) from (Complex.ofReal_sub s 1).symm]
  simp only [Complex.normSq_ofReal]
  field_simp [sub_ne_zero.mpr hs]

/-- Euler–Maclaurin identity for `1 < s` (mirror of
`TestAnalytic.lean:474`, Mathlib-only). -/
theorem door3EM_of_gt (s : ℝ) (_hs0 : 0 < s) (hs1 : 1 < s) :
    (riemannZeta₀ (s : ℂ)).re = 1 - s * ZetaAsymptotics.termTSum s := by
  have hsne : s ≠ 1 := by linarith
  rw [door3RealZeta0_re_of_real s hsne]
  suffices h : (riemannZeta (s : ℂ)).re = ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s from by
    rw [h, ZetaAsymptotics.zeta_limit_aux1 hs1]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow
    (by simp [Complex.ofReal_re]; linarith : 1 < Complex.re (s : ℂ))]
  have hterm : ∀ n : ℕ,
      (1 : ℂ) / (↑n + 1 : ℂ) ^ (s : ℂ) =
      ((↑((1 : ℝ) / (↑(n + 1 : ℕ) : ℝ) ^ s) : ℂ)) := by
    intro n
    have hp : 0 ≤ (↑n + 1 : ℝ) := by positivity
    push_cast
    rw [Complex.ofReal_cpow hp]
    norm_cast
  rw [show (∑' n : ℕ, (1 : ℂ) / (↑n + 1 : ℂ) ^ (s : ℂ)) =
      (∑' n : ℕ, ((↑((1 : ℝ) / (↑(n + 1 : ℕ) : ℝ) ^ s) : ℂ))) from tsum_congr hterm]
  rw [(_root_.Complex.ofReal_tsum
    (fun n => (1 : ℝ) / (↑(n + 1 : ℕ) : ℝ) ^ s : ℕ → ℝ)).symm]
  simp [Complex.ofReal_re]

/-- Left side is real-analytic on `(0,∞)`
(mirror of `TestAnalytic.lean:502`). -/
theorem door3EM_left_analytic :
    AnalyticOnNhd ℝ (fun s : ℝ => (riemannZeta₀ (s : ℂ)).re) (Set.Ioi 0) := by
  intro s hs
  exact AnalyticAt.re_ofReal (Differentiable.analyticAt differentiable_riemannZeta₀ (s : ℂ))

/-- Identity-theorem packaging: given right-side analyticity, both sides
agree on `(0,∞)` (mirror of `TestAnalytic.lean:514`). -/
theorem door3EM_eqOn_of_rightAnalytic (h : Door3EMRightAnalytic) :
    Set.EqOn (fun s : ℝ => (riemannZeta₀ (s : ℂ)).re)
      (fun s : ℝ => 1 - s * ZetaAsymptotics.termTSum s) (Set.Ioi 0) := by
  unfold Door3EMRightAnalytic at h
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq door3EM_left_analytic h
    isPreconnected_Ioi (by norm_num : (2 : ℝ) ∈ Set.Ioi 0) ?_
  have hAgree : ∀ z ∈ Set.Ioo (1 : ℝ) 3,
      (riemannZeta₀ (z : ℂ)).re = 1 - z * ZetaAsymptotics.termTSum z := by
    intro z hz
    exact door3EM_of_gt z (by linarith [hz.1] : 0 < z) hz.1
  have hmem : Set.Ioo (1 : ℝ) 3 ∈ 𝓝[≠] (2 : ℝ) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Ioo (1 : ℝ) 3, isOpen_Ioo.mem_nhds (by norm_num), ?_⟩
    intro x hx
    exact hx.1
  have hsubset : Set.Ioo (1 : ℝ) 3 ⊆
      {z : ℝ | (riemannZeta₀ (z : ℂ)).re = 1 - z * ZetaAsymptotics.termTSum z} := by
    intro z hz
    exact hAgree z hz
  have hfg' : ∀ᶠ (z : ℝ) in 𝓝[≠] (2 : ℝ),
      (riemannZeta₀ (z : ℂ)).re = 1 - z * ZetaAsymptotics.termTSum z :=
    Filter.mem_of_superset hmem hsubset
  exact Filter.Eventually.frequently hfg'

/-- The Euler–Maclaurin identity at `s = 1/2`, modulo the one analytic lemma. -/
theorem door3HalfIdentity_of_EM (h : Door3EMRightAnalytic) :
    (riemannZeta₀ ((((1 / 2 : ℝ))) : ℂ)).re =
      1 - (1 / 2 : ℝ) * ZetaAsymptotics.termTSum (1 / 2 : ℝ) := by
  have hEq := door3EM_eqOn_of_rightAnalytic h
  have hmem : (1 / 2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  exact hEq hmem

/-- Real-part upper bound at `s = 1/2`, modulo the one analytic lemma. -/
theorem door3HalfRe_le_one_of_EM (h : Door3EMRightAnalytic) :
    (riemannZeta₀ ((((1 / 2 : ℝ))) : ℂ)).re ≤ 1 := by
  have h0 := door3HalfIdentity_of_EM h
  have ht : (0 : ℝ) ≤ ZetaAsymptotics.termTSum (1 / 2 : ℝ) :=
    tsum_nonneg (fun n => ZetaAsymptotics.term_nonneg (n + 1) (1 / 2 : ℝ))
  have hprod : (0 : ℝ) ≤ (1 / 2 : ℝ) * ZetaAsymptotics.termTSum (1 / 2 : ℝ) :=
    mul_nonneg (by norm_num) ht
  linarith

/-- Norm lower bound at `s = 1/2` (mirror of `door3_zeta_cutoff.lean:472`),
modulo the one analytic lemma. -/
theorem door3HalfNorm_ge_one_of_EM (h : Door3EMRightAnalytic) :
    (1 : ℝ) ≤ ‖riemannZeta ((((1 / 2 : ℝ))) : ℂ)‖ := by
  have h12 : (1 / 2 : ℝ) ≠ 1 := by norm_num
  have hsne : ((((1 / 2 : ℝ))) : ℂ) ≠ 1 := by exact_mod_cast h12
  have hz := riemannZeta_eq_inv_sub_add (s := ((((1 / 2 : ℝ))) : ℂ)) hsne
  have hz0 := door3HalfRe_le_one_of_EM h
  have heq : ((((1 / 2 : ℝ))) : ℂ) - 1 = (((-1 / 2 : ℝ)) : ℂ) := by
    push_cast
    ring
  have hinv : ((((((1 / 2 : ℝ))) : ℂ) - 1)⁻¹).re = (-2 : ℝ) := by
    rw [heq, ← Complex.ofReal_inv, Complex.ofReal_re]
    norm_num
  have hre : (riemannZeta ((((1 / 2 : ℝ))) : ℂ)).re ≤ -1 := by
    rw [hz, Complex.add_re, hinv]
    linarith
  have hneg : (riemannZeta ((((1 / 2 : ℝ))) : ℂ)).re < 0 := by linarith
  calc (1 : ℝ) ≤ |(riemannZeta ((((1 / 2 : ℝ))) : ℂ)).re| := by
        rw [abs_of_neg hneg]
        linarith
    _ ≤ ‖riemannZeta ((((1 / 2 : ℝ))) : ℂ)‖ := Complex.abs_re_le_norm _

/-- Discharge of the committed hypothesis `Door3HalfRealHyp`
(modulo the one analytic lemma). -/
theorem door3HalfRealHyp_of_EM (h : Door3EMRightAnalytic) : Door3HalfRealHyp := by
  unfold Door3HalfRealHyp
  exact door3HalfNorm_ge_one_of_EM h

/-- Height-0 numeral from the EM bridge. -/
theorem door3RealPointwiseOne_at_zero_of_EM (h : Door3EMRightAnalytic) :
    (1 : ℝ) ≤ ‖riemannZeta (tailShiftedSReal 0)‖ := by
  rw [door3RealShift_at_zero]
  exact door3HalfNorm_ge_one_of_EM h

/-- Height-0 nonvanishing from the EM bridge. -/
theorem door3RealNonvan_at_zero_of_EM (h : Door3EMRightAnalytic) :
    riemannZeta (tailShiftedSReal 0) ≠ 0 := by
  have h1 := door3RealPointwiseOne_at_zero_of_EM h
  intro hzero
  rw [hzero, norm_zero] at h1
  norm_num at h1

/-- The height-0 point lies on the segment with the numeral bound. -/
theorem door3RealSeg_pointwiseC0_of_EM (h : Door3EMRightAnalytic) :
    door3RealC0 ≤ ‖riemannZeta (tailShiftedSReal (0 : ℂ))‖ ∧
      (0 : ℂ) ∈ door3RealSeg := by
  refine ⟨?_, door3RealSeg_zero_mem⟩
  unfold door3RealC0
  exact door3RealPointwiseOne_at_zero_of_EM h

#print axioms door3RealZeta0_re_of_real
#print axioms door3EM_of_gt
#print axioms door3EM_left_analytic
#print axioms door3EM_eqOn_of_rightAnalytic
#print axioms door3HalfIdentity_of_EM
#print axioms door3HalfRe_le_one_of_EM
#print axioms door3HalfNorm_ge_one_of_EM
#print axioms door3HalfRealHyp_of_EM
#print axioms door3RealPointwiseOne_at_zero_of_EM
#print axioms door3RealNonvan_at_zero_of_EM
#print axioms door3RealSeg_pointwiseC0_of_EM

/- Quantified remainder after this block (2026-09-08, Door-3 remainder 5):
BANKED the full height-0 discharge modulo ONE explicitly isolated analytic
lemma: `Door3EMRightAnalytic` (real-analyticity of
`1 - s * termTSum s` on `(0,∞)`, Mathlib-proved in
`TestAnalytic.lean:455` via `termTSumC`), plus unconditional in-file
`door3RealZeta0_re_of_real`, `door3EM_of_gt` (EM identity for `1 < s`),
`door3EM_left_analytic`, and conditional `door3EM_eqOn_of_rightAnalytic`,
`door3HalfIdentity_of_EM`, `door3HalfRe_le_one_of_EM`,
`door3HalfNorm_ge_one_of_EM` (`1 ≤ ‖ζ(1/2)‖`),
`door3HalfRealHyp_of_EM` (discharges committed `Door3HalfRealHyp`),
`door3RealPointwiseOne_at_zero_of_EM`, `door3RealNonvan_at_zero_of_EM`,
`door3RealSeg_pointwiseC0_of_EM` (height-0 `c = 1` on `door3RealSeg`).
RESIDUAL (exact next-agent task): mirror `TestAnalytic.lean:38-455`
(`termC`/`termTSumC` analyticity on `{z | 0 < z.re}` + agreement
`termTSumC_eq_termTSum`) in this tail to prove `Door3EMRightAnalytic`
unconditionally (Mathlib-only, no import edit), making
`door3HalfNorm_ge_one_of_EM` unconditional; then lift the height-0
`c = 1` to uniform `c > 0` over `door3RealSeg` (`1/2 + I*[-1,1]`, needs
height `|t| ≤ 1` enclosure) via committed `door3RealNonvan_of_lower`,
and tile `[-1,2]` onward toward `(-10,10)` by repeating the
`door3RealSegNext` pattern. -/

/-! ## Door-3 remainder 5b: EM right-analytic engine, prefix A (2026-09-08, append-only)
Mirror of `TestAnalytic.lean:24-172` with `door3`-prefixed names, Mathlib-only,
no import edit. No `simpa` (hang-guard); explicit binders; numerals ≤ 6 digits. -/

open Real MeasureTheory Filter

/-- Complex extension of `ZetaAsymptotics.term` (mirror of `termC`). -/
noncomputable def door3termC (n : ℕ) (s : ℂ) : ℂ :=
  ∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1),
    ((x - (n : ℝ)) : ℂ) * (x : ℂ) ^ (-(s + 1))

/-- Derivative of `door3termC n` in `s` (mirror of `termC'`). -/
noncomputable def door3termC' (n : ℕ) (s : ℂ) : ℂ :=
  ∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1),
    -((x - (n : ℝ)) : ℂ) * (x : ℂ) ^ (-(s + 1)) * Complex.log (x : ℂ)

/-- Complex extension of `ZetaAsymptotics.termTSum` (mirror of `termTSumC`). -/
noncomputable def door3termTSumC (s : ℂ) : ℂ :=
  ∑' n : ℕ, door3termC (n + 1) s

/-- `door3termC n` agrees with `ZetaAsymptotics.term n` on the real axis
(mirror of `TestAnalytic.lean:39`). -/
theorem door3termC_eq_term {n : ℕ} (_hn : 0 < n) {s : ℝ} :
    door3termC n (s : ℂ) = (ZetaAsymptotics.term n s : ℂ) := by
  unfold door3termC ZetaAsymptotics.term
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only []
  have hx0 : 0 ≤ x := by
    rw [Set.uIcc_of_le (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)] at hx
    exact le_trans (by exact_mod_cast (Nat.zero_le n)) hx.1
  rw [show -((s : ℂ) + 1) = ((-(s + 1) : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_cpow hx0 (-(s + 1))]
  rw [Real.rpow_neg hx0]
  norm_cast

/-- `door3termTSumC` agrees with `ZetaAsymptotics.termTSum` on `0 < s`
(mirror of `TestAnalytic.lean:55`). -/
theorem door3termTSumC_eq_termTSum {s : ℝ} (_hs : 0 < s) :
    door3termTSumC (s : ℂ) = (ZetaAsymptotics.termTSum s : ℂ) := by
  unfold door3termTSumC ZetaAsymptotics.termTSum
  rw [tsum_congr (fun n => door3termC_eq_term (Nat.succ_pos n))]
  exact (Complex.ofReal_tsum (fun n : ℕ => ZetaAsymptotics.term (n + 1) s)).symm

/-- Integrand of `door3termC` is differentiable in `s`
(mirror of `TestAnalytic.lean:62`). -/
theorem door3hasDerivAt_termC_integrand (n : ℕ) {s : ℂ} {x : ℝ} (hx : 1 ≤ x) :
    HasDerivAt (fun t : ℂ => ((x - (n : ℝ)) : ℂ) * (x : ℂ) ^ (-(t + 1)))
      (-((x - (n : ℝ)) : ℂ) * (x : ℂ) ^ (-(s + 1)) * Complex.log (x : ℂ)) s := by
  have hxne : (x : ℂ) ≠ 0 := by
    exact ofReal_ne_zero.mpr (by linarith)
  have hlin : HasDerivAt (fun t : ℂ => -(t + 1)) (-1) s := by
    exact HasDerivAt.neg (HasDerivAt.add_const (1 : ℂ) (hasDerivAt_id s))
  have hpow : HasDerivAt (fun t : ℂ => (x : ℂ) ^ (-(t + 1)))
      ((x : ℂ) ^ (-(s + 1)) * Complex.log (x : ℂ) * (-1)) s := by
    exact HasDerivAt.const_cpow hlin (Or.inl hxne)
  have hscalar : HasDerivAt (fun t : ℂ => ((x - (n : ℝ)) : ℂ) * (x : ℂ) ^ (-(t + 1)))
      (((x - (n : ℝ)) : ℂ) * ((x : ℂ) ^ (-(s + 1)) * Complex.log (x : ℂ) * (-1))) s := by
    exact HasDerivAt.const_mul ((x - (n : ℝ)) : ℂ) hpow
  exact hscalar.congr_deriv (by ring)

/-- `x ↦ (x : ℂ)` shifted is continuous (mirror of `TestAnalytic.lean:78`). -/
theorem door3continuousAt_ofReal_sub (n : ℕ) (x : ℝ) :
    ContinuousAt (fun x : ℝ => ((x - (n + 1 : ℝ)) : ℂ)) x := by
  have h1 : ContinuousAt (fun x : ℝ => (x : ℂ)) x := Complex.continuous_ofReal.continuousAt
  have h2 : ContinuousAt (fun x : ℝ => ((n + 1 : ℝ) : ℂ)) x := continuousAt_const
  convert h1.sub h2 using 1
  ext y
  simp

/-- `x ↦ (x : ℂ) ^ c` is continuous at positive `x`
(mirror of `TestAnalytic.lean:87`, no `simpa`). -/
theorem door3continuousAt_cpow_ofReal (c : ℂ) {x : ℝ} (hxpos : 0 < x) :
    ContinuousAt (fun x : ℝ => (x : ℂ) ^ c) x := by
  have hre : 0 < ((x : ℂ)).re := by
    rw [Complex.ofReal_re]
    exact hxpos
  have hmem : (x : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl hre
  have hd0 : HasDerivAt (fun y : ℂ => y ^ c) (c * (x : ℂ) ^ (c - 1) * 1) (x : ℂ) :=
    HasDerivAt.cpow_const (hasDerivAt_id (x : ℂ)) hmem
  have hd : HasDerivAt (fun y : ℂ => y ^ c) (c * (x : ℂ) ^ (c - 1)) (x : ℂ) :=
    hd0.congr_deriv (by ring)
  exact hd.continuousAt.comp Complex.continuous_ofReal.continuousAt

/-- `x ↦ Complex.log (x : ℂ)` is continuous at positive `x`
(mirror of `TestAnalytic.lean:95`, no `simpa`). -/
theorem door3continuousAt_log_ofReal {x : ℝ} (hxpos : 0 < x) :
    ContinuousAt (fun x : ℝ => Complex.log (x : ℂ)) x := by
  have hre : 0 < ((x : ℂ)).re := by
    rw [Complex.ofReal_re]
    exact hxpos
  have hmem : (x : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl hre
  have hdlog : HasDerivAt Complex.log (x : ℂ)⁻¹ (x : ℂ) :=
    Complex.hasDerivAt_log hmem
  exact hdlog.continuousAt.comp Complex.continuous_ofReal.continuousAt

/-- Integrand of `door3termC` is continuous on `[n+1, n+2]`
(mirror of `TestAnalytic.lean:104`). -/
theorem door3continuousOn_termC_integrand (n : ℕ) (t : ℂ) :
    ContinuousOn (fun x : ℝ => ((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(t + 1)))
      (Set.Icc (n + 1 : ℝ) ((n + 1 : ℝ) + 1)) := by
  refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
  have hxpos : 0 < x := by linarith [hx.1]
  exact ContinuousAt.mul (door3continuousAt_ofReal_sub n x)
    (door3continuousAt_cpow_ofReal (-(t + 1)) hxpos)

/-- Derivative integrand of `door3termC` is continuous on `[n+1, n+2]`
(mirror of `TestAnalytic.lean:112`). -/
theorem door3continuousOn_termC'_integrand (n : ℕ) (t : ℂ) :
    ContinuousOn (fun x : ℝ =>
      -((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(t + 1)) * Complex.log (x : ℂ))
      (Set.Icc (n + 1 : ℝ) ((n + 1 : ℝ) + 1)) := by
  refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
  have hxpos : 0 < x := by linarith [hx.1]
  exact ContinuousAt.mul
    (ContinuousAt.mul (door3continuousAt_ofReal_sub n x).neg
      (door3continuousAt_cpow_ofReal (-(t + 1)) hxpos))
    (door3continuousAt_log_ofReal hxpos)

/-- Norm of the derivative integrand is bounded
(mirror of `TestAnalytic.lean:124`). -/
theorem door3norm_termC'_integrand_le (n : ℕ) {s : ℂ} (hs : 0 < s.re) {x : ℝ}
    (hx1 : (n + 1 : ℝ) ≤ x) :
    ‖-((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(s + 1)) * Complex.log (x : ℂ)‖ ≤
      (x - (n + 1 : ℝ)) * x ^ (-(1 : ℝ)) * Real.log x := by
  have hxpos : 0 < x := by
    have hnp : 0 < (n + 1 : ℝ) := by positivity
    linarith
  have hxge1 : 1 ≤ x := by linarith
  have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) := (Complex.ofReal_log hxpos.le).symm
  rw [hlog]
  have h1 : ‖-((x - (n + 1 : ℝ)) : ℂ)‖ = x - (n + 1 : ℝ) := by
    rw [norm_neg]; norm_cast; exact abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hx1))
  have h2 : ‖(x : ℂ) ^ (-(s + 1))‖ = x ^ (-(s.re + 1)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos (-(s + 1))]
    rw [show (-(s + 1)).re = -(s.re + 1) by simp]
  have h3 : ‖(Real.log x : ℂ)‖ = Real.log x := by
    calc
      ‖(Real.log x : ℂ)‖ = |Real.log x| := RCLike.norm_ofReal (Real.log x)
      _ = Real.log x := abs_of_nonneg (Real.log_nonneg hxge1)
  rw [norm_mul, norm_mul]
  rw [h1, h2, h3]
  have hpow : x ^ (-(s.re + 1)) ≤ x ^ (-(1 : ℝ)) := by
    exact rpow_le_rpow_of_exponent_le hxge1 (by linarith [hs])
  have hnonneg : 0 ≤ (x - (n + 1 : ℝ)) * Real.log x :=
    mul_nonneg (sub_nonneg.mpr hx1) (Real.log_nonneg hxge1)
  calc
    (x - (n + 1 : ℝ)) * x ^ (-(s.re + 1)) * Real.log x
        = (x - (n + 1 : ℝ)) * Real.log x * x ^ (-(s.re + 1)) := by ring
    _ ≤ (x - (n + 1 : ℝ)) * Real.log x * x ^ (-(1 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hpow hnonneg
    _ = (x - (n + 1 : ℝ)) * x ^ (-(1 : ℝ)) * Real.log x := by ring

/-- Norm of the `door3termC` integrand is bounded
(mirror of `TestAnalytic.lean:157`). -/
theorem door3norm_termC_integrand_le (n : ℕ) {s : ℂ} (_hs : 0 < s.re) {x : ℝ}
    (hx1 : (n + 1 : ℝ) ≤ x) :
    ‖((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(s + 1))‖ ≤
      (x - (n + 1 : ℝ)) * x ^ (-(s.re + 1)) := by
  have hxpos : 0 < x := by
    have hnp : 0 < (n + 1 : ℝ) := by positivity
    linarith
  rw [norm_mul]
  have h1 : ‖((x - (n + 1 : ℝ)) : ℂ)‖ = x - (n + 1 : ℝ) := by
    norm_cast; exact abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hx1))
  rw [h1]
  have h2 : ‖(x : ℂ) ^ (-(s + 1))‖ = x ^ (-(s.re + 1)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos (-(s + 1))]
    rw [show (-(s + 1)).re = -(s.re + 1) by simp]
  rw [h2]

#print axioms door3termC_eq_term
#print axioms door3termTSumC_eq_termTSum
#print axioms door3hasDerivAt_termC_integrand
#print axioms door3continuousOn_termC_integrand
#print axioms door3continuousOn_termC'_integrand
#print axioms door3norm_termC'_integrand_le
#print axioms door3norm_termC_integrand_le

/-! ## Door-3 remainder 5c: engine prefix B — single-term differentiability + norm
Mirror of `TestAnalytic.lean:173-314` with `door3` names. No `simpa`. -/

/-- `door3termC (n+1)` is differentiable on the right half-plane
(mirror of `TestAnalytic.lean:174`). -/
theorem door3hasDerivAt_termC (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (fun t : ℂ => door3termC (n + 1) t) (door3termC' (n + 1) s) s := by
  let a : ℝ := (n + 1 : ℝ)
  let b : ℝ := (n + 1 : ℝ) + 1
  let F : ℂ → ℝ → ℂ := fun t x => ((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(t + 1))
  let F' : ℂ → ℝ → ℂ := fun t x =>
    -((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(t + 1)) * Complex.log (x : ℂ)
  let bound : ℝ → ℝ := fun x => (x - (n + 1 : ℝ)) * x ^ (-(1 : ℝ)) * Real.log x
  let halfPlane : Set ℂ := {z : ℂ | 0 < z.re}
  have hhalf_open : IsOpen halfPlane := isOpen_lt continuous_const continuous_re
  have hhalf_mem : halfPlane ∈ 𝓝 s := hhalf_open.mem_nhds hs
  have hA : a ≤ b := by dsimp [a, b]; linarith
  have hF_meas : ∀ᶠ t in 𝓝 s, AEStronglyMeasurable (F t) (volume.restrict (Set.uIoc a b)) := by
    filter_upwards [hhalf_mem] with t ht
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    rw [Set.uIoc_of_le hA]
    exact (door3continuousOn_termC_integrand n t).mono Set.Ioc_subset_Icc_self
  have hF_int : IntervalIntegrable (F s) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hA]
    exact ContinuousOn.integrableOn_Icc (door3continuousOn_termC_integrand n s) |>.mono_set Set.Ioc_subset_Icc_self
  have hF'_meas : AEStronglyMeasurable (F' s) (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hA]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact (door3continuousOn_termC'_integrand n s).mono Set.Ioc_subset_Icc_self
  have hcontBound : ContinuousOn bound (Set.Icc a b) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hxpos : 0 < x := by
      have hnp : 0 < (n + 1 : ℝ) := by positivity
      linarith [hx.1]
    dsimp [bound]
    exact ContinuousAt.mul
      (ContinuousAt.mul
        (ContinuousAt.sub continuousAt_id continuousAt_const)
        (Real.continuousAt_rpow_const x (-(1 : ℝ)) (Or.inl (by linarith : x ≠ 0))))
      (Real.continuousAt_log (by linarith : x ≠ 0))
  have hbound_int : IntervalIntegrable bound volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hA]
    exact ContinuousOn.integrableOn_Icc hcontBound |>.mono_set Set.Ioc_subset_Icc_self
  have h_bound : ∀ᵐ x ∂volume, x ∈ Set.uIoc a b → ∀ t ∈ halfPlane, ‖F' t x‖ ≤ bound x := by
    refine ae_of_all volume (fun x hx => ?_)
    intro t ht
    have hx1 : (n + 1 : ℝ) ≤ x := by
      rw [Set.uIoc_of_le hA] at hx
      exact le_of_lt hx.1
    dsimp [F', bound]
    exact door3norm_termC'_integrand_le n ht hx1
  have h_diff : ∀ᵐ x ∂volume, x ∈ Set.uIoc a b → ∀ t ∈ halfPlane,
      HasDerivAt (fun t => F t x) (F' t x) t := by
    refine ae_of_all volume (fun x hx => ?_)
    intro t ht
    have hx1 : 1 ≤ x := by
      have hle : (n + 1 : ℝ) ≤ x := by
        rw [Set.uIoc_of_le hA] at hx
        exact le_of_lt hx.1
      have h1n : 1 ≤ (n + 1 : ℝ) := by linarith
      linarith
    have hbase := door3hasDerivAt_termC_integrand (n + 1) (s := t) hx1
    have hEq1 : (fun u : ℂ => ((x - (((n + 1 : ℕ) : ℝ))) : ℂ) * (x : ℂ) ^ (-(u + 1)))
        = (fun u : ℂ => F u x) := by
      funext u
      dsimp [F]
      congr 1
      congr 1
      push_cast
      ring
    have hEq2 : -((x - (((n + 1 : ℕ) : ℝ))) : ℂ) * (x : ℂ) ^ (-(t + 1)) *
        Complex.log (x : ℂ) = F' t x := by
      dsimp [F']
      push_cast
      ring
    rw [← hEq1, ← hEq2]
    exact hbase
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (μ := volume) (a := a) (b := b) (bound := bound) hhalf_mem hF_meas hF_int hF'_meas h_bound
    hbound_int h_diff
  have h2 := h.2
  have hfun : (fun t : ℂ => door3termC (n + 1) t) = (fun x => ∫ t in a..b, F x t) := by
    funext t
    simp only [door3termC, F, a, b]
    norm_cast
  have hderiv : door3termC' (n + 1) s = ∫ t in a..b, F' s t := by
    simp only [door3termC', F', a, b]
    norm_cast
  rw [hfun] at *
  rw [hderiv]
  exact h2

/-- Norm of `door3termC (n+1)` on the right half-plane
(mirror of `TestAnalytic.lean:256`). -/
theorem door3norm_termC_le (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖door3termC (n + 1) s‖ ≤ (n + 1 : ℝ) ^ (-(s.re + 1)) := by
  unfold door3termC
  have hA : (n + 1 : ℝ) ≤ (n + 1 : ℝ) + 1 := by norm_num
  have h1 : ‖∫ x : ℝ in (n + 1 : ℝ)..((n + 1 : ℝ) + 1),
      ((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(s + 1))‖ ≤
      ∫ x : ℝ in (n + 1 : ℝ)..((n + 1 : ℝ) + 1),
      ‖((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(s + 1))‖ :=
    intervalIntegral.norm_integral_le_integral_norm hA
  have hbound : ∀ x, x ∈ Set.uIoc ((n + 1 : ℝ)) ((n + 1 : ℝ) + 1) →
      ‖((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(s + 1))‖ ≤ (n + 1 : ℝ) ^ (-(s.re + 1)) := by
    intro x hx
    have hx1 : (n + 1 : ℝ) ≤ x := by rw [Set.uIoc_of_le hA] at hx; exact hx.1.le
    have hxpos : 0 < x := by
      have hnp : 0 < (n + 1 : ℝ) := by positivity
      exact lt_of_lt_of_le hnp hx1
    have h1n : ‖((x - (n + 1 : ℝ)) : ℂ)‖ = x - (n + 1 : ℝ) := by
      have hnn : ‖((x - (n + 1 : ℝ)) : ℂ)‖ = |x - (n + 1 : ℝ)| := by norm_cast
      rw [hnn]
      exact abs_of_nonneg (by linarith)
    have h2n : ‖(x : ℂ) ^ (-(s + 1))‖ = x ^ (-(s.re + 1)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos (-(s + 1))]; simp
    rw [norm_mul, h1n, h2n]
    have hpow : x ^ (-(s.re + 1)) ≤ (n + 1 : ℝ) ^ (-(s.re + 1)) := by
      exact rpow_le_rpow_of_nonpos (by positivity : 0 < (n + 1 : ℝ)) hx1 (by linarith [hs])
    have h5 : (x - (n + 1 : ℝ)) * x ^ (-(s.re + 1)) ≤ (n + 1 : ℝ) ^ (-(s.re + 1)) := by
      have h6 : (x - (n + 1 : ℝ)) * x ^ (-(s.re + 1)) ≤ (x - (n + 1 : ℝ)) * (n + 1 : ℝ) ^ (-(s.re + 1)) :=
        mul_le_mul_of_nonneg_left hpow (by linarith)
      have h7 : x - (n + 1 : ℝ) ≤ 1 := by
        have hxx : x ≤ (n + 1 : ℝ) + 1 := by
          rw [Set.uIoc_of_le hA] at hx; exact hx.2
        linarith
      have h8 : (n + 1 : ℝ) ^ (-(s.re + 1)) ≥ 0 := rpow_nonneg (by positivity) _
      calc (x - (n + 1 : ℝ)) * x ^ (-(s.re + 1))
        ≤ (x - (n + 1 : ℝ)) * (n + 1 : ℝ) ^ (-(s.re + 1)) := h6
      _ ≤ 1 * (n + 1 : ℝ) ^ (-(s.re + 1)) := mul_le_mul_of_nonneg_right h7 h8
      _ = (n + 1 : ℝ) ^ (-(s.re + 1)) := one_mul _
    exact h5
  have h2 : (∫ x : ℝ in (n + 1 : ℝ)..((n + 1 : ℝ) + 1),
      ‖((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(s + 1))‖) ≤
      ∫ x : ℝ in (n + 1 : ℝ)..((n + 1 : ℝ) + 1), (n + 1 : ℝ) ^ (-(s.re + 1)) := by
    refine intervalIntegral.integral_mono_on hA ?_ ?_ (fun x hx => ?_)
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hA]
      exact (continuous_norm.comp_continuousOn (door3continuousOn_termC_integrand n s)).integrableOn_Icc |>.mono_set Set.Ioc_subset_Icc_self
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hA]
      exact continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    · by_cases heq : x = n + 1
      · subst heq; simp [norm_zero, mul_zero]; positivity
      · have hx' : x ∈ Set.uIoc (n + 1 : ℝ) ((n + 1 : ℝ) + 1) := by
          rw [Set.uIoc_of_le hA]; exact ⟨lt_of_le_of_ne hx.1 (Ne.symm heq), hx.2⟩
        exact hbound x hx'
  have h3 : (∫ x : ℝ in (n + 1 : ℝ)..((n + 1 : ℝ) + 1),
      (n + 1 : ℝ) ^ (-(s.re + 1))) = (n + 1 : ℝ) ^ (-(s.re + 1)) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring_nf
  rw [h3] at h2
  norm_cast at *
  linarith [h1, h2]

#print axioms door3hasDerivAt_termC
#print axioms door3norm_termC_le

/-! ## Door-3 remainder 5d: engine prefix C — tsum differentiability + bridge
Mirror of `TestAnalytic.lean:316-462` with `door3` names. No `simpa`. -/

/-- `door3termTSumC` is differentiable on the right half-plane
(mirror of `TestAnalytic.lean:317`). -/
theorem door3hasDerivAt_termTSumC {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt door3termTSumC (∑' n : ℕ, door3termC' (n + 1) s) s := by
  let σ : ℝ := s.re
  let t : Set ℂ := {z : ℂ | σ / 2 < z.re}
  have ht_open : IsOpen t := isOpen_lt continuous_const continuous_re
  have ht_pre : IsPreconnected t :=
    (convex_halfSpace_re_gt (σ / 2)).isPreconnected
  have hst : s ∈ t := by dsimp [t, σ]; linarith [hs]
  have hσpos : 0 < σ := by dsimp [σ]; exact hs
  have hsum_pow : ∀ p : ℝ, p < -1 → Summable (fun n : ℕ => (n + 1 : ℝ) ^ p) := by
    intro p hp
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ p) := Real.summable_nat_rpow.mpr hp
    have h2 : Summable ((fun n : ℕ => (n : ℝ) ^ p) ∘ Nat.succ) :=
      Summable.comp_injective h1 Nat.succ_injective
    have he : (fun n : ℕ => ((n : ℝ) + 1) ^ p) = ((fun n : ℕ => (n : ℝ) ^ p) ∘ Nat.succ) := by
      ext n; norm_cast
    rw [he]; exact h2
  let u : ℕ → ℝ := fun n => (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * Real.log (n + 2)
  have hu : Summable u := by
    let v : ℕ → ℝ := fun n => ((4 / σ) * 2 ^ (σ / 4)) * (n + 1 : ℝ) ^ (-(σ / 4 + 1))
    have hv : Summable v :=
      (hsum_pow (-(σ / 4 + 1)) (by linarith [hσpos])).mul_left
        ((4 / σ) * 2 ^ (σ / 4))
    refine Summable.of_norm_bounded hv (fun n => ?_)
    dsimp [u, v]
    rw [abs_of_nonneg]
    · have hlog : Real.log (n + 2 : ℝ) ≤ (n + 2 : ℝ) ^ (σ / 4) / (σ / 4) := by
        have hll := Real.log_natCast_le_rpow_div (n + 2) (by linarith : 0 < σ / 4)
        push_cast at hll ⊢
        exact hll
      have hpow : (n + 2 : ℝ) ^ (σ / 4) ≤ (2 * (n + 1 : ℝ)) ^ (σ / 4) := by
        refine rpow_le_rpow (by positivity : 0 ≤ (n + 2 : ℝ)) ?_ ?_
        · nlinarith
        · exact div_nonneg (le_of_lt hσpos) (by norm_num)
      have h2 : (2 * (n + 1 : ℝ)) ^ (σ / 4) = 2 ^ (σ / 4) * (n + 1 : ℝ) ^ (σ / 4) := by
        rw [mul_rpow] <;> positivity
      have hpow2 : (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * (n + 1 : ℝ) ^ (σ / 4) =
          (n + 1 : ℝ) ^ (-(σ / 4 + 1)) := by
        rw [← rpow_add (by positivity : 0 < (n + 1 : ℝ))]
        congr 1
        ring
      have hnonneg : 0 ≤ (n + 1 : ℝ) ^ (-(σ / 2 + 1)) := by positivity
      calc (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * Real.log (↑n + 2)
        ≤ (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * ((↑n + 2) ^ (σ / 4) / (σ / 4)) :=
          mul_le_mul_of_nonneg_left hlog hnonneg
      _ ≤ (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * ((2 * (↑n + 1)) ^ (σ / 4) / (σ / 4)) := by
        apply mul_le_mul_of_nonneg_left _ hnonneg
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hpow (inv_nonneg.mpr (le_of_lt (by linarith [hσpos])))
      _ = (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * (2 ^ (σ / 4) * (↑n + 1) ^ (σ / 4) / (σ / 4)) := by rw [h2]
      _ = (n + 1 : ℝ) ^ (-(σ / 4 + 1)) * (2 ^ (σ / 4) / (σ / 4)) := by
        rw [← hpow2]; ring
      _ = 4 / σ * 2 ^ (σ / 4) * (n + 1 : ℝ) ^ (-(σ / 4 + 1)) := by ring
    · exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hg0 : Summable (fun n : ℕ => door3termC (n + 1) s) := by
    refine Summable.of_norm_bounded (hsum_pow (-(σ + 1)) (by linarith [hσpos])) (fun n => ?_)
    exact door3norm_termC_le (n := n) hs
  have hg : ∀ n y, y ∈ t → HasDerivAt (fun z : ℂ => door3termC (n + 1) z) (door3termC' (n + 1) y) y := by
    intro n y hy
    have hypos : 0 < y.re := by
      have hlt : σ / 2 < y.re := by dsimp [t] at hy; exact hy
      linarith [hσpos]
    exact door3hasDerivAt_termC n hypos
  have hg' : ∀ n y, y ∈ t → ‖door3termC' (n + 1) y‖ ≤ u n := by
    intro n y hy
    dsimp [door3termC', u]
    have hyσ : σ / 2 ≤ y.re := le_of_lt (by dsimp [t] at hy; exact hy)
    have hA : (n + 1 : ℝ) ≤ (n + 1 : ℝ) + 1 := by norm_num
    have hnorm :
        ‖∫ x : ℝ in (n + 1 : ℝ)..((n + 1 : ℝ) + 1),
          -((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(y + 1)) * Complex.log (x : ℂ)‖ ≤
        ∫ x : ℝ in (n + 1 : ℝ)..((n + 1 : ℝ) + 1),
          ‖-((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(y + 1)) * Complex.log (x : ℂ)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hA
    have hbnd : ∀ x, (n + 1 : ℝ) ≤ x → x ≤ (n + 1 : ℝ) + 1 →
        ‖-((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(y + 1)) * Complex.log (x : ℂ)‖ ≤
          (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * Real.log (n + 2) := by
      intro x hx1 hx2
      by_cases heq : x = n + 1
      · subst heq; simp [neg_zero, zero_mul, norm_zero]
        exact mul_nonneg (rpow_nonneg (by positivity) _) (Real.log_nonneg (by linarith [Nat.le_add_left 1 n]))
      have hx1' : (n + 1 : ℝ) < x := lt_of_le_of_ne hx1 (Ne.symm heq)
      have hxpos : 0 < x := by
        have hnp : 0 < (n + 1 : ℝ) := by positivity
        linarith
      have hxge1 : 1 ≤ x := by linarith
      have hlogc : Complex.log (x : ℂ) = (Real.log x : ℂ) := (Complex.ofReal_log hxpos.le).symm
      rw [hlogc]
      have h1 : ‖-((x - (n + 1 : ℝ)) : ℂ)‖ = x - (n + 1 : ℝ) := by
        rw [norm_neg]; norm_cast; exact abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hx1))
      have h2 : ‖(x : ℂ) ^ (-(y + 1))‖ = x ^ (-(y.re + 1)) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos (-(y + 1))]; simp
      have h3 : ‖(Real.log x : ℂ)‖ = Real.log x := by
        calc
          ‖(Real.log x : ℂ)‖ = |Real.log x| := RCLike.norm_ofReal (Real.log x)
          _ = Real.log x := abs_of_nonneg (Real.log_nonneg hxge1)
      rw [norm_mul, norm_mul, h1, h2, h3]
      have hpow_le : x ^ (-(y.re + 1)) ≤ (n + 1 : ℝ) ^ (-(y.re + 1)) :=
        rpow_le_rpow_of_nonpos (by positivity) hx1 (by linarith)
      have hpow2 : (n + 1 : ℝ) ^ (-(y.re + 1)) ≤ (n + 1 : ℝ) ^ (-(σ / 2 + 1)) := by
        apply rpow_le_rpow_of_exponent_le _ (by linarith)
        linarith [Nat.le_succ n]
      have hlog : Real.log x ≤ Real.log (n + 2) :=
        Real.log_le_log (by positivity) (by push_cast; linarith)
      have hn1 : 0 ≤ x - (n + 1 : ℝ) := sub_nonneg.mpr hx1
      have hn2 : 0 ≤ Real.log x := Real.log_nonneg hxge1
      have hn3 : 0 ≤ (n + 1 : ℝ) ^ (-(σ / 2 + 1)) := by positivity
      calc (x - (n + 1 : ℝ)) * x ^ (-(y.re + 1)) * Real.log x
        ≤ (x - (n + 1 : ℝ)) * (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * Real.log x :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_trans hpow_le hpow2) hn1) hn2
        _ ≤ 1 * (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * Real.log x :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hn3) hn2
        _ = (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * Real.log x := by ring
        _ ≤ (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * Real.log (n + 2) :=
            mul_le_mul_of_nonneg_left hlog hn3
    have hint : ∫ x : ℝ in (n + 1 : ℝ)..((n + 1 : ℝ) + 1),
        ‖-((x - (n + 1 : ℝ)) : ℂ) * (x : ℂ) ^ (-(y + 1)) * Complex.log (x : ℂ)‖ ≤
      ∫ x : ℝ in (n + 1 : ℝ)..((n + 1 : ℝ) + 1),
        (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * Real.log (n + 2) := by
      refine intervalIntegral.integral_mono_on hA ?_ ?_ (fun x hx => ?_)
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hA]
        exact (continuous_norm.comp_continuousOn (door3continuousOn_termC'_integrand n y)).integrableOn_Icc |>.mono_set Set.Ioc_subset_Icc_self
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hA]
        exact continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      · exact hbnd x hx.1 hx.2
    have hconst : ∫ x : ℝ in (n + 1 : ℝ)..((n + 1 : ℝ) + 1),
        (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * Real.log (n + 2) ≤
      (n + 1 : ℝ) ^ (-(σ / 2 + 1)) * Real.log (n + 2) := by
      rw [intervalIntegral.integral_const]; simp [smul_eq_mul, mul_one]
    exact_mod_cast le_trans hnorm (le_trans hint hconst)
  exact hasDerivAt_tsum_of_isPreconnected (𝕜 := ℂ) hu ht_open ht_pre hg hg' hst hg0 hst

/-- `door3termTSumC` is analytic on the right half-plane
(mirror of `TestAnalytic.lean:449`). -/
theorem door3analyticOnNhd_termTSumC :
    AnalyticOnNhd ℂ door3termTSumC {z : ℂ | 0 < z.re} := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const continuous_re)
  intro z hz
  exact (door3hasDerivAt_termTSumC hz).differentiableAt.differentiableWithinAt

/-- `ZetaAsymptotics.termTSum` is real-analytic on `(0,∞)`
(mirror of `TestAnalytic.lean:455`). -/
theorem door3analyticOnNhd_termTSum_real :
    AnalyticOnNhd ℝ ZetaAsymptotics.termTSum (Set.Ioi 0) := by
  intro s hs
  have hA : AnalyticAt ℝ (fun t : ℝ => (door3termTSumC (t : ℂ)).re) s := by
    exact AnalyticAt.re_ofReal (door3analyticOnNhd_termTSumC _ hs)
  refine hA.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
  rw [door3termTSumC_eq_termTSum ht]
  rfl

/-- THE BRIDGE: unconditional proof of the isolated analytic lemma. -/
theorem door3EMRightAnalytic_proved : Door3EMRightAnalytic := by
  unfold Door3EMRightAnalytic
  intro s hs
  have h1 : AnalyticAt ℝ (fun _t : ℝ => (1 : ℝ)) s := analyticAt_const
  have h2 : AnalyticAt ℝ (fun t : ℝ => t) s := analyticAt_id
  have h3 : AnalyticAt ℝ (fun t : ℝ => ZetaAsymptotics.termTSum t) s :=
    door3analyticOnNhd_termTSum_real s hs
  have h4 : AnalyticAt ℝ (fun t : ℝ => t * ZetaAsymptotics.termTSum t) s := h2.mul h3
  exact h1.sub h4

/-- Unconditional norm bound `1 ≤ ‖ζ(1/2)‖` (discharges the `of_EM` chain). -/
theorem door3HalfNorm_ge_one : (1 : ℝ) ≤ ‖riemannZeta ((((1 / 2 : ℝ))) : ℂ)‖ :=
  door3HalfNorm_ge_one_of_EM door3EMRightAnalytic_proved

/-- Unconditional discharge of committed `Door3HalfRealHyp`. -/
theorem door3HalfRealHyp : Door3HalfRealHyp :=
  door3HalfRealHyp_of_EM door3EMRightAnalytic_proved

/-- Unconditional height-0 numeral on the segment. -/
theorem door3RealSeg_pointwiseC0 :
    door3RealC0 ≤ ‖riemannZeta (tailShiftedSReal (0 : ℂ))‖ ∧
      (0 : ℂ) ∈ door3RealSeg :=
  door3RealSeg_pointwiseC0_of_EM door3EMRightAnalytic_proved

#print axioms door3hasDerivAt_termTSumC
#print axioms door3analyticOnNhd_termTSumC
#print axioms door3analyticOnNhd_termTSum_real
#print axioms door3EMRightAnalytic_proved
#print axioms door3HalfNorm_ge_one
#print axioms door3HalfRealHyp
#print axioms door3RealSeg_pointwiseC0

/-!
## Door-3 remainder 5c: height-|t|<=1 upper enclosure + second tile toward (-10,10) (2026-09-08, append-only)

Slice audit (read-only, `import Mathlib` only, no new import):
* Uniform `c > 0` over `door3RealSeg` needs pointwise nonvanishing on the whole
  `1/2 + I*[-1,1]` arc; the banked numeral covers height `t = 0` only, and the
  `|Im| in [10,11]` tail numerals live in a disjoint band -- so the uniform lower
  bound stays residual. What IS banked here, Mathlib-only and unconditional:
  (a) the one-sided height enclosure (upper bound) over `door3RealSeg` via the
  committed T4 compact-continuity pattern (`door3RealSeg_isCompact` +
  `IsCompact.exists_bound_of_continuousOn`, as in `exists_tailCell_zetaUpper`);
  (b) the second tile `door3RealSegNext2` (`2 <= Re <= 3`, `Im = 0`) repeating the
  committed `door3RealSegNext` pattern, chained by `door3RealSegNext2_meet`
  (`2` in both tiles), extending coverage `[-1,2]` to `[-1,3]` toward `(-10,10)`.
-/

/-- Height-`|t| <= 1` UPPER enclosure over `door3RealSeg`
(mirror of `exists_tailCell_zetaUpper`: compactness + continuity). -/
theorem exists_door3RealSeg_zetaUpper :
    ∃ B : ℝ, ∀ z ∈ door3RealSeg,
      ‖riemannZeta (tailShiftedSReal z)‖ ≤ B :=
  door3RealSeg_isCompact.exists_bound_of_continuousOn door3RealZetaContinuousOnSeg

/-- Second compact tile toward `(-10,10)`: `2 ≤ Re z ≤ 3`, `Im z = 0`. -/
def door3RealSegNext2 : Set ℂ :=
  Complex.re ⁻¹' Set.Icc (2 : ℝ) 3 ∩ Complex.im ⁻¹' Set.Icc (0 : ℝ) 0

/-- Closed-rectangle membership for the second tile. -/
theorem door3RealSegNext2_mem_of_reim (z : ℂ) (hre1 : (2 : ℝ) ≤ z.re)
    (hre2 : z.re ≤ 3) (hlo : (0 : ℝ) ≤ z.im) (hhi : z.im ≤ 0) :
    z ∈ door3RealSegNext2 := by
  simp only [door3RealSegNext2, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc]
  exact ⟨⟨hre1, hre2⟩, hlo, hhi⟩

/-- Witness: `5/2` lies in the second tile. -/
theorem door3RealSegNext2_witness : ((((5 / 2 : ℝ))) : ℂ) ∈ door3RealSegNext2 := by
  simp only [door3RealSegNext2, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num

/-- The second tile is closed. -/
theorem door3RealSegNext2_isClosed : IsClosed door3RealSegNext2 := by
  unfold door3RealSegNext2
  exact (IsClosed.preimage Complex.continuous_re isClosed_Icc).inter
    (IsClosed.preimage Complex.continuous_im isClosed_Icc)

/-- The second tile lies in `closedBall 0 4`, hence is bounded. -/
theorem door3RealSegNext2_isBounded : Bornology.IsBounded door3RealSegNext2 := by
  apply Metric.isBounded_closedBall.subset
  intro z hz
  obtain ⟨⟨h1, h2⟩, hlo, hhi⟩ := hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have him : z.im = 0 := le_antisymm hhi hlo
  have habs : |z.re| ≤ 3 := by
    rw [abs_le]
    constructor
    · linarith
    · exact h2
  have hre2 : z.re * z.re ≤ (3 : ℝ) * 3 := by
    have h := mul_le_mul habs habs (abs_nonneg _) (show (0 : ℝ) ≤ 3 by norm_num)
    rwa [abs_mul_abs_self] at h
  have him2 : z.im * z.im ≤ (0 : ℝ) := by
    rw [him]
    norm_num
  have hnorm : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hle : ‖z‖ ^ 2 ≤ (4 : ℝ) ^ 2 := by
    rw [hnorm]
    have hsum := add_le_add hre2 him2
    have h16 : (3 : ℝ) * 3 + 0 ≤ 4 ^ 2 := by norm_num
    exact le_trans hsum h16
  exact le_of_sq_le_sq hle (by norm_num)

/-- The second tile is compact (Heine–Borel). -/
theorem door3RealSegNext2_isCompact : IsCompact door3RealSegNext2 := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨door3RealSegNext2_isClosed, door3RealSegNext2_isBounded⟩

/-- The second tile sits inside the required open slice `-10 < Re < 10`. -/
theorem door3RealSegNext2_in_open_strip (z : ℂ) (hz : z ∈ door3RealSegNext2) :
    (-10 : ℝ) < z.re ∧ z.re < 10 ∧ z.im = 0 := by
  obtain ⟨⟨h1, h2⟩, hlo, hhi⟩ := hz
  exact ⟨by linarith, by linarith, le_antisymm hhi hlo⟩

/-- Shifted real part on the second tile: `Re s = 1/2` (critical line). -/
theorem door3RealNext2Shift_re (z : ℂ) (hz : z ∈ door3RealSegNext2) :
    (tailShiftedSReal z).re = 1 / 2 := by
  obtain ⟨_, hlo, hhi⟩ := hz
  have him : z.im = 0 := le_antisymm hhi hlo
  rw [tailShiftedSReal_re, him]
  norm_num

/-- Pole avoidance on the second tile. -/
theorem door3RealNext2Shift_ne_one_of_seg (z : ℂ) (hz : z ∈ door3RealSegNext2) :
    tailShiftedSReal z ≠ 1 := by
  intro hcon
  have hre : (tailShiftedSReal z).re = (1 : ℂ).re := congrArg Complex.re hcon
  rw [door3RealNext2Shift_re z hz, Complex.one_re] at hre
  norm_num at hre

/-- Zeta pulled back through the shift is continuous on the second tile. -/
theorem door3RealNext2ZetaContinuousOnSeg :
    ContinuousOn (fun z => riemannZeta (tailShiftedSReal z)) door3RealSegNext2 := by
  intro x hx
  have hne : tailShiftedSReal x ≠ 1 := door3RealNext2Shift_ne_one_of_seg x hx
  have hdiff : DifferentiableAt ℂ riemannZeta (tailShiftedSReal x) :=
    differentiableAt_riemannZeta hne
  exact (hdiff.continuousAt.comp' tailShiftedSReal_continuous.continuousAt).continuousWithinAt

/-- Chaining point: `2` lies in both tiles, so `[-1,2] ∪ [2,3] = [-1,3]`. -/
theorem door3RealSegNext2_meet :
    ((((2 : ℝ))) : ℂ) ∈ door3RealSegNext ∧
      ((((2 : ℝ))) : ℂ) ∈ door3RealSegNext2 := by
  simp only [door3RealSegNext, door3RealSegNext2, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_Icc, Complex.ofReal_re, Complex.ofReal_im]
  norm_num

#print axioms exists_door3RealSeg_zetaUpper
#print axioms door3RealSegNext2_witness
#print axioms door3RealSegNext2_isClosed
#print axioms door3RealSegNext2_isBounded
#print axioms door3RealSegNext2_isCompact
#print axioms door3RealSegNext2_in_open_strip
#print axioms door3RealNext2Shift_re
#print axioms door3RealNext2Shift_ne_one_of_seg
#print axioms door3RealNext2ZetaContinuousOnSeg
#print axioms door3RealSegNext2_meet

/-!
## Door-3 remainder 5 third tile: `[3,4]` toward `(-10,10)` (2026-09-08, append-only)

Extends the committed `door3RealSegNext2` pattern (`[-1,3]` chained by
`door3RealSeg_next_meet` + `door3RealSegNext2_meet`) one step further to
`[-1,4]`. Same critical-line shape (`Re s = 1/2` via `tailShiftedSReal_re`),
pole avoidance (`Re s = 1/2`, so `differentiableAt_riemannZeta` applies),
continuity, plus upper enclosures on both the committed second tile and the
new third tile (one-liner `IsCompact.exists_bound_of_continuousOn`, as in
committed `exists_door3RealSeg_zetaUpper`). The new-height pointwise LOWER
bound (`c > 0` at `t = +-1/2`, or nonvanishing at a meet point, via a
kernel-checked enclosure) remains the exact residual; this tile is the
tightest proved step toward it.
-/

/-- Third compact tile toward `(-10,10)`: `3 ≤ Re z ≤ 4`, `Im z = 0`. -/
def door3RealSegNext3 : Set ℂ :=
  Complex.re ⁻¹' Set.Icc (3 : ℝ) 4 ∩ Complex.im ⁻¹' Set.Icc (0 : ℝ) 0

/-- Closed-rectangle membership for the third tile. -/
theorem door3RealSegNext3_mem_of_reim (z : ℂ) (hre1 : (3 : ℝ) ≤ z.re)
    (hre2 : z.re ≤ 4) (hlo : (0 : ℝ) ≤ z.im) (hhi : z.im ≤ 0) :
    z ∈ door3RealSegNext3 := by
  simp only [door3RealSegNext3, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc]
  exact ⟨⟨hre1, hre2⟩, hlo, hhi⟩

/-- Witness: `7/2` lies in the third tile. -/
theorem door3RealSegNext3_witness : ((((7 / 2 : ℝ))) : ℂ) ∈ door3RealSegNext3 := by
  simp only [door3RealSegNext3, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num

/-- The third tile is closed. -/
theorem door3RealSegNext3_isClosed : IsClosed door3RealSegNext3 := by
  unfold door3RealSegNext3
  exact (IsClosed.preimage Complex.continuous_re isClosed_Icc).inter
    (IsClosed.preimage Complex.continuous_im isClosed_Icc)

/-- The third tile lies in `closedBall 0 5`, hence is bounded. -/
theorem door3RealSegNext3_isBounded : Bornology.IsBounded door3RealSegNext3 := by
  apply Metric.isBounded_closedBall.subset
  intro z hz
  obtain ⟨⟨h1, h2⟩, hlo, hhi⟩ := hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have him : z.im = 0 := le_antisymm hhi hlo
  have habs : |z.re| ≤ 4 := by
    rw [abs_le]
    constructor
    · linarith
    · exact h2
  have hre2 : z.re * z.re ≤ (4 : ℝ) * 4 := by
    have h := mul_le_mul habs habs (abs_nonneg _) (show (0 : ℝ) ≤ 4 by norm_num)
    rwa [abs_mul_abs_self] at h
  have him2 : z.im * z.im ≤ (0 : ℝ) := by
    rw [him]
    norm_num
  have hnorm : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hle : ‖z‖ ^ 2 ≤ (5 : ℝ) ^ 2 := by
    rw [hnorm]
    have hsum := add_le_add hre2 him2
    have h25 : (4 : ℝ) * 4 + 0 ≤ 5 ^ 2 := by norm_num
    exact le_trans hsum h25
  exact le_of_sq_le_sq hle (by norm_num)

/-- The third tile is compact (Heine–Borel). -/
theorem door3RealSegNext3_isCompact : IsCompact door3RealSegNext3 := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨door3RealSegNext3_isClosed, door3RealSegNext3_isBounded⟩

/-- The third tile sits inside the required open slice `-10 < Re < 10`. -/
theorem door3RealSegNext3_in_open_strip (z : ℂ) (hz : z ∈ door3RealSegNext3) :
    (-10 : ℝ) < z.re ∧ z.re < 10 ∧ z.im = 0 := by
  obtain ⟨⟨h1, h2⟩, hlo, hhi⟩ := hz
  exact ⟨by linarith, by linarith, le_antisymm hhi hlo⟩

/-- Shifted real part on the third tile: `Re s = 1/2` (critical line). -/
theorem door3RealNext3Shift_re (z : ℂ) (hz : z ∈ door3RealSegNext3) :
    (tailShiftedSReal z).re = 1 / 2 := by
  obtain ⟨_, hlo, hhi⟩ := hz
  have him : z.im = 0 := le_antisymm hhi hlo
  rw [tailShiftedSReal_re, him]
  norm_num

/-- Pole avoidance on the third tile. -/
theorem door3RealNext3Shift_ne_one_of_seg (z : ℂ) (hz : z ∈ door3RealSegNext3) :
    tailShiftedSReal z ≠ 1 := by
  intro hcon
  have hre : (tailShiftedSReal z).re = (1 : ℂ).re := congrArg Complex.re hcon
  rw [door3RealNext3Shift_re z hz, Complex.one_re] at hre
  norm_num at hre

/-- Zeta pulled back through the shift is continuous on the third tile. -/
theorem door3RealNext3ZetaContinuousOnSeg :
    ContinuousOn (fun z => riemannZeta (tailShiftedSReal z)) door3RealSegNext3 := by
  intro x hx
  have hne : tailShiftedSReal x ≠ 1 := door3RealNext3Shift_ne_one_of_seg x hx
  have hdiff : DifferentiableAt ℂ riemannZeta (tailShiftedSReal x) :=
    differentiableAt_riemannZeta hne
  exact (hdiff.continuousAt.comp' tailShiftedSReal_continuous.continuousAt).continuousWithinAt

/-- Height upper enclosure over the committed second tile
(mirror of `exists_door3RealSeg_zetaUpper`). -/
theorem exists_door3RealSegNext2_zetaUpper :
    ∃ B : ℝ, ∀ z ∈ door3RealSegNext2,
      ‖riemannZeta (tailShiftedSReal z)‖ ≤ B :=
  door3RealSegNext2_isCompact.exists_bound_of_continuousOn door3RealNext2ZetaContinuousOnSeg

/-- Height upper enclosure over the third tile
(mirror of `exists_door3RealSeg_zetaUpper`). -/
theorem exists_door3RealSegNext3_zetaUpper :
    ∃ B : ℝ, ∀ z ∈ door3RealSegNext3,
      ‖riemannZeta (tailShiftedSReal z)‖ ≤ B :=
  door3RealSegNext3_isCompact.exists_bound_of_continuousOn door3RealNext3ZetaContinuousOnSeg

/-- Chaining point: `3` lies in both tiles, so `[-1,3] ∪ [3,4] = [-1,4]`. -/
theorem door3RealSegNext3_meet :
    ((((3 : ℝ))) : ℂ) ∈ door3RealSegNext2 ∧
      ((((3 : ℝ))) : ℂ) ∈ door3RealSegNext3 := by
  simp only [door3RealSegNext2, door3RealSegNext3, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_Icc, Complex.ofReal_re, Complex.ofReal_im]
  norm_num

#print axioms door3RealSegNext3_witness
#print axioms door3RealSegNext3_isClosed
#print axioms door3RealSegNext3_isBounded
#print axioms door3RealSegNext3_isCompact
#print axioms door3RealSegNext3_in_open_strip
#print axioms door3RealNext3Shift_re
#print axioms door3RealNext3Shift_ne_one_of_seg
#print axioms door3RealNext3ZetaContinuousOnSeg
#print axioms exists_door3RealSegNext2_zetaUpper
#print axioms exists_door3RealSegNext3_zetaUpper
#print axioms door3RealSegNext3_meet

/-!
## Door-3 remainder 5 fourth tile: `[4,5]` toward `(-10,10)` (2026-09-08, append-only)

Extends the committed `door3RealSegNext3` pattern (`[-1,4]` chained by
`door3RealSeg_next_meet` + `door3RealSegNext2_meet` + `door3RealSegNext3_meet`)
one step further to `[-1,5]`. Same critical-line shape (`Re s = 1/2` via
`tailShiftedSReal_re`), pole avoidance (`Re s = 1/2`, so
`differentiableAt_riemannZeta` applies), continuity, plus an upper enclosure
on the new fourth tile (one-liner `IsCompact.exists_bound_of_continuousOn`,
as in committed `exists_door3RealSeg_zetaUpper`). The new-height pointwise
LOWER bound (`c > 0` at `t = +-1/2`, or nonvanishing at a meet point, via a
kernel-checked enclosure) remains the exact residual; this tile is the
tightest proved step toward it.
-/

/-- Fourth compact tile toward `(-10,10)`: `4 ≤ Re z ≤ 5`, `Im z = 0`. -/
def door3RealSegNext4 : Set ℂ :=
  Complex.re ⁻¹' Set.Icc (4 : ℝ) 5 ∩ Complex.im ⁻¹' Set.Icc (0 : ℝ) 0

/-- Closed-rectangle membership for the fourth tile. -/
theorem door3RealSegNext4_mem_of_reim (z : ℂ) (hre1 : (4 : ℝ) ≤ z.re)
    (hre2 : z.re ≤ 5) (hlo : (0 : ℝ) ≤ z.im) (hhi : z.im ≤ 0) :
    z ∈ door3RealSegNext4 := by
  simp only [door3RealSegNext4, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc]
  exact ⟨⟨hre1, hre2⟩, hlo, hhi⟩

/-- Witness: `9/2` lies in the fourth tile. -/
theorem door3RealSegNext4_witness : ((((9 / 2 : ℝ))) : ℂ) ∈ door3RealSegNext4 := by
  simp only [door3RealSegNext4, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num

/-- The fourth tile is closed. -/
theorem door3RealSegNext4_isClosed : IsClosed door3RealSegNext4 := by
  unfold door3RealSegNext4
  exact (IsClosed.preimage Complex.continuous_re isClosed_Icc).inter
    (IsClosed.preimage Complex.continuous_im isClosed_Icc)

/-- The fourth tile lies in `closedBall 0 6`, hence is bounded. -/
theorem door3RealSegNext4_isBounded : Bornology.IsBounded door3RealSegNext4 := by
  apply Metric.isBounded_closedBall.subset
  intro z hz
  obtain ⟨⟨h1, h2⟩, hlo, hhi⟩ := hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have him : z.im = 0 := le_antisymm hhi hlo
  have habs : |z.re| ≤ 5 := by
    rw [abs_le]
    constructor
    · linarith
    · exact h2
  have hre2 : z.re * z.re ≤ (5 : ℝ) * 5 := by
    have h := mul_le_mul habs habs (abs_nonneg _) (show (0 : ℝ) ≤ 5 by norm_num)
    rwa [abs_mul_abs_self] at h
  have him2 : z.im * z.im ≤ (0 : ℝ) := by
    rw [him]
    norm_num
  have hnorm : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hle : ‖z‖ ^ 2 ≤ (6 : ℝ) ^ 2 := by
    rw [hnorm]
    have hsum := add_le_add hre2 him2
    have h36 : (5 : ℝ) * 5 + 0 ≤ 6 ^ 2 := by norm_num
    exact le_trans hsum h36
  exact le_of_sq_le_sq hle (by norm_num)

/-- The fourth tile is compact (Heine–Borel). -/
theorem door3RealSegNext4_isCompact : IsCompact door3RealSegNext4 := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨door3RealSegNext4_isClosed, door3RealSegNext4_isBounded⟩

/-- The fourth tile sits inside the required open slice `-10 < Re < 10`. -/
theorem door3RealSegNext4_in_open_strip (z : ℂ) (hz : z ∈ door3RealSegNext4) :
    (-10 : ℝ) < z.re ∧ z.re < 10 ∧ z.im = 0 := by
  obtain ⟨⟨h1, h2⟩, hlo, hhi⟩ := hz
  exact ⟨by linarith, by linarith, le_antisymm hhi hlo⟩

/-- Shifted real part on the fourth tile: `Re s = 1/2` (critical line). -/
theorem door3RealNext4Shift_re (z : ℂ) (hz : z ∈ door3RealSegNext4) :
    (tailShiftedSReal z).re = 1 / 2 := by
  obtain ⟨_, hlo, hhi⟩ := hz
  have him : z.im = 0 := le_antisymm hhi hlo
  rw [tailShiftedSReal_re, him]
  norm_num

/-- Pole avoidance on the fourth tile. -/
theorem door3RealNext4Shift_ne_one_of_seg (z : ℂ) (hz : z ∈ door3RealSegNext4) :
    tailShiftedSReal z ≠ 1 := by
  intro hcon
  have hre : (tailShiftedSReal z).re = (1 : ℂ).re := congrArg Complex.re hcon
  rw [door3RealNext4Shift_re z hz, Complex.one_re] at hre
  norm_num at hre

/-- Zeta pulled back through the shift is continuous on the fourth tile. -/
theorem door3RealNext4ZetaContinuousOnSeg :
    ContinuousOn (fun z => riemannZeta (tailShiftedSReal z)) door3RealSegNext4 := by
  intro x hx
  have hne : tailShiftedSReal x ≠ 1 := door3RealNext4Shift_ne_one_of_seg x hx
  have hdiff : DifferentiableAt ℂ riemannZeta (tailShiftedSReal x) :=
    differentiableAt_riemannZeta hne
  exact (hdiff.continuousAt.comp' tailShiftedSReal_continuous.continuousAt).continuousWithinAt

/-- Height upper enclosure over the fourth tile
(mirror of `exists_door3RealSeg_zetaUpper`). -/
theorem exists_door3RealSegNext4_zetaUpper :
    ∃ B : ℝ, ∀ z ∈ door3RealSegNext4,
      ‖riemannZeta (tailShiftedSReal z)‖ ≤ B :=
  door3RealSegNext4_isCompact.exists_bound_of_continuousOn door3RealNext4ZetaContinuousOnSeg

/-- Chaining point: `4` lies in both tiles, so `[-1,4] ∪ [4,5] = [-1,5]`. -/
theorem door3RealSegNext4_meet :
    ((((4 : ℝ))) : ℂ) ∈ door3RealSegNext3 ∧
      ((((4 : ℝ))) : ℂ) ∈ door3RealSegNext4 := by
  simp only [door3RealSegNext3, door3RealSegNext4, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_Icc, Complex.ofReal_re, Complex.ofReal_im]
  norm_num

#print axioms door3RealSegNext4_witness
#print axioms door3RealSegNext4_isClosed
#print axioms door3RealSegNext4_isBounded
#print axioms door3RealSegNext4_isCompact
#print axioms door3RealSegNext4_in_open_strip
#print axioms door3RealNext4Shift_re
#print axioms door3RealNext4Shift_ne_one_of_seg
#print axioms door3RealNext4ZetaContinuousOnSeg
#print axioms exists_door3RealSegNext4_zetaUpper
#print axioms door3RealSegNext4_meet

/-!
## Door-3 remainder 5 fifth tile: `[5,6]` toward `(-10,10)` (2026-09-08, append-only)

Extends the committed `door3RealSegNext4` pattern (`[-1,5]` chained by
`door3RealSeg_next_meet` + `door3RealSegNext2_meet` + `door3RealSegNext3_meet` +
`door3RealSegNext4_meet`) one step further to `[-1,6]`. Same critical-line
shape (`Re s = 1/2` via `tailShiftedSReal_re`), pole avoidance (`Re s = 1/2`,
so `differentiableAt_riemannZeta` applies), continuity, plus an upper
enclosure on the new fifth tile (one-liner
`IsCompact.exists_bound_of_continuousOn`, as in committed
`exists_door3RealSeg_zetaUpper`).

Height-`t != 0` scope verdict (2026-09-08, Mathlib-visible only): NO Mathlib
lemma yields a lower bound `‖riemannZeta s‖ >= c > 0` (or nonvanishing) at any
point with `s.re = 1/2` and `s.im != 0`. Closest hits, all inapplicable on
the critical line:
- `riemannZeta_ne_zero_of_one_lt_re` (`Dirichlet.lean:328`, needs `1 < s.re`);
- `riemannZeta_ne_zero_of_one_le_re` (`Nonvanishing.lean:411`, needs
  `1 <= s.re`; junk value at `s = 1` handled by `riemannZeta_one_ne_zero`);
- `LFunction_ne_zero_of_re_eq_one` (`Nonvanishing.lean:385`, needs `s.re = 1`);
- `LFunction_ne_zero_of_one_le_re` (`Nonvanishing.lean:398`, needs `1 <= s.re`);
- `RiemannZeta.lean:186` is the Riemann-hypothesis *statement*
  (zeros imply `s.re = 1/2`), not an enclosure;
- value lemmas (`riemannZeta_zero`, `riemannZeta_four`,
  `riemannZeta_two_mul_nat`, `riemannZeta_neg_two_mul_nat_add_one`) are at
  isolated real/even points only;
- zero grep hits Mathlib-wide for `‖riemannZeta`, `ZeroFree`/`zeroFree`, or
  `1/2`-height zeta enclosures.
So the new-height pointwise LOWER bound (`c > 0` at `t = +-1/2`, or
nonvanishing at a meet point, via a kernel-checked enclosure) remains the
exact residual; this tile is the tightest proved step toward it.
-/

/-- Fifth compact tile toward `(-10,10)`: `5 ≤ Re z ≤ 6`, `Im z = 0`. -/
def door3RealSegNext5 : Set ℂ :=
  Complex.re ⁻¹' Set.Icc (5 : ℝ) 6 ∩ Complex.im ⁻¹' Set.Icc (0 : ℝ) 0

/-- Closed-rectangle membership for the fifth tile. -/
theorem door3RealSegNext5_mem_of_reim (z : ℂ) (hre1 : (5 : ℝ) ≤ z.re)
    (hre2 : z.re ≤ 6) (hlo : (0 : ℝ) ≤ z.im) (hhi : z.im ≤ 0) :
    z ∈ door3RealSegNext5 := by
  simp only [door3RealSegNext5, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc]
  exact ⟨⟨hre1, hre2⟩, hlo, hhi⟩

/-- Witness: `11/2` lies in the fifth tile. -/
theorem door3RealSegNext5_witness : ((((11 / 2 : ℝ))) : ℂ) ∈ door3RealSegNext5 := by
  simp only [door3RealSegNext5, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num

/-- The fifth tile is closed. -/
theorem door3RealSegNext5_isClosed : IsClosed door3RealSegNext5 := by
  unfold door3RealSegNext5
  exact (IsClosed.preimage Complex.continuous_re isClosed_Icc).inter
    (IsClosed.preimage Complex.continuous_im isClosed_Icc)

/-- The fifth tile lies in `closedBall 0 7`, hence is bounded. -/
theorem door3RealSegNext5_isBounded : Bornology.IsBounded door3RealSegNext5 := by
  apply Metric.isBounded_closedBall.subset
  intro z hz
  obtain ⟨⟨h1, h2⟩, hlo, hhi⟩ := hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have him : z.im = 0 := le_antisymm hhi hlo
  have habs : |z.re| ≤ 6 := by
    rw [abs_le]
    constructor
    · linarith
    · exact h2
  have hre2 : z.re * z.re ≤ (6 : ℝ) * 6 := by
    have h := mul_le_mul habs habs (abs_nonneg _) (show (0 : ℝ) ≤ 6 by norm_num)
    rwa [abs_mul_abs_self] at h
  have him2 : z.im * z.im ≤ (0 : ℝ) := by
    rw [him]
    norm_num
  have hnorm : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hle : ‖z‖ ^ 2 ≤ (7 : ℝ) ^ 2 := by
    rw [hnorm]
    have hsum := add_le_add hre2 him2
    have h49 : (6 : ℝ) * 6 + 0 ≤ 7 ^ 2 := by norm_num
    exact le_trans hsum h49
  exact le_of_sq_le_sq hle (by norm_num)

/-- The fifth tile is compact (Heine–Borel). -/
theorem door3RealSegNext5_isCompact : IsCompact door3RealSegNext5 := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨door3RealSegNext5_isClosed, door3RealSegNext5_isBounded⟩

/-- The fifth tile sits inside the required open slice `-10 < Re < 10`. -/
theorem door3RealSegNext5_in_open_strip (z : ℂ) (hz : z ∈ door3RealSegNext5) :
    (-10 : ℝ) < z.re ∧ z.re < 10 ∧ z.im = 0 := by
  obtain ⟨⟨h1, h2⟩, hlo, hhi⟩ := hz
  exact ⟨by linarith, by linarith, le_antisymm hhi hlo⟩

/-- Shifted real part on the fifth tile: `Re s = 1/2` (critical line). -/
theorem door3RealNext5Shift_re (z : ℂ) (hz : z ∈ door3RealSegNext5) :
    (tailShiftedSReal z).re = 1 / 2 := by
  obtain ⟨_, hlo, hhi⟩ := hz
  have him : z.im = 0 := le_antisymm hhi hlo
  rw [tailShiftedSReal_re, him]
  norm_num

/-- Pole avoidance on the fifth tile. -/
theorem door3RealNext5Shift_ne_one_of_seg (z : ℂ) (hz : z ∈ door3RealSegNext5) :
    tailShiftedSReal z ≠ 1 := by
  intro hcon
  have hre : (tailShiftedSReal z).re = (1 : ℂ).re := congrArg Complex.re hcon
  rw [door3RealNext5Shift_re z hz, Complex.one_re] at hre
  norm_num at hre

/-- Zeta pulled back through the shift is continuous on the fifth tile. -/
theorem door3RealNext5ZetaContinuousOnSeg :
    ContinuousOn (fun z => riemannZeta (tailShiftedSReal z)) door3RealSegNext5 := by
  intro x hx
  have hne : tailShiftedSReal x ≠ 1 := door3RealNext5Shift_ne_one_of_seg x hx
  have hdiff : DifferentiableAt ℂ riemannZeta (tailShiftedSReal x) :=
    differentiableAt_riemannZeta hne
  exact (hdiff.continuousAt.comp' tailShiftedSReal_continuous.continuousAt).continuousWithinAt

/-- Height upper enclosure over the fifth tile
(mirror of `exists_door3RealSeg_zetaUpper`). -/
theorem exists_door3RealSegNext5_zetaUpper :
    ∃ B : ℝ, ∀ z ∈ door3RealSegNext5,
      ‖riemannZeta (tailShiftedSReal z)‖ ≤ B :=
  door3RealSegNext5_isCompact.exists_bound_of_continuousOn door3RealNext5ZetaContinuousOnSeg

/-- Chaining point: `5` lies in both tiles, so `[-1,5] ∪ [5,6] = [-1,6]`. -/
theorem door3RealSegNext5_meet :
    ((((5 : ℝ))) : ℂ) ∈ door3RealSegNext4 ∧
      ((((5 : ℝ))) : ℂ) ∈ door3RealSegNext5 := by
  simp only [door3RealSegNext4, door3RealSegNext5, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_Icc, Complex.ofReal_re, Complex.ofReal_im]
  norm_num

#print axioms door3RealSegNext5_witness
#print axioms door3RealSegNext5_isClosed
#print axioms door3RealSegNext5_isBounded
#print axioms door3RealSegNext5_isCompact
#print axioms door3RealSegNext5_in_open_strip
#print axioms door3RealNext5Shift_re
#print axioms door3RealNext5Shift_ne_one_of_seg
#print axioms door3RealNext5ZetaContinuousOnSeg
#print axioms exists_door3RealSegNext5_zetaUpper
#print axioms door3RealSegNext5_meet

/-!
## Door-3 remainder 5 sixth tile: `[6,7]` + height-`1/2` enclosure attempt (2026-09-08, append-only)

Two parts, both FULLY PROVED below (no sorry/admit/axiom, `import Mathlib` only):

PART 1 — sixth compact tile toward `(-10,10)`: `6 ≤ Re z ≤ 7`, `Im z = 0`.
Extends the committed `door3RealSegNext5` pattern (`[-1,6]` chained by
`door3RealSeg_next_meet` + `door3RealSegNext2_meet` + `door3RealSegNext3_meet` +
`door3RealSegNext4_meet` + `door3RealSegNext5_meet`) one step further to
`[-1,7]`. Same critical-line shape (`Re s = 1/2` via `tailShiftedSReal_re`),
pole avoidance, continuity, upper enclosure
(`IsCompact.exists_bound_of_continuousOn`), witness `13/2`, `closedBall 0 8`,
meet point `6`.

PART 2 — direct kernel-checked enclosure ATTEMPT at `1/2 + I/2`
(= `tailShiftedSReal (((1/2:ℝ)):ℂ)`, since `Re s = 1/2 - Im z`,
`Im s = Re z`). The `door3_off_axis_certificates` module
(`FiniteZetaLowerCertificate`, `lower_of_re`, `zeta_lower_of_Sn_tail_factor`,
`zetaCell_even_remainder_le`) is OUTSIDE this file's `import Mathlib` closure,
so per task direction the needed eta bounds are reproved in-tail from
Mathlib-visible lemmas (R03/R05 slow+tail+factor pattern):
`d3EtaTerm` replica of `etaDirichletTerm`, two-term closed form `d3Eta_S2_eq`,
cleared-square rpow bounds `d3rpow_half_ge/le` (`7/5 ≤ 2^(1/2) ≤ 8/5`),
slow bound `d3Eta_S2_norm_ge` (`1/5 ≤ ‖S₂‖` by reverse triangle),
factor upper `d3EtaFactor_upper` (`‖1 - 2^(1-s)‖ ≤ 13/5`), factor
nonvanishing `d3EtaFactor_ne_zero`. TIGHTEST PROVED STEP: slow + factor at the
exact height-`1/2` point. RESIDUAL (honest, Mathlib-closure gap): the paired
tail estimate `‖G - S₂‖ ≤ rtail` (needs `etaPairTerm` summability/remainder
machinery) and the division bridge `ζ(s) = G/(1-2^(1-s))`, hence the final
`c₁ ≤ ‖ζ(1/2+I/2)‖` feeding `door3RealNonvan_of_lower` stays open.
-/

/-- Sixth compact tile toward `(-10,10)`: `6 ≤ Re z ≤ 7`, `Im z = 0`. -/
def door3RealSegNext6 : Set ℂ :=
  Complex.re ⁻¹' Set.Icc (6 : ℝ) 7 ∩ Complex.im ⁻¹' Set.Icc (0 : ℝ) 0

/-- Closed-rectangle membership for the sixth tile. -/
theorem door3RealSegNext6_mem_of_reim (z : ℂ) (hre1 : (6 : ℝ) ≤ z.re)
    (hre2 : z.re ≤ 7) (hlo : (0 : ℝ) ≤ z.im) (hhi : z.im ≤ 0) :
    z ∈ door3RealSegNext6 := by
  simp only [door3RealSegNext6, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc]
  exact ⟨⟨hre1, hre2⟩, hlo, hhi⟩

/-- Witness: `13/2` lies in the sixth tile. -/
theorem door3RealSegNext6_witness : ((((13 / 2 : ℝ))) : ℂ) ∈ door3RealSegNext6 := by
  simp only [door3RealSegNext6, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num

/-- The sixth tile is closed. -/
theorem door3RealSegNext6_isClosed : IsClosed door3RealSegNext6 := by
  unfold door3RealSegNext6
  exact (IsClosed.preimage Complex.continuous_re isClosed_Icc).inter
    (IsClosed.preimage Complex.continuous_im isClosed_Icc)

/-- The sixth tile lies in `closedBall 0 8`, hence is bounded. -/
theorem door3RealSegNext6_isBounded : Bornology.IsBounded door3RealSegNext6 := by
  apply Metric.isBounded_closedBall.subset
  intro z hz
  obtain ⟨⟨h1, h2⟩, hlo, hhi⟩ := hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have him : z.im = 0 := le_antisymm hhi hlo
  have habs : |z.re| ≤ 7 := by
    rw [abs_le]
    constructor
    · linarith
    · exact h2
  have hre2 : z.re * z.re ≤ (7 : ℝ) * 7 := by
    have h := mul_le_mul habs habs (abs_nonneg _) (show (0 : ℝ) ≤ 7 by norm_num)
    rwa [abs_mul_abs_self] at h
  have him2 : z.im * z.im ≤ (0 : ℝ) := by
    rw [him]
    norm_num
  have hnorm : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hle : ‖z‖ ^ 2 ≤ (8 : ℝ) ^ 2 := by
    rw [hnorm]
    have hsum := add_le_add hre2 him2
    have h64 : (7 : ℝ) * 7 + 0 ≤ 8 ^ 2 := by norm_num
    exact le_trans hsum h64
  exact le_of_sq_le_sq hle (by norm_num)

/-- The sixth tile is compact (Heine–Borel). -/
theorem door3RealSegNext6_isCompact : IsCompact door3RealSegNext6 := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨door3RealSegNext6_isClosed, door3RealSegNext6_isBounded⟩

/-- The sixth tile sits inside the required open slice `-10 < Re < 10`. -/
theorem door3RealSegNext6_in_open_strip (z : ℂ) (hz : z ∈ door3RealSegNext6) :
    (-10 : ℝ) < z.re ∧ z.re < 10 ∧ z.im = 0 := by
  obtain ⟨⟨h1, h2⟩, hlo, hhi⟩ := hz
  exact ⟨by linarith, by linarith, le_antisymm hhi hlo⟩

/-- Shifted real part on the sixth tile: `Re s = 1/2` (critical line). -/
theorem door3RealNext6Shift_re (z : ℂ) (hz : z ∈ door3RealSegNext6) :
    (tailShiftedSReal z).re = 1 / 2 := by
  obtain ⟨_, hlo, hhi⟩ := hz
  have him : z.im = 0 := le_antisymm hhi hlo
  rw [tailShiftedSReal_re, him]
  norm_num

/-- Pole avoidance on the sixth tile. -/
theorem door3RealNext6Shift_ne_one_of_seg (z : ℂ) (hz : z ∈ door3RealSegNext6) :
    tailShiftedSReal z ≠ 1 := by
  intro hcon
  have hre : (tailShiftedSReal z).re = (1 : ℂ).re := congrArg Complex.re hcon
  rw [door3RealNext6Shift_re z hz, Complex.one_re] at hre
  norm_num at hre

/-- Zeta pulled back through the shift is continuous on the sixth tile. -/
theorem door3RealNext6ZetaContinuousOnSeg :
    ContinuousOn (fun z => riemannZeta (tailShiftedSReal z)) door3RealSegNext6 := by
  intro x hx
  have hne : tailShiftedSReal x ≠ 1 := door3RealNext6Shift_ne_one_of_seg x hx
  have hdiff : DifferentiableAt ℂ riemannZeta (tailShiftedSReal x) :=
    differentiableAt_riemannZeta hne
  exact (hdiff.continuousAt.comp' tailShiftedSReal_continuous.continuousAt).continuousWithinAt

/-- Height upper enclosure over the sixth tile
(mirror of `exists_door3RealSeg_zetaUpper`). -/
theorem exists_door3RealSegNext6_zetaUpper :
    ∃ B : ℝ, ∀ z ∈ door3RealSegNext6,
      ‖riemannZeta (tailShiftedSReal z)‖ ≤ B :=
  door3RealSegNext6_isCompact.exists_bound_of_continuousOn door3RealNext6ZetaContinuousOnSeg

/-- Chaining point: `6` lies in both tiles, so `[-1,6] ∪ [6,7] = [-1,7]`. -/
theorem door3RealSegNext6_meet :
    ((((6 : ℝ))) : ℂ) ∈ door3RealSegNext5 ∧
      ((((6 : ℝ))) : ℂ) ∈ door3RealSegNext6 := by
  simp only [door3RealSegNext5, door3RealSegNext6, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_Icc, Complex.ofReal_re, Complex.ofReal_im]
  norm_num

/-- Height-`1/2` target: shifted real part at real `1/2` is `1/2`. -/
theorem d3HalfPt_re :
    (tailShiftedSReal (((1 / 2 : ℝ)) : ℂ)).re = 1 / 2 := by
  rw [tailShiftedSReal_re, Complex.ofReal_im, sub_zero]

/-- Height-`1/2` target: shifted imaginary part at real `1/2` is `1/2`. -/
theorem d3HalfPt_im :
    (tailShiftedSReal (((1 / 2 : ℝ)) : ℂ)).im = 1 / 2 := by
  rw [tailShiftedSReal_im, Complex.ofReal_re]

/-- Height-`1/2` target avoids the zeta pole at `1`. -/
theorem d3HalfPt_ne_one :
    tailShiftedSReal (((1 / 2 : ℝ)) : ℂ) ≠ 1 := by
  intro hcon
  have hre : (tailShiftedSReal (((1 / 2 : ℝ)) : ℂ)).re = (1 : ℂ).re :=
    congrArg Complex.re hcon
  rw [d3HalfPt_re, Complex.one_re] at hre
  norm_num at hre

/-- Height-`1/2` target lies in `closedBall 0 1`. -/
theorem d3HalfPt_norm_le :
    ‖tailShiftedSReal (((1 / 2 : ℝ)) : ℂ)‖ ≤ 1 := by
  have hsq : ‖tailShiftedSReal (((1 / 2 : ℝ)) : ℂ)‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, d3HalfPt_re, d3HalfPt_im]
    norm_num
  exact le_of_sq_le_sq hsq (by norm_num)

/-- In-tail Dirichlet eta term replica (mirror of `etaDirichletTerm`;
Mathlib-only closure, no import added). -/
noncomputable def d3EtaTerm (s : ℂ) (n : ℕ) : ℂ := (-1 : ℂ) ^ n / ((((n + 1 : ℕ)) : ℂ) ^ s)

/-- In-tail two-term eta partial sum in closed form (`S₂ = 1 - (2^s)⁻¹`,
mirror of `R03_eta_S2_eq`). -/
theorem d3Eta_S2_eq (s : ℂ) :
    (∑ k ∈ Finset.range 2, d3EtaTerm s k) = 1 - (((((2 : ℕ)) : ℂ) ^ s)⁻¹) := by
  have hsum : (∑ k ∈ Finset.range 2, d3EtaTerm s k) = d3EtaTerm s 0 + d3EtaTerm s 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
  have h0 : d3EtaTerm s 0 = 1 := by
    have h01 : (0 + 1 : ℕ) = 1 := rfl
    have hcast : ((((0 + 1 : ℕ)) : ℂ)) = 1 := by
      rw [h01, Nat.cast_one]
    simp only [d3EtaTerm, pow_zero, hcast, Complex.one_cpow, div_one]
  have h1 : d3EtaTerm s 1 = -((((((2 : ℕ)) : ℂ) ^ s)⁻¹)) := by
    unfold d3EtaTerm
    rw [pow_one]
    rw [show (((1 + 1 : ℕ) : ℂ)) = ((((2 : ℕ)) : ℂ)) by norm_num]
    rw [neg_div, one_div]
  rw [hsum, h0, h1]
  ring

/-- Cleared square: `(2^(1/2:ℝ))^2 = 2` (mirror of the R03/R05 rpow clearing). -/
theorem d3rpow_half_sq :
    (((((2 : ℝ) ^ ((1 / 2 : ℝ)))) ^ ((2 : ℕ)) : ℝ)) = 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show ((1 / 2 : ℝ)) * (((2 : ℕ)) : ℝ) = (1 : ℝ) by norm_num]
  exact Real.rpow_one 2

/-- Numeral rpow lower bound `7/5 ≤ 2^(1/2:ℝ)` (cleared: `(7/5)^2 ≤ 2`). -/
theorem d3rpow_half_ge : (7 / 5 : ℝ) ≤ (2 : ℝ) ^ ((1 / 2 : ℝ)) := by
  have hpow : ((7 / 5 : ℝ)) ^ ((2 : ℕ)) ≤
      (((((2 : ℝ) ^ ((1 / 2 : ℝ)))) ^ ((2 : ℕ)) : ℝ)) := by
    rw [d3rpow_half_sq]
    norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Numeral rpow upper bound `2^(1/2:ℝ) ≤ 8/5` (cleared: `2 ≤ (8/5)^2`). -/
theorem d3rpow_half_le : (2 : ℝ) ^ ((1 / 2 : ℝ)) ≤ (8 / 5 : ℝ) := by
  have hpow : (((((2 : ℝ) ^ ((1 / 2 : ℝ)))) ^ ((2 : ℕ)) : ℝ)) ≤
      ((8 / 5 : ℝ)) ^ ((2 : ℕ)) := by
    rw [d3rpow_half_sq]
    norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow

/-- Modulus of the height-`1/2` second eta term (`2^(-1/2) ≤ 4/5`,
mirror of `R03_eta_second_norm_le`). -/
theorem d3Eta_second_norm_le :
    ‖((((2 : ℕ)) : ℂ) ^ tailShiftedSReal (((1 / 2 : ℝ)) : ℂ))⁻¹‖ ≤ 4 / 5 := by
  have h2eq : ((((2 : ℕ)) : ℂ)) = (2 : ℂ) := by norm_cast
  have hnorm : ‖(2 : ℂ) ^ tailShiftedSReal (((1 / 2 : ℝ)) : ℂ)‖ =
      (2 : ℝ) ^ ((1 / 2 : ℝ)) := by
    have hbase := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)
      (tailShiftedSReal (((1 / 2 : ℝ)) : ℂ))
    rw [d3HalfPt_re] at hbase
    exact hbase
  rw [h2eq, norm_inv, hnorm]
  have hge := d3rpow_half_ge
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hInv : (((2 : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (((7 / 5 : ℝ)))⁻¹ :=
    (inv_le_inv₀ hpos (by norm_num)).mpr hge
  have heq : (((7 / 5 : ℝ)))⁻¹ ≤ (4 / 5 : ℝ) := by norm_num
  exact le_trans hInv heq

/-- In-tail finite-sum lower bound at height `1/2`
(`1/5 ≤ ‖S₂‖`, reverse triangle, mirror of `R03_eta_S2_norm_ge`). -/
theorem d3Eta_S2_norm_ge :
    (1 / 5 : ℝ) ≤
      ‖∑ k ∈ Finset.range 2, d3EtaTerm (tailShiftedSReal (((1 / 2 : ℝ)) : ℂ)) k‖ := by
  rw [d3Eta_S2_eq]
  have hX := d3Eta_second_norm_le
  have h := norm_add_le
    (1 - ((((2 : ℕ)) : ℂ) ^ tailShiftedSReal (((1 / 2 : ℝ)) : ℂ))⁻¹)
    (((((2 : ℕ)) : ℂ) ^ tailShiftedSReal (((1 / 2 : ℝ)) : ℂ))⁻¹)
  rw [sub_add_cancel] at h
  rw [norm_one] at h
  linarith

/-- Real part of the eta factor base at height `1/2`: `Re (1 - s) = 1/2`. -/
theorem d3HalfPt_one_sub_re :
    (((1 : ℂ) - tailShiftedSReal (((1 / 2 : ℝ)) : ℂ))).re = (1 / 2 : ℝ) := by
  rw [Complex.sub_re, Complex.one_re, d3HalfPt_re]
  norm_num

/-- In-tail eta-factor upper bound at height `1/2`
(`‖1 - 2^(1-s)‖ ≤ 13/5`, mirror of `R03_etaFactor_upper`). -/
theorem d3EtaFactor_upper :
    ‖(1 - (2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal (((1 / 2 : ℝ)) : ℂ)))‖ ≤
      13 / 5 := by
  have hY : ‖(2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal (((1 / 2 : ℝ)) : ℂ))‖ ≤
      8 / 5 := by
    have hnorm : ‖(2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal (((1 / 2 : ℝ)) : ℂ))‖ =
        (2 : ℝ) ^ ((((1 : ℂ) - tailShiftedSReal (((1 / 2 : ℝ)) : ℂ))).re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) _
    rw [hnorm, d3HalfPt_one_sub_re]
    exact d3rpow_half_le
  calc ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal (((1 / 2 : ℝ)) : ℂ))‖
        ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal (((1 / 2 : ℝ)) : ℂ))‖ :=
          norm_sub_le _ _
    _ ≤ 13 / 5 := by
          rw [norm_one]
          linarith [hY]

/-- In-tail eta-factor nonvanishing at height `1/2`
(mirror of `etaFactor_ne_zero_of_re_ne` at `Re = 1/2`). -/
theorem d3EtaFactor_ne_zero :
    (1 - (2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal (((1 / 2 : ℝ)) : ℂ))) ≠ 0 := by
  intro h
  have heq : (2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal (((1 / 2 : ℝ)) : ℂ)) = 1 :=
    (sub_eq_zero.mp h).symm
  have hnorm : ‖(2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal (((1 / 2 : ℝ)) : ℂ))‖ =
      ‖(1 : ℂ)‖ := congrArg (fun x : ℂ => ‖x‖) heq
  have hbase : ‖(2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal (((1 / 2 : ℝ)) : ℂ))‖ =
      (2 : ℝ) ^ ((1 / 2 : ℝ)) := by
    have hnorm2 : ‖(2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal (((1 / 2 : ℝ)) : ℂ))‖ =
        (2 : ℝ) ^ ((((1 : ℂ) - tailShiftedSReal (((1 / 2 : ℝ)) : ℂ))).re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) _
    rw [hnorm2, d3HalfPt_one_sub_re]
  rw [hbase, norm_one] at hnorm
  have hge := d3rpow_half_ge
  linarith

#print axioms door3RealSegNext6_witness
#print axioms door3RealSegNext6_isClosed
#print axioms door3RealSegNext6_isBounded
#print axioms door3RealSegNext6_isCompact
#print axioms door3RealSegNext6_in_open_strip
#print axioms door3RealNext6Shift_re
#print axioms door3RealNext6Shift_ne_one_of_seg
#print axioms door3RealNext6ZetaContinuousOnSeg
#print axioms exists_door3RealSegNext6_zetaUpper
#print axioms door3RealSegNext6_meet
#print axioms d3HalfPt_re
#print axioms d3HalfPt_im
#print axioms d3HalfPt_ne_one
#print axioms d3HalfPt_norm_le
#print axioms d3Eta_S2_eq
#print axioms d3rpow_half_sq
#print axioms d3rpow_half_ge
#print axioms d3rpow_half_le
#print axioms d3Eta_second_norm_le
#print axioms d3Eta_S2_norm_ge
#print axioms d3HalfPt_one_sub_re
#print axioms d3EtaFactor_upper
#print axioms d3EtaFactor_ne_zero

/-!
## Door-3 remainder 5 continued: tile `[7,8]` + mirrored slow/factor at `1/2-I/2` (2026-09-08, append-only)

Two FULLY PROVED parts (no sorry/admit/axiom, `import Mathlib` only):

PART (b) — seventh compact tile toward `(-10,10)`: `7 ≤ Re z ≤ 8`, `Im z = 0`.
Exact mirror of committed `door3RealSegNext6` (`6 ≤ Re ≤ 7`, witness `13/2`,
`closedBall 0 8`, meet `6`): witness `15/2`, `closedBall 0 9`, meet `7`,
chaining `[-1,7] ∪ [7,8] = [-1,8]`. Same critical-line shape
(`Re s = 1/2` via `tailShiftedSReal_re`), pole avoidance, continuity, upper
enclosure (`IsCompact.exists_bound_of_continuousOn`).

PART (a-fallback) — mirror of the committed height-`1/2` slow + factor block
(`d3Eta_S2_norm_ge` giving `1/5 ≤ ‖S₂‖`, `d3EtaFactor_upper` giving
`‖1 - 2^(1-s)‖ ≤ 13/5`, `d3EtaFactor_ne_zero`) at the conjugate point
`1/2 - I/2 = tailShiftedSReal ((((-1/2:ℝ)) : ℂ))` (so `Re s = 1/2`,
`Im s = -1/2`). Same cleared-square rpow bounds `d3rpow_half_ge/le` reused
(norm of `cpow` sees only `Re s = 1/2`).

RESIDUAL (honest): the in-tail paired-tail estimate `‖G - S₂‖ ≤ rtail` at
`1/2 ± I/2` (needs `etaPairTerm` summability/remainder machinery outside this
file's `import Mathlib` closure) and hence the division bridge
`ζ(s) = G/(1-2^(1-s))` yielding `(1/5-rtail)/(13/5) ≤ ‖ζ‖` to feed committed
`door3RealNonvan_of_lower` + `door3RealUniform_of_nonvan` stays open.
-/

/-- Seventh compact tile toward `(-10,10)`: `7 ≤ Re z ≤ 8`, `Im z = 0`. -/
def door3RealSegNext7 : Set ℂ :=
  Complex.re ⁻¹' Set.Icc (7 : ℝ) 8 ∩ Complex.im ⁻¹' Set.Icc (0 : ℝ) 0

/-- Closed-rectangle membership for the seventh tile. -/
theorem door3RealSegNext7_mem_of_reim (z : ℂ) (hre1 : (7 : ℝ) ≤ z.re)
    (hre2 : z.re ≤ 8) (hlo : (0 : ℝ) ≤ z.im) (hhi : z.im ≤ 0) :
    z ∈ door3RealSegNext7 := by
  simp only [door3RealSegNext7, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc]
  exact ⟨⟨hre1, hre2⟩, hlo, hhi⟩

/-- Witness: `15/2` lies in the seventh tile. -/
theorem door3RealSegNext7_witness : ((((15 / 2 : ℝ))) : ℂ) ∈ door3RealSegNext7 := by
  simp only [door3RealSegNext7, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num

/-- The seventh tile is closed. -/
theorem door3RealSegNext7_isClosed : IsClosed door3RealSegNext7 := by
  unfold door3RealSegNext7
  exact (IsClosed.preimage Complex.continuous_re isClosed_Icc).inter
    (IsClosed.preimage Complex.continuous_im isClosed_Icc)

/-- The seventh tile lies in `closedBall 0 9`, hence is bounded. -/
theorem door3RealSegNext7_isBounded : Bornology.IsBounded door3RealSegNext7 := by
  apply Metric.isBounded_closedBall.subset
  intro z hz
  obtain ⟨⟨h1, h2⟩, hlo, hhi⟩ := hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have him : z.im = 0 := le_antisymm hhi hlo
  have habs : |z.re| ≤ 8 := by
    rw [abs_le]
    constructor
    · linarith
    · exact h2
  have hre2 : z.re * z.re ≤ (8 : ℝ) * 8 := by
    have h := mul_le_mul habs habs (abs_nonneg _) (show (0 : ℝ) ≤ 8 by norm_num)
    rwa [abs_mul_abs_self] at h
  have him2 : z.im * z.im ≤ (0 : ℝ) := by
    rw [him]
    norm_num
  have hnorm : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hle : ‖z‖ ^ 2 ≤ (9 : ℝ) ^ 2 := by
    rw [hnorm]
    have hsum := add_le_add hre2 him2
    have h81 : (8 : ℝ) * 8 + 0 ≤ 9 ^ 2 := by norm_num
    exact le_trans hsum h81
  exact le_of_sq_le_sq hle (by norm_num)

/-- The seventh tile is compact (Heine–Borel). -/
theorem door3RealSegNext7_isCompact : IsCompact door3RealSegNext7 := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨door3RealSegNext7_isClosed, door3RealSegNext7_isBounded⟩

/-- The seventh tile sits inside the required open slice `-10 < Re < 10`. -/
theorem door3RealSegNext7_in_open_strip (z : ℂ) (hz : z ∈ door3RealSegNext7) :
    (-10 : ℝ) < z.re ∧ z.re < 10 ∧ z.im = 0 := by
  obtain ⟨⟨h1, h2⟩, hlo, hhi⟩ := hz
  exact ⟨by linarith, by linarith, le_antisymm hhi hlo⟩

/-- Shifted real part on the seventh tile: `Re s = 1/2` (critical line). -/
theorem door3RealNext7Shift_re (z : ℂ) (hz : z ∈ door3RealSegNext7) :
    (tailShiftedSReal z).re = 1 / 2 := by
  obtain ⟨_, hlo, hhi⟩ := hz
  have him : z.im = 0 := le_antisymm hhi hlo
  rw [tailShiftedSReal_re, him]
  norm_num

/-- Pole avoidance on the seventh tile. -/
theorem door3RealNext7Shift_ne_one_of_seg (z : ℂ) (hz : z ∈ door3RealSegNext7) :
    tailShiftedSReal z ≠ 1 := by
  intro hcon
  have hre : (tailShiftedSReal z).re = (1 : ℂ).re := congrArg Complex.re hcon
  rw [door3RealNext7Shift_re z hz, Complex.one_re] at hre
  norm_num at hre

/-- Zeta pulled back through the shift is continuous on the seventh tile. -/
theorem door3RealNext7ZetaContinuousOnSeg :
    ContinuousOn (fun z => riemannZeta (tailShiftedSReal z)) door3RealSegNext7 := by
  intro x hx
  have hne : tailShiftedSReal x ≠ 1 := door3RealNext7Shift_ne_one_of_seg x hx
  have hdiff : DifferentiableAt ℂ riemannZeta (tailShiftedSReal x) :=
    differentiableAt_riemannZeta hne
  exact (hdiff.continuousAt.comp' tailShiftedSReal_continuous.continuousAt).continuousWithinAt

/-- Height upper enclosure over the seventh tile
(mirror of `exists_door3RealSeg_zetaUpper`). -/
theorem exists_door3RealSegNext7_zetaUpper :
    ∃ B : ℝ, ∀ z ∈ door3RealSegNext7,
      ‖riemannZeta (tailShiftedSReal z)‖ ≤ B :=
  door3RealSegNext7_isCompact.exists_bound_of_continuousOn door3RealNext7ZetaContinuousOnSeg

/-- Chaining point: `7` lies in both tiles, so `[-1,7] ∪ [7,8] = [-1,8]`. -/
theorem door3RealSegNext7_meet :
    ((((7 : ℝ))) : ℂ) ∈ door3RealSegNext6 ∧
      ((((7 : ℝ))) : ℂ) ∈ door3RealSegNext7 := by
  simp only [door3RealSegNext6, door3RealSegNext7, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_Icc, Complex.ofReal_re, Complex.ofReal_im]
  norm_num

/-- Conjugate height target: shifted real part at real `-1/2` is `1/2`. -/
theorem d3HalfNegPt_re :
    (tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ)).re = 1 / 2 := by
  rw [tailShiftedSReal_re, Complex.ofReal_im, sub_zero]

/-- Conjugate height target: shifted imaginary part at real `-1/2` is `-1/2`. -/
theorem d3HalfNegPt_im :
    (tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ)).im = -1 / 2 := by
  rw [tailShiftedSReal_im, Complex.ofReal_re]

/-- Conjugate height target avoids the zeta pole at `1`. -/
theorem d3HalfNegPt_ne_one :
    tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ) ≠ 1 := by
  intro hcon
  have hre : (tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ)).re = (1 : ℂ).re :=
    congrArg Complex.re hcon
  rw [d3HalfNegPt_re, Complex.one_re] at hre
  norm_num at hre

/-- Conjugate height target lies in `closedBall 0 1`. -/
theorem d3HalfNegPt_norm_le :
    ‖tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ)‖ ≤ 1 := by
  have hsq : ‖tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ)‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, d3HalfNegPt_re, d3HalfNegPt_im]
    norm_num
  exact le_of_sq_le_sq hsq (by norm_num)

/-- Modulus of the conjugate second eta term (`2^(-1/2) ≤ 4/5`,
mirror of `d3Eta_second_norm_le`). -/
theorem d3Eta_second_norm_le_neg :
    ‖((((2 : ℕ)) : ℂ) ^ tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ))⁻¹‖ ≤ 4 / 5 := by
  have h2eq : ((((2 : ℕ)) : ℂ)) = (2 : ℂ) := by norm_cast
  have hnorm : ‖(2 : ℂ) ^ tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ)‖ =
      (2 : ℝ) ^ ((1 / 2 : ℝ)) := by
    have hbase := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)
      (tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ))
    rw [d3HalfNegPt_re] at hbase
    exact hbase
  rw [h2eq, norm_inv, hnorm]
  have hge := d3rpow_half_ge
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hInv : (((2 : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (((7 / 5 : ℝ)))⁻¹ :=
    (inv_le_inv₀ hpos (by norm_num)).mpr hge
  have heq : (((7 / 5 : ℝ)))⁻¹ ≤ (4 / 5 : ℝ) := by norm_num
  exact le_trans hInv heq

/-- In-tail finite-sum lower bound at the conjugate point
(`1/5 ≤ ‖S₂‖`, reverse triangle, mirror of `d3Eta_S2_norm_ge`). -/
theorem d3Eta_S2_norm_ge_neg :
    (1 / 5 : ℝ) ≤
      ‖∑ k ∈ Finset.range 2, d3EtaTerm (tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ)) k‖ := by
  rw [d3Eta_S2_eq]
  have hX := d3Eta_second_norm_le_neg
  have h := norm_add_le
    (1 - ((((2 : ℕ)) : ℂ) ^ tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ))⁻¹)
    (((((2 : ℕ)) : ℂ) ^ tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ))⁻¹)
  rw [sub_add_cancel] at h
  rw [norm_one] at h
  linarith

/-- Real part of the eta factor base at the conjugate point: `Re (1 - s) = 1/2`. -/
theorem d3HalfNegPt_one_sub_re :
    (((1 : ℂ) - tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ))).re = (1 / 2 : ℝ) := by
  rw [Complex.sub_re, Complex.one_re, d3HalfNegPt_re]
  norm_num

/-- In-tail eta-factor upper bound at the conjugate point
(`‖1 - 2^(1-s)‖ ≤ 13/5`, mirror of `d3EtaFactor_upper`). -/
theorem d3EtaFactor_upper_neg :
    ‖(1 - (2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ)))‖ ≤
      13 / 5 := by
  have hY : ‖(2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ))‖ ≤
      8 / 5 := by
    have hnorm : ‖(2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ))‖ =
        (2 : ℝ) ^ ((((1 : ℂ) - tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ))).re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) _
    rw [hnorm, d3HalfNegPt_one_sub_re]
    exact d3rpow_half_le
  calc ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ))‖
        ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ))‖ :=
          norm_sub_le _ _
    _ ≤ 13 / 5 := by
          rw [norm_one]
          linarith [hY]

/-- In-tail eta-factor nonvanishing at the conjugate point
(mirror of `d3EtaFactor_ne_zero` at `Re = 1/2`). -/
theorem d3EtaFactor_ne_zero_neg :
    (1 - (2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ))) ≠ 0 := by
  intro h
  have heq : (2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ)) = 1 :=
    (sub_eq_zero.mp h).symm
  have hnorm : ‖(2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ))‖ =
      ‖(1 : ℂ)‖ := congrArg (fun x : ℂ => ‖x‖) heq
  have hbase : ‖(2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ))‖ =
      (2 : ℝ) ^ ((1 / 2 : ℝ)) := by
    have hnorm2 : ‖(2 : ℂ) ^ ((1 : ℂ) - tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ))‖ =
        (2 : ℝ) ^ ((((1 : ℂ) - tailShiftedSReal ((((-1 / 2 : ℝ))) : ℂ))).re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) _
    rw [hnorm2, d3HalfNegPt_one_sub_re]
  rw [hbase, norm_one] at hnorm
  have hge := d3rpow_half_ge
  linarith

#print axioms door3RealSegNext7_witness
#print axioms door3RealSegNext7_isClosed
#print axioms door3RealSegNext7_isBounded
#print axioms door3RealSegNext7_isCompact
#print axioms door3RealSegNext7_in_open_strip
#print axioms door3RealNext7Shift_re
#print axioms door3RealNext7Shift_ne_one_of_seg
#print axioms door3RealNext7ZetaContinuousOnSeg
#print axioms exists_door3RealSegNext7_zetaUpper
#print axioms door3RealSegNext7_meet
#print axioms d3HalfNegPt_re
#print axioms d3HalfNegPt_im
#print axioms d3HalfNegPt_ne_one
#print axioms d3HalfNegPt_norm_le
#print axioms d3Eta_second_norm_le_neg
#print axioms d3Eta_S2_norm_ge_neg
#print axioms d3HalfNegPt_one_sub_re
#print axioms d3EtaFactor_upper_neg
#print axioms d3EtaFactor_ne_zero_neg

/-!
## Door-3 remainder 5 (paired-tail step 1): in-tail pair term + cleared rpow bound

In-tail `d3EtaPairTerm` replica of `etaPairTerm`, pair-zero identity
(`pair 0 = S₂`), and cleared-square rpow bound `5/3 ≤ 3^(1/2:ℝ)`
feeding the `m = 1` pair estimate at height `1/2`.
-/

/-- In-tail paired eta increment replica (mirror of `etaPairTerm`). -/
noncomputable def d3EtaPairTerm (s : ℂ) (m : ℕ) : ℂ :=
  d3EtaTerm s (2 * m) + d3EtaTerm s (2 * m + 1)

/-- Pair zero unfolds to the first two Dirichlet terms. -/
theorem d3EtaPair_zero_eq (s : ℂ) :
    d3EtaPairTerm s 0 = d3EtaTerm s 0 + d3EtaTerm s 1 := by
  unfold d3EtaPairTerm
  rw [show (2 * 0 : ℕ) = 0 by norm_num, show (2 * 0 + 1 : ℕ) = 1 by norm_num]

/-- Pair zero equals the two-term partial sum `S₂`. -/
theorem d3EtaPair_zero_eq_S2 (s : ℂ) :
    d3EtaPairTerm s 0 = ∑ k ∈ Finset.range 2, d3EtaTerm s k := by
  have hsum : (∑ k ∈ Finset.range 2, d3EtaTerm s k) =
      d3EtaTerm s 0 + d3EtaTerm s 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
  rw [hsum]
  exact d3EtaPair_zero_eq s

/-- Cleared square: `(3^(1/2:ℝ))^2 = 3`. -/
theorem d3rpow_sqrt3_sq :
    (((((3 : ℝ) ^ ((1 / 2 : ℝ)))) ^ ((2 : ℕ)) : ℝ)) = 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  rw [show ((1 / 2 : ℝ)) * (((2 : ℕ)) : ℝ) = (1 : ℝ) by norm_num]
  exact Real.rpow_one 3

/-- Numeral rpow lower bound `5/3 ≤ 3^(1/2:ℝ)` (cleared: `(5/3)^2 ≤ 3`). -/
theorem d3rpow_sqrt3_ge : (5 / 3 : ℝ) ≤ (3 : ℝ) ^ ((1 / 2 : ℝ)) := by
  have hpow : ((5 / 3 : ℝ)) ^ ((2 : ℕ)) ≤
      (((((3 : ℝ) ^ ((1 / 2 : ℝ)))) ^ ((2 : ℕ)) : ℝ)) := by
    rw [d3rpow_sqrt3_sq]
    norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Numeral rpow lower bound `2 ≤ 4^(1/2:ℝ)` (cleared: `2^2 ≤ 4`). -/
theorem d3rpow_four_half_ge : (2 : ℝ) ≤ (4 : ℝ) ^ ((1 / 2 : ℝ)) := by
  have hsq : (((((4 : ℝ) ^ ((1 / 2 : ℝ)))) ^ ((2 : ℕ)) : ℝ)) = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show ((1 / 2 : ℝ)) * (((2 : ℕ)) : ℝ) = (1 : ℝ) by norm_num]
    exact Real.rpow_one 4
  have hpow : ((2 : ℝ)) ^ ((2 : ℕ)) ≤
      (((((4 : ℝ) ^ ((1 / 2 : ℝ)))) ^ ((2 : ℕ)) : ℝ)) := by
    rw [hsq]
    norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- Modulus of the height-`1/2` third eta term (`3^(-1/2) ≤ 3/5`). -/
theorem d3Eta_term2_norm_le :
    ‖d3EtaTerm (tailShiftedSReal (((1 / 2 : ℝ)) : ℂ)) 2‖ ≤ 3 / 5 := by
  have hcast : ((((3 : ℕ)) : ℂ)) = (((3 : ℝ)) : ℂ) := by norm_cast
  have hnorm : ‖((((3 : ℕ)) : ℂ) ^ tailShiftedSReal (((1 / 2 : ℝ)) : ℂ))‖ =
      (3 : ℝ) ^ ((1 / 2 : ℝ)) := by
    rw [hcast]
    have hbase := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 3)
      (tailShiftedSReal (((1 / 2 : ℝ)) : ℂ))
    rw [d3HalfPt_re] at hbase
    exact hbase
  have hterm : d3EtaTerm (tailShiftedSReal (((1 / 2 : ℝ)) : ℂ)) 2 =
      (-1 : ℂ) ^ (2 : ℕ) /
        ((((3 : ℕ)) : ℂ) ^ tailShiftedSReal (((1 / 2 : ℝ)) : ℂ)) := by
    unfold d3EtaTerm
    rw [show ((((2 + 1 : ℕ)) : ℂ)) = ((((3 : ℕ)) : ℂ)) by norm_num]
  have hneg : ‖((-1 : ℂ) ^ (2 : ℕ))‖ = 1 := by
    have h1 : ‖(-1 : ℂ)‖ = 1 := by
      rw [norm_neg, norm_one]
    rw [norm_pow, h1, one_pow]
  rw [hterm, norm_div, hneg, hnorm]
  have hge := d3rpow_sqrt3_ge
  have hpos : (0 : ℝ) < (3 : ℝ) ^ ((1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hInv : (((3 : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (((5 / 3 : ℝ)))⁻¹ :=
    (inv_le_inv₀ hpos (by norm_num)).mpr hge
  have heq : (((5 / 3 : ℝ)))⁻¹ ≤ (3 / 5 : ℝ) := by norm_num
  have hdiv : (1 : ℝ) / ((3 : ℝ) ^ ((1 / 2 : ℝ))) =
      (((3 : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ := by
    rw [one_div]
  rw [hdiv]
  exact le_trans hInv heq

/-- Pair one unfolds to the third and fourth Dirichlet terms. -/
theorem d3EtaPair_one_eq (s : ℂ) :
    d3EtaPairTerm s 1 = d3EtaTerm s 2 + d3EtaTerm s 3 := by
  unfold d3EtaPairTerm
  rw [show (2 * 1 : ℕ) = 2 by norm_num, show (2 * 1 + 1 : ℕ) = 3 by norm_num]

/-- Modulus of the height-`1/2` fourth eta term (`4^(-1/2) ≤ 1/2`). -/
theorem d3Eta_term3_norm_le :
    ‖d3EtaTerm (tailShiftedSReal (((1 / 2 : ℝ)) : ℂ)) 3‖ ≤ 1 / 2 := by
  have hcast : ((((4 : ℕ)) : ℂ)) = (((4 : ℝ)) : ℂ) := by norm_cast
  have hnorm : ‖((((4 : ℕ)) : ℂ) ^ tailShiftedSReal (((1 / 2 : ℝ)) : ℂ))‖ =
      (4 : ℝ) ^ ((1 / 2 : ℝ)) := by
    rw [hcast]
    have hbase := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 4)
      (tailShiftedSReal (((1 / 2 : ℝ)) : ℂ))
    rw [d3HalfPt_re] at hbase
    exact hbase
  have hterm : d3EtaTerm (tailShiftedSReal (((1 / 2 : ℝ)) : ℂ)) 3 =
      (-1 : ℂ) ^ (3 : ℕ) /
        ((((4 : ℕ)) : ℂ) ^ tailShiftedSReal (((1 / 2 : ℝ)) : ℂ)) := by
    unfold d3EtaTerm
    rw [show ((((3 + 1 : ℕ)) : ℂ)) = ((((4 : ℕ)) : ℂ)) by norm_num]
  have hneg : ‖((-1 : ℂ) ^ (3 : ℕ))‖ = 1 := by
    have h1 : ‖(-1 : ℂ)‖ = 1 := by
      rw [norm_neg, norm_one]
    rw [norm_pow, h1, one_pow]
  rw [hterm, norm_div, hneg, hnorm]
  have hge := d3rpow_four_half_ge
  have hpos : (0 : ℝ) < (4 : ℝ) ^ ((1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hInv : (((4 : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ ((2 : ℝ))⁻¹ :=
    (inv_le_inv₀ hpos (by norm_num)).mpr hge
  have heq : ((2 : ℝ))⁻¹ ≤ (1 / 2 : ℝ) := by norm_num
  have hdiv : (1 : ℝ) / ((4 : ℝ) ^ ((1 / 2 : ℝ))) =
      (((4 : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ := by
    rw [one_div]
  rw [hdiv]
  exact le_trans hInv heq

/-- In-tail pair estimate at height `1/2`: `‖pair 1‖ ≤ 11/10`
(triangle on the third and fourth Dirichlet terms). -/
theorem d3EtaPair_one_norm_le :
    ‖d3EtaPairTerm (tailShiftedSReal (((1 / 2 : ℝ)) : ℂ)) 1‖ ≤ 11 / 10 := by
  rw [d3EtaPair_one_eq]
  have h2 := d3Eta_term2_norm_le
  have h3 := d3Eta_term3_norm_le
  have htri := norm_add_le (d3EtaTerm (tailShiftedSReal (((1 / 2 : ℝ)) : ℂ)) 2)
    (d3EtaTerm (tailShiftedSReal (((1 / 2 : ℝ)) : ℂ)) 3)
  linarith

#print axioms d3EtaPair_zero_eq
#print axioms d3EtaPair_zero_eq_S2
#print axioms d3rpow_sqrt3_sq
#print axioms d3rpow_sqrt3_ge
#print axioms d3rpow_four_half_ge
#print axioms d3Eta_term2_norm_le
#print axioms d3EtaPair_one_eq
#print axioms d3Eta_term3_norm_le
#print axioms d3EtaPair_one_norm_le

/-!
## Door-3 remainder 5 (paired-tail step 2a): in-tail pair cpow-difference form

Helpers reproved in-tail (mirror of `zeta_rigorous` `etaDirichletTerm_eq_cpow_neg`
+ `etaPairTerm_eq_cpow_sub`, no import added): `(-1)^(2k)=1`,
`(-1)^(2k+1)=-1`, term cpow-neg form, pair cpow-difference form.
-/

/-- In-tail `(-1)^(2k) = 1` over `ℂ`. -/
theorem d3_neg_one_pow_two_mul (k : ℕ) : ((-1 : ℂ) ^ (2 * k) = 1) := by
  rw [pow_mul]
  simp

/-- In-tail `(-1)^(2k+1) = -1` over `ℂ`. -/
theorem d3_neg_one_pow_two_mul_add_one (k : ℕ) : ((-1 : ℂ) ^ (2 * k + 1) = -1) := by
  rw [pow_add, d3_neg_one_pow_two_mul k, pow_one, one_mul]

/-- In-tail Dirichlet eta term in cpow-neg form. -/
theorem d3EtaTerm_eq_cpow_neg (s : ℂ) (n : ℕ) :
    d3EtaTerm s n = (-1 : ℂ) ^ n * (((((n : ℝ) + 1 : ℝ))) : ℂ) ^ (-s) := by
  have hcast : ((((n + 1 : ℕ) : ℂ))) = (((((n : ℝ) + 1 : ℝ))) : ℂ) := by
    push_cast
    ring
  unfold d3EtaTerm
  rw [hcast, div_eq_mul_inv, ← Complex.cpow_neg]

/-- In-tail pair in cpow-difference form. -/
theorem d3EtaPair_eq_cpow_sub (s : ℂ) (m : ℕ) :
    d3EtaPairTerm s m
      = (((((2 * m + 1 : ℕ) : ℝ)) : ℂ) ^ (-s))
        - (((((2 * m + 2 : ℕ) : ℝ)) : ℂ) ^ (-s)) := by
  have e0 := d3EtaTerm_eq_cpow_neg s (2 * m)
  have e1 := d3EtaTerm_eq_cpow_neg s (2 * m + 1)
  have hcast0 : ((((2 * m : ℕ) : ℝ) + 1 : ℝ)) = ((((2 * m + 1 : ℕ) : ℝ))) := by
    push_cast
    ring
  have hcast1 : ((((2 * m + 1 : ℕ) : ℝ) + 1 : ℝ)) = ((((2 * m + 2 : ℕ) : ℝ))) := by
    push_cast
    ring
  unfold d3EtaPairTerm
  rw [e0, e1, d3_neg_one_pow_two_mul, d3_neg_one_pow_two_mul_add_one, hcast0,
    hcast1]
  ring

#print axioms d3_neg_one_pow_two_mul
#print axioms d3_neg_one_pow_two_mul_add_one
#print axioms d3EtaTerm_eq_cpow_neg
#print axioms d3EtaPair_eq_cpow_sub

/-- In-tail mean-value pair bound
`‖pair m‖ ≤ ‖s‖ * (2m+1)^{-Re s - 1}` (`0 < Re s`; mirror of
`zeta_rigorous.norm_etaPairTerm_le`, reproved in-tail via
`Convex.norm_image_sub_le_of_norm_deriv_le`). -/
theorem d3EtaPair_norm_le (s : ℂ) (hs : 0 < s.re) (m : ℕ) :
    ‖d3EtaPairTerm s m‖ ≤ ‖s‖ * (((((2 * m + 1 : ℕ) : ℝ)) ^ (-s.re - 1))) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    exact lt_irrefl _ hs
  have hnegs : -s ≠ 0 := neg_ne_zero.mpr hs0
  set a : ℝ := (((2 * m + 1 : ℕ) : ℝ)) with ha
  set b : ℝ := (((2 * m + 2 : ℕ) : ℝ)) with hb
  have ha_pos : (0 : ℝ) < a := by
    rw [ha]
    exact Nat.cast_pos.mpr (by omega)
  have hab : a ≤ b := by
    rw [ha, hb]
    exact Nat.cast_le.mpr (by omega)
  have hb_eq : b = a + 1 := by
    rw [ha, hb]
    have heq : 2 * m + 1 + 1 = 2 * m + 2 := by omega
    calc ((((2 * m + 2 : ℕ)) : ℝ))
        = ((((2 * m + 1 + 1 : ℕ)) : ℝ)) := by rw [heq]
      _ = ((((2 * m + 1 : ℕ)) : ℝ)) + 1 := by rw [Nat.cast_add, Nat.cast_one]
  have hpair : d3EtaPairTerm s m = (a : ℂ) ^ (-s) - (b : ℂ) ^ (-s) := by
    rw [d3EtaPair_eq_cpow_sub]
  have hdiff : ∀ x ∈ Set.Icc a b,
      DifferentiableAt ℝ (fun t : ℝ => (t : ℂ) ^ (-s)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha_pos (Set.mem_Icc.mp hx).1
    exact (hasDerivAt_ofReal_cpow_const (ne_of_gt hx0) hnegs).differentiableAt
  have hderiv_eq : ∀ x : ℝ, x ≠ 0 →
      deriv (fun t : ℝ => (t : ℂ) ^ (-s)) x = (-s) * (x : ℂ) ^ (-s - 1) := by
    intro x hx0
    exact Complex.deriv_ofReal_cpow_const hx0 hnegs
  have hexp_nonpos : -s.re - 1 ≤ 0 := by linarith
  have hbound : ∀ x ∈ Set.Icc a b, ‖deriv (fun t : ℝ => (t : ℂ) ^ (-s)) x‖
      ≤ ‖s‖ * (a ^ (-s.re - 1)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha_pos (Set.mem_Icc.mp hx).1
    have hax : a ≤ x := (Set.mem_Icc.mp hx).1
    rw [hderiv_eq x (ne_of_gt hx0)]
    have hnorm_cpow : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ ((-s - 1).re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos hx0 _
    have hre : ((-s - 1).re) = -s.re - 1 := by
      rw [Complex.sub_re, Complex.neg_re, Complex.one_re]
    have hle : x ^ (-s.re - 1) ≤ a ^ (-s.re - 1) :=
      Real.rpow_le_rpow_of_nonpos ha_pos hax hexp_nonpos
    calc ‖-s * (x : ℂ) ^ (-s - 1)‖
        = ‖s‖ * (x ^ (-s.re - 1)) := by
          rw [norm_mul, norm_neg, hnorm_cpow, hre]
      _ ≤ ‖s‖ * (a ^ (-s.re - 1)) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_Icc a b) (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  have hba : ‖b - a‖ = 1 := by
    have hsub : b - a = 1 := by rw [hb_eq]; ring
    rw [hsub, norm_one]
  rw [hba, mul_one] at hmvt
  have hrev : ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖
      = ‖(b : ℂ) ^ (-s) - (a : ℂ) ^ (-s)‖ := norm_sub_rev _ _
  rw [hpair, hrev]
  exact hmvt

#print axioms d3EtaPair_norm_le

/-- In-tail paired series is summable at `Re = 1/2` (M-test vs `p = 3/2 > 1`;
mirror of `zeta_rigorous.summable_etaPairTerm`). -/
theorem summable_d3EtaPair (s : ℂ) (hs : s.re = 1 / 2) :
    Summable (d3EtaPairTerm s) := by
  have hspos : 0 < s.re := by rw [hs]; norm_num
  have hp1 : (1 : ℝ) < s.re + 1 := by rw [hs]; norm_num
  have hbase : Summable (fun n : ℕ => ((((n : ℝ)) ^ (s.re + 1)))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hp1
  have hshift : Summable (fun m : ℕ => ((((m + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹) :=
    (summable_nat_add_iff 1).mpr hbase
  have hC : Summable (fun m : ℕ => ‖s‖ * ((((m + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹) :=
    hshift.mul_left _
  refine Summable.of_norm_bounded hC (fun m => ?_)
  have hle1 := d3EtaPair_norm_le s hspos m
  have ha_pos : (0 : ℝ) < ((((2 * m + 1 : ℕ)) : ℝ)) := Nat.cast_pos.mpr (by omega)
  have hm_pos : (0 : ℝ) < ((((m + 1 : ℕ)) : ℝ)) := Nat.cast_pos.mpr (by omega)
  have hm_le : ((((m + 1 : ℕ)) : ℝ)) ≤ ((((2 * m + 1 : ℕ)) : ℝ)) :=
    Nat.cast_le.mpr (by omega)
  have hexp_nonneg : (0 : ℝ) ≤ s.re + 1 := by linarith
  have hrpow_eq : ((((2 * m + 1 : ℕ) : ℝ)) ^ (-s.re - 1))
      = ((((2 * m + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹ := by
    have e : -s.re - 1 = -(s.re + 1) := by ring
    rw [e]
    exact Real.rpow_neg (Nat.cast_nonneg _) _
  have hrpow_le : ((((2 * m + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹
      ≤ ((((m + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹ := by
    apply (inv_le_inv₀ (Real.rpow_pos_of_pos ha_pos _)
      (Real.rpow_pos_of_pos hm_pos _)).mpr
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hm_le hexp_nonneg
  calc ‖d3EtaPairTerm s m‖ ≤ ‖s‖ * ((((2 * m + 1 : ℕ) : ℝ)) ^ (-s.re - 1)) := hle1
    _ = ‖s‖ * ((((2 * m + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹ := by rw [hrpow_eq]
    _ ≤ ‖s‖ * ((((m + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹ :=
        mul_le_mul_of_nonneg_left hrpow_le (norm_nonneg _)

#print axioms summable_d3EtaPair

/-!
## Door-3 remainder 5 (paired-tail step 3a): M=1 tail-shift identity

`∑' m, pair (m+1) = G - S₂` via `Summable.sum_add_tsum_nat_add` at `k = 1`
plus the committed `d3EtaPair_zero_eq_S2`.
-/

/-- Height-`1/2` in-tail base point. -/
noncomputable abbrev d3HalfS0 : ℂ := tailShiftedSReal (((1 / 2 : ℝ)) : ℂ)

/-- M=1 paired-tail shift: the shifted tsum is the full paired sum minus
the two-term partial sum `S₂`. -/
theorem d3Pair_tail_eq (s : ℂ) (hs : Summable (d3EtaPairTerm s)) :
    (∑' m, d3EtaPairTerm s (m + 1))
      = (∑' m, d3EtaPairTerm s m) - ∑ k ∈ Finset.range 2, d3EtaTerm s k := by
  have h1 := hs.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at h1
  have heq : (∑' i, d3EtaPairTerm s (i + 1))
      = (∑' i, d3EtaPairTerm s i) - d3EtaPairTerm s 0 := by
    rw [← h1]
    exact (add_sub_cancel_left _ _).symm
  have hpair0 := d3EtaPair_zero_eq_S2 s
  rw [heq, hpair0]

#print axioms d3Pair_tail_eq

/-- Zeta lower bound from a paired-tail bound: with `‖G - S₂‖ ≤ rtail < 1/5`
and the eta bridge `G = (1 - 2^(1-s₀)) * ζ(s₀)`, reverse-triangle on the
committed `1/5 ≤ ‖S₂‖` plus the committed factor cap `13/5` yields
`(1/5 - rtail)/(13/5) ≤ ‖ζ(s₀)‖` for `door3RealNonvan_of_lower`. -/
theorem d3Zeta_lower_of_tail (rtail : ℝ) (hrt : rtail < 1 / 5)
    (hTail : ‖∑' m, d3EtaPairTerm d3HalfS0 (m + 1)‖ ≤ rtail)
    (hZeta : (∑' m, d3EtaPairTerm d3HalfS0 m)
      = (1 - (2 : ℂ) ^ ((1 : ℂ) - d3HalfS0)) * riemannZeta d3HalfS0) :
    (1 / 5 - rtail) / (13 / 5) ≤ ‖riemannZeta d3HalfS0‖ := by
  have hre : d3HalfS0.re = 1 / 2 := d3HalfPt_re
  have hS2 : (1 / 5 : ℝ) ≤ ‖∑ k ∈ Finset.range 2, d3EtaTerm d3HalfS0 k‖ :=
    d3Eta_S2_norm_ge
  have hFac : ‖(1 - (2 : ℂ) ^ ((1 : ℂ) - d3HalfS0))‖ ≤ 13 / 5 :=
    d3EtaFactor_upper
  have hshift := d3Pair_tail_eq d3HalfS0 (summable_d3EtaPair d3HalfS0 hre)
  have htri : ‖∑ k ∈ Finset.range 2, d3EtaTerm d3HalfS0 k‖
      ≤ ‖∑' m, d3EtaPairTerm d3HalfS0 m‖ + rtail := by
    have hdecomp : (∑ k ∈ Finset.range 2, d3EtaTerm d3HalfS0 k)
        = (∑' m, d3EtaPairTerm d3HalfS0 m)
          - (∑' m, d3EtaPairTerm d3HalfS0 (m + 1)) := by
      rw [hshift]
      ring
    calc ‖∑ k ∈ Finset.range 2, d3EtaTerm d3HalfS0 k‖
        = ‖(∑' m, d3EtaPairTerm d3HalfS0 m)
          - (∑' m, d3EtaPairTerm d3HalfS0 (m + 1))‖ := by rw [hdecomp]
      _ ≤ ‖∑' m, d3EtaPairTerm d3HalfS0 m‖
          + ‖∑' m, d3EtaPairTerm d3HalfS0 (m + 1)‖ := norm_sub_le _ _
      _ ≤ ‖∑' m, d3EtaPairTerm d3HalfS0 m‖ + rtail := by linarith [hTail]
  have hGle : ‖∑' m, d3EtaPairTerm d3HalfS0 m‖
      ≤ (13 / 5) * ‖riemannZeta d3HalfS0‖ := by
    rw [hZeta, norm_mul]
    exact mul_le_mul_of_nonneg_right hFac (norm_nonneg _)
  have hkey : (1 / 5 - rtail) ≤ (13 / 5) * ‖riemannZeta d3HalfS0‖ := by
    linarith [hS2, htri, hGle]
  have : 0 < (1 / 5 : ℝ) - rtail := by linarith
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 13 / 5)]
  rw [mul_comm]
  exact hkey

#print axioms d3Zeta_lower_of_tail
