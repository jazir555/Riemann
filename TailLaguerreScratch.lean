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
