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
