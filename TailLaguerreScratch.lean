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
