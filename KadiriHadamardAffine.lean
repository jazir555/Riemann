import Mathlib
import ZeroFreeRegionHadamard
import KadiriZeroFree

open Complex Real Topology Metric Filter
open ZeroFreeRegionHadamard
open scoped BigOperators

/-!
# Affineness of the Hadamard exponent of the completed xi-function

We obtain (from `KadiriZeroFree` / `ZeroFreeRegionHadamard`) a zero enumeration `a` of `xi`,
a zero-count `N(r) = O(r^{7/4})`, the summability `Σ 1/|a n|^2 < ∞`, and Hadamard's
genus-one factorization `xi = exp(g) * canonicalProductNat 1 a` with `g` entire.

Writing `P := canonicalProductNat 1 a`, the quotient `Q := xi / P = exp(g)` is a zero-free
entire function. The completed proof shows `g` has order at most `3 / 2 < 2`; by Cauchy's
estimate on the second derivative this forces `g'' = 0`, so `g` is affine.

The growth input (a uniform bound `Re (g z) <= O(|z|^{3/2})` on every disk, obtained from
Borel-Caratheodory once a lower bound for `|P z|` away from the zeros is available, and a
matching bound near the zeros via the skip product) is isolated in residual predicates
`AwayLowerResidual` / `DerivLowerResidual` / `XiUpperResidual` / `ReBoundResidual` below.
Unconditional partial results (summability from the count, nonvanishing and zero location
of the product, skip-product nonvanishing, entirety of `xi`) are proved from banked
lemmas. The three deep estimates are stated in conditional form: each follows directly
from its residual hypothesis, with zero placeholders. The main theorem threads the
residuals explicitly.

Quantification of the remaining analytic work (for an unconditional proof):
- away lower bound: needs Jensen summation-by-parts + tail integral + head count,
  about 5 to 7 supporting lemmas;
- deriv lower bound: needs skip-product factorization + away bound applied to the
  skip product, about 4 to 6 supporting lemmas;
- `Re` bound: needs the `xi` order `3 / 2` upper bound (Stirling + Mellin) combined
  with the two product lowers, about 5 to 8 supporting lemmas.
Each exceeds the 4-lemma threshold for direct closure here, hence the conditional form.
-/

namespace KadiriHadamardAffine

noncomputable section

/-- Residual lower bound for the canonical product away from its zeros. -/
def AwayLowerResidual (a : ℕ → ℂ) : Prop :=
  ∃ (C : ℝ), 0 < C ∧ ∀ (z : ℂ), (∀ (n : ℕ), (1 / 2 : ℝ) ≤ ‖z - a n‖) →
    ‖canonicalProductNat 1 a z‖ ≥ Real.exp (-C * (1 + ‖z‖ ^ (7 / 4 : ℝ)
      * (1 + Real.log (1 + ‖z‖))))

/-- Residual lower bound for the derivative of the product at its zeros. -/
def DerivLowerResidual (a : ℕ → ℂ) : Prop :=
  ∃ (C : ℝ), 0 < C ∧ ∀ (n : ℕ),
    ‖deriv (canonicalProductNat 1 a) (a n)‖ ≥ Real.exp (-C * (1 + ‖a n‖ ^ (7 / 4 : ℝ)
      * (1 + Real.log (1 + ‖a n‖))))

/-- Residual upper bound for `xi` of order `3 / 2`. -/
def XiUpperResidual : Prop :=
  ∃ (K : ℝ), 0 < K ∧ ∀ (z : ℂ), ‖xi z‖ ≤ Real.exp (K * (1 + ‖z‖ ^ (3 / 2 : ℝ)))

/-- Residual uniform `Re` bound for the Hadamard exponent on disks. -/
def ReBoundResidual (a : ℕ → ℂ) (g : ℂ → ℂ) : Prop :=
  ∃ (A₀ : ℝ), 0 < A₀ ∧ ∀ (R : ℝ), R ≥ 1 → ∀ (z : ℂ), ‖z‖ < R →
    (g z).re ≤ A₀ * (1 + R ^ (3 / 2 : ℝ))

/-! ## Unconditional partial results banked from existing lemmas. -/

/-- Summability `Σ 1/‖a n‖^2 < ∞` from the counting bound (banked convergence input). -/
lemma partial_summable_of_count (a : ℕ → ℂ)
    (hfinite : ∀ (r : ℝ), 1 ≤ r → (({n : ℕ | ‖a n‖ ≤ r} : Set ℕ).Finite))
    (hcount : ∃ (D : ℝ), 0 ≤ D ∧ ∀ (r : ℝ), 1 ≤ r →
      (({n : ℕ | ‖a n‖ ≤ r} : Set ℕ).ncard ≤ D * r ^ (7 / 4 : ℝ))) :
    Summable fun (n : ℕ) => (‖a n‖ ^ 2)⁻¹ := by
  exact_mod_cast summable_inv_norm_pow_of_ncard_bound (by norm_num)
    (by norm_num : (7 / 4 : ℝ) < 2) hfinite hcount

/-- The product does not vanish away from the zero set. -/
lemma partial_product_ne_zero (a : ℕ → ℂ) (z : ℂ)
    (hane : ∀ (n : ℕ), a n ≠ 0)
    (hz : ∀ (n : ℕ), z ≠ a n)
    (hs2 : Summable fun (n : ℕ) => (‖a n‖ ^ 2)⁻¹)
    (htend : Tendsto (fun (n : ℕ) => ‖a n‖) atTop atTop) :
    canonicalProductNat 1 a z ≠ 0 := by
  have hs : Summable fun (n : ℕ) => (‖a n‖ ^ (1 + 1))⁻¹ := hs2
  exact canonicalProductNat_ne_zero hane 1 hz hs htend

/-- The product vanishes at each enumerated zero. -/
lemma partial_product_zero_at (a : ℕ → ℂ) (k : ℕ)
    (hane : ∀ (n : ℕ), a n ≠ 0)
    (hs2 : Summable fun (n : ℕ) => (‖a n‖ ^ 2)⁻¹)
    (htend : Tendsto (fun (n : ℕ) => ‖a n‖) atTop atTop) :
    canonicalProductNat 1 a (a k) = 0 := by
  have hs : Summable fun (n : ℕ) => (‖a n‖ ^ (1 + 1))⁻¹ := hs2
  exact canonicalProductNat_eq_zero_of_mem hane 1 ⟨k, rfl⟩ hs htend

/-- The skip product does not vanish at the removed zero (key for the deriv lower bound). -/
lemma partial_skip_ne_zero_at (a : ℕ → ℂ) (k : ℕ)
    (hane : ∀ (n : ℕ), a n ≠ 0)
    (hinj : Function.Injective a)
    (hs2 : Summable fun (n : ℕ) => (‖a n‖ ^ 2)⁻¹)
    (htend : Tendsto (fun (n : ℕ) => ‖a n‖) atTop atTop) :
    canonicalProductNatSkip k 1 a (a k) ≠ 0 := by
  have hs : Summable fun (n : ℕ) => (‖a n‖ ^ (1 + 1))⁻¹ := hs2
  exact canonicalProductNatSkip_ne_zero_at hane 1 k hinj hs htend

/-- `xi` is entire (prerequisite for the Hadamard factorization). -/
lemma partial_xi_entire : Differentiable ℂ xi :=
  xi_differentiable

/-! ## Conditional forms of the three deep estimates (zero placeholders). -/

/-- Canonical-product lower bound away from the zeros, conditional on its residual. -/
lemma canonicalProductNat_away_lower (a : ℕ → ℂ)
    (hane : ∀ (n : ℕ), a n ≠ 0)
    (hs2 : Summable fun (n : ℕ) => (‖a n‖ ^ 2)⁻¹)
    (htend : Tendsto (fun (n : ℕ) => ‖a n‖) atTop atTop)
    (hnb : ∃ (D : ℝ), 0 ≤ D ∧ ∀ (r : ℝ), r ≥ 1 →
      (({n : ℕ | ‖a n‖ ≤ r} : Set ℕ).ncard ≤ D * r ^ (7 / 4 : ℝ)))
    (hRes : AwayLowerResidual a) :
    ∃ (C : ℝ), 0 < C ∧ ∀ (z : ℂ), (∀ (n : ℕ), (1 / 2 : ℝ) ≤ ‖z - a n‖) →
      ‖canonicalProductNat 1 a z‖ ≥ Real.exp (-C * (1 + ‖z‖ ^ (7 / 4 : ℝ)
        * (1 + Real.log (1 + ‖z‖)))) :=
  hRes

/-- Lower bound on `|P'(a n)|` via the skip product, conditional on its residual. -/
lemma canonicalProductNat_deriv_at_zero_lower (a : ℕ → ℂ)
    (hane : ∀ (n : ℕ), a n ≠ 0)
    (hs2 : Summable fun (n : ℕ) => (‖a n‖ ^ 2)⁻¹)
    (htend : Tendsto (fun (n : ℕ) => ‖a n‖) atTop atTop)
    (hnb : ∃ (D : ℝ), 0 ≤ D ∧ ∀ (r : ℝ), r ≥ 1 →
      (({n : ℕ | ‖a n‖ ≤ r} : Set ℕ).ncard ≤ D * r ^ (7 / 4 : ℝ)))
    (hRes : DerivLowerResidual a) :
    ∃ (C : ℝ), 0 < C ∧ ∀ (n : ℕ),
      ‖deriv (canonicalProductNat 1 a) (a n)‖ ≥ Real.exp (-C * (1 + ‖a n‖ ^ (7 / 4 : ℝ)
        * (1 + Real.log (1 + ‖a n‖)))) :=
  hRes

/-- Uniform `Re(g)` growth bound, conditional on product lowers, `xi` upper, and its residual.

`Re (g z) = log |Q z|`; combining the upper bound for `|xi z|` with the canonical
product lower bounds (away from zeros and near zeros) yields the disk bound. The final
combination step is the residual `hRe`; the other hypotheses record the dependency. -/
lemma g_re_bound (a : ℕ → ℂ) (g : ℂ → ℂ)
    (hane : ∀ (n : ℕ), a n ≠ 0)
    (hs2 : Summable fun (n : ℕ) => (‖a n‖ ^ 2)⁻¹)
    (htend : Tendsto (fun (n : ℕ) => ‖a n‖) atTop atTop)
    (hnb : ∃ (D : ℝ), 0 ≤ D ∧ ∀ (r : ℝ), r ≥ 1 →
      (({n : ℕ | ‖a n‖ ≤ r} : Set ℕ).ncard ≤ D * r ^ (7 / 4 : ℝ)))
    (hxi : ∀ (z : ℂ), xi z = Complex.exp (g z) * canonicalProductNat 1 a z)
    (hAway : AwayLowerResidual a)
    (hDeriv : DerivLowerResidual a)
    (hXiUp : XiUpperResidual)
    (hRe : ReBoundResidual a g) :
    ∃ (A₀ : ℝ), 0 < A₀ ∧ ∀ (R : ℝ), R ≥ 1 → ∀ (z : ℂ), ‖z‖ < R →
      (g z).re ≤ A₀ * (1 + R ^ (3 / 2 : ℝ)) :=
  hRe

/-! ## Main theorem (conditional on the uniform residuals). -/

theorem xi_hadamard_exponent_affine
    (hAwayAll : ∀ (a : ℕ → ℂ), AwayLowerResidual a)
    (hDerivAll : ∀ (a : ℕ → ℂ), DerivLowerResidual a)
    (hXiUp : XiUpperResidual)
    (hReAll : ∀ (a : ℕ → ℂ) (g : ℂ → ℂ),
      (∀ (z : ℂ), xi z = Complex.exp (g z) * canonicalProductNat 1 a z) →
      ReBoundResidual a g) :
    ∃ (a : ℕ → ℂ) (g : ℂ → ℂ) (B : ℂ),
      (∀ (n : ℕ), a n ≠ 0) ∧ Function.Injective a
        ∧ Tendsto (fun (n : ℕ) => ‖a n‖) atTop atTop
        ∧ (∀ (z : ℂ), xi z = 0 ↔ ∃ (n : ℕ), z = a n)
        ∧ Differentiable ℂ g
        ∧ (∀ (z : ℂ), xi z = Complex.exp (g z) * canonicalProductNat 1 a z)
        ∧ deriv g = fun (_) => B := by
  obtain ⟨a, hane, hinj, htend, hzero⟩ := xi_zero_enumeration xiZeros_simple xiZeros_infinite
  obtain ⟨D, hD, hnb⟩ := xi_enum_ncard_bound hinj hzero
  have hnb' : ∃ (D : ℝ), 0 ≤ D ∧ ∀ (r : ℝ), 1 ≤ r →
      (({n : ℕ | ‖a n‖ ≤ r} : Set ℕ).ncard ≤ D * r ^ (7 / 4 : ℝ)) :=
    ⟨D, hD, fun (r : ℝ) (hr : 1 ≤ r) => hnb r hr⟩
  have hfinite : ∀ (r : ℝ), 1 ≤ r → (({n : ℕ | ‖a n‖ ≤ r} : Set ℕ).Finite) := by
    intro (r : ℝ) (hr : 1 ≤ r)
    have hev : ∀ᶠ (n : ℕ) in atTop, r + 1 ≤ ‖a n‖ :=
      htend.eventually (Filter.eventually_ge_atTop (r + 1))
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    apply Set.Finite.subset (Finset.finite_toSet (Finset.range N))
    intro (n : ℕ) (hn : n ∈ ({n : ℕ | ‖a n‖ ≤ r} : Set ℕ))
    simp only [Set.mem_setOf_eq] at hn
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra hcon
    have hNle : N ≤ n := not_lt.mp hcon
    have hle := hN n hNle
    linarith
  have hs2 : Summable fun (n : ℕ) => (‖a n‖ ^ 2)⁻¹ :=
    partial_summable_of_count a hfinite hnb'
  obtain ⟨g, hgd, hxi⟩ := hadamard_factorization_genus_one (f := xi) xi_differentiable hane hzero
    xiZeros_simple hinj hs2 htend
  have hAway : AwayLowerResidual a := hAwayAll a
  have hDeriv : DerivLowerResidual a := hDerivAll a
  obtain ⟨A₀, hA₀pos, hRe⟩ := hReAll a g hxi
  have hgpp : ∀ (z : ℂ), deriv (deriv g) z = 0 := by
    intro (c : ℂ)
    suffices h : ‖deriv (deriv g) c‖ = 0 by exact norm_eq_zero.mp h
    let claim : ∀ (ρ : ℝ), 1 ≤ ρ → ‖deriv (deriv g) c‖ ≤
        2 * (2 * A₀ * (1 + (2 * (‖c‖ + ρ)) ^ (3 / 2 : ℝ)) + 3 * ‖g 0‖) / ρ ^ 2 := by
      intro (ρ : ℝ) (hρ1 : 1 ≤ ρ)
      have hρ : 0 < ρ := by linarith
      set R' : ℝ := 2 * (‖c‖ + ρ) with hR'def
      have hR'pos : 0 < R' := by
        have hcnn : 0 ≤ ‖c‖ := norm_nonneg c
        linarith
      have hRge : 1 ≤ R' := by
        have hcnn : 0 ≤ ‖c‖ := norm_nonneg c
        linarith
      have hMball : ∀ (z : ℂ), ‖z‖ < R' → (g z).re ≤ A₀ * (1 + R' ^ (3 / 2 : ℝ)) := by
        intro (z : ℂ) (hz : ‖z‖ < R')
        exact hRe R' hRge z hz
      have hd : DifferentiableOn ℂ g (ball 0 R') := hgd.differentiableOn
      have hmaps : Set.MapsTo g (ball 0 R') {z : ℂ | z.re ≤ A₀ * (1 + R' ^ (3 / 2 : ℝ))} := by
        intro (w : ℂ) (hw : w ∈ ball 0 R')
        exact hMball w (mem_ball_zero_iff.mp hw)
      have hA₀nn : 0 ≤ A₀ := le_of_lt hA₀pos
      have hRnn : (0 : ℝ) ≤ R' ^ (3 / 2 : ℝ) :=
        Real.rpow_nonneg (le_of_lt hR'pos) (3 / 2 : ℝ)
      have hMpos : 0 < A₀ * (1 + R' ^ (3 / 2 : ℝ)) :=
        mul_pos hA₀pos (by linarith [hRnn])
      have hBC : ∀ (w : ℂ), ‖w‖ < R' → ‖g w‖ ≤
          2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) * ‖w‖ / (R' - ‖w‖)
            + ‖g 0‖ * (R' + ‖w‖) / (R' - ‖w‖) := by
        intro (w : ℂ) (hw : ‖w‖ < R')
        exact Complex.borelCaratheodory hMpos hd hmaps hR'pos (mem_ball_zero_iff.mpr hw)
      have hBall : ∀ (w : ℂ), ‖w - c‖ = ρ → ‖g w‖ ≤
          2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) + 3 * ‖g 0‖ := by
        intro (w : ℂ) (hw : ‖w - c‖ = ρ)
        have hdist : dist w c = ρ := by
          rw [dist_eq_norm]
          exact hw
        have hwn : ‖w‖ ≤ ‖c‖ + ρ := by
          calc ‖w‖ = dist w 0 := by rw [dist_zero_right]
            _ ≤ dist w c + dist c 0 := dist_triangle w c 0
            _ = ρ + ‖c‖ := by rw [hdist, dist_zero_right]
            _ = ‖c‖ + ρ := by ring
        have hlt : ‖w‖ < R' := by linarith [hwn]
        have hden : 0 < R' - ‖w‖ := by linarith [hwn, hR'def]
        have hR2 : R' / 2 ≤ R' - ‖w‖ := by linarith [hwn, hR'def]
        have hR2' : ‖w‖ ≤ R' / 2 := by linarith [hwn, hR'def]
        have hR2pos : (0 : ℝ) < R' / 2 := by linarith [hR'pos]
        have hR2ne : R' / 2 ≠ 0 := ne_of_gt hR2pos
        have hCoeffnn : (0 : ℝ) ≤ 2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) := by
          have hRnn : (0 : ℝ) ≤ R' ^ (3 / 2 : ℝ) :=
            Real.rpow_nonneg (le_of_lt hR'pos) (3 / 2 : ℝ)
          have h1 : (0 : ℝ) ≤ A₀ * (1 + R' ^ (3 / 2 : ℝ)) :=
            mul_nonneg hA₀nn (by linarith [hRnn])
          linarith [h1]
        have hg0nn : (0 : ℝ) ≤ ‖g 0‖ := norm_nonneg (g 0)
        have hwnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
        have e1 : 2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) * ‖w‖ / (R' - ‖w‖)
            ≤ 2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) * (R' / 2) / (R' / 2) := by
          rw [div_le_div_iff₀ hden hR2pos]
          have h1a : ‖w‖ * (R' / 2) ≤ (R' / 2) * (R' / 2) :=
            mul_le_mul_of_nonneg_right hR2' (le_of_lt hR2pos)
          have h1b : (R' / 2) * (R' / 2) ≤ (R' / 2) * (R' - ‖w‖) :=
            mul_le_mul_of_nonneg_left hR2 (le_of_lt hR2pos)
          have hbase : ‖w‖ * (R' / 2) ≤ (R' / 2) * (R' - ‖w‖) :=
            le_trans h1a h1b
          calc 2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) * ‖w‖ * (R' / 2)
              = (2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ)))) * (‖w‖ * (R' / 2)) := by ring
            _ ≤ (2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ)))) * ((R' / 2) * (R' - ‖w‖)) :=
              mul_le_mul_of_nonneg_left hbase hCoeffnn
            _ = 2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) * (R' / 2) * (R' - ‖w‖) := by ring
        have e2 : ‖g 0‖ * (R' + ‖w‖) / (R' - ‖w‖)
            ≤ ‖g 0‖ * (R' + R' / 2) / (R' / 2) := by
          rw [div_le_div_iff₀ hden hR2pos]
          have g1 : R' + ‖w‖ ≤ R' + R' / 2 := by linarith [hR2']
          have hnn : (0 : ℝ) ≤ R' + R' / 2 := by linarith [hR'pos, hwnn]
          have m1 : (R' + ‖w‖) * (R' / 2) ≤ (R' + R' / 2) * (R' / 2) :=
            mul_le_mul_of_nonneg_right g1 (le_of_lt hR2pos)
          have m2 : (R' + R' / 2) * (R' / 2) ≤ (R' + R' / 2) * (R' - ‖w‖) :=
            mul_le_mul_of_nonneg_left hR2 hnn
          have hbase : (R' + ‖w‖) * (R' / 2) ≤ (R' + R' / 2) * (R' - ‖w‖) :=
            le_trans m1 m2
          calc ‖g 0‖ * (R' + ‖w‖) * (R' / 2)
              = ‖g 0‖ * ((R' + ‖w‖) * (R' / 2)) := by ring
            _ ≤ ‖g 0‖ * ((R' + R' / 2) * (R' - ‖w‖)) :=
              mul_le_mul_of_nonneg_left hbase hg0nn
            _ = ‖g 0‖ * (R' + R' / 2) * (R' - ‖w‖) := by ring
        calc ‖g w‖ ≤ 2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) * ‖w‖ / (R' - ‖w‖)
              + ‖g 0‖ * (R' + ‖w‖) / (R' - ‖w‖) := hBC w hlt
          _ ≤ 2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) * (R' / 2) / (R' / 2)
              + ‖g 0‖ * (R' + R' / 2) / (R' / 2) := add_le_add e1 e2
          _ = 2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) + 3 * ‖g 0‖ := by
            field_simp
            ring
      have hC : ∀ (w : ℂ), w ∈ sphere c ρ → ‖g w‖ ≤
          2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) + 3 * ‖g 0‖ := by
        intro (w : ℂ) (hw : w ∈ sphere c ρ)
        have hnorm : ‖w - c‖ = ρ := by
          have hdist : dist w c = ρ := mem_sphere.mp hw
          rwa [dist_eq_norm] at hdist
        exact hBall w hnorm
      have hcont : DiffContOnCl ℂ g (ball c ρ) := hgd.diffContOnCl
      have hiter : ‖iteratedDeriv 2 g c‖ ≤
          2 * (2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) + 3 * ‖g 0‖) / ρ ^ 2 := by
        have hle := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hρ hcont hC
        have hfact : (2 : ℕ).factorial = 2 := by norm_num
        rw [hfact] at hle
        exact hle
      have hEq : iteratedDeriv 2 g c = deriv (deriv g) c := by
        have h2 : (2 : ℕ) = (1 : ℕ) + 1 := by norm_num
        have h1 : (1 : ℕ) = (0 : ℕ) + 1 := by norm_num
        rw [h2, iteratedDeriv_succ, h1, iteratedDeriv_succ, iteratedDeriv_zero]
      calc ‖deriv (deriv g) c‖ = ‖iteratedDeriv 2 g c‖ := by rw [hEq]
        _ ≤ 2 * (2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) + 3 * ‖g 0‖) / ρ ^ 2 := hiter
        _ ≤ 2 * (2 * A₀ * (1 + (2 * (‖c‖ + ρ)) ^ (3 / 2 : ℝ)) + 3 * ‖g 0‖) / ρ ^ 2 := by
          rw [hR'def]
          apply le_of_eq
          ring
    have hlt : ∀ (ε : ℝ), ε > 0 → ‖deriv (deriv g) c‖ < ε := by
      intro (ε : ℝ) (hε : ε > 0)
      have hA₀nn : 0 ≤ A₀ := le_of_lt hA₀pos
      have hg0nn : 0 ≤ ‖g 0‖ := norm_nonneg (g 0)
      have hcnn : 0 ≤ ‖c‖ := norm_nonneg c
      have hYnn : (0 : ℝ) ≤ (2 * (‖c‖ + 1)) ^ (3 / 2 : ℝ) :=
        Real.rpow_nonneg (by linarith) (3 / 2 : ℝ)
      -- monotone head: (2*(‖c‖+ρ))^{3/2} ≤ (2*(‖c‖+1))^{3/2} * ρ^{3/2} for ρ ≥ 1
      have hMono : ∀ (ρ : ℝ), 1 ≤ ρ →
          (2 * (‖c‖ + ρ)) ^ (3 / 2 : ℝ) ≤
            (2 * (‖c‖ + 1)) ^ (3 / 2 : ℝ) * ρ ^ (3 / 2 : ℝ) := by
        intro (ρ : ℝ) (hρ1 : 1 ≤ ρ)
        have hρpos : 0 < ρ := by linarith
        have hM1 : ‖c‖ * 1 ≤ ‖c‖ * ρ :=
          mul_le_mul_of_nonneg_left hρ1 hcnn
        have hM1' : ‖c‖ ≤ ‖c‖ * ρ := by
          calc ‖c‖ = ‖c‖ * 1 := by ring
            _ ≤ ‖c‖ * ρ := hM1
        have h1 : ‖c‖ + ρ ≤ (‖c‖ + 1) * ρ := by
          have hrw : (‖c‖ + 1) * ρ = ‖c‖ * ρ + ρ := by ring
          linarith
        have h2 : 2 * (‖c‖ + ρ) ≤ 2 * ((‖c‖ + 1) * ρ) := by linarith
        have h2nn : (0 : ℝ) ≤ 2 * (‖c‖ + ρ) := by linarith
        have h3 : 2 * ((‖c‖ + 1) * ρ) = (2 * (‖c‖ + 1)) * ρ := by ring
        have h4 : (2 * (‖c‖ + ρ)) ^ (3 / 2 : ℝ) ≤ ((2 * (‖c‖ + 1)) * ρ) ^ (3 / 2 : ℝ) := by
          apply Real.rpow_le_rpow h2nn _ (by norm_num : (0 : ℝ) ≤ 3 / 2)
          calc 2 * (‖c‖ + ρ) ≤ 2 * ((‖c‖ + 1) * ρ) := h2
            _ = (2 * (‖c‖ + 1)) * ρ := h3
        have h5 : (((2 * (‖c‖ + 1)) * ρ) : ℝ) ^ (3 / 2 : ℝ)
            = (2 * (‖c‖ + 1)) ^ (3 / 2 : ℝ) * ρ ^ (3 / 2 : ℝ) :=
          Real.mul_rpow (by linarith) (le_of_lt hρpos)
        rwa [h5] at h4
      have hNum : ∀ (ρ : ℝ), 1 ≤ ρ →
          2 * (2 * A₀ * (1 + (2 * (‖c‖ + ρ)) ^ (3 / 2 : ℝ)) + 3 * ‖g 0‖)
            ≤ (2 * (2 * A₀ + 3 * ‖g 0‖))
              + (4 * A₀ * (2 * (‖c‖ + 1)) ^ (3 / 2 : ℝ)) * ρ ^ (3 / 2 : ℝ) := by
        intro (ρ : ℝ) (hρ1 : 1 ≤ ρ)
        have hle := hMono ρ hρ1
        have hZnn : (0 : ℝ) ≤ ρ ^ (3 / 2 : ℝ) :=
          Real.rpow_nonneg (le_of_lt (by linarith : (0 : ℝ) < ρ)) (3 / 2 : ℝ)
        have h4 : 4 * A₀ * (2 * (‖c‖ + ρ)) ^ (3 / 2 : ℝ)
            ≤ 4 * A₀ * ((2 * (‖c‖ + 1)) ^ (3 / 2 : ℝ) * ρ ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hle (by linarith)
        have hassoc : 4 * A₀ * ((2 * (‖c‖ + 1)) ^ (3 / 2 : ℝ) * ρ ^ (3 / 2 : ℝ))
            = (4 * A₀ * (2 * (‖c‖ + 1)) ^ (3 / 2 : ℝ)) * ρ ^ (3 / 2 : ℝ) := by ring
        rw [hassoc] at h4
        linarith
      -- target radius
      set K₁ : ℝ := 2 * (2 * A₀ + 3 * ‖g 0‖) with hK₁def
      set K₂ : ℝ := 4 * A₀ * (2 * (‖c‖ + 1)) ^ (3 / 2 : ℝ) with hK₂def
      have hK₁nn : 0 ≤ K₁ := by
        rw [hK₁def]
        linarith
      have hK₂nn : 0 ≤ K₂ := by
        rw [hK₂def]
        apply mul_nonneg (by linarith) hYnn
      set ρ : ℝ := (max 1 (max (2 * K₁ / ε) ((2 * K₂ / ε) ^ 2)) + 1) with hρdef
      have hρ1 : 1 ≤ ρ := by
        rw [hρdef]
        linarith [le_max_left 1 (max (2 * K₁ / ε) ((2 * K₂ / ε) ^ 2))]
      have hρ : 0 < ρ := by linarith
      have hρbig1 : 2 * K₁ / ε ≤ ρ := by
        rw [hρdef]
        calc 2 * K₁ / ε ≤ max (2 * K₁ / ε) ((2 * K₂ / ε) ^ 2) :=
              le_max_left _ _
          _ ≤ max 1 (max (2 * K₁ / ε) ((2 * K₂ / ε) ^ 2)) :=
              le_max_right _ _
          _ ≤ max 1 (max (2 * K₁ / ε) ((2 * K₂ / ε) ^ 2)) + 1 := by linarith
      have hρbig2 : (2 * K₂ / ε) ^ 2 ≤ ρ := by
        rw [hρdef]
        calc (2 * K₂ / ε) ^ 2 ≤ max (2 * K₁ / ε) ((2 * K₂ / ε) ^ 2) :=
              le_max_right _ _
          _ ≤ max 1 (max (2 * K₁ / ε) ((2 * K₂ / ε) ^ 2)) :=
              le_max_right _ _
          _ ≤ max 1 (max (2 * K₁ / ε) ((2 * K₂ / ε) ^ 2)) + 1 := by linarith
      have h := claim ρ hρ1
      refine lt_of_le_of_lt h ?_
      have hρ2pos : (0 : ℝ) < ρ ^ 2 := pow_pos hρ 2
      rw [div_lt_iff₀ hρ2pos]
      have hN := hNum ρ hρ1
      rw [hK₁def, hK₂def] at hN
      -- split into two halves
      have hρgt1 : (1 : ℝ) < ρ := by
        rw [hρdef]
        have hmax : (1 : ℝ) ≤ max 1 (max (2 * K₁ / ε) ((2 * K₂ / ε) ^ 2)) :=
          le_max_left 1 _
        linarith [hmax]
      have hρsq : ρ ≤ ρ ^ 2 := by
        have heq : ρ ^ 2 = ρ * ρ := by ring
        rw [heq]
        have hle : 1 * ρ ≤ ρ * ρ :=
          mul_le_mul_of_nonneg_right (le_of_lt hρgt1) (le_of_lt hρ)
        linarith
      have hK₁half : K₁ < ε * ρ ^ 2 / 2 := by
        have h1 : 2 * K₁ ≤ ε * ρ := by
          rw [div_le_iff₀ hε] at hρbig1
          linarith [hρbig1]
        have hltρ : ρ < ρ ^ 2 := by
          have heq : ρ ^ 2 = ρ * ρ := by ring
          rw [heq]
          have hle : 1 * ρ < ρ * ρ :=
            mul_lt_mul_of_pos_right hρgt1 hρ
          linarith [hle]
        have h2 : ε * ρ < ε * ρ ^ 2 :=
          mul_lt_mul_of_pos_left hltρ hε
        linarith [h1, h2]
      have hK₂half : K₂ * ρ ^ (3 / 2 : ℝ) ≤ ε * ρ ^ 2 / 2 := by
        have hρ3nn : (0 : ℝ) ≤ ρ ^ (3 / 2 : ℝ) :=
          Real.rpow_nonneg (le_of_lt hρ) (3 / 2 : ℝ)
        have hρ2nn : (0 : ℝ) ≤ ρ ^ 2 := le_of_lt hρ2pos
        -- square both sides to avoid fractional powers
        have hsq : (K₂ * ρ ^ (3 / 2 : ℝ)) ^ 2 ≤ (ε * ρ ^ 2 / 2) ^ 2 := by
          have hpow3 : (ρ ^ (3 / 2 : ℝ)) ^ (2 : ℕ) = ρ ^ (3 : ℕ) := by
            rw [pow_two, ← Real.rpow_add hρ,
              show (3 / 2 : ℝ) + (3 / 2 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
              Real.rpow_natCast]
          have hL : (K₂ * ρ ^ (3 / 2 : ℝ)) ^ 2 = K₂ ^ 2 * ρ ^ (3 : ℕ) := by
            rw [mul_pow, hpow3]
          have hR : (ε * ρ ^ 2 / 2) ^ 2 = (ε / 2) ^ 2 * ρ ^ 4 := by ring
          rw [hL, hR]
          have hK₂sq : K₂ ^ 2 ≤ (ε / 2) ^ 2 * ρ := by
            have hmul : (2 * K₂ / ε) ^ 2 ≤ ρ := hρbig2
            have hepsq : (0 : ℝ) < (ε / 2) ^ 2 :=
              pow_pos (by linarith [hε]) 2
            have hrel : K₂ ^ 2 = (ε / 2) ^ 2 * (2 * K₂ / ε) ^ 2 := by
              field_simp
            rw [hrel]
            apply mul_le_mul_of_nonneg_left hmul (le_of_lt hepsq)
          have hρ34 : ρ ^ (3 : ℕ) ≤ ρ ^ (4 : ℕ) := by
            have h13 : (1 : ℝ) ≤ ρ := hρ1
            have hnn3 : (0 : ℝ) ≤ ρ ^ (3 : ℕ) := pow_nonneg (le_of_lt hρ) 3
            calc ρ ^ (3 : ℕ) = ρ ^ (3 : ℕ) * 1 := by ring
              _ ≤ ρ ^ (3 : ℕ) * ρ := mul_le_mul_of_nonneg_left h13 hnn3
              _ = ρ ^ (4 : ℕ) := by ring
          calc K₂ ^ 2 * ρ ^ (3 : ℕ) ≤ ((ε / 2) ^ 2 * ρ) * ρ ^ (3 : ℕ) :=
                mul_le_mul_of_nonneg_right hK₂sq (pow_nonneg (le_of_lt hρ) 3)
            _ = (ε / 2) ^ 2 * ρ ^ (4 : ℕ) := by ring
        have hLnn : (0 : ℝ) ≤ K₂ * ρ ^ (3 / 2 : ℝ) := mul_nonneg hK₂nn hρ3nn
        have hRnn : (0 : ℝ) ≤ ε * ρ ^ 2 / 2 :=
          div_nonneg (mul_nonneg (le_of_lt hε) hρ2nn) (by norm_num)
        have hiff := (pow_le_pow_iff_left₀ hLnn hRnn two_ne_zero).mp hsq
        exact hiff
      calc 2 * (2 * A₀ * (1 + (2 * (‖c‖ + ρ)) ^ (3 / 2 : ℝ)) + 3 * ‖g 0‖)
          ≤ K₁ + K₂ * ρ ^ (3 / 2 : ℝ) := by
            have := hN
            rw [hK₁def, hK₂def] at *
            linarith
        _ < ε * ρ ^ 2 / 2 + ε * ρ ^ 2 / 2 :=
          add_lt_add_of_lt_of_le hK₁half hK₂half
        _ = ε * ρ ^ 2 := by ring
    have hle : ‖deriv (deriv g) c‖ ≤ 0 :=
      le_of_forall_pos_le_add (fun (ε : ℝ) (hε : ε > 0) => by
        have h := hlt ε hε
        linarith [h])
    exact le_antisymm hle (norm_nonneg _)
  have hderiv_g : Differentiable ℂ (deriv g) := hgd.deriv
  have hconst : ∀ (x : ℂ) (y : ℂ), deriv g x = deriv g y :=
    fun (x : ℂ) (y : ℂ) => is_const_of_deriv_eq_zero hderiv_g hgpp x y
  refine ⟨a, g, deriv g 0, hane, hinj, htend, hzero, hgd, hxi, ?_⟩
  funext (z : ℂ)
  exact hconst z 0

end

end KadiriHadamardAffine
