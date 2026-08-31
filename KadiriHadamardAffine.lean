import Mathlib
import ZeroFreeRegionHadamard
import KadiriZeroFree

open Complex Real Topology
open ZeroFreeRegionHadamard
open scoped BigOperators

/-!
# Affineness of the Hadamard exponent of the completed Riemann xi-function

We obtain (from `KadiriZeroFree` / `ZeroFreeRegionHadamard`) a zero enumeration `a` of `xi`,
a zero-count `N(r) = O(r^{7/4})`, the summability `Σ 1/|a n|² < ∞`, and Hadamard's
genus-one factorization `xi = exp(g)·canonicalProductNat 1 a` with `g` entire.

Writing `P := canonicalProductNat 1 a`, the quotient `Q := xi/P = exp(g)` is a zero-free entire
function.  The completed proof shows `g` has entire order `≤ 3/2 < 2`; by Cauchy's estimate on
the second derivative this forces `g'' ≡ 0`, i.e. `g` is affine (`deriv g ≡ B`).

The growth input (a uniform bound `Re(g z) ≤ O(|z|^{3/2})` on every disk, obtained from
Borel–Carathéodory once a lower bound `|P z| ≥ exp(-O(|z|^{7/4}log|z|))` away from the zeros is
established, and a matching bound near the zeros via the analytic zero-free quotient) is
isolated in `canonicalProductNat_away_lower` / `canonicalProductNat_deriv_at_zero_lower` /
`g_re_bound`.  The deduction `g'' = 0` from that growth bound (Borel–Carathéodory + the Cauchy
second-derivative estimate) is proved below without `sorry`.
-/

namespace KadiriHadamardAffine

noncomputable section

/-! ## Canonical-product lower bound away from the zeros.

A lower bound `|P z| ≥ exp(-C(1+|z|^{7/4}log(1+|z|)))` valid whenever `dist(z,{a n}) ≥ 1/2`,
deduced from the zero-count `N(r)=O(r^{7/4})` and the genus-1 convergence `Σ 1/|a n|² < ∞`. -/
lemma canonicalProductNat_away_lower {a : ℕ → ℂ}
    (hane : ∀ n, a n ≠ 0) (hs2 : Summable fun n => (‖a n‖ ^ 2)⁻¹)
    (htend : Tendsto (fun n => ‖a n‖) atTop atTop)
    (hnb : ∃ D : ℝ, 0 ≤ D ∧ ∀ r ≥ 1, (({n | ‖a n‖ ≤ r} : Set ℕ).ncard : ℝ) ≤ D * r ^ (7 / 4 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z, (∀ n, (1 / 2 : ℝ) ≤ ‖z - a n‖) →
      ‖canonicalProductNat 1 a z‖ ≥ Real.exp (-C * (1 + ‖z‖ ^ (7 / 4 : ℝ)
        * (1 + Real.log (1 + ‖z‖)))) :=
  sorry

/-! ## Lower bound on `|P'(a n)|` via the skip product.

`P'(a n)` is bounded below (up to an `exp(O(|a n|^{7/4}log|a n|))` factor) by the skip-product
estimate, which is what bounds `Q` near a zero. -/
lemma canonicalProductNat_deriv_at_zero_lower {a : ℕ → ℂ}
    (hane : ∀ n, a n ≠ 0) (hs2 : Summable fun n => (‖a n‖ ^ 2)⁻¹)
    (htend : Tendsto (fun n => ‖a n‖) atTop atTop)
    (hnb : ∃ D : ℝ, 0 ≤ D ∧ ∀ r ≥ 1, (({n | ‖a n‖ ≤ r} : Set ℕ).ncard : ℝ) ≤ D * r ^ (7 / 4 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n,
      ‖deriv (canonicalProductNat 1 a) (a n)‖ ≥ Real.exp (-C * (1 + ‖a n‖ ^ (7 / 4 : ℝ)
        * (1 + Real.log (1 + ‖a n‖)))) :=
  sorry

/-! ## Uniform `Re(g)` growth bound.

`Re(g z) = log|Q z|`; combining the upper bound `|xi z| ≤ exp(K|z|^{3/2})` with the canonical
product lower bounds (away from zeros and near zeros) yields `Re(g z) ≤ O(|z|^{3/2})` on every
disk, hence on every sphere. -/
lemma g_re_bound {a : ℕ → ℂ} (g : ℂ → ℂ)
    (hane : ∀ n, a n ≠ 0) (hs2 : Summable fun n => (‖a n‖ ^ 2)⁻¹)
    (htend : Tendsto (fun n => ‖a n‖) atTop atTop)
    (hnb : ∃ D : ℝ, 0 ≤ D ∧ ∀ r ≥ 1, (({n | ‖a n‖ ≤ r} : Set ℕ).ncard : ℝ) ≤ D * r ^ (7 / 4 : ℝ))
    (hxi : ∀ z, xi z = Complex.exp (g z) * canonicalProductNat 1 a z) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ R ≥ 1, ∀ z, ‖z‖ < R → (g z).re ≤ A₀ * (1 + R ^ (3 / 2 : ℝ)) :=
  sorry

/-! ## Main theorem.

From the growth bound `Re(g) ≤ O(|z|^{3/2})` (which implies `|g| = O(|z|^{3/2})` by
Borel–Carathéodory) we apply the Cauchy second-derivative estimate and let the radius tend to
infinity, forcing `g'' ≡ 0`.  Hence `g` is affine. -/
theorem xi_hadamard_exponent_affine :
    ∃ (a : ℕ → ℂ) (g : ℂ → ℂ) (B : ℂ),
      (∀ n, a n ≠ 0) ∧ Function.Injective a
        ∧ Tendsto (fun n => ‖a n‖) atTop atTop
        ∧ (∀ z, xi z = 0 ↔ ∃ n, z = a n)
        ∧ Differentiable ℂ g
        ∧ (∀ z, xi z = Complex.exp (g z) * canonicalProductNat 1 a z)
        ∧ deriv g = fun _ => B := by
  obtain ⟨a, hane, hinj, htend, hzero⟩ := xi_zero_enumeration xiZeros_simple xiZeros_infinite
  obtain ⟨D, hD, hnb⟩ := xi_enum_ncard_bound hinj hzero
  have hfinite : ∀ r ≥ 1, (({n | ‖a n‖ ≤ r} : Set ℕ).Finite) := by
    intro r _
    have : (0 : ℝ) < D := hD
    have hc : (({n | ‖a n‖ ≤ r} : Set ℕ).ncard : ℝ) ≤ D * r ^ (7 / 4 : ℝ) := hnb r (by linarith)
    -- the zero count is finite, so the set is finite
    exact Set.finite_of_ncard (by simpa using hc)
  have hs2 : Summable fun n => (‖a n‖ ^ 2)⁻¹ :=
    summable_inv_norm_pow_of_ncard_bound (by norm_num) (by norm_num : (7/4:ℝ) < 2) hfinite hnb
  obtain ⟨g, hgd, hxi⟩ := hadamard_factorization_genus_one (f := xi) xi_differentiable hane hzero
    xiZeros_simple hinj hs2 htend
  obtain ⟨A₀, hA₀pos, hRe⟩ := g_re_bound a g hane hs2 htend hnb hxi
  have hgpp : ∀ z, deriv (deriv g) z = 0 := by
    intro c
    suffices ‖deriv (deriv g) c‖ = 0 by exact (norm_eq_zero.mp this).symm
    let claim (ρ : ℝ) (hρ : ρ > 0) : ‖deriv (deriv g) c‖ ≤
        2 * (2 * A₀ * (1 + (2 * (‖c‖ + ρ)) ^ (3 / 2 : ℝ)) + 3 * ‖g 0‖) / ρ ^ 2 := by
      set R' : ℝ := 2 * (‖c‖ + ρ) with hR'def
      have hR'pos : 0 < R' := by linarith [hρ, norm_nonneg c]
      have hMball : ∀ z, ‖z‖ < R' → (g z).re ≤ A₀ * (1 + R' ^ (3 / 2 : ℝ)) := by
        intro z hz
        have hRge : 1 ≤ R' := by linarith
        exact hRe R' hRge z hz
      have hd : DifferentiableOn ℂ g (ball 0 R') := hgd.differentiableOn
      have hmaps : Set.MapsTo g (ball 0 R') {z | z.re ≤ A₀ * (1 + R' ^ (3 / 2 : ℝ))} := by
        intro w hw; exact hMball w hw
      have hBC (w : ℂ) (hw : ‖w‖ < R') : ‖g w‖ ≤
          2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) * ‖w‖ / (R' - ‖w‖)
            + ‖g 0‖ * (R' + ‖w‖) / (R' - ‖w‖) :=
        Complex.borelCaratheodory hA₀pos hd hmaps hR'pos hw
      have hBall (w : ℂ) (hw : ‖w - c‖ = ρ) : ‖g w‖ ≤
          2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) + 3 * ‖g 0‖ := by
        have hwn : ‖w‖ ≤ ‖c‖ + ρ := by
          rw [← dist_eq_norm, ← dist_eq_norm] at hw
          exact le_trans (dist_triangle c w 0) (by rw [dist_zero_right]; linarith)
        have hlt : ‖w‖ < R' := by linarith [hwn]
        have hden : 0 < R' - ‖w‖ := by linarith [hwn, hR'def]
        have hR2 : R' / 2 ≤ R' - ‖w‖ := by linarith [hwn, hR'def]
        have hR2' : ‖w‖ ≤ R' / 2 := by linarith [hwn, hR'def]
        calc ‖g w‖ ≤ 2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) * ‖w‖ / (R' - ‖w‖)
              + ‖g 0‖ * (R' + ‖w‖) / (R' - ‖w‖) := hBC w hlt
          _ ≤ 2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) * (R' / 2) / (R' / 2)
              + ‖g 0‖ * (R' + R' / 2) / (R' / 2) := by
            gcongr
            · gcongr; exact hR2'
            · gcongr; linarith [hR2']
            · linarith [hR2']
          _ = 2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) + 3 * ‖g 0‖ := by field_simp
      have hC (w : ℂ) (hw : w ∈ sphere c ρ) : ‖g w‖ ≤
          2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) + 3 * ‖g 0‖ := hBall w (mem_sphere.mp hw)
      have hcont : DiffContOnCl ℂ g (ball c ρ) := hgd.diffContOnCl
      have hiter : ‖iteratedDeriv 2 g c‖ ≤
          2 * (2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) + 3 * ‖g 0‖) / ρ ^ 2 := by
        exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hρ hcont hC
      have hEq : iteratedDeriv 2 g c = deriv (deriv g) c := by
        rw [iteratedDeriv_succ', iteratedDeriv_zero]
      calc ‖deriv (deriv g) c‖ = ‖iteratedDeriv 2 g c‖ := by rw [hEq]
        _ ≤ 2 * (2 * (A₀ * (1 + R' ^ (3 / 2 : ℝ))) + 3 * ‖g 0‖) / ρ ^ 2 := hiter
        _ ≤ 2 * (2 * A₀ * (1 + (2 * (‖c‖ + ρ)) ^ (3 / 2 : ℝ)) + 3 * ‖g 0‖) / ρ ^ 2 := by
          rw [hR'def]; gcongr; linarith
    have hlt : ∀ ε : ℝ, ε > 0 → ‖deriv (deriv g) c‖ < ε := by
      intro ε hε
      set ρ : ℝ := max (1 + ‖c‖)
        (2 * (2 * A₀ * (1 + (2 * (‖c‖ + 1)) ^ (3 / 2 : ℝ)) + 3 * ‖g 0‖) / ε) + 1) with hρdef
      have hρ : ρ > 0 := by linarith
      have h := claim ρ hρ
      refine lt_of_le_of_lt h (div_lt_of_mul_lt hρ.ne' ?_)
      calc (2 * (2 * A₀ * (1 + (2 * (‖c‖ + ρ)) ^ (3 / 2 : ℝ)) + 3 * ‖g 0‖)) < ρ ^ 2 * ε := by
        calc ρ ≥ 2 * (2 * A₀ * (1 + (2 * (‖c‖ + 1)) ^ (3 / 2 : ℝ)) + 3 * ‖g 0‖) / ε + 1 := le_max_right _ _
        _ ≥ 2 * (2 * A₀ * (1 + (2 * (‖c‖ + ρ)) ^ (3 / 2 : ℝ)) + 3 * ‖g 0‖) / ε := by
          gcongr
          · linarith
          · rw [hρdef]; apply le_max_left
        _ ≥ _ := by linarith
    exact le_of_forall_lt hlt
  obtain ⟨B, hB⟩ := is_const_of_deriv_eq_zero hgd hgpp
  refine ⟨a, g, B, hane, hinj, htend, hzero, hgd, hxi, hB⟩

end KadiriHadamardAffine
