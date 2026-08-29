import Mathlib
import ZeroFreeRegionHadamard

/-!
# A sharp upper bound for `Re ψ` on the strip `0 < Re z ≤ 1`

The Kadiri–Lamzouri explicit zero-free region needs an upper bound for the real part of the
digamma function on the vertical strip `0 < Re z ≤ 1` (the arguments occurring there are
`z = w/2` with `Re w = σ ∈ (1, 9/8]`, so `Re z ∈ (1/2, 9/16]`).

The bound available in `ZeroFreeRegionHadamard` is
`digamma_le_log : ‖ψ(z)‖ ≤ γ + 2·Re z + 7 + log(|Im z| + 2)`,
whose additive constant is `≈ 8.7` on that strip.  That is fatal for the Kadiri constant:
in the 3–4–1 combination the digamma bound enters with total weight
`(3 + 4 + 1)/2 = 4`, and the admissibility condition of
`riemannZeta_ne_zero_of_zeroFreeEdge` (with `kadiriConstant = 1/57.54`) only tolerates an
additive constant of about `6.2` in the whole `h_analytic` bound.

This file proves the sharp form

`re_digamma_le : 0 < Re z → Re z ≤ 1 → Im z ≠ 0 → Re ψ(z) ≤ log (|Im z| + 2) + 1`

whose additive constant `1` *does* fit the budget (it costs `4·1 = 4 < 6.2`), together with
the companion bound for real arguments

`re_digamma_le_of_real : 0 < x → x ≤ 1 → Re ψ(x) ≤ 1 - 1/x - γ`.

The proof is elementary, from the digamma series `ψ(z) = -γ + Σ_n (1/(n+1) - 1/(n+z))`
(`ZeroFreeRegionHadamard.psi_eq_tsum`), and uses that *only the real part* is needed:
writing `z = x + iy` and `m = n + x`,

`Re (1/(n+1) - 1/(n+z)) = (y² - (1-x)·m) / ((n+1)(m² + y²)) ≤ y²/(m(m²+y²)) ≤ |y|/(2m²)`,

so the series is bounded by the harmonic head `H_N ≤ 1 + log N` (taking `N = ⌈|y|⌉ + 1`)
plus a tail `≤ (|y|/2)·Σ_{k≥0} (k + N + x)⁻² ≤ (|y|/2)/(⌈|y|⌉ + x) ≤ 1/2`.
Since `γ > 1/2`, the total is `≤ log(|y| + 2) + 1`.
-/

open Finset ZeroFreeRegionHadamard
open scoped BigOperators

namespace KadiriDigamma

/-! ### Two elementary summation lemmas -/

/-- Telescoping tail bound: `Σ_{k ≥ 0} 1/(k + a)² ≤ 1/(a - 1)` for `1 < a`. -/
theorem tsum_one_div_add_sq_le {a : ℝ} (ha : 1 < a) :
    ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + a) ^ 2 ≤ 1 / (a - 1) := by
  have ha1 : (0 : ℝ) < a - 1 := by linarith
  have hfin : ∀ n : ℕ, ∑ k ∈ range n, (1 : ℝ) / ((k : ℝ) + a) ^ 2
      ≤ 1 / (a - 1) - 1 / ((a - 1) + (n : ℝ)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have h1 : (0 : ℝ) < (a - 1) + (n : ℝ) := by linarith
        have h2 : (0 : ℝ) < (a - 1) + (n : ℝ) + 1 := by linarith
        have hdiff : 1 / ((a - 1) + (n : ℝ)) - 1 / ((a - 1) + (n : ℝ) + 1)
            = 1 / (((a - 1) + (n : ℝ)) * ((a - 1) + (n : ℝ) + 1)) := by
          field_simp
          ring
        have hprod : ((a - 1) + (n : ℝ)) * ((a - 1) + (n : ℝ) + 1)
            = ((n : ℝ) + a) ^ 2 - ((n : ℝ) + a) := by ring
        have hle : (1 : ℝ) / (((n : ℝ) + a) ^ 2)
            ≤ 1 / (((a - 1) + (n : ℝ)) * ((a - 1) + (n : ℝ) + 1)) := by
          refine one_div_le_one_div_of_le (by positivity) ?_
          rw [hprod]
          linarith
        have hcast : ((a - 1) + ((n + 1 : ℕ) : ℝ)) = (a - 1) + (n : ℝ) + 1 := by
          push_cast; ring
        rw [Finset.sum_range_succ, hcast]
        linarith [ih, hle, hdiff]
  refine Real.tsum_le_of_sum_range_le (fun k => by positivity) (fun n => ?_)
  have h2 : (0 : ℝ) ≤ 1 / ((a - 1) + (n : ℝ)) := by positivity
  linarith [hfin n]

/-- `Σ_k 1/(k+a)²` converges for `1 ≤ a`. -/
theorem summable_one_div_add_sq {a : ℝ} (ha : 1 ≤ a) :
    Summable fun k : ℕ => (1 : ℝ) / ((k : ℝ) + a) ^ 2 := by
  have h1 : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have h2 : Summable fun k : ℕ => (1 : ℝ) / (((k + 1 : ℕ) : ℝ)) ^ 2 :=
    (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr h1
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) h2
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  refine one_div_le_one_div_of_le (by positivity) ?_
  have hc : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hc]
  nlinarith

/-- `H_N = Σ_{n < N} 1/(n+1)` as a real number. -/
private theorem harmonic_cast_real' (N : ℕ) :
    ((harmonic N : ℚ) : ℝ) = ∑ n ∈ range N, 1 / ((n : ℝ) + 1) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  push_cast
  rfl

/-! ### The real part of the digamma series -/

/-- Real part of the general term of the digamma series. -/
private theorem re_term (z : ℂ) (n : ℕ) :
    (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z)).re
      = 1 / ((n : ℝ) + 1) - ((n : ℝ) + z.re) / (((n : ℝ) + z.re) ^ 2 + z.im ^ 2) := by
  have e1 : (1 / ((n : ℂ) + 1)) = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
  have e2 : (1 / ((n : ℂ) + z)).re
      = ((n : ℝ) + z.re) / (((n : ℝ) + z.re) ^ 2 + z.im ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, zero_add]
    ring
  rw [Complex.sub_re, e1, Complex.ofReal_re, e2]

/-- The digamma series for the real part: `Re ψ(z) = -γ + Σ_n Re(1/(n+1) - 1/(n+z))`. -/
theorem re_digamma_eq_tsum {z : ℂ} (hs : ∀ m : ℕ, z ≠ -(m : ℂ)) :
    (Complex.digamma z).re = -Real.eulerMascheroniConstant
      + ∑' n : ℕ, (1 / ((n : ℝ) + 1)
          - ((n : ℝ) + z.re) / (((n : ℝ) + z.re) ^ 2 + z.im ^ 2)) := by
  have h2 : (Complex.digamma z).re
      = (-(Real.eulerMascheroniConstant : ℂ)).re
        + (∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z))).re := by
    rw [psi_eq_tsum z hs]
    exact Complex.add_re _ _
  have hre1 : (-(Real.eulerMascheroniConstant : ℂ)).re = -Real.eulerMascheroniConstant := by
    simp
  have h4 : (∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z))).re
      = ∑' n : ℕ, (1 / ((n : ℝ) + 1)
          - ((n : ℝ) + z.re) / (((n : ℝ) + z.re) ^ 2 + z.im ^ 2)) := by
    rw [Complex.re_tsum (summable_inv_add_sub 1 z)]
    exact tsum_congr (re_term z)
  rw [h2, hre1, h4]

/-- Summability of the real digamma series. -/
theorem summable_re_digamma_terms (z : ℂ) :
    Summable fun n : ℕ => 1 / ((n : ℝ) + 1)
      - ((n : ℝ) + z.re) / (((n : ℝ) + z.re) ^ 2 + z.im ^ 2) :=
  ((Complex.hasSum_re (summable_inv_add_sub 1 z).hasSum).summable).congr (re_term z)

/-! ### The bound -/

/-- The key termwise estimate: for `0 < x ≤ 1` and `y ≠ 0`,
`Re(1/(n+1) - 1/(n+z)) ≤ |y| / (2 (n+x)²)`. -/
private theorem term_le {z : ℂ} (hx0 : 0 < z.re) (hx1 : z.re ≤ 1) (n : ℕ) :
    1 / ((n : ℝ) + 1) - ((n : ℝ) + z.re) / (((n : ℝ) + z.re) ^ 2 + z.im ^ 2)
      ≤ |z.im| / (2 * ((n : ℝ) + z.re) ^ 2) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnx : 0 < (n : ℝ) + z.re := by linarith
  have hA : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hm' : ((n : ℝ) + z.re) ≠ 0 := ne_of_gt hnx
  have hD : 0 < ((n : ℝ) + z.re) ^ 2 + z.im ^ 2 := by positivity
  have hD' : (((n : ℝ) + z.re) ^ 2 + z.im ^ 2) ≠ 0 := ne_of_gt hD
  have hstepA : 1 / ((n : ℝ) + 1) - ((n : ℝ) + z.re) / (((n : ℝ) + z.re) ^ 2 + z.im ^ 2)
      ≤ z.im ^ 2 / (((n : ℝ) + z.re) * (((n : ℝ) + z.re) ^ 2 + z.im ^ 2)) := by
    have hid : (1 / ((n : ℝ) + 1) - ((n : ℝ) + z.re) / (((n : ℝ) + z.re) ^ 2 + z.im ^ 2))
        - z.im ^ 2 / (((n : ℝ) + z.re) * (((n : ℝ) + z.re) ^ 2 + z.im ^ 2))
        = (z.re - 1) / (((n : ℝ) + 1) * ((n : ℝ) + z.re)) := by
      field_simp
      ring
    have hneg : (z.re - 1) / (((n : ℝ) + 1) * ((n : ℝ) + z.re)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    linarith [hid, hneg]
  have hstepB : z.im ^ 2 / (((n : ℝ) + z.re) * (((n : ℝ) + z.re) ^ 2 + z.im ^ 2))
      ≤ |z.im| / (2 * ((n : ℝ) + z.re) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), ← sq_abs z.im]
    nlinarith [mul_nonneg (mul_nonneg (abs_nonneg z.im) hnx.le)
      (sq_nonneg (((n : ℝ) + z.re) - |z.im|))]
  linarith

/-- The digamma series on the strip `0 < Re z ≤ 1` is at most `log(|Im z| + 2) + 3/2`. -/
theorem tsum_re_digamma_terms_le {z : ℂ} (hx0 : 0 < z.re) (hx1 : z.re ≤ 1) (hy : z.im ≠ 0) :
    ∑' n : ℕ, (1 / ((n : ℝ) + 1)
        - ((n : ℝ) + z.re) / (((n : ℝ) + z.re) ^ 2 + z.im ^ 2))
      ≤ Real.log (|z.im| + 2) + 3 / 2 := by
  have hyabs : 0 < |z.im| := abs_pos.mpr hy
  set f : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
      - ((n : ℝ) + z.re) / (((n : ℝ) + z.re) ^ 2 + z.im ^ 2) with hf
  have hfsum : Summable f := summable_re_digamma_terms z
  set m : ℕ := ⌈|z.im|⌉₊ with hm
  have hm1 : 0 < m := Nat.ceil_pos.mpr hyabs
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmy : |z.im| ≤ (m : ℝ) := Nat.le_ceil _
  have hmy' : (m : ℝ) < |z.im| + 1 := Nat.ceil_lt_add_one (le_of_lt hyabs)
  -- head
  have hhead : ∑ n ∈ range (m + 1), f n ≤ 1 + Real.log ((m : ℝ) + 1) := by
    have hb : ∀ n ∈ range (m + 1), f n ≤ 1 / ((n : ℝ) + 1) := by
      intro n _
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hnn : 0 ≤ ((n : ℝ) + z.re) / (((n : ℝ) + z.re) ^ 2 + z.im ^ 2) :=
        div_nonneg (by linarith) (by positivity)
      simp only [hf]
      linarith
    calc ∑ n ∈ range (m + 1), f n
        ≤ ∑ n ∈ range (m + 1), 1 / ((n : ℝ) + 1) := Finset.sum_le_sum hb
      _ = ((harmonic (m + 1) : ℚ) : ℝ) := (harmonic_cast_real' (m + 1)).symm
      _ ≤ 1 + Real.log ((m + 1 : ℕ) : ℝ) := harmonic_le_one_add_log (m + 1)
      _ = 1 + Real.log ((m : ℝ) + 1) := by push_cast; ring
  -- tail
  have hc : (1 : ℝ) < (m : ℝ) + 1 + z.re := by linarith
  have hc1 : (1 : ℝ) ≤ (m : ℝ) + 1 + z.re := le_of_lt hc
  have htail : ∑' k : ℕ, f (k + (m + 1)) ≤ 1 / 2 := by
    have hs1 : Summable fun k : ℕ => f (k + (m + 1)) :=
      (summable_nat_add_iff (m + 1)).mpr hfsum
    have hgsum : Summable fun k : ℕ => |z.im| / (2 * ((k : ℝ) + ((m : ℝ) + 1 + z.re)) ^ 2) := by
      refine ((summable_one_div_add_sq hc1).mul_left (|z.im| / 2)).congr (fun k => ?_)
      have hkc : (0 : ℝ) < ((k : ℝ) + ((m : ℝ) + 1 + z.re)) := by
        have := Nat.cast_nonneg (α := ℝ) k
        linarith
      field_simp
    have hterm : ∀ k : ℕ,
        f (k + (m + 1)) ≤ |z.im| / (2 * ((k : ℝ) + ((m : ℝ) + 1 + z.re)) ^ 2) := by
      intro k
      have h := term_le hx0 hx1 (k + (m + 1))
      have hcast : (((k + (m + 1) : ℕ) : ℝ) + z.re) = ((k : ℝ) + ((m : ℝ) + 1 + z.re)) := by
        push_cast; ring
      simp only [hf]
      rw [← hcast]
      exact h
    have hstep : ∑' k : ℕ, f (k + (m + 1))
        ≤ ∑' k : ℕ, |z.im| / (2 * ((k : ℝ) + ((m : ℝ) + 1 + z.re)) ^ 2) :=
      hs1.tsum_le_tsum hterm hgsum
    have hEq : ∑' k : ℕ, |z.im| / (2 * ((k : ℝ) + ((m : ℝ) + 1 + z.re)) ^ 2)
        = |z.im| / 2 * ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + ((m : ℝ) + 1 + z.re)) ^ 2 := by
      rw [← tsum_mul_left]
      refine tsum_congr (fun k => ?_)
      have hkc : (0 : ℝ) < ((k : ℝ) + ((m : ℝ) + 1 + z.re)) := by
        have := Nat.cast_nonneg (α := ℝ) k
        linarith
      field_simp
    have hbound : ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + ((m : ℝ) + 1 + z.re)) ^ 2
        ≤ 1 / (((m : ℝ) + 1 + z.re) - 1) := tsum_one_div_add_sq_le hc
    have hden : |z.im| ≤ ((m : ℝ) + 1 + z.re) - 1 := by linarith
    have hfrac : 1 / (((m : ℝ) + 1 + z.re) - 1) ≤ 1 / |z.im| :=
      one_div_le_one_div_of_le hyabs hden
    have hfinal : |z.im| / 2 * (1 / |z.im|) = 1 / 2 := by
      field_simp
    calc ∑' k : ℕ, f (k + (m + 1))
        ≤ |z.im| / 2 * ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + ((m : ℝ) + 1 + z.re)) ^ 2 := by
          rw [← hEq]; exact hstep
      _ ≤ |z.im| / 2 * (1 / |z.im|) := by
          refine mul_le_mul_of_nonneg_left (le_trans hbound hfrac) (by positivity)
      _ = 1 / 2 := hfinal
  -- assemble
  have hsplit := hfsum.sum_add_tsum_nat_add (m + 1)
  have hlog : Real.log ((m : ℝ) + 1) ≤ Real.log (|z.im| + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  linarith [hsplit, hhead, htail, hlog]

/-- **Sharp digamma bound on the strip `0 < Re z ≤ 1`.**
For `0 < Re z ≤ 1` and `Im z ≠ 0`,  `Re ψ(z) ≤ log (|Im z| + 2) + 1`.

Contrast `ZeroFreeRegionHadamard.digamma_le_log`, which has the additive constant
`γ + 2 Re z + 7` (`≈ 8.7` on this strip); the constant `1` here is what the Kadiri
3–4–1 budget can absorb. -/
theorem re_digamma_le {z : ℂ} (hx0 : 0 < z.re) (hx1 : z.re ≤ 1) (hy : z.im ≠ 0) :
    (Complex.digamma z).re ≤ Real.log (|z.im| + 2) + 1 := by
  have hs : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    have h0 : 0 < z.re := hx0
    rw [h] at h0
    simp only [Complex.neg_re, Complex.natCast_re, neg_pos] at h0
    exact absurd h0 (not_lt.mpr (Nat.cast_nonneg m))
  have hγ : (1 : ℝ) / 2 < Real.eulerMascheroniConstant :=
    Real.one_half_lt_eulerMascheroniConstant
  rw [re_digamma_eq_tsum hs]
  linarith [tsum_re_digamma_terms_le hx0 hx1 hy]

/-- Companion bound for **real** arguments in `(0, 1]`: `ψ(x) ≤ 1 - 1/x - γ`.
(The digamma series has all terms `≤ 0` for `x ≤ 1`, and the `n = 0` term is `1 - 1/x`.) -/
theorem re_digamma_le_of_real {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (Complex.digamma (x : ℂ)).re ≤ 1 - 1 / x - Real.eulerMascheroniConstant := by
  have hs : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have h0 : (0 : ℝ) < ((x : ℂ)).re := by simpa using hx0
    rw [h] at h0
    simp only [Complex.neg_re, Complex.natCast_re, neg_pos] at h0
    exact absurd h0 (not_lt.mpr (Nat.cast_nonneg m))
  have hre : ((x : ℂ)).re = x := Complex.ofReal_re x
  have him : ((x : ℂ)).im = 0 := Complex.ofReal_im x
  set f : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
      - ((n : ℝ) + ((x : ℂ)).re) / (((n : ℝ) + ((x : ℂ)).re) ^ 2 + ((x : ℂ)).im ^ 2) with hf
  have hfsum : Summable f := summable_re_digamma_terms (x : ℂ)
  have hf0 : f 0 = 1 - 1 / x := by
    simp only [hf, hre, him]
    norm_num
    field_simp
  have hnonpos : ∀ k : ℕ, f (k + 1) ≤ 0 := by
    intro k
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hkx : 0 < ((k : ℝ) + 1) + x := by linarith
    have hval : f (k + 1) = 1 / ((k : ℝ) + 1 + 1) - 1 / (((k : ℝ) + 1) + x) := by
      simp only [hf, hre, him]
      have hcast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hne : (((k : ℝ) + 1) + x) ≠ 0 := ne_of_gt hkx
      field_simp
      ring
    rw [hval]
    have hle : ((k : ℝ) + 1) + x ≤ (k : ℝ) + 1 + 1 := by linarith
    have := one_div_le_one_div_of_le hkx hle
    linarith
  have htail : ∑' k : ℕ, f (k + 1) ≤ 0 := tsum_nonpos hnonpos
  have hsplit := hfsum.sum_add_tsum_nat_add 1
  rw [re_digamma_eq_tsum hs]
  have hgoal : ∑' n : ℕ, f n ≤ 1 - 1 / x := by
    have hsum1 : ∑ i ∈ range 1, f i = f 0 := by simp
    rw [hsum1] at hsplit
    rw [hf0] at hsplit
    linarith [hsplit, htail]
  have hconv : ∑' n : ℕ, (1 / ((n : ℝ) + 1)
      - ((n : ℝ) + ((x : ℂ)).re) / (((n : ℝ) + ((x : ℂ)).re) ^ 2 + ((x : ℂ)).im ^ 2))
      = ∑' n : ℕ, f n := by simp only [hf]
  rw [hconv]
  linarith [hgoal]

end KadiriDigamma
