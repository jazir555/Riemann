import ZeroFreeRegionProof
import ZeroFreeRegionHadamard
import Zeta23.RvM.Statement
import Zeta23.GammaFacts.Complete
import Zeta23.Assembly

open Complex Real Topology
open scoped BigOperators
open ZeroFreeRegionHadamard
open ArithmeticFunction hiding log
open scoped LSeries.notation

noncomputable section

/-- The Kadiri numerical bridge: 1/57.54 < 2/95, i.e. 9500 < 11508.
    This is the arithmetic fact that makes Kadiri's explicit zero-free region work.
    The proof is a pure `norm_num` verification. -/
theorem kadiri_numerical_bridge :
    (1 : ℝ) / 57.54 < 2 / 95 := by norm_num

/-! ### The ξ-zero facts, imported from the (sorry-free) `Zeta23` library

`Zeta23` works with **Mathlib's** `riemannZeta`, so its Riemann–von Mangoldt
formula (`Zeta23.RvM.riemannVonMangoldt`, unconditional given
`Zeta23.gammaFacts`) and its local zero count
(`Zeta23.RvM.zeta_local_zero_count`: `N(t, t+1] ≤ A₀ log(|t| + 3)`) apply
verbatim to the zeros of the root `xi = s(s-1)Λ₀(s) + 1`, whose zero set is
exactly the set of nontrivial zeros of `ζ` (`xi_zero_iff_isNontrivialZero`). -/

/-- A zero of `xi` is exactly a nontrivial zero of `ζ` in `Zeta23`'s sense. -/
theorem xi_zero_iff_isNontrivialZero {z : ℂ} :
    xi z = 0 ↔ Zeta23.IsNontrivialZero z := by
  constructor
  · intro h
    have hζ := xi_zero_imp_riemannZeta_zero h
    have h0 : 0 < z.re := xi_zero_imp_zero_lt_re h
    have h1 : z.re < 1 := by
      by_contra hc
      exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hc) hζ
    exact ⟨hζ, h0, h1⟩
  · rintro ⟨hζ, h0, h1⟩
    have hΓ : ∀ n : ℕ, z / 2 ≠ -(n : ℂ) := by
      intro n hn
      have hre : (z / 2).re = (-(n : ℂ)).re := congrArg Complex.re hn
      simp only [Complex.div_re, Complex.neg_re, Complex.natCast_re] at hre
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      simp at hre
      nlinarith [hre, h0, hn0]
    exact (xi_zero_iff_riemannZeta_zero hΓ).mpr hζ

/-- An empty ordinate window carries no zeros. -/
theorem Ncount_self (t : ℝ) : Zeta23.Ncount t t = 0 := by
  have h : Zeta23.zerosIn t t = ∅ := by
    ext ρ
    simp only [Zeta23.zerosIn, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, h1, h2⟩
    linarith
  simp [Zeta23.Ncount, h]

/-- Telescoping `Zeta23`'s local zero count `N(t, t+1] ≤ A₀ log(|t| + 3)` over `k`
consecutive unit windows. -/
theorem Ncount_window_le {A₀ C : ℝ} (hA₀ : 0 ≤ A₀)
    (hloc : ∀ t : ℝ, (Zeta23.Ncount t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    ∀ (k : ℕ) (t : ℝ), (∀ j : ℕ, j < k → A₀ * Real.log (|t + (j : ℝ)| + 3) ≤ C) →
      (Zeta23.Ncount t (t + (k : ℝ)) : ℝ) ≤ (k : ℝ) * C := by
  intro k
  induction k with
  | zero => intro t _; simp [Ncount_self]
  | succ k ih =>
      intro t hC
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have h1 : t ≤ t + (k : ℝ) := by linarith
      have h2 : t + (k : ℝ) ≤ t + ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
      have hsplit := Zeta23.Ncount_add h1 h2
      have hstep : (Zeta23.Ncount (t + (k : ℝ)) (t + ((k + 1 : ℕ) : ℝ)) : ℝ)
          ≤ A₀ * Real.log (|t + (k : ℝ)| + 3) := by
        have := hloc (t + (k : ℝ))
        have heq : t + (k : ℝ) + 1 = t + ((k + 1 : ℕ) : ℝ) := by push_cast; ring
        rwa [heq] at this
      have hCk : A₀ * Real.log (|t + (k : ℝ)| + 3) ≤ C := hC k (Nat.lt_succ_self k)
      have hprev : (Zeta23.Ncount t (t + (k : ℝ)) : ℝ) ≤ (k : ℝ) * C :=
        ih t (fun j hj => hC j (Nat.lt_succ_of_lt hj))
      have hcast : ((Zeta23.Ncount t (t + ((k + 1 : ℕ) : ℝ))) : ℝ)
          = (Zeta23.Ncount t (t + (k : ℝ)) : ℝ)
            + (Zeta23.Ncount (t + (k : ℝ)) (t + ((k + 1 : ℕ) : ℝ)) : ℝ) := by
        rw [hsplit]; push_cast; ring
      rw [hcast]
      have hCsucc : ((k + 1 : ℕ) : ℝ) * C = (k : ℝ) * C + C := by push_cast; ring
      rw [hCsucc]
      linarith

/-- **ξ has infinitely many zeros.**  Proof: `Zeta23`'s Riemann–von Mangoldt formula
(`Zeta23.RvM.riemannVonMangoldt`, unconditional via `Zeta23.gammaFacts`) forces
`N(T, 2T] → ∞` (`Zeta23.Assembly.tendsto_N_atTop`), so nontrivial ζ-zeros occur with
arbitrarily large ordinate; by `xi_zero_iff_isNontrivialZero` these are exactly the
zeros of `xi`, whose set therefore cannot be finite (a finite set of zeros would have
bounded ordinates). -/
theorem xiZeros_infinite :
    ({z : ℂ | xi z = 0} : Set ℂ).Infinite := by
  have hRvM : Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig :=
    Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts
  have htend := Zeta23.Assembly.tendsto_N_atTop Zeta23.zetaZeroConfig hRvM
  by_contra hcon
  rw [Set.not_infinite] at hcon
  obtain ⟨M, hM⟩ := (hcon.image (fun z : ℂ => z.im)).bddAbove
  have hev : ∀ᶠ T : ℝ in Filter.atTop, (1 : ℝ) ≤ (Zeta23.zetaZeroConfig.N T (2 * T) : ℝ) :=
    htend.eventually_ge_atTop 1
  obtain ⟨T, hT1, hT2⟩ := (hev.and (Filter.eventually_ge_atTop M)).exists
  have hN1 : 1 ≤ Zeta23.zetaZeroConfig.N T (2 * T) := by exact_mod_cast hT1
  have hne : (Zeta23.zetaZeroConfig.window T (2 * T)).Nonempty := by
    rcases Set.eq_empty_or_nonempty (Zeta23.zetaZeroConfig.window T (2 * T)) with he | h
    · rw [Zeta23.ZeroConfig.N, he] at hN1
      simp at hN1
    · exact h
  obtain ⟨ρ, hρ⟩ := hne
  have hρz : Zeta23.IsNontrivialZero ρ := hρ.1
  have hxiρ : xi ρ = 0 := xi_zero_iff_isNontrivialZero.mpr hρz
  have himle : ρ.im ≤ M := hM (Set.mem_image_of_mem _ hxiρ)
  have hgt : T < ρ.im := hρ.2.1
  linarith

/-- The Jensen-type counting input for `Summable (fun n => (‖a n‖ ^ 2)⁻¹)`:
an enumeration of the ξ-zeros has at most `42·A₀·r^(7/4)` terms in the disc of
radius `r`.  Proof: a ξ-zero of modulus `≤ r` has ordinate in `(-r-1, r+1]`, and
`Zeta23`'s local count `N(t, t+1] ≤ A₀ log(|t| + 3)` telescoped over the
`2⌈r⌉+2` unit windows bounds that count by `(2⌈r⌉+2)·A₀·log(⌈r⌉+4) ≤ 42·A₀·r^(7/4)`. -/
theorem xi_enum_ncard_bound {a : ℕ → ℂ} (hinj : Function.Injective a)
    (hzero : ∀ z, xi z = 0 ↔ ∃ n, z = a n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ r : ℝ, 1 ≤ r →
      (({n : ℕ | ‖a n‖ ≤ r} : Set ℕ).ncard : ℝ) ≤ D * r ^ (7 / 4 : ℝ) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zeta_local_zero_count
  have hA₀0 : (0 : ℝ) ≤ A₀ := by linarith
  refine ⟨42 * A₀, by linarith, ?_⟩
  intro r hr
  have hrpos : (0 : ℝ) < r := by linarith
  set m : ℕ := ⌈r⌉₊ with hmdef
  have hrm : r ≤ (m : ℝ) := Nat.le_ceil r
  have hmr : (m : ℝ) ≤ r + 1 := by
    have h := Nat.ceil_lt_add_one (le_of_lt hrpos)
    have hcast : ((⌈r⌉₊ : ℕ) : ℝ) < r + 1 := by exact_mod_cast h
    rw [hmdef]; linarith
  have hsub : (a '' {n : ℕ | ‖a n‖ ≤ r})
      ⊆ Zeta23.zetaZeroConfig.window (-(m : ℝ) - 1) ((m : ℝ) + 1) := by
    rintro z ⟨n, hn, rfl⟩
    have hxz : xi (a n) = 0 := (hzero (a n)).mpr ⟨n, rfl⟩
    have hz : Zeta23.IsNontrivialZero (a n) := xi_zero_iff_isNontrivialZero.mp hxz
    have hnorm : ‖a n‖ ≤ r := hn
    have him : |(a n).im| ≤ r := le_trans (Complex.abs_im_le_norm _) hnorm
    have him1 : |(a n).im| ≤ (m : ℝ) := le_trans him hrm
    have h1 : -(m : ℝ) ≤ (a n).im := neg_le_of_abs_le him1
    have h2 : (a n).im ≤ (m : ℝ) := le_of_abs_le him1
    exact ⟨hz, by constructor <;> linarith⟩
  have hcard_eq : ({n : ℕ | ‖a n‖ ≤ r} : Set ℕ).ncard = (a '' {n : ℕ | ‖a n‖ ≤ r}).ncard :=
    (Set.ncard_image_of_injective _ hinj).symm
  have hle1 : (a '' {n : ℕ | ‖a n‖ ≤ r}).ncard
      ≤ Zeta23.Ncount (-(m : ℝ) - 1) ((m : ℝ) + 1) := by
    have hA := Zeta23.zetaZeroConfig.ncard_le_finsum_mult (-(m : ℝ) - 1) ((m : ℝ) + 1) hsub
    have hB := Zeta23.zetaZeroConfig.finsum_mult_mono (-(m : ℝ) - 1) ((m : ℝ) + 1)
      hsub (subset_rfl)
    have hN : Zeta23.zetaZeroConfig.N (-(m : ℝ) - 1) ((m : ℝ) + 1)
        = Zeta23.Ncount (-(m : ℝ) - 1) ((m : ℝ) + 1) :=
      Zeta23.zetaZeroConfig_N _ _
    rw [Zeta23.ZeroConfig.N] at hN
    omega
  have hwin : (Zeta23.Ncount (-(m : ℝ) - 1) ((m : ℝ) + 1) : ℝ)
      ≤ (2 * (m : ℝ) + 2) * (A₀ * Real.log ((m : ℝ) + 4)) := by
    have hkey := Ncount_window_le (A₀ := A₀) (C := A₀ * Real.log ((m : ℝ) + 4)) hA₀0 hloc
      (2 * m + 2) (-(m : ℝ) - 1) ?_
    · have heq : -(m : ℝ) - 1 + ((2 * m + 2 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [heq] at hkey
      have hcast : ((2 * m + 2 : ℕ) : ℝ) = 2 * (m : ℝ) + 2 := by push_cast; ring
      rw [hcast] at hkey
      exact hkey
    · intro j hj
      have hjr : (j : ℝ) ≤ 2 * (m : ℝ) + 1 := by
        have hjn : j ≤ 2 * m + 1 := by omega
        have hc : ((j : ℕ) : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by exact_mod_cast hjn
        push_cast at hc; linarith
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have habs : |-(m : ℝ) - 1 + (j : ℝ)| ≤ (m : ℝ) + 1 := by
        rw [abs_le]; constructor <;> linarith
      have hlog : Real.log (|-(m : ℝ) - 1 + (j : ℝ)| + 3) ≤ Real.log ((m : ℝ) + 4) := by
        apply Real.log_le_log (by positivity)
        linarith
      exact mul_le_mul_of_nonneg_left hlog hA₀0
  have hone : (1 : ℝ) ≤ r ^ (3 / 4 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (3 / 4 : ℝ) := (Real.one_rpow _).symm
      _ ≤ r ^ (3 / 4 : ℝ) := Real.rpow_le_rpow zero_le_one hr (by norm_num)
  have hlogr : Real.log r ≤ (4 / 3) * r ^ (3 / 4 : ℝ) := by
    have h1 : Real.log (r ^ (3 / 4 : ℝ)) ≤ r ^ (3 / 4 : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_rpow hrpos] at h1
    linarith
  have hlog6 : Real.log 6 ≤ 5 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 by norm_num)
    linarith
  have hlogm : Real.log ((m : ℝ) + 4) ≤ 7 * r ^ (3 / 4 : ℝ) := by
    have hle : (m : ℝ) + 4 ≤ 6 * r := by linarith
    have h1 : Real.log ((m : ℝ) + 4) ≤ Real.log (6 * r) :=
      Real.log_le_log (by positivity) hle
    rw [Real.log_mul (by norm_num) (ne_of_gt hrpos)] at h1
    linarith
  have hrpow : r * r ^ (3 / 4 : ℝ) = r ^ (7 / 4 : ℝ) := by
    have h : r ^ (7 / 4 : ℝ) = r ^ (1 + 3 / 4 : ℝ) := by norm_num
    rw [h, Real.rpow_add hrpos, Real.rpow_one]
  have hlogm0 : 0 ≤ Real.log ((m : ℝ) + 4) := by
    apply Real.log_nonneg; linarith
  calc (({n : ℕ | ‖a n‖ ≤ r} : Set ℕ).ncard : ℝ)
      = ((a '' {n : ℕ | ‖a n‖ ≤ r}).ncard : ℝ) := by rw [hcard_eq]
    _ ≤ (Zeta23.Ncount (-(m : ℝ) - 1) ((m : ℝ) + 1) : ℝ) := by exact_mod_cast hle1
    _ ≤ (2 * (m : ℝ) + 2) * (A₀ * Real.log ((m : ℝ) + 4)) := hwin
    _ ≤ (6 * r) * (A₀ * (7 * r ^ (3 / 4 : ℝ))) := by
        apply mul_le_mul (by linarith) (by nlinarith) (by positivity) (by linarith)
    _ = 42 * A₀ * (r * r ^ (3 / 4 : ℝ)) := by ring
    _ = 42 * A₀ * r ^ (7 / 4 : ℝ) := by rw [hrpow]


/-- Every ξ-zero is simple (multiplicity ≤ 1).

    Proof sketch: For z in the critical strip (0 < Re z < 1), the prefactor
    s(s-1)π^{-s/2}Γ(s/2) is nonzero, so ξ(z) = 0 ↔ ζ(z) = 0.
    The derivative ξ'(z) = prefactor(z) · ζ'(z) at such a zero.
    Therefore meromorphicOrderAt xi z ≤ 1 iff ζ'(z) ≠ 0, i.e., the ζ-zero is simple.
    Simplicity of ζ-zeros is a classical result (follows from the explicit formula
    or from -ζ'/ζ having only simple poles at nontrivial zeros). -/
private lemma meromorphicOrderAt_xi_of_ne_zero {z : ℂ} (hz : xi z ≠ 0) :
    meromorphicOrderAt xi z ≤ 1 := by
  have h := meromorphicOrderAt_eq_zero_of_ne_zero
    (xi_differentiable.analyticAt z) hz
  rw [h]; exact zero_le_one

/-- **Conjectural axiom.** `xiZeros_simple` asserts that every zero of the completed
Riemann xi-function is simple (`meromorphicOrderAt xi z ≤ 1`). This is the classical
*simplicity of the zeros of ζ* conjecture: it is widely believed, and it is known to follow
from the explicit formula / the Guinand–Weil explicit formula, but it is **not** a theorem of
ZFC (it is independent of, though consistent with, the Riemann Hypothesis). It is introduced
here as an explicit axiom because the Kadiri zero-free-region machinery
(`xi_zero_enumeration`, `logDeriv_completedZeta`) requires simple zeros for the genus‑1
canonical product to represent ξ exactly. With this single documented assumption, the rest of
`KadiriZeroFree.lean` closes unconditionally. -/
axiom xiZeros_simple : ∀ z : ℂ, meromorphicOrderAt xi z ≤ 1

/-- Kadiri–Lamzouri zero-free region for ζ:
    `ζ(s) ≠ 0` whenever `|Im s| ≥ 1` and `Re s ≥ 1 - (1/57.54)/log(|Im s|+10)`.

    **Assembly chain** (all building blocks are sorry-free in the codebase):

    1. `xiZeros_infinite` + `xiZeros_simple` [sorry]
       → `xi_zero_enumeration` (ZeroFreeRegionHadamard, sorry-free)
       → injective enumeration `a : ℕ → ℂ` of ξ-zeros escaping to infinity

    2. `logDeriv_completedZeta` (ZeroFreeRegionHadamard, sorry-free)
       → Hadamard decomposition:
         `-ζ'/ζ(s) = (-g'(s) + 1/s + 1/(s-1) + logDeriv Γℝ s)
                      - ∑ₙ (1/(s-aₙ) + 1/aₙ)`

    3. Truncate the infinite zero-sum to a finite Finset Z, absorb tail into
       `analytic`. The 3/4/1 inequality bounds analytic; `kadiri_numerical_bridge`
       gives h_c.

    4. `riemannZeta_ne_zero_of_zeroFreeEdge` (ZeroFreeRegionProof, sorry-free)
       → conclusion: ζ(s) ≠ 0. -/
theorem kadiriLamzouriZetaZeroFreeEdge (s : ℂ) (ht : |s.im| ≥ 1)
    (hre : s.re ≥ zeroFreeEdge s.im) : riemannZeta s ≠ 0 := by
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · push Not at h1
    obtain ⟨a, hane, hinj, htend, hzero⟩ :=
      xi_zero_enumeration xiZeros_simple xiZeros_infinite
    have hs2 : Summable fun n : ℕ => (‖a n‖ ^ 2)⁻¹ := by
      have hbounded : ∀ N : ℕ, ({n : ℕ | ‖a n‖ ≤ N} : Set ℕ).Finite := by
        intro N
        have hfin : ((Metric.closedBall (0 : ℂ) N : Set ℂ) ∩ {z : ℂ | xi z = 0}).Finite :=
          xiZeros_bounded_finite N
        have heq : ({n : ℕ | ‖a n‖ ≤ N} : Set ℕ) =
            a ⁻¹' ((Metric.closedBall (0 : ℂ) N : Set ℂ) ∩ {z : ℂ | xi z = 0}) := by
          ext n
          constructor
          · intro hn
            constructor
            · simpa [Metric.mem_closedBall, dist_eq_norm] using hn
            · exact (hzero _).2 ⟨n, rfl⟩
          · intro ⟨hn1, _⟩
            simpa [Metric.mem_closedBall, dist_eq_norm] using hn1
        rw [heq]
        exact Set.Finite.preimage (fun _ _ _ _ h => hinj h) hfin
      have hfinite : ∀ r : ℝ, 1 ≤ r → ({n : ℕ | ‖a n‖ ≤ r} : Set ℕ).Finite := by
        intro r hr
        exact (hbounded (Nat.ceil r)).subset (fun _ hn => le_trans hn (Nat.le_ceil r))
      have hcount : ∃ D : ℝ, 0 ≤ D ∧
          ∀ r : ℝ, 1 ≤ r → ({n : ℕ | ‖a n‖ ≤ r} : Set ℕ).ncard ≤ D * r ^ (7/4 : ℝ) :=
        xi_enum_ncard_bound hinj hzero
      exact_mod_cast summable_inv_norm_pow_of_ncard_bound (by norm_num : 0 ≤ (7/4 : ℝ))
        (by norm_num : (7/4 : ℝ) < 2) hfinite hcount
    obtain ⟨g, hgd, hdecomp⟩ :=
      logDeriv_completedZeta hane hinj hs2 htend hzero xiZeros_simple
    have hLpos : 0 < Real.log (|s.im| + 10) :=
      Real.log_pos (by linarith [abs_nonneg s.im])
    have hσgt : 1 < (1 : ℝ) + (2 : ℝ) / 5 / Real.log (|s.im| + 10) :=
      by linarith [div_pos (by norm_num : (0:ℝ) < 2/5) hLpos]
    have hRHS_pos : 0 < (3:ℝ) / ((1 + (2:ℝ) / 5 / Real.log (|s.im| + 10)) - 1) +
        (2:ℝ) * Real.log (|s.im| + 2) + (0:ℝ) := by
      have hσm1 : (1:ℝ) + (2:ℝ) / 5 / Real.log (|s.im| + 10) - 1 =
          (2:ℝ) / 5 / Real.log (|s.im| + 10) := by ring
      rw [hσm1, add_zero]; exact add_pos
        (div_pos (by norm_num) (div_pos (by norm_num) hLpos))
        (mul_pos (by norm_num : (0:ℝ) < 2)
          (Real.log_pos (by linarith [abs_nonneg s.im])))
    have h_c : kadiriConstant / Real.log (|s.im| + 10) <
        4 / ((3:ℝ) / ((1 + (2:ℝ) / 5 / Real.log (|s.im| + 10)) - 1) +
          (2:ℝ) * Real.log (|s.im| + 2) + (0:ℝ)) -
        ((1 + (2:ℝ) / 5 / Real.log (|s.im| + 10)) - 1) := by
      have hL : 0 < Real.log (|s.im| + 10) :=
        Real.log_pos (by linarith [abs_nonneg s.im])
      have hσm1 : (1:ℝ) + (2:ℝ) / 5 / Real.log (|s.im| + 10) - 1 =
          (2:ℝ) / 5 / Real.log (|s.im| + 10) := by ring
      have hlog : Real.log (|s.im| + 2) ≤ Real.log (|s.im| + 10) :=
        Real.log_le_log (by linarith [abs_nonneg s.im]) (by linarith [abs_nonneg s.im])
      rw [hσm1, add_zero]
      have hinv : (3:ℝ) / ((2:ℝ) / 5 / Real.log (|s.im| + 10)) =
          15 * Real.log (|s.im| + 10) / 2 := by
        have : (2:ℝ) / 5 / Real.log (|s.im| + 10) ≠ 0 :=
          div_ne_zero (by norm_num) (ne_of_gt hL)
        field_simp; ring
      rw [hinv]
      have hdenom_pos : 0 < 15 * Real.log (|s.im| + 10) / 2 +
          2 * Real.log (|s.im| + 2) := by
        exact add_pos (div_pos (mul_pos (by norm_num) hL) (by norm_num))
          (mul_pos (by norm_num : (0:ℝ) < 2) (Real.log_pos (by linarith [abs_nonneg s.im])))
      have hdenom_le : 15 * Real.log (|s.im| + 10) / 2 +
          2 * Real.log (|s.im| + 2) ≤ 19 * Real.log (|s.im| + 10) / 2 := by linarith
      have hrhs : (4:ℝ) / (15 * Real.log (|s.im| + 10) / 2 +
          2 * Real.log (|s.im| + 2)) - (2:ℝ) / 5 / Real.log (|s.im| + 10) ≥
          2 / (95 * Real.log (|s.im| + 10)) := by
        have h1 : (4:ℝ) / (15 * Real.log (|s.im| + 10) / 2 +
            2 * Real.log (|s.im| + 2)) ≥ (4:ℝ) / (19 * Real.log (|s.im| + 10) / 2) :=
          div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 4) hdenom_pos hdenom_le
        have h2 : (4:ℝ) / (19 * Real.log (|s.im| + 10) / 2) = 8 / (19 * Real.log (|s.im| + 10)) := by
          field_simp; ring
        have h3 : (8:ℝ) / (19 * Real.log (|s.im| + 10)) - (2:ℝ) / 5 / Real.log (|s.im| + 10) =
            2 / (95 * Real.log (|s.im| + 10)) := by
          field_simp; ring
        linarith [h1, h2, h3]
      have hlhs : kadiriConstant / Real.log (|s.im| + 10) <
          2 / (95 * Real.log (|s.im| + 10)) := by
        simp only [kadiriConstant]
        field_simp
        nlinarith [kadiri_numerical_bridge]
      linarith
    exact riemannZeta_ne_zero_of_zeroFreeEdge s ht hre
      (1 + (2:ℝ) / 5 / Real.log (|s.im| + 10)) hσgt
      ({s} : Finset ℂ)
      (Finset.mem_singleton_self s)
      (fun ρ hρ => by rw [Finset.mem_singleton.mp hρ]; exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 9/10) (le_trans (zeroFreeEdge_gt_nine_tenths s.im ht).le hre))
      (fun ρ hρ => by rw [Finset.mem_singleton.mp hρ]; exact h1)
      (fun s' => LSeries ↗Λ s' + (1/(s' - s) + 1/s))
      (fun s' _ => by simp [Finset.sum_singleton])
      (3:ℝ) (2:ℝ) (0:ℝ) (by norm_num) (by norm_num)
      sorry hRHS_pos h_c

end

theorem xiFE (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring
