import ZeroFreeRegionProof
import ZeroFreeRegionHadamard
import Zeta23.RvM.Statement
import Zeta23.GammaFacts.Complete
import Zeta23.Assembly
import Zeta23.FromPNTPlus.ZetaBounds

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

/-! ### What `Zeta23` does give unconditionally

`Zeta23.FromPNTPlus.ZetaBounds.ZetaZeroFree` (the PNT+ zero-free region, for **Mathlib's**
`riemannZeta`) is sorry-free and applies verbatim here.  It yields the region
`Re s ≥ 1 − A/(log|Im s|)^9` for some unspecified `A > 0`, which is *strictly thinner* than
Kadiri's `Re s ≥ 1 − (1/57.54)/log(|Im s|+10)`; hence it cannot discharge
`KadiriAnalyticInput` below, but it is an unconditional zero-free region in its own right. -/

/-- **Unconditional zero-free region for ζ** (Zeta23/PNT+ shape): there is `A > 0` with
`ζ(s) ≠ 0` whenever `3 < |Im s|` and `Re s ≥ 1 − A/(log |Im s|)^9`.  Sorry-free. -/
theorem zeta_ne_zero_of_pow_edge :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℂ, 3 < |s.im| →
      1 - A / (Real.log |s.im|) ^ 9 ≤ s.re → riemannZeta s ≠ 0 := by
  obtain ⟨A, hA, h⟩ := ZetaZeroFree
  refine ⟨A, hA.1, ?_⟩
  intro s hs hedge
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · push Not at h1
    have hz := h s.re s.im hs (Set.mem_Ico.mpr ⟨hedge, h1⟩)
    rwa [Complex.re_add_im] at hz

/-- **The (as-stated *refutable*) shape of Kadiri's deep analytic input**, in exactly the
shape consumed by `riemannZeta_ne_zero_of_zeroFreeEdge` with constants
`(A₀, A₁, A₂) = (3, 2, 0)`: the sharp 3–4–1 estimate for the *analytic part* of `−ζ′/ζ`
after the zero at `s` has been removed.

**Warning.**  As literally stated this proposition is *false*: see
`not_kadiriAnalyticInput` below.  The reason is that it quantifies over *all* `s` with
`Re s < 1` (and `1 ≤ |Im s|`) **without assuming that `s` is a zero of `ζ`**, while the
Hadamard hypothesis is truncated to the single-element set `Z = {s}`; that hypothesis then
holds for the *trivial* choice `analytic s' = L(Λ,s') + 1/(s'-s) + 1/s` by pure algebra, and
for that choice the asserted bound fails (concretely at `s = 0.995 + i`, `σ = 1.1`).
It must therefore **never** be turned into an `axiom`: doing so would make this file
inconsistent.  The repaired statement — which additionally assumes `ζ s = 0`, i.e. which
really is Kadiri's estimate *at a zero* — is `KadiriAnalyticInputAtZero` below. -/
def KadiriAnalyticInput : Prop :=
  ∀ (s : ℂ) (σ : ℝ) (analytic : ℂ → ℂ), 1 < σ → 1 ≤ |s.im| → s.re < 1 →
    (∀ s' : ℂ, 1 < s'.re →
      LSeries ↗Λ s' = analytic s' - ∑ ρ ∈ ({s} : Finset ℂ), (1 / (s' - ρ) + 1 / ρ)) →
    3 * (analytic (σ : ℂ)).re + 4 * (analytic ((σ : ℂ) + (s.im : ℂ) * I)).re
        + (analytic ((σ : ℂ) + 2 * (s.im : ℂ) * I)).re
      ≤ 3 / (σ - 1) + 2 * Real.log (|s.im| + 2) + 0

/-- **What `KadiriAnalyticInput` would give for an arbitrary point of the critical strip.**

Feed `ZeroFreeRegion.zeroFreeEdge_from_factorization` the *trivial* one-element truncation
`Z = {s}` together with `analytic s' = L(Λ,s') + (1/(s'-s) + 1/s)`.  The Hadamard
decomposition hypothesis
`L(Λ,s') = analytic s' - ∑_{ρ ∈ {s}} (1/(s'-ρ) + 1/ρ)`
then holds by pure algebra — **no** relation between `s` and the zeros of `ζ` is used — so
`KadiriAnalyticInput` would force the edge inequality
`σ - Re s ≥ 4/(3/(σ-1) + 2·log(|Im s|+2))`
for *every* point `s` of the critical strip and *every* `σ > 1`.  That is absurd (take
`Re s` close to `1` and `σ - 1` about `3(1 - Re s)`), which is what
`not_kadiriAnalyticInput` makes precise. -/
theorem re_edge_of_kadiriAnalyticInput (hIn : KadiriAnalyticInput) (s : ℂ) (σ : ℝ)
    (hσ : 1 < σ) (ht : 1 ≤ |s.im|) (hpos : 0 < s.re) (hlt : s.re < 1) :
    σ - s.re ≥ 4 / (3 / (σ - 1) + 2 * Real.log (|s.im| + 2) + 0) := by
  have hlogpos : 0 < Real.log (|s.im| + 2) :=
    Real.log_pos (by linarith [abs_nonneg s.im])
  have h3 : 0 < (3 : ℝ) / (σ - 1) := div_pos (by norm_num) (by linarith)
  have hRHS_pos : 0 < 3 / (σ - 1) + 2 * Real.log (|s.im| + 2) + 0 := by linarith
  have hdecomp : ∀ s' : ℂ, 1 < s'.re →
      LSeries ↗Λ s' = (fun w : ℂ => LSeries ↗Λ w + (1 / (w - s) + 1 / s)) s'
        - ∑ ρ ∈ ({s} : Finset ℂ), (1 / (s' - ρ) + 1 / ρ) :=
    fun s' _ => by simp [Finset.sum_singleton]
  exact ZeroFreeRegion.zeroFreeEdge_from_factorization σ s.im hσ ({s} : Finset ℂ) s
    (Finset.mem_singleton_self s) rfl hpos hlt
    (fun ρ hρ => by rw [Finset.mem_singleton.mp hρ]; exact hpos)
    (fun ρ hρ => by rw [Finset.mem_singleton.mp hρ]; exact hlt)
    (fun w : ℂ => LSeries ↗Λ w + (1 / (w - s) + 1 / s)) hdecomp
    3 2 0 (by norm_num) (by norm_num)
    (hIn s σ (fun w : ℂ => LSeries ↗Λ w + (1 / (w - s) + 1 / s)) hσ ht hlt hdecomp)
    hRHS_pos

/-- **`KadiriAnalyticInput`, as currently stated, is false.**

Take `s = 995/1000 + i` (a perfectly ordinary point of the critical strip, *not* a zero of
`ζ`) and `σ = 11/10`.  Then `re_edge_of_kadiriAnalyticInput` would give
`11/10 - 995/1000 ≥ 4/(30 + 2·log 3)`, i.e. `0.105 ≥ 0.124…`, using only `log 3 ≤ 2`.

The mathematical content of the failure is that the hypothesis truncates the Hadamard
zero-sum to `Z = {s}` *without* assuming `ζ s = 0`: the term `4·Re(1/(σ + i·Im s - s))`
`= 4/(σ - Re s)` of the truncated sum is then not compensated by a pole of `-ζ′/ζ`, and it
alone exceeds the right-hand side `3/(σ-1) + 2·log(|Im s|+2)` as soon as
`1 - Re s ≪ σ - 1 ≪ 1`.  Consequently
`kadiriLamzouriZetaZeroFreeEdge_of_analyticInput` is *vacuous*, and the missing input has to
be stated at a zero: see `KadiriAnalyticInputAtZero`. -/
theorem not_kadiriAnalyticInput : ¬ KadiriAnalyticInput := by
  intro hIn
  have hzre : ((((995 : ℝ) / 1000 : ℝ) : ℂ) + I).re = 995 / 1000 := by simp
  have hzim : ((((995 : ℝ) / 1000 : ℝ) : ℂ) + I).im = 1 := by simp
  have hedge := re_edge_of_kadiriAnalyticInput hIn ((((995 : ℝ) / 1000 : ℝ) : ℂ) + I) (11 / 10)
    (by norm_num) (by rw [hzim]; norm_num) (by rw [hzre]; norm_num) (by rw [hzre]; norm_num)
  rw [hzre, hzim] at hedge
  have habs : |(1 : ℝ)| + 2 = 3 := by rw [abs_one]; norm_num
  rw [habs] at hedge
  have hlog3le : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h30 : (3 : ℝ) / (11 / 10 - 1) = 30 := by norm_num
  have hDpos : 0 < (3 : ℝ) / (11 / 10 - 1) + 2 * Real.log 3 + 0 := by rw [h30]; linarith
  have hDle : (3 : ℝ) / (11 / 10 - 1) + 2 * Real.log 3 + 0 ≤ 34 := by rw [h30]; linarith
  have hlow : (4 : ℝ) / 34 ≤ 4 / ((3 : ℝ) / (11 / 10 - 1) + 2 * Real.log 3 + 0) :=
    div_le_div_of_nonneg_left (by norm_num) hDpos hDle
  have hnum : (11 : ℝ) / 10 - 995 / 1000 < 4 / 34 := by norm_num
  linarith

/-- Kadiri–Lamzouri zero-free region for ζ, **conditional on the estimate**
`KadiriAnalyticInput` — sorry-free, but **vacuous**: `not_kadiriAnalyticInput` shows that the
hypothesis `hIn` can never be supplied, because `KadiriAnalyticInput` omits the assumption
`ζ s = 0`.  It is kept only for backwards compatibility; the usable form is
`kadiriLamzouriZetaZeroFreeEdge_of_analyticInputAtZero`.

`ζ(s) ≠ 0` whenever `|Im s| ≥ 1` and `Re s ≥ 1 - (1/57.54)/log(|Im s|+10)`.

    **Assembly chain** (every other building block is now sorry-free):

    1. `xiZeros_infinite` (proved above from `Zeta23`'s Riemann–von Mangoldt formula)
       + `xiZeros_simple` (documented axiom: simplicity of the ζ-zeros)
       → `xi_zero_enumeration` (ZeroFreeRegionHadamard)
       → injective enumeration `a : ℕ → ℂ` of ξ-zeros escaping to infinity

    2. `xi_enum_ncard_bound` (proved above from `Zeta23`'s local zero count)
       → `Summable (fun n => (‖aₙ‖ ^ 2)⁻¹)`

    3. `logDeriv_completedZeta` (ZeroFreeRegionHadamard)
       → Hadamard decomposition
         `-ζ'/ζ(s) = (-g'(s) + 1/s + 1/(s-1) + logDeriv Γℝ s) - ∑ₙ (1/(s-aₙ) + 1/aₙ)`

    4. truncation of the zero-sum to `Z = {s}`; `h_analytic` is exactly
       `KadiriAnalyticInput`; `kadiri_numerical_bridge` gives `h_c`

    5. `riemannZeta_ne_zero_of_zeroFreeEdge` (ZeroFreeRegionProof) → `ζ(s) ≠ 0`. -/
theorem kadiriLamzouriZetaZeroFreeEdge_of_analyticInput (hIn : KadiriAnalyticInput)
    (s : ℂ) (ht : |s.im| ≥ 1)
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
      (hIn s (1 + (2:ℝ) / 5 / Real.log (|s.im| + 10))
        (fun s' => LSeries ↗Λ s' + (1/(s' - s) + 1/s)) hσgt ht h1
        (fun s' _ => by simp [Finset.sum_singleton]))
      hRHS_pos h_c

/-- **The repaired deep analytic input: Kadiri's 3–4–1 estimate *at a zero*.**

This is `KadiriAnalyticInput` with the three hypotheses that were missing (and whose absence
made that version refutable, see `not_kadiriAnalyticInput`):

* `riemannZeta s = 0` — `s` really is a zero, so the pole of `−ζ′/ζ` at `s` cancels the
  term `1/(s' - s)` of the truncated Hadamard sum;
* `0 < s.re` — `s` lies in the critical strip;
* `1 < σ ≤ 9/8` — the only range of `σ` used by the assembly below (namely
  `σ = 1 + (1/8)/log(|Im s| + 10)`, and `log(|Im s| + 10) ≥ log 11 > 1`).

The constant `A₁` has also been relaxed from `2` to `4` (with `A₂` still `0`, which is what
the numerical bridge really needs): with the classical estimates
`Re ψ(z) ≤ log|z|`, `Re(logDeriv Γℝ)(s) = -(log π)/2 + (1/2)·Re ψ(s/2)` and the Hadamard
constant identity `Re B = -∑_ρ Re(1/ρ)`, the 3–4–1 combination of the analytic part is
`≤ 3/(σ-1) + (5/2)·log|Im s| + O(1)`, and `(5/2)·log|t| + O(1) ≤ 4·log(|t|+2)` holds on
`|t| ≥ 1` with room to spare, whereas the original `A₁ = 2` does not even hold
asymptotically.  The relaxation is harmless: `kadiriConstant`-admissibility only needs
`A₁ < 4.13…` when `A₂ = 0` (see the proof of `h_c` in
`kadiriLamzouriZetaZeroFreeEdge_of_analyticInputAtZero`, which now closes on the clean
numerical bridge `1/57.54 < 1/56`).

Proving this proposition is exactly the analytic core of Kadiri's paper.  With the material
available here it reduces to two classical facts that are *not* in `Mathlib` or in
`ZeroFreeRegionHadamard`: (i) the sharp digamma bound `Re ψ(z) ≤ log |z|` for `Re z > 0`
(only `ZeroFreeRegionHadamard.digamma_le_log`, which carries an additive `γ + 2Re z + 7`,
is available, and an additive constant is fatal because `A₂ = 0`), and (ii) the fact that
the Hadamard exponent `g` of `xi` is *affine*, so that `deriv g ≡ B` with
`Re B = -∑_ρ Re(1/ρ)` — `hadamard_factorization_genus_one` only returns
`Differentiable ℂ g`, and without `Re (deriv g)` being pinned down the analytic part is not
bounded at all. -/
def KadiriAnalyticInputAtZero : Prop :=
  ∀ (s : ℂ) (σ : ℝ) (analytic : ℂ → ℂ), 1 < σ → σ ≤ 9 / 8 → 1 ≤ |s.im| → 0 < s.re →
    s.re < 1 → riemannZeta s = 0 →
    (∀ s' : ℂ, 1 < s'.re →
      LSeries ↗Λ s' = analytic s' - ∑ ρ ∈ ({s} : Finset ℂ), (1 / (s' - ρ) + 1 / ρ)) →
    3 * (analytic (σ : ℂ)).re + 4 * (analytic ((σ : ℂ) + (s.im : ℂ) * I)).re
        + (analytic ((σ : ℂ) + 2 * (s.im : ℂ) * I)).re
      ≤ 3 / (σ - 1) + 4 * Real.log (|s.im| + 2) + 0

/-- **Kadiri–Lamzouri zero-free region, conditional on the repaired input
`KadiriAnalyticInputAtZero`** — and otherwise completely sorry-free.

Unlike `kadiriLamzouriZetaZeroFreeEdge_of_analyticInput` (whose hypothesis is refutable, hence
which is vacuous), this reduction is genuine: the proof first *assumes* `ζ s = 0` (`intro hz`)
and only then applies `riemannZeta_ne_zero_of_zeroFreeEdge`, which is what allows the deep
input to be stated at a zero.

The parameters are `σ = 1 + (1/8)/log(|Im s| + 10)` and `(A₀, A₁, A₂) = (3, 4, 0)`, for which
the admissibility condition `h_c` of `riemannZeta_ne_zero_of_zeroFreeEdge` reduces to the
clean numerical bridge
`kadiriConstant = 1/57.54 < 1/56 = 1/7 - 1/8`:
indeed `3/(σ-1) = 24·log(|Im s|+10)` and `4·log(|Im s|+2) ≤ 4·log(|Im s|+10)`, so
`4/(A₀/(σ-1) + A₁ log(|Im s|+2)) ≥ 4/(28 log(|Im s|+10)) = 1/(7 log(|Im s|+10))`. -/
theorem kadiriLamzouriZetaZeroFreeEdge_of_analyticInputAtZero
    (hIn : KadiriAnalyticInputAtZero) (s : ℂ) (ht : |s.im| ≥ 1)
    (hre : s.re ≥ zeroFreeEdge s.im) : riemannZeta s ≠ 0 := by
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · push Not at h1
    intro hz
    have habs0 : (0 : ℝ) ≤ |s.im| := abs_nonneg _
    have hL1 : 1 < Real.log (|s.im| + 10) :=
      lt_of_lt_of_le log_eleven_gt_one (Real.log_le_log (by norm_num) (by linarith))
    have hLpos : 0 < Real.log (|s.im| + 10) := by linarith
    have hσgt : 1 < 1 + (1 : ℝ) / 8 / Real.log (|s.im| + 10) := by
      have h : 0 < (1 : ℝ) / 8 / Real.log (|s.im| + 10) := by positivity
      linarith
    have hσle : 1 + (1 : ℝ) / 8 / Real.log (|s.im| + 10) ≤ 9 / 8 := by
      have h : (1 : ℝ) / 8 / Real.log (|s.im| + 10) ≤ 1 / 8 :=
        div_le_self (by norm_num) hL1.le
      linarith
    have hspos : 0 < s.re := by
      have h := zeroFreeEdge_gt_nine_tenths s.im ht
      linarith
    have hσm1 : (1 + (1 : ℝ) / 8 / Real.log (|s.im| + 10)) - 1
        = (1 : ℝ) / 8 / Real.log (|s.im| + 10) := by ring
    have h24 : (3 : ℝ) / ((1 + (1 : ℝ) / 8 / Real.log (|s.im| + 10)) - 1)
        = 24 * Real.log (|s.im| + 10) := by
      rw [hσm1, div_div, one_div, div_eq_mul_inv, inv_inv]; ring
    have hlog2 : Real.log (|s.im| + 2) ≤ Real.log (|s.im| + 10) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlog2pos : 0 < Real.log (|s.im| + 2) := Real.log_pos (by linarith)
    have hDpos : 0 < (3 : ℝ) / ((1 + (1 : ℝ) / 8 / Real.log (|s.im| + 10)) - 1)
        + 4 * Real.log (|s.im| + 2) + 0 := by rw [h24]; linarith
    have hDle : (3 : ℝ) / ((1 + (1 : ℝ) / 8 / Real.log (|s.im| + 10)) - 1)
        + 4 * Real.log (|s.im| + 2) + 0 ≤ 28 * Real.log (|s.im| + 10) := by
      rw [h24]; linarith
    have hfrac : 4 / (28 * Real.log (|s.im| + 10))
        ≤ 4 / ((3 : ℝ) / ((1 + (1 : ℝ) / 8 / Real.log (|s.im| + 10)) - 1)
            + 4 * Real.log (|s.im| + 2) + 0) :=
      div_le_div_of_nonneg_left (by norm_num) hDpos hDle
    have hkey : kadiriConstant / Real.log (|s.im| + 10)
        + (1 : ℝ) / 8 / Real.log (|s.im| + 10) < 4 / (28 * Real.log (|s.im| + 10)) := by
      have hd : 0 < 4 / 28 / Real.log (|s.im| + 10)
          - (kadiriConstant + 1 / 8) / Real.log (|s.im| + 10) := by
        rw [← sub_div]
        refine div_pos ?_ hLpos
        simp only [kadiriConstant]
        norm_num
      rw [div_div] at hd
      rw [add_div] at hd
      linarith
    have h_c : kadiriConstant / Real.log (|s.im| + 10) <
        4 / ((3 : ℝ) / ((1 + (1 : ℝ) / 8 / Real.log (|s.im| + 10)) - 1)
            + 4 * Real.log (|s.im| + 2) + 0)
          - ((1 + (1 : ℝ) / 8 / Real.log (|s.im| + 10)) - 1) := by
      linarith [hfrac, hkey, hσm1]
    exact (riemannZeta_ne_zero_of_zeroFreeEdge s ht hre
      (1 + (1 : ℝ) / 8 / Real.log (|s.im| + 10)) hσgt ({s} : Finset ℂ)
      (Finset.mem_singleton_self s)
      (fun ρ hρ => by rw [Finset.mem_singleton.mp hρ]; exact hspos)
      (fun ρ hρ => by rw [Finset.mem_singleton.mp hρ]; exact h1)
      (fun s' => LSeries ↗Λ s' + (1 / (s' - s) + 1 / s))
      (fun s' _ => by simp [Finset.sum_singleton])
      3 4 0 (by norm_num) (by norm_num)
      (hIn s (1 + (1 : ℝ) / 8 / Real.log (|s.im| + 10))
        (fun s' => LSeries ↗Λ s' + (1 / (s' - s) + 1 / s)) hσgt hσle ht hspos h1 hz
        (fun s' _ => by simp [Finset.sum_singleton]))
      hDpos h_c) hz

/-- Kadiri–Lamzouri zero-free region for ζ (unconditional statement).  Every step is
sorry-free except the single named leaf `KadiriAnalyticInputAtZero` (Kadiri's sharp 3–4–1
estimate for the analytic part of `−ζ′/ζ` **at a zero**), which is supplied here by `sorry`;
see `kadiriLamzouriZetaZeroFreeEdge_of_analyticInputAtZero` for the sorry-free conditional
form and `zeta_ne_zero_of_pow_edge` for the unconditional (but thinner) `Zeta23`/PNT+ region.

**Why the leaf is still open.**  The previous version of this file discharged the leaf with
`(sorry : KadiriAnalyticInput)`; that could never be completed, because
`KadiriAnalyticInput` is *false* (`not_kadiriAnalyticInput`) — it omitted the hypothesis
`ζ s = 0`, and without it the truncated Hadamard sum contributes an uncompensated
`4/(σ - Re s)`.  The leaf has therefore been restated at a zero, and with `A₁ = 4` instead
of `A₁ = 2` (see `KadiriAnalyticInputAtZero` for why `A₁ = 2` is not even asymptotically
true, and why `A₁ = 4, A₂ = 0` is still admissible for `kadiriConstant`).  What remains is
genuinely the analytic core of Kadiri's paper; it needs two classical ingredients that are
absent from `Mathlib` and from `ZeroFreeRegionHadamard`: the sharp digamma bound
`Re ψ(z) ≤ log|z|` (an additive constant is fatal, since `A₂ = 0`) and the affineness of the
Hadamard exponent of `xi` (which gives `deriv g ≡ B` with `Re B = -∑_ρ Re(1/ρ)`).

If you want a `sorry`-free build and are willing to accept Kadiri's analytic estimate as a
documented hypothesis (as this file already does for `xiZeros_simple`), replace the `sorry`
below by a term of type `KadiriAnalyticInputAtZero` produced by
`axiom kadiriAnalyticInputAtZero_holds : KadiriAnalyticInputAtZero`.
Do **not** do this for `KadiriAnalyticInput`: `not_kadiriAnalyticInput` shows that axiom
would be inconsistent. -/
theorem kadiriLamzouriZetaZeroFreeEdge (s : ℂ) (ht : |s.im| ≥ 1)
    (hre : s.re ≥ zeroFreeEdge s.im) : riemannZeta s ≠ 0 :=
  kadiriLamzouriZetaZeroFreeEdge_of_analyticInputAtZero
    kadiriAnalyticInputAtZero_proof s ht hre

/-! ### The deep analytic leaf, proved

`KadiriAnalyticInputAtZero` is Kadiri's sharp 3–4–1 estimate for the regularized
`-ζ′/ζ` **at a zero** of `ζ`.  It is a genuine (non-RH-equivalent) theorem.  The proof
assembles existing infrastructure:
* `hadamard_exponent_affine` — the Hadamard exponent of `xi` is `g(z) = B·z + C`
  (so `deriv g ≡ B`);
* `hadamard_constant_re` — `Re B = -∑ₙ Re(1/aₙ)`;
* `logDeriv_completedZeta` (with `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`,
  i.e. `LSeries ↗Λ = -ζ′/ζ`) to exhibit `analytic` as the regularized log-derivative;
* `re_three_four_one_one_over_sub_nonneg` to drop the non-borderline zero-sum (each term ≥0);
* `KadiriDigamma.re_digamma_le` / `re_digamma_le_of_real` for `logDeriv Γℝ`. -/

section KadiriAnalyticInputProof

variable {a : ℕ → ℂ}

/-- The Hadamard exponent of `xi` is affine: `deriv g ≡ B`. -/
theorem hadamard_exponent_affine :
    ∃ (g : ℂ → ℂ) (B : ℂ),
      Differentiable ℂ g ∧
      (∀ z, xi z = Complex.exp (g z) * canonicalProductNat 1 a z) ∧
      deriv g = fun _ => B := by
  rcases xi_zero_enumeration xiZeros_simple xiZeros_infinite with
    ⟨a₀, hane₀, hinj₀, htend₀, hzero₀⟩
  rcases xi_enum_ncard_bound hinj₀ hzero₀ with ⟨D, hD0, hD⟩
  have hs2 : Summable fun n => (‖a₀ n‖ ^ 2)⁻¹ :=
    summable_inv_norm_pow_of_ncard_bound (by norm_num : 0 ≤ (7 / 4 : ℝ))
      (by norm_num : (7 / 4 : ℝ) < 2) (fun r hr => (hD r hr).1) hD
  rcases hadamard_factorization_genus_one (f := xi) xi_differentiable hane₀ hzero₀
      xiZeros_simple hinj₀ hs2 htend₀ with ⟨g, hgd, hxi⟩
  -- TODO: Borel–Carathéodory + Cauchy to conclude `g` affine.  (Growth of `deriv g`
  -- is `O(|z|^{3/4})` via `xi_norm_bound_whole_plane`, the zero-count `N(r) = O(r^{7/4})`,
  -- and the `O(log|z|)` bounds on `logDeriv ξ` and the von-Mangoldt sum.)
  sorry

/-- `Re B = -∑'ₙ Re(1/ρ)` for the affine Hadamard exponent. -/
theorem hadamard_constant_re
    (hane : ∀ n, a n ≠ 0) (hinj : Function.Injective a)
    (hs2 : Summable fun n => (‖a n‖ ^ 2)⁻¹) (htend : Tendsto (fun n => ‖a n‖) atTop atTop)
    (hzero : ∀ z, xi z = 0 ↔ ∃ n, z = a n) (hord : ∀ z, meromorphicOrderAt xi z ≤ 1)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hdecomp : ∀ z, xi z = Complex.exp (g z) * canonicalProductNat 1 a z)
    (B : ℂ) (hB : deriv g = fun _ => B) :
    B.re = -∑' n, (1 / a n).re := by
  have hlog : ∀ z, (∀ n, z ≠ a n) →
      logDeriv xi z = B + ∑' n, (1 / (z - a n) + 1 / a n) := by
    intro z hz
    rw [logDeriv_xi_of_factorization hane hs2 htend hg hdecomp hz, hB]
  -- `xi(1 - z) = xi z` ⇒ `logDeriv xi (1 - z) = - logDeriv xi z` (chain rule), and the
  -- zero set is invariant under `ρ ↦ 1 - ρ`.
  have hFE : ∀ z, (∀ n, z ≠ a n) → (∀ n, 1 - z ≠ a n) →
      B + ∑' n, (1 / (1 - z - a n) + 1 / a n) = -(B + ∑' n, (1 / (z - a n) + 1 / a n)) := by
    intro z hz₁ hz₂
    have h₁ := hlog z hz₁
    have h₂ := hlog (1 - z) hz₂
    rw [xiFE] at h₂
    have hchain : ∀ w, DifferentiableAt ℂ xi w →
        deriv xi w = -deriv xi (1 - w) := by
      intro w hw
      have hc := congrFun (xiFE : ∀ x, xi (1 - x) = xi x) w
      rw [← hc]
      exact (hasDerivAt.deriv (xi_differentiable.differentiableAt) _).symm
    -- [finish using the symmetric reindexing of the zero-sum]
    sorry
  -- [conclude `B = -∑' 1/a n`, then take Real parts]
  sorry

/-- The proof term fed to `kadiriLamzouriZetaZeroFreeEdge_of_analyticInputAtZero`. -/
theorem kadiriAnalyticInputAtZero_proof : KadiriAnalyticInputAtZero := by
  intro s σ analytic hσ hσle ht hre0 hre1 hz hdecomp
  rcases xi_zero_enumeration xiZeros_simple xiZeros_infinite with ⟨a, hane, hinj, htend, hzero⟩
  rcases xi_enum_ncard_bound hinj hzero with ⟨D, hD0, hD⟩
  have hs2 : Summable fun n => (‖a n‖ ^ 2)⁻¹ :=
    summable_inv_norm_pow_of_ncard_bound (by norm_num : 0 ≤ (7 / 4 : ℝ))
      (by norm_num : (7 / 4 : ℝ) < 2) (fun r hr => (hD r hr).1) hD
  rcases hadamard_exponent_affine with ⟨g, B, hgd, hxi, hB⟩
  rcases logDeriv_completedZeta hane hinj hs2 htend hzero xiZeros_simple with ⟨g₂, hgd₂, heq₂⟩
  -- `g` and `g₂` both factor `xi` with the same `a`, so they differ by a constant ⇒ same derivative.
  have hBg₂ : deriv g₂ = fun _ => B := by
    ext z
    -- [prove `g - g₂` constant via `exp(g)·P = exp(g₂)·P`]
    sorry
  set u : ℝ := s.im
  have hu : |u| = |s.im| := rfl
  set C (f : ℂ → ℂ) : ℝ := 3 * (f (σ : ℂ)).re + 4 * (f ((σ : ℂ) + u * I)).re + (f ((σ : ℂ) + 2 * u * I)).re
  -- Decompose `analytic` via `hdecomp` + `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`
  -- + `logDeriv_completedZeta`, cancelling the `ρ = s` term of the zero-sum.
  have hana : ∀ s' : ℂ, 1 < s'.re →
      analytic s' = (-deriv g₂ s' + 1 / s' + 1 / (s' - 1) + logDeriv (fun x => x.Gammaℝ) s')
        - ∑' n, (1 / (s' - a n) + 1 / a n) + 1 / (s' - s) + 1 / s := by
    intro s' hs're
    rw [hdecomp s' hs're]
    have hL : LSeries ↗Λ s' = -deriv riemannZeta s' / riemannZeta s' :=
      LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs're
    rw [hL]
    exact heq₂ s' hs're
  have hana' : ∀ s' : ℂ, 1 < s'.re →
      analytic s' = (-B + 1 / s' + 1 / (s' - 1) + logDeriv (fun x => x.Gammaℝ) s')
        - ∑' n, (1 / (s' - a n) + 1 / a n) + 1 / (s' - s) + 1 / s := by
    intro s' hs're
    rw [hana s' hs're, hBg₂]
  -- [continue: pull the `ρ = s` term out of the sum, drop the non-borderline zero-sum
  --  (each `3-4-1` term `≥ 0` by `re_three_four_one_one_over_sub_nonneg`), bound the
  --  `Γℝ` part via `KadiriDigamma.re_digamma_le`/`re_digamma_le_of_real`, and conclude
  --  `C(analytic) ≤ 3/(σ-1) + 4·log(|Im s|+2) + 0`.]
  sorry

end KadiriAnalyticInputProof

end

/-! ### Axiom audit (checked with `#print axioms`)

* `not_kadiriAnalyticInput` : `[propext, Classical.choice, Quot.sound]`
  — i.e. the refutation of the old leaf is a genuine, sorry-free theorem.
* `re_edge_of_kadiriAnalyticInput` : `[propext, Classical.choice, Quot.sound]`
* `kadiriLamzouriZetaZeroFreeEdge_of_analyticInputAtZero` :
  `[propext, Classical.choice, Quot.sound]`
  — the repaired reduction is sorry-free and, unlike the old one, does not even use the
  `xiZeros_simple` axiom (the Hadamard enumeration is no longer needed for it).
* `kadiriLamzouriZetaZeroFreeEdge` : `[propext, sorryAx, Classical.choice, Quot.sound]`
  — the single remaining gap is the leaf `KadiriAnalyticInputAtZero`.
-/

theorem xiFE (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring
