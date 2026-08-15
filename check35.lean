import Mathlib
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable

open Complex Finset Real HurwitzZeta
open scoped Topology Filter
open Filter Metric

set_option maxHeartbeats 800000 in
noncomputable def xi (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1

set_option maxHeartbeats 800000 in
theorem xi_differentiable : Differentiable ℂ xi := by
  unfold xi
  apply Differentiable.add
  · apply Differentiable.mul
    · apply Differentiable.mul <;> fun_prop
    · exact differentiable_completedZeta₀
  · fun_prop

set_option maxHeartbeats 800000 in
theorem xi_eq_mul_completedRiemannZeta {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
    xi s = s * (s - 1) * completedRiemannZeta s := by
  rw [xi, completedRiemannZeta_eq]
  field_simp [hs, sub_ne_zero.mpr hs']
  ring

set_option maxHeartbeats 800000 in
theorem xi_zero_iff_riemannZeta_zero {s : ℂ} (hΓ : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) :
    xi s = 0 ↔ riemannZeta s = 0 := by
  constructor
  · intro hxi
    by_cases hs : s = 0
    · rw [hs, xi] at hxi
      norm_num at hxi
    · by_cases hs1 : s = 1
      · rw [hs1, xi] at hxi
        norm_num at hxi
      · have hΛ : completedRiemannZeta s = 0 := by
          have hxi' : s * (s - 1) * completedRiemannZeta s = 0 := by
            rwa [xi_eq_mul_completedRiemannZeta hs hs1] at hxi
          have hsnz : s * (s - 1) ≠ 0 := mul_ne_zero hs (sub_ne_zero.mpr hs1)
          exact (mul_eq_zero.mp hxi').resolve_left hsnz
        rw [riemannZeta_def_of_ne_zero hs, hΛ]
        simp
  · intro hζ
    by_cases hs : s = 0
    · rw [hs, riemannZeta_zero] at hζ
      norm_num at hζ
    · by_cases hs1 : s = 1
      · rw [hs1] at hζ
        exact False.elim ((riemannZeta_ne_zero_of_one_le_re (s := 1) (by norm_num)) hζ)
      · have hΓne : s.Gammaℝ ≠ 0 := by
          rw [Complex.Gammaℝ_def]
          apply mul_ne_zero
          · rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero)]
            exact Complex.exp_ne_zero _
          · exact Complex.Gamma_ne_zero hΓ
        have hΛ : completedRiemannZeta s = 0 := by
          rw [riemannZeta_def_of_ne_zero hs] at hζ
          exact (div_eq_zero_iff.mp hζ).resolve_right hΓne
        rw [xi_eq_mul_completedRiemannZeta hs hs1, hΛ]
        simp

set_option maxHeartbeats 800000 in
theorem riemannZeta_zero_imp_critical_strip_or_trivial {s : ℂ} (hζ : riemannZeta s = 0) :
    0 < s.re ∨ ∃ n : ℕ, s = -2 * (n + 1) := by
  by_contra h
  push_neg at h
  have hsre : s.re ≤ 0 := h.1
  have hs1 : s ≠ 1 := by
    intro hs
    rw [hs] at hsre
    norm_num at hsre
  by_cases hint : ∃ n : ℕ, s = -n
  · rcases hint with ⟨n, rfl⟩
    by_cases hn : n = 0
    · subst n
      simp only [neg_zero, Nat.cast_zero] at hζ
      rw [riemannZeta_zero] at hζ
      norm_num at hζ
    · rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · have hm : 1 ≤ m := by
          by_contra hm'
          have : m = 0 := by omega
          subst m
          simp at hn
        exact h.2 (m - 1) (by
          rw [Nat.cast_sub hm]
          norm_num
          ring)
      · have hne : riemannZeta (-((2 * m + 1 : ℕ) : ℂ)) ≠ 0 := by
          let n' : ℕ := 2 * m + 1
          have hn'0 : (n' : ℂ) ≠ 0 := by exact_mod_cast (show n' ≠ 0 by omega)
          have hΓneg : (-(n' : ℂ)).Gammaℝ ≠ 0 := by
            rw [Complex.Gammaℝ_def]
            apply mul_ne_zero
            · rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero)]
              exact Complex.exp_ne_zero _
            · apply Complex.Gamma_ne_zero
              intro k hk
              have hre : (-(n' : ℂ) / 2).re = (-(k : ℂ)).re := congrArg Complex.re hk
              have h1 : (-(n' : ℂ) / 2).re = -(n' : ℝ) / 2 := by simp
              have h2 : (-(k : ℂ)).re = -(k : ℝ) := by simp
              rw [h1, h2] at hre
              have hrn : (n' : ℝ) = 2 * (k : ℝ) := by linarith
              have hn' : n' = 2 * k := by exact_mod_cast hrn
              dsimp [n'] at hn'
              omega
          have hζ1 : riemannZeta (1 + (n' : ℂ)) ≠ 0 :=
            riemannZeta_ne_zero_of_one_le_re (s := 1 + (n' : ℂ)) (by simp)
          have hΛ1 : completedRiemannZeta (1 + (n' : ℂ)) ≠ 0 := by
            intro hΛ
            have hdef := riemannZeta_def_of_ne_zero (s := 1 + (n' : ℂ))
              (by
                have h : 1 ≤ (1 + (n' : ℂ)).re := by simp
                intro h0
                rw [h0] at h
                norm_num at h)
            rw [hΛ] at hdef
            exact hζ1 (by simpa using hdef)
          have hΛneg : completedRiemannZeta (1 + (n' : ℂ)) = completedRiemannZeta (-(n' : ℂ)) := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              (completedRiemannZeta_one_sub (1 + (n' : ℂ))).symm
          intro hz
          have hdef := riemannZeta_def_of_ne_zero (s := -(n' : ℂ)) (neg_ne_zero.mpr hn'0)
          rw [hdef] at hz
          have hΛ0 : completedRiemannZeta (-(n' : ℂ)) = 0 :=
            (div_eq_zero_iff.mp hz).resolve_right hΓneg
          exact hΛ1 (by
            rw [hΛneg]
            exact hΛ0)
        exact hne hζ
  · push_neg at hint
    have hfe := riemannZeta_one_sub (s := s) hint hs1
    have hζ1s : riemannZeta (1 - s) = 0 := by
      rw [hfe, hζ]
      simp
    have hre1 : 1 ≤ (1 - s).re := by
      simp
      linarith
    exact (riemannZeta_ne_zero_of_one_le_re (s := 1 - s) hre1) hζ1s