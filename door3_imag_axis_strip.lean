import door3_top_edge

open Complex Real Set Topology
open CentralCoverAssembly

noncomputable section

namespace Door3ImagAxis

/-- A qualitative two-dimensional zero-free neighborhood of the shifted
imaginary axis.  The width is obtained from the compact lower bound on the
axis and a Cauchy derivative bound on an outer ball. -/
theorem exists_imaginary_axis_horizontal_strip :
    ∃ ρ m : ℝ, 0 < ρ ∧ 0 < m ∧
      ∀ z : ℂ, |z.re| ≤ ρ →
        -(1 / 2 : ℝ) ≤ z.im → z.im ≤ (1 / 2 : ℝ) →
        m ≤ ‖xiShiftedEntire z‖ := by
  obtain ⟨m₀, hm₀, haxis⟩ :=
    Door3TopEdge.exists_imaginary_axis_compact_lower_bound
  obtain ⟨M, hM, hderiv⟩ :=
    Door3TopEdge.exists_deriv_bound_on_closedBall
      xiShiftedEntire xiShiftedEntire_differentiable (by norm_num)
  let ρ : ℝ := min (m₀ / (2 * M)) (1 / 4 : ℝ)
  have hMpos : 0 < M := hM
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (div_pos hm₀ (by positivity)) (by norm_num)
  have hρsmall : ρ ≤ (1 / 4 : ℝ) := min_le_right _ _
  have hρratio : M * ρ ≤ m₀ / 2 := by
    have hρle : ρ ≤ m₀ / (2 * M) := min_le_left _ _
    calc
      M * ρ ≤ M * (m₀ / (2 * M)) :=
        mul_le_mul_of_nonneg_left hρle hMpos.le
      _ = m₀ / 2 := by field_simp; ring
  let S : Set ℂ := {w : ℂ |
    -ρ ≤ w.re ∧ w.re ≤ ρ ∧
      -(1 / 2 : ℝ) ≤ w.im ∧ w.im ≤ (1 / 2 : ℝ)}
  have hSconv : Convex ℝ S := by
    intro z₁ hz₁ z₂ hz₂ a b ha hb hab
    simp only [S, Set.mem_setOf_eq] at hz₁ hz₂ ⊢
    have hre : (a • z₁ + b • z₂).re = a * z₁.re + b * z₂.re := by
      simp [Complex.add_re]
    have him : (a • z₁ + b • z₂).im = a * z₁.im + b * z₂.im := by
      simp [Complex.add_im]
    rw [hre, him]
    refine ⟨?_, ?_, ?_, ?_⟩
    · linarith [mul_le_mul_of_nonneg_left hz₁.1 ha,
        mul_le_mul_of_nonneg_left hz₂.1 hb]
    · linarith [mul_le_mul_of_nonneg_left hz₁.2.1 ha,
        mul_le_mul_of_nonneg_left hz₂.2.1 hb]
    · linarith [mul_le_mul_of_nonneg_left hz₁.2.2.1 ha,
        mul_le_mul_of_nonneg_left hz₂.2.2.1 hb]
    · linarith [mul_le_mul_of_nonneg_left hz₁.2.2.2 ha,
        mul_le_mul_of_nonneg_left hz₂.2.2.2 hb]
  have hSball : ∀ w ∈ S, w ∈ Metric.closedBall (0 : ℂ) 2 := by
    intro w hw
    simp only [S, Set.mem_setOf_eq] at hw
    have hwre : |w.re| ≤ ρ := by
      rw [abs_le]
      exact ⟨by linarith [hw.1], hw.2.1⟩
    have hwim : |w.im| ≤ (1 : ℝ) / 2 := by
      rw [abs_le]
      exact ⟨hw.2.2.1, hw.2.2.2⟩
    have hwrepr : w = (w.re : ℂ) + Complex.I * (w.im : ℂ) := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    have hnorm : ‖w‖ ≤ |w.re| + |w.im| := by
      rw [hwrepr]
      calc
        ‖(w.re : ℂ) + Complex.I * (w.im : ℂ)‖ ≤
            ‖(w.re : ℂ)‖ + ‖Complex.I * (w.im : ℂ)‖ := norm_add_le _ _
        _ = |w.re| + |w.im| := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I,
            one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [Metric.mem_closedBall]
    have hdist : dist w 0 = ‖w‖ := by simp [dist_eq_norm]
    rw [hdist]
    linarith
  have hderivS : ∀ w ∈ S, ‖deriv xiShiftedEntire w‖ ≤ M := by
    intro w hw
    exact hderiv w (hSball w hw)
  refine ⟨ρ, m₀ / 2, hρ, by linarith, ?_⟩
  intro z hzre hzlo hzhi
  have hzmem : z ∈ S := by
    simp only [S, Set.mem_setOf_eq]
    rw [abs_le] at hzre
    exact ⟨hzre.1, hzre.2, hzlo, hzhi⟩
  let z₀ : ℂ := Complex.I * (z.im : ℂ)
  have hz₀mem : z₀ ∈ S := by
    simp only [S, Set.mem_setOf_eq, z₀]
    have hzero : (0 : ℝ) ≤ ρ := hρ.le
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, add_zero]
    exact ⟨by linarith, by linarith, hzlo, hzhi⟩
  have hLip : ‖xiShiftedEntire z - xiShiftedEntire z₀‖ ≤
      M * ‖z - z₀‖ :=
    CellProofEngine.norm_image_sub_le_of_deriv_bound hSconv
      (fun w _ => xiShiftedEntire_differentiable w)
      hderivS hzmem hz₀mem
  have harg : z - z₀ = (z.re : ℂ) := by
    apply Complex.ext <;> simp [z₀, Complex.mul_re, Complex.mul_im]
  have hdist : ‖z - z₀‖ = |z.re| := by
    rw [harg, Complex.norm_real, Real.norm_eq_abs]
  have hLip' : ‖xiShiftedEntire z - xiShiftedEntire z₀‖ ≤ M * |z.re| := by
    simpa [hdist] using hLip
  have hbase : m₀ ≤ ‖xiShiftedEntire z₀‖ := by
    exact haxis z.im ⟨hzlo, hzhi⟩
  have hstep : M * |z.re| ≤ m₀ / 2 := by
    have hzre' : |z.re| ≤ ρ := hzre
    exact le_trans (mul_le_mul_of_nonneg_left hzre' hMpos.le) hρratio
  have hrev : ‖xiShiftedEntire z₀‖ -
      ‖xiShiftedEntire z - xiShiftedEntire z₀‖ ≤
      ‖xiShiftedEntire z‖ := by
    exact CellProofEngine.norm_ge_center_sub_diff
      (xiShiftedEntire z) (xiShiftedEntire z₀)
  linarith

#print axioms exists_imaginary_axis_horizontal_strip

end Door3ImagAxis
