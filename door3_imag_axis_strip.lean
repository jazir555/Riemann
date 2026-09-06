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
      xiShiftedEntire xiShiftedEntire_differentiable (R := 2) (by norm_num)
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
      _ = m₀ / 2 := by field_simp
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
        mul_le_mul_of_nonneg_left hz₂.1 hb,
        show a * (-ρ) + b * (-ρ) = -ρ by
          rw [← add_mul, hab, one_mul]]
    · linarith [mul_le_mul_of_nonneg_left hz₁.2.1 ha,
        mul_le_mul_of_nonneg_left hz₂.2.1 hb,
        show a * ρ + b * ρ = ρ by
          rw [← add_mul, hab, one_mul]]
    · linarith [mul_le_mul_of_nonneg_left hz₁.2.2.1 ha,
        mul_le_mul_of_nonneg_left hz₂.2.2.1 hb,
        show a * (-(1 / 2 : ℝ)) + b * (-(1 / 2 : ℝ)) = -(1 / 2 : ℝ) by
          rw [← add_mul, hab, one_mul]]
    · linarith [mul_le_mul_of_nonneg_left hz₁.2.2.2 ha,
        mul_le_mul_of_nonneg_left hz₂.2.2.2 hb,
        show a * (1 / 2 : ℝ) + b * (1 / 2 : ℝ) = (1 / 2 : ℝ) by
          rw [← add_mul, hab, one_mul]]
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
      calc
        ‖w‖ = ‖(w.re : ℂ) + Complex.I * (w.im : ℂ)‖ := congrArg norm hwrepr
        _ ≤
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
    have hzero : (0 : ℝ) ≤ ρ := hρ.le
    simpa [S, z₀] using (show -ρ ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ ρ ∧
      -(1 / 2 : ℝ) ≤ z.im ∧ z.im ≤ (1 / 2 : ℝ) from
      ⟨by linarith, hzero, hzlo, hzhi⟩)
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

theorem exists_imaginary_axis_local_rect :
    ∃ R : XiLocalZeroFreeRect,
      R.x0 < 0 ∧ 0 < R.x1 ∧ R.y0 = -(1 / 4 : ℝ) ∧
        R.y1 = (1 / 4 : ℝ) := by
  obtain ⟨ρ, m, hρ, hm, hstrip⟩ :=
    exists_imaginary_axis_horizontal_strip
  let R : XiLocalZeroFreeRect :=
    { x0 := -ρ / 2
      x1 := ρ / 2
      y0 := -(1 / 4 : ℝ)
      y1 := (1 / 4 : ℝ)
      x_lt := by linarith
      y_lt := by norm_num
      no_zero := by
        intro z hx0 hx1 hy0 hy1 hzero
        have hzre : |z.re| ≤ ρ := by
          rw [abs_le]
          constructor <;> linarith
        have hzlo : -(1 / 2 : ℝ) ≤ z.im := by linarith
        have hzhi : z.im ≤ (1 / 2 : ℝ) := by linarith
        have hlow : m ≤ ‖xiShiftedEntire z‖ := hstrip z hzre hzlo hzhi
        have hstrip_lo : -(1 / 2 : ℝ) < z.im := by linarith
        have hstrip_hi : z.im < (1 / 2 : ℝ) := by linarith
        have heq : xiShifted z = xiShiftedEntire z :=
          CentralCoverAssembly.xiShifted_eq_entire_on_strip z
            hstrip_lo hstrip_hi
        have hlow' : m ≤ ‖xiShifted z‖ := by simpa [heq] using hlow
        rw [hzero, norm_zero] at hlow'
        linarith }
  refine ⟨R, ?_, ?_, rfl, rfl⟩
  · dsimp [R]
    linarith
  · dsimp [R]
    linarith

theorem exists_small_central_zero_free_cover :
    ∃ X : ℝ, 0 < X ∧ Nonempty (XiCentralZeroFreeCover X) := by
  obtain ⟨ρ, m, hρ, hm, hstrip⟩ :=
    exists_imaginary_axis_horizontal_strip
  let X : ℝ := ρ / 2
  let R : XiLocalZeroFreeRect :=
    { x0 := -ρ
      x1 := ρ
      y0 := -(1 / 2 : ℝ)
      y1 := (1 / 2 : ℝ)
      x_lt := by linarith
      y_lt := by norm_num
      no_zero := by
        intro z hx0 hx1 hy0 hy1 hzero
        have hzre : |z.re| ≤ ρ := by
          rw [abs_le]
          exact ⟨by linarith, by linarith⟩
        have hzlo : -(1 / 2 : ℝ) ≤ z.im := by linarith
        have hzhi : z.im ≤ (1 / 2 : ℝ) := by linarith
        have hlow : m ≤ ‖xiShiftedEntire z‖ := hstrip z hzre hzlo hzhi
        have hstrip_lo : -(1 / 2 : ℝ) < z.im := by linarith
        have hstrip_hi : z.im < (1 / 2 : ℝ) := by linarith
        have heq : xiShifted z = xiShiftedEntire z :=
          CentralCoverAssembly.xiShifted_eq_entire_on_strip z
            hstrip_lo hstrip_hi
        have hlow' : m ≤ ‖xiShifted z‖ := by simpa [heq] using hlow
        rw [hzero, norm_zero] at hlow'
        linarith }
  refine ⟨X, by dsimp [X]; linarith, ?_⟩
  refine ⟨{ rects := [R], covers := ?_ }⟩
  intro z hXlo hXhi hzlo hzhi hzne
  refine ⟨R, by simp, ?_, ?_, ?_, ?_⟩
  · dsimp [R, X] at hXlo ⊢
    linarith
  · dsimp [R, X] at hXhi ⊢
    linarith
  · dsimp [R]
    linarith
  · dsimp [R]
    linarith

def combine_central_cover_with_annulus
    {X Y : ℝ} (C : XiCentralZeroFreeCover X)
    (ann : List XiLocalZeroFreeRect)
    (hann : ∀ z : ℂ,
      -Y ≤ z.re → z.re ≤ Y →
      -(1 : ℝ) / 2 < z.im → z.im < (1 : ℝ) / 2 → z.im ≠ 0 →
      (z.re < -X ∨ X < z.re) →
      ∃ R ∈ ann,
        R.x0 < z.re ∧ z.re < R.x1 ∧
        R.y0 < z.im ∧ z.im < R.y1) :
    XiCentralZeroFreeCover Y := by
  refine { rects := C.rects ++ ann, covers := ?_ }
  intro z hYlo hYhi hzlo hzhi hzne
  by_cases hleft : z.re < -X
  · obtain ⟨R, hR, hx0, hx1, hy0, hy1⟩ :=
      hann z hYlo hYhi hzlo hzhi hzne (Or.inl hleft)
    exact ⟨R, List.mem_append_right _ hR, hx0, hx1, hy0, hy1⟩
  by_cases hright : X < z.re
  · obtain ⟨R, hR, hx0, hx1, hy0, hy1⟩ :=
      hann z hYlo hYhi hzlo hzhi hzne (Or.inr hright)
    exact ⟨R, List.mem_append_right _ hR, hx0, hx1, hy0, hy1⟩
  · have hXlo : -X ≤ z.re := le_of_not_gt hleft
    have hXhi : z.re ≤ X := le_of_not_gt hright
    obtain ⟨R, hR, hx0, hx1, hy0, hy1⟩ :=
      C.covers z hXlo hXhi hzlo hzhi hzne
    exact ⟨R, List.mem_append_left _ hR, hx0, hx1, hy0, hy1⟩

/-! ## Explicit edge rectangles

The Cauchy data from `door3_top_edge.lean` is stronger than pointwise
nonvanishing: it supplies a positive lower bound on a closed rectangular
edge strip.  The next two constructors turn that bound into the local-rect
objects used by the central-cover assembler.  Keeping the conversion here
avoids repeating the totalized-entire-function bookkeeping in every finite
edge partition.
-/

theorem exists_top_edge_zero_free_rect {a b : ℝ} (hab : a < b) :
    ∃ R : XiLocalZeroFreeRect,
      R.x0 = a ∧ R.x1 = b ∧ R.y1 = (1 / 2 : ℝ) ∧
        R.y0 < R.y1 := by
  obtain ⟨δ, m, M, hδ, hδsmall, hm, hM, hdata, _⟩ :=
    Door3TopEdge.exists_two_edge_cauchy_data (le_of_lt hab)
  let R : XiLocalZeroFreeRect :=
    { x0 := a
      x1 := b
      y0 := (1 / 2 : ℝ) - δ
      y1 := (1 / 2 : ℝ)
      x_lt := hab
      y_lt := by linarith
      no_zero := by
        intro z hx0 hx1 hy0 hy1 hzero
        have hx : z.re ∈ Set.Icc a b := by
          exact ⟨by linarith [hx0], by linarith [hx1]⟩
        have hy : z.im ∈ Set.Icc ((1 / 2 : ℝ) - δ) (1 / 2 : ℝ) :=
          ⟨le_of_lt hy0, le_of_lt hy1⟩
        obtain ⟨hlow, _⟩ := hdata z.re hx z.im hy
        have hzform : z = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by
          apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
        have heq : xiShifted z = xiShiftedEntire z :=
          xiShifted_eq_entire_on_strip z (by linarith [hy.1, hδsmall])
            (by linarith [hy.2])
        rw [← hzform] at hlow
        have hlow' : m ≤ ‖xiShifted z‖ := by
          rw [heq]
          exact hlow
        rw [hzero, norm_zero] at hlow'
        linarith }
  refine ⟨R, rfl, rfl, rfl, ?_⟩
  dsimp [R]
  linarith

theorem exists_bottom_edge_zero_free_rect {a b : ℝ} (hab : a < b) :
    ∃ R : XiLocalZeroFreeRect,
      R.x0 = a ∧ R.x1 = b ∧ R.y0 = -(1 / 2 : ℝ) ∧
        R.y0 < R.y1 := by
  obtain ⟨δ, m, M, hδ, hδsmall, hm, hM, _, hdata⟩ :=
    Door3TopEdge.exists_two_edge_cauchy_data (le_of_lt hab)
  let R : XiLocalZeroFreeRect :=
    { x0 := a
      x1 := b
      y0 := -(1 / 2 : ℝ)
      y1 := -(1 / 2 : ℝ) + δ
      x_lt := hab
      y_lt := by linarith
      no_zero := by
        intro z hx0 hx1 hy0 hy1 hzero
        have hx : z.re ∈ Set.Icc a b := by
          exact ⟨by linarith [hx0], by linarith [hx1]⟩
        have hy : z.im ∈ Set.Icc (-(1 / 2 : ℝ)) (- (1 / 2 : ℝ) + δ) :=
          ⟨le_of_lt hy0, le_of_lt hy1⟩
        obtain ⟨hlow, _⟩ := hdata z.re hx z.im hy
        have hzform : z = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by
          apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
        have heq : xiShifted z = xiShiftedEntire z :=
          xiShifted_eq_entire_on_strip z (by linarith [hy.1])
            (by linarith [hy.2, hδsmall])
        rw [← hzform] at hlow
        have hlow' : m ≤ ‖xiShifted z‖ := by
          rw [heq]
          exact hlow
        rw [hzero, norm_zero] at hlow'
        linarith }
  refine ⟨R, rfl, rfl, rfl, ?_⟩
  dsimp [R]
  linarith

theorem exists_boundary_edge_rectangles :
    ∃ top bottom : XiLocalZeroFreeRect,
      top.x0 = -(10 : ℝ) ∧ top.x1 = 10 ∧ top.y1 = (1 / 2 : ℝ) ∧
      bottom.x0 = -(10 : ℝ) ∧ bottom.x1 = 10 ∧
        bottom.y0 = -(1 / 2 : ℝ) := by
  obtain ⟨top, htx0, htx1, hty1, _⟩ :=
    exists_top_edge_zero_free_rect (a := -(10 : ℝ)) (b := 10) (by norm_num)
  obtain ⟨bottom, hbx0, hbx1, hby0, _⟩ :=
    exists_bottom_edge_zero_free_rect (a := -(10 : ℝ)) (b := 10) (by norm_num)
  exact ⟨top, bottom, htx0, htx1, hty1, hbx0, hbx1, hby0⟩

#print axioms exists_imaginary_axis_horizontal_strip
#print axioms exists_imaginary_axis_local_rect
#print axioms exists_small_central_zero_free_cover
#print axioms exists_top_edge_zero_free_rect
#print axioms exists_bottom_edge_zero_free_rect
#print axioms exists_boundary_edge_rectangles

end Door3ImagAxis
