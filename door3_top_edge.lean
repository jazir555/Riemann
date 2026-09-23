import central_cover_assembly
import door3_boundary_real
import door3_boundary_endpoints

open Complex Real Set Topology
noncomputable section

namespace Door3TopEdge

open CentralCoverAssembly

theorem xiShiftedEntire_eq_xiShifted_top {x : ℝ} (hx : x ≠ 0) :
    CentralCoverAssembly.xiShiftedEntire ((x : ℂ) + Complex.I / 2) =
      _root_.xiShifted ((x : ℂ) + Complex.I / 2) := by
  have hs : (1 / 2 : ℂ) + Complex.I * ((x : ℂ) + Complex.I / 2) =
      Complex.I * (x : ℂ) := by
    rw [mul_add]
    have hI : (Complex.I : ℂ) * (Complex.I / 2) = -(1 / 2 : ℂ) := by
      calc
        (Complex.I : ℂ) * (Complex.I / 2) =
            (Complex.I * Complex.I) / 2 := by ring
        _ = -(1 / 2 : ℂ) := by rw [Complex.I_mul_I]; ring
    rw [hI]
    ring
  have hs0 : Complex.I * (x : ℂ) ≠ 0 := by
    intro h
    have hi := congr_arg Complex.im h
    have hix : x = 0 := by simpa using hi
    exact hx hix
  have hs1 : Complex.I * (x : ℂ) ≠ 1 := by
    intro h
    have hr := congr_arg Complex.re h
    norm_num at hr
  have hgam : Complex.Gamma ((Complex.I * (x : ℂ)) / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have hi := congr_arg Complex.im hn
    have hix : x = 0 := by simpa using hi
    exact hx hix
  have hxi := classicalXi_eq_completed_add_half
      (Complex.I * (x : ℂ)) hs0 hs1 hgam
  unfold CentralCoverAssembly.xiShiftedEntire
  unfold _root_.xiShifted
  rw [hs]
  rw [hxi]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem xiShiftedEntire_ne_zero_top {x : ℝ} :
    CentralCoverAssembly.xiShiftedEntire ((x : ℂ) + Complex.I / 2) ≠ 0 := by
  by_cases hx : x = 0
  · subst x
    have harg : ((0 : ℂ) + Complex.I / 2) = Complex.I / 2 := by ring
    change CentralCoverAssembly.xiShiftedEntire ((0 : ℂ) + Complex.I / 2) ≠ 0
    rw [harg, Door3BoundaryEndpoints.xiShiftedEntire_at_pos_I_half]
    norm_num
  · rw [xiShiftedEntire_eq_xiShifted_top hx]
    exact xiShifted_ne_zero_on_top_edge_proved hx

theorem exists_top_edge_lower_bound {a b : ℝ} (hab : a ≤ b) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ Set.Icc a b,
        ε ≤ ‖CentralCoverAssembly.xiShiftedEntire ((x : ℂ) + Complex.I / 2)‖ := by
  let F : ℝ → ℝ := fun x =>
    ‖CentralCoverAssembly.xiShiftedEntire ((x : ℂ) + Complex.I / 2)‖
  have hcont : Continuous F := by
    have hE : Continuous CentralCoverAssembly.xiShiftedEntire :=
      CentralCoverAssembly.xiShiftedEntire_differentiable.continuous
    fun_prop
  have hmin := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab)
      hcont.continuousOn
  obtain ⟨x₀, hx₀, hxmin⟩ := hmin
  have hE₀ : CentralCoverAssembly.xiShiftedEntire ((x₀ : ℂ) + Complex.I / 2) ≠ 0 :=
    xiShiftedEntire_ne_zero_top
  refine ⟨F x₀, ?_, ?_⟩
  · exact norm_pos_iff.mpr hE₀
  · intro x hx
    exact (isMinOn_iff.mp hxmin) x hx

theorem xiShiftedEntire_eq_xiShifted_bottom {x : ℝ} (hx : x ≠ 0) :
    CentralCoverAssembly.xiShiftedEntire ((x : ℂ) - Complex.I / 2) =
      _root_.xiShifted ((x : ℂ) - Complex.I / 2) := by
  have hs : (1 / 2 : ℂ) + Complex.I * ((x : ℂ) - Complex.I / 2) =
      1 + Complex.I * (x : ℂ) := by
    rw [mul_sub]
    have hI : (Complex.I : ℂ) * (Complex.I / 2) = -(1 / 2 : ℂ) := by
      calc
        (Complex.I : ℂ) * (Complex.I / 2) =
            (Complex.I * Complex.I) / 2 := by ring
        _ = -(1 / 2 : ℂ) := by rw [Complex.I_mul_I]; ring
    rw [hI]
    ring
  have hs0 : (1 : ℂ) + Complex.I * (x : ℂ) ≠ 0 := by
    intro h
    have hr := congr_arg Complex.re h
    norm_num at hr
  have hs1 : (1 : ℂ) + Complex.I * (x : ℂ) ≠ 1 := by
    intro h
    have hi := congr_arg Complex.im h
    have hix : x = 0 := by simpa using hi
    exact hx hix
  have hgam : Complex.Gamma ((1 + Complex.I * (x : ℂ)) / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have hr := congr_arg Complex.re hn
    have hn0 : (0 : ℝ) ≤ n := by positivity
    norm_num at hr
    linarith
  have hxi := classicalXi_eq_completed_add_half
      (1 + Complex.I * (x : ℂ)) hs0 hs1 hgam
  unfold CentralCoverAssembly.xiShiftedEntire
  unfold _root_.xiShifted
  rw [hs]
  rw [hxi]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem xiShiftedEntire_ne_zero_bottom {x : ℝ} :
    CentralCoverAssembly.xiShiftedEntire ((x : ℂ) - Complex.I / 2) ≠ 0 := by
  by_cases hx : x = 0
  · subst x
    have harg : ((0 : ℂ) - Complex.I / 2) = -(Complex.I / 2) := by ring
    change CentralCoverAssembly.xiShiftedEntire ((0 : ℂ) - Complex.I / 2) ≠ 0
    rw [harg, Door3BoundaryEndpoints.xiShiftedEntire_at_neg_I_half]
    norm_num
  · rw [xiShiftedEntire_eq_xiShifted_bottom hx]
    unfold _root_.xiShifted
    intro hz
    have hs : (1 / 2 : ℂ) + Complex.I * ((x : ℂ) - Complex.I / 2) =
        1 + Complex.I * (x : ℂ) := by
      rw [mul_sub]
      have hI : (Complex.I : ℂ) * (Complex.I / 2) = -(1 / 2 : ℂ) := by
        calc
          (Complex.I : ℂ) * (Complex.I / 2) =
              (Complex.I * Complex.I) / 2 := by ring
          _ = -(1 / 2 : ℂ) := by rw [Complex.I_mul_I]; ring
      rw [hI]
      ring
    rw [hs] at hz
    have hs1 : (1 : ℂ) + Complex.I * (x : ℂ) ≠ 1 := by
      intro h
      have hi := congr_arg Complex.im h
      have hix : x = 0 := by simpa using hi
      exact hx hix
    have hs0 : (1 : ℂ) + Complex.I * (x : ℂ) ≠ 0 := by
      intro h
      have hr := congr_arg Complex.re h
      norm_num at hr
    have hzeta : zeta (1 + Complex.I * (x : ℂ)) ≠ 0 := by
      simpa [zeta] using (riemannZeta_ne_zero_of_one_le_re (s :=
        (1 : ℂ) + Complex.I * (x : ℂ)) (by norm_num))
    have hpref : classicalXiPrefactor (1 + Complex.I * (x : ℂ)) ≠ 0 := by
      unfold classicalXiPrefactor
      have hhalf : (1 / 2 : ℂ) ≠ 0 := by norm_num
      have hpi : (Real.pi : ℂ) ^ (-((1 + Complex.I * (x : ℂ)) / 2)) ≠ 0 :=
        pi_cpow_ne_zero _
      have hgamma : Complex.Gamma ((1 + Complex.I * (x : ℂ)) / 2) ≠ 0 := by
        apply Complex.Gamma_ne_zero
        intro n hn
        have hr := congr_arg Complex.re hn
        have hn0 : (0 : ℝ) ≤ n := by positivity
        norm_num at hr
        linarith
      have hsm1 : (1 + Complex.I * (x : ℂ)) - 1 ≠ 0 := sub_ne_zero.mpr hs1
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hhalf hs0) hsm1) hpi) hgamma
    exact hzeta ((mul_eq_zero.mp (by simpa [classicalXi, XiFromPrefactor] using hz)).resolve_left hpref)

theorem exists_bottom_edge_lower_bound {a b : ℝ} (hab : a ≤ b) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ Set.Icc a b,
        ε ≤ ‖CentralCoverAssembly.xiShiftedEntire ((x : ℂ) - Complex.I / 2)‖ := by
  let F : ℝ → ℝ := fun x =>
    ‖CentralCoverAssembly.xiShiftedEntire ((x : ℂ) - Complex.I / 2)‖
  have hcont : Continuous F := by
    have hE : Continuous CentralCoverAssembly.xiShiftedEntire :=
      CentralCoverAssembly.xiShiftedEntire_differentiable.continuous
    fun_prop
  have hmin := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab)
      hcont.continuousOn
  obtain ⟨x₀, hx₀, hxmin⟩ := hmin
  have hE₀ : CentralCoverAssembly.xiShiftedEntire ((x₀ : ℂ) - Complex.I / 2) ≠ 0 :=
    xiShiftedEntire_ne_zero_bottom
  refine ⟨F x₀, ?_, ?_⟩
  · exact norm_pos_iff.mpr hE₀
  · intro x hx
    exact (isMinOn_iff.mp hxmin) x hx

/-! A qualitative (non-quantitative) consequence of the edge certificate:
every fixed top-edge point has an open vertical zero-free neighbourhood.  The
proof obtains a Cauchy bound from continuity on one compact closed ball and
then applies the outer-bound fencing theorem. -/
theorem exists_top_edge_local_strip (x : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℝ, (1 / 2 : ℝ) - δ < y → y < (1 / 2 : ℝ) →
        _root_.xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
  let ztop : ℂ := (x : ℂ) + Complex.I / 2
  have htop : CentralCoverAssembly.xiShiftedEntire ztop ≠ 0 := by
    dsimp [ztop]
    exact xiShiftedEntire_ne_zero_top
  let e0 : ℝ := ‖CentralCoverAssembly.xiShiftedEntire ztop‖
  have he0 : 0 < e0 := by
    dsimp [e0]
    exact norm_pos_iff.mpr htop
  have hcont : Continuous CentralCoverAssembly.xiShiftedEntire :=
    CentralCoverAssembly.xiShiftedEntire_differentiable.continuous
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall ztop (2 : ℝ)).exists_bound_of_continuousOn
      (hcont.continuousOn)
  let M : ℝ := max C 1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  let e : ℝ := min e0 M
  have he : 0 < e := lt_min he0 hM
  let δ : ℝ := e / M
  have hδ : 0 < δ := div_pos he hM
  refine ⟨δ, hδ, ?_⟩
  intro y hy_low hy_top
  have hδle : δ ≤ 1 := by
    dsimp [δ]
    have heM : e ≤ M := min_le_right _ _
    apply (div_le_iff₀ hM).2
    simpa using heM
  have hmargin : (1 / 2 : ℝ) - y < δ := by
    linarith
  have hderiv : ∀ v ∈ Set.Icc ((1 / 2 : ℝ) - δ) (1 / 2 : ℝ),
      ‖deriv CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) + Complex.I * (v : ℂ))‖ ≤ M := by
    intro v hv
    let w : ℂ := (x : ℂ) + Complex.I * (v : ℂ)
    have hwtop : dist w ztop = (1 / 2 : ℝ) - v := by
      have heq : w - ztop = Complex.I * (((v - (1 / 2 : ℝ)) : ℝ) : ℂ) := by
        dsimp [w, ztop]
        push_cast
        ring
      rw [dist_eq_norm, heq, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr hv.2)]
      ring
    have hsphere : ∀ z ∈ Metric.sphere w (1 : ℝ),
        z ∈ Metric.closedBall ztop (2 : ℝ) := by
      intro z hz
      have hzw : dist z w = (1 : ℝ) := Metric.mem_sphere.mp hz
      have htri : dist z ztop ≤ dist z w + dist w ztop := dist_triangle _ _ _
      rw [hzw, hwtop] at htri
      rw [Metric.mem_closedBall]
      have hv_lower : -(1 / 2 : ℝ) ≤ v := by
        linarith [hv.1, hδle]
      linarith
    have hDC : DiffContOnCl ℂ CentralCoverAssembly.xiShiftedEntire
        (Metric.ball w (1 : ℝ)) :=
      CentralCoverAssembly.xiShiftedEntire_differentiable.diffContOnCl
    have hsphere_bound : ∀ z ∈ Metric.sphere w (1 : ℝ),
        ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C := by
      intro z hz
      exact hC z (hsphere z hz)
    have hbound : ‖deriv CentralCoverAssembly.xiShiftedEntire w‖ ≤ C / 1 :=
      Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num) hDC hsphere_bound
    have hCM : C ≤ M := le_max_left _ _
    have hboundM : ‖deriv CentralCoverAssembly.xiShiftedEntire w‖ ≤ M := by
      calc
        ‖deriv CentralCoverAssembly.xiShiftedEntire w‖ ≤ C / 1 := hbound
        _ = C := by ring
        _ ≤ M := hCM
    simpa [w] using hboundM
  have htopbound : e ≤ ‖CentralCoverAssembly.xiShiftedEntire ztop‖ := by
    change e ≤ e0
    exact min_le_left _ _
  have htopbound' : e ≤ ‖CentralCoverAssembly.xiShiftedEntire
      ((x : ℂ) + Complex.I * (1 / 2 : ℂ))‖ := by
    have harg : ((x : ℂ) + Complex.I * (1 / 2 : ℂ)) = ztop := by
      dsimp [ztop]
      ring
    rw [harg]
    exact htopbound
  have hne_ent : CentralCoverAssembly.xiShiftedEntire
      ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
    have hres := BoundaryProofEngine.upper_boundary_nonvanishing_from_outer_bound
      CentralCoverAssembly.xiShiftedEntire
      CentralCoverAssembly.xiShiftedEntire_differentiable x e M he hM htopbound'
      hderiv y (by simpa [δ] using hy_low) (le_of_lt hy_top)
    simpa [ztop] using hres
  have hstrip_lo : -(1 / 2 : ℝ) < y := by
    linarith [hy_low, hδle]
  have him : ((x : ℂ) + Complex.I * (y : ℂ)).im = y := by
    simp
  have hagree : _root_.xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) =
      CentralCoverAssembly.xiShiftedEntire ((x : ℂ) + Complex.I * (y : ℂ)) :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip _ (by simpa [him] using hstrip_lo)
      (by simpa [him] using hy_top)
  rw [hagree]
  exact hne_ent

theorem exists_top_edge_uniform_strip {a b : ℝ} (hab : a ≤ b) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ Set.Icc a b, ∀ y : ℝ,
        (1 / 2 : ℝ) - δ < y → y < (1 / 2 : ℝ) →
          _root_.xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
  obtain ⟨e0, he0, htop⟩ := exists_top_edge_lower_bound hab
  let R : ℝ := max |a| |b| + 3
  have hR : 0 < R := by
    dsimp [R]
    have : 0 ≤ max |a| |b| :=
      le_trans (abs_nonneg a) (le_max_left _ _)
    linarith
  have hcont : Continuous CentralCoverAssembly.xiShiftedEntire :=
    CentralCoverAssembly.xiShiftedEntire_differentiable.continuous
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
      hcont.continuousOn
  let M : ℝ := max C 1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  let e : ℝ := min e0 M
  have he : 0 < e := lt_min he0 hM
  let δ : ℝ := e / M
  have hδ : 0 < δ := div_pos he hM
  have hδle : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_iff₀ hM).2
    have heM : e ≤ M := by
      dsimp [e]
      exact min_le_right _ _
    simpa using heM
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy_low hy_top
  have hderiv : ∀ v ∈ Set.Icc ((1 / 2 : ℝ) - δ) (1 / 2 : ℝ),
      ‖deriv CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) + Complex.I * (v : ℂ))‖ ≤ M := by
    intro v hv
    let w : ℂ := (x : ℂ) + Complex.I * (v : ℂ)
    have hxabs : |x| ≤ max |a| |b| :=
      abs_le_max_abs_abs (Set.mem_Icc.mp hx).1 (Set.mem_Icc.mp hx).2
    have hvabs : |v| ≤ 1 := by
      rw [abs_le]
      constructor
      · linarith [hv.1, hδle]
      · linarith [hv.2]
    have hw_norm : ‖w‖ ≤ max |a| |b| + 1 := by
      dsimp [w]
      calc
        ‖(x : ℂ) + Complex.I * (v : ℂ)‖ ≤
            ‖(x : ℂ)‖ + ‖Complex.I * (v : ℂ)‖ := norm_add_le _ _
        _ = |x| + |v| := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I,
            one_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ max |a| |b| + 1 := by linarith
    have hsphere : ∀ z ∈ Metric.sphere w (1 : ℝ),
        z ∈ Metric.closedBall (0 : ℂ) R := by
      intro z hz
      have hzw : dist z w = (1 : ℝ) := Metric.mem_sphere.mp hz
      have htri : dist z 0 ≤ dist z w + dist w 0 := dist_triangle _ _ _
      have hw0 : dist w 0 = ‖w‖ := by simp [dist_eq_norm]
      rw [hzw, hw0] at htri
      rw [Metric.mem_closedBall]
      dsimp [R]
      linarith
    have hDC : DiffContOnCl ℂ CentralCoverAssembly.xiShiftedEntire
        (Metric.ball w (1 : ℝ)) :=
      CentralCoverAssembly.xiShiftedEntire_differentiable.diffContOnCl
    have hsphere_bound : ∀ z ∈ Metric.sphere w (1 : ℝ),
        ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C := by
      intro z hz
      exact hC z (hsphere z hz)
    have hbound : ‖deriv CentralCoverAssembly.xiShiftedEntire w‖ ≤ C / 1 :=
      Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num) hDC hsphere_bound
    have hCM : C ≤ M := le_max_left _ _
    have hboundM : ‖deriv CentralCoverAssembly.xiShiftedEntire w‖ ≤ M := by
      calc
        ‖deriv CentralCoverAssembly.xiShiftedEntire w‖ ≤ C / 1 := hbound
        _ = C := by ring
        _ ≤ M := hCM
    simpa [w] using hboundM
  have htopbound : e ≤ ‖CentralCoverAssembly.xiShiftedEntire
      ((x : ℂ) + Complex.I * (1 / 2 : ℂ))‖ := by
    have hx0 := htop x hx
    have harg : ((x : ℂ) + Complex.I * (1 / 2 : ℂ)) =
        ((x : ℂ) + Complex.I / 2) := by ring
    rw [harg]
    exact le_trans (min_le_left _ _) hx0
  have hne_ent : CentralCoverAssembly.xiShiftedEntire
      ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
    have hres := BoundaryProofEngine.upper_boundary_nonvanishing_from_outer_bound
      CentralCoverAssembly.xiShiftedEntire
      CentralCoverAssembly.xiShiftedEntire_differentiable x e M he hM htopbound
      hderiv y (by simpa [δ] using hy_low) (le_of_lt hy_top)
    simpa using hres
  have hstrip_lo : -(1 / 2 : ℝ) < y := by
    linarith [hy_low, hδle]
  have him : ((x : ℂ) + Complex.I * (y : ℂ)).im = y := by simp
  have hagree : _root_.xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) =
      CentralCoverAssembly.xiShiftedEntire ((x : ℂ) + Complex.I * (y : ℂ)) :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip _ (by simpa [him] using hstrip_lo)
      (by simpa [him] using hy_top)
  rw [hagree]
  exact hne_ent

theorem lower_boundary_nonvanishing_from_outer_bound
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ)
    (ε_top M1 : ℝ) (hε : 0 < ε_top) (hM1 : 0 < M1)
    (h_bottom : ε_top ≤ ‖f ((x : ℂ) - Complex.I * (1 / 2 : ℂ))‖)
    (h_deriv : ∀ y ∈ Set.Icc (-(1 / 2 : ℝ))
        (-(1 / 2 : ℝ) + ε_top / M1),
        ‖deriv f ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ M1)
    (y : ℝ) (hy_bottom : -(1 / 2 : ℝ) < y)
    (hy_low : y < -(1 / 2 : ℝ) + ε_top / M1) :
    f ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
  let g : ℂ → ℂ := fun z => f (z - Complex.I / 2)
  have hg : Differentiable ℂ g := by
    unfold g
    exact hf.comp (by fun_prop)
  have hη : 0 < ε_top / M1 := div_pos hε hM1
  have hbase : ε_top ≤ ‖g (x : ℂ)‖ := by
    dsimp [g]
    simpa [sub_eq_add_neg, div_eq_mul_inv] using h_bottom
  have hderiv_g : ∀ t ∈ Set.Icc (0 : ℝ) (ε_top / M1),
      ‖deriv g ((x : ℂ) + Complex.I * (t : ℂ))‖ ≤ M1 := by
    intro t ht
    have hv : -(1 / 2 : ℝ) ≤ t - 1 / 2 ∧
        t - 1 / 2 ≤ -(1 / 2 : ℝ) + ε_top / M1 := by
      constructor <;> linarith [ht.1, ht.2]
    have hpoint : ((x : ℂ) + Complex.I * (t : ℂ)) - Complex.I / 2 =
        (x : ℂ) + Complex.I * ((t - 1 / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    have hcomp : deriv g ((x : ℂ) + Complex.I * (t : ℂ)) =
        deriv f ((x : ℂ) + Complex.I * ((t - 1 / 2 : ℝ) : ℂ)) := by
      have hout := (hf (((x : ℂ) + Complex.I * (t : ℂ)) - Complex.I / 2)).hasDerivAt
      have hin := (hasDerivAt_id ((x : ℂ) + Complex.I * (t : ℂ))).sub_const
        (Complex.I / 2)
      have hc := hout.comp (x := ((x : ℂ) + Complex.I * (t : ℂ))) hin
      simpa [g, Function.comp_def, hpoint] using hc.deriv
    rw [hcomp]
    exact h_deriv (t - 1 / 2) ⟨hv.1, hv.2⟩
  have hres := BoundaryProofEngine.boundary_strip_nonvanishing_of_nonzero_base
    g hg x ε_top M1 (ε_top / M1) hε hM1 hη hbase hderiv_g
    (y + 1 / 2) (by linarith) (by linarith) (by linarith)
  have harg : ((x : ℂ) + Complex.I * ((y + 1 / 2 : ℝ) : ℂ)) - Complex.I / 2 =
      (x : ℂ) + Complex.I * (y : ℂ) := by
    push_cast
    ring
  change f (((x : ℂ) + Complex.I * ((y + 1 / 2 : ℝ) : ℂ)) - Complex.I / 2) ≠ 0 at hres
  rw [harg] at hres
  exact hres

theorem exists_bottom_edge_uniform_strip {a b : ℝ} (hab : a ≤ b) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ Set.Icc a b, ∀ y : ℝ,
        -(1 / 2 : ℝ) < y → y < -(1 / 2 : ℝ) + δ →
          _root_.xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
  obtain ⟨e0, he0, hbottom⟩ := exists_bottom_edge_lower_bound hab
  let R : ℝ := max |a| |b| + 3
  have hR : 0 < R := by
    dsimp [R]
    have hnonneg : 0 ≤ max |a| |b| :=
      le_trans (abs_nonneg a) (le_max_left _ _)
    linarith
  have hcont : Continuous CentralCoverAssembly.xiShiftedEntire :=
    CentralCoverAssembly.xiShiftedEntire_differentiable.continuous
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
      hcont.continuousOn
  let M : ℝ := max C 1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  let e : ℝ := min e0 M
  have he : 0 < e := lt_min he0 hM
  let δ : ℝ := e / M
  have hδ : 0 < δ := div_pos he hM
  have hδle : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_iff₀ hM).2
    have heM : e ≤ M := by
      dsimp [e]
      exact min_le_right _ _
    simpa using heM
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy_bottom hy_high
  have hderiv : ∀ v ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + δ),
      ‖deriv CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) + Complex.I * (v : ℂ))‖ ≤ M := by
    intro v hv
    let w : ℂ := (x : ℂ) + Complex.I * (v : ℂ)
    have hxabs : |x| ≤ max |a| |b| :=
      abs_le_max_abs_abs (Set.mem_Icc.mp hx).1 (Set.mem_Icc.mp hx).2
    have hvabs : |v| ≤ 1 := by
      rw [abs_le]
      constructor
      · linarith [hv.1]
      · linarith [hv.2, hδle]
    have hw_norm : ‖w‖ ≤ max |a| |b| + 1 := by
      dsimp [w]
      calc
        ‖(x : ℂ) + Complex.I * (v : ℂ)‖ ≤
            ‖(x : ℂ)‖ + ‖Complex.I * (v : ℂ)‖ := norm_add_le _ _
        _ = |x| + |v| := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I,
            one_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ max |a| |b| + 1 := by linarith
    have hsphere : ∀ z ∈ Metric.sphere w (1 : ℝ),
        z ∈ Metric.closedBall (0 : ℂ) R := by
      intro z hz
      have hzw : dist z w = (1 : ℝ) := Metric.mem_sphere.mp hz
      have htri : dist z 0 ≤ dist z w + dist w 0 := dist_triangle _ _ _
      have hw0 : dist w 0 = ‖w‖ := by simp [dist_eq_norm]
      rw [hzw, hw0] at htri
      rw [Metric.mem_closedBall]
      dsimp [R]
      linarith
    have hDC : DiffContOnCl ℂ CentralCoverAssembly.xiShiftedEntire
        (Metric.ball w (1 : ℝ)) :=
      CentralCoverAssembly.xiShiftedEntire_differentiable.diffContOnCl
    have hsphere_bound : ∀ z ∈ Metric.sphere w (1 : ℝ),
        ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C := by
      intro z hz
      exact hC z (hsphere z hz)
    have hbound : ‖deriv CentralCoverAssembly.xiShiftedEntire w‖ ≤ C / 1 :=
      Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num) hDC hsphere_bound
    have hCM : C ≤ M := le_max_left _ _
    have hboundM : ‖deriv CentralCoverAssembly.xiShiftedEntire w‖ ≤ M := by
      calc
        ‖deriv CentralCoverAssembly.xiShiftedEntire w‖ ≤ C / 1 := hbound
        _ = C := by ring
        _ ≤ M := hCM
    simpa [w] using hboundM
  have hbottombound : e ≤ ‖CentralCoverAssembly.xiShiftedEntire
      ((x : ℂ) - Complex.I * (1 / 2 : ℂ))‖ := by
    have hx0 := hbottom x hx
    have harg : ((x : ℂ) - Complex.I * (1 / 2 : ℂ)) =
        ((x : ℂ) - Complex.I / 2) := by ring
    rw [harg]
    exact le_trans (min_le_left _ _) hx0
  have hne_ent : CentralCoverAssembly.xiShiftedEntire
      ((x : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
    have hres := lower_boundary_nonvanishing_from_outer_bound
      CentralCoverAssembly.xiShiftedEntire
      CentralCoverAssembly.xiShiftedEntire_differentiable x e M he hM hbottombound
      hderiv y hy_bottom (by simpa [δ] using hy_high)
    simpa using hres
  have him : ((x : ℂ) + Complex.I * (y : ℂ)).im = y := by simp
  have hagree : _root_.xiShifted ((x : ℂ) + Complex.I * (y : ℂ)) =
      CentralCoverAssembly.xiShiftedEntire ((x : ℂ) + Complex.I * (y : ℂ)) :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip _ (by simpa [him] using hy_bottom)
      (by simpa [him] using (by linarith [hy_high, hδle] : y < (1 / 2 : ℝ)))
  rw [hagree]
  exact hne_ent

theorem exists_top_edge_compact_lower_bound {a b : ℝ} (hab : a ≤ b) :
    ∃ δ m : ℝ, 0 < δ ∧ 0 < m ∧
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc ((1 / 2 : ℝ) - δ) (1 / 2 : ℝ),
        m ≤ ‖CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) + Complex.I * (y : ℂ))‖ := by
  obtain ⟨δ₀, hδ₀, hstrip⟩ := exists_top_edge_uniform_strip hab
  let δ : ℝ := min (δ₀ / 2) (1 / 4 : ℝ)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith) (by norm_num)
  let s : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc ((1 / 2 : ℝ) - δ) (1 / 2 : ℝ)
  have hscomp : IsCompact s := (isCompact_Icc.prod isCompact_Icc)
  have hsne : s.Nonempty := by
    refine ⟨(a, (1 / 2 : ℝ) - δ), ?_⟩
    exact ⟨⟨le_rfl, hab⟩, ⟨le_rfl, by linarith⟩⟩
  let F : ℝ × ℝ → ℝ := fun p =>
    ‖CentralCoverAssembly.xiShiftedEntire
      ((p.1 : ℂ) + Complex.I * (p.2 : ℂ))‖
  have hcont_ent : Continuous CentralCoverAssembly.xiShiftedEntire :=
    CentralCoverAssembly.xiShiftedEntire_differentiable.continuous
  have hF : Continuous F := by
    have hmap : Continuous (fun p : ℝ × ℝ =>
        ((p.1 : ℂ) + Complex.I * (p.2 : ℂ))) := by fun_prop
    dsimp [F]
    exact (hcont_ent.comp hmap).norm
  have hFpos : ∀ p ∈ s, 0 < F p := by
    intro p hp
    have hxp : p.1 ∈ Set.Icc a b := hp.1
    have hyp : p.2 ∈ Set.Icc ((1 / 2 : ℝ) - δ) (1 / 2 : ℝ) := hp.2
    have hygt : (1 / 2 : ℝ) - δ₀ < p.2 := by
      dsimp [δ] at hyp ⊢
      have hle : min (δ₀ / 2) (1 / 4 : ℝ) ≤ δ₀ / 2 := min_le_left _ _
      linarith [hyp.1, hδ₀, hle]
    have hygt_im : -(1 / 2 : ℝ) < p.2 := by
      dsimp [δ] at hyp
      have hle : min (δ₀ / 2) (1 / 4 : ℝ) ≤ (1 / 4 : ℝ) := min_le_right _ _
      linarith [hyp.1, hle]
    by_cases htop : p.2 = (1 / 2 : ℝ)
    · have hne := xiShiftedEntire_ne_zero_top (x := p.1)
      have hnepoint : CentralCoverAssembly.xiShiftedEntire
          ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ≠ 0 := by
        rw [htop]
        convert hne using 1 <;> norm_num <;> ring
      exact norm_pos_iff.mpr hnepoint
    · have hylt : p.2 < (1 / 2 : ℝ) := lt_of_le_of_ne hyp.2 htop
      have hne := hstrip p.1 hxp p.2 hygt hylt
      have him : ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)).im = p.2 := by simp
      have hagree : _root_.xiShifted ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) =
          CentralCoverAssembly.xiShiftedEntire ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) :=
        CentralCoverAssembly.xiShifted_eq_entire_on_strip _
          (by rw [him]; exact hygt_im)
          (by rw [him]; exact hylt)
      have hne_ent : CentralCoverAssembly.xiShiftedEntire
          ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ≠ 0 := by
        rw [← hagree]
        exact hne
      exact norm_pos_iff.mpr hne_ent
  obtain ⟨m, hm, hmlow⟩ := hscomp.exists_forall_le' hF.continuousOn hFpos
  refine ⟨δ, m, hδ, hm, ?_⟩
  intro x hx y hy
  exact hmlow (x, y) ⟨hx, hy⟩

theorem exists_bottom_edge_compact_lower_bound {a b : ℝ} (hab : a ≤ b) :
    ∃ δ m : ℝ, 0 < δ ∧ 0 < m ∧
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc (-(1 / 2 : ℝ)) (- (1 / 2 : ℝ) + δ),
        m ≤ ‖CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) + Complex.I * (y : ℂ))‖ := by
  obtain ⟨δ₀, hδ₀, hstrip⟩ := exists_bottom_edge_uniform_strip hab
  let δ : ℝ := min (δ₀ / 2) (1 / 4 : ℝ)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith) (by norm_num)
  let s : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc (-(1 / 2 : ℝ)) (- (1 / 2 : ℝ) + δ)
  have hscomp : IsCompact s := (isCompact_Icc.prod isCompact_Icc)
  have hsne : s.Nonempty := by
    refine ⟨(a, -(1 / 2 : ℝ)), ?_⟩
    exact ⟨⟨le_rfl, hab⟩, ⟨le_rfl, by linarith⟩⟩
  let F : ℝ × ℝ → ℝ := fun p =>
    ‖CentralCoverAssembly.xiShiftedEntire
      ((p.1 : ℂ) + Complex.I * (p.2 : ℂ))‖
  have hcont_ent : Continuous CentralCoverAssembly.xiShiftedEntire :=
    CentralCoverAssembly.xiShiftedEntire_differentiable.continuous
  have hF : Continuous F := by
    have hmap : Continuous (fun p : ℝ × ℝ =>
        ((p.1 : ℂ) + Complex.I * (p.2 : ℂ))) := by fun_prop
    dsimp [F]
    exact (hcont_ent.comp hmap).norm
  have hFpos : ∀ p ∈ s, 0 < F p := by
    intro p hp
    have hxp : p.1 ∈ Set.Icc a b := hp.1
    have hyp : p.2 ∈ Set.Icc (-(1 / 2 : ℝ)) (- (1 / 2 : ℝ) + δ) := hp.2
    by_cases heq : p.2 = -(1 / 2 : ℝ)
    · have hne := xiShiftedEntire_ne_zero_bottom (x := p.1)
      have hnepoint : CentralCoverAssembly.xiShiftedEntire
          ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ≠ 0 := by
        rw [heq]
        convert hne using 1 <;> norm_num <;> ring
      exact norm_pos_iff.mpr hnepoint
    · have hygt : -(1 / 2 : ℝ) < p.2 := lt_of_le_of_ne hyp.1 (Ne.symm heq)
      have hylt : p.2 < -(1 / 2 : ℝ) + δ₀ := by
        dsimp [δ] at hyp ⊢
        have hle : min (δ₀ / 2) (1 / 4 : ℝ) ≤ δ₀ / 2 := min_le_left _ _
        linarith [hyp.2, hδ₀, hle]
      have hne := hstrip p.1 hxp p.2 hygt hylt
      have him : ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)).im = p.2 := by simp
      have hagree : _root_.xiShifted ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) =
          CentralCoverAssembly.xiShiftedEntire ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) :=
        CentralCoverAssembly.xiShifted_eq_entire_on_strip _
          (by rw [him]; exact hygt)
          (by rw [him]; have hle : min (δ₀ / 2) (1 / 4 : ℝ) ≤ (1 / 4 : ℝ) := min_le_right _ _; dsimp [δ] at hyp; linarith [hyp.2, hle])
      have hne_ent : CentralCoverAssembly.xiShiftedEntire
          ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ≠ 0 := by
        rw [← hagree]
        exact hne
      exact norm_pos_iff.mpr hne_ent
  obtain ⟨m, hm, hmlow⟩ := hscomp.exists_forall_le' hF.continuousOn hFpos
  refine ⟨δ, m, hδ, hm, ?_⟩
  intro x hx y hy
  exact hmlow (x, y) ⟨hx, hy⟩

theorem exists_deriv_bound_on_closedBall
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) {R : ℝ} (hR : 0 < R) :
    ∃ M : ℝ, 0 < M ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖deriv f z‖ ≤ M := by
  let R' : ℝ := R + 1
  have hR' : 0 < R' := by dsimp [R']; linarith
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : ℂ) R').exists_bound_of_continuousOn
      hf.continuous.continuousOn
  let M : ℝ := max C 1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨M, hM, ?_⟩
  intro z hz
  let w : ℂ := z
  have hz0 : dist z 0 ≤ R := by
    exact Metric.mem_closedBall.mp hz
  have hsphere : ∀ u ∈ Metric.sphere w (1 : ℝ),
      u ∈ Metric.closedBall (0 : ℂ) R' := by
    intro u hu
    have huz : dist u z = (1 : ℝ) := by
      simpa [w] using (Metric.mem_sphere.mp hu)
    have htri : dist u 0 ≤ dist u z + dist z 0 := dist_triangle _ _ _
    rw [huz] at htri
    rw [Metric.mem_closedBall]
    dsimp [R']
    linarith
  have hDC : DiffContOnCl ℂ f (Metric.ball w (1 : ℝ)) :=
    hf.diffContOnCl
  have hsphere_bound : ∀ u ∈ Metric.sphere w (1 : ℝ), ‖f u‖ ≤ C := by
    intro u hu
    exact hC u (hsphere u hu)
  have hbound : ‖deriv f w‖ ≤ C / 1 :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num) hDC
      hsphere_bound
  have hCM : C ≤ M := le_max_left _ _
  calc
    ‖deriv f z‖ = ‖deriv f w‖ := by rfl
    _ ≤ C / 1 := hbound
    _ = C := by ring
    _ ≤ M := hCM

theorem exists_top_edge_cauchy_data {a b : ℝ} (hab : a ≤ b) :
    ∃ δ m M : ℝ, 0 < δ ∧ 0 < m ∧ 0 < M ∧
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc ((1 / 2 : ℝ) - δ) (1 / 2 : ℝ),
        m ≤ ‖CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) + Complex.I * (y : ℂ))‖ ∧
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ M := by
  obtain ⟨δ₀, m₀, hδ₀, hm₀, hbound₀⟩ := exists_top_edge_compact_lower_bound hab
  let δ : ℝ := min δ₀ (1 / 4 : ℝ)
  have hδ : 0 < δ := lt_min hδ₀ (by norm_num)
  let R : ℝ := max |a| |b| + 2
  have hR : 0 < R := by
    dsimp [R]
    have hnonneg : 0 ≤ max |a| |b| :=
      le_trans (abs_nonneg a) (le_max_left _ _)
    linarith
  obtain ⟨M, hM, hderiv⟩ :=
    exists_deriv_bound_on_closedBall CentralCoverAssembly.xiShiftedEntire
      CentralCoverAssembly.xiShiftedEntire_differentiable hR
  refine ⟨δ, m₀, M, hδ, hm₀, hM, ?_⟩
  intro x hx y hy
  have hδle : δ ≤ (1 / 4 : ℝ) := min_le_right _ _
  have hδle0 : δ ≤ δ₀ := min_le_left _ _
  have hylow : (1 / 4 : ℝ) ≤ y := by linarith [hy.1, hδle]
  have hyhigh : y ≤ (1 / 2 : ℝ) := hy.2
  have hyabs : |y| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hxabs : |x| ≤ max |a| |b| :=
    abs_le_max_abs_abs hx.1 hx.2
  let w : ℂ := (x : ℂ) + Complex.I * (y : ℂ)
  have hwball : w ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall]
    have hw_norm : ‖w‖ ≤ max |a| |b| + 1 := by
      dsimp [w]
      calc
        ‖(x : ℂ) + Complex.I * (y : ℂ)‖ ≤
            ‖(x : ℂ)‖ + ‖Complex.I * (y : ℂ)‖ := norm_add_le _ _
        _ = |x| + |y| := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I,
            one_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ max |a| |b| + 1 := by linarith
    have hdist : dist w 0 = ‖w‖ := by simp [dist_eq_norm]
    rw [hdist]
    dsimp [R]
    linarith
  have hlow : m₀ ≤ ‖CentralCoverAssembly.xiShiftedEntire w‖ := by
    have hy₀ : y ∈ Set.Icc ((1 / 2 : ℝ) - δ₀) (1 / 2 : ℝ) := by
      constructor
      · dsimp [δ] at hy ⊢
        exact le_trans (sub_le_sub_left (min_le_left _ _) _) hy.1
      · exact hy.2
    exact hbound₀ x hx y hy₀
  have hD : ‖deriv CentralCoverAssembly.xiShiftedEntire w‖ ≤ M :=
    hderiv w hwball
  exact ⟨by simpa [w] using hlow, by simpa [w] using hD⟩

theorem exists_bottom_edge_cauchy_data {a b : ℝ} (hab : a ≤ b) :
    ∃ δ m M : ℝ, 0 < δ ∧ 0 < m ∧ 0 < M ∧
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc (-(1 / 2 : ℝ)) (- (1 / 2 : ℝ) + δ),
        m ≤ ‖CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) + Complex.I * (y : ℂ))‖ ∧
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ M := by
  obtain ⟨δ₀, m₀, hδ₀, hm₀, hbound₀⟩ := exists_bottom_edge_compact_lower_bound hab
  let δ : ℝ := min (δ₀ / 2) (1 / 4 : ℝ)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith) (by norm_num)
  let R : ℝ := max |a| |b| + 2
  have hR : 0 < R := by
    dsimp [R]
    have hnonneg : 0 ≤ max |a| |b| :=
      le_trans (abs_nonneg a) (le_max_left _ _)
    linarith
  obtain ⟨M, hM, hderiv⟩ :=
    exists_deriv_bound_on_closedBall CentralCoverAssembly.xiShiftedEntire
      CentralCoverAssembly.xiShiftedEntire_differentiable hR
  refine ⟨δ, m₀, M, hδ, hm₀, hM, ?_⟩
  intro x hx y hy
  have hδle : δ ≤ (1 / 4 : ℝ) := min_le_right _ _
  have hδle0 : δ ≤ δ₀ := by
    dsimp [δ]
    exact le_trans (min_le_left _ _) (by linarith)
  have hylow : -(1 / 2 : ℝ) ≤ y := hy.1
  have hyhigh : y ≤ -(1 / 2 : ℝ) + δ := hy.2
  have hyabs : |y| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hxabs : |x| ≤ max |a| |b| :=
    abs_le_max_abs_abs hx.1 hx.2
  let w : ℂ := (x : ℂ) + Complex.I * (y : ℂ)
  have hwball : w ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall]
    have hw_norm : ‖w‖ ≤ max |a| |b| + 1 := by
      dsimp [w]
      calc
        ‖(x : ℂ) + Complex.I * (y : ℂ)‖ ≤
            ‖(x : ℂ)‖ + ‖Complex.I * (y : ℂ)‖ := norm_add_le _ _
        _ = |x| + |y| := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I,
            one_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ max |a| |b| + 1 := by linarith
    have hdist : dist w 0 = ‖w‖ := by simp [dist_eq_norm]
    rw [hdist]
    dsimp [R]
    linarith
  have hlow : m₀ ≤ ‖CentralCoverAssembly.xiShiftedEntire w‖ := by
    have hy₀ : y ∈ Set.Icc (-(1 / 2 : ℝ)) (- (1 / 2 : ℝ) + δ₀) := by
      constructor
      · exact hy.1
      · linarith [hy.2, hδle0]
    exact hbound₀ x hx y hy₀
  have hD : ‖deriv CentralCoverAssembly.xiShiftedEntire w‖ ≤ M :=
    hderiv w hwball
  exact ⟨by simpa [w] using hlow, by simpa [w] using hD⟩

theorem exists_imaginary_axis_compact_lower_bound :
    ∃ m : ℝ, 0 < m ∧
      ∀ y ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        m ≤ ‖CentralCoverAssembly.xiShiftedEntire (Complex.I * (y : ℂ))‖ := by
  let K : Set ℝ := Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)
  have hK : IsCompact K := isCompact_Icc
  have hKne : K.Nonempty := by
    refine ⟨0, ?_⟩
    exact ⟨by norm_num, by norm_num⟩
  let F : ℝ → ℝ := fun y =>
    ‖CentralCoverAssembly.xiShiftedEntire (Complex.I * (y : ℂ))‖
  have hFcont : Continuous F := by
    have hmap : Continuous (fun y : ℝ => Complex.I * (y : ℂ)) := by fun_prop
    exact (CentralCoverAssembly.xiShiftedEntire_differentiable.continuous.comp hmap).norm
  have hFpos : ∀ y ∈ K, 0 < F y := by
    intro y hy
    have hylo : -(1 / 2 : ℝ) ≤ y := hy.1
    have hyhi : y ≤ (1 / 2 : ℝ) := hy.2
    have hne : CentralCoverAssembly.xiShiftedEntire (Complex.I * (y : ℂ)) ≠ 0 := by
      by_cases htop : y = (1 / 2 : ℝ)
      · subst y
        have hv : CentralCoverAssembly.xiShiftedEntire
            (Complex.I * ((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by
          simpa [div_eq_mul_inv] using
            Door3BoundaryEndpoints.xiShiftedEntire_at_pos_I_half
        rw [hv]
        norm_num
      by_cases hbot : y = -(1 / 2 : ℝ)
      · subst y
        have hne : CentralCoverAssembly.xiShiftedEntire
            (-(Complex.I / 2)) ≠ 0 := by
          rw [Door3BoundaryEndpoints.xiShiftedEntire_at_neg_I_half]
          norm_num
        convert hne using 1 <;> norm_num [div_eq_mul_inv]
      have hylo' : -(1 / 2 : ℝ) < y := lt_of_le_of_ne hylo (Ne.symm hbot)
      have hyhi' : y < (1 / 2 : ℝ) := lt_of_le_of_ne hyhi htop
      have hxi := xiShifted_ne_zero_on_imaginary_axis_all_proved y hylo' hyhi'
      have hzlo : -(1 / 2 : ℝ) < (Complex.I * (y : ℂ)).im := by
        simpa [Complex.mul_im] using hylo'
      have hzhi : (Complex.I * (y : ℂ)).im < (1 / 2 : ℝ) := by
        simpa [Complex.mul_im] using hyhi'
      have heq := CentralCoverAssembly.xiShifted_eq_entire_on_strip
        (Complex.I * (y : ℂ)) hzlo hzhi
      intro hzero
      apply hxi
      rw [heq]
      exact hzero
    exact norm_pos_iff.mpr hne
  obtain ⟨m, hm, hmlow⟩ := hK.exists_forall_le' hFcont.continuousOn hFpos
  refine ⟨m, hm, ?_⟩
  intro y hy
  exact hmlow y hy

theorem exists_two_edge_cauchy_data {a b : ℝ} (hab : a ≤ b) :
    ∃ δ m M : ℝ, 0 < δ ∧ δ ≤ (1 / 4 : ℝ) ∧ 0 < m ∧ 0 < M ∧
      (∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc ((1 / 2 : ℝ) - δ) (1 / 2 : ℝ),
        m ≤ ‖CentralCoverAssembly.xiShiftedEntire
            ((x : ℂ) + Complex.I * (y : ℂ))‖ ∧
          ‖deriv CentralCoverAssembly.xiShiftedEntire
            ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ M) ∧
      (∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc (-(1 / 2 : ℝ)) (- (1 / 2 : ℝ) + δ),
        m ≤ ‖CentralCoverAssembly.xiShiftedEntire
            ((x : ℂ) + Complex.I * (y : ℂ))‖ ∧
          ‖deriv CentralCoverAssembly.xiShiftedEntire
            ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ M) := by
  obtain ⟨δt, mt, Mt, hδt, hmt, hMt, htop⟩ := exists_top_edge_cauchy_data hab
  obtain ⟨δb, mb, Mb, hδb, hmb, hMb, hbot⟩ := exists_bottom_edge_cauchy_data hab
  let δ₀ : ℝ := min δt δb
  let δ : ℝ := min δ₀ (1 / 4 : ℝ)
  let m : ℝ := min mt mb
  let M : ℝ := max Mt Mb
  have hδ₀ : 0 < δ₀ := lt_min hδt hδb
  have hδ : 0 < δ := lt_min hδ₀ (by norm_num)
  have hδsmall : δ ≤ (1 / 4 : ℝ) := min_le_right _ _
  have hm : 0 < m := lt_min hmt hmb
  have hM : 0 < M := lt_of_lt_of_le hMt (le_max_left _ _)
  refine ⟨δ, m, M, hδ, hδsmall, hm, hM, ?_, ?_⟩
  · intro x hx y hy
    have hy' : y ∈ Set.Icc ((1 / 2 : ℝ) - δt) (1 / 2 : ℝ) := by
      constructor
      · exact le_trans (sub_le_sub_left
          (le_trans (min_le_left _ _) (min_le_left _ _)) _) hy.1
      · exact hy.2
    obtain ⟨hval, hderiv⟩ := htop x hx y hy'
    exact ⟨le_trans (min_le_left _ _) hval, le_trans hderiv (le_max_left _ _)⟩
  · intro x hx y hy
    have hy' : y ∈ Set.Icc (-(1 / 2 : ℝ)) (- (1 / 2 : ℝ) + δb) := by
      constructor
      · exact hy.1
      · have hδb' : δ ≤ δb := by
          dsimp [δ, δ₀]
          exact le_trans (min_le_left _ _) (min_le_right _ _)
        linarith [hy.2, hδb']
    obtain ⟨hval, hderiv⟩ := hbot x hx y hy'
    exact ⟨le_trans (min_le_right _ _) hval, le_trans hderiv (le_max_right _ _)⟩

theorem exists_two_edge_open_cauchy_data {a b : ℝ} (hab : a ≤ b) :
    ∃ δ m M : ℝ, 0 < δ ∧ 0 < m ∧ 0 < M ∧
      (∀ x ∈ Set.Icc a b, ∀ y : ℝ,
        (1 / 2 : ℝ) - δ ≤ y → y < (1 / 2 : ℝ) →
          m ≤ ‖_root_.xiShifted ((x : ℂ) + Complex.I * (y : ℂ))‖ ∧
          ‖deriv _root_.xiShifted ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ M) ∧
      (∀ x ∈ Set.Icc a b, ∀ y : ℝ,
        -(1 / 2 : ℝ) < y → y ≤ -(1 / 2 : ℝ) + δ →
          m ≤ ‖_root_.xiShifted ((x : ℂ) + Complex.I * (y : ℂ))‖ ∧
          ‖deriv _root_.xiShifted ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ M) := by
  obtain ⟨δ, m, M, hδ, hδsmall, hm, hM, htop, hbot⟩ :=
    exists_two_edge_cauchy_data hab
  refine ⟨δ, m, M, hδ, hm, hM, ?_, ?_⟩
  · intro x hx y hylo hyhi
    have hyclosed : y ∈ Set.Icc ((1 / 2 : ℝ) - δ) (1 / 2 : ℝ) :=
      ⟨hylo, le_of_lt hyhi⟩
    obtain ⟨hval, hderiv⟩ := htop x hx y hyclosed
    let z : ℂ := (x : ℂ) + Complex.I * (y : ℂ)
    have him : z.im = y := by simp [z]
    have hstrip_lo : -(1 / 2 : ℝ) < y := by linarith [hylo, hδsmall]
    have hz_lo : -(1 / 2 : ℝ) < z.im := by simpa [him] using hstrip_lo
    have hz_hi : z.im < (1 / 2 : ℝ) := by simpa [him] using hyhi
    have heq : _root_.xiShifted z = CentralCoverAssembly.xiShiftedEntire z :=
      CentralCoverAssembly.xiShifted_eq_entire_on_strip z hz_lo hz_hi
    have hdeq : deriv _root_.xiShifted z =
        deriv CentralCoverAssembly.xiShiftedEntire z :=
      CentralCoverAssembly.deriv_xiShifted_eq_entire_of_mem_strip z hz_lo hz_hi
    exact ⟨by simpa [z, heq] using hval, by simpa [z, hdeq] using hderiv⟩
  · intro x hx y hylo hyhi
    have hyclosed : y ∈ Set.Icc (-(1 / 2 : ℝ)) (- (1 / 2 : ℝ) + δ) :=
      ⟨le_of_lt hylo, hyhi⟩
    obtain ⟨hval, hderiv⟩ := hbot x hx y hyclosed
    let z : ℂ := (x : ℂ) + Complex.I * (y : ℂ)
    have him : z.im = y := by simp [z]
    have hz_lo : -(1 / 2 : ℝ) < z.im := by simpa [him] using hylo
    have hz_hi : z.im < (1 / 2 : ℝ) := by linarith [hyhi, hδsmall]
    have heq : _root_.xiShifted z = CentralCoverAssembly.xiShiftedEntire z :=
      CentralCoverAssembly.xiShifted_eq_entire_on_strip z hz_lo hz_hi
    have hdeq : deriv _root_.xiShifted z =
        deriv CentralCoverAssembly.xiShiftedEntire z :=
      CentralCoverAssembly.deriv_xiShifted_eq_entire_of_mem_strip z hz_lo hz_hi
    exact ⟨by simpa [z, heq] using hval, by simpa [z, hdeq] using hderiv⟩

#print axioms xiShiftedEntire_eq_xiShifted_top
#print axioms xiShiftedEntire_ne_zero_top
#print axioms exists_top_edge_lower_bound
#print axioms xiShiftedEntire_eq_xiShifted_bottom
#print axioms xiShiftedEntire_ne_zero_bottom
#print axioms exists_bottom_edge_lower_bound
#print axioms exists_top_edge_local_strip
#print axioms exists_top_edge_uniform_strip
#print axioms lower_boundary_nonvanishing_from_outer_bound
#print axioms exists_bottom_edge_uniform_strip
#print axioms exists_top_edge_compact_lower_bound
#print axioms exists_bottom_edge_compact_lower_bound
#print axioms exists_deriv_bound_on_closedBall
#print axioms exists_top_edge_cauchy_data
#print axioms exists_bottom_edge_cauchy_data
#print axioms exists_imaginary_axis_compact_lower_bound
#print axioms exists_two_edge_cauchy_data
#print axioms exists_two_edge_open_cauchy_data

end Door3TopEdge

/-! ## TOPEDGE-NEEDS lower-boundary premise (append-only, value + residual).

Grep (read before filing):
* engine `lower_boundary_nonvanishing_from_outer_bound` (`door3_top_edge.lean:397-443`)
  premises: `Differentiable`, `0 < eps`, `0 < M1`,
  `h_bottom : eps ≤ ‖f (x - I*(1/2))‖`,
  `h_deriv : ∀ y ∈ Icc (-1/2) (-1/2+eps/M1), ‖deriv f ...‖ ≤ M1`,
  via `BoundaryProofEngine.boundary_strip_nonvanishing_of_nonzero_base`
  (`rh_certificate_infra.lean:254-300`).
* bottom feeders `door3_rh_wiring.lean:2040-2080` (`wireStrip_bottom_M40_at_zero_of_ballSup40`)
  and `:2243-2283` (`wireStrip_bottom_M1000_at_zero_of_ballSup1000`) use engine at `x = 0`
  with `eps = 1/2`, `M = 40/1000`, endpoint `wireHbot_bot_point_half_feeder` (`:1897-1899`)
  via `Door3SliverEdge.edgeBot_single_lower` (`door3_sliver_edge.lean:243-246`),
  endpoint norms `:196-200` / `:229-234`, deriv bridges `:768-776` / `:942-950`.
* endpoints `Door3BoundaryEndpoints.xiShiftedEntire_at_neg_I_half`
  (`door3_boundary_endpoints.lean:36-42`).

Value below: closes `h_bottom` at `x = 0`, `eps = 1/2` for `xiShiftedEntire`
from the banked endpoint value, with norm computed by cast + `Complex.norm_real`.
Uniform lower over `Icc (-10) 10` and closed-ball sups stay OPEN, filed as Props.
-/

namespace Door3TopEdgeNeeds

open Complex Real Set Topology

theorem lower_outer_point_half_at_zero :
    (1 / 2 : ℝ) ≤ ‖CentralCoverAssembly.xiShiftedEntire
      (((0 : ℝ) : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ))‖ := by
  have hF : ((((0 : ℝ)) : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ)) =
      (-(Complex.I / 2)) := by
    push_cast
    ring
  have hnorm : ‖CentralCoverAssembly.xiShiftedEntire (-(Complex.I / 2))‖ =
      (1 / 2 : ℝ) := by
    rw [Door3BoundaryEndpoints.xiShiftedEntire_at_neg_I_half]
    have hcast : ((1 / 2 : ℂ)) = ((((1 / 2 : ℝ))) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [hF, hnorm]

def bottom_uniform_lower_residual : Prop :=
  ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
    (1 / 2 : ℝ) ≤ ‖CentralCoverAssembly.xiShiftedEntire
      ((x : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ))‖

def bottom_ballSup_residual (C : ℝ) : Prop :=
  ∀ z ∈ Metric.closedBall (0 : ℂ) 12,
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C

def bottom_uniform_deriv_residual (M : ℝ) : Prop :=
  ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
    ∀ v ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + (1 / 2 : ℝ) / M),
      ‖deriv CentralCoverAssembly.xiShiftedEntire
        ((x : ℂ) + Complex.I * (v : ℂ))‖ ≤ M

end Door3TopEdgeNeeds

/-! ## TOPEDGE-NEXT uniform-deriv conditional (append-only).

Grep:
* `h_bottom` at `door3_top_edge.lean:400` (engine premise) and value
  `lower_outer_point_half_at_zero` (`Door3TopEdgeNeeds`, closes `x = 0`,
  `eps = 1 / 2` for `xiShiftedEntire`).
* residuals `bottom_uniform_lower_residual`, `bottom_ballSup_residual`,
  `bottom_uniform_deriv_residual` (same file, `Door3TopEdgeNeeds` block).

Value: `bottom_uniform_deriv_of_ballSup` reduces the uniform-deriv residual
to the closed-ball sup residual, rebuilding the Cauchy sphere-in-ball argument
used in `exists_bottom_edge_uniform_strip` (sphere radius `1` over the bottom
strip lies in `closedBall 0 12` since `|x| + |v| ≤ 11`), via
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` and
`CentralCoverAssembly.xiShiftedEntire_differentiable.diffContOnCl`.
With `M = max C 1`, the interval `Icc (-1/2) (-1/2 + (1/2)/M)` stays inside
`|v| ≤ 1`, so the bound `C / 1 = C ≤ M` applies.
Remaining gap: `bottom_ballSup_residual` (explicit `C` on `closedBall 0 12`)
and `bottom_uniform_lower_residual` stay OPEN.
-/

namespace Door3TopEdgeNeeds

open Complex Real Set Topology

theorem bottom_uniform_deriv_of_ballSup {C : ℝ}
    (hC : bottom_ballSup_residual C) :
    bottom_uniform_deriv_residual (max C 1) := by
  unfold bottom_uniform_deriv_residual
  intro x hx v hv
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hv1, hv2⟩ := hv
  have hMpos : (0 : ℝ) < max C 1 :=
    lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hM1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
  have hCM : C ≤ max C 1 := le_max_left _ _
  have hdiv : (1 / 2 : ℝ) / max C 1 ≤ 1 / 2 := by
    rw [div_le_iff₀ hMpos]
    linarith [hM1]
  have hxabs : |x| ≤ 10 := by
    rw [abs_le]
    constructor <;> linarith
  have hvabs : |v| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hw_norm : ‖((x : ℂ) + Complex.I * ((v : ℝ) : ℂ))‖ ≤ 10 + 1 := by
    calc
      ‖((x : ℂ) + Complex.I * ((v : ℝ) : ℂ))‖ ≤
          ‖(x : ℂ)‖ + ‖Complex.I * ((v : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |x| + |v| := by
        rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I,
          one_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 10 + 1 := by linarith [hxabs, hvabs]
  have hsphere : ∀ z ∈ Metric.sphere ((x : ℂ) + Complex.I * ((v : ℝ) : ℂ)) (1 : ℝ),
      z ∈ Metric.closedBall (0 : ℂ) 12 := by
    intro z hz
    have hzw : dist z ((x : ℂ) + Complex.I * ((v : ℝ) : ℂ)) = (1 : ℝ) :=
      Metric.mem_sphere.mp hz
    have htri : dist z 0 ≤
        dist z ((x : ℂ) + Complex.I * ((v : ℝ) : ℂ)) +
          dist ((x : ℂ) + Complex.I * ((v : ℝ) : ℂ)) 0 :=
      dist_triangle _ _ _
    have hw0 : dist ((x : ℂ) + Complex.I * ((v : ℝ) : ℂ)) 0 =
        ‖((x : ℂ) + Complex.I * ((v : ℝ) : ℂ))‖ := by
      simp [dist_eq_norm]
    rw [hzw, hw0] at htri
    rw [Metric.mem_closedBall]
    linarith [htri, hw_norm]
  have hDC : DiffContOnCl ℂ CentralCoverAssembly.xiShiftedEntire
      (Metric.ball ((x : ℂ) + Complex.I * ((v : ℝ) : ℂ)) (1 : ℝ)) :=
    CentralCoverAssembly.xiShiftedEntire_differentiable.diffContOnCl
  have hsphere_bound : ∀ z ∈ Metric.sphere
      ((x : ℂ) + Complex.I * ((v : ℝ) : ℂ)) (1 : ℝ),
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C := by
    intro z hz
    exact hC z (hsphere z hz)
  have hbound : ‖deriv CentralCoverAssembly.xiShiftedEntire
      ((x : ℂ) + Complex.I * ((v : ℝ) : ℂ))‖ ≤ C / 1 :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num) hDC
      hsphere_bound
  calc
    ‖deriv CentralCoverAssembly.xiShiftedEntire
        ((x : ℂ) + Complex.I * ((v : ℝ) : ℂ))‖ ≤ C / 1 := hbound
    _ = C := by ring
    _ ≤ max C 1 := hCM

end Door3TopEdgeNeeds

/-! ## TOPEDGE-BALLSUP ballSup premise attempt (append-only, value + exact gap).

Grep (read before filing):
* tail `door3_top_edge.lean:1044-1130` (`bottom_uniform_deriv_of_ballSup` reduces
  uniform-deriv residual to `bottom_ballSup_residual C` on `closedBall 0 12`).
* banked sliver factors `door3_sliver_edge.lean:1049-1084` (poly 78/79),
  `:1146-1163` (pi 4096), `:1166-1180` (joint 319488), residual `:1111-1116`
  (Gamma/zeta uppers absent; poles s=0/s=1 in ball).
* wiring infeasibility `door3_rh_wiring.lean:2303-2375` (joint 319488 exceeds 1000;
  sup1000 target + gammaZeta residual OPEN).
* this file does NOT import the sliver file, so the two banked factors are
  rebuilt locally below from `CentralCoverAssembly.polyOf/piOf` with the same
  triangle/rpow proofs as banked.

Value: local rebuild of poly-78, pi-4096, joint-319488 on `closedBall 0 12`,
plus budget-exceed numerals showing the two-factor product alone cannot meet
C=40 or C=1000.
Gap (exact, OPEN): `Door3TopEdgeNeeds.bottom_ballSup_residual` for
`xiShiftedEntire` stays OPEN; the full-ball Gamma/zeta uppers needed for the
remaining product factors are not supplied in-tree (poles in ball per cited
residuals), filed below as an explicit OPEN target.
-/

namespace Door3TopEdgeBallSup

open Complex Real Set Topology

theorem ballSup_poly_factor_ball12 {s : ℂ}
    (hs : s ∈ Metric.closedBall (0 : ℂ) 12) :
    ‖CentralCoverAssembly.polyOf s‖ ≤ (78 : ℝ) := by
  unfold CentralCoverAssembly.polyOf
  have hdist : dist s (0 : ℂ) ≤ (12 : ℝ) := Metric.mem_closedBall.mp hs
  have heq : dist s (0 : ℂ) = ‖s‖ := dist_zero_right s
  have hnorm : ‖s‖ ≤ (12 : ℝ) := by
    rw [heq] at hdist
    exact hdist
  have hle : ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le s 1
  have h1 : ‖(1 : ℂ)‖ = (1 : ℝ) := norm_one
  have hs1 : ‖s - 1‖ ≤ (13 : ℝ) := by
    rw [h1] at hle
    linarith
  have hstep1 : ‖s‖ * ‖s - 1‖ ≤ (12 : ℝ) * ‖s - 1‖ :=
    mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
  have hstep2 : (12 : ℝ) * ‖s - 1‖ ≤ (12 : ℝ) * (13 : ℝ) :=
    mul_le_mul_of_nonneg_left hs1 (by norm_num)
  have hmul : ‖s * (s - 1)‖ ≤ (12 : ℝ) * (13 : ℝ) := by
    have hnm : ‖s * (s - 1)‖ = ‖s‖ * ‖s - 1‖ := norm_mul s (s - 1)
    rw [hnm]
    exact le_trans hstep1 hstep2
  have hdiv : ‖s * (s - 1) / (2 : ℂ)‖ ≤ (12 : ℝ) * (13 : ℝ) / 2 := by
    rw [norm_div, Complex.norm_two]
    linarith
  have hcalc : (12 : ℝ) * (13 : ℝ) / 2 = (78 : ℝ) := by norm_num
  rw [hcalc] at hdiv
  exact hdiv

theorem ballSup_ball12_re_bounds {s : ℂ} (hs : s ∈ Metric.closedBall (0 : ℂ) 12) :
    (-12 : ℝ) ≤ s.re ∧ s.re ≤ (12 : ℝ) := by
  have hdist : dist s (0 : ℂ) ≤ (12 : ℝ) := Metric.mem_closedBall.mp hs
  have heq : dist s (0 : ℂ) = ‖s‖ := dist_zero_right s
  have hnorm : ‖s‖ ≤ (12 : ℝ) := by
    rw [heq] at hdist
    exact hdist
  have hre : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  rw [abs_le] at hre
  obtain ⟨hlo, hhi⟩ := hre
  constructor <;> linarith

theorem ballSup_piOf_norm_eq (s : ℂ) :
    ‖CentralCoverAssembly.piOf s‖ = Real.pi ^ (-(s.re) / 2) := by
  unfold CentralCoverAssembly.piOf
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos _]
  congr 1
  have h2 : (s / 2).re = s.re / 2 := by rw [Complex.div_ofNat_re]
  have hneg : (-(s / 2)).re = -((s / 2).re) := Complex.neg_re _
  rw [hneg, h2]
  ring

theorem ballSup_pi_factor_ball12 {s : ℂ}
    (hs : s ∈ Metric.closedBall (0 : ℂ) 12) :
    ‖CentralCoverAssembly.piOf s‖ ≤ (4096 : ℝ) := by
  rw [ballSup_piOf_norm_eq]
  obtain ⟨hlo, _⟩ := ballSup_ball12_re_bounds hs
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hexp : -(s.re) / 2 ≤ (6 : ℝ) := by linarith
  have hle1 : Real.pi ^ (-(s.re) / 2) ≤ Real.pi ^ (6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hpi1 hexp
  have hle2 : Real.pi ^ (6 : ℝ) ≤ (4 : ℝ) ^ (6 : ℝ) :=
    Real.rpow_le_rpow (le_of_lt Real.pi_pos) Real.pi_le_four (by norm_num)
  have h4 : (4 : ℝ) ^ (6 : ℝ) = (4096 : ℝ) := by
    have h6 : (6 : ℝ) = (((6 : ℕ)) : ℝ) := by norm_num
    rw [h6, Real.rpow_natCast]
    norm_num
  calc Real.pi ^ (-(s.re) / 2) ≤ Real.pi ^ (6 : ℝ) := hle1
    _ ≤ (4 : ℝ) ^ (6 : ℝ) := hle2
    _ = (4096 : ℝ) := h4

theorem ballSup_polyPi_joint_ball12 {s : ℂ}
    (hs : s ∈ Metric.closedBall (0 : ℂ) 12) :
    ‖CentralCoverAssembly.polyOf s * CentralCoverAssembly.piOf s‖ ≤ (319488 : ℝ) := by
  have hpoly := ballSup_poly_factor_ball12 hs
  have hpi := ballSup_pi_factor_ball12 hs
  have hnn2 : (0 : ℝ) ≤ ‖CentralCoverAssembly.piOf s‖ := norm_nonneg _
  have hmul : ‖CentralCoverAssembly.polyOf s‖ * ‖CentralCoverAssembly.piOf s‖ ≤
      (78 : ℝ) * (4096 : ℝ) :=
    mul_le_mul hpoly hpi hnn2 (by norm_num)
  have hnm : ‖CentralCoverAssembly.polyOf s * CentralCoverAssembly.piOf s‖ =
      ‖CentralCoverAssembly.polyOf s‖ * ‖CentralCoverAssembly.piOf s‖ :=
    norm_mul _ _
  have hcalc : (78 : ℝ) * (4096 : ℝ) = (319488 : ℝ) := by norm_num
  rw [hnm, hcalc] at hmul
  exact hmul

theorem ballSup_joint_exceeds_1000 : (1000 : ℝ) < (319488 : ℝ) := by
  norm_num

theorem ballSup_joint_exceeds_40 : (40 : ℝ) < (319488 : ℝ) := by
  norm_num

def ballSup_full_exact_gap_1000 : Prop :=
  Door3TopEdgeNeeds.bottom_ballSup_residual 1000

def ballSup_full_exact_gap_40 : Prop :=
  Door3TopEdgeNeeds.bottom_ballSup_residual 40

end Door3TopEdgeBallSup

/-! ## TOPEDGE-GAMMA full-ball Gamma/zeta upper attempt (append-only, value + exact gap).

Grep (read before filing):
* tail `door3_top_edge.lean:1155-1257` (`Door3TopEdgeBallSup`: poly-78
  `ballSup_poly_factor_ball12`, pi-4096 `ballSup_pi_factor_ball12`,
  joint-319488 `ballSup_polyPi_joint_ball12`, exceed numerals,
  `ballSup_full_exact_gap_1000/40` as `bottom_ballSup_residual` aliases).
* local Gamma uses in this file are only nonvanishing
  (`Complex.Gamma_ne_zero` at `:34-39`, `:103-109`, `:159-165`); no norm
  upper `‖Complex.Gamma (_ / 2)‖ ≤ G` on `closedBall 0 12` is present here.
* sliver residual `door3_sliver_edge.lean:1111-1116` records Gamma/zeta
  uppers absent on ball-12 with pole obstruction at `s = 0` (Gamma pole
  for `s / 2 = 0`) and `s = 1` (zeta pole), both points in the ball.
* product identity `CentralCoverAssembly.xiShifted_eq_parts`
  (`central_cover_assembly.lean:6339-6347`) factors `xiShifted`, not
  `xiShiftedEntire`; agreement `xiShifted_eq_entire_on_strip` holds only
  on the open strip, so no full-ball transfer to `xiShiftedEntire` is
  available in-tree.

Value: conditional four-factor composition on `closedBall 0 12` from the
locally rebuilt joint-319488 plus hypothetical Gamma/zeta uppers.
Gap (exact, OPEN): `gamma_ball12_upper_residual`, `zeta_ball12_upper_residual`,
and `entire_eq_product_ball12_gap` below; hence `bottom_ballSup_residual`
for `xiShiftedEntire` stays OPEN.
-/

namespace Door3TopEdgeGammaGap

open Complex Real Set Topology

def gamma_ball12_upper_residual (G : ℝ) : Prop :=
  ∀ s ∈ Metric.closedBall (0 : ℂ) 12,
    ‖CentralCoverAssembly.gammaOf s‖ ≤ G

def zeta_ball12_upper_residual (Z : ℝ) : Prop :=
  ∀ s ∈ Metric.closedBall (0 : ℂ) 12,
    ‖zeta s‖ ≤ Z

def entire_eq_product_ball12_gap : Prop :=
  ∀ z ∈ Metric.closedBall (0 : ℂ) 12,
    CentralCoverAssembly.xiShiftedEntire z =
      CentralCoverAssembly.polyOf ((1 / 2 : ℂ) + Complex.I * z) *
      CentralCoverAssembly.piOf ((1 / 2 : ℂ) + Complex.I * z) *
      CentralCoverAssembly.gammaOf ((1 / 2 : ℂ) + Complex.I * z) *
      zeta ((1 / 2 : ℂ) + Complex.I * z)

theorem four_factor_joint_conditional_ball12 {s : ℂ} {G Z : ℝ}
    (hs : s ∈ Metric.closedBall (0 : ℂ) 12)
    (hGnn : 0 ≤ G) (hZnn : 0 ≤ Z)
    (hG : ‖CentralCoverAssembly.gammaOf s‖ ≤ G)
    (hZ : ‖zeta s‖ ≤ Z) :
    ‖CentralCoverAssembly.polyOf s * CentralCoverAssembly.piOf s *
      CentralCoverAssembly.gammaOf s * zeta s‖ ≤ 319488 * G * Z := by
  have hPP := Door3TopEdgeBallSup.ballSup_polyPi_joint_ball12 hs
  have hPPnn : (0 : ℝ) ≤
      ‖CentralCoverAssembly.polyOf s * CentralCoverAssembly.piOf s‖ :=
    norm_nonneg _
  have hGnn0 : (0 : ℝ) ≤ ‖CentralCoverAssembly.gammaOf s‖ :=
    norm_nonneg _
  have hZnn0 : (0 : ℝ) ≤ ‖zeta s‖ := norm_nonneg _
  have h319nn : (0 : ℝ) ≤ (319488 : ℝ) := by norm_num
  have h319Gnn : (0 : ℝ) ≤ (319488 : ℝ) * G :=
    mul_nonneg h319nn hGnn
  have h1 : ‖CentralCoverAssembly.polyOf s * CentralCoverAssembly.piOf s‖ *
      ‖CentralCoverAssembly.gammaOf s‖ ≤ (319488 : ℝ) * G :=
    mul_le_mul hPP hG hGnn0 h319nn
  have h2 : (‖CentralCoverAssembly.polyOf s * CentralCoverAssembly.piOf s‖ *
      ‖CentralCoverAssembly.gammaOf s‖) * ‖zeta s‖ ≤
      ((319488 : ℝ) * G) * Z :=
    mul_le_mul h1 hZ hZnn0 h319Gnn
  have hnorm : ‖CentralCoverAssembly.polyOf s * CentralCoverAssembly.piOf s *
      CentralCoverAssembly.gammaOf s * zeta s‖ =
      (‖CentralCoverAssembly.polyOf s * CentralCoverAssembly.piOf s‖ *
      ‖CentralCoverAssembly.gammaOf s‖) * ‖zeta s‖ := by
    rw [norm_mul, norm_mul]
  have hassoc : (319488 : ℝ) * G * Z = ((319488 : ℝ) * G) * Z := by
    ring
  rw [hnorm, hassoc]
  exact h2

end Door3TopEdgeGammaGap

/-! ## TOPEDGE-ZETA ball12 zeta-premise attempt (append-only, value-or-gap).

Grep (read before filing):
* tail `door3_top_edge.lean:1155-1339` (`Door3TopEdgeBallSup` poly-78,
  pi-4096, joint-319488, plus `Door3TopEdgeGammaGap` Gamma/zeta upper
  residuals, product gap, four-factor conditional).
* this file banks no `‖zeta s‖ ≤ Z` upper on `closedBall 0 12` (only
  nonvanishing at Re = 1 via `riemannZeta_ne_zero_of_one_le_re` near
  `:151-153`); imports are `central_cover_assembly`,
  `door3_boundary_real`, `door3_boundary_endpoints` only, so R02-disc /
  sphere zeta caps from other files are out of scope here.
* pole obstruction `door3_sliver_edge.lean:1234-1240`
  (`pole_zero_mem_ball12`, `pole_one_mem_ball12`) and residual
  `:1111-1116` (points `s = 0` / `s = 1` lie in the ball).

Value: local pole-membership rebuild plus shift-exact joint conditional
closing `Door3TopEdgeNeeds.bottom_ballSup_residual` from Gamma/zeta
uppers plus the product identity.
Gap (exact, OPEN): `Door3TopEdgeGammaGap.zeta_ball12_upper_residual`,
`gamma_ball12_upper_residual`, `entire_eq_product_ball12_gap` stay OPEN;
hence `Door3TopEdgeNeeds.bottom_ballSup_residual` stays OPEN.
-/

namespace Door3TopEdgeZetaAttempt

open Complex Real Set Topology

theorem pole_zero_mem_ball12_local :
    (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 12 := by
  rw [Metric.mem_closedBall, dist_self]
  norm_num

theorem pole_one_mem_ball12_local :
    (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) 12 := by
  rw [Metric.mem_closedBall, dist_zero_right, norm_one]
  norm_num

theorem entire_bound_of_shifted_factors {z : ℂ} {G Z : ℝ}
    (hs : ((1 / 2 : ℂ) + Complex.I * z) ∈ Metric.closedBall (0 : ℂ) 12)
    (hGnn : 0 ≤ G) (hZnn : 0 ≤ Z)
    (hG : ‖CentralCoverAssembly.gammaOf ((1 / 2 : ℂ) + Complex.I * z)‖ ≤ G)
    (hZ : ‖zeta ((1 / 2 : ℂ) + Complex.I * z)‖ ≤ Z)
    (hprod : CentralCoverAssembly.xiShiftedEntire z =
      CentralCoverAssembly.polyOf ((1 / 2 : ℂ) + Complex.I * z) *
      CentralCoverAssembly.piOf ((1 / 2 : ℂ) + Complex.I * z) *
      CentralCoverAssembly.gammaOf ((1 / 2 : ℂ) + Complex.I * z) *
      zeta ((1 / 2 : ℂ) + Complex.I * z)) :
    ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 319488 * G * Z := by
  rw [hprod]
  exact Door3TopEdgeGammaGap.four_factor_joint_conditional_ball12
    hs hGnn hZnn hG hZ

theorem bottom_ballSup_of_shifted_uppers {C G Z : ℝ}
    (hGnn : 0 ≤ G) (hZnn : 0 ≤ Z) (hC : C = 319488 * G * Z)
    (hshift : ∀ z ∈ Metric.closedBall (0 : ℂ) 12,
      ((1 / 2 : ℂ) + Complex.I * z) ∈ Metric.closedBall (0 : ℂ) 12)
    (hG : ∀ s ∈ Metric.closedBall (0 : ℂ) 12,
      ‖CentralCoverAssembly.gammaOf s‖ ≤ G)
    (hZ : ∀ s ∈ Metric.closedBall (0 : ℂ) 12, ‖zeta s‖ ≤ Z)
    (hprod : Door3TopEdgeGammaGap.entire_eq_product_ball12_gap) :
    Door3TopEdgeNeeds.bottom_ballSup_residual C := by
  unfold Door3TopEdgeNeeds.bottom_ballSup_residual
  intro z hz
  have hs := hshift z hz
  have hGb := hG _ hs
  have hZb := hZ _ hs
  have hpr := hprod z hz
  have hb := entire_bound_of_shifted_factors hs hGnn hZnn hGb hZb hpr
  rw [hC]
  exact hb

end Door3TopEdgeZetaAttempt

/-! ## TOPEDGE-UNIFORM-LOWER uniform-lower attempt (append-only, value + exact gap).

Grep (read before filing):
* tail `door3_top_edge.lean:1364-1412` (`Door3TopEdgeZetaAttempt`: pole-membership
  rebuild `pole_zero_mem_ball12_local`, `pole_one_mem_ball12_local`,
  shift-exact joint conditional `entire_bound_of_shifted_factors`,
  `bottom_ballSup_of_shifted_uppers` closing `bottom_ballSup_residual`
  from Gamma/zeta uppers plus product identity).
* banked lower bounds in this file: `exists_bottom_edge_lower_bound`
  (`door3_top_edge.lean:170-188`, existential epsilon over any `Icc a b`
  from compact minimum plus `xiShiftedEntire_ne_zero_bottom`),
  `exists_bottom_edge_compact_lower_bound` (`:608-664`, existential `m`
  over edge strip), pointwise `1 / 2` only at `x = 0`
  (`Door3TopEdgeNeeds.lower_outer_point_half_at_zero`).
* residual `Door3TopEdgeNeeds.bottom_uniform_lower_residual` (`:1027-1030`)
  demands `1 / 2` uniformly over `Icc (-10) 10`; no banked lemma in this
  file supplies `1 / 2` away from `x = 0`.
* ball12 uppers `Door3TopEdgeGammaGap.gamma_ball12_upper_residual`,
  `zeta_ball12_upper_residual`, `entire_eq_product_ball12_gap`
  (`:1289-1303`) stay OPEN, so `bottom_ballSup_residual` stays OPEN.

Value: `bottom_uniform_exist_lower_on_Icc10` chains the banked existential
lower bound at `a = -10`, `b = 10`; `bottom_point_form_eq` rewrites the
edge point to the residual point form.
Gap (exact, OPEN): `uniform_half_open_gap` (alias of
`bottom_uniform_lower_residual`) plus `ballSup_open_gap_40/1000` below.
-/

namespace Door3TopEdgeUniformLower

open Complex Real Set Topology

theorem bottom_uniform_exist_lower_on_Icc10 :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
        ε ≤ ‖CentralCoverAssembly.xiShiftedEntire ((x : ℂ) - Complex.I / 2)‖ := by
  have hab : (-10 : ℝ) ≤ (10 : ℝ) := by norm_num
  obtain ⟨ε, hε, h⟩ :=
    Door3TopEdge.exists_bottom_edge_lower_bound (a := (-10 : ℝ)) (b := (10 : ℝ)) hab
  exact ⟨ε, hε, h⟩

theorem bottom_point_form_eq (x : ℝ) :
    ((x : ℂ) - Complex.I / 2) =
      ((x : ℂ) - Complex.I * (((1 / 2 : ℝ)) : ℂ)) := by
  push_cast
  ring

def uniform_half_open_gap : Prop :=
  Door3TopEdgeNeeds.bottom_uniform_lower_residual

def ballSup_open_gap_40 : Prop :=
  Door3TopEdgeBallSup.ballSup_full_exact_gap_40

def ballSup_open_gap_1000 : Prop :=
  Door3TopEdgeBallSup.ballSup_full_exact_gap_1000

end Door3TopEdgeUniformLower

/-! ## TOPEDGE-STRIP shift-invariance premise attempt (append-only, value-or-gap).

Grep (read before filing):
* tail `door3_top_edge.lean:1393-1470` (`bottom_ballSup_of_shifted_uppers`
  needs `hshift : ∀ z ∈ closedBall 0 12, (1/2 + I*z) ∈ closedBall 0 12`;
  `Door3TopEdgeUniformLower` banks exist-lower Icc10, point-form eq,
  open gaps 40/1000).
* local ball12 inclusions: sphere-in-ball `closedBall 0 12` at `:1097-1111`
  (`|x| + |v| ≤ 11` triangle) and `:498-507`, `:347-356`; poly-78
  `:1159-1186`, pi-4096 `:1210-1227`, joint-319488 `:1229-1243`;
  no `shift_mem` lemma present locally (grep `shift_mem` empty in this file).
* agreement `xiShifted_eq_entire_on_strip` holds only on the open strip
  (`:1274-1276`), so no full-ball transfer is available in-tree.

Value: triangle rebuild chaining the banked `norm_add_le` technique gives
`12 → 25/2` inclusion for `z ↦ 1/2 + I*z`.
Gap (exact, OPEN): `shift_invariance_12_gap` (`12 → 12`) below; the
triangle bound yields `1/2 + 12 = 25/2`, not `12`, and no banked lemma
in this file improves it to `12`, so the `12 → 12` premise stays OPEN.
-/

namespace Door3TopEdgeStrip

open Complex Real Set Topology

theorem shift_norm_le_of_mem_ball12 {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 12) :
    ‖(1 / 2 : ℂ) + Complex.I * z‖ ≤ (25 / 2 : ℝ) := by
  have hdist : dist z (0 : ℂ) ≤ (12 : ℝ) := Metric.mem_closedBall.mp hz
  rw [dist_zero_right] at hdist
  have hI : ‖Complex.I * z‖ = ‖z‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    have hcast : (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have htri : ‖(1 / 2 : ℂ) + Complex.I * z‖ ≤
      ‖(1 / 2 : ℂ)‖ + ‖Complex.I * z‖ := norm_add_le _ _
  rw [hhalf, hI] at htri
  linarith

theorem shift_mem_ball125_of_mem_ball12 {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 12) :
    ((1 / 2 : ℂ) + Complex.I * z) ∈ Metric.closedBall (0 : ℂ) (25 / 2) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  exact shift_norm_le_of_mem_ball12 hz

def shift_invariance_12_gap : Prop :=
  ∀ z ∈ Metric.closedBall (0 : ℂ) 12,
    ((1 / 2 : ℂ) + Complex.I * z) ∈ Metric.closedBall (0 : ℂ) 12

def shift_invariance_12_open : Prop :=
  shift_invariance_12_gap

end Door3TopEdgeStrip

/-! ## TOPEDGE-BALL25 ball-25/2 premise attempt (append-only, value + exact gap).

Grep (read before filing):
* tail `door3_top_edge.lean:1493-1528` (`Door3TopEdgeStrip`: triangle
  `shift_norm_le_of_mem_ball12`, inclusion `shift_mem_ball125_of_mem_ball12`
  `12 -> 25/2`, gap `shift_invariance_12_gap` `12 -> 12` OPEN).
* ball-12 factors `Door3TopEdgeBallSup` (`:1159-1243`: poly-78, pi-4096,
  joint-319488) live on `closedBall 0 12`; no lemma in this file supplies a
  sup on `closedBall 0 (25/2)` (grep `closedBall.*25` in this file hits only
  `:1517`, the shift target).
* Gamma/zeta uppers `Door3TopEdgeGammaGap.gamma_ball12_upper_residual`,
  `zeta_ball12_upper_residual` (`:1289-1295`) are ball-12 only; product gap
  `entire_eq_product_ball12_gap` (`:1297-1303`) is at `z` in ball-12.

Value: local poly/pi/joint rebuild on `closedBall 0 (25/2)` (poly `675/8`,
pi `16384` via exponent `<= 7`, joint `1382400`), four-factor conditional on
the shifted point, and `bottom_ballSup_of_shifted_uppers_25` chaining the
banked `12 -> 25/2` inclusion so `bottom_ballSup_residual` follows from
25/2 Gamma/zeta uppers plus the existing product identity.
Gap (exact, OPEN): `gamma_ball25_upper_residual`, `zeta_ball25_upper_residual`
below; hence `Door3TopEdgeNeeds.bottom_ballSup_residual` stays OPEN.
-/

namespace Door3TopEdgeBall25

open Complex Real Set Topology

theorem ballSup_ball25_re_bounds {s : ℂ}
    (hs : s ∈ Metric.closedBall (0 : ℂ) (25 / 2)) :
    (-(25 / 2) : ℝ) ≤ s.re ∧ s.re ≤ (25 / 2 : ℝ) := by
  have hdist : dist s (0 : ℂ) ≤ (25 / 2 : ℝ) := Metric.mem_closedBall.mp hs
  have heq : dist s (0 : ℂ) = ‖s‖ := dist_zero_right s
  have hnorm : ‖s‖ ≤ (25 / 2 : ℝ) := by
    rw [heq] at hdist
    exact hdist
  have hre : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  rw [abs_le] at hre
  obtain ⟨hlo, hhi⟩ := hre
  constructor <;> linarith

theorem ballSup_poly_factor_ball25 {s : ℂ}
    (hs : s ∈ Metric.closedBall (0 : ℂ) (25 / 2)) :
    ‖CentralCoverAssembly.polyOf s‖ ≤ (675 / 8 : ℝ) := by
  unfold CentralCoverAssembly.polyOf
  have hdist : dist s (0 : ℂ) ≤ (25 / 2 : ℝ) := Metric.mem_closedBall.mp hs
  have heq : dist s (0 : ℂ) = ‖s‖ := dist_zero_right s
  have hnorm : ‖s‖ ≤ (25 / 2 : ℝ) := by
    rw [heq] at hdist
    exact hdist
  have hle : ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le s 1
  have h1 : ‖(1 : ℂ)‖ = (1 : ℝ) := norm_one
  have hs1 : ‖s - 1‖ ≤ (27 / 2 : ℝ) := by
    rw [h1] at hle
    linarith
  have hstep1 : ‖s‖ * ‖s - 1‖ ≤ (25 / 2 : ℝ) * ‖s - 1‖ :=
    mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
  have hstep2 : (25 / 2 : ℝ) * ‖s - 1‖ ≤ (25 / 2 : ℝ) * (27 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_left hs1 (by norm_num)
  have hmul : ‖s * (s - 1)‖ ≤ (25 / 2 : ℝ) * (27 / 2 : ℝ) := by
    have hnm : ‖s * (s - 1)‖ = ‖s‖ * ‖s - 1‖ := norm_mul s (s - 1)
    rw [hnm]
    exact le_trans hstep1 hstep2
  have hdiv : ‖s * (s - 1) / (2 : ℂ)‖ ≤ (25 / 2 : ℝ) * (27 / 2 : ℝ) / 2 := by
    rw [norm_div, Complex.norm_two]
    linarith
  have hcalc : (25 / 2 : ℝ) * (27 / 2 : ℝ) / 2 = (675 / 8 : ℝ) := by
    norm_num
  rw [hcalc] at hdiv
  exact hdiv

theorem ballSup_piOf_norm_eq_25 (s : ℂ) :
    ‖CentralCoverAssembly.piOf s‖ = Real.pi ^ (-(s.re) / 2) := by
  unfold CentralCoverAssembly.piOf
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos _]
  congr 1
  have h2 : (s / 2).re = s.re / 2 := by rw [Complex.div_ofNat_re]
  have hneg : (-(s / 2)).re = -((s / 2).re) := Complex.neg_re _
  rw [hneg, h2]
  ring

theorem ballSup_pi_factor_ball25 {s : ℂ}
    (hs : s ∈ Metric.closedBall (0 : ℂ) (25 / 2)) :
    ‖CentralCoverAssembly.piOf s‖ ≤ (16384 : ℝ) := by
  rw [ballSup_piOf_norm_eq_25]
  obtain ⟨hlo, _⟩ := ballSup_ball25_re_bounds hs
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hexp : -(s.re) / 2 ≤ (7 : ℝ) := by linarith
  have hle1 : Real.pi ^ (-(s.re) / 2) ≤ Real.pi ^ (7 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hpi1 hexp
  have hle2 : Real.pi ^ (7 : ℝ) ≤ (4 : ℝ) ^ (7 : ℝ) :=
    Real.rpow_le_rpow (le_of_lt Real.pi_pos) Real.pi_le_four (by norm_num)
  have h4 : (4 : ℝ) ^ (7 : ℝ) = (16384 : ℝ) := by
    have h7 : (7 : ℝ) = (((7 : ℕ)) : ℝ) := by norm_num
    rw [h7, Real.rpow_natCast]
    norm_num
  calc Real.pi ^ (-(s.re) / 2) ≤ Real.pi ^ (7 : ℝ) := hle1
    _ ≤ (4 : ℝ) ^ (7 : ℝ) := hle2
    _ = (16384 : ℝ) := h4

theorem ballSup_polyPi_joint_ball25 {s : ℂ}
    (hs : s ∈ Metric.closedBall (0 : ℂ) (25 / 2)) :
    ‖CentralCoverAssembly.polyOf s * CentralCoverAssembly.piOf s‖ ≤
      (1382400 : ℝ) := by
  have hpoly := ballSup_poly_factor_ball25 hs
  have hpi := ballSup_pi_factor_ball25 hs
  have hnn2 : (0 : ℝ) ≤ ‖CentralCoverAssembly.piOf s‖ := norm_nonneg _
  have hmul : ‖CentralCoverAssembly.polyOf s‖ * ‖CentralCoverAssembly.piOf s‖ ≤
      (675 / 8 : ℝ) * (16384 : ℝ) :=
    mul_le_mul hpoly hpi hnn2 (by norm_num)
  have hnm : ‖CentralCoverAssembly.polyOf s * CentralCoverAssembly.piOf s‖ =
      ‖CentralCoverAssembly.polyOf s‖ * ‖CentralCoverAssembly.piOf s‖ :=
    norm_mul _ _
  have hcalc : (675 / 8 : ℝ) * (16384 : ℝ) = (1382400 : ℝ) := by norm_num
  rw [hnm, hcalc] at hmul
  exact hmul

theorem ballSup_joint25_exceeds_1000 : (1000 : ℝ) < (1382400 : ℝ) := by
  norm_num

theorem ballSup_joint25_exceeds_40 : (40 : ℝ) < (1382400 : ℝ) := by
  norm_num

theorem four_factor_joint_conditional_ball25 {s : ℂ} {G Z : ℝ}
    (hs : s ∈ Metric.closedBall (0 : ℂ) (25 / 2))
    (hGnn : 0 ≤ G) (hZnn : 0 ≤ Z)
    (hG : ‖CentralCoverAssembly.gammaOf s‖ ≤ G)
    (hZ : ‖zeta s‖ ≤ Z) :
    ‖CentralCoverAssembly.polyOf s * CentralCoverAssembly.piOf s *
      CentralCoverAssembly.gammaOf s * zeta s‖ ≤ 1382400 * G * Z := by
  have hPP := ballSup_polyPi_joint_ball25 hs
  have hPPnn : (0 : ℝ) ≤
      ‖CentralCoverAssembly.polyOf s * CentralCoverAssembly.piOf s‖ :=
    norm_nonneg _
  have hGnn0 : (0 : ℝ) ≤ ‖CentralCoverAssembly.gammaOf s‖ :=
    norm_nonneg _
  have hZnn0 : (0 : ℝ) ≤ ‖zeta s‖ := norm_nonneg _
  have h319nn : (0 : ℝ) ≤ (1382400 : ℝ) := by norm_num
  have h319Gnn : (0 : ℝ) ≤ (1382400 : ℝ) * G :=
    mul_nonneg h319nn hGnn
  have h1 : ‖CentralCoverAssembly.polyOf s * CentralCoverAssembly.piOf s‖ *
      ‖CentralCoverAssembly.gammaOf s‖ ≤ (1382400 : ℝ) * G :=
    mul_le_mul hPP hG hGnn0 h319nn
  have h2 : (‖CentralCoverAssembly.polyOf s * CentralCoverAssembly.piOf s‖ *
      ‖CentralCoverAssembly.gammaOf s‖) * ‖zeta s‖ ≤
      ((1382400 : ℝ) * G) * Z :=
    mul_le_mul h1 hZ hZnn0 h319Gnn
  have hnorm : ‖CentralCoverAssembly.polyOf s * CentralCoverAssembly.piOf s *
      CentralCoverAssembly.gammaOf s * zeta s‖ =
      (‖CentralCoverAssembly.polyOf s * CentralCoverAssembly.piOf s‖ *
      ‖CentralCoverAssembly.gammaOf s‖) * ‖zeta s‖ := by
    rw [norm_mul, norm_mul]
  have hassoc : (1382400 : ℝ) * G * Z = ((1382400 : ℝ) * G) * Z := by
    ring
  rw [hnorm, hassoc]
  exact h2

def gamma_ball25_upper_residual (G : ℝ) : Prop :=
  ∀ s ∈ Metric.closedBall (0 : ℂ) (25 / 2),
    ‖CentralCoverAssembly.gammaOf s‖ ≤ G

def zeta_ball25_upper_residual (Z : ℝ) : Prop :=
  ∀ s ∈ Metric.closedBall (0 : ℂ) (25 / 2),
    ‖zeta s‖ ≤ Z

theorem bottom_ballSup_of_shifted_uppers_25 {C G Z : ℝ}
    (hGnn : 0 ≤ G) (hZnn : 0 ≤ Z) (hC : C = 1382400 * G * Z)
    (hG : ∀ s ∈ Metric.closedBall (0 : ℂ) (25 / 2),
      ‖CentralCoverAssembly.gammaOf s‖ ≤ G)
    (hZ : ∀ s ∈ Metric.closedBall (0 : ℂ) (25 / 2), ‖zeta s‖ ≤ Z)
    (hprod : Door3TopEdgeGammaGap.entire_eq_product_ball12_gap) :
    Door3TopEdgeNeeds.bottom_ballSup_residual C := by
  unfold Door3TopEdgeNeeds.bottom_ballSup_residual
  intro z hz
  have hs25 : ((1 / 2 : ℂ) + Complex.I * z) ∈
      Metric.closedBall (0 : ℂ) (25 / 2) :=
    Door3TopEdgeStrip.shift_mem_ball125_of_mem_ball12 hz
  have hGb : ‖CentralCoverAssembly.gammaOf ((1 / 2 : ℂ) + Complex.I * z)‖ ≤ G :=
    hG _ hs25
  have hZb : ‖zeta ((1 / 2 : ℂ) + Complex.I * z)‖ ≤ Z :=
    hZ _ hs25
  have hpr : CentralCoverAssembly.xiShiftedEntire z =
      CentralCoverAssembly.polyOf ((1 / 2 : ℂ) + Complex.I * z) *
      CentralCoverAssembly.piOf ((1 / 2 : ℂ) + Complex.I * z) *
      CentralCoverAssembly.gammaOf ((1 / 2 : ℂ) + Complex.I * z) *
      zeta ((1 / 2 : ℂ) + Complex.I * z) := hprod z hz
  have hb : ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ 1382400 * G * Z := by
    rw [hpr]
    exact four_factor_joint_conditional_ball25 hs25 hGnn hZnn hGb hZb
  rw [hC]
  exact hb

end Door3TopEdgeBall25

/-! ## TOPEDGE-PRODUCT product-identity premise attempt (append-only, value + exact gap).

Grep (read before filing):
* tail `door3_top_edge.lean:1493-1721` (`Door3TopEdgeStrip` 12 to 25/2 inclusion,
  `Door3TopEdgeBall25` poly 675/8, pi 16384, joint 1382400, conditional
  `bottom_ballSup_of_shifted_uppers_25`).
* banked agreement `CentralCoverAssembly.xiShifted_eq_entire_on_strip`
  (`central_cover_assembly.lean:836-840`, used locally at `:287-292`, `:391-393`).
* banked factorisation `DerivCauchyBridge.xiShifted_eq_parts`
  (`central_cover_assembly.lean:6339-6347`, for `_root_.xiShifted`, not entire).
* open product gap `Door3TopEdgeGammaGap.entire_eq_product_ball12_gap` (`:1297-1303`).

Value: strip-conditional entire product identity chaining the two banked lemmas.
Gap (exact, OPEN): full-ball `entire_eq_product_ball12_gap` stays OPEN; ball-12
holds a point outside the strip so the chain does not extend, filed below.
-/

namespace Door3TopEdgeProduct

open Complex Real Set Topology

theorem entire_eq_product_of_mem_strip (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ)) :
    CentralCoverAssembly.xiShiftedEntire z =
      DerivCauchyBridge.polyOf ((1 / 2 : ℂ) + Complex.I * z) *
      DerivCauchyBridge.piOf ((1 / 2 : ℂ) + Complex.I * z) *
      DerivCauchyBridge.gammaOf ((1 / 2 : ℂ) + Complex.I * z) *
      zeta ((1 / 2 : ℂ) + Complex.I * z) := by
  have hagree : _root_.xiShifted z = CentralCoverAssembly.xiShiftedEntire z :=
    CentralCoverAssembly.xiShifted_eq_entire_on_strip z hgt hlt
  have hparts : _root_.xiShifted z =
      DerivCauchyBridge.polyOf ((1 / 2 : ℂ) + Complex.I * z) *
      DerivCauchyBridge.piOf ((1 / 2 : ℂ) + Complex.I * z) *
      DerivCauchyBridge.gammaOf ((1 / 2 : ℂ) + Complex.I * z) *
      zeta ((1 / 2 : ℂ) + Complex.I * z) :=
    DerivCauchyBridge.xiShifted_eq_parts z
  exact hagree.symm.trans hparts

theorem outer_point_mem_ball12 :
    Complex.I * (((12 : ℝ)) : ℂ) ∈ Metric.closedBall (0 : ℂ) 12 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  have hmul : ‖Complex.I * ((((12 : ℝ))) : ℂ)‖ = ‖((((12 : ℝ))) : ℂ)‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  rw [hmul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  exact le_rfl

theorem outer_point_im_eq :
    (Complex.I * (((12 : ℝ)) : ℂ)).im = (12 : ℝ) := by
  simp [Complex.mul_im]

theorem outer_point_outside_strip :
    ¬ ((Complex.I * (((12 : ℝ)) : ℂ)).im < (1 / 2 : ℝ)) := by
  rw [outer_point_im_eq]
  norm_num

def product_full_ball_open_gap : Prop :=
  Door3TopEdgeGammaGap.entire_eq_product_ball12_gap

def gamma_ball12_open_gap (G : ℝ) : Prop :=
  Door3TopEdgeGammaGap.gamma_ball12_upper_residual G

def zeta_ball12_open_gap (Z : ℝ) : Prop :=
  Door3TopEdgeGammaGap.zeta_ball12_upper_residual Z

def gamma_ball25_open_gap (G : ℝ) : Prop :=
  Door3TopEdgeBall25.gamma_ball25_upper_residual G

def zeta_ball25_open_gap (Z : ℝ) : Prop :=
  Door3TopEdgeBall25.zeta_ball25_upper_residual Z

end Door3TopEdgeProduct

/-! ## TOPEDGE-AGREE agreement-extension attempt (append-only, exact gap).

Grep (read before filing):
* tail `door3_top_edge.lean:1740-1793` (`Door3TopEdgeProduct`: strip-conditional
  `entire_eq_product_of_mem_strip` via `xiShifted_eq_entire_on_strip` plus
  `xiShifted_eq_parts`, obstruction `outer_point_mem_ball12`,
  `outer_point_im_eq`, `outer_point_outside_strip`).
* banked agreement in this file: `CentralCoverAssembly.xiShifted_eq_entire_on_strip`
  at `:289, :392, :541, :595, :653, :865, :943, :957, :1752`;
  `CentralCoverAssembly.deriv_xiShifted_eq_entire_of_mem_strip` at `:946, :960`;
  factor `DerivCauchyBridge.xiShifted_eq_parts` at `:1758`.
* ball12 uppers `Door3TopEdgeGammaGap.gamma_ball12_upper_residual`,
  `zeta_ball12_upper_residual` (`:1289-1295`), ball25 uppers
  `Door3TopEdgeBall25.gamma_ball25_upper_residual`,
  `zeta_ball25_upper_residual` (`:1686-1692`) stay OPEN.

Value: `agree_chain_on_strip` re-chains the two banked lemmas through the
filed strip-conditional identity; `agree_extension_blocked` plus
`agree_chain_stops_at_outer` witness that the chain needs the upper strip
bound at the outer ball point, which the banked obstruction refutes.
Gap (exact, OPEN): `agree_extension_open_gap` (full-ball product gap) plus
ball12/ball25 upper gaps below; hence `bottom_ballSup_residual` stays OPEN.
-/

namespace Door3TopEdgeAgreeExt

open Complex Real Set Topology

theorem agree_chain_on_strip (z : ℂ)
    (hgt : -(1 / 2 : ℝ) < z.im) (hlt : z.im < (1 / 2 : ℝ)) :
    CentralCoverAssembly.xiShiftedEntire z =
      DerivCauchyBridge.polyOf ((1 / 2 : ℂ) + Complex.I * z) *
      DerivCauchyBridge.piOf ((1 / 2 : ℂ) + Complex.I * z) *
      DerivCauchyBridge.gammaOf ((1 / 2 : ℂ) + Complex.I * z) *
      zeta ((1 / 2 : ℂ) + Complex.I * z) :=
  Door3TopEdgeProduct.entire_eq_product_of_mem_strip z hgt hlt

theorem agree_extension_blocked :
    (Complex.I * (((12 : ℝ)) : ℂ)) ∈ Metric.closedBall (0 : ℂ) 12 ∧
      ¬ ((Complex.I * (((12 : ℝ)) : ℂ)).im < (1 / 2 : ℝ)) := by
  constructor
  · exact Door3TopEdgeProduct.outer_point_mem_ball12
  · exact Door3TopEdgeProduct.outer_point_outside_strip

theorem agree_chain_stops_at_outer
    (h : (Complex.I * (((12 : ℝ)) : ℂ)).im < (1 / 2 : ℝ)) : False :=
  Door3TopEdgeProduct.outer_point_outside_strip h

def agree_extension_open_gap : Prop :=
  Door3TopEdgeGammaGap.entire_eq_product_ball12_gap

def agree_ball12_gamma_open (G : ℝ) : Prop :=
  Door3TopEdgeGammaGap.gamma_ball12_upper_residual G

def agree_ball12_zeta_open (Z : ℝ) : Prop :=
  Door3TopEdgeGammaGap.zeta_ball12_upper_residual Z

def agree_ball25_gamma_open (G : ℝ) : Prop :=
  Door3TopEdgeBall25.gamma_ball25_upper_residual G

def agree_ball25_zeta_open (Z : ℝ) : Prop :=
  Door3TopEdgeBall25.zeta_ball25_upper_residual Z

end Door3TopEdgeAgreeExt

/-! ## TOPEDGE-FINAL-LEDGER (append-only, proof-only, clean block).

Grep (full tail read before filing, `Select-String ^(theorem|def)` + tail windows):
* CLOSED engine/edge: `xiShiftedEntire_eq_xiShifted_top` (:12), `xiShiftedEntire_ne_zero_top`
  (:50), `exists_top_edge_lower_bound` (:61), `xiShiftedEntire_eq_xiShifted_bottom` (:81),
  `xiShiftedEntire_ne_zero_bottom` (:120), `exists_bottom_edge_lower_bound` (:170),
  `exists_top_edge_local_strip` (:194), `exists_top_edge_uniform_strip` (:294),
  `lower_boundary_nonvanishing_from_outer_bound` (:397),
  `exists_bottom_edge_uniform_strip` (:445), `exists_top_edge_compact_lower_bound` (:546),
  `exists_bottom_edge_compact_lower_bound` (:608), `exists_deriv_bound_on_closedBall` (:666),
  `exists_top_edge_cauchy_data` (:707), `exists_bottom_edge_cauchy_data` (:764),
  `exists_imaginary_axis_compact_lower_bound` (:824), `exists_two_edge_cauchy_data` (:877),
  `exists_two_edge_open_cauchy_data` (:920).
* CLOSED numerals: `Door3TopEdgeNeeds.lower_outer_point_half_at_zero` (:1010)
  value `1/2`; `Door3TopEdgeBallSup.ballSup_poly_factor_ball12` (:1159) value `78`;
  `ballSup_pi_factor_ball12` (:1210) value `4096`; `ballSup_polyPi_joint_ball12` (:1229)
  value `319488`; `ballSup_joint_exceeds_1000` (:1245) `1000 < 319488`;
  `ballSup_joint_exceeds_40` (:1248) `40 < 319488`;
  `Door3TopEdgeBall25.ballSup_poly_factor_ball25` (:1570) value `675/8`;
  `ballSup_pi_factor_ball25` (:1610) value `16384`;
  `ballSup_polyPi_joint_ball25` (:1629) value `1382400`;
  `ballSup_joint25_exceeds_1000` (:1646) `1000 < 1382400`;
  `ballSup_joint25_exceeds_40` (:1649) `40 < 1382400`.
* CLOSED conditionals/inclusions: `Door3TopEdgeNeeds.bottom_uniform_deriv_of_ballSup`
  (:1069) `M = max C 1`; `Door3TopEdgeGammaGap.four_factor_joint_conditional_ball12`
  (:1305) factor `319488 * G * Z`; `Door3TopEdgeZetaAttempt.pole_zero_mem_ball12_local`
  (:1368), `pole_one_mem_ball12_local` (:1373), `entire_bound_of_shifted_factors` (:1378),
  `bottom_ballSup_of_shifted_uppers` (:1393);
  `Door3TopEdgeUniformLower.bottom_uniform_exist_lower_on_Icc10` (:1446),
  `bottom_point_form_eq` (:1455); `Door3TopEdgeStrip.shift_norm_le_of_mem_ball12` (:1497)
  bound `25/2`, `shift_mem_ball125_of_mem_ball12` (:1515) `12 -> 25/2`;
  `Door3TopEdgeBall25.four_factor_joint_conditional_ball25` (:1652)
  factor `1382400 * G * Z`, `bottom_ballSup_of_shifted_uppers_25` (:1694);
  `Door3TopEdgeProduct.entire_eq_product_of_mem_strip` (:1744) strip-conditional,
  `outer_point_mem_ball12` (:1761), `outer_point_im_eq` (:1769),
  `outer_point_outside_strip` (:1773);
  `Door3TopEdgeAgreeExt.agree_chain_on_strip` (:1823),
  `agree_extension_blocked` (:1832), `agree_chain_stops_at_outer` (:1839).
* OPEN gaps (exact Props, no numeral closed): `Door3TopEdgeNeeds.bottom_uniform_lower_residual`
  (:1027) `∀ x ∈ Icc (-10) 10, 1/2 ≤ ‖xiShiftedEntire (x - I*(1/2))‖`;
  `Door3TopEdgeNeeds.bottom_ballSup_residual C` (:1032)
  `∀ z ∈ closedBall 0 12, ‖xiShiftedEntire z‖ ≤ C`;
  `Door3TopEdgeNeeds.bottom_uniform_deriv_residual M` (:1036);
  `Door3TopEdgeBallSup.ballSup_full_exact_gap_1000` (:1251) `= bottom_ballSup_residual 1000`;
  `ballSup_full_exact_gap_40` (:1254) `= bottom_ballSup_residual 40`;
  `Door3TopEdgeGammaGap.gamma_ball12_upper_residual G` (:1289);
  `zeta_ball12_upper_residual Z` (:1293); `entire_eq_product_ball12_gap` (:1297);
  `Door3TopEdgeUniformLower.uniform_half_open_gap` (:1461);
  `ballSup_open_gap_40` (:1464); `ballSup_open_gap_1000` (:1467);
  `Door3TopEdgeStrip.shift_invariance_12_gap` (:1521) `12 -> 12`;
  `shift_invariance_12_open` (:1525); `Door3TopEdgeBall25.gamma_ball25_upper_residual` (:1686);
  `zeta_ball25_upper_residual` (:1690); `Door3TopEdgeProduct.product_full_ball_open_gap` (:1778);
  `gamma_ball12_open_gap` (:1781); `zeta_ball12_open_gap` (:1784);
  `gamma_ball25_open_gap` (:1787); `zeta_ball25_open_gap` (:1790);
  `Door3TopEdgeAgreeExt.agree_extension_open_gap` (:1843);
  `agree_ball12_gamma_open` (:1846); `agree_ball12_zeta_open` (:1849);
  `agree_ball25_gamma_open` (:1852); `agree_ball25_zeta_open` (:1855).

Ledger verdict: NO remaining closable premise in this file under the proof-only
constraint; every numeral above is banked, every residual above stays OPEN.
Bottom `bottom_ballSup_residual` (C = 40 / 1000) stays OPEN for lack of full-ball
Gamma/zeta uppers + full-ball product identity + `12 -> 12` shift invariance;
uniform `1/2` lower over `Icc (-10) 10` stays OPEN (only pointwise `1/2` at `x = 0`
plus existential lower are banked). Aliases below re-export the exact open Props.
-/

namespace Door3TopEdgeFinalLedger

open Complex Real Set Topology

def final_open_uniform_lower : Prop :=
  Door3TopEdgeNeeds.bottom_uniform_lower_residual

def final_open_ballSup (C : ℝ) : Prop :=
  Door3TopEdgeNeeds.bottom_ballSup_residual C

def final_open_ballSup_40 : Prop :=
  Door3TopEdgeBallSup.ballSup_full_exact_gap_40

def final_open_ballSup_1000 : Prop :=
  Door3TopEdgeBallSup.ballSup_full_exact_gap_1000

def final_open_deriv (M : ℝ) : Prop :=
  Door3TopEdgeNeeds.bottom_uniform_deriv_residual M

def final_open_gamma12 (G : ℝ) : Prop :=
  Door3TopEdgeGammaGap.gamma_ball12_upper_residual G

def final_open_zeta12 (Z : ℝ) : Prop :=
  Door3TopEdgeGammaGap.zeta_ball12_upper_residual Z

def final_open_product12 : Prop :=
  Door3TopEdgeGammaGap.entire_eq_product_ball12_gap

def final_open_shift12 : Prop :=
  Door3TopEdgeStrip.shift_invariance_12_gap

def final_open_gamma25 (G : ℝ) : Prop :=
  Door3TopEdgeBall25.gamma_ball25_upper_residual G

def final_open_zeta25 (Z : ℝ) : Prop :=
  Door3TopEdgeBall25.zeta_ball25_upper_residual Z

def final_open_agree : Prop :=
  Door3TopEdgeAgreeExt.agree_extension_open_gap

end Door3TopEdgeFinalLedger

/-! ## TOPEDGE-CLOSE final confirmation (append-only, proof-only).

Grep tail before filing (1966 lines):
* closed engines/edges lines 12-920, closed numerals lines 1010-1649,
  closed conditionals lines 1069-1839, final aliases lines 1926-1966.
* open residuals lines 1027-1855 re-exported by FinalLedger defs.

Value below: `ballSup_40_to_1000` chains banked defs locally:
  sup bound 40 gives sup bound 1000 by transitivity of `≤` with `40 ≤ 1000`.
Residual below: absolute sup bounds stay OPEN, filed as exact Props.
-/

namespace Door3TopEdgeClose

open Complex Real Set Topology

theorem ballSup_40_to_1000 :
    Door3TopEdgeNeeds.bottom_ballSup_residual 40 →
      Door3TopEdgeNeeds.bottom_ballSup_residual 1000 := by
  intro h z hz
  have hle := h z hz
  have h40 : (40 : ℝ) ≤ 1000 := by norm_num
  exact le_trans hle h40

def close_open_ballSup_40 : Prop :=
  Door3TopEdgeNeeds.bottom_ballSup_residual 40

def close_open_ballSup_1000 : Prop :=
  Door3TopEdgeNeeds.bottom_ballSup_residual 1000

def close_open_uniform_lower : Prop :=
  Door3TopEdgeNeeds.bottom_uniform_lower_residual

def close_open_gamma12 (G : ℝ) : Prop :=
  Door3TopEdgeGammaGap.gamma_ball12_upper_residual G

def close_open_zeta12 (Z : ℝ) : Prop :=
  Door3TopEdgeGammaGap.zeta_ball12_upper_residual Z

end Door3TopEdgeClose

/-! ## TOPEDGE-UNIFORM chain exist-lower to residual form (append-only, value + exact gap).

Grep (read before filing):
* tail `door3_top_edge.lean:1984-2007` (`Door3TopEdgeClose`: `ballSup_40_to_1000`
  monotone 40 to 1000, open gaps re-exported).
* banked lower bounds in this file: `Door3TopEdge.exists_bottom_edge_lower_bound`
  (`:170-188`, existential over any `Icc`),
  `Door3TopEdgeUniformLower.bottom_uniform_exist_lower_on_Icc10` (`:1446-1453`,
  existential over `Icc (-10) 10`),
  `Door3TopEdgeUniformLower.bottom_point_form_eq` (`:1455-1459`, rewrites
  `x - I / 2` to residual point form), pointwise `1 / 2` at `x = 0`
  (`Door3TopEdgeNeeds.lower_outer_point_half_at_zero` `:1010-1025`).
* residual `Door3TopEdgeNeeds.bottom_uniform_lower_residual` (`:1027-1030`)
  demands `1 / 2` uniformly over `Icc (-10) 10`; no banked lemma supplies
  `1 / 2` away from `x = 0`.

Value: `bottom_uniform_exist_lower_residual_form` chains the banked
existential Icc10 lower into residual point form.
Gap (exact, OPEN): `uniform_half_exact_gap` alias of
`bottom_uniform_lower_residual`; hence uniform `1 / 2` stays OPEN.
-/

namespace Door3TopEdgeUniformChain

open Complex Real Set Topology

theorem bottom_uniform_exist_lower_residual_form :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ Set.Icc (-10 : ℝ) (10 : ℝ),
        ε ≤ ‖CentralCoverAssembly.xiShiftedEntire
          ((x : ℂ) - Complex.I * (((1 / 2 : ℝ)) : ℂ))‖ := by
  obtain ⟨ε, hε, h⟩ :=
    Door3TopEdgeUniformLower.bottom_uniform_exist_lower_on_Icc10
  refine ⟨ε, hε, ?_⟩
  intro x hx
  have hlo := h x hx
  have heq := Door3TopEdgeUniformLower.bottom_point_form_eq x
  rw [heq] at hlo
  exact hlo

def uniform_half_exact_gap : Prop :=
  Door3TopEdgeNeeds.bottom_uniform_lower_residual

end Door3TopEdgeUniformChain
