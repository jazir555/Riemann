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
