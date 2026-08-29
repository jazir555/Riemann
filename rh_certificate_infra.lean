import Mathlib

open Complex Real Set Topology

noncomputable section

namespace CellProofEngine

/-- A 2D complex rectangle $[x_0, x_1] \times [y_0, y_1]$. -/
structure Rect2D where
  x0 : ℝ
  x1 : ℝ
  y0 : ℝ
  y1 : ℝ
  hx : x0 < x1
  hy : y0 < y1

namespace Rect2D

/-- Set membership for a point $z \in \mathbb{C}$ in a 2D rectangle. -/
def mem (R : Rect2D) (z : ℂ) : Prop :=
  R.x0 ≤ z.re ∧ z.re ≤ R.x1 ∧ R.y0 ≤ z.im ∧ z.im ≤ R.y1

/-- The geometric center point of the rectangle $z_0 = x_{mid} + i \cdot y_{mid}$. -/
def center (R : Rect2D) : ℂ :=
  ((R.x0 + R.x1) / 2 : ℂ) + I * ((R.y0 + R.y1) / 2 : ℂ)

/-- Half-width of the real span. -/
def dx (R : Rect2D) : ℝ := (R.x1 - R.x0) / 2

/-- Half-width of the imaginary span. -/
def dy (R : Rect2D) : ℝ := (R.y1 - R.y0) / 2

/-- Maximum distance (radius) from the center to any point in the box. -/
def radius (R : Rect2D) : ℝ :=
  Real.sqrt (R.dx ^ 2 + R.dy ^ 2)

theorem dx_pos (R : Rect2D) : 0 < R.dx := by
  dsimp [dx]; linarith [R.hx]

theorem dy_pos (R : Rect2D) : 0 < R.dy := by
  dsimp [dy]; linarith [R.hy]

theorem radius_pos (R : Rect2D) : 0 < R.radius := by
  dsimp [radius]
  apply Real.sqrt_pos.mpr
  have h1 : 0 < R.dx ^ 2 := sq_pos_of_pos R.dx_pos
  have h2 : 0 ≤ R.dy ^ 2 := sq_nonneg _
  linarith

/-- **Lemma 1**: Every point $z \in R$ satisfies $\|z - z_0\| \le \text{radius}(R)$. -/
theorem norm_sub_center_le_radius (R : Rect2D) {z : ℂ} (hz : R.mem z) :
    ‖z - R.center‖ ≤ R.radius := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hz
  have hcre : (z - R.center).re = z.re - (R.x0 + R.x1) / 2 := by
    simp [center]
  have hcim : (z - R.center).im = z.im - (R.y0 + R.y1) / 2 := by
    simp [center]
  have hre : |(z - R.center).re| ≤ R.dx := by
    rw [hcre, abs_le]
    dsimp only [dx]
    constructor <;> linarith
  have him : |(z - R.center).im| ≤ R.dy := by
    rw [hcim, abs_le]
    dsimp only [dy]
    constructor <;> linarith
  have hsq_re : (z - R.center).re ^ 2 ≤ R.dx ^ 2 := by
    rw [← abs_of_nonneg R.dx_pos.le] at hre
    exact sq_le_sq.mpr hre
  have hsq_im : (z - R.center).im ^ 2 ≤ R.dy ^ 2 := by
    rw [← abs_of_nonneg R.dy_pos.le] at him
    exact sq_le_sq.mpr him
  have hnorm_sq : ‖z - R.center‖ ^ 2 = (z - R.center).re ^ 2 + (z - R.center).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, pow_two, pow_two]
  have h_sum : ‖z - R.center‖ ^ 2 ≤ R.dx ^ 2 + R.dy ^ 2 := by
    rw [hnorm_sq]
    linarith
  dsimp [radius]
  rw [← Real.sqrt_le_sqrt_iff (by positivity)] at h_sum
  rw [Real.sqrt_sq (norm_nonneg _)] at h_sum
  exact h_sum

end Rect2D

/-- **Lemma 2**: Reverse triangle inequality for complex values. -/
theorem norm_ge_center_sub_diff (w w0 : ℂ) :
    ‖w0‖ - ‖w - w0‖ ≤ ‖w‖ := by
  have h := norm_sub_norm_le w0 w
  rw [norm_sub_rev w0 w] at h
  linarith

/-- **Lemma 3**: Lipschitz bound on a convex set from a derivative bound. -/
theorem norm_image_sub_le_of_deriv_bound {f : ℂ → ℂ} {s : Set ℂ} (hs : Convex ℝ s)
    {M : ℝ} (hd : ∀ z ∈ s, DifferentiableAt ℂ f z)
    (hM : ∀ z ∈ s, ‖deriv f z‖ ≤ M) {z z0 : ℂ} (hz : z ∈ s) (hz0 : z0 ∈ s) :
    ‖f z - f z0‖ ≤ M * ‖z - z0‖ := by
  exact Convex.norm_image_sub_le_of_norm_deriv_le (fun x hx => hd x hx) hM hs hz0 hz

/-- As a Set in $\mathbb{C}$, `R` is convex. -/
theorem rect2D_convex (R : Rect2D) : Convex ℝ {z : ℂ | R.mem z} := by
  intro z1 hz1 z2 hz2 a b ha hb hab
  simp only [Rect2D.mem, Set.mem_ofPred_eq] at hz1 hz2 ⊢
  obtain ⟨h11, h12, h13, h14⟩ := hz1
  obtain ⟨h21, h22, h23, h24⟩ := hz2
  have hre : (a • z1 + b • z2).re = a * z1.re + b * z2.re := by
    simp [Complex.add_re]
  have him : (a • z1 + b • z2).im = a * z1.im + b * z2.im := by
    simp [Complex.add_im]
  have hx0 : a * R.x0 + b * R.x0 = R.x0 := by linear_combination R.x0 * hab
  have hx1 : a * R.x1 + b * R.x1 = R.x1 := by linear_combination R.x1 * hab
  have hy0 : a * R.y0 + b * R.y0 = R.y0 := by linear_combination R.y0 * hab
  have hy1 : a * R.y1 + b * R.y1 = R.y1 := by linear_combination R.y1 * hab
  rw [hre, him]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h11 ha, mul_le_mul_of_nonneg_left h21 hb]
  · linarith [mul_le_mul_of_nonneg_left h12 ha, mul_le_mul_of_nonneg_left h22 hb]
  · linarith [mul_le_mul_of_nonneg_left h13 ha, mul_le_mul_of_nonneg_left h23 hb]
  · linarith [mul_le_mul_of_nonneg_left h14 ha, mul_le_mul_of_nonneg_left h24 hb]

theorem center_mem_rect2D (R : Rect2D) : R.mem R.center := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Rect2D.center]; ring_nf; linarith [R.hx]
  · simp [Rect2D.center]; ring_nf; linarith [R.hx]
  · simp [Rect2D.center]; ring_nf; linarith [R.hy]
  · simp [Rect2D.center]; ring_nf; linarith [R.hy]

/-- **Master Theorem**: given an entire function with a derivative bound over $R$ and a
center evaluation $\|f(z_0)\| \ge \varepsilon_0$, then for every $z \in R$,
$\|f(z)\| \ge \varepsilon_0 - M \cdot \text{radius}(R)$. -/
theorem cell_lower_bound_from_center_and_deriv
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (R : Rect2D) (M : ℝ) (hM : ∀ z, R.mem z → ‖deriv f z‖ ≤ M)
    (ε0 : ℝ) (h_center : ε0 ≤ ‖f R.center‖) :
    ∀ z : ℂ, R.mem z → (ε0 - M * R.radius) ≤ ‖f z‖ := by
  intro z hz
  have h_convex := rect2D_convex R
  have h_center_mem := center_mem_rect2D R
  have h_diff_at : ∀ w ∈ {w : ℂ | R.mem w}, DifferentiableAt ℂ f w := fun w _ => hf w
  have h_lip := norm_image_sub_le_of_deriv_bound h_convex h_diff_at
    (fun w hw => hM w hw) hz h_center_mem
  have h_rad := R.norm_sub_center_le_radius hz
  have h_M_nonneg : 0 ≤ M := by
    have h_deriv_bound := hM R.center h_center_mem
    exact le_trans (norm_nonneg _) h_deriv_bound
  have h_dist_bound : ‖f z - f R.center‖ ≤ M * R.radius := by
    calc ‖f z - f R.center‖ ≤ M * ‖z - R.center‖ := h_lip
      _ ≤ M * R.radius := mul_le_mul_of_nonneg_left h_rad h_M_nonneg
  have h_rev := norm_ge_center_sub_diff (f z) (f R.center)
  linarith

end CellProofEngine

open Complex Real Topology Set

noncomputable section

namespace TailProofEngine

/-- Shifted complex coordinate $s(z) = 1/2 + i z$. -/
def shiftedS (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) + I * z

/-- Component 1: Polynomial prefactor $f_{poly}(s) = \frac{1}{2} s (s - 1)$. -/
def fPoly (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1)

/-- Component 2: Pi-power prefactor $f_{\pi}(s) = \pi^{-s/2}$. -/
def fPi (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-(s / 2))

/-- Component 3: Gamma factor $f_{\Gamma}(s) = \Gamma(s/2)$. -/
def fGamma (s : ℂ) : ℂ :=
  Complex.Gamma (s / 2)

/-- Component 4: Riemann Zeta factor $f_{\zeta}(s) = \zeta(s)$. -/
def fZeta (s : ℂ) : ℂ :=
  riemannZeta s

/-- Definition of classical $\xi(s)$ as the product of the four components. -/
def classicalXi (s : ℂ) : ℂ :=
  fPoly s * fPi s * fGamma s * fZeta s

/-- Shifted $\xi$ function $\xi_{shift}(z) = \xi(1/2 + i z)$. -/
def xiShifted (z : ℂ) : ℂ :=
  classicalXi (shiftedS z)

/-- **Lemma 1**: Norm of shifted $\xi(z)$ equals the product of the norms of its 4 components. -/
theorem norm_xiShifted_eq_prod_norms (z : ℂ) :
    ‖xiShifted z‖ = ‖fPoly (shiftedS z)‖ * ‖fPi (shiftedS z)‖ * ‖fGamma (shiftedS z)‖ *
      ‖fZeta (shiftedS z)‖ := by
  dsimp [xiShifted, classicalXi]
  rw [norm_mul, norm_mul, norm_mul]

/-- **Lemma 2**: Product lower bound rule for four non-negative real quantities. -/
theorem prod_four_ge_of_ge {a b c d A B C D : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hA : A ≤ a) (hB : B ≤ b) (hC : C ≤ c) (hD : D ≤ d)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C) (hD0 : 0 ≤ D) :
    A * B * C * D ≤ a * b * c * d := by
  have hAB : A * B ≤ a * b := mul_le_mul hA hB hB0 ha
  have hAB0 : 0 ≤ A * B := mul_nonneg hA0 hB0
  have hab0 : 0 ≤ a * b := mul_nonneg ha hb
  have hABC : A * B * C ≤ a * b * c := mul_le_mul hAB hC hC0 hab0
  have hABC0 : 0 ≤ A * B * C := mul_nonneg hAB0 hC0
  have habc0 : 0 ≤ a * b * c := mul_nonneg hab0 hc
  exact mul_le_mul hABC hD hD0 habc0

/-- **Lemma 3**: Combining a polynomial/constant prefactor bound with an exponential Gamma bound. -/
theorem exp_decay_mul_const_le (C_pre C_gam α x : ℝ)
    (h_pre : 0 ≤ C_pre) (h_gam : 0 ≤ C_gam) :
    (C_pre * C_gam) * Real.exp (-α * x) = C_pre * (C_gam * Real.exp (-α * x)) := by
  ring

/-- **Master Tail Reduction Theorem**:
If the four component functions satisfy explicit lower bounds over $x \in (40, \infty)$,
then for $c_{tail} = C_{poly} \cdot C_{\pi} \cdot C_{\Gamma} \cdot C_{\zeta}$,
$\|\xi(1/2 + ix + iy)\| \ge c_{tail} \cdot e^{-\alpha x}$.
-/
theorem tail_lower_bound_from_component_bounds
    (X_min : ℝ) (z : ℂ) (hz_x : X_min < |z.re|)
    (C_poly C_pi C_gam C_zeta α : ℝ)
    (hC_poly0 : 0 ≤ C_poly) (hC_pi0 : 0 ≤ C_pi) (hC_gam0 : 0 ≤ C_gam) (hC_zeta0 : 0 ≤ C_zeta)
    (h_poly : C_poly ≤ ‖fPoly (shiftedS z)‖)
    (h_pi   : C_pi ≤ ‖fPi (shiftedS z)‖)
    (h_gam  : C_gam * Real.exp (-α * |z.re|) ≤ ‖fGamma (shiftedS z)‖)
    (h_zeta : C_zeta ≤ ‖fZeta (shiftedS z)‖) :
    (C_poly * C_pi * C_gam * C_zeta) * Real.exp (-α * |z.re|) ≤ ‖xiShifted z‖ := by
  have h_exp_pos : 0 ≤ Real.exp (-α * |z.re|) := le_of_lt (Real.exp_pos _)
  have h_gam_bound_pos : 0 ≤ C_gam * Real.exp (-α * |z.re|) := mul_nonneg hC_gam0 h_exp_pos
  have h_prod := prod_four_ge_of_ge
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    h_poly h_pi h_gam h_zeta
    hC_poly0 hC_pi0 h_gam_bound_pos hC_zeta0
  rw [← norm_xiShifted_eq_prod_norms] at h_prod
  have h_algebra : C_poly * C_pi * (C_gam * Real.exp (-α * |z.re|)) * C_zeta =
      (C_poly * C_pi * C_gam * C_zeta) * Real.exp (-α * |z.re|) := by ring
  rwa [h_algebra] at h_prod

end TailProofEngine

open Complex Real Topology Set

noncomputable section

namespace BoundaryProofEngine

/-- Line segment evaluation $g(y) = f(x + i y)$ for a fixed real height $x$. -/
def lineEval (f : ℂ → ℂ) (x : ℝ) (y : ℝ) : ℂ :=
  f ((x : ℂ) + I * (y : ℂ))

/-- **Theorem 1**: If $f(x) \neq 0$ at height $x$ with $\|f(x)\| \ge \varepsilon_0 > 0$ and
$\|f'\| \le M_1$ on the vertical strip $[0, \eta]$, then for all
$y \in (0, \min(\eta, \varepsilon_0 / M_1))$, $f(x + i y) \neq 0$. -/
theorem boundary_strip_nonvanishing_of_nonzero_base
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ)
    (ε0 M1 η : ℝ) (hε0 : 0 < ε0) (hM1 : 0 < M1) (hη : 0 < η)
    (h_base : ε0 ≤ ‖f (x : ℂ)‖)
    (h_deriv : ∀ y ∈ Icc 0 η, ‖deriv f ((x : ℂ) + I * (y : ℂ))‖ ≤ M1)
    (y : ℝ) (hy_pos : 0 < y) (hy_lt : y < η) (hy_margin : y < ε0 / M1) :
    f ((x : ℂ) + I * (y : ℂ)) ≠ 0 := by
  have hy_icc : y ∈ Icc 0 η := ⟨le_of_lt hy_pos, le_of_lt hy_lt⟩
  have h0_icc : (0 : ℝ) ∈ Icc 0 η := ⟨le_rfl, le_of_lt hη⟩
  set z0 : ℂ := (x : ℂ) with hz0def
  set z : ℂ := (x : ℂ) + I * (y : ℂ) with hzdef
  have h_seg : Convex ℝ (Icc 0 η) := convex_Icc 0 η
  have h_dist : ‖z - z0‖ = y := by
    have hzz : z - z0 = I * (y : ℂ) := by simp only [hzdef, hz0def]; ring
    rw [hzz, norm_mul, Complex.norm_I, one_mul, Complex.norm_of_nonneg hy_pos.le]
  have h_lip : ‖f z - f z0‖ ≤ M1 * y := by
    have h_convex : Convex ℝ {w : ℂ | ∃ t ∈ Icc 0 η, w = (x : ℂ) + I * (t : ℂ)} := by
      intro w1 ⟨t1, ht1, hw1⟩ w2 ⟨t2, ht2, hw2⟩ a b ha hb hab
      subst hw1 hw2
      refine ⟨a * t1 + b * t2, h_seg ht1 ht2 ha hb hab, ?_⟩
      have hab' : (a : ℂ) + (b : ℂ) = 1 := by
        rw [← Complex.ofReal_add, hab, Complex.ofReal_one]
      simp only [Complex.real_smul]
      push_cast
      linear_combination (x : ℂ) * hab'
    have h_mem_z : z ∈ {w : ℂ | ∃ t ∈ Icc 0 η, w = (x : ℂ) + I * (t : ℂ)} := by
      refine ⟨y, hy_icc, ?_⟩
      simp only [hzdef]
    have h_mem_z0 : z0 ∈ {w : ℂ | ∃ t ∈ Icc 0 η, w = (x : ℂ) + I * (t : ℂ)} := by
      refine ⟨0, h0_icc, ?_⟩
      simp only [hz0def, Complex.ofReal_zero, mul_zero, add_zero]
    have h_deriv_bound : ∀ w ∈ {w : ℂ | ∃ t ∈ Icc 0 η, w = (x : ℂ) + I * (t : ℂ)},
        ‖deriv f w‖ ≤ M1 := by
      rintro w ⟨t, ht, rfl⟩
      exact h_deriv t ht
    have hres := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (fun w _ => hf w)
      h_deriv_bound h_convex h_mem_z0 h_mem_z
    rwa [h_dist] at hres
  have h_lower : ε0 - M1 * y ≤ ‖f z‖ := by
    have h_rev := norm_sub_norm_le (f z0) (f z)
    rw [norm_sub_rev (f z0) (f z)] at h_rev
    linarith
  have h_pos_margin : 0 < ε0 - M1 * y := by
    have h := (lt_div_iff₀ hM1).mp hy_margin
    linarith
  have h_norm_pos : 0 < ‖f z‖ := lt_of_lt_of_le h_pos_margin h_lower
  exact norm_pos_iff.mp h_norm_pos

/-! ### Second-order Taylor estimate with the sharp `1/2` factor

Mathlib only provides the *first-order* mean-value inequality
(`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`,
`Convex.norm_image_sub_le_of_norm_deriv_le`), which applied to `deriv f` yields the
remainder bound `M₂ · y²` — off by a factor of `2` from the sharp Taylor constant.

The sharp `½ M₂ y²` is recovered below from the *fencing* theorem
`image_norm_le_of_norm_deriv_right_le_deriv_boundary`: the first-order Taylor
remainder `F t = f(x + i t) - f(x) - t · i · f'(x)` satisfies `F 0 = 0` and
`‖F' t‖ ≤ M₂ t`, so comparing with `B t = ½ M₂ t²` (which has `B 0 = 0` and
`B' t = M₂ t`) gives `‖F t‖ ≤ ½ M₂ t²`.  This is the integral form of Taylor's
theorem in differential-inequality disguise.
-/

/-- `t ↦ (t : ℂ)` has derivative `1` as a map `ℝ → ℂ`. -/
lemma hasDerivAt_ofReal_toComplex (t : ℝ) : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := by
  simpa [Complex.real_smul] using (hasDerivAt_id t).smul_const (1 : ℂ)

/-- The vertical line `t ↦ x + i t` has derivative `I`. -/
lemma hasDerivAt_vertLine (x t : ℝ) :
    HasDerivAt (fun u : ℝ => (x : ℂ) + I * (u : ℂ)) I t := by
  have h := ((hasDerivAt_id t).smul_const I).const_add ((x : ℂ))
  simpa [Complex.real_smul, mul_comm] using h

/-- Chain rule along the vertical line `t ↦ x + i t`: if `g` is holomorphic then
`t ↦ g (x + i t)` has derivative `i · g' (x + i t)`. -/
lemma hasDerivAt_comp_vertLine {g : ℂ → ℂ} (hg : Differentiable ℂ g) (x t : ℝ) :
    HasDerivAt (fun u : ℝ => g ((x : ℂ) + I * (u : ℂ)))
      (I * deriv g ((x : ℂ) + I * (t : ℂ))) t := by
  have hgat : HasDerivAt g (deriv g ((x : ℂ) + I * (t : ℂ))) ((x : ℂ) + I * (t : ℂ)) :=
    (hg _).hasDerivAt
  have hcomp := hgat.scomp t (hasDerivAt_vertLine x t)
  simpa [Function.comp_def, smul_eq_mul] using hcomp

/-- **Second-order Taylor estimate with the sharp `1/2` factor**, along a vertical
segment.  If `‖f''‖ ≤ M₂` on `{x + i t : t ∈ [0, η]}` and `0 < y ≤ η`, then
`‖f(x + iy) - (f(x) + f'(x) · (iy))‖ ≤ ½ M₂ y²`. -/
lemma norm_sub_taylor_le_half_mul_sq
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf' : Differentiable ℂ (deriv f))
    (x : ℝ) {M2 η : ℝ}
    (h_deriv2 : ∀ t ∈ Icc (0 : ℝ) η, ‖deriv (deriv f) ((x : ℂ) + I * (t : ℂ))‖ ≤ M2)
    {y : ℝ} (hy_pos : 0 < y) (hy_le : y ≤ η) :
    ‖f ((x : ℂ) + I * (y : ℂ)) - (f (x : ℂ) + deriv f (x : ℂ) * (I * (y : ℂ)))‖
      ≤ 1 / 2 * M2 * y ^ 2 := by
  have hsub : Icc (0 : ℝ) y ⊆ Icc (0 : ℝ) η := Icc_subset_Icc le_rfl hy_le
  -- derivative of `t ↦ f'(x + i t)`
  have hG : ∀ t : ℝ, HasDerivAt (fun u : ℝ => deriv f ((x : ℂ) + I * (u : ℂ)))
      (I * deriv (deriv f) ((x : ℂ) + I * (t : ℂ))) t := fun t =>
    hasDerivAt_comp_vertLine hf' x t
  -- derivative of the first-order Taylor remainder
  have hF : ∀ t : ℝ, HasDerivAt
      (fun u : ℝ => f ((x : ℂ) + I * (u : ℂ)) - f (x : ℂ) - (u : ℂ) * (I * deriv f (x : ℂ)))
      (I * deriv f ((x : ℂ) + I * (t : ℂ)) - I * deriv f (x : ℂ)) t := by
    intro t
    have h1 := (hasDerivAt_comp_vertLine hf x t).sub_const (f (x : ℂ))
    have h2 := (hasDerivAt_ofReal_toComplex t).mul_const (I * deriv f (x : ℂ))
    have h3 := h1.sub h2
    have hrw : I * deriv f ((x : ℂ) + I * (t : ℂ)) - I * deriv f (x : ℂ)
        = I * deriv f ((x : ℂ) + I * (t : ℂ)) - 1 * (I * deriv f (x : ℂ)) := by ring
    rw [hrw]
    exact h3
  -- Step A: `f'` is `M₂`-Lipschitz along the segment.
  have hA : ∀ t ∈ Icc (0 : ℝ) y,
      ‖deriv f ((x : ℂ) + I * (t : ℂ)) - deriv f (x : ℂ)‖ ≤ M2 * t := by
    have hseg := norm_image_sub_le_of_norm_deriv_right_le_segment
      (f := fun u : ℝ => deriv f ((x : ℂ) + I * (u : ℂ)))
      (f' := fun u : ℝ => I * deriv (deriv f) ((x : ℂ) + I * (u : ℂ)))
      (C := M2) (a := 0) (b := y)
      (fun t _ => (hG t).continuousAt.continuousWithinAt)
      (fun t _ => (hG t).hasDerivWithinAt)
      (fun t ht => by
        rw [norm_mul, Complex.norm_I, one_mul]
        exact h_deriv2 t (hsub (Ico_subset_Icc_self ht)))
    intro t ht
    have h := hseg t ht
    rw [Complex.ofReal_zero, mul_zero, add_zero, sub_zero] at h
    exact h
  -- Step B: fence the remainder against `B t = ½ M₂ t²`.
  have hBderiv : ∀ t : ℝ, HasDerivAt (fun u : ℝ => 1 / 2 * M2 * u ^ 2) (M2 * t) t := by
    intro t
    have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h := hsq.const_mul (1 / 2 * M2)
    have hrw : 1 / 2 * M2 * (2 * t) = M2 * t := by ring
    rw [hrw] at h
    exact h
  have hzero : ‖f ((x : ℂ) + I * ((0 : ℝ) : ℂ)) - f (x : ℂ)
      - ((0 : ℝ) : ℂ) * (I * deriv f (x : ℂ))‖ ≤ 1 / 2 * M2 * (0 : ℝ) ^ 2 := by
    simp
  have hfence := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun u : ℝ => f ((x : ℂ) + I * (u : ℂ)) - f (x : ℂ) - (u : ℂ) * (I * deriv f (x : ℂ)))
    (f' := fun u : ℝ => I * deriv f ((x : ℂ) + I * (u : ℂ)) - I * deriv f (x : ℂ))
    (B := fun u : ℝ => 1 / 2 * M2 * u ^ 2) (B' := fun u : ℝ => M2 * u)
    (a := 0) (b := y)
    (fun t _ => (hF t).continuousAt.continuousWithinAt)
    (fun t _ => (hF t).hasDerivWithinAt)
    hzero hBderiv
    (fun t ht => by
      have hle := hA t (Ico_subset_Icc_self ht)
      calc ‖I * deriv f ((x : ℂ) + I * (t : ℂ)) - I * deriv f (x : ℂ)‖
          = ‖deriv f ((x : ℂ) + I * (t : ℂ)) - deriv f (x : ℂ)‖ := by
            rw [← mul_sub, norm_mul, Complex.norm_I, one_mul]
        _ ≤ M2 * t := hle)
  have hres := hfence (⟨hy_pos.le, le_rfl⟩ : y ∈ Icc (0 : ℝ) y)
  have heq : f ((x : ℂ) + I * (y : ℂ)) - (f (x : ℂ) + deriv f (x : ℂ) * (I * (y : ℂ)))
      = f ((x : ℂ) + I * (y : ℂ)) - f (x : ℂ) - (y : ℂ) * (I * deriv f (x : ℂ)) := by
    ring
  rw [heq]
  exact hres

/-- **Theorem 2**: If $f(x) = 0$ with a simple zero ($d_0 = \|f'(x)\| > 0$) and
$\|f''\| \le M_2$ on $[0, \eta]$, then for all $y \in (0, \min(\eta, 2 d_0 / M_2))$,
$f(x + i y) \neq 0$. -/
theorem boundary_strip_nonvanishing_of_simple_zero_base
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf' : Differentiable ℂ (deriv f)) (x : ℝ)
    (d0 M2 η : ℝ) (hd0 : 0 < d0) (hM2 : 0 < M2) (hη : 0 < η)
    (h_zero : f (x : ℂ) = 0)
    (h_simple : d0 ≤ ‖deriv f (x : ℂ)‖)
    (h_deriv2 : ∀ y ∈ Icc 0 η, ‖deriv (deriv f) ((x : ℂ) + I * (y : ℂ))‖ ≤ M2)
    (y : ℝ) (hy_pos : 0 < y) (hy_lt : y < η) (hy_margin : y < 2 * d0 / M2) :
    f ((x : ℂ) + I * (y : ℂ)) ≠ 0 := by
  set z0 : ℂ := (x : ℂ) with hz0def
  set z : ℂ := (x : ℂ) + I * (y : ℂ) with hzdef
  have hy_icc : y ∈ Icc 0 η := ⟨le_of_lt hy_pos, le_of_lt hy_lt⟩
  have h0_icc : (0 : ℝ) ∈ Icc 0 η := ⟨le_rfl, le_of_lt hη⟩
  have h_dist : ‖z - z0‖ = y := by
    have hzz : z - z0 = I * (y : ℂ) := by simp only [hzdef, hz0def]; ring
    rw [hzz, norm_mul, Complex.norm_I, one_mul, Complex.norm_of_nonneg hy_pos.le]
  -- Sharp second-order Taylor bound (factor `½`), via the fencing argument above.
  have h_taylor : ‖f z - (f z0 + deriv f z0 * (z - z0))‖ ≤ (1 / 2) * M2 * y ^ 2 := by
    have hzz : z - z0 = I * (y : ℂ) := by simp only [hzdef, hz0def]; ring
    have hz' : z = (x : ℂ) + I * (y : ℂ) := hzdef
    have hz0' : z0 = (x : ℂ) := hz0def
    rw [hzz, hz', hz0']
    exact norm_sub_taylor_le_half_mul_sq hf hf' x h_deriv2 hy_pos hy_lt.le
  rw [h_zero, zero_add] at h_taylor
  have h_lin_norm : ‖deriv f z0 * (z - z0)‖ = ‖deriv f z0‖ * y := by
    rw [norm_mul, h_dist]
  have h_lin_lower : d0 * y ≤ ‖deriv f z0 * (z - z0)‖ := by
    rw [h_lin_norm]
    exact mul_le_mul_of_nonneg_right h_simple (le_of_lt hy_pos)
  have h_f_lower : d0 * y - (1 / 2) * M2 * y ^ 2 ≤ ‖f z‖ := by
    have h_rev := norm_sub_norm_le (deriv f z0 * (z - z0)) (f z)
    rw [norm_sub_rev (deriv f z0 * (z - z0)) (f z)] at h_rev
    linarith
  have h_factor : d0 * y - (1 / 2) * M2 * y ^ 2 = y * (d0 - (1 / 2) * M2 * y) := by ring
  rw [h_factor] at h_f_lower
  have h_inner_pos : 0 < d0 - (1 / 2) * M2 * y := by
    have h := (lt_div_iff₀ hM2).mp hy_margin
    linarith
  have h_prod_pos : 0 < y * (d0 - (1 / 2) * M2 * y) := mul_pos hy_pos h_inner_pos
  have h_norm_pos : 0 < ‖f z‖ := lt_of_lt_of_le h_prod_pos h_f_lower
  exact norm_pos_iff.mp h_norm_pos

/-- **Theorem 3**: If $f(x + i \cdot 0.5) \neq 0$ with $\|f\| \ge \varepsilon_{top}$ and
$\|f'\| \le M_1$, then non-vanishing holds in $y \in (0.5 - \varepsilon_{top}/M_1, 0.5)$. -/
theorem upper_boundary_nonvanishing_from_outer_bound
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ)
    (ε_top M1 : ℝ) (hε : 0 < ε_top) (hM1 : 0 < M1)
    (h_top : ε_top ≤ ‖f ((x : ℂ) + I * (1 / 2 : ℂ))‖)
    (h_deriv : ∀ y ∈ Icc (1 / 2 - ε_top / M1) (1 / 2), ‖deriv f ((x : ℂ) + I * (y : ℂ))‖ ≤ M1)
    (y : ℝ) (hy_low : 1 / 2 - ε_top / M1 < y) (hy_top : y ≤ 1 / 2) :
    f ((x : ℂ) + I * (y : ℂ)) ≠ 0 := by
  set z_top : ℂ := (x : ℂ) + I * (1 / 2 : ℂ) with hztopdef
  set z : ℂ := (x : ℂ) + I * (y : ℂ) with hzdef
  have h_dist : ‖z_top - z‖ = 1 / 2 - y := by
    have hzz : z_top - z = I * ((1 / 2 - y : ℝ) : ℂ) := by
      simp only [hztopdef, hzdef]; push_cast; ring
    rw [hzz, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - y)]
  have h_lip : ‖f z_top - f z‖ ≤ M1 * (1 / 2 - y) := by
    have h_convex : Convex ℝ {w : ℂ | ∃ t ∈ Icc (1 / 2 - ε_top / M1) (1 / 2),
        w = (x : ℂ) + I * (t : ℂ)} := by
      intro w1 ⟨t1, ht1, hw1⟩ w2 ⟨t2, ht2, hw2⟩ a b ha hb hab
      subst hw1 hw2
      refine ⟨a * t1 + b * t2,
        (convex_Icc (1 / 2 - ε_top / M1) (1 / 2)) ht1 ht2 ha hb hab, ?_⟩
      have hab' : (a : ℂ) + (b : ℂ) = 1 := by
        rw [← Complex.ofReal_add, hab, Complex.ofReal_one]
      simp only [Complex.real_smul]
      push_cast
      linear_combination (x : ℂ) * hab'
    have h_mem_ztop : z_top ∈ {w : ℂ | ∃ t ∈ Icc (1 / 2 - ε_top / M1) (1 / 2),
        w = (x : ℂ) + I * (t : ℂ)} := by
      refine ⟨(1 / 2 : ℝ), ⟨by linarith [div_pos hε hM1], le_rfl⟩, ?_⟩
      simp only [hztopdef]
      push_cast
      ring
    have h_mem_z : z ∈ {w : ℂ | ∃ t ∈ Icc (1 / 2 - ε_top / M1) (1 / 2),
        w = (x : ℂ) + I * (t : ℂ)} := by
      refine ⟨y, ⟨le_of_lt hy_low, hy_top⟩, ?_⟩
      simp only [hzdef]
    have h_deriv_bound : ∀ w ∈ {w : ℂ | ∃ t ∈ Icc (1 / 2 - ε_top / M1) (1 / 2),
        w = (x : ℂ) + I * (t : ℂ)}, ‖deriv f w‖ ≤ M1 := by
      rintro w ⟨t, ht, rfl⟩
      exact h_deriv t ht
    have hres := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (fun w _ => hf w)
      h_deriv_bound h_convex h_mem_z h_mem_ztop
    rwa [h_dist] at hres
  have h_lower : ε_top - M1 * (1 / 2 - y) ≤ ‖f z‖ := by
    have h_rev := norm_sub_norm_le (f z_top) (f z)
    linarith
  have h_pos_margin : 0 < ε_top - M1 * (1 / 2 - y) := by
    have h1 : 1 / 2 - y < ε_top / M1 := by linarith
    have h2 := (lt_div_iff₀ hM1).mp h1
    linarith
  have h_norm_pos : 0 < ‖f z‖ := lt_of_lt_of_le h_pos_margin h_lower
  exact norm_pos_iff.mp h_norm_pos

end BoundaryProofEngine
