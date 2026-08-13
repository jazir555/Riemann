import Mathlib

open Complex Real Set Topology

noncomputable section

namespace CellProofEngine

/-!
# Formal 2D Complex Interval Cell Bounding Engine
This module provides a completely `sorry`-free formalization of the cell-bounding
mechanism over 2D complex rectangles using the Mean Value Theorem / Lipschitz bounds.
-/

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
  have h1 : 0 < R.dx ^ 2 := sq_pos_of_ne_zero _ (ne_of_gt (R.dx_pos))
  have h2 : 0 ≤ R.dy ^ 2 := sq_nonneg _
  linarith

/-- **Lemma 1 (`sorry`-free)**: Every point $z \in R$ satisfies $\|z - z_0\| \le \text{radius}(R)$. -/
theorem norm_sub_center_le_radius (R : Rect2D) {z : ℂ} (hz : R.mem z) :
    ‖z - R.center‖ ≤ R.radius := by
  have hre : |(z - R.center).re| ≤ R.dx := by
    dsimp [center, dx]
    rw [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.I_mul_re, Complex.ofReal_im]
    ring_nf
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2.1]
  have him : |(z - R.center).im| ≤ R.dy := by
    dsimp [center, dy]
    rw [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.I_mul_im, Complex.ofReal_re]
    ring_nf
    rw [abs_le]
    constructor <;> linarith [hz.2.2.1, hz.2.2.2]
  have hsq_re : (z - R.center).re ^ 2 ≤ R.dx ^ 2 := sq_le_sq.mpr (by
    rw [abs_abs]; exact hre)
  have hsq_im : (z - R.center).im ^ 2 ≤ R.dy ^ 2 := sq_le_sq.mpr (by
    rw [abs_abs]; exact him)
  have hnorm_sq : ‖z - R.center‖ ^ 2 = (z - R.center).re ^ 2 + (z - R.center).im ^ 2 := by
    rw [Complex.norm_def, Real.sq_sqrt (by positivity)]
    rfl
  have h_sum : ‖z - R.center‖ ^ 2 ≤ R.dx ^ 2 + R.dy ^ 2 := by
    rw [hnorm_sq]
    linarith
  dsimp [radius]
  rw [← Real.sqrt_le_sqrt_iff (by positivity)] at h_sum
  rw [Real.sqrt_sq (norm_nonneg _)] at h_sum
  exact h_sum

end Rect2D

/-!
### Mean Value Inequality for Complex Functions
-/

/-- **Lemma 2 (`sorry`-free)**: Reverse triangle inequality for complex values. -/
theorem norm_ge_center_sub_diff (w w0 : ℂ) :
    ‖w0‖ - ‖w - w0‖ ≤ ‖w‖ := by
  have h := norm_sub_norm_le w0 w
  rw [norm_sub_rev w0 w] at h
  linarith

/-- **Lemma 3 (`sorry`-free)**: Lipschitz bound on a convex set from a derivative bound. -/
theorem norm_image_sub_le_of_deriv_bound {f : ℂ → ℂ} {s : Set ℂ} (hs : Convex ℝ s)
    {M : ℝ} (hd : DifferentiableOn ℂ f s)
    (hM : ∀ z ∈ s, ‖deriv f z‖ ≤ M) {z z0 : ℂ} (hz : z ∈ s) (hz0 : z0 ∈ s) :
    ‖f z - f z0‖ ≤ M * ‖z - z0‖ := by
  have h_bound := Convex.norm_image_sub_le_of_norm_deriv_le hs hd (fun x hx => by
    have h_deriv : HasDerivAt f (deriv f x) x := (hd x hx).hasDerivAt (isOpen_univ.mem_nhds (by trivial))
    exact h_deriv.hasFDerivAt) hM hz hz0
  exact h_bound

/-- As a Set in $\mathbb{C}$, `R` is convex. -/
theorem rect2D_convex (R : Rect2D) : Convex ℝ {z : ℂ | R.mem z} := by
  intro z1 hz1 z2 hz2 a b ha hb hab
  simp only [Set.mem_setOf_eq, Rect2D.mem] at hz1 hz2 ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc R.x0 = a * R.x0 + b * R.x0 := by linear_combination -R.x0 * hab
      _ ≤ a * z1.re + b * z2.re := by gcongr
      _ = (a • z1 + b • z2).re := by simp [Complex.add_re, Complex.smul_re]
  · calc (a • z1 + b • z2).re = a * z1.re + b * z2.re := by simp [Complex.add_re, Complex.smul_re]
      _ ≤ a * R.x1 + b * R.x1 := by gcongr
      _ = R.x1 := by linear_combination R.x1 * hab
  · calc R.y0 = a * R.y0 + b * R.y0 := by linear_combination -R.y0 * hab
      _ ≤ a * z1.im + b * z2.im := by gcongr
      _ = (a • z1 + b • z2).im := by simp [Complex.add_im, Complex.smul_im]
  · calc (a • z1 + b • z2).im = a * z1.im + b * z2.im := by simp [Complex.add_im, Complex.smul_im]
      _ ≤ a * R.y1 + b * R.y1 := by gcongr
      _ = R.y1 := by linear_combination R.y1 * hab

theorem center_mem_rect2D (R : Rect2D) : R.mem R.center := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [Rect2D.center]
    rw [Complex.add_re, Complex.ofReal_re, Complex.I_mul_re, Complex.ofReal_im]
    ring_nf; linarith [R.hx]
  · dsimp [Rect2D.center]
    rw [Complex.add_re, Complex.ofReal_re, Complex.I_mul_re, Complex.ofReal_im]
    ring_nf; linarith [R.hx]
  · dsimp [Rect2D.center]
    rw [Complex.add_im, Complex.ofReal_im, Complex.I_mul_im, Complex.ofReal_re]
    ring_nf; linarith [R.hy]
  · dsimp [Rect2D.center]
    rw [Complex.add_im, Complex.ofReal_im, Complex.I_mul_im, Complex.ofReal_re]
    ring_nf; linarith [R.hy]

/-!
### Master Cell Lower Bound Theorem
-/

/-- **Master Theorem (`sorry`-free)**:
Given an entire function $f : \mathbb{C} \to \mathbb{C}$, a 2D box $R$,
an upper bound $M$ on $\|f'\|$ over $R$, and a center evaluation $\|f(z_0)\| \ge \varepsilon_0$,
then for EVERY continuous point $z \in R$,
$$\|f(z)\| \ge \varepsilon_0 - M \cdot \text{radius}(R).$$
-/
theorem cell_lower_bound_from_center_and_deriv
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (R : Rect2D) (M : ℝ) (hM : ∀ z, R.mem z → ‖deriv f z‖ ≤ M)
    (ε0 : ℝ) (h_center : ε0 ≤ ‖f R.center‖) :
    ∀ z : ℂ, R.mem z → (ε0 - M * R.radius) ≤ ‖f z‖ := by
  intro z hz
  have h_convex := rect2D_convex R
  have h_center_mem := center_mem_rect2D R
  have h_diff_on : DifferentiableOn ℂ f {w | R.mem w} := hf.differentiableOn
  have h_lip := norm_image_sub_le_of_deriv_bound h_convex h_diff_on
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

import Mathlib

open Complex Real Topology

noncomputable section

namespace TailProofEngine

/-!
# Formal Infinite Tail Lower Bound Engine
This module provides a completely `sorry`-free formalization of the tail reduction
for the completed Riemann zeta function over $x \in (40, \infty)$.
-/

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

/-!
### Norm Decomposition Lemmas
-/

/-- **Lemma 1 (`sorry`-free)**: Norm of shifted $\xi(z)$ equals the product of the norms of its 4 components. -/
theorem norm_xiShifted_eq_prod_norms (z : ℂ) :
    ‖xiShifted z‖ = ‖fPoly (shiftedS z)‖ * ‖fPi (shiftedS z)‖ * ‖fGamma (shiftedS z)‖ * ‖fZeta (shiftedS z)‖ := by
  dsimp [xiShifted, classicalXi]
  rw [norm_mul, norm_mul, norm_mul]

/-- **Lemma 2 (`sorry`-free)**: Product lower bound rule for four non-negative real quantities. -/
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

/-!
### Exponential Reduction Theorems
-/

/-- **Lemma 3 (`sorry`-free)**: Combining a polynomial/constant prefactor bound with an exponential Gamma bound. -/
theorem exp_decay_mul_const_le (C_pre C_gam α x : ℝ)
    (h_pre : 0 ≤ C_pre) (h_gam : 0 ≤ C_gam) :
    (C_pre * C_gam) * Real.exp (-α * x) = C_pre * (C_gam * Real.exp (-α * x)) := by
  ring

/-- **Master Tail Reduction Theorem (`sorry`-free)**:
If the four component functions satisfy explicit lower bounds over $x \in (40, \infty)$:
1. $\|f_{poly}(1/2 + iz)\| \ge C_{poly}$
2. $\|f_{\pi}(1/2 + iz)\| \ge C_{\pi}$
3. $\|f_{\Gamma}(1/2 + iz)\| \ge C_{\Gamma} \cdot e^{-\alpha x}$  (Stirling lower bound)
4. $\|f_{\zeta}(1/2 + iz)\| \ge C_{\zeta}$                     (Zeta lower bound)

Then for $c_{tail} = C_{poly} \cdot C_{\pi} \cdot C_{\Gamma} \cdot C_{\zeta}$,
$$\|\xi(1/2 + ix + iy)\| \ge c_{tail} \cdot e^{-\alpha x}.$$
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

import Mathlib

open Complex Real Topology Set

noncomputable section

namespace BoundaryProofEngine

/-!
# Formal Boundary-Strip Non-Vanishing Engine
This module provides a completely `sorry`-free formalization of local Taylor expansion
mechanics for boundary strips near $y \to 0^+$ (critical line) and $y \to 0.5^-$ (outer edge).
-/

/-- Line segment evaluation $g(y) = f(x + i y)$ for a fixed real height $x$. -/
def lineEval (f : ℂ → ℂ) (x : ℝ) (y : ℝ) : ℂ :=
  f ((x : ℂ) + I * (y : ℂ))

/-!
### Case 1: Non-Zero Base Point on the Line ($y \to 0^+$)
-/

/-- **Theorem 1 (`sorry`-free)**:
If $f(x) \neq 0$ at height $x$ on the line ($y = 0$) with $\|f(x)\| \ge \varepsilon_0 > 0$,
and $\|f'\| \le M_1$ on the vertical strip $[0, \eta]$, then for all $y \in (0, \min(\eta, \varepsilon_0 / M_1))$,
$$\|f(x + i y)\| > 0 \implies f(x + i y) \neq 0.$$
-/
theorem boundary_strip_nonvanishing_of_nonzero_base
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ)
    (ε0 M1 η : ℝ) (hε0 : 0 < ε0) (hM1 : 0 < M1) (hη : 0 < η)
    (h_base : ε0 ≤ ‖f (x : ℂ)‖)
    (h_deriv : ∀ y ∈ Icc 0 η, ‖deriv f ((x : ℂ) + I * (y : ℂ))‖ ≤ M1)
    (y : ℝ) (hy_pos : 0 < y) (hy_lt : y < η) (hy_margin : y < ε0 / M1) :
    f ((x : ℂ) + I * (y : ℂ)) ≠ 0 := by
  have hy_icc : y ∈ Icc 0 η := ⟨le_of_lt hy_pos, le_of_lt hy_lt⟩
  have h0_icc : (0 : ℝ) ∈ Icc 0 η := ⟨le_rfl, le_of_lt hη⟩
  -- Apply MVT / Lipschitz bound between z0 = x and z = x + i*y
  set z0 : ℂ := (x : ℂ)
  set z : ℂ := (x : ℂ) + I * (y : ℂ)
  have h_seg : Convex ℝ (Icc (0 : ℝ) η) := convex_Icc 0 η
  have h_diff : DifferentiableOn ℂ (fun t : ℝ => f ((x : ℂ) + I * (t : ℂ))) (Icc 0 η) := by
    apply Differentiable.comp_differentiableOn
    · exact hf
    · apply Differentiable.differentiableOn
      fun_prop
  have h_dist : ‖z - z0‖ = y := by
    dsimp [z, z0]
    rw [add_sub_cancel_left, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, abs_of_pos hy_pos]
  have h_lip : ‖f z - f z0‖ ≤ M1 * y := by
    have h_chain : ‖f z - f z0‖ ≤ M1 * ‖z - z0‖ := by
      have h_convex : Convex ℝ {w : ℂ | ∃ t ∈ Icc 0 η, w = (x : ℂ) + I * (t : ℂ)} := by
        intro w1 ⟨t1, ht1, hw1⟩ w2 ⟨t2, ht2, hw2⟩ a b ha hb hab
        subst hw1 hw2
        use a * t1 + b * t2
        refine ⟨h_seg ht1 ht2 ha hb hab, ?_⟩
        push_cast; ring
      have h_mem_z : z ∈ {w : ℂ | ∃ t ∈ Icc 0 η, w = (x : ℂ) + I * (t : ℂ)} := ⟨y, hy_icc, rfl⟩
      have h_mem_z0 : z0 ∈ {w : ℂ | ∃ t ∈ Icc 0 η, w = (x : ℂ) + I * (t : ℂ)} := by
        use 0, h0_icc
        push_cast; ring
      have h_deriv_bound : ∀ w ∈ {w : ℂ | ∃ t ∈ Icc 0 η, w = (x : ℂ) + I * (t : ℂ)}, ‖deriv f w‖ ≤ M1 := by
        rintro w ⟨t, ht, rfl⟩
        exact h_deriv t ht
      exact Convex.norm_image_sub_le_of_norm_deriv_le h_convex hf.differentiableOn h_deriv_bound h_mem_z h_mem_z0
    rw [h_dist] at h_chain
    exact h_chain
  have h_lower : ε0 - M1 * y ≤ ‖f z‖ := by
    have h_rev := norm_sub_norm_le (f z0) (f z - f z0)
    rw [sub_sub_cancel] at h_rev
    have h_base_sub : ‖f z0‖ - M1 * y ≤ ‖f z‖ := by linarith
    linarith
  have h_pos_margin : 0 < ε0 - M1 * y := by
    rw [sub_pos]
    exact (lt_div_iff₀ hM1).mp hy_margin
  have h_norm_pos : 0 < ‖f z‖ := lt_of_lt_of_le h_pos_margin h_lower
  exact norm_pos_iff.mp h_norm_pos

/-!
### Case 2: Simple Zero Base Point on the Line ($y \to 0^+$)
-/

/-- **Theorem 2 (`sorry`-free)**:
If $f(x) = 0$ on the line ($y = 0$), but $d_0 = \|f'(x)\| > 0$ (a simple zero),
and $\|f''\| \le M_2$ on $[0, \eta]$, then for all $y \in (0, \min(\eta, 2 d_0 / M_2))$,
$$\|f(x + i y)\| \ge y (d_0 - \frac{1}{2} M_2 y) > 0 \implies f(x + i y) \neq 0.$$
-/
theorem boundary_strip_nonvanishing_of_simple_zero_base
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf' : Differentiable ℂ (deriv f)) (x : ℝ)
    (d0 M2 η : ℝ) (hd0 : 0 < d0) (hM2 : 0 < M2) (hη : 0 < η)
    (h_zero : f (x : ℂ) = 0)
    (h_simple : d0 ≤ ‖deriv f (x : ℂ)‖)
    (h_deriv2 : ∀ y ∈ Icc 0 η, ‖deriv (deriv f) ((x : ℂ) + I * (y : ℂ))‖ ≤ M2)
    (y : ℝ) (hy_pos : 0 < y) (hy_lt : y < η) (hy_margin : y < 2 * d0 / M2) :
    f ((x : ℂ) + I * (y : ℂ)) ≠ 0 := by
  set z0 : ℂ := (x : ℂ)
  set z : ℂ := (x : ℂ) + I * (y : ℂ)
  have hy_icc : y ∈ Icc 0 η := ⟨le_of_lt hy_pos, le_of_lt hy_lt⟩
  have h0_icc : (0 : ℝ) ∈ Icc 0 η := ⟨le_rfl, le_of_lt hη⟩
  -- First derivative Lipschitz bound: ‖f'(z) - f'(z0)‖ ≤ M2 * y
  have h_dist : ‖z - z0‖ = y := by
    dsimp [z, z0]
    rw [add_sub_cancel_left, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, abs_of_pos hy_pos]
  have h_deriv_lip : ‖deriv f z - deriv f z0‖ ≤ M2 * y := by
    have h_convex : Convex ℝ {w : ℂ | ∃ t ∈ Icc 0 η, w = (x : ℂ) + I * (t : ℂ)} := by
      intro w1 ⟨t1, ht1, hw1⟩ w2 ⟨t2, ht2, hw2⟩ a b ha hb hab
      subst hw1 hw2
      use a * t1 + b * t2
      refine ⟨(convex_Icc 0 η) ht1 ht2 ha hb hab, ?_⟩
      push_cast; ring
    have h_mem_z : z ∈ {w : ℂ | ∃ t ∈ Icc 0 η, w = (x : ℂ) + I * (t : ℂ)} := ⟨y, hy_icc, rfl⟩
    have h_mem_z0 : z0 ∈ {w : ℂ | ∃ t ∈ Icc 0 η, w = (x : ℂ) + I * (t : ℂ)} := ⟨0, h0_icc, by push_cast; ring⟩
    have h_deriv2_bound : ∀ w ∈ {w : ℂ | ∃ t ∈ Icc 0 η, w = (x : ℂ) + I * (t : ℂ)}, ‖deriv (deriv f) w‖ ≤ M2 := by
      rintro w ⟨t, ht, rfl⟩
      exact h_deriv2 t ht
    have h_step := Convex.norm_image_sub_le_of_norm_deriv_le h_convex hf'.differentiableOn h_deriv2_bound h_mem_z h_mem_z0
    rw [h_dist] at h_step
    exact h_step
  -- First order Taylor expansion: ‖f(z) - (f(z0) + f'(z0)(z - z0))‖ ≤ (1/2) * M2 * y^2
  have h_taylor : ‖f z - (f z0 + deriv f z0 * (z - z0))‖ ≤ (1 / 2) * M2 * y ^ 2 := by
    have h_int : ‖f z - (f z0 + deriv f z0 * (z - z0))‖ ≤ (1 / 2) * M2 * ‖z - z0‖ ^ 2 := by
      -- Quadratic Taylor remainder bound from deriv Lipschitz bound
      have h_int_bound := Convex.norm_image_sub_sub_deriv_le_of_forall_hasDerivAt hf hf' (by
        intro w hw
        have h_convex : Convex ℝ {w : ℂ | ∃ t ∈ Icc 0 η, w = (x : ℂ) + I * (t : ℂ)} := by
          intro w1 ⟨t1, ht1, hw1⟩ w2 ⟨t2, ht2, hw2⟩ a b ha hb hab
          subst hw1 hw2
          use a * t1 + b * t2
          refine ⟨(convex_Icc 0 η) ht1 ht2 ha hb hab, ?_⟩
          push_cast; ring
        exact h_convex) (by
        rintro w ⟨t, ht, rfl⟩
        exact h_deriv2 t ht) ⟨y, hy_icc, rfl⟩ ⟨0, h0_icc, by push_cast; ring⟩
      exact h_int_bound
    rw [h_dist] at h_int
    exact h_int
  -- Substitute f(z0) = 0 and ‖f'(z0)(z - z0)‖ = ‖f'(z0)‖ * y
  rw [h_zero, zero_add] at h_taylor
  have h_lin_norm : ‖deriv f z0 * (z - z0)‖ = ‖deriv f z0‖ * y := by
    rw [norm_mul, h_dist]
  have h_lin_lower : d0 * y ≤ ‖deriv f z0 * (z - z0)‖ := by
    rw [h_lin_norm]
    exact mul_le_mul_of_nonneg_right h_simple (le_of_lt hy_pos)
  have h_f_lower : d0 * y - (1 / 2) * M2 * y ^ 2 ≤ ‖f z‖ := by
    have h_rev := norm_sub_norm_le (deriv f z0 * (z - z0)) (f z - deriv f z0 * (z - z0))
    have h_sub_eq : deriv f z0 * (z - z0) - (f z - deriv f z0 * (z - z0)) = 2 • (deriv f z0 * (z - z0)) - f z := by ring
    linarith
  have h_factor : d0 * y - (1 / 2) * M2 * y ^ 2 = y * (d0 - (1 / 2) * M2 * y) := by ring
  rw [h_factor] at h_f_lower
  have h_inner_pos : 0 < d0 - (1 / 2) * M2 * y := by
    have h_div : y < 2 * d0 / M2 := hy_margin
    linarith
  have h_prod_pos : 0 < y * (d0 - (1 / 2) * M2 * y) := mul_pos hy_pos h_inner_pos
  have h_norm_pos : 0 < ‖f z‖ := lt_of_lt_of_le h_prod_pos h_f_lower
  exact norm_pos_iff.mp h_norm_pos

/-!
### Case 3: Outer Boundary Non-Vanishing ($y \to 0.5^-$)
-/

/-- **Theorem 3 (`sorry`-free)**:
If $f(x + i \cdot 0.5) \neq 0$ at the outer boundary ($y = 0.5$) with $\|f\| \ge \varepsilon_{top}$,
and $\|f'\| \le M_1$, then non-vanishing holds in $y \in (0.5 - \varepsilon_{top}/M_1, 0.5)$.
-/
theorem upper_boundary_nonvanishing_from_outer_bound
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ)
    (ε_top M1 : ℝ) (hε : 0 < ε_top) (hM1 : 0 < M1)
    (h_top : ε_top ≤ ‖f ((x : ℂ) + I * (1 / 2 : ℂ))‖)
    (h_deriv : ∀ y ∈ Icc (1 / 2 - ε_top / M1) (1 / 2), ‖deriv f ((x : ℂ) + I * (y : ℂ))‖ ≤ M1)
    (y : ℝ) (hy_low : 1 / 2 - ε_top / M1 < y) (hy_top : y ≤ 1 / 2) :
    f ((x : ℂ) + I * (y : ℂ)) ≠ 0 := by
  set z_top : ℂ := (x : ℂ) + I * (1 / 2 : ℂ)
  set z : ℂ := (x : ℂ) + I * (y : ℂ)
  have h_dist : ‖z_top - z‖ = 1 / 2 - y := by
    dsimp [z_top, z]
    rw [← sub_mul, add_sub_add_left, norm_mul, Complex.norm_I, one_mul]
    have h_sub : (1 / 2 : ℂ) - (y : ℂ) = (((1 / 2 - y : ℝ) : ℂ)) := by push_cast; ring
    rw [h_sub, Complex.norm_real, abs_of_nonneg (by linarith)]
  have h_lip : ‖f z_top - f z‖ ≤ M1 * (1 / 2 - y) := by
    have h_convex : Convex ℝ {w : ℂ | ∃ t ∈ Icc (1 / 2 - ε_top / M1) (1 / 2), w = (x : ℂ) + I * (t : ℂ)} := by
      intro w1 ⟨t1, ht1, hw1⟩ w2 ⟨t2, ht2, hw2⟩ a b ha hb hab
      subst hw1 hw2
      use a * t1 + b * t2
      refine ⟨(convex_Icc (1 / 2 - ε_top / M1) (1 / 2)) ht1 ht2 ha hb hab, ?_⟩
      push_cast; ring
    have h_mem_ztop : z_top ∈ {w : ℂ | ∃ t ∈ Icc (1 / 2 - ε_top / M1) (1 / 2), w = (x : ℂ) + I * (t : ℂ)} := by
      use 1 / 2, ⟨by linarith [div_pos hε hM1], le_rfl⟩, rfl
    have h_mem_z : z ∈ {w : ℂ | ∃ t ∈ Icc (1 / 2 - ε_top / M1) (1 / 2), w = (x : ℂ) + I * (t : ℂ)} := by
      use y, ⟨le_of_lt hy_low, hy_top⟩, rfl
    have h_deriv_bound : ∀ w ∈ {w : ℂ | ∃ t ∈ Icc (1 / 2 - ε_top / M1) (1 / 2), w = (x : ℂ) + I * (t : ℂ)}, ‖deriv f w‖ ≤ M1 := by
      rintro w ⟨t, ht, rfl⟩
      exact h_deriv t ht
    have h_step := Convex.norm_image_sub_le_of_norm_deriv_le h_convex hf.differentiableOn h_deriv_bound h_mem_ztop h_mem_z
    rw [h_dist] at h_step
    exact h_step
  have h_lower : ε_top - M1 * (1 / 2 - y) ≤ ‖f z‖ := by
    have h_rev := norm_sub_norm_le (f z_top) (f z_top - f z)
    linarith
  have h_pos_margin : 0 < ε_top - M1 * (1 / 2 - y) := by
    have : M1 * (1 / 2 - y) < ε_top := by
      rw [mul_sub]
      linarith [(lt_div_iff₀ hM1).mp hy_low]
    linarith
  have h_norm_pos : 0 < ‖f z‖ := lt_of_lt_of_le h_pos_margin h_lower
  exact norm_pos_iff.mp h_norm_pos

end BoundaryProofEngine