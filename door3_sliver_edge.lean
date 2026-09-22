import Mathlib
import central_cover_assembly

/-! # Door-3 sliver edge supplier (write-only, new file)

Owns ONLY this file. No other repo file is touched. No build is run here.
Central registration is deferred.

Consumer shapes (from `door3_sliver_nonvan.lean`, `sliver_hSliver_of_numericData`):
* `hTopLower : forall (x : Real), x in Set.Icc (-10) 10 ->
    mT <= || CentralCoverAssembly.xiShiftedEntire ((x : Complex) + Complex.I * (1/2 : Complex)) ||`
* `hBotLower : forall (x : Real), x in Set.Icc (-10) 10 ->
    mB <= || CentralCoverAssembly.xiShiftedEntire ((x : Complex) - Complex.I * (1/2 : Complex)) ||`
* `hTopDeriv : forall (x : Real), x in Set.Icc (-10) 10 ->
    forall (y : Real), y in Set.Icc (1/2 - mT / MT) (1/2) ->
      || deriv CentralCoverAssembly.xiShiftedEntire ((x : Complex) + Complex.I * (y : Complex)) || <= MT`
* `hBotDeriv : mirror on Set.Icc (-(1/2)) (-(1/2) + mB / MB)`
* gates `0.01 < mT / MT`, `0.01 < mB / MB`, side conditions `mT / MT <= 1`.

What this file banks (all proved, numerals at most 6 digits):
* (S) explicit s-mapping at the two edges and in general;
* (F) entire-expansion factor identities at the edges;
* (E) sharp single-point numerals `1 / 2` at `x = 0` (largest true there, equality);
* (D) generic entire Cauchy step plus closed-ball covering (`R = 12`, `r = 1`)
    discharging the `hTopDeriv` / `hBotDeriv` shapes from one closed-ball sup;
* (G) width-gate iff lemmas, example arithmetic `11 / 1000 = 0.011`,
    sharp-ratio identities and shortfall lemmas.

Residual (left for the patch phase, stated openly):
* uniform numerals `mT / mB` over `Set.Icc (-10) 10` are NOT landed here;
  only the pointwise `1 / 2` values and conditional mono lemmas are banked.
* uniform closed-ball sups `C` on `Metric.closedBall 0 12` are taken as
  explicit premises; once numeric `C` values are computed, (D) yields `MT / MB`.
-/

noncomputable section

namespace Door3SliverEdge

/-! ### (S) s-mapping at the edges -/

/-- Top edge s-point: `1 / 2 + I * (x + I / 2) = I * x`. -/
theorem edgeS_top (x : ℝ) :
    (1 / 2 : ℂ) + Complex.I * (((x : ℂ) + Complex.I / 2)) =
      Complex.I * ((x : ℂ)) := by
  have hI : Complex.I * (Complex.I / 2) = -(1 / 2 : ℂ) := by
    calc Complex.I * (Complex.I / 2) = (Complex.I * Complex.I) / 2 := by ring
      _ = -(1 / 2 : ℂ) := by rw [Complex.I_mul_I]; ring
  calc (1 / 2 : ℂ) + Complex.I * (((x : ℂ) + Complex.I / 2))
      = (1 / 2 : ℂ) + (Complex.I * ((x : ℂ)) + Complex.I * (Complex.I / 2)) := by ring
    _ = (1 / 2 : ℂ) + (Complex.I * ((x : ℂ)) + (-(1 / 2 : ℂ))) := by rw [hI]
    _ = Complex.I * ((x : ℂ)) := by ring

/-- Bottom edge s-point: `1 / 2 + I * (x - I / 2) = 1 + I * x`. -/
theorem edgeS_bot (x : ℝ) :
    (1 / 2 : ℂ) + Complex.I * (((x : ℂ) - Complex.I / 2)) =
      1 + Complex.I * ((x : ℂ)) := by
  have hI : Complex.I * (Complex.I / 2) = -(1 / 2 : ℂ) := by
    calc Complex.I * (Complex.I / 2) = (Complex.I * Complex.I) / 2 := by ring
      _ = -(1 / 2 : ℂ) := by rw [Complex.I_mul_I]; ring
  calc (1 / 2 : ℂ) + Complex.I * (((x : ℂ) - Complex.I / 2))
      = (1 / 2 : ℂ) + (Complex.I * ((x : ℂ)) - Complex.I * (Complex.I / 2)) := by ring
    _ = (1 / 2 : ℂ) + (Complex.I * ((x : ℂ)) - (-(1 / 2 : ℂ))) := by rw [hI]
    _ = 1 + Complex.I * ((x : ℂ)) := by ring

/-- General vertical s-point: `1 / 2 + I * (x + I * y) = (1 / 2 - y) + I * x`. -/
theorem edgeS_general (x : ℝ) (y : ℝ) :
    (1 / 2 : ℂ) + Complex.I * (((x : ℂ) + Complex.I * ((y : ℝ) : ℂ))) =
      ((((1 / 2 - y : ℝ)) : ℂ)) + Complex.I * ((x : ℂ)) := by
  have hII : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
  have h1 : Complex.I * (Complex.I * (((y : ℝ)) : ℂ)) = -((((y : ℝ)) : ℂ)) := by
    calc Complex.I * (Complex.I * (((y : ℝ)) : ℂ))
        = (Complex.I * Complex.I) * ((((y : ℝ)) : ℂ)) := by ring
      _ = -((((y : ℝ)) : ℂ)) := by rw [hII]; ring
  calc (1 / 2 : ℂ) + Complex.I * (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))
      = (1 / 2 : ℂ) + Complex.I * ((x : ℂ)) + Complex.I * (Complex.I * (((y : ℝ)) : ℂ)) := by ring
    _ = (1 / 2 : ℂ) + Complex.I * ((x : ℂ)) + (-((((y : ℝ)) : ℂ))) := by rw [h1]
    _ = ((((1 / 2 - y : ℝ)) : ℂ)) + Complex.I * ((x : ℂ)) := by push_cast; ring

/-! ### Edge-line forms used by the consumer -/

/-- Consumer top form equals the `+ I / 2` form. -/
theorem edgeTopForm_eq (x : ℝ) :
    (((x : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ))) = (((x : ℂ) + Complex.I / 2)) := by
  have h : Complex.I * (((((1 / 2 : ℝ))) : ℂ)) = Complex.I / 2 := by push_cast; ring
  rw [h]

/-- Consumer bottom form equals the `- I / 2` form. -/
theorem edgeBotForm_eq (x : ℝ) :
    (((x : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ))) = (((x : ℂ) - Complex.I / 2)) := by
  have h : Complex.I * (((((1 / 2 : ℝ))) : ℂ)) = Complex.I / 2 := by push_cast; ring
  rw [h]

/-- Top edge polynomial factor: `(x + I / 2)^2 + 1 / 4 = x * (x + I)`. -/
theorem edgePoly_top (x : ℝ) :
    ((((x : ℂ) + Complex.I / 2)) ^ 2 + (1 / 4 : ℂ)) =
      (((x : ℂ)) * (((x : ℂ) + Complex.I))) := by
  have hsq : (Complex.I / 2) ^ 2 = (-1 / 4 : ℂ) := by
    calc (Complex.I / 2) ^ 2 = (Complex.I * Complex.I) / 4 := by ring
      _ = (-1 / 4 : ℂ) := by rw [Complex.I_mul_I]
  have hcross : 2 * (((x : ℂ)) * (Complex.I / 2)) = Complex.I * ((x : ℂ)) := by ring
  calc ((((x : ℂ) + Complex.I / 2)) ^ 2 + (1 / 4 : ℂ))
      = (((x : ℂ)) ^ 2 + 2 * (((x : ℂ)) * (Complex.I / 2)) + (Complex.I / 2) ^ 2 + (1 / 4 : ℂ)) := by ring
    _ = (((x : ℂ)) ^ 2 + Complex.I * ((x : ℂ)) + (-1 / 4 : ℂ) + (1 / 4 : ℂ)) := by rw [hsq, hcross]
    _ = (((x : ℂ)) * (((x : ℂ) + Complex.I))) := by ring

/-- Bottom edge polynomial factor: `(x - I / 2)^2 + 1 / 4 = x * (x - I)`. -/
theorem edgePoly_bot (x : ℝ) :
    ((((x : ℂ) - Complex.I / 2)) ^ 2 + (1 / 4 : ℂ)) =
      (((x : ℂ)) * (((x : ℂ) - Complex.I))) := by
  have hsq : (Complex.I / 2) ^ 2 = (-1 / 4 : ℂ) := by
    calc (Complex.I / 2) ^ 2 = (Complex.I * Complex.I) / 4 := by ring
      _ = (-1 / 4 : ℂ) := by rw [Complex.I_mul_I]
  have hcross : 2 * (((x : ℂ)) * (Complex.I / 2)) = Complex.I * ((x : ℂ)) := by ring
  calc ((((x : ℂ) - Complex.I / 2)) ^ 2 + (1 / 4 : ℂ))
      = (((x : ℂ)) ^ 2 - 2 * (((x : ℂ)) * (Complex.I / 2)) + (Complex.I / 2) ^ 2 + (1 / 4 : ℂ)) := by ring
    _ = (((x : ℂ)) ^ 2 - Complex.I * ((x : ℂ)) + (-1 / 4 : ℂ) + (1 / 4 : ℂ)) := by rw [hsq, hcross]
    _ = (((x : ℂ)) * (((x : ℂ) - Complex.I))) := by ring

/-! ### (F) entire-expansion at the edges -/

/-- Entire value on the top edge, factored via the s-point `I * x`. -/
theorem entire_top_expand (x : ℝ) :
    CentralCoverAssembly.xiShiftedEntire (((x : ℂ) + Complex.I / 2)) =
      (1 / 2 : ℂ) - ((((x : ℂ)) * (((x : ℂ) + Complex.I))) / 2 *
        completedRiemannZeta₀ (Complex.I * ((x : ℂ)))) := by
  have hP : ((((x : ℂ) + Complex.I / 2)) ^ 2 + (1 / 4 : ℂ)) =
      (((x : ℂ)) * (((x : ℂ) + Complex.I))) := edgePoly_top x
  have hS : (1 / 2 : ℂ) + Complex.I * (((x : ℂ) + Complex.I / 2)) =
      Complex.I * ((x : ℂ)) := edgeS_top x
  unfold CentralCoverAssembly.xiShiftedEntire
  rw [hP, hS]

/-- Entire value on the bottom edge, factored via the s-point `1 + I * x`. -/
theorem entire_bot_expand (x : ℝ) :
    CentralCoverAssembly.xiShiftedEntire (((x : ℂ) - Complex.I / 2)) =
      (1 / 2 : ℂ) - ((((x : ℂ)) * (((x : ℂ) - Complex.I))) / 2 *
        completedRiemannZeta₀ (1 + Complex.I * ((x : ℂ)))) := by
  have hP : ((((x : ℂ) - Complex.I / 2)) ^ 2 + (1 / 4 : ℂ)) =
      (((x : ℂ)) * (((x : ℂ) - Complex.I))) := edgePoly_bot x
  have hS : (1 / 2 : ℂ) + Complex.I * (((x : ℂ) - Complex.I / 2)) =
      1 + Complex.I * ((x : ℂ)) := edgeS_bot x
  unfold CentralCoverAssembly.xiShiftedEntire
  rw [hP, hS]

/-- Entire value in consumer top form. -/
theorem entire_top_expand_consumer (x : ℝ) :
    CentralCoverAssembly.xiShiftedEntire (((x : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ))) =
      (1 / 2 : ℂ) - ((((x : ℂ)) * (((x : ℂ) + Complex.I))) / 2 *
        completedRiemannZeta₀ (Complex.I * ((x : ℂ)))) := by
  have hF : (((x : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ))) =
      (((x : ℂ) + Complex.I / 2)) := edgeTopForm_eq x
  rw [hF]
  exact entire_top_expand x

/-- Entire value in consumer bottom form. -/
theorem entire_bot_expand_consumer (x : ℝ) :
    CentralCoverAssembly.xiShiftedEntire (((x : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ))) =
      (1 / 2 : ℂ) - ((((x : ℂ)) * (((x : ℂ) - Complex.I))) / 2 *
        completedRiemannZeta₀ (1 + Complex.I * ((x : ℂ)))) := by
  have hF : (((x : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ))) =
      (((x : ℂ) - Complex.I / 2)) := edgeBotForm_eq x
  rw [hF]
  exact entire_bot_expand x

/-! ### (E) sharp single-point numerals at `x = 0` -/

/-- Endpoint value on top (reproved locally, no extra import). -/
theorem endpoint_top_value :
    CentralCoverAssembly.xiShiftedEntire (Complex.I / 2) = (1 / 2 : ℂ) := by
  unfold CentralCoverAssembly.xiShiftedEntire
  have hsq : (Complex.I / 2) ^ 2 + (1 / 4 : ℂ) = 0 := by
    rw [div_pow, Complex.I_sq]
    norm_num
  rw [hsq]
  ring

/-- Endpoint value on bottom (reproved locally). -/
theorem endpoint_bot_value :
    CentralCoverAssembly.xiShiftedEntire (-(Complex.I / 2)) = (1 / 2 : ℂ) := by
  unfold CentralCoverAssembly.xiShiftedEntire
  have hsq : (-(Complex.I / 2)) ^ 2 + (1 / 4 : ℂ) = 0 := by
    rw [neg_sq, div_pow, Complex.I_sq]
    norm_num
  rw [hsq]
  ring

/-- Norm of the top endpoint value. -/
theorem endpoint_top_norm :
    ‖CentralCoverAssembly.xiShiftedEntire (Complex.I / 2)‖ = (1 / 2 : ℝ) := by
  rw [endpoint_top_value]
  have hcast : ((1 / 2 : ℂ)) = ((((1 / 2 : ℝ))) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]

/-- Norm of the bottom endpoint value. -/
theorem endpoint_bot_norm :
    ‖CentralCoverAssembly.xiShiftedEntire (-(Complex.I / 2))‖ = (1 / 2 : ℝ) := by
  rw [endpoint_bot_value]
  have hcast : ((1 / 2 : ℂ)) = ((((1 / 2 : ℝ))) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]

/-- Sharpness on top: `m` lower-bounds the endpoint norm exactly when `m <= 1 / 2`. -/
theorem endpoint_top_sharp (m : ℝ) :
    m ≤ ‖CentralCoverAssembly.xiShiftedEntire (Complex.I / 2)‖ ↔ m ≤ (1 / 2 : ℝ) := by
  rw [endpoint_top_norm]

/-- Sharpness on bottom. -/
theorem endpoint_bot_sharp (m : ℝ) :
    m ≤ ‖CentralCoverAssembly.xiShiftedEntire (-(Complex.I / 2))‖ ↔ m ≤ (1 / 2 : ℝ) := by
  rw [endpoint_bot_norm]

/-- Edge-line point at `x = 0` on top equals `I / 2`. -/
theorem edgeTop_at_zero :
    (((0 : ℂ) + Complex.I / 2)) = Complex.I / 2 := by ring

/-- Edge-line point at `x = 0` on bottom equals `-(I / 2)`. -/
theorem edgeBot_at_zero :
    (((0 : ℂ) - Complex.I / 2)) = -(Complex.I / 2) := by ring

/-- Consumer-form top numeral at `x = 0`: norm equals `1 / 2`. -/
theorem edgeTop_consumer_norm_at_zero :
    ‖CentralCoverAssembly.xiShiftedEntire (((0 : ℝ) : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ))‖ =
      (1 / 2 : ℝ) := by
  have hF : ((((0 : ℝ)) : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ)) =
      (((0 : ℂ) + Complex.I / 2)) := edgeTopForm_eq 0
  rw [hF, edgeTop_at_zero, endpoint_top_norm]

/-- Consumer-form bottom numeral at `x = 0`: norm equals `1 / 2`. -/
theorem edgeBot_consumer_norm_at_zero :
    ‖CentralCoverAssembly.xiShiftedEntire (((((0 : ℝ))) : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ))‖ =
      (1 / 2 : ℝ) := by
  have hF : (((((0 : ℝ))) : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ)) =
      (((0 : ℂ) - Complex.I / 2)) := edgeBotForm_eq 0
  rw [hF, edgeBot_at_zero, endpoint_bot_norm]

/-- Largest true single-point top numeral: `1 / 2` holds with equality. -/
theorem edgeTop_single_lower :
    ((1 / 2 : ℝ)) ≤
      ‖CentralCoverAssembly.xiShiftedEntire (((((0 : ℝ))) : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ))‖ := by
  rw [edgeTop_consumer_norm_at_zero]

/-- Largest true single-point bottom numeral. -/
theorem edgeBot_single_lower :
    ((1 / 2 : ℝ)) ≤
      ‖CentralCoverAssembly.xiShiftedEntire (((((0 : ℝ))) : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ))‖ := by
  rw [edgeBot_consumer_norm_at_zero]

/-! ### Uniform lower shapes (conditional mono, matching the consumer) -/

/-- Mono for uniform top lowers: a smaller `m1` inherits the bound. -/
theorem uniform_lower_mono_top (m1 : ℝ) (m2 : ℝ) (hle : m1 ≤ m2)
    (h : ∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      m2 ≤ ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖) :
    ∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      m1 ≤ ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖ := by
  intro x hx
  exact le_trans hle (h x hx)

/-- Mono for uniform bottom lowers. -/
theorem uniform_lower_mono_bot (m1 : ℝ) (m2 : ℝ) (hle : m1 ≤ m2)
    (h : ∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      m2 ≤ ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖) :
    ∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      m1 ≤ ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖ := by
  intro x hx
  exact le_trans hle (h x hx)

/-! ### (D) deriv sups via the entire Cauchy estimate -/

/-- Pointwise Cauchy step for the entire extension (distinct name). -/
theorem entire_deriv_le_of_sphere_bound (w : ℂ) (r : ℝ) (C : ℝ) (hr : 0 < r)
    (hC : ∀ (z : ℂ), z ∈ Metric.sphere w r →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ‖deriv CentralCoverAssembly.xiShiftedEntire w‖ ≤ C / r := by
  have hDC : DiffContOnCl ℂ CentralCoverAssembly.xiShiftedEntire (Metric.ball w r) :=
    CentralCoverAssembly.xiShiftedEntire_differentiable.diffContOnCl
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hDC hC

/-- Every edge vertical point with `|x| <= 10`, `|y| <= 1 / 2` has norm at most `11`. -/
theorem edgeMem_norm_le (x : ℝ) (y : ℝ)
    (hx : x ∈ Set.Icc (-10 : ℝ) (10 : ℝ)) (hy : y ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    ‖(((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ 11 := by
  have hxpair := Set.mem_Icc.mp hx
  have hypair := Set.mem_Icc.mp hy
  have hxabs : |x| ≤ 10 := by
    rw [abs_le]
    constructor
    · linarith [hxpair.1]
    · linarith [hxpair.2]
  have hyabs : |y| ≤ 1 / 2 := by
    rw [abs_le]
    constructor
    · linarith [hypair.1]
    · linarith [hypair.2]
  calc ‖(((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖
      ≤ ‖((x : ℂ))‖ + ‖Complex.I * ((((y : ℝ))) : ℂ)‖ := norm_add_le _ _
    _ = |x| + |y| := by
      rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 11 := by linarith [hxabs, hyabs]

/-- Unit spheres over the edge band lie in `closedBall 0 12`. -/
theorem edgeSphere_cover (x : ℝ) (y : ℝ)
    (hx : x ∈ Set.Icc (-10 : ℝ) (10 : ℝ)) (hy : y ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (z : ℂ) (hz : z ∈ Metric.sphere (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ))) 1) :
    z ∈ Metric.closedBall (0 : ℂ) 12 := by
  have hw : ‖(((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ 11 :=
    edgeMem_norm_le x y hx hy
  have hdist : dist z (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ))) = 1 :=
    Metric.mem_sphere.mp hz
  have htri : dist z (0 : ℂ) ≤
      dist z (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ))) +
        dist (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ))) (0 : ℂ) :=
    dist_triangle _ _ _
  have hw0 : dist (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ))) (0 : ℂ) =
      ‖(((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ := by
    rw [dist_eq_norm, sub_zero]
  rw [hdist, hw0] at htri
  rw [Metric.mem_closedBall]
  linarith [htri, hw]

/-- Half-radius spheres over the edge band lie in `closedBall 0 12` (tighter-radius cover). -/
theorem edgeSphere_cover_half (x : ℝ) (y : ℝ)
    (hx : x ∈ Set.Icc (-10 : ℝ) (10 : ℝ)) (hy : y ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (z : ℂ) (hz : z ∈ Metric.sphere (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ))) (1 / 2)) :
    z ∈ Metric.closedBall (0 : ℂ) 12 := by
  have hw : ‖(((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ 11 :=
    edgeMem_norm_le x y hx hy
  have hdist : dist z (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ))) = 1 / 2 :=
    Metric.mem_sphere.mp hz
  have htri : dist z (0 : ℂ) ≤
      dist z (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ))) +
        dist (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ))) (0 : ℂ) :=
    dist_triangle _ _ _
  have hw0 : dist (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ))) (0 : ℂ) =
      ‖(((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ := by
    rw [dist_eq_norm, sub_zero]
  rw [hdist, hw0] at htri
  rw [Metric.mem_closedBall]
  linarith [htri, hw]

/-- Uniform top deriv sup from one closed-ball sup (`r = 1`, so `MT = C`). -/
theorem uniform_top_deriv_of_closedBall (d : ℝ) (C : ℝ) (hdle : d ≤ 1)
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C)
    (x : ℝ) (hx : x ∈ Set.Icc (-10 : ℝ) (10 : ℝ))
    (y : ℝ) (hy : y ∈ Set.Icc ((1 / 2 : ℝ) - d) (1 / 2 : ℝ)) :
    ‖deriv CentralCoverAssembly.xiShiftedEntire
      (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ C := by
  have hypair := Set.mem_Icc.mp hy
  have hyband : y ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    apply Set.mem_Icc.mpr
    constructor
    · linarith [hypair.1, hdle]
    · exact hypair.2
  have hsphere : ∀ (z : ℂ), z ∈
      Metric.sphere (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ))) 1 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C := by
    intro z hz
    exact hC z (edgeSphere_cover x y hx hyband z hz)
  have h := entire_deriv_le_of_sphere_bound
    (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ))) 1 C (by norm_num) hsphere
  calc ‖deriv CentralCoverAssembly.xiShiftedEntire
        (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ C / 1 := h
    _ = C := by ring

/-- Uniform bottom deriv sup from one closed-ball sup (mirror). -/
theorem uniform_bot_deriv_of_closedBall (d : ℝ) (C : ℝ) (hdle : d ≤ 1)
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C)
    (x : ℝ) (hx : x ∈ Set.Icc (-10 : ℝ) (10 : ℝ))
    (y : ℝ) (hy : y ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + d)) :
    ‖deriv CentralCoverAssembly.xiShiftedEntire
      (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ C := by
  have hypair := Set.mem_Icc.mp hy
  have hyband : y ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    apply Set.mem_Icc.mpr
    constructor
    · exact hypair.1
    · linarith [hypair.2, hdle]
  have hsphere : ∀ (z : ℂ), z ∈
      Metric.sphere (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ))) 1 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C := by
    intro z hz
    exact hC z (edgeSphere_cover x y hx hyband z hz)
  have h := entire_deriv_le_of_sphere_bound
    (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ))) 1 C (by norm_num) hsphere
  calc ‖deriv CentralCoverAssembly.xiShiftedEntire
        (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ C / 1 := h
    _ = C := by ring

/-- Uniform top deriv sup from one closed-ball sup (`r = 1 / 2`, so `MT = 2 * C`). -/
theorem uniform_top_deriv_of_closedBall_half (d : ℝ) (C : ℝ) (hdle : d ≤ 1)
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C)
    (x : ℝ) (hx : x ∈ Set.Icc (-10 : ℝ) (10 : ℝ))
    (y : ℝ) (hy : y ∈ Set.Icc ((1 / 2 : ℝ) - d) (1 / 2 : ℝ)) :
    ‖deriv CentralCoverAssembly.xiShiftedEntire
      (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ 2 * C := by
  have hypair := Set.mem_Icc.mp hy
  have hyband : y ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    apply Set.mem_Icc.mpr
    constructor
    · linarith [hypair.1, hdle]
    · exact hypair.2
  have hsphere : ∀ (z : ℂ), z ∈
      Metric.sphere (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ))) (1 / 2) →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C := by
    intro z hz
    exact hC z (edgeSphere_cover_half x y hx hyband z hz)
  have h := entire_deriv_le_of_sphere_bound
    (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ))) (1 / 2) C (by norm_num) hsphere
  calc ‖deriv CentralCoverAssembly.xiShiftedEntire
        (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ C / (1 / 2) := h
    _ = 2 * C := by ring

/-- Uniform bottom deriv sup from one closed-ball sup (`r = 1 / 2` mirror, so `MB = 2 * C`). -/
theorem uniform_bot_deriv_of_closedBall_half (d : ℝ) (C : ℝ) (hdle : d ≤ 1)
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C)
    (x : ℝ) (hx : x ∈ Set.Icc (-10 : ℝ) (10 : ℝ))
    (y : ℝ) (hy : y ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + d)) :
    ‖deriv CentralCoverAssembly.xiShiftedEntire
      (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ 2 * C := by
  have hypair := Set.mem_Icc.mp hy
  have hyband : y ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    apply Set.mem_Icc.mpr
    constructor
    · exact hypair.1
    · linarith [hypair.2, hdle]
  have hsphere : ∀ (z : ℂ), z ∈
      Metric.sphere (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ))) (1 / 2) →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C := by
    intro z hz
    exact hC z (edgeSphere_cover_half x y hx hyband z hz)
  have h := entire_deriv_le_of_sphere_bound
    (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ))) (1 / 2) C (by norm_num) hsphere
  calc ‖deriv CentralCoverAssembly.xiShiftedEntire
        (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ C / (1 / 2) := h
    _ = 2 * C := by ring

/-! ### (G) width gates, ratios and shortfall -/

/-- Top width gate iff form. -/
theorem width_gate_top_iff (d : ℝ) :
    (1 / 2 : ℝ) - d < 0.49 ↔ (0.01 : ℝ) < d := by
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- Bottom width gate iff form. -/
theorem width_gate_bot_iff (d : ℝ) :
    (-0.49 : ℝ) < -(1 / 2 : ℝ) + d ↔ (0.01 : ℝ) < d := by
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- Proved arithmetic: example width clears the top gate. -/
theorem example_width_top :
    (1 / 2 : ℝ) - 11 / 1000 < 0.49 := by norm_num

/-- Proved arithmetic: example width clears the bottom gate. -/
theorem example_width_bot :
    (-0.49 : ℝ) < -(1 / 2 : ℝ) + 11 / 1000 := by norm_num

/-- Proved arithmetic: `0.011` exceeds `0.01`. -/
theorem example_gate :
    (0.01 : ℝ) < 11 / 1000 := by norm_num

/-- Miss identity on top. -/
theorem miss_top (mT : ℝ) (MT : ℝ) :
    (0.01 : ℝ) - mT / MT = ((1 / 2 : ℝ) - mT / MT) - (0.49 : ℝ) := by ring

/-- Miss identity on bottom. -/
theorem miss_bot (mB : ℝ) (MB : ℝ) :
    (0.01 : ℝ) - mB / MB = (-0.49 : ℝ) - (-(1 / 2 : ℝ) + mB / MB) := by ring

/-- Shortfall on top: a missed gate leaves the fenced edge at or above `0.49`. -/
theorem shortfall_top (mT : ℝ) (MT : ℝ) (hshort : mT / MT ≤ 0.01) :
    (0.49 : ℝ) ≤ (1 / 2 : ℝ) - mT / MT := by linarith

/-- Shortfall on bottom (mirror). -/
theorem shortfall_bot (mB : ℝ) (MB : ℝ) (hshort : mB / MB ≤ 0.01) :
    -(1 / 2 : ℝ) + mB / MB ≤ (-0.49 : ℝ) := by linarith

/-! ### (H) uniform `mT = 1 / 2` feasibility adjudication (top edge)

Poly-zero check at `x = 0`: `edgePoly_top 0` gives `(0 + I / 2)^2 + 1 / 4 = 0`,
so `entire_top_expand 0` collapses to `1 / 2`, and
`edgeTop_consumer_norm_at_zero` gives norm `1 / 2` — NOT zero.
Hence the poly zero does NOT kill `m = 1 / 2`; it kills only `m > 1 / 2`.
This banks the sharp ceiling: any uniform top lower over
`Set.Icc (-10) 10` is at most `1 / 2`, so `1 / 2` would be optimal if held.
Uniform existence of `mT = 1 / 2` itself remains open (needs pointwise
`completedRiemannZeta₀` bounds away from `x = 0`; no force here). -/

/-- Sharp ceiling for uniform top lowers: no `m > 1 / 2` works; `1 / 2` is best possible. -/
theorem uniform_top_lower_le_half (m : ℝ)
    (h : ∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      m ≤ ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖) :
    m ≤ (1 / 2 : ℝ) := by
  have h0mem : (0 : ℝ) ∈ Set.Icc (-10 : ℝ) (10 : ℝ) := by
    rw [Set.mem_Icc]
    constructor
    · norm_num
    · norm_num
  have h0 := h 0 h0mem
  rw [edgeTop_consumer_norm_at_zero] at h0
  exact h0

/-- Sharp ceiling for uniform bottom lowers: no `m > 1 / 2` works; `1 / 2` is best possible. -/
theorem uniform_bot_lower_le_half (m : ℝ)
    (h : ∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      m ≤ ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖) :
    m ≤ (1 / 2 : ℝ) := by
  have h0mem : (0 : ℝ) ∈ Set.Icc (-10 : ℝ) (10 : ℝ) := by
    rw [Set.mem_Icc]
    constructor
    · norm_num
    · norm_num
  have h0 := h 0 h0mem
  rw [edgeBot_consumer_norm_at_zero] at h0
  exact h0

/-! ### (I) honest partial existence near zero (half-optimal `1 / 4`)

What is banked here: continuity of the edge norm at `x = 0` (value `1 / 2`)
yields a small symmetric interval where the norm stays above `1 / 4`
(half of optimal). This is a genuine positive uniform lower on a restricted
range, proved with no zeta input.

What is NOT claimed: uniform `1 / 2` over `Set.Icc (-10) 10`, uniform `1 / 2`
on any non-singleton interval, or uniform `1 / 2` away from zero. Those need
pointwise lower bounds on `completedRiemannZeta₀` at `I * x` (`x ≠ 0`, top arm)
and at `1 + I * x` (bottom arm) controlling the correction terms in
`entire_top_expand` / `entire_bot_expand` via `edgePoly_top` / `edgePoly_bot`.
Repo grep finds only upper bounds for `completedRiemannZeta₀`
(`door3_cell_suppliers.lean:992` norm `≤ 479`,
`door3_first_cell.lean:842` norm `≤ 479`,
`door3_R02_ball_advance.lean:162` norm `≤ M`), plus order/tail upper premises
in `riemann_hypothesis.lean`; no lower bound at `I * x` or `1 + I * x`.
So full `m = 1 / 2` existence stays open; no force here. -/

/-- Top edge norm map is continuous. -/
theorem topEdgeNorm_continuous :
    Continuous (fun x : ℝ =>
      ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖) := by
  have hmap : Continuous (fun x : ℝ => (((x : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ)))) := by
    fun_prop
  exact (CentralCoverAssembly.xiShiftedEntire_differentiable.continuous.comp hmap).norm

/-- Bottom edge norm map is continuous. -/
theorem botEdgeNorm_continuous :
    Continuous (fun x : ℝ =>
      ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖) := by
  have hmap : Continuous (fun x : ℝ => (((x : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ)))) := by
    fun_prop
  exact (CentralCoverAssembly.xiShiftedEntire_differentiable.continuous.comp hmap).norm

/-- Half-optimal uniform lower near zero, top arm: some `δ > 0` gives `1 / 4` on `Icc (-δ) δ`. -/
theorem m_half_existence_of_zero_top :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : ℝ), x ∈ Set.Icc (-δ) δ →
      (1 / 4 : ℝ) ≤
        ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖ := by
  have hFcont : Continuous (fun x : ℝ =>
      ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖) :=
    topEdgeNorm_continuous
  have hcontAt : ContinuousAt (fun x : ℝ =>
      ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖) 0 :=
    hFcont.continuousAt
  rw [Metric.continuousAt_iff] at hcontAt
  obtain ⟨δ, hδpos, hδ⟩ := hcontAt (1 / 4 : ℝ) (by norm_num)
  refine ⟨δ, hδpos, ?_⟩
  intro x hx
  have hxpair := Set.mem_Icc.mp hx
  have habs : |x| < δ := by
    rw [abs_lt]
    constructor
    · linarith [hxpair.1]
    · linarith [hxpair.2]
  have hdistx : dist x (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero]
    exact habs
  have hFx := hδ x hdistx
  have hFxR : dist
      ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖
      ‖CentralCoverAssembly.xiShiftedEntire (((((0 : ℝ))) : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖ <
      (1 / 4 : ℝ) := hFx
  have h0norm : ‖CentralCoverAssembly.xiShiftedEntire (((((0 : ℝ))) : ℂ) +
      Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖ = (1 / 2 : ℝ) :=
    edgeTop_consumer_norm_at_zero
  rw [h0norm] at hFxR
  have hFx2 : dist
      ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖
      (1 / 2 : ℝ) < (1 / 4 : ℝ) := hFxR
  rw [Real.dist_eq] at hFx2
  rw [abs_lt] at hFx2
  linarith [hFx2.1]

/-- Half-optimal uniform lower near zero, bottom arm. -/
theorem m_half_existence_of_zero_bot :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : ℝ), x ∈ Set.Icc (-δ) δ →
      (1 / 4 : ℝ) ≤
        ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖) := by
  have hFcont : Continuous (fun x : ℝ =>
      ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖) :=
    botEdgeNorm_continuous
  have hcontAt : ContinuousAt (fun x : ℝ =>
      ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖) 0 :=
    hFcont.continuousAt
  rw [Metric.continuousAt_iff] at hcontAt
  obtain ⟨δ, hδpos, hδ⟩ := hcontAt (1 / 4 : ℝ) (by norm_num)
  refine ⟨δ, hδpos, ?_⟩
  intro x hx
  have hxpair := Set.mem_Icc.mp hx
  have habs : |x| < δ := by
    rw [abs_lt]
    constructor
    · linarith [hxpair.1]
    · linarith [hxpair.2]
  have hdistx : dist x (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero]
    exact habs
  have hFx := hδ x hdistx
  have hFxR : dist
      ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖
      ‖CentralCoverAssembly.xiShiftedEntire (((((0 : ℝ))) : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖ <
      (1 / 4 : ℝ) := hFx
  have h0norm : ‖CentralCoverAssembly.xiShiftedEntire (((((0 : ℝ))) : ℂ) -
      Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖ = (1 / 2 : ℝ) :=
    edgeBot_consumer_norm_at_zero
  rw [h0norm] at hFxR
  have hFx2 : dist
      ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖
      (1 / 2 : ℝ) < (1 / 4 : ℝ) := hFxR
  rw [Real.dist_eq] at hFx2
  rw [abs_lt] at hFx2
  linarith [hFx2.1]

/-- Combined honest partial existence near zero: one `δ > 0` works for both arms at `1 / 4`. -/
theorem m_half_existence_of_zero :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ (x : ℝ), x ∈ Set.Icc (-δ) δ →
        (1 / 4 : ℝ) ≤
          ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖) ∧
      (∀ (x : ℝ), x ∈ Set.Icc (-δ) δ →
        (1 / 4 : ℝ) ≤
          ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖) := by
  obtain ⟨δ1, hδ1pos, h1⟩ := m_half_existence_of_zero_top
  obtain ⟨δ2, hδ2pos, h2⟩ := m_half_existence_of_zero_bot
  refine ⟨min δ1 δ2, lt_min hδ1pos hδ2pos, ?_, ?_⟩
  · intro x hx
    have hxpair := Set.mem_Icc.mp hx
    have hx1 : x ∈ Set.Icc (-δ1) δ1 := by
      apply Set.mem_Icc.mpr
      constructor
      · linarith [hxpair.1, min_le_left δ1 δ2, hδ2pos]
      · linarith [hxpair.2, min_le_left δ1 δ2]
    exact h1 x hx1
  · intro x hx
    have hxpair := Set.mem_Icc.mp hx
    have hx2 : x ∈ Set.Icc (-δ2) δ2 := by
      apply Set.mem_Icc.mpr
      constructor
      · linarith [hxpair.1, min_le_right δ1 δ2, hδ1pos]
      · linarith [hxpair.2, min_le_right δ1 δ2]
/-! ### (J) M40 gates + strict `m ≤ 1 / 2` ceilings (top-owned feeder arithmetic)

Grepped base:
* ceilings `uniform_top_lower_le_half :502`, `uniform_bot_lower_le_half :516`;
* covers `edgeSphere_cover :303`, `edgeSphere_cover_half :323`;
* deriv bridges `uniform_top_deriv_of_closedBall :343`,
  `uniform_top_deriv_of_closedBall_half :393` (+ bottom mirrors);
* M40 strips banked outside this file in `door3_rh_wiring.lean`
  (`edgeStrip_top_half_M40 :487`, `edgeStrip_bottom_half_M40 :523`).
What is added here: M40 gate/width/delta numerals (`δ = (1 / 2) / 40`),
  the closed-ball-40 to top-deriv-40 bridge instance, and strict
  `m > 1 / 2` impossibility + explicit gap numerals.
Residual (open, not forced): uniform `1 / 2` lowers over `Icc (-10) 10`
  and closed-ball sup `C = 40` on `closedBall 0 12` stay as premises;
  repo grep shows only upper bounds for `completedRiemannZeta₀`
  and no uniform edge lower at `1 / 2`, so `hTopLower`/`hTopDeriv` for M40
  are not closed here. -/

/-- M40 gate on top: `0.01 < (1 / 2) / 40`. -/
theorem m40_gate_top : (0.01 : ℝ) < (1 / 2 : ℝ) / (40 : ℝ) := by norm_num

/-- M40 width on top: `1 / 2 - (1 / 2) / 40 < 0.49`. -/
theorem m40_width_top : (1 / 2 : ℝ) - (1 / 2 : ℝ) / (40 : ℝ) < (0.49 : ℝ) := by norm_num

/-- M40 width on bottom. -/
theorem m40_width_bot : (-0.49 : ℝ) < -(1 / 2 : ℝ) + (1 / 2 : ℝ) / (40 : ℝ) := by norm_num

/-- M40 delta is positive. -/
theorem m40_delta_pos : (0 : ℝ) < (1 / 2 : ℝ) / (40 : ℝ) := by norm_num

/-- M40 delta fits the `d ≤ 1` side condition of the closed-ball bridges. -/
theorem m40_delta_le_one : (1 / 2 : ℝ) / (40 : ℝ) ≤ 1 := by norm_num

/-- M40 delta value: `(1 / 2) / 40 = 1 / 80`. -/
theorem m40_delta_eq : (1 / 2 : ℝ) / (40 : ℝ) = (1 / 80 : ℝ) := by norm_num

/-- Edge-top M40 feeder bridge: closed-ball sup `40` gives deriv `40` on the M40 strip. -/
theorem uniform_top_deriv_M40_of_closedBall
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ (40 : ℝ))
    (x : ℝ) (hx : x ∈ Set.Icc (-10 : ℝ) (10 : ℝ))
    (y : ℝ) (hy : y ∈ Set.Icc ((1 / 2 : ℝ) - (1 / 2 : ℝ) / (40 : ℝ)) (1 / 2 : ℝ)) :
    ‖deriv CentralCoverAssembly.xiShiftedEntire
      (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ (40 : ℝ) := by
  exact uniform_top_deriv_of_closedBall ((1 / 2 : ℝ) / (40 : ℝ)) (40 : ℝ)
    (by norm_num) hC x hx y hy

/-- No uniform top lower exceeds `1 / 2`. -/
theorem uniform_top_lower_not_gt_half (m : ℝ) (hgt : (1 / 2 : ℝ) < m) :
    ¬ ∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      m ≤ ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖ := by
  intro h
  have hle := uniform_top_lower_le_half m h
  linarith

/-- No uniform bottom lower exceeds `1 / 2`. -/
theorem uniform_bot_lower_not_gt_half (m : ℝ) (hgt : (1 / 2 : ℝ) < m) :
    ¬ ∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      m ≤ ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖ := by
  intro h
  have hle := uniform_bot_lower_le_half m h
  linarith

/-- Explicit gap: `51 / 100` is not a uniform top lower. -/
theorem uniform_top_lower_gap_51 :
    ¬ ∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      (51 / 100 : ℝ) ≤
        ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖ := by
  apply uniform_top_lower_not_gt_half _ (by norm_num)

/-- Explicit gap: `51 / 100` is not a uniform bottom lower. -/
theorem uniform_bot_lower_gap_51 :
    ¬ ∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      (51 / 100 : ℝ) ≤
        ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖ := by
  apply uniform_bot_lower_not_gt_half _ (by norm_num)

end Door3SliverEdge
