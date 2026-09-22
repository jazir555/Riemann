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

/-! ### (K) Bottom M40 deriv feeder mirror + gap narrowing

Grepped base:
* top feeder `uniform_top_deriv_M40_of_closedBall :708` via `uniform_top_deriv_of_closedBall :343`;
* bottom bridges `uniform_bot_deriv_of_closedBall :368`,
  `uniform_bot_deriv_of_closedBall_half :418`;
* repo grep for `uniform_bot_deriv_M40` finds only the top `:708` hit, so the
  bottom M40 feeder is open before this section.
What is added here: `m40_gate_bot`, the bottom M40 feeder via `:368`,
  and tighter gaps `501 / 1000`, `1001 / 2000` on both arms.
Residual (open, not forced): uniform `1 / 2` lowers over `Icc (-10) 10`
  and closed-ball sup `C = 40` on `closedBall 0 12` stay as premises;
  repo grep shows only upper bounds for `completedRiemannZeta₀`
  and no uniform edge lower at `1 / 2`, so `hBotLower` / `hBotDeriv` for M40
  are reduced to ball-sup-40 here, not closed. -/

/-- M40 gate on bottom: `0.01 < (1 / 2) / 40` (mirror of `m40_gate_top`). -/
theorem m40_gate_bot : (0.01 : ℝ) < (1 / 2 : ℝ) / (40 : ℝ) := by norm_num

/-- Edge-bottom M40 feeder bridge: closed-ball sup `40` gives deriv `40` on the M40 strip. -/
theorem uniform_bot_deriv_M40_of_closedBall
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ (40 : ℝ))
    (x : ℝ) (hx : x ∈ Set.Icc (-10 : ℝ) (10 : ℝ))
    (y : ℝ) (hy : y ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + (1 / 2 : ℝ) / (40 : ℝ))) :
    ‖deriv CentralCoverAssembly.xiShiftedEntire
      (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ (40 : ℝ) := by
  exact uniform_bot_deriv_of_closedBall ((1 / 2 : ℝ) / (40 : ℝ)) (40 : ℝ)
    (by norm_num) hC x hx y hy

/-- Tighter gap: `501 / 1000` is not a uniform top lower. -/
theorem uniform_top_lower_gap_501 :
    ¬ ∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      (501 / 1000 : ℝ) ≤
        ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖ := by
  apply uniform_top_lower_not_gt_half _ (by norm_num)

/-- Tighter gap: `501 / 1000` is not a uniform bottom lower. -/
theorem uniform_bot_lower_gap_501 :
    ¬ ∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      (501 / 1000 : ℝ) ≤
        ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖ := by
  apply uniform_bot_lower_not_gt_half _ (by norm_num)

/-- Tighter gap: `1001 / 2000` is not a uniform top lower. -/
theorem uniform_top_lower_gap_1001_2000 :
    ¬ ∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      (1001 / 2000 : ℝ) ≤
        ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) + Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖ := by
  apply uniform_top_lower_not_gt_half _ (by norm_num)

/-- Tighter gap: `1001 / 2000` is not a uniform bottom lower. -/
theorem uniform_bot_lower_gap_1001_2000 :
    ¬ ∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      (1001 / 2000 : ℝ) ≤
        ‖CentralCoverAssembly.xiShiftedEntire (((x : ℂ) - Complex.I * ((((1 / 2 : ℝ))) : ℂ)))‖ := by
  apply uniform_bot_lower_not_gt_half _ (by norm_num)

/-! ### (L) M40 ball-sup premise management + BALLSUP-SURVEY confirmation

Grepped specs:
* ball-sup consumers `door3_rh_wiring.lean:470-471` (`hTopDeriv40_of_ballSup40`,
  `hC : ∀ z ∈ closedBall (0:ℂ) 12, ‖xiShiftedEntire z‖ ≤ 40`),
  `:1625-1627` (`hTopDeriv1000_of_ballSup1000`, `C = 1000` retier);
* bridges banked here `uniform_top_deriv_of_closedBall :343`,
  `uniform_bot_deriv_of_closedBall :368`,
  M40 feeders `uniform_top_deriv_M40_of_closedBall :708`,
  `uniform_bot_deriv_M40_of_closedBall :768`;
* BALLSUP-SURVEY (`AGENT_INFRASTRUCTURE_GUIDE.md:6544-6550`,
  background `ses_f34f3a72b`, read-only, no edits):
  ball-12 `C = 40` INFEASIBLE by product route — poly alone `> 78` on
  ball-12 (`12.5^2 / 2`), poly·pi `≈ 56300` (`π^5.75 ≈ 722` at `Re = -11.5`),
  realistic joint `≥ 10^6`; R02-disc best `40.74` conditional / `3805.12`
  unconditional (pi-tighten `≤ 0.972` reaches `39.59` on R02-disc only,
  not ball-12); VERDICT retier MT (1000-shape exists) or abandon product
  route; smallest-next `poly_upper_closedBall12 ≤ 79` spec'd.

What is added here (all conditional, no force on `C = 40`):
* endpoint membership + necessary floor `C ≥ 1 / 2` for any valid ball-12 sup;
* sup monotonicity (any banked `C` lifts to weaker `C' ≥ C`);
* generic paired deriv feeders at arbitrary `(d, C)` and the M40 pair
  instance, so a single `hC` closes both `hTopDeriv` and `hBotDeriv`.
Residual (exact, open, not forced): closed-ball sup `C = 40` on
`closedBall 0 12` is NOT proved here — per survey it is INFEASIBLE by the
product route (poly floor `> 78 > 40`), so no `C = 40` numeral is banked;
`hTopDeriv` / `hBotDeriv` for M40 remain conditional on the open `hC`
premise; next step is the survey's retier/spec (`C = 1000` shape or
`poly_upper_closedBall12 ≤ 79`), owned elsewhere. -/

/-- Top endpoint lies in `closedBall 0 12` (norm `1 / 2 ≤ 12`). -/
theorem closedBall12_mem_endpoint_top :
    (Complex.I / 2) ∈ Metric.closedBall (0 : ℂ) 12 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  have h : ‖Complex.I / 2‖ = (1 / 2 : ℝ) := by
    rw [norm_div, Complex.norm_I]
    norm_num
  rw [h]
  norm_num

/-- Necessary floor: any valid ball-12 sup satisfies `1 / 2 ≤ C`. -/
theorem ballSup_necessary_ge_half (C : ℝ)
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    (1 / 2 : ℝ) ≤ C := by
  have hmem := closedBall12_mem_endpoint_top
  have hle := hC (Complex.I / 2) hmem
  rw [endpoint_top_norm] at hle
  exact hle

/-- Sup monotonicity: a banked `C` lifts to any weaker `C' ≥ C`. -/
theorem ballSup_mono (C : ℝ) (C' : ℝ) (hle : C ≤ C')
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C' := by
  intro z hz
  exact le_trans (hC z hz) hle

/-- Generic paired deriv feeders at arbitrary `(d, C)`: one `hC` closes both arms. -/
theorem uniform_pair_of_closedBall (d : ℝ) (C : ℝ) (hdle : d ≤ 1)
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ C) :
    (∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      ∀ (y : ℝ), y ∈ Set.Icc ((1 / 2 : ℝ) - d) (1 / 2 : ℝ) →
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ C) ∧
    (∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      ∀ (y : ℝ), y ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + d) →
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ C) := by
  constructor
  · intro x hx y hy
    exact uniform_top_deriv_of_closedBall d C hdle hC x hx y hy
  · intro x hx y hy
    exact uniform_bot_deriv_of_closedBall d C hdle hC x hx y hy

/-- M40 paired feeder: one ball-12 sup `40` closes both deriv arms at `δ = (1/2)/40`. -/
theorem uniform_M40_pair_of_closedBall
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ (40 : ℝ)) :
    (∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      ∀ (y : ℝ), y ∈ Set.Icc ((1 / 2 : ℝ) - (1 / 2 : ℝ) / (40 : ℝ)) (1 / 2 : ℝ) →
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ (40 : ℝ)) ∧
    (∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      ∀ (y : ℝ), y ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + (1 / 2 : ℝ) / (40 : ℝ)) →
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ (40 : ℝ)) := by
  constructor
  · intro x hx y hy
    exact uniform_top_deriv_M40_of_closedBall hC x hx y hy
  · intro x hx y hy
    exact uniform_bot_deriv_M40_of_closedBall hC x hx y hy

/-! ### (M) M1000 pair-closer mirror + mono lift chain

Grepped specs:
* pair closers `door3_sliver_edge.lean:838-885`
  (`closedBall12_mem_endpoint_top`, `ballSup_necessary_ge_half`, `ballSup_mono`,
  `uniform_pair_of_closedBall`, `uniform_M40_pair_of_closedBall`);
* wiring `door3_rh_wiring.lean:1625-1633` (`hTopDeriv1000_of_ballSup1000`,
  `C = 1000` retier via `uniform_top_deriv_of_closedBall` at `d = (1/2)/1000`);
* `C = 40` confirmed infeasible per (L) survey (poly floor `> 78 > 40`).

What is added here (all conditional, no force on `C = 1000`):
* M1000 delta numerals + top/bottom M1000 feeder bridges via `:343` / `:368`;
* M1000 paired feeder closing both deriv arms from one ball-12 sup `1000`;
* mono lifts `40 -> 1000` and `79 -> 1000` via `ballSup_mono`, plus
  `79`-premise and `40`-premise pair closers, so the
  `poly_upper_closedBall12 <= 79` spec feeds the `1000` shape.
Residual (exact, open, not forced): closed-ball sup `C = 1000` on
`closedBall 0 12` is NOT proved here; `hTopDeriv` / `hBotDeriv` for M1000 remain
conditional on the open `hC` premise; the smallest-next numeral
`poly_upper_closedBall12 <= 79` is owned elsewhere and enters here only as an
explicit premise via the `79 -> 1000` lift. -/

/-- M1000 delta fits the `d <= 1` side condition of the closed-ball bridges. -/
theorem m1000_delta_le_one : (1 / 2 : ℝ) / (1000 : ℝ) ≤ 1 := by norm_num

/-- M1000 delta is positive. -/
theorem m1000_delta_pos : (0 : ℝ) < (1 / 2 : ℝ) / (1000 : ℝ) := by norm_num

/-- Edge-top M1000 feeder bridge: closed-ball sup `1000` gives deriv `1000`. -/
theorem uniform_top_deriv_M1000_of_closedBall
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ (1000 : ℝ))
    (x : ℝ) (hx : x ∈ Set.Icc (-10 : ℝ) (10 : ℝ))
    (y : ℝ) (hy : y ∈ Set.Icc ((1 / 2 : ℝ) - (1 / 2 : ℝ) / (1000 : ℝ)) (1 / 2 : ℝ)) :
    ‖deriv CentralCoverAssembly.xiShiftedEntire
      (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ (1000 : ℝ) := by
  exact uniform_top_deriv_of_closedBall ((1 / 2 : ℝ) / (1000 : ℝ)) (1000 : ℝ)
    (by norm_num) hC x hx y hy

/-- Edge-bottom M1000 feeder bridge: closed-ball sup `1000` gives deriv `1000`. -/
theorem uniform_bot_deriv_M1000_of_closedBall
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ (1000 : ℝ))
    (x : ℝ) (hx : x ∈ Set.Icc (-10 : ℝ) (10 : ℝ))
    (y : ℝ) (hy : y ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + (1 / 2 : ℝ) / (1000 : ℝ))) :
    ‖deriv CentralCoverAssembly.xiShiftedEntire
      (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ (1000 : ℝ) := by
  exact uniform_bot_deriv_of_closedBall ((1 / 2 : ℝ) / (1000 : ℝ)) (1000 : ℝ)
    (by norm_num) hC x hx y hy

/-- M1000 paired feeder: one ball-12 sup `1000` closes both deriv arms. -/
theorem uniform_M1000_pair_of_closedBall
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ (1000 : ℝ)) :
    (∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      ∀ (y : ℝ), y ∈ Set.Icc ((1 / 2 : ℝ) - (1 / 2 : ℝ) / (1000 : ℝ)) (1 / 2 : ℝ) →
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ (1000 : ℝ)) ∧
    (∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      ∀ (y : ℝ), y ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + (1 / 2 : ℝ) / (1000 : ℝ)) →
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ (1000 : ℝ)) := by
  constructor
  · intro x hx y hy
    exact uniform_top_deriv_M1000_of_closedBall hC x hx y hy
  · intro x hx y hy
    exact uniform_bot_deriv_M1000_of_closedBall hC x hx y hy

/-- Mono lift: ball-12 sup `40` lifts to ball-12 sup `1000`. -/
theorem ballSup40_to_ballSup1000
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ (40 : ℝ)) :
    ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ (1000 : ℝ) := by
  intro z hz
  exact ballSup_mono (40 : ℝ) (1000 : ℝ) (by norm_num) hC z hz

/-- Mono lift: ball-12 sup `79` lifts to ball-12 sup `1000`. -/
theorem ballSup79_to_ballSup1000
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ (79 : ℝ)) :
    ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ (1000 : ℝ) := by
  intro z hz
  exact ballSup_mono (79 : ℝ) (1000 : ℝ) (by norm_num) hC z hz

/-- M1000 pair from a `79` sup: `poly_upper_closedBall12 <= 79` shape feeds `1000`. -/
theorem uniform_M1000_pair_of_ballSup79
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ (79 : ℝ)) :
    (∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      ∀ (y : ℝ), y ∈ Set.Icc ((1 / 2 : ℝ) - (1 / 2 : ℝ) / (1000 : ℝ)) (1 / 2 : ℝ) →
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ (1000 : ℝ)) ∧
    (∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      ∀ (y : ℝ), y ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + (1 / 2 : ℝ) / (1000 : ℝ)) →
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ (1000 : ℝ)) := by
  have h1000 := ballSup79_to_ballSup1000 hC
  exact uniform_M1000_pair_of_closedBall h1000

/-- M1000 pair from a `40` sup (kept for the infeasible-tier chain). -/
theorem uniform_M1000_pair_of_ballSup40
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 12 →
      ‖CentralCoverAssembly.xiShiftedEntire z‖ ≤ (40 : ℝ)) :
    (∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      ∀ (y : ℝ), y ∈ Set.Icc ((1 / 2 : ℝ) - (1 / 2 : ℝ) / (1000 : ℝ)) (1 / 2 : ℝ) →
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ (1000 : ℝ)) ∧
    (∀ (x : ℝ), x ∈ Set.Icc (-10 : ℝ) (10 : ℝ) →
      ∀ (y : ℝ), y ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + (1 / 2 : ℝ) / (1000 : ℝ)) →
        ‖deriv CentralCoverAssembly.xiShiftedEntire
          (((x : ℂ) + Complex.I * (((y : ℝ)) : ℂ)))‖ ≤ (1000 : ℝ)) := by
  have h1000 := ballSup40_to_ballSup1000 hC
  exact uniform_M1000_pair_of_closedBall h1000

end Door3SliverEdge

/-! ### (N) Poly sup on closedBall 12 for M1000 closers

Grepped:
* M1000 block `door3_sliver_edge.lean:931-1004` (`uniform_top_deriv_M1000_of_closedBall`,
  `uniform_bot_deriv_M1000_of_closedBall`, `uniform_M1000_pair_of_closedBall`,
  `ballSup40_to_ballSup1000`, `ballSup79_to_ballSup1000`,
  `uniform_M1000_pair_of_ballSup79`, `uniform_M1000_pair_of_ballSup40`);
* poly shape `central_cover_assembly.lean:6328` (`polyOf s = s * (s - 1) / 2`);
* banked poly uppers `central_cover_assembly.lean:6360` (`poly_upper_R02_disc <= 42`),
  edge rects `<= 56` (`edgeS00_poly_upper_rect :6699` and siblings),
  generic lower `edgeLower_poly_upper_generic :8167`.

What is banked here (honest triangle route, no product claim):
* `poly_upper_closedBall12_le78`: for `s` in `closedBall 0 12`,
  `‖polyOf s‖ <= 78` via `‖s‖ <= 12`, `‖s - 1‖ <= 13`, `norm_mul`, `norm_div`;
  `12 * 13 / 2 = 78`;
* `poly_upper_closedBall12`: the `<= 79` form feeding the `79 -> 1000` lift shape.

Residual (exact, open, not forced):
* poly `<= 79` alone does not give `‖xiShiftedEntire z‖ <= 79` or `<= 1000`
  on `closedBall 0 12`; the full product needs pi / Gamma / zeta uppers
  on ball-12, which are not banked here;
* M1000 deriv closers stay conditional on the `hC : ‖xiShiftedEntire‖ <= 79`
  premise via `uniform_M1000_pair_of_ballSup79`; poly supplies only one factor.
-/

namespace Door3SliverEdge

/-- Poly sup `78` on `closedBall 0 12` via triangle (`12 * 13 / 2`). -/
theorem poly_upper_closedBall12_le78 {s : ℂ}
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

/-- Poly sup `79` on `closedBall 0 12` (the shape feeding the `79 -> 1000` lift). -/
theorem poly_upper_closedBall12 {s : ℂ}
    (hs : s ∈ Metric.closedBall (0 : ℂ) 12) :
    ‖CentralCoverAssembly.polyOf s‖ ≤ (79 : ℝ) := by
  have h78 := poly_upper_closedBall12_le78 hs
  have h7879 : (78 : ℝ) ≤ (79 : ℝ) := by norm_num
  exact le_trans h78 h7879

end Door3SliverEdge

/-! ### (O) Pi-factor upper on closedBall 12 + joint poly-pi sup

Grepped before writing:
* poly79 block `door3_sliver_edge.lean:1049-1084` (`poly_upper_closedBall12_le78`
  triangle `12 * 13 / 2 = 78`; `poly_upper_closedBall12` lift to `79`);
* pi shapes `central_cover_assembly.lean:6331` (`piOf s = (Real.pi : ℂ) ^ (-(s/2))`),
  `:6396` (`pi_upper_R02_disc`, needs `0.05 ≤ s.re`, inapplicable on ball-12
  where `s.re` reaches `-12`), and `door3_deriv_certs.lean:419/492/504`
  (`fPi_shape`, norm equation, sup `≤ 4` on the R00 `s`-image with
  `s.re ≥ -1.61`, likewise inapplicable here).

What is banked here (same-domain `closedBall 0 12`, rpow route mirroring the
banked pi proofs; the `‖s/2‖ ≤ 6` detour is not needed):
* `ball12_re_bounds`: `s.re ∈ [-12, 12]` on `closedBall 0 12`;
* `piOf_norm_eq_ball12`: `‖piOf s‖ = π ^ (-s.re/2)`;
* `piOf_upper_closedBall12`: `‖piOf s‖ ≤ 4096` on `closedBall 0 12`
  (`-s.re/2 ≤ 6`, `π ^ e ≤ π ^ 6 ≤ 4 ^ 6 = 4096`);
* `poly_pi_upper_closedBall12`: joint two-factor
  `‖polyOf s * piOf s‖ ≤ 319488` (`78 * 4096`) on `closedBall 0 12`.

Value-or-gap: two of four product factors now have same-domain ball-12 uppers
(`78` poly, `4096` pi, joint `319488`). No claim is made here about
`‖xiShiftedEntire‖` on ball-12.
Residual (exact, open, not forced): Gamma / zeta uppers on ball-12 are not
banked here — `s = 0` puts `s/2 = 0` at the Gamma pole and `s = 1` is the zeta
pole, both points lying in `closedBall 0 12`, so uniform uppers on the full
closed ball are not supplied and would need punctured domains; the M1000
deriv closers stay conditional on the open `hC` premise via
`uniform_M1000_pair_of_ballSup79`.
-/

namespace Door3SliverEdge

/-- Real-part bounds on `closedBall 0 12`. -/
theorem ball12_re_bounds {s : ℂ} (hs : s ∈ Metric.closedBall (0 : ℂ) 12) :
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

/-- Norm of the pi factor: `‖π ^ (-(s/2))‖ = π ^ (-s.re/2)`. -/
theorem piOf_norm_eq_ball12 (s : ℂ) :
    ‖CentralCoverAssembly.piOf s‖ = Real.pi ^ (-(s.re) / 2) := by
  unfold CentralCoverAssembly.piOf
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos _]
  congr 1
  have h2 : (s / 2).re = s.re / 2 := by rw [Complex.div_ofNat_re]
  have hneg : (-(s / 2)).re = -((s / 2).re) := Complex.neg_re _
  rw [hneg, h2]
  ring

/-- Pi-factor upper `4096` on `closedBall 0 12`. -/
theorem piOf_upper_closedBall12 {s : ℂ}
    (hs : s ∈ Metric.closedBall (0 : ℂ) 12) :
    ‖CentralCoverAssembly.piOf s‖ ≤ (4096 : ℝ) := by
  rw [piOf_norm_eq_ball12]
  obtain ⟨hlo, _⟩ := ball12_re_bounds hs
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

/-- Joint poly-pi sup `319488` on `closedBall 0 12` (`78 * 4096`). -/
theorem poly_pi_upper_closedBall12 {s : ℂ}
    (hs : s ∈ Metric.closedBall (0 : ℂ) 12) :
    ‖CentralCoverAssembly.polyOf s * CentralCoverAssembly.piOf s‖ ≤ (319488 : ℝ) := by
  have hpoly := poly_upper_closedBall12_le78 hs
  have hpi := piOf_upper_closedBall12 hs
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

end Door3SliverEdge
