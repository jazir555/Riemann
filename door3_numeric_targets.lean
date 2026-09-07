import Mathlib
import rh_certificate_infra
import central_cover_assembly

namespace Door3NumericTargets

/-- Exact-rational shell for generated numerical targets.  The fields are
deliberately separated from `xiShifted`: the JSON generator samples mpmath,
so these inequalities are arithmetic checks only, pending formal analytic
enclosures for the center and derivative. -/
structure Target where
  x0 : ℚ
  x1 : ℚ
  y0 : ℚ
  y1 : ℚ
  epsilon : ℚ
  slope : ℚ
  centerLower : ℚ
  geometry_sq : ((x1 - x0) / 2)^2 + ((y1 - y0) / 2)^2 < (126 / 100 : ℚ)^2
  epsilon_pos : 0 < epsilon
  slope_nonneg : 0 ≤ slope
  budget_ok : epsilon + slope * (126 / 100 : ℚ) ≤ centerLower
  margin_pos : 0 < centerLower - (epsilon + slope * (126 / 100 : ℚ))

def targets : List Target := [
  { x0 := -10, x1 := -7.5, y0 := 0.3, y1 := 0.49,
    epsilon := 0.007424, slope := 0.051861, centerLower := 0.074243,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := -10, x1 := -7.5, y0 := 0.2, y1 := 0.4,
    epsilon := 0.007404, slope := 0.051708, centerLower := 0.074049,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := -10, x1 := -7.5, y0 := 0.1, y1 := 0.3,
    epsilon := 0.007390, slope := 0.051575, centerLower := 0.073902,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := -10, x1 := -7.5, y0 := 0.01, y1 := 0.2,
    epsilon := 0.007381, slope := 0.051480, centerLower := 0.073817,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := -8, x1 := -5.5, y0 := 0.3, y1 := 0.49,
    epsilon := 0.016680, slope := 0.068996, centerLower := 0.166806,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := -8, x1 := -5.5, y0 := 0.2, y1 := 0.4,
    epsilon := 0.016647, slope := 0.068771, centerLower := 0.166473,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := -8, x1 := -5.5, y0 := 0.1, y1 := 0.3,
    epsilon := 0.016622, slope := 0.068574, centerLower := 0.166221,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := -8, x1 := -5.5, y0 := 0.01, y1 := 0.2,
    epsilon := 0.016607, slope := 0.068434, centerLower := 0.166076,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := -6, x1 := -3.5, y0 := 0.3, y1 := 0.49,
    epsilon := 0.029339, slope := 0.070801, centerLower := 0.293397,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := -6, x1 := -3.5, y0 := 0.2, y1 := 0.4,
    epsilon := 0.029289, slope := 0.070543, centerLower := 0.292893,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := -6, x1 := -3.5, y0 := 0.1, y1 := 0.3,
    epsilon := 0.029251, slope := 0.070318, centerLower := 0.292512,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := -6, x1 := -3.5, y0 := 0.01, y1 := 0.2,
    epsilon := 0.029229, slope := 0.070158, centerLower := 0.292291,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := -4, x1 := -1.5, y0 := 0.3, y1 := 0.49,
    epsilon := 0.041853, slope := 0.069045, centerLower := 0.418534,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := -4, x1 := -1.5, y0 := 0.2, y1 := 0.4,
    epsilon := 0.041787, slope := 0.068749, centerLower := 0.417872,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := -4, x1 := -1.5, y0 := 0.1, y1 := 0.3,
    epsilon := 0.041737, slope := 0.068490, centerLower := 0.417371,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := -4, x1 := -1.5, y0 := 0.01, y1 := 0.2,
    epsilon := 0.041708, slope := 0.068305, centerLower := 0.417081,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := -2, x1 := 0.5, y0 := 0.3, y1 := 0.49,
    epsilon := 0.049247, slope := 0.045805, centerLower := 0.492475,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := -2, x1 := 0.5, y0 := 0.2, y1 := 0.4,
    epsilon := 0.049172, slope := 0.045292, centerLower := 0.491722,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := -2, x1 := 0.5, y0 := 0.1, y1 := 0.3,
    epsilon := 0.049115, slope := 0.044840, centerLower := 0.491153,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := -2, x1 := 0.5, y0 := 0.01, y1 := 0.2,
    epsilon := 0.049082, slope := 0.044517, centerLower := 0.490824,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 0, x1 := 2.5, y0 := 0.3, y1 := 0.49,
    epsilon := 0.048121, slope := 0.053980, centerLower := 0.481216,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 0, x1 := 2.5, y0 := 0.2, y1 := 0.4,
    epsilon := 0.048047, slope := 0.053551, centerLower := 0.480477,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 0, x1 := 2.5, y0 := 0.1, y1 := 0.3,
    epsilon := 0.047991, slope := 0.053176, centerLower := 0.479918,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 0, x1 := 2.5, y0 := 0.01, y1 := 0.2,
    epsilon := 0.047959, slope := 0.052907, centerLower := 0.479595,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 2, x1 := 4.5, y0 := 0.3, y1 := 0.49,
    epsilon := 0.039012, slope := 0.070634, centerLower := 0.390120,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 2, x1 := 4.5, y0 := 0.2, y1 := 0.4,
    epsilon := 0.038949, slope := 0.070364, centerLower := 0.389493,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 2, x1 := 4.5, y0 := 0.1, y1 := 0.3,
    epsilon := 0.038901, slope := 0.070129, centerLower := 0.389019,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 2, x1 := 4.5, y0 := 0.01, y1 := 0.2,
    epsilon := 0.038874, slope := 0.069961, centerLower := 0.388744,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 4, x1 := 6.5, y0 := 0.3, y1 := 0.49,
    epsilon := 0.026007, slope := 0.070768, centerLower := 0.260071,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 4, x1 := 6.5, y0 := 0.2, y1 := 0.4,
    epsilon := 0.025961, slope := 0.070514, centerLower := 0.259610,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 4, x1 := 6.5, y0 := 0.1, y1 := 0.3,
    epsilon := 0.025926, slope := 0.070292, centerLower := 0.259262,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 4, x1 := 6.5, y0 := 0.01, y1 := 0.2,
    epsilon := 0.025906, slope := 0.070134, centerLower := 0.259061,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 6, x1 := 8.5, y0 := 0.3, y1 := 0.49,
    epsilon := 0.013969, slope := 0.066101, centerLower := 0.139691,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 6, x1 := 8.5, y0 := 0.2, y1 := 0.4,
    epsilon := 0.013939, slope := 0.065896, centerLower := 0.139397,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 6, x1 := 8.5, y0 := 0.1, y1 := 0.3,
    epsilon := 0.013917, slope := 0.065716, centerLower := 0.139174,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 6, x1 := 8.5, y0 := 0.01, y1 := 0.2,
    epsilon := 0.013904, slope := 0.065588, centerLower := 0.139045,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 7.5, x1 := 10, y0 := 0.3, y1 := 0.49,
    epsilon := 0.007424, slope := 0.051861, centerLower := 0.074243,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 7.5, x1 := 10, y0 := 0.2, y1 := 0.4,
    epsilon := 0.007404, slope := 0.051708, centerLower := 0.074049,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 7.5, x1 := 10, y0 := 0.1, y1 := 0.3,
    epsilon := 0.007390, slope := 0.051575, centerLower := 0.073902,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
  { x0 := 7.5, x1 := 10, y0 := 0.01, y1 := 0.2,
    epsilon := 0.007381, slope := 0.051480, centerLower := 0.073817,
    epsilon_pos := by norm_num, slope_nonneg := by norm_num,
    geometry_sq := by norm_num,
    budget_ok := by norm_num, margin_pos := by norm_num },
]

theorem all_budgets_ok : ∀ t ∈ targets,
    t.epsilon + t.slope * (126 / 100 : ℚ) ≤ t.centerLower := by
  intro t ht
  exact t.budget_ok

theorem all_eps_pos : ∀ t ∈ targets, 0 < t.epsilon := by
  intro t ht
  exact t.epsilon_pos

theorem all_slopes_nonneg : ∀ t ∈ targets, 0 ≤ t.slope := by
  intro t ht
  exact t.slope_nonneg

theorem all_margins_pos : ∀ t ∈ targets,
    0 < t.centerLower - (t.epsilon + t.slope * (126 / 100 : ℚ)) := by
  intro t ht
  exact t.margin_pos

theorem all_geometry_sq : ∀ t ∈ targets,
    ((t.x1 - t.x0) / 2)^2 + ((t.y1 - t.y0) / 2)^2 < (126 / 100 : ℚ)^2 := by
  intro t ht
  exact t.geometry_sq

/-- Convert the exact square budget into the geometric radius bound
used by `inner_nonvanishing_of_fenced_grid_fine`. -/
theorem rect_radius_lt_of_geometry (R : CellProofEngine.Rect2D)
    (h : R.dx ^ 2 + R.dy ^ 2 < (126 / 100 : ℝ)^2) :
    R.radius < (126 / 100 : ℝ) := by
  unfold CellProofEngine.Rect2D.radius
  exact (Real.sqrt_lt' (by norm_num)).2 h

/-- Arithmetic transfer used by the real cell-fencing theorem. -/
theorem transfer_budget {ε M c radius n : ℝ}
    (hM : 0 ≤ M) (hr : radius ≤ (126 / 100 : ℝ))
    (hb : ε + M * (126 / 100 : ℝ) ≤ c) (hc : c ≤ n) :
    ε + M * radius ≤ n := by
  have hm := mul_le_mul_of_nonneg_left hr hM
  linarith

/-- Package the transferred center inequality as the exact fencing
hypothesis consumed by the Door 3 cover. -/
theorem make_cell_fencing (R : CellProofEngine.Rect2D) (ε M c : ℝ)
    (hε : 0 < ε) (hM : ∀ w, R.mem w → ‖deriv xiShifted w‖ ≤ M)
    (hM0 : 0 ≤ M) (hr : R.radius ≤ (126 / 100 : ℝ))
    (hb : ε + M * (126 / 100 : ℝ) ≤ c)
    (hc : c ≤ ‖xiShifted R.center‖) :
    CentralCoverAssembly.CellFencingHypotheses R ε M := by
  refine ⟨hε, hM, ?_⟩
  exact transfer_budget hM0 hr hb hc

/-- The strict radius estimate needed to use `budget_ok` is proved
    separately in `central_cover_assembly`; this theorem does not
    assert that `centerLower ≤ ‖xiShifted center‖`. -/
theorem target_count : targets.length = 40 := by native_decide

end Door3NumericTargets
