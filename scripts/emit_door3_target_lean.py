#!/usr/bin/env python3
"""Emit the exact-rational arithmetic shell for generated Door 3 targets."""
import json
from decimal import Decimal, ROUND_DOWN, ROUND_UP, getcontext
from pathlib import Path

getcontext().prec = 80
q = Decimal("0.000001")
j = json.loads((Path(__file__).resolve().parent.parent / "door3_numeric_targets.json").read_text())

def down(s):
    return str(Decimal(s).quantize(q, rounding=ROUND_DOWN))

def up(s):
    return str(Decimal(s).quantize(q, rounding=ROUND_UP))

lines = [
    "import Mathlib", "", "namespace Door3NumericTargets", "",
    "/-- Exact-rational shell for generated numerical targets.  The fields are",
    "deliberately separated from `xiShifted`: the JSON generator samples mpmath,",
    "so these inequalities are arithmetic checks only, pending formal analytic",
    "enclosures for the center and derivative. -/",
    "structure Target where",
    "  x0 : ℚ", "  x1 : ℚ", "  y0 : ℚ", "  y1 : ℚ",
    "  epsilon : ℚ", "  slope : ℚ", "  centerLower : ℚ",
    "  geometry_sq : ((x1 - x0) / 2)^2 + ((y1 - y0) / 2)^2 < (126 / 100 : ℚ)^2",
    "  epsilon_pos : 0 < epsilon",
    "  slope_nonneg : 0 ≤ slope",
    "  budget_ok : epsilon + slope * (126 / 100 : ℚ) ≤ centerLower",
    "  margin_pos : 0 < centerLower - (epsilon + slope * (126 / 100 : ℚ))",
    "",
    "def targets : List Target := [",
]
for r in j["rows"]:
    lines += [
        "  { x0 := %s, x1 := %s, y0 := %s, y1 := %s," % (r["x0"], r["x1"], r["y0"], r["y1"]),
        "    epsilon := %s, slope := %s, centerLower := %s," % (down(r["target_epsilon"]), up(r["target_M"]), down(r["center_norm"])),
        "    epsilon_pos := by norm_num, slope_nonneg := by norm_num,",
        "    geometry_sq := by norm_num,",
        "    budget_ok := by norm_num, margin_pos := by norm_num },",
    ]
lines += ["]", "", "theorem all_budgets_ok : ∀ t ∈ targets,",
          "    t.epsilon + t.slope * (126 / 100 : ℚ) ≤ t.centerLower := by",
          "  intro t ht", "  exact t.budget_ok", "",
          "theorem all_eps_pos : ∀ t ∈ targets, 0 < t.epsilon := by",
          "  intro t ht", "  exact t.epsilon_pos", "",
          "theorem all_slopes_nonneg : ∀ t ∈ targets, 0 ≤ t.slope := by",
          "  intro t ht", "  exact t.slope_nonneg", "",
          "theorem all_margins_pos : ∀ t ∈ targets,",
          "    0 < t.centerLower - (t.epsilon + t.slope * (126 / 100 : ℚ)) := by",
          "  intro t ht", "  exact t.margin_pos", "",
          "theorem all_geometry_sq : ∀ t ∈ targets,",
          "    ((t.x1 - t.x0) / 2)^2 + ((t.y1 - t.y0) / 2)^2 < (126 / 100 : ℚ)^2 := by",
          "  intro t ht", "  exact t.geometry_sq", "",
          "/-- Arithmetic transfer used by the real cell-fencing theorem. -/",
          "theorem transfer_budget {ε M c radius n : ℝ}",
          "    (hM : 0 ≤ M) (hr : radius ≤ (126 / 100 : ℝ))",
          "    (hb : ε + M * (126 / 100 : ℝ) ≤ c) (hc : c ≤ n) :",
          "    ε + M * radius ≤ n := by",
          "  have hm := mul_le_mul_of_nonneg_left hr hM",
          "  linarith", "",
          "/-- The strict radius estimate needed to use `budget_ok` is proved",
          "    separately in `central_cover_assembly`; this theorem does not",
          "    assert that `centerLower ≤ ‖xiShifted center‖`. -/",
          "theorem target_count : targets.length = 40 := by native_decide", "",
          "end Door3NumericTargets", ""]
out = Path(__file__).resolve().parent.parent / "door3_numeric_targets.lean"
out.write_text("\n".join(lines), encoding="utf-8")
print(f"wrote {out}")
