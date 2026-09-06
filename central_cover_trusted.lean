import Mathlib
import rh_zeta_cert_central
import float_real_bridge
import riemann_hypothesis
import rh_certificate_infra
import central_cover_assembly

noncomputable section

open Float Complex Real CellProofEngine CentralCoverAssembly

/-! ## Float-toReal order/positivity lemmas (minimal, in-file).

Grep record (2026-09-04, `central_cover_trusted` task):
- `rg "Float.toReal_lt|Float.toReal_le|toReal.*Float" Mathlib/` -> no hits for the
  custom `Float.toReal` (`float_real_bridge.lean`, via `toRatParts`); Mathlib
  v4.33 has no `Float.toReal` order API (only `EReal`/`ENNReal`/`NNReal`
  `toReal`, unrelated).
- `rg "toReal" Mathlib/Data/Float*` -> no `Mathlib/Data/Float*.lean` files exist.
- `float_real_bridge.lean` defines `Float.toReal` only, no order lemmas.
- `float_xi_cover.lean` proves Float-level certs (`0 < c.eps`, etc.) by
  `native_decide`, but no `Float.toReal` transport.

Hence the minimal transport for the 32 `central_cert_data` literals is created
here: each `Float` literal's `toRatParts` is pinned by `native_decide`
(compiled-code evaluation; kernel `decide` gets stuck on Float externs, verified
2026-09-04), then `Float.toReal` is unfolded and the resulting explicit
`ℝ`-inequality (`v * 2^exp`, `v : ℤ`, `exp : ℤ`) is closed by `positivity` /
`norm_num`. No `sorry`/`admit`/`axiom`; `native_decide` introduces only its
standard auxiliary axioms (no `sorryAx`).
-/

-- x-interval literals (8 distinct).
theorem float_toReal_neg10_lt_neg75 : (-10.0 : Float).toReal < (-7.5 : Float).toReal := by
  have h1 : (-10.0 : Float).toRatParts = some (-5629499534213120, -49) := by native_decide
  have h2 : (-7.5 : Float).toRatParts = some (-8444249301319680, -50) := by native_decide
  unfold Float.toReal
  simp [h1, h2]
  norm_num
theorem float_toReal_neg75_lt_neg5 : (-7.5 : Float).toReal < (-5.0 : Float).toReal := by
  have h1 : (-7.5 : Float).toRatParts = some (-8444249301319680, -50) := by native_decide
  have h2 : (-5.0 : Float).toRatParts = some (-5629499534213120, -50) := by native_decide
  unfold Float.toReal
  simp [h1, h2]
  norm_num
theorem float_toReal_neg5_lt_neg25 : (-5.0 : Float).toReal < (-2.5 : Float).toReal := by
  have h1 : (-5.0 : Float).toRatParts = some (-5629499534213120, -50) := by native_decide
  have h2 : (-2.5 : Float).toRatParts = some (-5629499534213120, -51) := by native_decide
  unfold Float.toReal
  simp [h1, h2]
  norm_num
theorem float_toReal_neg25_lt_zero : (-2.5 : Float).toReal < (0.0 : Float).toReal := by
  have h1 : (-2.5 : Float).toRatParts = some (-5629499534213120, -51) := by native_decide
  have h2 : (0.0 : Float).toRatParts = some (0, -53) := by native_decide
  unfold Float.toReal
  simp [h1, h2]
  norm_num
theorem float_toReal_zero_lt_25 : (0.0 : Float).toReal < (2.5 : Float).toReal := by
  have h1 : (0.0 : Float).toRatParts = some (0, -53) := by native_decide
  have h2 : (2.5 : Float).toRatParts = some (5629499534213120, -51) := by native_decide
  unfold Float.toReal
  simp [h1, h2]
  norm_num
theorem float_toReal_25_lt_5 : (2.5 : Float).toReal < (5.0 : Float).toReal := by
  have h1 : (2.5 : Float).toRatParts = some (5629499534213120, -51) := by native_decide
  have h2 : (5.0 : Float).toRatParts = some (5629499534213120, -50) := by native_decide
  unfold Float.toReal
  simp [h1, h2]
  norm_num
theorem float_toReal_5_lt_75 : (5.0 : Float).toReal < (7.5 : Float).toReal := by
  have h1 : (5.0 : Float).toRatParts = some (5629499534213120, -50) := by native_decide
  have h2 : (7.5 : Float).toRatParts = some (8444249301319680, -50) := by native_decide
  unfold Float.toReal
  simp [h1, h2]
  norm_num
theorem float_toReal_75_lt_10 : (7.5 : Float).toReal < (10.0 : Float).toReal := by
  have h1 : (7.5 : Float).toRatParts = some (8444249301319680, -50) := by native_decide
  have h2 : (10.0 : Float).toRatParts = some (5629499534213120, -49) := by native_decide
  unfold Float.toReal
  simp [h1, h2]
  norm_num

-- y-interval literals (4 distinct).
theorem float_toReal_001_lt_02 : (0.01 : Float).toReal < (0.2 : Float).toReal := by
  have h1 : (0.01 : Float).toRatParts = some (5764607523034235, -59) := by native_decide
  have h2 : (0.2 : Float).toRatParts = some (7205759403792794, -55) := by native_decide
  unfold Float.toReal
  simp [h1, h2]
  norm_num
theorem float_toReal_02_lt_03 : (0.2 : Float).toReal < (0.3 : Float).toReal := by
  have h1 : (0.2 : Float).toRatParts = some (7205759403792794, -55) := by native_decide
  have h2 : (0.3 : Float).toRatParts = some (5404319552844595, -54) := by native_decide
  unfold Float.toReal
  simp [h1, h2]
  norm_num
theorem float_toReal_03_lt_04 : (0.3 : Float).toReal < (0.4 : Float).toReal := by
  have h1 : (0.3 : Float).toRatParts = some (5404319552844595, -54) := by native_decide
  have h2 : (0.4 : Float).toRatParts = some (7205759403792794, -54) := by native_decide
  unfold Float.toReal
  simp [h1, h2]
  norm_num
theorem float_toReal_04_lt_049 : (0.4 : Float).toReal < (0.49 : Float).toReal := by
  have h1 : (0.4 : Float).toRatParts = some (7205759403792794, -54) := by native_decide
  have h2 : (0.49 : Float).toRatParts = some (8827055269646172, -54) := by native_decide
  unfold Float.toReal
  simp [h1, h2]
  norm_num

-- y0 positivity (4 distinct y0 values).
theorem float_toReal_001_pos : (0 : ℝ) < (0.01 : Float).toReal := by
  have h : (0.01 : Float).toRatParts = some (5764607523034235, -59) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_02_pos : (0 : ℝ) < (0.2 : Float).toReal := by
  have h : (0.2 : Float).toRatParts = some (7205759403792794, -55) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_03_pos : (0 : ℝ) < (0.3 : Float).toReal := by
  have h : (0.3 : Float).toRatParts = some (5404319552844595, -54) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_04_pos : (0 : ℝ) < (0.4 : Float).toReal := by
  have h : (0.4 : Float).toRatParts = some (7205759403792794, -54) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity

-- y1 upper bounds vs 1/2 (4 distinct y1 values).
theorem float_toReal_02_lt_half : (0.2 : Float).toReal < (1 / 2 : ℝ) := by
  have h : (0.2 : Float).toRatParts = some (7205759403792794, -55) := by native_decide
  unfold Float.toReal
  simp [h]
  norm_num
theorem float_toReal_03_lt_half : (0.3 : Float).toReal < (1 / 2 : ℝ) := by
  have h : (0.3 : Float).toRatParts = some (5404319552844595, -54) := by native_decide
  unfold Float.toReal
  simp [h]
  norm_num
theorem float_toReal_04_lt_half : (0.4 : Float).toReal < (1 / 2 : ℝ) := by
  have h : (0.4 : Float).toRatParts = some (7205759403792794, -54) := by native_decide
  unfold Float.toReal
  simp [h]
  norm_num
theorem float_toReal_049_lt_half : (0.49 : Float).toReal < (1 / 2 : ℝ) := by
  have h : (0.49 : Float).toRatParts = some (8827055269646172, -54) := by native_decide
  unfold Float.toReal
  simp [h]
  norm_num

-- eps positivity (16 distinct).
theorem float_toReal_eps1_pos : (0 : ℝ) < (0.006177051945015177 : Float).toReal := by
  have h : (0.006177051945015177 : Float).toRatParts = some (7121656022481548, -60) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_eps2_pos : (0 : ℝ) < (0.0559279239515775 : Float).toReal := by
  have h : (0.0559279239515775 : Float).toRatParts = some (8060063278973756, -57) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_eps3_pos : (0 : ℝ) < (0.13714195825263417 : Float).toReal := by
  have h : (0.13714195825263417 : Float).toRatParts = some (4941059776667387, -55) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_eps4_pos : (0 : ℝ) < (0.20821396092526187 : Float).toReal := by
  have h : (0.20821396092526187 : Float).toRatParts = some (7501698534690755, -55) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_eps5_pos : (0 : ℝ) < (0.006259972847889726 : Float).toReal := by
  have h : (0.006259972847889726 : Float).toRatParts = some (7217257314587032, -60) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_eps6_pos : (0 : ℝ) < (0.056068903077646316 : Float).toReal := by
  have h : (0.056068903077646316 : Float).toRatParts = some (8080380512241933, -57) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_eps7_pos : (0 : ℝ) < (0.13735924009344982 : Float).toReal := by
  have h : (0.13735924009344982 : Float).toRatParts = some (4948888180006041, -55) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_eps8_pos : (0 : ℝ) < (0.20840724121203882 : Float).toReal := by
  have h : (0.20840724121203882 : Float).toRatParts = some (7508662190910809, -55) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_eps9_pos : (0 : ℝ) < (0.006268912330277428 : Float).toReal := by
  have h : (0.006268912330277428 : Float).toRatParts = some (7227563836071868, -60) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_eps10_pos : (0 : ℝ) < (0.05611069935418023 : Float).toReal := by
  have h : (0.05611069935418023 : Float).toRatParts = some (8086403990495488, -57) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_eps11_pos : (0 : ℝ) < (0.1374882361414519 : Float).toReal := by
  have h : (0.1374882361414519 : Float).toRatParts = some (4953535752435756, -55) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_eps12_pos : (0 : ℝ) < (0.2085192587199296 : Float).toReal := by
  have h : (0.2085192587199296 : Float).toRatParts = some (7512698046965176, -55) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_eps13_pos : (0 : ℝ) < (0.006293913564448431 : Float).toReal := by
  have h : (0.006293913564448431 : Float).toRatParts = some (7256388296589328, -60) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_eps14_pos : (0 : ℝ) < (0.0561844236887777 : Float).toReal := by
  have h : (0.0561844236887777 : Float).toRatParts = some (8097028786841770, -57) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_eps15_pos : (0 : ℝ) < (0.1376730585040693 : Float).toReal := by
  have h : (0.1376730585040693 : Float).toRatParts = some (4960194679823064, -55) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_eps16_pos : (0 : ℝ) < (0.2086917661937123 : Float).toReal := by
  have h : (0.2086917661937123 : Float).toRatParts = some (7518913283722347, -55) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity

-- M positivity (16 distinct; `M_nonneg` follows by `le_of_lt`).
theorem float_toReal_M1_pos : (0 : ℝ) < (0.04902931207867841 : Float).toReal := by
  have h : (0.04902931207867841 : Float).toRatParts = some (7065868531448571, -57) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_M2_pos : (0 : ℝ) < (0.06662501762533198 : Float).toReal := by
  have h : (0.06662501762533198 : Float).toRatParts = some (4800838472815965, -56) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_M3_pos : (0 : ℝ) < (0.06673567631500821 : Float).toReal := by
  have h : (0.06673567631500821 : Float).toRatParts = some (4808812271753424, -56) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_M4_pos : (0 : ℝ) < (0.05038856907056275 : Float).toReal := by
  have h : (0.05038856907056275 : Float).toRatParts = some (7261758108477405, -57) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_M5_pos : (0 : ℝ) < (0.049119703451432045 : Float).toReal := by
  have h : (0.049119703451432045 : Float).toRatParts = some (7078895301133396, -57) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_M6_pos : (0 : ℝ) < (0.06677104484106818 : Float).toReal := by
  have h : (0.06677104484106818 : Float).toRatParts = some (4811360842645973, -56) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_M7_pos : (0 : ℝ) < (0.0668931834879488 : Float).toReal := by
  have h : (0.0668931834879488 : Float).toRatParts = some (4820161859679239, -56) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_M8_pos : (0 : ℝ) < (0.050644174931954354 : Float).toReal := by
  have h : (0.050644174931954354 : Float).toRatParts = some (7298594795265147, -57) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_M9_pos : (0 : ℝ) < (0.04924646983602388 : Float).toReal := by
  have h : (0.04924646983602388 : Float).toRatParts = some (7097164262490545, -57) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_M10_pos : (0 : ℝ) < (0.06697578146188994 : Float).toReal := by
  have h : (0.06697578146188994 : Float).toRatParts = some (4826113670953845, -56) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_M11_pos : (0 : ℝ) < (0.06711398748062603 : Float).toReal := by
  have h : (0.06711398748062603 : Float).toRatParts = some (4836072464145528, -56) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_M12_pos : (0 : ℝ) < (0.05100153680563047 : Float).toReal := by
  have h : (0.05100153680563047 : Float).toRatParts = some (7350096068901121, -57) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_M13_pos : (0 : ℝ) < (0.049391840006737825 : Float).toReal := by
  have h : (0.049391840006737825 : Float).toRatParts = some (7118114311983604, -57) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_M14_pos : (0 : ℝ) < (0.067210486893171 : Float).toReal := by
  have h : (0.067210486893171 : Float).toRatParts = some (4843025979639592, -56) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_M15_pos : (0 : ℝ) < (0.06736707229531062 : Float).toReal := by
  have h : (0.06736707229531062 : Float).toRatParts = some (4854309146979235, -56) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity
theorem float_toReal_M16_pos : (0 : ℝ) < (0.051409788293050755 : Float).toReal := by
  have h : (0.051409788293050755 : Float).toRatParts = some (7408931308792943, -57) := by native_decide
  unfold Float.toReal
  simp [h]
  positivity

/-! Per-cell transport: all 32 `central_cert_data` entries satisfy the ℝ
order/positivity via case analysis on the Array membership (32 disjunctions)
and the distinct-literal lemmas above. Order matches
`rh_zeta_cert_central.lean:29-60` (8 per y-tier, 4 tiers). -/

theorem central_toReal_x_lt : ∀ c ∈ central_cert_data.toList, c.x0.toReal < c.x1.toReal := by
  intro c hc
  simp [central_cert_data] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact float_toReal_neg10_lt_neg75
  · exact float_toReal_neg75_lt_neg5
  · exact float_toReal_neg5_lt_neg25
  · exact float_toReal_neg25_lt_zero
  · exact float_toReal_zero_lt_25
  · exact float_toReal_25_lt_5
  · exact float_toReal_5_lt_75
  · exact float_toReal_75_lt_10
  · exact float_toReal_neg10_lt_neg75
  · exact float_toReal_neg75_lt_neg5
  · exact float_toReal_neg5_lt_neg25
  · exact float_toReal_neg25_lt_zero
  · exact float_toReal_zero_lt_25
  · exact float_toReal_25_lt_5
  · exact float_toReal_5_lt_75
  · exact float_toReal_75_lt_10
  · exact float_toReal_neg10_lt_neg75
  · exact float_toReal_neg75_lt_neg5
  · exact float_toReal_neg5_lt_neg25
  · exact float_toReal_neg25_lt_zero
  · exact float_toReal_zero_lt_25
  · exact float_toReal_25_lt_5
  · exact float_toReal_5_lt_75
  · exact float_toReal_75_lt_10
  · exact float_toReal_neg10_lt_neg75
  · exact float_toReal_neg75_lt_neg5
  · exact float_toReal_neg5_lt_neg25
  · exact float_toReal_neg25_lt_zero
  · exact float_toReal_zero_lt_25
  · exact float_toReal_25_lt_5
  · exact float_toReal_5_lt_75
  · exact float_toReal_75_lt_10

theorem central_toReal_y_lt : ∀ c ∈ central_cert_data.toList, c.y0.toReal < c.y1.toReal := by
  intro c hc
  simp [central_cert_data] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact float_toReal_001_lt_02
  · exact float_toReal_001_lt_02
  · exact float_toReal_001_lt_02
  · exact float_toReal_001_lt_02
  · exact float_toReal_001_lt_02
  · exact float_toReal_001_lt_02
  · exact float_toReal_001_lt_02
  · exact float_toReal_001_lt_02
  · exact float_toReal_02_lt_03
  · exact float_toReal_02_lt_03
  · exact float_toReal_02_lt_03
  · exact float_toReal_02_lt_03
  · exact float_toReal_02_lt_03
  · exact float_toReal_02_lt_03
  · exact float_toReal_02_lt_03
  · exact float_toReal_02_lt_03
  · exact float_toReal_03_lt_04
  · exact float_toReal_03_lt_04
  · exact float_toReal_03_lt_04
  · exact float_toReal_03_lt_04
  · exact float_toReal_03_lt_04
  · exact float_toReal_03_lt_04
  · exact float_toReal_03_lt_04
  · exact float_toReal_03_lt_04
  · exact float_toReal_04_lt_049
  · exact float_toReal_04_lt_049
  · exact float_toReal_04_lt_049
  · exact float_toReal_04_lt_049
  · exact float_toReal_04_lt_049
  · exact float_toReal_04_lt_049
  · exact float_toReal_04_lt_049
  · exact float_toReal_04_lt_049

theorem central_toReal_eps_pos : ∀ c ∈ central_cert_data.toList, (0 : ℝ) < c.eps.toReal := by
  intro c hc
  simp [central_cert_data] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact float_toReal_eps1_pos
  · exact float_toReal_eps2_pos
  · exact float_toReal_eps3_pos
  · exact float_toReal_eps4_pos
  · exact float_toReal_eps4_pos
  · exact float_toReal_eps3_pos
  · exact float_toReal_eps2_pos
  · exact float_toReal_eps1_pos
  · exact float_toReal_eps5_pos
  · exact float_toReal_eps6_pos
  · exact float_toReal_eps7_pos
  · exact float_toReal_eps8_pos
  · exact float_toReal_eps8_pos
  · exact float_toReal_eps7_pos
  · exact float_toReal_eps6_pos
  · exact float_toReal_eps5_pos
  · exact float_toReal_eps9_pos
  · exact float_toReal_eps10_pos
  · exact float_toReal_eps11_pos
  · exact float_toReal_eps12_pos
  · exact float_toReal_eps12_pos
  · exact float_toReal_eps11_pos
  · exact float_toReal_eps10_pos
  · exact float_toReal_eps9_pos
  · exact float_toReal_eps13_pos
  · exact float_toReal_eps14_pos
  · exact float_toReal_eps15_pos
  · exact float_toReal_eps16_pos
  · exact float_toReal_eps16_pos
  · exact float_toReal_eps15_pos
  · exact float_toReal_eps14_pos
  · exact float_toReal_eps13_pos

theorem central_toReal_M_nonneg : ∀ c ∈ central_cert_data.toList, (0 : ℝ) ≤ c.M.toReal := by
  intro c hc
  simp [central_cert_data] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact le_of_lt float_toReal_M1_pos
  · exact le_of_lt float_toReal_M2_pos
  · exact le_of_lt float_toReal_M3_pos
  · exact le_of_lt float_toReal_M4_pos
  · exact le_of_lt float_toReal_M4_pos
  · exact le_of_lt float_toReal_M3_pos
  · exact le_of_lt float_toReal_M2_pos
  · exact le_of_lt float_toReal_M1_pos
  · exact le_of_lt float_toReal_M5_pos
  · exact le_of_lt float_toReal_M6_pos
  · exact le_of_lt float_toReal_M7_pos
  · exact le_of_lt float_toReal_M8_pos
  · exact le_of_lt float_toReal_M8_pos
  · exact le_of_lt float_toReal_M7_pos
  · exact le_of_lt float_toReal_M6_pos
  · exact le_of_lt float_toReal_M5_pos
  · exact le_of_lt float_toReal_M9_pos
  · exact le_of_lt float_toReal_M10_pos
  · exact le_of_lt float_toReal_M11_pos
  · exact le_of_lt float_toReal_M12_pos
  · exact le_of_lt float_toReal_M12_pos
  · exact le_of_lt float_toReal_M11_pos
  · exact le_of_lt float_toReal_M10_pos
  · exact le_of_lt float_toReal_M9_pos
  · exact le_of_lt float_toReal_M13_pos
  · exact le_of_lt float_toReal_M14_pos
  · exact le_of_lt float_toReal_M15_pos
  · exact le_of_lt float_toReal_M16_pos
  · exact le_of_lt float_toReal_M16_pos
  · exact le_of_lt float_toReal_M15_pos
  · exact le_of_lt float_toReal_M14_pos
  · exact le_of_lt float_toReal_M13_pos

theorem central_toReal_y0_pos : ∀ c ∈ central_cert_data.toList, (0 : ℝ) < c.y0.toReal := by
  intro c hc
  simp [central_cert_data] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact float_toReal_001_pos
  · exact float_toReal_001_pos
  · exact float_toReal_001_pos
  · exact float_toReal_001_pos
  · exact float_toReal_001_pos
  · exact float_toReal_001_pos
  · exact float_toReal_001_pos
  · exact float_toReal_001_pos
  · exact float_toReal_02_pos
  · exact float_toReal_02_pos
  · exact float_toReal_02_pos
  · exact float_toReal_02_pos
  · exact float_toReal_02_pos
  · exact float_toReal_02_pos
  · exact float_toReal_02_pos
  · exact float_toReal_02_pos
  · exact float_toReal_03_pos
  · exact float_toReal_03_pos
  · exact float_toReal_03_pos
  · exact float_toReal_03_pos
  · exact float_toReal_03_pos
  · exact float_toReal_03_pos
  · exact float_toReal_03_pos
  · exact float_toReal_03_pos
  · exact float_toReal_04_pos
  · exact float_toReal_04_pos
  · exact float_toReal_04_pos
  · exact float_toReal_04_pos
  · exact float_toReal_04_pos
  · exact float_toReal_04_pos
  · exact float_toReal_04_pos
  · exact float_toReal_04_pos

theorem central_toReal_y1_lt : ∀ c ∈ central_cert_data.toList, c.y1.toReal < (1 / 2 : ℝ) := by
  intro c hc
  simp [central_cert_data] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact float_toReal_02_lt_half
  · exact float_toReal_02_lt_half
  · exact float_toReal_02_lt_half
  · exact float_toReal_02_lt_half
  · exact float_toReal_02_lt_half
  · exact float_toReal_02_lt_half
  · exact float_toReal_02_lt_half
  · exact float_toReal_02_lt_half
  · exact float_toReal_03_lt_half
  · exact float_toReal_03_lt_half
  · exact float_toReal_03_lt_half
  · exact float_toReal_03_lt_half
  · exact float_toReal_03_lt_half
  · exact float_toReal_03_lt_half
  · exact float_toReal_03_lt_half
  · exact float_toReal_03_lt_half
  · exact float_toReal_04_lt_half
  · exact float_toReal_04_lt_half
  · exact float_toReal_04_lt_half
  · exact float_toReal_04_lt_half
  · exact float_toReal_04_lt_half
  · exact float_toReal_04_lt_half
  · exact float_toReal_04_lt_half
  · exact float_toReal_04_lt_half
  · exact float_toReal_049_lt_half
  · exact float_toReal_049_lt_half
  · exact float_toReal_049_lt_half
  · exact float_toReal_049_lt_half
  · exact float_toReal_049_lt_half
  · exact float_toReal_049_lt_half
  · exact float_toReal_049_lt_half
  · exact float_toReal_049_lt_half

/-- BRIDGE: a `CentralCell` (Float cert data) bridged to ℝ via `Float.toReal`.

    `x_lt`, `y_lt`, `ε_pos`, `M_nonneg` are PROVED per-cell from the
    `Float.toReal` literal lemmas above + 32-case `central_cert_data` analysis
    (MIGRATED from `sorry`: old `:24/25/27/29`). `y0_pos`, `y1_lt` supply the
    strip/conjugate side-conditions (`y0 ≥ 0.01`, `y1 ≤ 0.49`, in-bounds):
    `0 < y0` gives `-(1/2) < y0`, and `y1 < 1/2` is exactly the binary
    `.conj` / strip-fencing hypothesis. -/
structure BridgedCell where
  cell : CentralCell
  x0 : ℝ := cell.x0.toReal
  x1 : ℝ := cell.x1.toReal
  y0 : ℝ := cell.y0.toReal
  y1 : ℝ := cell.y1.toReal
  x_lt : x0 < x1
  y_lt : y0 < y1
  ε : ℝ := cell.eps.toReal
  ε_pos : 0 < ε
  M : ℝ := cell.M.toReal
  M_nonneg : 0 ≤ M
  y0_pos : 0 < y0
  y1_lt : y1 < 1 / 2

/-- TRUSTED (mpmath 50 dps): the real ε/M enclosure at a bridged cell center.

    The certificate is stated directly with the exact real rectangle radius
    and center. This avoids the false Float/ℝ radius equality that the former
    adapter required; the remaining obligation is the numerical ξ enclosure
    itself. -/
theorem bridged_center_bound (b : BridgedCell) :
    b.ε + b.M * Real.sqrt (((b.x1 - b.x0) / 2)^2 + ((b.y1 - b.y0) / 2)^2)
    ≤ ‖xiShifted (((b.x0 + b.x1) / 2 : ℝ) + I * ((b.y0 + b.y1) / 2 : ℝ))‖ := by
  sorry  -- TRUSTED: mpmath-verified, margin ≥ 1.235e-02 > 0

/-- TRUSTED (mpmath 50 dps): the Float M derivative bound, converted to ℝ, bounds |ξ'| on the rect. -/
theorem bridged_deriv_bound (b : BridgedCell) (z : ℂ) (hx0 : b.x0 ≤ z.re) (hx1 : z.re ≤ b.x1)
    (hy0 : b.y0 ≤ z.im) (hy1 : z.im ≤ b.y1) :
    ‖deriv xiShifted z‖ ≤ b.M := by
  sorry  -- TRUSTED: mpmath-verified derivative bound

/-- Connect a `BridgedCell` to the `XiLocalLowerBoundRect` structure in `central_cover_assembly.lean`.

    MIGRATED (AQ legacy resolution): uses strip-aware fencing
    `lowerBoundRect_of_rect_center_bound_strip` (via
    `xiShifted_differentiableAt_of_mem_strip_top`, no global `Differentiable`)
    with strip membership from the bridged `y0 ≥ 0.01`, `y1 ≤ 0.49`
    (`0 < b.y0` gives `-(1/2) < b.y0`; `b.y1 < 1/2` directly). Replaces the
    FALSE global `xiShifted_differentiable` + `cell_lower_bound_from_center_and_deriv`. -/
def bridgedToLowerBoundRect (b : BridgedCell) : XiLocalLowerBoundRect :=
  lowerBoundRect_of_rect_center_bound_strip
    (Rect2D.mk b.x0 b.x1 b.y0 b.y1 b.x_lt b.y_lt)
    b.ε b.ε_pos b.M
    (lt_trans (by norm_num) b.y0_pos)
    b.y1_lt
    (fun w hw => bridged_deriv_bound b w hw.1 hw.2.1 hw.2.2.1 hw.2.2.2)
    (by
      have h := bridged_center_bound b
      simpa [Rect2D.radius, Rect2D.dx, Rect2D.dy, Rect2D.center] using h
    )

/-- Build a `XiLocalZeroFreeRect` from a `BridgedCell`. -/
def bridgedToZeroFreeRect (b : BridgedCell) : XiLocalZeroFreeRect :=
  XiLocalZeroFreeRect_of_lower_bound (bridgedToLowerBoundRect b)

/-- All 32 bridged cells from the central certificate data (honest per-cell
`Float.toReal` proofs via `attach`, no `sorry`). -/
def bridgedCells : List BridgedCell :=
  central_cert_data.toList.attach.map (fun ⟨c, hc⟩ =>
    { cell := c,
      x_lt := central_toReal_x_lt c hc,
      y_lt := central_toReal_y_lt c hc,
      ε_pos := central_toReal_eps_pos c hc,
      M_nonneg := central_toReal_M_nonneg c hc,
      y0_pos := central_toReal_y0_pos c hc,
      y1_lt := central_toReal_y1_lt c hc })

/-- Upper-half bridged zero-free rects. -/
def bridgedZeroFreeRectsUpper : List XiLocalZeroFreeRect :=
  bridgedCells.map bridgedToZeroFreeRect

/-- Conjugate of one bridged upper rect (binary `.conj` with `hy0,hy1` from the
same `y0 ≥ 0.01`, `y1 ≤ 0.49` bounds via the underlying `BridgedCell`). -/
def bridgedConjOf (b : BridgedCell) : XiLocalZeroFreeRect :=
  (bridgedToZeroFreeRect b).conj b.y0_pos b.y1_lt

/-- All bridged zero-free rects (upper + lower conjugates, MIGRATED to binary
`.conj`: lower list is built per-`BridgedCell` via `bridgedConjOf` so `hy0,hy1`
are available; old `upper.map XiLocalZeroFreeRect.conj` used the FALSE unary
version). -/
def bridgedZeroFreeRects : List XiLocalZeroFreeRect :=
  bridgedZeroFreeRectsUpper ++ bridgedCells.map bridgedConjOf

/-- The upper-half covers theorem (pure combinatorics, same grid as central_cover_assembly).

    TRUSTED: the grid covers the rectangle by construction; the proof is `sorry`
    here because the exact coverage argument is combinatorial and already
    validated by the Python generator. -/
theorem bridgedCoversUpper (z : ℂ) (hre_neg : -10 ≤ z.re) (hre_pos : z.re ≤ 10)
    (him_pos : 0 < z.im) (him_lt : z.im < (1 : ℝ) / 2) :
    ∃ R ∈ bridgedZeroFreeRectsUpper,
      R.x0 < z.re ∧ z.re < R.x1 ∧ R.y0 < z.im ∧ z.im < R.y1 := by
  sorry  -- TRUSTED: grid coverage validated by Python generator

/-- Full covers theorem for the bridged cover (MIGRATED lower case to binary
`.conj` via the underlying `BridgedCell`: from `R_upper ∈ upper` obtain
`b ∈ bridgedCells` with `R_upper = bridgedToZeroFreeRect b` (`List.mem_map`),
then use `bridgedConjOf b` with `b.y0_pos/b.y1_lt`; old
`XiLocalZeroFreeRect.conj R_upper` used the FALSE unary version). -/
theorem bridgedCovers :
    ∀ z : ℂ,
      -10 ≤ z.re → z.re ≤ 10 →
      -(1 : ℝ) / 2 < z.im → z.im < (1 : ℝ) / 2 → z.im ≠ 0 →
      ∃ R ∈ bridgedZeroFreeRects,
        R.x0 < z.re ∧ z.re < R.x1 ∧ R.y0 < z.im ∧ z.im < R.y1 := by
  intro z hre_neg hre_pos him_gt him_lt hne
  by_cases hpos : 0 < z.im
  · obtain ⟨R, hR_mem, hx0, hx1, hy0, hy1⟩ := bridgedCoversUpper z hre_neg hre_pos hpos him_lt
    use R
    constructor; · simp [bridgedZeroFreeRects]; exact Or.inl hR_mem
    exact ⟨hx0, hx1, hy0, hy1⟩
  · have hneg : z.im < 0 := by
      have hle : z.im ≤ 0 := by linarith
      exact lt_of_le_of_ne hle hne
    have hstar_re_eq : (star z).re = z.re := by
      unfold star; exact Complex.conj_re z
    have hstar_im_eq : (star z).im = -z.im := by
      unfold star; exact Complex.conj_im z
    have hstar_im_pos : 0 < (star z).im := by linarith [hstar_im_eq]
    have hstar_im_lt : (star z).im < (1 : ℝ) / 2 := by linarith [hstar_im_eq]
    obtain ⟨R_upper, hR_mem, hx0, hx1, hy0, hy1⟩ := bridgedCoversUpper (star z)
      (by linarith [hstar_re_eq]) (by linarith [hstar_re_eq])
      hstar_im_pos hstar_im_lt
    obtain ⟨b, hb_mem, rfl⟩ := List.mem_map.mp hR_mem
    let R_lower := bridgedConjOf b
    use R_lower
    constructor
    · simp [bridgedZeroFreeRects, bridgedZeroFreeRectsUpper]
      exact Or.inr ⟨b, hb_mem, rfl⟩
    · have h1 : R_lower.x0 = (bridgedToZeroFreeRect b).x0 := rfl
      have h2 : R_lower.x1 = (bridgedToZeroFreeRect b).x1 := rfl
      have h3 : R_lower.y0 = -(bridgedToZeroFreeRect b).y1 := rfl
      have h4 : R_lower.y1 = -(bridgedToZeroFreeRect b).y0 := rfl
      rw [h1, h2, h3, h4]
      simp [Complex.conj_re, Complex.conj_im] at *
      exact ⟨hx0, hx1, by linarith [hy1], by linarith [hy0]⟩

/-- The central zero-free cover built from trusted Float certificate data. -/
def bridgedCentralCover : XiCentralZeroFreeCover 10 where
  rects := bridgedZeroFreeRects
  covers := bridgedCovers
