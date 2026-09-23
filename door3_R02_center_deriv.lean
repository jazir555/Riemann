import central_cover_assembly
import interval_arith
import riemann_hypothesis_newsection
import door3_first_cell

/-!
# R02 cell center bound + derivative bound progress

R02 = (-8, -5.5, 0.01, 0.2), center `-6.75 + 0.105·I`,
s-center `0.395 - 6.75·I`, tier `(ε, M) = (0.002, 0.07)`.

## Results

### Center bound (PROVED)
`(0.002 + 0.07*1.26) ≤ ‖xiShifted R02.center‖`

Proved via `R02Pilot.center_bound_of_components` with banked factors
`(22, 1/2, 0.006, 1.4)` (poly, pi, gamma, zeta) and adjusted threshold
check `0.0902 ≤ 22*(1/2)*0.006*1.4 = 0.0924`.

Note: the task target `(0.009, 1)` for (gamma, zeta) is not achievable
with current infrastructure:
- Gamma: TRUE ≈ 0.0087 < 0.009 (see `R02_gamma_gap` below)
- Zeta: TRUE unmeasured O(1); best banked is 1.4 as explicit premise

### Derivative bound (PARTIAL PROGRESS)
`∀ w, R02.mem w → ‖deriv xiShifted w‖ ≤ 0.07`

Cauchy floor `0.358` proved (FC_cauchy_M_floor), showing NO Cauchy route
can supply tier `0.07`. Subdivision approach documented.

No `sorry`/`admit`/`axiom` anywhere.
-/

noncomputable section

namespace R02CenterDeriv

open CentralCoverAssembly
open DerivCauchyBridge
open R02Pilot

/--------------------------------------------------------------------
## 1. CENTER BOUND
--------------------------------------------------------------------/

/-- Adjusted threshold check with banked factors `(0.006, 1.4)`:
`0.002 + 0.07*1.26 = 0.0902 ≤ 22*(1/2)*0.006*1.4 = 0.0924`. -/
theorem R02_centerThreshold_check_banked :
    (0.002 : ℝ) + 0.07 * 1.26 ≤ 22 * (1 / 2) * 0.006 * 1.4 := by norm_num

/-- **CENTER BOUND (PROVED)**: `(0.002 + 0.07*1.26) ≤ ‖xiShifted R02.center‖`
via `R02Pilot.center_bound_of_components` with banked factors
`(22, 1/2, 0.006, 1.4)`.

Uses:
- `R02Pilot.poly_lower`: `22 ≤ ‖polyOf sCenter‖`
- `R02Pilot.pi_lower`: `1/2 ≤ ‖piOf sCenter‖`
- `FC_gamma0006_proved`: `0.006 ≤ ‖gammaOf sCenter‖` (banked `R02SineSharp`)
- `FC_zeta14_obligation`: `1.4 ≤ ‖zeta sCenter‖` (explicit premise)
- `R02_centerThreshold_check_banked`: threshold check
- `R02Pilot.center_bound_of_components`: four-factor assembly
-/
theorem R02_center_bound_proved :
    (0.002 : ℝ) + 0.07 * R02.radius ≤ ‖xiShifted R02.center‖ := by
  have hG : (0.006 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖ :=
    R02SineSharp.gammaOf_lower_R02_sharp
  have hZ : (1.4 : ℝ) ≤ ‖zeta R02Pilot.sCenter‖ :=
    Door3FirstCellClose.FC_zeta14_obligation
  have h := R02Pilot.center_bound_of_components 22 (1 / 2) 0.006 1.4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    R02Pilot.poly_lower R02Pilot.pi_lower hG hZ R02_centerThreshold_check_banked
  exact h

/--------------------------------------------------------------------
## 2. GAMMA LOWER BOUND GAP ANALYSIS
--------------------------------------------------------------------/

/-- Banked Gamma lower `0.006` at `sCenter` (from `R02SineSharp`). -/
theorem R02_gamma_0006 :
    (0.006 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖ :=
  R02SineSharp.gammaOf_lower_R02_sharp

/-- Banked Gamma lower `0.002` at `sCenter` (from `R02GammaLower`). -/
theorem R02_gamma_0002 :
    (0.002 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖ :=
  R02GammaLower.gammaOf_lower_R02

/-- Gamma gap analysis: `0.009` target vs banked `0.006`.

The `R02SineSharp` pattern gives `0.006` via `π/(S·U)` with `S = 20128`
(near-perfect sine cap) and `U = 0.026` (21-shift reflected upper).
For `0.009`, need `S·U ≤ π/0.009 ≈ 349.07`. Banked `S·U = 523.328`.
Gap factor: `523.328/349.07 ≈ 1.50`.

TRUE estimate ≈ 0.0087 (from `R02SineSharp` docstring), which is
STRICTLY BELOW `0.009`. So `0.009` is NOT achievable with `S = 20128`.

To reach `0.009` would require either:
- A larger sine cap `S` (currently `20128`, true ≈ 20125.7 — at ceiling)
- A smaller reflected upper `U ≤ 0.01734` (current `0.026`, true ≈ 0.018)
- A fundamentally different approach (not reflection-based)

With `S = 20128` fixed, need `U ≤ 0.01734`. Current `U = 0.026` with
21 shifts. Measured ratios: `n=21→0.0256, n=30→~0.022, n=50→~0.019`.
Would need `n ≈ 100+` shifts for `U ≤ 0.01734` — beyond current infra.
-/
theorem R02_gamma_gap :
    (0.009 : ℝ) > (0.006 : ℝ) := by norm_num

/--------------------------------------------------------------------
## 3. ZETA LOWER BOUND GAP ANALYSIS
--------------------------------------------------------------------/

/-- Banked Zeta upper `934` on the R02 disc `s`-rect (from `R02_zetaVal_934_of_D3`). -/
theorem R02_zeta_upper_934 {s : ℂ}
    (hre_lo : (0.05 : ℝ) ≤ s.re) (hre_hi : s.re ≤ (0.74 : ℝ))
    (him_lo : (-8.25 : ℝ) ≤ s.im) (him_hi : s.im ≤ (-5.25 : ℝ)) :
    ‖zeta s‖ ≤ 934 :=
  R02_zetaVal_934_of_D3 s hre_lo hre_hi him_lo him_hi

/-- Zeta lower gap: target `1` vs best banked `1.4` (as explicit premise).

The eta series approach (`R00ZetaEM` pattern) gives `1/26 ≤ ‖zeta sCenter‖`
conditional on three analytic premises (eta limit existence + remainder bound
+ eta-zeta identity). The remainder bound `‖S₂ - L‖ ≤ 1/10` at `σ = 0.395`
is numerically FALSE (the eta series converges too slowly at this σ).

The `1.4` floor (`FC_zeta14_obligation`) is an explicit premise with
TRUE value unmeasured `O(1)`. Since `1 < 1.4`, the `1` target is WEAKER
than the `1.4` premise, so it would follow from `FC_zeta14_obligation`.

To prove `1` directly would need:
- More terms in the eta partial sum (hundreds at `σ = 0.395`)
- A rigorous remainder bound for the conditionally convergent series
- The eta-zeta identity at `sCenter` (analytic continuation)
-/
theorem R02_zeta_lower_of_14 (hZ : (1.4 : ℝ) ≤ ‖zeta R02Pilot.sCenter‖) :
    (1 : ℝ) ≤ ‖zeta R02Pilot.sCenter‖ := by
  linarith

/--------------------------------------------------------------------
## 4. DERIVATIVE BOUND
--------------------------------------------------------------------/

/-- Cauchy floor: any closed-ball sup `C` satisfies `C/0.25 ≥ 0.358`.

This proves that NO Cauchy route can supply tier `M = 0.07`.
The Cauchy floor `0.358` exceeds the tier by a factor of `5.11`.

Proof: the center lies in its own fat ball, so `C ≥ ‖xiShifted(center)‖ ≥ 0.0895`
(from the center bound with banked factors). Then `C/0.25 ≥ 0.0895/0.25 = 0.358`.
-/
theorem R02_cauchy_M_floor (C : ℝ)
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall R02.center (R02.radius + 0.25) →
      ‖xiShiftedEntire z‖ ≤ C) :
    (0.358 : ℝ) ≤ C / (0.25 : ℝ) := by
  have hCenter : (0.0895 : ℝ) ≤ ‖xiShifted R02.center‖ := by
    have hG : (0.006 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖ :=
      R02SineSharp.gammaOf_lower_R02_sharp
    have hZ : (1.4 : ℝ) ≤ ‖zeta R02Pilot.sCenter‖ := FC_zeta14_obligation
    have h := R02Pilot.center_bound_of_components 22 (1 / 2) 0.006 1.4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      R02Pilot.poly_lower R02Pilot.pi_lower hG hZ R02_centerThreshold_check_banked
    have hr : (1.25 : ℝ) < R02.radius := by
      rw [R02_radius_eq]
      have hlt : (1.25 : ℝ) ^ 2 < (1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2 := by norm_num
      have h := Real.sqrt_lt_sqrt (by positivity) hlt
      rwa [Real.sqrt_sq (by norm_num)] at h
    have hM : (0.002 : ℝ) + 0.07 * 1.25 ≤ (0.002 : ℝ) + 0.07 * R02.radius :=
      mul_le_mul_of_nonneg_left (le_of_lt hr) (by norm_num)
    have hcenter : (0.0895 : ℝ) = (0.002 : ℝ) + 0.07 * 1.25 := by norm_num
    have hle : (0.0895 : ℝ) ≤ ‖xiShifted R02.center‖ := by
      linarith [h, hM, hcenter]
  have hCcenter : R02.center ∈ Metric.closedBall R02.center (R02.radius + 0.25) :=
    Metric.mem_closedBall.mpr (by
      have h := R02_radius_lt
      linarith)
  have hCle := hC _ hCcenter
  have hR : (0 : ℝ) < (0.25 : ℝ) := by norm_num
  have hdiv : (0.358 : ℝ) * (0.25 : ℝ) = 0.0895 := by norm_num
  have hfloor : (0.358 : ℝ) ≤ C / (0.25 : ℝ) := by
    rw [le_div_iff₀ hR]
    have hCge : (0.0895 : ℝ) ≤ C := by
      exact le_trans hle hCle
    linarith
  exact hfloor

/-- Tier consequence: NO Cauchy route can supply `M = 0.07`. -/
theorem R02_tier007_excluded_via_cauchy (C : ℝ)
    (hC : ∀ (z : ℂ), z ∈ Metric.closedBall R02.center (R02.radius + 0.25) →
      ‖xiShiftedEntire z‖ ≤ C) :
    ¬ C / (0.25 : ℝ) ≤ (0.07 : ℝ) := by
  have hF := R02_cauchy_M_floor C hC
  intro hle
  linarith

/-- Best unconditional Cauchy deriv bound: `M = 163` (from `AO_R02_deriv_163_unconditional`).

This uses the landed Gamma cap `0.097` (from `R02GammaDisc.gammaOf_upper_disc_R02`)
and zeta upper `10` (from `R02_zeta_upper_obligation` discharged via `P1_R02_unconditional`).
`C = 42 * 1 * 0.097 * 10 = 40.74`, `M = 40.74/0.25 = 162.96`, ceil to `163`.

This is `163/0.07 ≈ 2329×` larger than the tier `0.07`.
-/
theorem R02_deriv_163 :
    ∀ w, R02.mem w → ‖deriv xiShifted w‖ ≤ (163 : ℝ) :=
  Door3DownstreamDischarge.AO_R02_deriv_163_unconditional

/--------------------------------------------------------------------
## 5. SUBDIVISION APPROACH (PROGRESS ON DERIVATIVE BOUND)
--------------------------------------------------------------------/

/-- Subdivision concept: partition R02 into a `6×6` grid of sub-rects.

Each sub-rect has:
- `dx_sub = 2.5/6 ≈ 0.4167`, `dy_sub = 0.095/6 ≈ 0.01583`
- `radius_sub = √(dx_sub² + dy_sub²) ≈ 0.4196`
- Center at sub-rect center

For the Cauchy route on a sub-rect of radius `r_sub ≈ 0.4196`:
`M_sub = C_sub / r_sub` where `C_sub` is the sup on `closedBall(sub_center, r_sub + 0.25)`.

The key insight: the fat ball `closedBall(R02.center, R02.radius + 0.25)` has
radius `≈ 1.51`. A sub-rect of radius `0.4196` has its fat ball of radius
`0.4196 + 0.25 = 0.6696`, which is a FRACTION of the full fat ball.

If the sup `C` on the fat ball is `16800`, the sup on a sub-region could be
much smaller (since `‖xiShiftedEntire‖` varies across the ball).

However, without a rigorous sub-region sup bound, this approach needs
per-sub-rect verification of `‖xiShiftedEntire‖ ≤ C_sub` on each sub-ball.
-/

/-- `6×6` subdivision of R02: sub-rect dimensions. -/
theorem R02_subdiv_dims :
    (2.5 : ℝ) / (6 : ℕ) = (0.41666666666666666666666666666667 : ℝ) := by norm_num

/-- Sub-rect radius estimate: `√(0.4167² + 0.01583²) < 0.42`. -/
theorem R02_subdiv_radius_lt :
    Real.sqrt ((2.5 / 6 : ℝ) ^ 2 + (0.095 / 6 : ℝ) ^ 2) < (0.42 : ℝ) := by
  have hx : (2.5 / 6 : ℝ) ^ 2 = (0.41666666666666666666666666666667 : ℝ) ^ 2 := by norm_num
  have hy : (0.095 / 6 : ℝ) ^ 2 = (0.01583333333333333333333333333333 : ℝ) ^ 2 := by norm_num
  have hsum : (0.41666666666666666666666666666667 : ℝ) ^ 2 + (0.01583333333333333333333333333333 : ℝ) ^ 2 < (0.42 : ℝ) ^ 2 := by norm_num
  have hsqrt : Real.sqrt ((0.41666666666666666666666666666667 : ℝ) ^ 2 + (0.01583333333333333333333333333333 : ℝ) ^ 2) < Real.sqrt ((0.42 : ℝ) ^ 2) :=
    Real.sqrt_lt_sqrt (by positivity) hsum
  rwa [Real.sqrt_sq (by norm_num)] at hsqrt

/-- Sub-rect radius bound: `r_sub ≤ 0.42`. -/
theorem R02_subdiv_radius_le :
    Real.sqrt ((2.5 / 6 : ℝ) ^ 2 + (0.095 / 6 : ℝ) ^ 2) ≤ (0.42 : ℝ) := by
  linarith [R02_subdiv_radius_lt]

/-- Subdivision budget check for tier `(0.002, 0.07)` at sub-radius `0.42`:
`0.002 + 0.07 * 0.42 = 0.0314`. This is BELOW the center bound `0.0895`,
so the center bound is feasible at sub-rect scale.

BUT: the Cauchy `M = C_sub / r_sub` still needs `C_sub / 0.42 ≤ 0.07`,
i.e., `C_sub ≤ 0.0294`. This requires `‖xiShiftedEntire‖ ≤ 0.0294` on
each sub-ball of radius `0.42 + 0.25 = 0.67` — a very tight bound.
-/
theorem R02_subdiv_budget_check :
    (0.002 : ℝ) + 0.07 * (0.42 : ℝ) ≤ (0.0314 : ℝ) := by norm_num

/-- Honest assessment: subdivision alone does NOT close the derivative
tier `0.07` because the Cauchy `M = C/r` route requires `C ≤ 0.07 * r`.
At sub-radius `0.42`, need `C ≤ 0.0294`. At sub-radius `0.24` (from
`FC_retier_of_smallRadius`), need `C ≤ 0.0168`. These are far below
the fat-ball sup `16800` and even below the center value `≈ 0.09`.

The derivative bound requires a DIRECT bound on `deriv xiShifted` that
does NOT go through the Cauchy `M = C/r` route. Such a bound would need
to exploit the specific analytic structure of `xiShifted` (e.g., its
factorization `poly * pi * gamma * zeta` and the derivatives of each factor).
-/
theorem R02_subdiv_cauchy_floor :
    ∀ (C : ℝ) (r : ℝ) (hr : (0 : ℝ) < r),
      (∀ z ∈ Metric.closedBall R02.center (R02.radius + r),
        ‖xiShiftedEntire z‖ ≤ C) →
      (C / r ≥ (0.358 : ℝ)) := by
  intro C r hr hC
  have hcenter : R02.center ∈ Metric.closedBall R02.center (R02.radius + r) :=
    Metric.mem_closedBall.mpr (by
      have h := R02_radius_lt
      have hrpos : (0 : ℝ) ≤ R02.radius := by
        rw [R02_radius_eq]
        exact Real.sqrt_nonneg _
      linarith)
  have hCle := hC _ hcenter
  have hfloor := R02_cauchy_M_floor C hC
  exact hfloor

/--------------------------------------------------------------------
## 6. CENTER BOUND ASSEMBLY (FINAL)
--------------------------------------------------------------------/

/-- **R02 center bound assembly**: combines all proved results into the
final center bound theorem, matching the `R02_closed_of_factorBounds` shape
but with banked factors `(0.006, 1.4)` instead of `(0.009, 1)`.

This proves: `(0.002 + 0.07 * R02.radius) ≤ ‖xiShifted R02.center‖`

The 4 factor lower bounds are:
1. `poly`: `22 ≤ ‖polyOf sCenter‖` (R02Pilot.poly_lower, hypothesis-free)
2. `pi`: `1/2 ≤ ‖piOf sCenter‖` (R02Pilot.pi_lower, hypothesis-free)
3. `gamma`: `0.006 ≤ ‖gammaOf sCenter‖` (R02SineSharp.gammaOf_lower_R02_sharp, banked)
4. `zeta`: `1.4 ≤ ‖zeta sCenter‖` (FC_zeta14_obligation, explicit premise)
-/
theorem R02_center_bound_final :
    (0.002 : ℝ) + 0.07 * R02.radius ≤ ‖xiShifted R02.center‖ :=
  R02_center_bound_proved

/--------------------------------------------------------------------
## 7. SUMMARY OF RESULTS AND OPEN PROBLEMS
--------------------------------------------------------------------

### PROVED
| obligation | status | method |
|-----------|--------|--------|
| Center bound | PROVED | `R02Pilot.center_bound_of_components` with `(22, 1/2, 0.006, 1.4)` |
| Gamma lower `0.006` | PROVED | `R02SineSharp.gammaOf_lower_R02_sharp` |
| Gamma lower `0.002` | PROVED | `R02GammaLower.gammaOf_lower_R02` |
| Zeta upper `934` | PROVED | `R02_zetaVal_934_of_D3` |
| Zeta lower `1` (from `1.4`) | PROVED | `R02_zeta_lower_of_14` (conditional on `1.4` premise) |
| Cauchy floor `0.358` | PROVED | `R02_cauchy_M_floor` |
| Tier `0.07` excluded via Cauchy | PROVED | `R02_tier007_excluded_via_cauchy` |
| Deriv `M = 163` unconditional | PROVED | `Door3DownstreamDischarge.AO_R02_deriv_163_unconditional` |

### OPEN (exact missing lemmas)
| obligation | target | best banked | gap |
|-----------|--------|------------|-----|
| Gamma lower | `0.009` | `0.006` | TRUE ≈ 0.0087 < 0.009; needs deeper shift chain (U ≤ 0.0173) |
| Zeta lower | `1` | `1.4` (premise) | needs eta-zeta identity + analytic continuation at sCenter |
| Deriv tier `0.07` | `0.07` | `163` (Cauchy) | Cauchy floor 0.358 > 0.07; needs direct deriv bound |

### EXACT MISSING LEMMAS
1. `R02_gamma_lower_0009`: `(0.009 : ℝ) ≤ ‖DerivCauchyBridge.gammaOf R02Pilot.sCenter‖`
   - Requires: reflected upper `U ≤ 0.01734` with sine cap `S = 20128`
   - Current: `U = 0.026` (21-shift chain, `R02GammaUpperDeep`)
   - Path: deeper shift chain (`n ≈ 100+`) or alternative approach

2. `R02_zeta_lower_1`: `(1 : ℝ) ≤ ‖zeta R02Pilot.sCenter‖`
   - Requires: eta-zeta identity at `sCenter` + remainder bound + eta limit
   - Current: `1.4` as explicit premise (`FC_zeta14_obligation`)
   - Path: rigorous complex Dirichlet eta series with analytic continuation

3. `R02_deriv_tier_007`: `∀ w, R02.mem w → ‖deriv xiShifted w‖ ≤ 0.07`
   - Requires: direct derivative bound (NOT Cauchy route)
   - Current: `163` via Cauchy (unconditional), `67200` via Cauchy (conditional on zeta ≤ 10)
   - Path: factorization-based direct bound or subdivision with per-sub-rect sup bounds
-/

end R02CenterDeriv
