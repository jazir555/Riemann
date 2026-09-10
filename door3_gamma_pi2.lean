import Mathlib

/-!
# Door 3 Gamma π/2 scout: feasibility + first fourth-tier lemmas.

## Consumer (Tier-B unlock, ledgered)
Tier B at ρ = 0.01 needs joint ball-sup `C ≤ 2.5` with `poly * pi = 214`,
i.e. `Gamma * zeta ≤ 0.0117`. With `zeta → 2`, need `Gamma ≤ ~0.006`.
Current banked Gamma rate `c = 1 / 2` (σ-general) / `c = log 2 ≈ 0.69`
(Re = 0.95 global) gives `~0.8` on the ball at `|T| ≈ 4.5` — about `400×`
loose vs true `~0.002`. True `π / 2` rate gives
`exp (-π * 4.5 / 2) ≈ 0.0009`-scale, which fits with headroom.

## Feasibility verdict: dyadic tiers CANNOT reach π/2; full tail product needed
Finite-product route: `‖Γ(σ + iT)‖ ^ 2 ≤ Γ(σ) ^ 2 * ∏ f_k`,
`f_k = (σ+k)^2 / ((σ+k)^2 + T^2)`.
Threshold `σ + k ≤ |T| / 2 ^ m` gives `f_k ≤ α^2 / (α^2 + 1)`,
`α = 1 / 2 ^ m`, i.e. half-weight `w ≈ m` per factor
(`1/2 → w 1`, `1/4 → w 2`, `1/16 → w 4`, `1/64 → w 6`, `1/256 → w 8`, …).

Per-tier weight accounting (mirrors `D3SG_prod_three_tier` exponent
`4 * Q + 2 * (H - Q) + (N - H)`, with `Q ≈ T/4`, `H ≈ T/2`, `N ≈ T`):
- 2-tier: `E = 2 * H + N ≈ 1.5 * T`, `c = E / (2 * T) * log 2 ≈ 0.52`
  (ledger quotes optimum `≈ 0.62` using exact `1/5` in place of `1/4`).
- 3-tier (banked): `E = 4 * Q + 2 * (H - Q) + (N - H) ≈ 2 * T`,
  `c ≈ log 2 ≈ 0.69`.
- 4-tier (this file): `E = 6 * O + 4 * (Q - O) + 2 * (H - Q) + (N - H)`,
  `O ≈ T/8`, so `E ≈ 2.25 * T`, `c ≈ 1.125 * log 2 ≈ 0.78`.
- 5-tier: `E ≈ 2.375 * T`, `c ≈ 0.82`.
- 6-tier: `E ≈ 2.4375 * T`, `c ≈ 0.84`.
- Infinite dyadic limit: `E / T → 1/2 + ∑ m / 2^m = 2.5`,
  `c → 1.25 * log 2 ≈ 0.867 ≪ π / 2 ≈ 1.5708`.
So NO finite (and not even infinite) dyadic power-of-two tier count reaches
`π / 2`. The residual must switch to the full-tail-product integral route
(`∑ log (1 + (T/x)^2)` over all `x = σ + k ≤ T`, comparison with
`∫ log (1 + (T/x)^2) dx = π * T / 2 + lower terms`), or equivalently a
Stirling-with-remainder route. That is multi-session work: exact-log product
lemma, integral comparison, `O(log T)` polynomial prefactor, small-height
merge with tight constant. Estimated `4-6` further sessions after this one.

## Uniform-M input: M = 20 banked is NOT sufficient at low ball height
Need `M * exp (-c * T) ≤ 0.007` at ball height `T ≈ 4.5`:
- `M = 20`, `c = π/2`: `20 * exp (-7.0686) ≈ 0.017 > 0.007`. FAILS (~2.4×).
  Even the TRUE rate with the banked uniform cap misses at `T = 4.5`.
- `M = 6.6` (`3 * 2.2`, local `Γ(0.4) ≈ 2.2` with `C = 3` overhead):
  `6.6 * exp (-7.0686) ≈ 0.0056 ≤ 0.007`. PASSES (narrow, needs `c ≥ 1.52`).
- `M = 5`: needs `c ≥ 1.46`. PASSES with true rate.
- At higher ball height `T ≥ 8`: `20 * exp (-π * 8 / 2) ≈ 0.00007 ≪ 0.007`.
  `M = 20` is ample there.
Verdict: keep `M = 20` for high balls; the `T ≈ 4.5` ball needs the local-M
σ-split (`Γ ≈ 2.2` near `σ = 0.4`, or the actual ball σ-slice cap) PLUS a
tight small-height/tall merge constant (`C ≤ 6`, not `18`).

## Honest blockers
- σ ≤ 0 reflection: PROVED blocked on the cheap route. Zeta FE `chi` grows
  like `exp (π * |T| / 2)` while the crude Gamma-side decay cannot cover it
  (ZU15: uniform-K reflection blocked on MVT route; Gdamp floor `≈ 9593`).
  Needs direct eta-pair linear bounds on the reflected line, not FE-shift.
  NOT attempted here.
- Floor-count floors at large T: NOT a blocker. Counts are linear with `O(1)`
  error (`Nat.lt_floor_add_one` / `Nat.floor_le` sandwich); the `+2` headroom
  absorbs it. The real loss is the dyadic `2/3 ≤ log 2` conversion and the
  small-height merge constant, not floors.
- Import: this file imports Mathlib ONLY. It does NOT import
  `door3_stirling_gamma.lean` (ST14 active lane). All helpers below are
  reproved locally under distinct `D3GP2_` names; theorem statements cite the
  `D3SG_` counterparts in docstrings.

## What this file banks (PROVED, no sorry/admit/axiom)
Fourth-tier triple mirroring the `D3SG_prod_sixteenth_pow` pattern:
- `D3GP2_factor_le_64th` (cf. `D3SG_factor_le_sixteenth`),
- `D3GP2_floor_eighth_le` (cf. `D3SG_floor_quarter_le`),
- `D3GP2_prod_64_pow` (cf. `D3SG_prod_sixteenth_pow`).

## Patch remainder (NOT in this file)
1. `Ico` middle-tier shifts for the 4-tier assembly (`1/16` on `[O,Q)`,
   `1/4` on `[Q,H)`, `1/2` on `[H,N)` in shifted-range form).
2. `D3GP2_prod_four_tier` product assembly with exponent
   `6 * O + 4 * (Q - O) + 2 * (H - Q) + (N - H)` (needs 1).
3. Tall `c ≈ 0.78` decay + global merge (needs 2 + `|T| ≤ 8` small-height).
4. Full-tail-product integral route to `π / 2` (replaces dyadic tiers).
5. Local-M σ-split cap at the ball slice + tight constant merge.
6. Zeta strip half (`zeta → 2`); σ ≤ 0 reflection via direct eta-pair route.
-/

open scoped BigOperators

/-- Each product factor lies in `[0,1]` for positive `σ`
(cf. `D3SG_factor_mem_Icc`, reproved locally). -/
theorem D3GP2_factor_mem_Icc (σ T : ℝ) (hσ : 0 < σ) (k : ℕ) :
    0 ≤ (σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2) ∧
    (σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2) ≤ 1 := by
  have hsk : (0 : ℝ) < σ + (k : ℝ) := by
    have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h2 : (0 : ℝ) < (σ + (k : ℝ)) ^ 2 := pow_pos hsk 2
  have hpos : (0 : ℝ) < (σ + (k : ℝ)) ^ 2 + T ^ 2 :=
    lt_of_lt_of_le h2 (le_add_of_nonneg_right (sq_nonneg T))
  constructor
  · exact div_nonneg (sq_nonneg _) (le_of_lt hpos)
  · rw [div_le_one hpos]
    linarith [sq_nonneg T]

/-- Threshold factor bound: `σ+k ≤ α·|T|` gives `≤ α²/(α²+1)`
(cf. `D3SG_factor_le_thresh`, reproved locally). -/
theorem D3GP2_factor_le_thresh (σ T α : ℝ) (hσ : 0 < σ) (k : ℕ)
    (h : σ + (k : ℝ) ≤ α * |T|) :
    (σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2) ≤ α ^ 2 / (α ^ 2 + 1) := by
  have hsk : (0 : ℝ) ≤ σ + (k : ℝ) := by
    have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hT2 : (σ + (k : ℝ)) ^ 2 ≤ α ^ 2 * T ^ 2 := by
    have h1 : (σ + (k : ℝ)) ^ 2 ≤ (α * |T|) ^ 2 := pow_le_pow_left₀ hsk h 2
    rw [mul_pow, sq_abs] at h1
    exact h1
  have hpos : (0 : ℝ) < (σ + (k : ℝ)) ^ 2 + T ^ 2 := by
    have h2 : (0 : ℝ) < (σ + (k : ℝ)) ^ 2 := by
      apply pow_pos _ 2
      have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    linarith [sq_nonneg T]
  have hden : (0 : ℝ) < α ^ 2 + 1 := by
    have hs := sq_nonneg α
    linarith
  rw [div_le_div_iff₀ hpos hden]
  nlinarith [hT2]

/-- Factors at height below `|T|/8` are at most one sixty-fourth
(via `1/65 ≤ 1/64`; cf. `D3SG_factor_le_sixteenth`). -/
theorem D3GP2_factor_le_64th (σ T : ℝ) (hσ : 0 < σ) (k : ℕ)
    (h : σ + (k : ℝ) ≤ |T| / 8) :
    (σ + (k : ℝ)) ^ 2 / ((σ + (k : ℝ)) ^ 2 + T ^ 2) ≤ 1 / 64 := by
  have hα : σ + (k : ℝ) ≤ (1 / 8) * |T| := by linarith
  have hth := D3GP2_factor_le_thresh σ T (1 / 8) hσ k hα
  have e : ((1 / 8 : ℝ)) ^ 2 / ((1 / 8) ^ 2 + 1) = 1 / 65 := by norm_num
  rw [e] at hth
  exact le_trans hth (by norm_num)

/-- Eighth-height count is dominated by the quarter-height count
(cf. `D3SG_floor_quarter_le`). -/
theorem D3GP2_floor_eighth_le (T : ℝ) (hT : 8 ≤ T) :
    Nat.floor (T / 8 - 0.95) + 1 ≤ Nat.floor (T / 4 - 0.95) + 1 := by
  have hnn : (0 : ℝ) ≤ T / 8 - 0.95 := by linarith
  have hle : T / 8 - 0.95 ≤ T / 4 - 0.95 := by linarith
  have c : ((Nat.floor (T / 8 - 0.95) + 1 : ℕ) : ℝ)
      ≤ ((Nat.floor (T / 4 - 0.95) + 1 : ℕ) : ℝ) := by
    push_cast
    have a := Nat.floor_le hnn
    have b := (Nat.lt_floor_add_one (T / 4 - 0.95)).le
    linarith
  exact Nat.cast_le.mp c

/-- Sixty-fourth-power product over the eighth-height range
(cf. `D3SG_prod_sixteenth_pow`). -/
theorem D3GP2_prod_64_pow (T : ℝ) (hT : 8 ≤ T) :
    ∏ k ∈ Finset.range (Nat.floor (T / 8 - 0.95) + 1),
      ((0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + T ^ 2))
      ≤ (1 / 2) ^ (6 * (Nat.floor (T / 8 - 0.95) + 1)) := by
  have hTh : (0 : ℝ) ≤ T / 8 - 0.95 := by linarith
  have h1 : ∀ k ∈ Finset.range (Nat.floor (T / 8 - 0.95) + 1),
      (0.95 + (k : ℝ)) ^ 2 / ((0.95 + (k : ℝ)) ^ 2 + T ^ 2) ≤ 1 / 64 := by
    intro k hk
    apply D3GP2_factor_le_64th 0.95 T (by norm_num) k
    have hkle : k ≤ Nat.floor (T / 8 - 0.95) :=
      Nat.lt_add_one_iff.mp (Finset.mem_range.mp hk)
    have hc : (k : ℝ) ≤ ((Nat.floor (T / 8 - 0.95) : ℕ) : ℝ) :=
      Nat.cast_le.mpr hkle
    have hf := Nat.floor_le hTh
    have hTnn : (0 : ℝ) ≤ T := by linarith
    rw [abs_of_nonneg hTnn]
    linarith
  have h := Finset.prod_le_prod
    (fun k _ => (D3GP2_factor_mem_Icc 0.95 T (by norm_num) k).1) h1
  rw [Finset.prod_const, Finset.card_range] at h
  have e : ((1 / 64 : ℝ)) ^ (Nat.floor (T / 8 - 0.95) + 1)
      = (1 / 2) ^ (6 * (Nat.floor (T / 8 - 0.95) + 1)) := by
    rw [show (1 / 64 : ℝ) = (1 / 2) ^ 6 by norm_num, ← pow_mul]
  rwa [e] at h

#print axioms D3GP2_prod_64_pow
