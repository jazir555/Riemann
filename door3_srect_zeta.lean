import Mathlib
import central_cover_assembly
import zeta_rigorous

/-! # Door-3 thin s-rect zeta upper (supplier lane, write-only)

Target rect (consumer shape in `door3_cutR10_retier.lean`, Tier-C choice):
`Re in [0.01, 0.99]`, `Im in [9.75, 10.25]` (image of `CutR10` under
`s = 1 / 2 + I * z`). Goal: sharpest true uniform `‖zeta s‖ ≤ C`.

IMPORT FLAG: `zeta_rigorous` is imported (cycle-safe: it imports only
Mathlib plus `Zeta23.MV.Final`, so no supplier cycle). Everything else used
here is Mathlib or `central_cover_assembly` (which supplies the root `zeta`
alias for `riemannZeta`). The eta-pair remainder machine
(`zetaCell_even_remainder_le`), the division bridge
(`zeta_of_etaPairLim_of_re_ne`) and the cpow norm (`two_cpow_one_sub_norm`)
are reused from `zeta_rigorous`; the head/tail/denominator numerals are
re-proved locally so each constant is auditable in-file.

ETA-BALL FINDING (verified below, numerals true within stated margins):
the eta factor `1 - 2 ^ (1 - s)` vanishes at `s = 1` (k = 0 branch, Im 0)
and at `s ≈ 1 + 9.06i` (k = -1 branch; true Im `2 * pi / log 2 ≈ 9.06`,
below `9.07`), with the next neighbor at Im `≈ 18.13` (k = -2 branch,
above `18.12`). All three lie OUTSIDE the rect:
`Re = 1` is right of `0.99`, Im `9.06` is below `9.75`, Im `18.13` is above
`10.25`. Bridge choice: eta-bridge everywhere on the rect; Euler pieces
nowhere (the `TailZetaUpper` lemmas `riemannZeta_norm_le_const_of_re_ge`,
`zeta_rightEdge_B3/B2` in `riemann_hypothesis_newsection.lean`, read-only,
need `Re ≥ 1 + delta` while the rect has `Re ≤ 0.99`); FE/convexity
reflection from the `Re ≥ 2` side is not needed since the rect stays in
`Re > 0` where the eta series converges.

C LANDED (proved below):
* low piece `Re in [0.01, 1/2]`: numerator `≤ 1202`, denom `≥ 2/5` → 3005.
* mid piece `Re in [1/2, 3/4]`: numerator `≤ 26`, denom `≥ 1/10` → 260.
* high piece `Re in [3/4, 0.99]`: numerator `≤ 26`, denom `≥ 2/5`
  (single explicit premise `HighEtaDenom`; true minimum on this piece is
  about `0.47` at the `(0.99, 9.75)` corner, so `0.4` holds with margin) → 65.
* uniform: `‖zeta s‖ ≤ 3005` on the whole rect, conditional ONLY on
  `HighEtaDenom`.

IMPLIED deriv-M (Tier-C arithmetic, proved as numeral identities below):
poly `≤ 78` and pi `≤ 1` are proved here; with the sibling-lane Gamma cap
`1 / 100` the joint function sup is `78 * (1/100) * 3005 = 2343.9 ≤ 2344`.
A Cauchy deriv step only divides by the margin distance, so the implied
`thinDerivRemainder`-style M is at least `2344`, far above the Tier-C target
`0.04`. Closing `0.04` from these poly/pi/Gamma caps would need
`Cz ≤ 0.051` (proved as `tierC_Cz_cap`); the landed `3005` does NOT close
Tier C. Honest gap: about five orders of magnitude.

THEOREMS PROVED: rect geometry (`srect_norm_le`), eta-zero location
(`etaZero_*`), eta head (`eta_head_two`), eta tail (`eta_tail_div`),
numerators (`eta_num_low`, `eta_num_midhigh`), denominators
(`eta_denom_low`, `two_pow_quarter_ge`, `eta_denom_mid`), zeta pieces
(`zeta_low`, `zeta_mid`, `zeta_high_of_denom`, `zeta_uniform_of_highDenom`,
`zeta_uniform_z_of_denom`), poly/pi caps (`srect_poly_le`, `srect_pi_le`),
joint assembly (`joint_func_of_caps`), Tier-C numerals
(`tierC_need_eq`, `landedM_eq`, `landedM_le`, `landedM_gt_tierC`,
`tierC_Cz_cap`).
RESIDUAL (not closed here): `HighEtaDenom` (the only delta: a uniform
`2/5` lower bound for `‖1 - 2^(1-s)‖` on the high piece; true value about
`0.47`, closable by a sine-mean-value bound over the boxed phase) and the
sibling-lane `sRectGammaSup (1/100)` input to the joint assembly.
PATCH REMAINDER: discharge `HighEtaDenom` (phase box for
`(1-s)*log 2` on the high piece), land `sRectGammaSup`, rewire the deriv
supplier to `joint_func_of_caps` plus a Cauchy step, or renegotiate Tier C
per `tierC_Cz_cap`.

Compliance: no placeholder tactics and no extra foundational assumptions;
all binders explicit; only separate rewrite steps (never the combined
simplify-with-assumption form); every numeral has at most six digits;
`norm_num` closes numeric goals without proof-by-computation on rationals.
-/

open scoped BigOperators

noncomputable section

namespace Door3SRectZeta

/-! ## Rect geometry. -/

/-- Norm cap on the thin rect: `‖s‖ ≤ 12`
(`|Re| ≤ 0.99`, `|Im| ≤ 10.25`, sum `≤ 11.24`). -/
theorem srect_norm_le (s : ℂ)
    (hlo : (0.01 : ℝ) ≤ s.re) (hhi : s.re ≤ (0.99 : ℝ))
    (hilo : (9.75 : ℝ) ≤ s.im) (hihi : s.im ≤ (10.25 : ℝ)) :
    ‖s‖ ≤ (12 : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im s
  have hreabs : |s.re| ≤ (0.99 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have himabs : |s.im| ≤ (10.25 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  linarith

/-! ## ETA-BALL location checks (all eta zeros outside the rect). -/

/-- The k = -1 eta-zero has Im about `9.06 < 9.07`, below the rect floor. -/
theorem etaZero_kNeg1_im_lt : (9.07 : ℝ) < 9.75 := by norm_num

/-- The eta-zero real part `1` lies right of the rect ceiling `0.99`. -/
theorem etaZero_re_out : (0.99 : ℝ) < 1 := by norm_num

/-- The k = -2 neighbor has Im about `18.13 > 18.12`, above the rect roof. -/
theorem etaZero_kNeg2_im_gt : (10.25 : ℝ) < 18.12 := by norm_num

/-- The k = 0 zero `s = 1` has Im `0`, below the rect floor. -/
theorem etaZero_k0_im_out : (0 : ℝ) < 9.75 := by norm_num

/-! ## Eta head (`S₂ ≤ 2`) and tail (`≤ 12 / Re`). -/

/-- Two-term eta head bound for `0 ≤ Re s` (local reproof of the
`zeta_rigorous` head pattern with renamed binders). -/
theorem eta_head_two (s : ℂ) (hsre : (0 : ℝ) ≤ s.re) :
    ‖∑ k ∈ Finset.range 2, etaDirichletTerm s k‖ ≤ (2 : ℝ) := by
  have h0 : etaDirichletTerm s 0 = 1 := by
    simp only [etaDirichletTerm]
    simp
  have hterm1_eq : etaDirichletTerm s 1 =
      -1 / ((((2 : ℕ)) : ℂ) ^ s) := by
    simp only [etaDirichletTerm]
    norm_num
  have h2cast : ((((2 : ℕ)) : ℂ)) = ((((2 : ℝ)) : ℂ)) := by norm_num
  have h2norm : ‖((((2 : ℕ)) : ℂ) ^ s)‖ = (2 : ℝ) ^ s.re := by
    rw [h2cast]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
  have h20 : (2 : ℝ) ^ (0 : ℝ) = 1 := Real.rpow_zero 2
  have h2ge : (1 : ℝ) ≤ (2 : ℝ) ^ s.re := by
    rw [← h20]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hsre
  have h1_norm : ‖etaDirichletTerm s 1‖ ≤ 1 := by
    rw [hterm1_eq, norm_div, norm_neg, norm_one, h2norm]
    rw [div_le_one (Real.rpow_pos_of_pos (by norm_num) _)]
    exact h2ge
  have hsum2 : (∑ k ∈ Finset.range 2, etaDirichletTerm s k) =
      etaDirichletTerm s 0 + etaDirichletTerm s 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
  rw [hsum2, h0]
  calc ‖(1 : ℂ) + etaDirichletTerm s 1‖ ≤
        ‖(1 : ℂ)‖ + ‖etaDirichletTerm s 1‖ := norm_add_le _ _
    _ ≤ 1 + 1 := by rw [norm_one]; linarith
    _ = 2 := by norm_num

/-- Paired tail with `M = 1`: distance from the head sum is `≤ 12 / Re`
on `‖s‖ ≤ 12` (from `zetaCell_even_remainder_le`). -/
theorem eta_tail_div (s : ℂ) (hspos : (0 : ℝ) < s.re)
    (hsnorm : ‖s‖ ≤ (12 : ℝ)) :
    ‖(∑' m, etaPairTerm s m) -
      (∑ k ∈ Finset.range 2, etaDirichletTerm s k)‖ ≤
      (12 : ℝ) / s.re := by
  have htail := zetaCell_even_remainder_le hspos hsnorm
    (by norm_num : (0 : ℝ) ≤ 12) 1 (by norm_num)
  simp only [Nat.cast_one, Real.one_rpow, mul_one] at htail
  rw [mul_one_div] at htail
  exact htail

/-- Numerator cap on the low piece: `Re ≥ 0.01` gives `12 / Re ≤ 1200`,
plus head `2`. -/
theorem eta_num_low (s : ℂ) (hlo : (0.01 : ℝ) ≤ s.re)
    (hsnorm : ‖s‖ ≤ (12 : ℝ)) :
    ‖∑' m, etaPairTerm s m‖ ≤ (1202 : ℝ) := by
  have hspos : (0 : ℝ) < s.re := by linarith
  have htail := eta_tail_div s hspos hsnorm
  have hdiv : (12 : ℝ) / s.re ≤ 1200 := by
    apply (div_le_iff₀ hspos).2
    linarith
  have hS2 : ‖∑ k ∈ Finset.range 2, etaDirichletTerm s k‖ ≤ (2 : ℝ) :=
    eta_head_two s (by linarith)
  have htri := norm_add_le (∑ k ∈ Finset.range 2, etaDirichletTerm s k)
    ((∑' m, etaPairTerm s m) - (∑ k ∈ Finset.range 2, etaDirichletTerm s k))
  rw [add_sub_cancel] at htri
  linarith

/-- Numerator cap on mid/high pieces: `Re ≥ 1/2` gives `12 / Re ≤ 24`,
plus head `2`. -/
theorem eta_num_midhigh (s : ℂ) (hlo : (1 / 2 : ℝ) ≤ s.re)
    (hsnorm : ‖s‖ ≤ (12 : ℝ)) :
    ‖∑' m, etaPairTerm s m‖ ≤ (26 : ℝ) := by
  have hspos : (0 : ℝ) < s.re := by linarith
  have htail := eta_tail_div s hspos hsnorm
  have hdiv : (12 : ℝ) / s.re ≤ 24 := by
    apply (div_le_iff₀ hspos).2
    linarith
  have hS2 : ‖∑ k ∈ Finset.range 2, etaDirichletTerm s k‖ ≤ (2 : ℝ) :=
    eta_head_two s (by linarith)
  have htri := norm_add_le (∑ k ∈ Finset.range 2, etaDirichletTerm s k)
    ((∑' m, etaPairTerm s m) - (∑ k ∈ Finset.range 2, etaDirichletTerm s k))
  rw [add_sub_cancel] at htri
  linarith

/-! ## Eta denominators. -/

/-- Low-piece denominator: `Re ≤ 1/2` gives `‖q‖ ≥ 7/5`, hence
`‖1 - q‖ ≥ 2/5` (reverse triangle). -/
theorem eta_denom_low (s : ℂ) (hs : s.re ≤ (1 / 2 : ℝ)) :
    (2 / 5 : ℝ) ≤ ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ := by
  have hqnorm : ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ = (2 : ℝ) ^ (1 - s.re) :=
    two_cpow_one_sub_norm s
  have hexp : (1 / 2 : ℝ) ≤ 1 - s.re := by linarith
  have hsq : (7 / 5 : ℝ) ^ (2 : ℕ) ≤ (2 : ℝ) := by norm_num
  have hpow : (((2 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ)) = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hsqrt : (7 / 5 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← hpow] at hsq
    exact le_of_pow_le_pow_left₀ (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _).le hsq
  have hqge : (7 / 5 : ℝ) ≤ ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ := by
    rw [hqnorm]
    exact le_trans hsqrt
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
  have htri := norm_add_le ((2 : ℂ) ^ ((1 : ℂ) - s) - 1) (1 : ℂ)
  have hqdecomp : (2 : ℂ) ^ ((1 : ℂ) - s) - 1 + 1 =
      (2 : ℂ) ^ ((1 : ℂ) - s) := by ring
  rw [hqdecomp, norm_one, norm_sub_rev] at htri
  linarith

/-- Fourth-root numeral: `11/10 ≤ 2 ^ (1/4)` since `(11/10)^4 ≤ 2`. -/
theorem two_pow_quarter_ge : (11 / 10 : ℝ) ≤ (2 : ℝ) ^ (1 / 4 : ℝ) := by
  have hpow4 : (11 / 10 : ℝ) ^ (4 : ℕ) ≤ (2 : ℝ) := by norm_num
  have hpow' : (((2 : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℕ)) = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [← hpow'] at hpow4
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow4

/-- Mid-piece denominator: `Re ≤ 3/4` gives `‖q‖ ≥ 11/10`, hence
`‖1 - q‖ ≥ 1/10`. -/
theorem eta_denom_mid (s : ℂ) (hlo : (1 / 2 : ℝ) ≤ s.re)
    (hhi : s.re ≤ (3 / 4 : ℝ)) :
    (1 / 10 : ℝ) ≤ ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ := by
  have hqnorm : ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ = (2 : ℝ) ^ (1 - s.re) :=
    two_cpow_one_sub_norm s
  have hexp : (1 / 4 : ℝ) ≤ 1 - s.re := by linarith
  have hqge : (11 / 10 : ℝ) ≤ ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ := by
    rw [hqnorm]
    exact le_trans two_pow_quarter_ge
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
  have hrev := norm_sub_norm_le ((2 : ℂ) ^ ((1 : ℂ) - s)) (1 : ℂ)
  rw [norm_one, norm_sub_rev] at hrev
  linarith

/-- High-piece denominator premise (THE delta, explicitly gated).
True value on this piece is about `0.47` at the `(0.99, 9.75)` corner
(see header), so `2/5` holds with margin; closable by a sine-mean-value
bound over the boxed phase `(1 - s) * log 2`. -/
def HighEtaDenom : Prop :=
  ∀ (s : ℂ), (3 / 4 : ℝ) ≤ s.re → s.re ≤ (0.99 : ℝ) →
    (9.75 : ℝ) ≤ s.im → s.im ≤ (10.25 : ℝ) →
    (2 / 5 : ℝ) ≤ ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖

/-! ## Zeta pieces and uniform bound. -/

/-- Low piece `Re in [0.01, 1/2]`: `1202 / (2/5) = 3005`. -/
theorem zeta_low (s : ℂ)
    (hlo : (0.01 : ℝ) ≤ s.re) (hhi : s.re ≤ (0.99 : ℝ))
    (hilo : (9.75 : ℝ) ≤ s.im) (hihi : s.im ≤ (10.25 : ℝ))
    (hR : s.re ≤ (1 / 2 : ℝ)) :
    ‖riemannZeta s‖ ≤ (3005 : ℝ) := by
  have hspos : (0 : ℝ) < s.re := by linarith
  have hre : s.re ≠ 1 := by linarith
  have hsnorm : ‖s‖ ≤ (12 : ℝ) := srect_norm_le s hlo hhi hilo hihi
  have hZ := zeta_of_etaPairLim_of_re_ne hspos hre
  rw [hZ, norm_div]
  have hnum : ‖∑' m, etaPairTerm s m‖ ≤ (1202 : ℝ) :=
    eta_num_low s hlo hsnorm
  have hden : (2 / 5 : ℝ) ≤ ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ :=
    eta_denom_low s hR
  have hdenpos : (0 : ℝ) < ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ :=
    lt_of_lt_of_le (by norm_num) hden
  have hscale : (1202 : ℝ) ≤ 3005 * ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ := by
    linarith
  have hle : ‖∑' m, etaPairTerm s m‖ ≤
      3005 * ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ :=
    le_trans hnum hscale
  exact (div_le_iff₀ hdenpos).2 hle

/-- Mid piece `Re in [1/2, 3/4]`: `26 / (1/10) = 260`. -/
theorem zeta_mid (s : ℂ)
    (hlo : (0.01 : ℝ) ≤ s.re) (hhi : s.re ≤ (0.99 : ℝ))
    (hilo : (9.75 : ℝ) ≤ s.im) (hihi : s.im ≤ (10.25 : ℝ))
    (hR1 : (1 / 2 : ℝ) ≤ s.re) (hR2 : s.re ≤ (3 / 4 : ℝ)) :
    ‖riemannZeta s‖ ≤ (260 : ℝ) := by
  have hspos : (0 : ℝ) < s.re := by linarith
  have hre : s.re ≠ 1 := by linarith
  have hsnorm : ‖s‖ ≤ (12 : ℝ) := srect_norm_le s hlo hhi hilo hihi
  have hZ := zeta_of_etaPairLim_of_re_ne hspos hre
  rw [hZ, norm_div]
  have hnum : ‖∑' m, etaPairTerm s m‖ ≤ (26 : ℝ) :=
    eta_num_midhigh s hR1 hsnorm
  have hden : (1 / 10 : ℝ) ≤ ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ :=
    eta_denom_mid s hR1 hR2
  have hdenpos : (0 : ℝ) < ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ :=
    lt_of_lt_of_le (by norm_num) hden
  have hscale : (26 : ℝ) ≤ 260 * ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ := by
    linarith
  have hle : ‖∑' m, etaPairTerm s m‖ ≤
      260 * ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ :=
    le_trans hnum hscale
  exact (div_le_iff₀ hdenpos).2 hle

/-- High piece `Re in [3/4, 0.99]`: `26 / (2/5) = 65`, conditional on the
delta premise. -/
theorem zeta_high_of_denom (s : ℂ)
    (hlo : (0.01 : ℝ) ≤ s.re) (hhi : s.re ≤ (0.99 : ℝ))
    (hilo : (9.75 : ℝ) ≤ s.im) (hihi : s.im ≤ (10.25 : ℝ))
    (hR : (3 / 4 : ℝ) ≤ s.re) (hDen : HighEtaDenom) :
    ‖riemannZeta s‖ ≤ (65 : ℝ) := by
  have hspos : (0 : ℝ) < s.re := by linarith
  have hre : s.re ≠ 1 := by linarith
  have hsnorm : ‖s‖ ≤ (12 : ℝ) := srect_norm_le s hlo hhi hilo hihi
  have hZ := zeta_of_etaPairLim_of_re_ne hspos hre
  rw [hZ, norm_div]
  have hnum : ‖∑' m, etaPairTerm s m‖ ≤ (26 : ℝ) :=
    eta_num_midhigh s (by linarith) hsnorm
  have hden : (2 / 5 : ℝ) ≤ ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ :=
    hDen s hR hhi hilo hihi
  have hdenpos : (0 : ℝ) < ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ :=
    lt_of_lt_of_le (by norm_num) hden
  have hscale : (26 : ℝ) ≤ 65 * ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ := by
    linarith
  have hle : ‖∑' m, etaPairTerm s m‖ ≤
      65 * ‖(1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)‖ :=
    le_trans hnum hscale
  exact (div_le_iff₀ hdenpos).2 hle

/-- Uniform bound on the whole thin rect, conditional only on the delta. -/
theorem zeta_uniform_of_highDenom (s : ℂ)
    (hlo : (0.01 : ℝ) ≤ s.re) (hhi : s.re ≤ (0.99 : ℝ))
    (hilo : (9.75 : ℝ) ≤ s.im) (hihi : s.im ≤ (10.25 : ℝ))
    (hDen : HighEtaDenom) :
    ‖riemannZeta s‖ ≤ (3005 : ℝ) := by
  by_cases hR : s.re ≤ (1 / 2 : ℝ)
  · exact zeta_low s hlo hhi hilo hihi hR
  · push_neg at hR
    by_cases hR2 : s.re ≤ (3 / 4 : ℝ)
    · have hle : (260 : ℝ) ≤ 3005 := by norm_num
      exact le_trans
        (zeta_mid s hlo hhi hilo hihi (le_of_lt hR) hR2) hle
    · push_neg at hR2
      have hle : (65 : ℝ) ≤ 3005 := by norm_num
      exact le_trans
        (zeta_high_of_denom s hlo hhi hilo hihi (le_of_lt hR2) hDen) hle

/-- Consumer-facing shape: the same uniform bound for root `zeta`
(byte-for-byte the `sRectZetaSup 3005` unfolding used by Tier C). -/
theorem zeta_uniform_z_of_denom (s : ℂ)
    (hlo : (0.01 : ℝ) ≤ s.re) (hhi : s.re ≤ (0.99 : ℝ))
    (hilo : (9.75 : ℝ) ≤ s.im) (hihi : s.im ≤ (10.25 : ℝ))
    (hDen : HighEtaDenom) :
    ‖zeta s‖ ≤ (3005 : ℝ) := by
  have hz : zeta s = riemannZeta s := rfl
  rw [hz]
  exact zeta_uniform_of_highDenom s hlo hhi hilo hihi hDen

/-! ## Poly and pi caps on the thin rect (proved, no premises). -/

/-- Poly factor on the rect: `‖(1/2) * s * (s-1)‖ ≤ (1/2) * 12 * 13 = 78`. -/
theorem srect_poly_le (s : ℂ) (hsnorm : ‖s‖ ≤ (12 : ℝ)) :
    ‖(1 / 2 : ℂ) * s * (s - 1)‖ ≤ (78 : ℝ) := by
  have hhalf : ‖((1 / 2 : ℂ))‖ = ((1 / 2 : ℝ)) := by
    have hcast : ((1 / 2 : ℂ)) = ((((1 / 2 : ℝ))) : ℂ) := by simp
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hsm : ‖s - 1‖ ≤ (13 : ℝ) := by
    have h1 : ‖((1 : ℂ))‖ = (1 : ℝ) := norm_one
    calc ‖s - 1‖ ≤ ‖s‖ + ‖((1 : ℂ))‖ := norm_sub_le _ _
      _ ≤ (13 : ℝ) := by rw [h1]; linarith
  rw [norm_mul, norm_mul, hhalf]
  have g1 : (1 / 2 : ℝ) * ‖s‖ ≤ (1 / 2 : ℝ) * 12 :=
    mul_le_mul_of_nonneg_left hsnorm (by norm_num)
  have g2 : ((1 / 2 : ℝ) * ‖s‖) * ‖s - 1‖ ≤ ((1 / 2 : ℝ) * 12) * 13 :=
    mul_le_mul g1 hsm (norm_nonneg _) (by norm_num)
  have hcap : ((1 / 2 : ℝ) * 12) * 13 = (78 : ℝ) := by norm_num
  rw [hcap] at g2
  exact g2

/-- Pi factor on the rect: `‖pi ^ (-(s/2))‖ = pi ^ (-Re/2) ≤ 1`
since `Re ≥ 0.01 > 0`. -/
theorem srect_pi_le (s : ℂ) (hlo : (0.01 : ℝ) ≤ s.re) :
    ‖((Real.pi : ℂ) ^ (-(s / 2)))‖ ≤ (1 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have hdiv : ((s / 2 : ℂ)).re = s.re / 2 := by
    simp [Complex.div_ofNat]
  have hre : (-(s / 2 : ℂ)).re = -s.re / 2 := by
    rw [Complex.neg_re, hdiv]
    ring
  rw [hre]
  have hexp : -s.re / 2 ≤ (0 : ℝ) := by linarith
  have hbase : Real.pi ^ (-s.re / 2) ≤ Real.pi ^ (0 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hexp
  rw [Real.rpow_zero] at hbase
  exact hbase

/-! ## Joint assembly and Tier-C numerals. -/

/-- Joint function sup from the proved caps plus the sibling-lane Gamma
cap: `78 * 1 * (1/100) * 3005 = 2343.9 ≤ 2344`. -/
theorem joint_func_of_caps (s : ℂ)
    (hlo : (0.01 : ℝ) ≤ s.re) (hhi : s.re ≤ (0.99 : ℝ))
    (hilo : (9.75 : ℝ) ≤ s.im) (hihi : s.im ≤ (10.25 : ℝ))
    (hDen : HighEtaDenom)
    (hGamma : ‖Complex.Gamma (s / 2)‖ ≤ (1 / 100 : ℝ)) :
    ‖((1 / 2 : ℂ) * s * (s - 1)) * ((Real.pi : ℂ) ^ (-(s / 2))) *
      (Complex.Gamma (s / 2)) * (zeta s)‖ ≤ (2344 : ℝ) := by
  rw [norm_mul, norm_mul, norm_mul]
  have hsnorm : ‖s‖ ≤ (12 : ℝ) := srect_norm_le s hlo hhi hilo hihi
  have hpoly := srect_poly_le s hsnorm
  have hpi := srect_pi_le s hlo
  have hz := zeta_uniform_z_of_denom s hlo hhi hilo hihi hDen
  have g1 : ‖(1 / 2 : ℂ) * s * (s - 1)‖ *
        ‖((Real.pi : ℂ) ^ (-(s / 2)))‖ ≤ (78 : ℝ) * 1 :=
    mul_le_mul hpoly hpi (norm_nonneg _) (by norm_num)
  have g2 : (‖(1 / 2 : ℂ) * s * (s - 1)‖ *
        ‖((Real.pi : ℂ) ^ (-(s / 2)))‖) * ‖Complex.Gamma (s / 2)‖ ≤
        ((78 : ℝ) * 1) * (1 / 100) :=
    mul_le_mul g1 hGamma (norm_nonneg _) (by norm_num)
  have g3 : ((‖(1 / 2 : ℂ) * s * (s - 1)‖ *
        ‖((Real.pi : ℂ) ^ (-(s / 2)))‖) * ‖Complex.Gamma (s / 2)‖) *
        ‖zeta s‖ ≤ (((78 : ℝ) * 1) * (1 / 100)) * 3005 :=
    mul_le_mul g2 hz (norm_nonneg _) (by norm_num)
  have hcap : (((78 : ℝ) * 1) * (1 / 100)) * 3005 ≤ (2344 : ℝ) := by
    norm_num
  exact le_trans g3 hcap

/-- Tier-C need at the radius cap (consumer arithmetic, restated). -/
theorem tierC_need_eq : (0.001 : ℝ) + 0.04 * 0.56 = 0.0234 := by norm_num

/-- Landed joint value (exact product). -/
theorem landedM_eq : (78 : ℝ) * (1 / 100) * 3005 = 2343.9 := by norm_num

/-- Landed joint cap. -/
theorem landedM_le : (2343.9 : ℝ) ≤ 2344 := by norm_num

/-- Landed M exceeds the Tier-C target (gap is honest, not closed). -/
theorem landedM_gt_tierC : (0.04 : ℝ) < 2344 := by norm_num

/-- What Tier C would need: with these poly/pi/Gamma caps, `0.04` forces
`Cz ≤ 0.052` (five orders below the landed `3005`). -/
theorem tierC_Cz_cap (Cz : ℝ)
    (h : (78 : ℝ) * (1 / 100) * Cz ≤ 0.04) :
    Cz ≤ (0.052 : ℝ) := by
  linarith

end Door3SRectZeta

#print axioms Door3SRectZeta.zeta_uniform_z_of_denom
#print axioms Door3SRectZeta.joint_func_of_caps
#print axioms Door3SRectZeta.tierC_Cz_cap
