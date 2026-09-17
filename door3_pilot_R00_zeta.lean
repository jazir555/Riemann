import Mathlib
import central_cover_assembly
import door3_premise_zeta
import door3_cell_suppliers
import zeta_rigorous

open Complex Real Set Topology
open scoped BigOperators

noncomputable section

/-!
# Door 3 pilot zeta-center lower: R00 (floor 1.9), honest wall (step 2: M = 2^21 tail).

Target: `Door3PremiseZeta.premZeta_R00`, i.e. `(1.9 : ℝ) ≤ ‖zeta zs_R00‖`
with `zs_R00 = ⟨0.395, -8.75⟩` (`door3_premise_zeta.lean:66,102`).
Local `sR00` mirrors those coordinates and is linked by `rfl`.

Route (same shape as the banked R05 certificates in
`door3_off_axis_certificates.lean` and the `CS_zeta_of_parts` assembly in
`door3_cell_suppliers.lean:284`, discharged through the generic bridge
`Door3PremiseZeta.zeta_floor_of_eta_bridge`):
* slow (proved lower): `1/5 ≤ ‖S₂‖` via reverse triangle, using only
  `Re = 0.395` (`‖2^{-s}‖ = 2^{-0.395} ≤ 4/5` from banked
  `zetaCellS0_rpow_0395_ge`). Independent of `t`, so it transfers from R05.
* tail (proved uppers): `‖G - S₂‖ ≤ 23` at `M = 1` and `‖G - S₈‖ ≤ 23`
  at `M = 4`, via `zetaCell_even_remainder_le` with proved `‖sR00‖ ≤ 8.76`
  and the trivial `4^{-0.395} ≤ 1` (no estimated numerics).
* factor (proved upper): `‖1 - 2^{1-sR00}‖ ≤ 3` by triangle plus
  `2^0.605 ≤ 2` (honest, self-contained; mirrors `r05_cF_upper`).

Honest outcome: the certificate value `(1/5 - 23)/3 = -38/5` sits far below
the `1.9` floor, so the `CS_zeta_of_parts`-shaped threshold
`1.9 * cF + tail ≤ slow` FAILS on banked numerals
(`1/5 < 1.9 * 3 + 23`). With the rigorous `M = 4` tail, the N = 8
estimate-style gap reads `0.6 - 23 - 0.95 < 0` (slow `0.6` is the premise
recon estimate from `door3_premise_zeta.lean:448`, labelled as such, not a
proved slow upper). `premZeta_R00` is NOT discharged here; best honest
unconditional floor banked: `0 ≤ ‖zeta sR00‖`.

No `sorry` / `admit` / `axiom`. All slow/tail/cF numerals used in the
failing inequality are proved above; the only estimate quoted is the
`0.6` slow reference, explicitly labelled estimate.
-/

namespace Door3PilotR00Zeta

/-! ## R00 center (mirror of the premise center) -/

noncomputable def sR00 : ℂ := ⟨(0.395 : ℝ), (-8.75 : ℝ)⟩

theorem sR00_eq_premise : sR00 = Door3PremiseZeta.zs_R00 := rfl

theorem sR00_re : sR00.re = (0.395 : ℝ) := rfl

theorem sR00_im : sR00.im = (-8.75 : ℝ) := rfl

theorem sR00_pos : 0 < sR00.re := by
  rw [sR00_re]
  norm_num

/-- Premise shape reminder: `premZeta_R00` is the `1.9` floor at `zs_R00`. -/
theorem R00_premise_shape :
    Door3PremiseZeta.premZeta_R00 =
      ((1.9 : ℝ) ≤ ‖zeta Door3PremiseZeta.zs_R00‖) := rfl

/-! ## Norm cap (`‖sR00‖ ≤ 8.76`; `0.395² + 8.75² = 76.718525 ≤ 76.7376`). -/

theorem sR00_norm_le : ‖sR00‖ ≤ (8.76 : ℝ) := by
  have hsq : ‖sR00‖ ^ 2 ≤ (8.76 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, sR00_re, sR00_im]
    norm_num
  have hnn : (0 : ℝ) ≤ ‖sR00‖ := norm_nonneg _
  calc ‖sR00‖ = Real.sqrt (‖sR00‖ ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((8.76 : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = (8.76 : ℝ) := Real.sqrt_sq (by norm_num)

/-! ## Trivial rpow decay upper (`4^{-0.395} ≤ 1`, no estimated numerics). -/

theorem R00_rpow_four_neg0395_le : (4 : ℝ) ^ (-0.395 : ℝ) ≤ 1 := by
  have h : (4 : ℝ) ^ (-0.395 : ℝ) ≤ (4 : ℝ) ^ (0 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [Real.rpow_zero] at h
  exact h

/-! ## Rigorous pair-tails at R00 via `zetaCell_even_remainder_le`. -/

/-- Genuine R00 paired tail at `M = 1` (`‖G - S₂‖ ≤ 23`). -/
theorem R00_eta_tail_M1_le :
    ‖(∑' m, etaPairTerm sR00 m) -
      (∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k)‖ ≤ (23 : ℝ) := by
  have hs : 0 < sR00.re := by
    rw [sR00_re]
    norm_num
  have hC : ‖sR00‖ ≤ (8.76 : ℝ) := sR00_norm_le
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 1 (by norm_num)
  have h21 : 2 * 1 = 2 := by norm_num
  rw [h21] at hgen
  have hre : sR00.re = (0.395 : ℝ) := sR00_re
  rw [hre] at hgen
  have h1 : ((((1 : ℕ)) : ℝ)) = (1 : ℝ) := by norm_cast
  rw [h1, Real.one_rpow] at hgen
  have hle : (8.76 : ℝ) * (1 / (0.395 : ℝ)) ≤ (23 : ℝ) := by norm_num
  linarith

/-- Genuine R00 paired tail at `M = 4` (`‖G - S₈‖ ≤ 23`). -/
theorem R00_eta_tail_M4_le :
    ‖(∑' m, etaPairTerm sR00 m) -
      (∑ k ∈ Finset.range 8, etaDirichletTerm sR00 k)‖ ≤ (23 : ℝ) := by
  have hs : 0 < sR00.re := by
    rw [sR00_re]
    norm_num
  have hC : ‖sR00‖ ≤ (8.76 : ℝ) := sR00_norm_le
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 4 (by norm_num)
  have h24 : 2 * 4 = 8 := by norm_num
  rw [h24] at hgen
  have hre : sR00.re = (0.395 : ℝ) := sR00_re
  rw [hre] at hgen
  have h4c : ((((4 : ℕ)) : ℝ)) = (4 : ℝ) := by norm_cast
  rw [h4c] at hgen
  have hdiv : (4 : ℝ) ^ (-0.395 : ℝ) / (0.395 : ℝ) ≤ 1 / (0.395 : ℝ) := by
    rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 0.395)]
    exact R00_rpow_four_neg0395_le
  have hmul : (8.76 : ℝ) * ((4 : ℝ) ^ (-0.395 : ℝ) / (0.395 : ℝ)) ≤
      (8.76 : ℝ) * (1 / (0.395 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv (by norm_num)
  have hnum : (8.76 : ℝ) * (1 / (0.395 : ℝ)) ≤ (23 : ℝ) := by norm_num
  linarith

/-! ## Proved slow lower (`1/5 ≤ ‖S₂‖`, `t`-independent reverse triangle). -/

/-- R00 two-term eta partial sum in closed form (`S₂ = 1 - (2^s)⁻¹`). -/
theorem R00_eta_S2_eq :
    (∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k)
      = 1 - ((((2 : ℕ) : ℂ) ^ sR00)⁻¹) := by
  have hsum : (∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k)
      = etaDirichletTerm sR00 0 + etaDirichletTerm sR00 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
  have h0 : etaDirichletTerm sR00 0 = 1 := by
    have h01 : (0 + 1 : ℕ) = 1 := rfl
    have hcast : ((((0 + 1 : ℕ)) : ℂ)) = 1 := by
      rw [h01, Nat.cast_one]
    simp only [etaDirichletTerm, pow_zero, hcast, Complex.one_cpow, div_one]
  have h1 : etaDirichletTerm sR00 1
      = -((((2 : ℕ) : ℂ) ^ sR00)⁻¹) := by
    unfold etaDirichletTerm
    rw [pow_one]
    rw [show (((1 + 1 : ℕ) : ℂ)) = ((((2 : ℕ)) : ℂ)) by norm_num]
    rw [neg_div, one_div]
  rw [hsum, h0, h1]
  ring

/-- Modulus of the R00 second eta term (`2^{-0.395} ≤ 4/5`). -/
theorem R00_eta_second_norm_le :
    ‖((((2 : ℕ) : ℂ) ^ sR00)⁻¹)‖ ≤ 4 / 5 := by
  have h2eq : ((((2 : ℕ)) : ℂ)) = (2 : ℂ) := by norm_cast
  rw [h2eq, norm_inv, two_cpow_norm, sR00_re]
  have hge := zetaCellS0_rpow_0395_ge
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (0.395 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  rw [show (4 / 5 : ℝ) = ((5 / 4 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

/-- Genuine R00 finite-sum lower bound (`1/5 ≤ ‖S₂‖`, reverse triangle). -/
theorem R00_eta_S2_norm_ge :
    (1 / 5 : ℝ) ≤ ‖∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k‖ := by
  rw [R00_eta_S2_eq]
  have hX := R00_eta_second_norm_le
  have h := norm_add_le
    (1 - ((((2 : ℕ) : ℂ) ^ sR00)⁻¹))
    ((((2 : ℕ) : ℂ) ^ sR00)⁻¹)
  rw [sub_add_cancel] at h
  rw [norm_one] at h
  linarith

/-! ## Honest eta-factor UPPER at R00 (`≤ 3`, triangle + `2^0.605 ≤ 2`). -/

theorem R00_denom_re : (1 - sR00).re = (0.605 : ℝ) := by
  rw [Complex.sub_re, Complex.one_re, sR00_re]
  norm_num

theorem R00_cF_upper : ‖(1 : ℂ) - ((2 : ℝ) : ℂ) ^ (1 - sR00)‖ ≤ 3 := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hnorm : ‖(((2 : ℝ) : ℂ) ^ (1 - sR00))‖ = (2 : ℝ) ^ (0.605 : ℝ) := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos h2pos (1 - sR00)
    have hre : (1 - sR00).re = (0.605 : ℝ) := by
      rw [Complex.sub_re, Complex.one_re, sR00_re]
      norm_num
    rw [hre] at h
    exact h
  have hpow_le : (2 : ℝ) ^ (0.605 : ℝ) ≤ 2 := by
    have hle : (2 : ℝ) ^ (0.605 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have heq : (2 : ℝ) ^ (1 : ℝ) = 2 := Real.rpow_one 2
    rw [heq] at hle
    exact hle
  have htri := norm_sub_le (1 : ℂ) ((((2 : ℝ) : ℂ) ^ (1 - sR00)))
  rw [hnorm] at htri
  have h1 : ‖(1 : ℂ)‖ = 1 := norm_one
  rw [h1] at htri
  linarith [htri, hpow_le]

theorem R00_cF_pos : (0 : ℝ) < 3 := by norm_num

/-! ## Conditional assembly (proved; threshold stays open — see below). -/

theorem R00_conditional (slow tail cF : ℝ) (hcF : 0 < cF)
    (hLink : slow - tail ≤ cF * ‖zeta sR00‖)
    (hThresh : (1.9 : ℝ) * cF + tail ≤ slow) :
    (1.9 : ℝ) ≤ ‖zeta sR00‖ :=
  Door3PremiseZeta.zeta_floor_of_eta_bridge slow tail cF (1.9 : ℝ) _
    hcF hLink hThresh

/-- Same wrapper at the premise center (rewrite by `sR00_eq_premise`). -/
theorem R00_conditional_premise (slow tail cF : ℝ) (hcF : 0 < cF)
    (hLink : slow - tail ≤ cF * ‖zeta Door3PremiseZeta.zs_R00‖)
    (hThresh : (1.9 : ℝ) * cF + tail ≤ slow) :
    (1.9 : ℝ) ≤ ‖zeta Door3PremiseZeta.zs_R00‖ := by
  have e : Door3PremiseZeta.zs_R00 = sR00 := sR00_eq_premise.symm
  rw [e] at hLink ⊢
  exact R00_conditional slow tail cF hcF hLink hThresh

/-! ## Honest wall: certificate value and the exact failing inequality.

Banked numerals: slow `1/5` (proved `R00_eta_S2_norm_ge`), tail `23`
(proved `R00_eta_tail_M1_le` / `R00_eta_tail_M4_le`), `cF = 3` (proved
`R00_cF_upper`). The `CS_zeta_of_parts`-shaped threshold
`need * cF + tail ≤ slow` at `need = 1.9` reads `28.7 ≤ 0.2`: false.
Exact numeric gap of the certificate value below the floor:
`-38/5 = -7.6` vs `1.9`, i.e. shortfall `9.5`. -/

/-- Exact certificate value: `(1/5 - 23)/3 = -38/5`. -/
theorem R00_cert_value_eq : ((1 / 5 : ℝ) - 23) / 3 = (-38 / 5 : ℝ) := by
  norm_num

/-- The certificate value sits below the `1.9` floor (shortfall `9.5`). -/
theorem R00_cert_below_floor : (-38 / 5 : ℝ) < 1.9 := by
  norm_num

/-- Threshold form of the miss: `1/5 < 1.9 * 3 + 23`, so the
`zeta_floor_of_eta_bridge` / `CS_zeta_of_parts`-shaped `hThresh` premise
fails on banked numerals and `premZeta_R00` is not discharged. -/
theorem R00_bridge_need_open : (1 / 5 : ℝ) < 1.9 * 3 + 23 := by
  norm_num

/-- N = 8 wall with the rigorous `M = 4` tail: estimate slow `0.6` (premise
recon value, `door3_premise_zeta.lean:448`, NOT a proved bound) minus
rigorous tail `23` minus `needEta = 1.9 * 0.5 = 0.95`: gap `-23.35 < 0`. -/
theorem R00_N8_rigorousTail_gap : (0.6 : ℝ) - 23 - 0.95 < 0 := by
  norm_num

/-! ## Wall push (one step): tighter factor (`2.53`) + tighter tail (`M = 8`).

* Factor: `R00_cF_253` reuses the banked `2^0.605 ≤ 1.53`
  (`Door3CellSuppliers.CS_rpow0605_proved`, same real numeral) in the
  `R00_cF_upper` triangle pattern: `‖1 - w‖ ≤ 1 + 1.53 = 2.53`.
  Phase-aware `≤ 1` is out of reach here (R00 phase `8.75 * log 2`
  needs a large mod-`2π` reduction); `2.53` is the honest magnitude route.
* Tail: `R00_eta_tail_M8_le` runs `zetaCell_even_remainder_le` at `M = 8`
  (`S₁₆`). The only new numeral is `8^{-0.395} ≤ 1/2`, i.e. `2 ≤ 8^{0.395}`,
  via `8 = 2^3` and `3 * 0.395 = 1.185 ≥ 1` (integer-exponent comparison,
  no estimated numerics).   Tail drops `23 → 11.1`
  (`8.76 * ((1/2)/0.395) = 876/79 ≈ 11.0886 ≤ 11.1`).
* New certificate value `(1/5 - 11.1)/2.53 = -1090/253 ≈ -4.308` vs the
  old `-38/5 = -7.6`: the wall moves `+3.29`. The threshold
  `1.9 * 2.53 + 11.1 = 15.907 ≤ 0.2` STILL FAILS (gap `15.707`;
  old gap `28.5`), so `premZeta_R00` is still not discharged. Honest
  shortfall of the new certificate below the floor:
  `1.9 - (-1090/253) = 15707/2530 ≈ 6.208` (old shortfall `9.5`). -/

/-- Banked `2^0.605` cap reused at R00 (same real numeral as the CS route). -/
theorem R00_rpow0605_le_153 : (2 : ℝ) ^ (0.605 : ℝ) ≤ (1.53 : ℝ) :=
  Door3CellSuppliers.CS_rpow0605_proved

/-- Tighter eta-factor upper at R00 (`≤ 2.53`, triangle + banked cap). -/
theorem R00_cF_253 : ‖(1 : ℂ) - ((2 : ℝ) : ℂ) ^ (1 - sR00)‖ ≤ (2.53 : ℝ) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hnorm : ‖(((2 : ℝ) : ℂ) ^ (1 - sR00))‖ = (2 : ℝ) ^ (0.605 : ℝ) := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos h2pos (1 - sR00)
    have hre : (1 - sR00).re = (0.605 : ℝ) := by
      rw [Complex.sub_re, Complex.one_re, sR00_re]
      norm_num
    rw [hre] at h
    exact h
  have hpow_le : (2 : ℝ) ^ (0.605 : ℝ) ≤ (1.53 : ℝ) := R00_rpow0605_le_153
  have htri := norm_sub_le (1 : ℂ) ((((2 : ℝ) : ℂ) ^ (1 - sR00)))
  rw [hnorm] at htri
  have h1 : ‖(1 : ℂ)‖ = 1 := norm_one
  rw [h1] at htri
  linarith [htri, hpow_le]

/-- Rpow numeral for the `M = 8` tail (`8^{-0.395} ≤ 1/2`, i.e. `2 ≤ 8^{0.395}`
via `8 = 2^3`, `3 * 0.395 = 1.185 ≥ 1`; no estimated numerics). -/
theorem R00_rpow_eight_neg0395_le_half : (8 : ℝ) ^ (-0.395 : ℝ) ≤ 1 / 2 := by
  have h8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) := by norm_num
  have hge : (2 : ℝ) ≤ (8 : ℝ) ^ (0.395 : ℝ) := by
    rw [h8, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hcast : ((((3 : ℕ)) : ℝ)) = (3 : ℝ) := by norm_cast
    rw [hcast]
    have hexp : (3 : ℝ) * 0.395 = 1.185 := by norm_num
    rw [hexp]
    have hle : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ (1.185 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [Real.rpow_one] at hle
    exact hle
  have hpos : (0 : ℝ) < (8 : ℝ) ^ (0.395 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hneg : (8 : ℝ) ^ (-0.395 : ℝ) = ((8 : ℝ) ^ (0.395 : ℝ))⁻¹ := by
    rw [show (-0.395 : ℝ) = -(0.395 : ℝ) by norm_num,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8)]
  rw [hneg, show (1 / 2 : ℝ) = ((2 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

/-- Genuine R00 paired tail at `M = 8` (`‖G - S₁₆‖ ≤ 11.1`). -/
theorem R00_eta_tail_M8_le :
    ‖(∑' m, etaPairTerm sR00 m) -
      (∑ k ∈ Finset.range 16, etaDirichletTerm sR00 k)‖ ≤ (11.1 : ℝ) := by
  have hs : 0 < sR00.re := by
    rw [sR00_re]
    norm_num
  have hC : ‖sR00‖ ≤ (8.76 : ℝ) := sR00_norm_le
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 8 (by norm_num)
  have h28 : 2 * 8 = 16 := by norm_num
  rw [h28] at hgen
  have hre : sR00.re = (0.395 : ℝ) := sR00_re
  rw [hre] at hgen
  have h8c : ((((8 : ℕ)) : ℝ)) = (8 : ℝ) := by norm_cast
  rw [h8c] at hgen
  have hdiv : (8 : ℝ) ^ (-0.395 : ℝ) / (0.395 : ℝ) ≤ (1 / 2 : ℝ) / (0.395 : ℝ) := by
    rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 0.395)]
    exact R00_rpow_eight_neg0395_le_half
  have hmul : (8.76 : ℝ) * ((8 : ℝ) ^ (-0.395 : ℝ) / (0.395 : ℝ)) ≤
      (8.76 : ℝ) * ((1 / 2 : ℝ) / (0.395 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv (by norm_num)
  have hnum : (8.76 : ℝ) * ((1 / 2 : ℝ) / (0.395 : ℝ)) ≤ (11.1 : ℝ) := by norm_num
  linarith

/-- Exact new certificate value: `(1/5 - 11.1)/2.53 = -1090/253`. -/
theorem R00_cert_value_253_M8_eq :
    (((1 / 5 : ℝ) - 11.1) / 2.53) = (-1090 / 253 : ℝ) := by
  norm_num

/-- The new certificate value still sits below the `1.9` floor. -/
theorem R00_cert_253_M8_below_floor : (-1090 / 253 : ℝ) < 1.9 := by
  norm_num

/-- Threshold form of the remaining miss: `1/5 < 1.9 * 2.53 + 11.1`. -/
theorem R00_bridge_need_open_253_M8 : (1 / 5 : ℝ) < 1.9 * 2.53 + 11.1 := by
  norm_num

/-- Exact threshold gap that remains: `(1.9 * 2.53 + 11.1) - 1/5 = 15707/1000`. -/
theorem R00_gap_253_M8_eq :
    ((1.9 * 2.53 + 11.1 : ℝ) - 1 / 5) = (15707 / 1000 : ℝ) := by
  norm_num

/-- Exact shortfall of the new certificate below the floor:
`1.9 - (-1090/253) = 15707/2530 ≈ 6.208` (old shortfall `9.5`). -/
theorem R00_shortfall_253_M8_eq :
    ((1.9 : ℝ) - (-1090 / 253)) = (15707 / 2530 : ℝ) := by
  norm_num

/-! ## Wall push, step 2: large-M tail (`M = 2097152 = 2^21`, `‖G - S₄₁₉₄₃₀₄‖ ≤ 0.087`).

Route mirrors the banked `zetaCellS0_M2097152` chain
(`zeta_rigorous.lean:2739`): `21 * 0.395 = 8.295 ≥ 8`, so
`M^{0.395} = 2^{8.295} ≥ 2^8 = 256` (integer-exponent comparison, no
estimated numerics). Tail drops `11.1 → 0.087`
(`8.76 * ((1/256)/0.395) = 219/2528 ≈ 0.08663 ≤ 0.087`).
Slow stays `1/5` (proved `R00_eta_S2_norm_ge`), factor stays `2.53`
(proved `R00_cF_253`): reverse-triangle slow lowers cannot beat `1/5`
(extra S₄/S₈ terms only add norm uncertainty), so the tail is the pushed link.
New certificate value `(1/5 - 0.087)/2.53 = 113/2530 ≈ 0.0447` vs the
old `-1090/253 ≈ -4.308`: the wall moves `+4.35`. The threshold
`1.9 * 2.53 + 0.087 = 4.894 ≤ 0.2` STILL FAILS (gap `4.694`;
old gap `15.707`), so `premZeta_R00` is still not discharged. Honest
shortfall of the new certificate below the floor:
`1.9 - 113/2530 = 2347/1265 ≈ 1.855` (old shortfall `6.208`). -/

/-- Rpow base numeral for the large-M tail (`2097152 = 2^21`). -/
theorem R00_M2097152_eq : ((((2097152 : ℕ)) : ℝ)) = (2 : ℝ) ^ (21 : ℕ) := by
  norm_num

/-- Rpow lower for the large-M tail (`256 ≤ M^{0.395}` via
`21 * 0.395 = 8.295 ≥ 8`; mirrors `zetaCellS0_M2097152_rpow_ge`). -/
theorem R00_rpow_M2097152_ge :
    (256 : ℝ) ≤ ((((2097152 : ℕ)) : ℝ) ^ (0.395 : ℝ)) := by
  rw [R00_M2097152_eq]
  have h1 : (((2 : ℝ) ^ (21 : ℕ)) ^ (0.395 : ℝ)) = (2 : ℝ) ^ (((((21 : ℕ)) : ℝ)) * (0.395 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [h1]
  have hexp_ge : (8 : ℝ) ≤ (((((21 : ℕ)) : ℝ)) * (0.395 : ℝ)) := by norm_num
  have h2 : (2 : ℝ) ^ (8 : ℝ) ≤ (2 : ℝ) ^ (((((21 : ℕ)) : ℝ)) * (0.395 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_ge
  have e8 : (8 : ℝ) = ((((8 : ℕ)) : ℝ)) := by norm_num
  have h3 : (2 : ℝ) ^ (8 : ℝ) = 256 := by
    rw [e8, Real.rpow_natCast]
    norm_num
  linarith

/-- Rpow numeral for the large-M tail (`M^{-0.395} ≤ 1/256`). -/
theorem R00_rpow_M2097152_neg0395_le :
    (2097152 : ℝ) ^ (-0.395 : ℝ) ≤ 1 / 256 := by
  have hM : (2097152 : ℝ) = ((((2097152 : ℕ)) : ℝ)) := by norm_cast
  rw [hM]
  have hMpos : (0 : ℝ) < ((((2097152 : ℕ)) : ℝ)) := by
    rw [R00_M2097152_eq]
    positivity
  have hge := R00_rpow_M2097152_ge
  have hpos : (0 : ℝ) < ((((2097152 : ℕ)) : ℝ) ^ (0.395 : ℝ)) :=
    Real.rpow_pos_of_pos hMpos _
  have hneg : ((((2097152 : ℕ)) : ℝ) ^ (-0.395 : ℝ)) = (((((2097152 : ℕ)) : ℝ) ^ (0.395 : ℝ))⁻¹) := by
    rw [show (-0.395 : ℝ) = -(0.395 : ℝ) by norm_num,
      Real.rpow_neg hMpos.le]
  rw [hneg, show (1 / 256 : ℝ) = ((256 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

/-- Genuine R00 paired tail at `M = 2097152` (`‖G - S₄₁₉₄₃₀₄‖ ≤ 0.087`). -/
theorem R00_eta_tail_M2097152_le :
    ‖(∑' m, etaPairTerm sR00 m) -
      (∑ k ∈ Finset.range 4194304, etaDirichletTerm sR00 k)‖ ≤ (0.087 : ℝ) := by
  have hs : 0 < sR00.re := by
    rw [sR00_re]
    norm_num
  have hC : ‖sR00‖ ≤ (8.76 : ℝ) := sR00_norm_le
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 2097152 (by norm_num)
  have h2M : 2 * 2097152 = 4194304 := by norm_num
  rw [h2M] at hgen
  have hre : sR00.re = (0.395 : ℝ) := sR00_re
  rw [hre] at hgen
  have hMc : ((((2097152 : ℕ)) : ℝ)) = (2097152 : ℝ) := by norm_cast
  rw [hMc] at hgen
  have hcap : (2097152 : ℝ) ^ (-0.395 : ℝ) ≤ 1 / 256 :=
    R00_rpow_M2097152_neg0395_le
  have hdiv : (2097152 : ℝ) ^ (-0.395 : ℝ) / (0.395 : ℝ) ≤ (1 / 256 : ℝ) / (0.395 : ℝ) := by
    rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 0.395)]
    exact hcap
  have hmul : (8.76 : ℝ) * ((2097152 : ℝ) ^ (-0.395 : ℝ) / (0.395 : ℝ)) ≤
      (8.76 : ℝ) * ((1 / 256 : ℝ) / (0.395 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv (by norm_num)
  have hnum : (8.76 : ℝ) * ((1 / 256 : ℝ) / (0.395 : ℝ)) ≤ (0.087 : ℝ) := by norm_num
  linarith

/-- Exact new certificate value: `(1/5 - 0.087)/2.53 = 113/2530`. -/
theorem R00_cert_value_253_M2097152_eq :
    (((1 / 5 : ℝ) - 0.087) / 2.53) = (113 / 2530 : ℝ) := by
  norm_num

/-- The new certificate value still sits below the `1.9` floor. -/
theorem R00_cert_253_M2097152_below_floor : (113 / 2530 : ℝ) < 1.9 := by
  norm_num

/-- Threshold form of the remaining miss: `1/5 < 1.9 * 2.53 + 0.087`. -/
theorem R00_bridge_need_open_253_M2097152 : (1 / 5 : ℝ) < 1.9 * 2.53 + 0.087 := by
  norm_num

/-- Exact threshold gap that remains: `(1.9 * 2.53 + 0.087) - 1/5 = 2347/500`. -/
theorem R00_gap_253_M2097152_eq :
    ((1.9 * 2.53 + 0.087 : ℝ) - 1 / 5) = (2347 / 500 : ℝ) := by
  norm_num

/-- Exact shortfall of the new certificate below the floor:
`1.9 - 113/2530 = 2347/1265 ≈ 1.855` (old shortfall `6.208`). -/
theorem R00_shortfall_253_M2097152_eq :
    ((1.9 : ℝ) - (113 / 2530)) = (2347 / 1265 : ℝ) := by
  norm_num

/-! ## ZETA-NEXT slow push: S4 attempt (weak, negative) + S2 tightening `0.20 → 0.23`.

* S4 route: `S₄ = 1 - a + b - c` with `a = (2^s)⁻¹`, `b = (3^s)⁻¹`,
  `c = (4^s)⁻¹`. Term uppers `‖b‖ ≤ 1` (trivial decay) and `‖c‖ ≤ 0.60`
  (banked `CS_rpow4neg_upper_proved`, same real numeral, `t`-independent).
  Reverse triangle from the tightened S2 (`0.23`) gives only
  `‖S₄‖ ≥ 0.23 - 1 - 0.60 = -1.37`, weaker than trivial `0 ≤ ‖S₄‖`.
  So complex S4 does NOT grow slow here (R00 phases `8.75·log n` are not
  constructive; real-σ `CS_etaS4_uncond` shape does not transfer).
  Banked honestly as `R00_eta_S4_norm_ge_neg137`.
* S2 tightening: `‖a‖ = 2^{-0.395} ≤ 0.77` via banked
  `CS_rpow2_proved` (same real numeral, `t`-independent; true `≈ 0.7605`),
  replacing `4/5 = 0.80` from `zetaCellS0_rpow_0395_ge`. Hence
  `‖S₂‖ ≥ 1 - 0.77 = 0.23` (`R00_eta_S2_norm_ge_023`).
* New certificate `(0.23 - 0.087)/2.53 = 143/2530 ≈ 0.0565`
  (was `113/2530 ≈ 0.0447`): wall moves `+30/2530 ≈ +0.0119`.
  Threshold `1.9 * 2.53 + 0.087 = 4.894 ≤ 0.23` STILL FAILS
  (gap `2332/500 = 4.664`; old gap `2347/500 = 4.694`), so
  `premZeta_R00` is still not discharged. Honest shortfall:
  `1.9 - 143/2530 = 2332/1265 ≈ 1.844` (old `2347/1265 ≈ 1.855`). -/

/-- Banked `2^{-0.395} ≤ 0.77` reused at R00 (same real numeral, `t`-independent). -/
theorem R00_rpow2_neg0395_le_077 : (2 : ℝ) ^ (-(0.395 : ℝ)) ≤ (0.77 : ℝ) :=
  Door3CellSuppliers.CS_rpow2_proved

/-- Tighter modulus of the R00 second eta term (`≤ 0.77` via banked cap). -/
theorem R00_eta_second_norm_le_077 :
    ‖((((2 : ℕ) : ℂ) ^ sR00)⁻¹)‖ ≤ (0.77 : ℝ) := by
  have h2eq : ((((2 : ℕ)) : ℂ)) = (2 : ℂ) := by norm_cast
  rw [h2eq, norm_inv, two_cpow_norm, sR00_re]
  have h77 : (2 : ℝ) ^ (-(0.395 : ℝ)) ≤ (0.77 : ℝ) :=
    Door3CellSuppliers.CS_rpow2_proved
  have heq : (((2 : ℝ) ^ (0.395 : ℝ)))⁻¹ = (2 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) _).symm
  rw [heq]
  exact h77

/-- Tightened R00 finite-sum lower bound (`0.23 ≤ ‖S₂‖`, reverse triangle). -/
theorem R00_eta_S2_norm_ge_023 :
    (0.23 : ℝ) ≤ ‖∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k‖ := by
  rw [R00_eta_S2_eq]
  have hX := R00_eta_second_norm_le_077
  have h := norm_add_le
    (1 - ((((2 : ℕ) : ℂ) ^ sR00)⁻¹))
    ((((2 : ℕ) : ℂ) ^ sR00)⁻¹)
  rw [sub_add_cancel] at h
  rw [norm_one] at h
  linarith

/-- Banked `4^{-0.395} ≤ 0.60` reused at R00 (same real numeral, `t`-independent). -/
theorem R00_rpow4_neg0395_le_060 : (4 : ℝ) ^ (-(0.395 : ℝ)) ≤ (0.60 : ℝ) :=
  Door3CellSuppliers.CS_rpow4neg_upper_proved

/-- R00 third eta term in closed form (`term 2 = (3^s)⁻¹`). -/
theorem R00_eta_third_eq :
    etaDirichletTerm sR00 2 = ((((3 : ℕ) : ℂ) ^ sR00)⁻¹) := by
  have e : (2 + 1 : ℕ) = 3 := rfl
  have hcast : ((((2 + 1 : ℕ)) : ℂ)) = ((((3 : ℕ)) : ℂ)) := by rw [e]
  have hneg : (-1 : ℂ) ^ (2 : ℕ) = 1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, one_div]

/-- R00 fourth eta term in closed form (`term 3 = -(4^s)⁻¹`). -/
theorem R00_eta_fourth_eq :
    etaDirichletTerm sR00 3 = -((((4 : ℕ) : ℂ) ^ sR00)⁻¹) := by
  have e : (3 + 1 : ℕ) = 4 := rfl
  have hcast : ((((3 + 1 : ℕ)) : ℂ)) = ((((4 : ℕ)) : ℂ)) := by rw [e]
  have hneg : (-1 : ℂ) ^ (3 : ℕ) = -1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, neg_div, one_div]

/-- R00 four-term eta partial sum in closed form. -/
theorem R00_eta_S4_eq :
    (∑ k ∈ Finset.range 4, etaDirichletTerm sR00 k)
      = 1 - ((((2 : ℕ) : ℂ) ^ sR00)⁻¹)
        + ((((3 : ℕ) : ℂ) ^ sR00)⁻¹) - ((((4 : ℕ) : ℂ) ^ sR00)⁻¹) := by
  have hsum : (∑ k ∈ Finset.range 4, etaDirichletTerm sR00 k)
      = etaDirichletTerm sR00 0 + etaDirichletTerm sR00 1
        + etaDirichletTerm sR00 2 + etaDirichletTerm sR00 3 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h0 : etaDirichletTerm sR00 0 = 1 := by
    have h01 : (0 + 1 : ℕ) = 1 := rfl
    have hcast : ((((0 + 1 : ℕ)) : ℂ)) = 1 := by
      rw [h01, Nat.cast_one]
    simp only [etaDirichletTerm, pow_zero, hcast, Complex.one_cpow, div_one]
  have h1 : etaDirichletTerm sR00 1
      = -((((2 : ℕ) : ℂ) ^ sR00)⁻¹) := by
    unfold etaDirichletTerm
    rw [pow_one]
    rw [show (((1 + 1 : ℕ) : ℂ)) = ((((2 : ℕ)) : ℂ)) by norm_num]
    rw [neg_div, one_div]
  rw [hsum, h0, h1, R00_eta_third_eq, R00_eta_fourth_eq]
  ring

/-- Modulus of the R00 third eta term (`3^{-0.395} ≤ 1`, trivial decay). -/
theorem R00_eta_third_norm_le_one :
    ‖((((3 : ℕ) : ℂ) ^ sR00)⁻¹)‖ ≤ (1 : ℝ) := by
  have h3n : ((((3 : ℕ)) : ℂ)) = (3 : ℂ) := by norm_cast
  have h3r : ((3 : ℂ)) = ((((3 : ℝ)) : ℂ)) := by simp
  rw [h3n, h3r, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 3), sR00_re]
  have heq : (((3 : ℝ) ^ (0.395 : ℝ)))⁻¹ = (3 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) _).symm
  rw [heq]
  have hle : (3 : ℝ) ^ (-(0.395 : ℝ)) ≤ (3 : ℝ) ^ (0 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [Real.rpow_zero] at hle
  exact hle

/-- Modulus of the R00 fourth eta term (`≤ 0.60` via banked cap). -/
theorem R00_eta_fourth_norm_le_060 :
    ‖((((4 : ℕ) : ℂ) ^ sR00)⁻¹)‖ ≤ (0.60 : ℝ) := by
  have h4n : ((((4 : ℕ)) : ℂ)) = (4 : ℂ) := by norm_cast
  have h4r : ((4 : ℂ)) = ((((4 : ℝ)) : ℂ)) := by simp
  rw [h4n, h4r, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 4), sR00_re]
  have h60 : (4 : ℝ) ^ (-(0.395 : ℝ)) ≤ (0.60 : ℝ) :=
    Door3CellSuppliers.CS_rpow4neg_upper_proved
  have heq : (((4 : ℝ) ^ (0.395 : ℝ)))⁻¹ = (4 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4) _).symm
  rw [heq]
  exact h60

/-- Honest weak S4 floor at R00 (`-1.37 ≤ ‖S₄‖`; reverse triangle from
tightened S2 minus the two extra term uppers — weaker than `0`, so S4
does not grow slow). -/
theorem R00_eta_S4_norm_ge_neg137 :
    (-1.37 : ℝ) ≤ ‖∑ k ∈ Finset.range 4, etaDirichletTerm sR00 k‖ := by
  rw [R00_eta_S4_eq]
  have hS2 : (0.23 : ℝ) ≤ ‖((1 : ℂ) - ((((2 : ℕ) : ℂ) ^ sR00)⁻¹))‖ := by
    have h := R00_eta_S2_norm_ge_023
    rw [R00_eta_S2_eq] at h
    exact h
  have hb := R00_eta_third_norm_le_one
  have hc := R00_eta_fourth_norm_le_060
  have hA : ‖((1 : ℂ) - ((((2 : ℕ) : ℂ) ^ sR00)⁻¹)
      + ((((3 : ℕ) : ℂ) ^ sR00)⁻¹))‖
      ≤ ‖((1 : ℂ) - ((((2 : ℕ) : ℂ) ^ sR00)⁻¹)
        + ((((3 : ℕ) : ℂ) ^ sR00)⁻¹) - ((((4 : ℕ) : ℂ) ^ sR00)⁻¹))‖
        + ‖((((4 : ℕ) : ℂ) ^ sR00)⁻¹)‖ := by
    have h := norm_add_le
      ((1 : ℂ) - ((((2 : ℕ) : ℂ) ^ sR00)⁻¹)
        + ((((3 : ℕ) : ℂ) ^ sR00)⁻¹) - ((((4 : ℕ) : ℂ) ^ sR00)⁻¹))
      ((((4 : ℕ) : ℂ) ^ sR00)⁻¹)
    have heq : (((1 : ℂ) - ((((2 : ℕ) : ℂ) ^ sR00)⁻¹)
        + ((((3 : ℕ) : ℂ) ^ sR00)⁻¹) - ((((4 : ℕ) : ℂ) ^ sR00)⁻¹))
        + ((((4 : ℕ) : ℂ) ^ sR00)⁻¹))
        = ((1 : ℂ) - ((((2 : ℕ) : ℂ) ^ sR00)⁻¹)
          + ((((3 : ℕ) : ℂ) ^ sR00)⁻¹)) := by abel
    rw [heq] at h
    exact h
  have hB : ‖((1 : ℂ) - ((((2 : ℕ) : ℂ) ^ sR00)⁻¹))‖
      ≤ ‖((1 : ℂ) - ((((2 : ℕ) : ℂ) ^ sR00)⁻¹)
        + ((((3 : ℕ) : ℂ) ^ sR00)⁻¹))‖
        + ‖((((3 : ℕ) : ℂ) ^ sR00)⁻¹)‖ := by
    have h := norm_sub_le
      ((1 : ℂ) - ((((2 : ℕ) : ℂ) ^ sR00)⁻¹)
        + ((((3 : ℕ) : ℂ) ^ sR00)⁻¹))
      ((((3 : ℕ) : ℂ) ^ sR00)⁻¹)
    have heq : (((1 : ℂ) - ((((2 : ℕ) : ℂ) ^ sR00)⁻¹)
        + ((((3 : ℕ) : ℂ) ^ sR00)⁻¹)) - ((((3 : ℕ) : ℂ) ^ sR00)⁻¹))
        = ((1 : ℂ) - ((((2 : ℕ) : ℂ) ^ sR00)⁻¹)) := by abel
    rw [heq] at h
    exact h
  linarith

/-- Exact new certificate value with tightened slow: `(0.23 - 0.087)/2.53`. -/
theorem R00_cert_value_023_M2097152_eq :
    (((0.23 : ℝ) - 0.087) / 2.53) = (143 / 2530 : ℝ) := by
  norm_num

/-- The tightened certificate value still sits below the `1.9` floor. -/
theorem R00_cert_023_M2097152_below_floor : (143 / 2530 : ℝ) < 1.9 := by
  norm_num

/-- Threshold form of the remaining miss with tightened slow. -/
theorem R00_bridge_need_open_023_M2097152 : (0.23 : ℝ) < 1.9 * 2.53 + 0.087 := by
  norm_num

/-- Exact threshold gap that remains: `(1.9 * 2.53 + 0.087) - 0.23`. -/
theorem R00_gap_023_M2097152_eq :
    ((1.9 * 2.53 + 0.087 : ℝ) - 0.23) = (2332 / 500 : ℝ) := by
  norm_num

/-- Exact shortfall of the tightened certificate below the floor. -/
theorem R00_shortfall_023_M2097152_eq :
    ((1.9 : ℝ) - (143 / 2530)) = (2332 / 1265 : ℝ) := by
  norm_num

/-! ## Best honest unconditional floor banked here. -/

/-- Best honest unconditional lower bound available in this closure. -/
theorem R00_best_unconditional : (0 : ℝ) ≤ ‖zeta sR00‖ :=
  norm_nonneg _

#print axioms sR00_norm_le
#print axioms R00_eta_tail_M1_le
#print axioms R00_eta_tail_M4_le
#print axioms R00_eta_S2_norm_ge
#print axioms R00_cF_upper
#print axioms R00_cert_value_eq
#print axioms R00_cert_below_floor
#print axioms R00_bridge_need_open
#print axioms R00_N8_rigorousTail_gap
#print axioms R00_rpow0605_le_153
#print axioms R00_cF_253
#print axioms R00_rpow_eight_neg0395_le_half
#print axioms R00_eta_tail_M8_le
#print axioms R00_cert_value_253_M8_eq
#print axioms R00_cert_253_M8_below_floor
#print axioms R00_bridge_need_open_253_M8
#print axioms R00_gap_253_M8_eq
#print axioms R00_shortfall_253_M8_eq
#print axioms R00_M2097152_eq
#print axioms R00_rpow_M2097152_ge
#print axioms R00_rpow_M2097152_neg0395_le
#print axioms R00_eta_tail_M2097152_le
#print axioms R00_cert_value_253_M2097152_eq
#print axioms R00_cert_253_M2097152_below_floor
#print axioms R00_bridge_need_open_253_M2097152
#print axioms R00_gap_253_M2097152_eq
#print axioms R00_shortfall_253_M2097152_eq
#print axioms R00_rpow2_neg0395_le_077
#print axioms R00_eta_second_norm_le_077
#print axioms R00_eta_S2_norm_ge_023
#print axioms R00_rpow4_neg0395_le_060
#print axioms R00_eta_S4_eq
#print axioms R00_eta_third_norm_le_one
#print axioms R00_eta_fourth_norm_le_060
#print axioms R00_eta_S4_norm_ge_neg137
#print axioms R00_cert_value_023_M2097152_eq
#print axioms R00_gap_023_M2097152_eq
#print axioms R00_shortfall_023_M2097152_eq

end Door3PilotR00Zeta
