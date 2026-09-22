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

/-! ## ZETA-NEXT2 tail-vs-slow: `M = 2^22` stalls, `M = 2^23` halves to `0.044`.

* `M = 4194304 = 2^22`: `22 * 0.395 = 8.69 ≥ 8` but `< 9`, so the
  integer-exponent route still gives only `256 ≤ M^{0.395}`, i.e.
  `M^{-0.395} ≤ 1/256`, tail `≤ 0.087` (no gain vs `M = 2^21`).
  Banked as an honest stall witness.
* `M = 8388608 = 2^23`: `23 * 0.395 = 9.085 ≥ 9`, so `512 ≤ M^{0.395}`,
  `M^{-0.395} ≤ 1/512`, tail `8.76 * ((1/512)/0.395) ≤ 0.044`.
  Genuine halving vs `0.087`.
* Slow stays `0.23` (`R00_eta_S2_norm_ge_023`, BINDING); S4 weak `-1.37`
  abandoned as weaker-than-zero; phase-aware slow NOT banked here
  (needs `log 3 / log 5` bridges at R00 phases `8.75 * log n`;
  only `log 2` exact available — sweep notes filed, not fixed).
* New certificate `(0.23 - 0.044)/2.53 = 186/2530 ≈ 0.0735`
  (was `143/2530 ≈ 0.0565`): wall moves `+43/2530 ≈ +0.0170`.
  Threshold `1.9 * 2.53 + 0.044 = 4.851 ≤ 0.23` STILL FAILS
  (gap `4621/1000 = 4.621`; old gap `2332/500 = 4.664`), so
  `premZeta_R00` is still not discharged. Honest shortfall:
  `1.9 - 186/2530 = 4621/2530 ≈ 1.827` (old `2332/1265 ≈ 1.844`). -/

/-- Rpow base numeral for the `M = 2^22` stall (`4194304 = 2^22`). -/
theorem R00_M4194304_eq : ((((4194304 : ℕ)) : ℝ)) = (2 : ℝ) ^ (22 : ℕ) := by
  norm_num

/-- Rpow lower for the `M = 2^22` stall (`256 ≤ M^{0.395}`; `22 * 0.395 ≥ 8`). -/
theorem R00_rpow_M4194304_ge :
    (256 : ℝ) ≤ ((((4194304 : ℕ)) : ℝ) ^ (0.395 : ℝ)) := by
  rw [R00_M4194304_eq]
  have h1 : (((2 : ℝ) ^ (22 : ℕ)) ^ (0.395 : ℝ)) = (2 : ℝ) ^ (((((22 : ℕ)) : ℝ)) * (0.395 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [h1]
  have hexp_ge : (8 : ℝ) ≤ (((((22 : ℕ)) : ℝ)) * (0.395 : ℝ)) := by norm_num
  have h2 : (2 : ℝ) ^ (8 : ℝ) ≤ (2 : ℝ) ^ (((((22 : ℕ)) : ℝ)) * (0.395 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_ge
  have e8 : (8 : ℝ) = ((((8 : ℕ)) : ℝ)) := by norm_num
  have h3 : (2 : ℝ) ^ (8 : ℝ) = 256 := by
    rw [e8, Real.rpow_natCast]
    norm_num
  linarith

/-- Rpow numeral for the `M = 2^22` stall (`M^{-0.395} ≤ 1/256`). -/
theorem R00_rpow_M4194304_neg0395_le :
    (4194304 : ℝ) ^ (-0.395 : ℝ) ≤ 1 / 256 := by
  have hM : (4194304 : ℝ) = ((((4194304 : ℕ)) : ℝ)) := by norm_cast
  rw [hM]
  have hMpos : (0 : ℝ) < ((((4194304 : ℕ)) : ℝ)) := by
    rw [R00_M4194304_eq]
    positivity
  have hge := R00_rpow_M4194304_ge
  have hpos : (0 : ℝ) < ((((4194304 : ℕ)) : ℝ) ^ (0.395 : ℝ)) :=
    Real.rpow_pos_of_pos hMpos _
  have hneg : ((((4194304 : ℕ)) : ℝ) ^ (-0.395 : ℝ)) = (((((4194304 : ℕ)) : ℝ) ^ (0.395 : ℝ))⁻¹) := by
    rw [show (-0.395 : ℝ) = -(0.395 : ℝ) by norm_num,
      Real.rpow_neg hMpos.le]
  rw [hneg, show (1 / 256 : ℝ) = ((256 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

/-- Stall witness: R00 paired tail at `M = 4194304` (`‖G - S₈₃₈₈₆₀₈‖ ≤ 0.087`). -/
theorem R00_eta_tail_M4194304_le :
    ‖(∑' m, etaPairTerm sR00 m) -
      (∑ k ∈ Finset.range 8388608, etaDirichletTerm sR00 k)‖ ≤ (0.087 : ℝ) := by
  have hs : 0 < sR00.re := by
    rw [sR00_re]
    norm_num
  have hC : ‖sR00‖ ≤ (8.76 : ℝ) := sR00_norm_le
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 4194304 (by norm_num)
  have h2M : 2 * 4194304 = 8388608 := by norm_num
  rw [h2M] at hgen
  have hre : sR00.re = (0.395 : ℝ) := sR00_re
  rw [hre] at hgen
  have hMc : ((((4194304 : ℕ)) : ℝ)) = (4194304 : ℝ) := by norm_cast
  rw [hMc] at hgen
  have hcap : (4194304 : ℝ) ^ (-0.395 : ℝ) ≤ 1 / 256 :=
    R00_rpow_M4194304_neg0395_le
  have hdiv : (4194304 : ℝ) ^ (-0.395 : ℝ) / (0.395 : ℝ) ≤ (1 / 256 : ℝ) / (0.395 : ℝ) := by
    rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 0.395)]
    exact hcap
  have hmul : (8.76 : ℝ) * ((4194304 : ℝ) ^ (-0.395 : ℝ) / (0.395 : ℝ)) ≤
      (8.76 : ℝ) * ((1 / 256 : ℝ) / (0.395 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv (by norm_num)
  have hnum : (8.76 : ℝ) * ((1 / 256 : ℝ) / (0.395 : ℝ)) ≤ (0.087 : ℝ) := by norm_num
  linarith

/-- Rpow base numeral for the halving tail (`8388608 = 2^23`). -/
theorem R00_M8388608_eq : ((((8388608 : ℕ)) : ℝ)) = (2 : ℝ) ^ (23 : ℕ) := by
  norm_num

/-- Rpow lower for the halving tail (`512 ≤ M^{0.395}` via `23 * 0.395 ≥ 9`). -/
theorem R00_rpow_M8388608_ge :
    (512 : ℝ) ≤ ((((8388608 : ℕ)) : ℝ) ^ (0.395 : ℝ)) := by
  rw [R00_M8388608_eq]
  have h1 : (((2 : ℝ) ^ (23 : ℕ)) ^ (0.395 : ℝ)) = (2 : ℝ) ^ (((((23 : ℕ)) : ℝ)) * (0.395 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [h1]
  have hexp_ge : (9 : ℝ) ≤ (((((23 : ℕ)) : ℝ)) * (0.395 : ℝ)) := by norm_num
  have h2 : (2 : ℝ) ^ (9 : ℝ) ≤ (2 : ℝ) ^ (((((23 : ℕ)) : ℝ)) * (0.395 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_ge
  have e9 : (9 : ℝ) = ((((9 : ℕ)) : ℝ)) := by norm_num
  have h3 : (2 : ℝ) ^ (9 : ℝ) = 512 := by
    rw [e9, Real.rpow_natCast]
    norm_num
  linarith

/-- Rpow numeral for the halving tail (`M^{-0.395} ≤ 1/512`). -/
theorem R00_rpow_M8388608_neg0395_le :
    (8388608 : ℝ) ^ (-0.395 : ℝ) ≤ 1 / 512 := by
  have hM : (8388608 : ℝ) = ((((8388608 : ℕ)) : ℝ)) := by norm_cast
  rw [hM]
  have hMpos : (0 : ℝ) < ((((8388608 : ℕ)) : ℝ)) := by
    rw [R00_M8388608_eq]
    positivity
  have hge := R00_rpow_M8388608_ge
  have hpos : (0 : ℝ) < ((((8388608 : ℕ)) : ℝ) ^ (0.395 : ℝ)) :=
    Real.rpow_pos_of_pos hMpos _
  have hneg : ((((8388608 : ℕ)) : ℝ) ^ (-0.395 : ℝ)) = (((((8388608 : ℕ)) : ℝ) ^ (0.395 : ℝ))⁻¹) := by
    rw [show (-0.395 : ℝ) = -(0.395 : ℝ) by norm_num,
      Real.rpow_neg hMpos.le]
  rw [hneg, show (1 / 512 : ℝ) = ((512 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

/-- Genuine R00 paired tail at `M = 8388608` (`‖G - S₁₆₇₇₇₂₁₆‖ ≤ 0.044`). -/
theorem R00_eta_tail_M8388608_le :
    ‖(∑' m, etaPairTerm sR00 m) -
      (∑ k ∈ Finset.range 16777216, etaDirichletTerm sR00 k)‖ ≤ (0.044 : ℝ) := by
  have hs : 0 < sR00.re := by
    rw [sR00_re]
    norm_num
  have hC : ‖sR00‖ ≤ (8.76 : ℝ) := sR00_norm_le
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 8388608 (by norm_num)
  have h2M : 2 * 8388608 = 16777216 := by norm_num
  rw [h2M] at hgen
  have hre : sR00.re = (0.395 : ℝ) := sR00_re
  rw [hre] at hgen
  have hMc : ((((8388608 : ℕ)) : ℝ)) = (8388608 : ℝ) := by norm_cast
  rw [hMc] at hgen
  have hcap : (8388608 : ℝ) ^ (-0.395 : ℝ) ≤ 1 / 512 :=
    R00_rpow_M8388608_neg0395_le
  have hdiv : (8388608 : ℝ) ^ (-0.395 : ℝ) / (0.395 : ℝ) ≤ (1 / 512 : ℝ) / (0.395 : ℝ) := by
    rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 0.395)]
    exact hcap
  have hmul : (8.76 : ℝ) * ((8388608 : ℝ) ^ (-0.395 : ℝ) / (0.395 : ℝ)) ≤
      (8.76 : ℝ) * ((1 / 512 : ℝ) / (0.395 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv (by norm_num)
  have hnum : (8.76 : ℝ) * ((1 / 512 : ℝ) / (0.395 : ℝ)) ≤ (0.044 : ℝ) := by norm_num
  linarith

/-- Exact new certificate value with halved tail: `(0.23 - 0.044)/2.53`. -/
theorem R00_cert_value_023_M8388608_eq :
    (((0.23 : ℝ) - 0.044) / 2.53) = (186 / 2530 : ℝ) := by
  norm_num

/-- The halved-tail certificate value still sits below the `1.9` floor. -/
theorem R00_cert_023_M8388608_below_floor : (186 / 2530 : ℝ) < 1.9 := by
  norm_num

/-- Threshold form of the remaining miss with halved tail. -/
theorem R00_bridge_need_open_023_M8388608 : (0.23 : ℝ) < 1.9 * 2.53 + 0.044 := by
  norm_num

/-- Exact threshold gap that remains: `(1.9 * 2.53 + 0.044) - 0.23`. -/
theorem R00_gap_023_M8388608_eq :
    ((1.9 * 2.53 + 0.044 : ℝ) - 0.23) = (4621 / 1000 : ℝ) := by
  norm_num

/-- Exact shortfall of the halved-tail certificate below the floor. -/
theorem R00_shortfall_023_M8388608_eq :
    ((1.9 : ℝ) - (186 / 2530)) = (4621 / 2530 : ℝ) := by
  norm_num

/-! ## ZETA-NEXT3 log bridges + phase-aware slow term (`n = 5`).

* Log bridges (R00-usable lane-local aliases; proofs are `exact` / short
  `linarith` from the banked `Door3CellSuppliers` lemmas, which another lane
  owns — nothing duplicated): `log 3` (`1.0529 ≤ log 3 ≤ 1.1363`),
  `log 4 = 2·log 2` (`1.386294 ≤ log 4 ≤ 1.386296`), `log 5`
  (`16094/10000 ≤ log 5 ≤ 16095/10000`), `log 6 = log 2 + log 3`
  (`1.74604 ≤ log 6 ≤ 1.8295`).
* Banked rpow shapes reused at R00 (`t`-independent real numerals):
  `3^0.395 ≤ 1.57`, `0.63 ≤ 3^-0.395`, `5^0.395 ≤ 1.90`,
  `0.52 ≤ 5^-0.395`, `1.92 ≤ 6^0.395`, `6^-0.395 ≤ 0.53`.
* Phase-aware slow term (`n = 5`, eta sign `+1`): the fifth eta term has
  closed form `(5^s)⁻¹`, norm `≥ 0.52`, and — the new piece — cpow real
  part `5^-0.395·cos(8.75·log 5) ≥ 0`. The cosine floor comes from the
  `log 5` bridge: `8.75·log 5 ∈ [14.08225, 14.08313]`, so the phase shifted
  by `2·2π` sits in `[1.51, 1.52] ⊆ [-π/2, π/2]` (via `pi_gt_d6` /
  `pi_lt_d6`), where cosine is nonnegative. True `cos(8.75·log 5) ≈ 0.053`,
  so `≥ 0` is safe with large margin.
* Honest status: the binding slow stays `0.23` (`R00_eta_S2_norm_ge_023`);
  the `Re₅ ≥ 0` piece does not yet assemble into a stronger certificate
  (`Re` floors for the `n = 3, 4` eta terms, and the `inv_re` bridge from
  the cpow form to the eta-term form, are still open — sweep notes filed,
  not fixed). Threshold gap stays `4621/1000 = 4.621`, shortfall stays
  `4621/2530 ≈ 1.827` (`R00_gap_023_M8388608_eq`,
  `R00_shortfall_023_M8388608_eq`). -/

/-- R00-usable `log 3` lower (banked supplier bridge). -/
theorem R00_log_three_ge : (1.0529 : ℝ) ≤ Real.log 3 :=
  Door3CellSuppliers.CS_log_three_ge

/-- R00-usable `log 3` upper (banked supplier bridge). -/
theorem R00_log_three_le : Real.log 3 ≤ (1.1363 : ℝ) :=
  Door3CellSuppliers.CS_log_three_le

/-- R00-usable `log 4 = 2 * log 2` (banked supplier bridge). -/
theorem R00_log_four_eq : Real.log 4 = 2 * Real.log 2 :=
  Door3CellSuppliers.CS_log_four_eq

/-- R00-usable `log 4` lower (`2 * 0.693147 = 1.386294`). -/
theorem R00_log_four_ge : (1.386294 : ℝ) ≤ Real.log 4 := by
  have h4 := R00_log_four_eq
  have h2 := Door3CellSuppliers.CS_log2_ge
  linarith

/-- R00-usable `log 4` upper (`2 * 0.693148 = 1.386296`). -/
theorem R00_log_four_le : Real.log 4 ≤ (1.386296 : ℝ) := by
  have h4 := R00_log_four_eq
  have h2 := Door3CellSuppliers.CS_log2_le
  linarith

/-- R00-usable `log 5` lower (banked supplier bridge). -/
theorem R00_log_five_ge : (16094 / 10000 : ℝ) ≤ Real.log 5 :=
  Door3CellSuppliers.CS_log_five_ge

/-- R00-usable `log 5` upper (banked supplier bridge). -/
theorem R00_log_five_le : Real.log 5 ≤ (16095 / 10000 : ℝ) :=
  Door3CellSuppliers.CS_log_five_le

/-- R00-usable `log 6 = log 2 + log 3` (banked supplier bridge). -/
theorem R00_log_six_eq : Real.log 6 = Real.log 2 + Real.log 3 :=
  Door3CellSuppliers.CS_log_six_eq

/-- R00-usable `log 6` lower (banked supplier bridge). -/
theorem R00_log_six_ge : (1.74604 : ℝ) ≤ Real.log 6 :=
  Door3CellSuppliers.CS_log_six_ge

/-- R00-usable `log 6` upper (banked supplier bridge). -/
theorem R00_log_six_le : Real.log 6 ≤ (1.8295 : ℝ) :=
  Door3CellSuppliers.CS_log_six_le

/-- Banked `3^0.395 ≤ 1.57` reused at R00 (same real numeral). -/
theorem R00_rpow3_pos_le_157 : (3 : ℝ) ^ ((0.395 : ℝ)) ≤ (1.57 : ℝ) :=
  Door3CellSuppliers.CS_rpow3pos_proved

/-- Banked `0.63 ≤ 3^-0.395` reused at R00 (same real numeral). -/
theorem R00_rpow3_neg_ge_063 : (0.63 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ)) :=
  Door3CellSuppliers.CS_rpow3neg_lower_proved

/-- Banked `5^0.395 ≤ 1.90` reused at R00 (same real numeral). -/
theorem R00_rpow5_pos_le_190 : (5 : ℝ) ^ ((0.395 : ℝ)) ≤ (1.90 : ℝ) :=
  Door3CellSuppliers.CS_rpow5pos_proved

/-- Banked `0.52 ≤ 5^-0.395` reused at R00 (same real numeral). -/
theorem R00_rpow5_neg_ge_052 : (0.52 : ℝ) ≤ (5 : ℝ) ^ (-(0.395 : ℝ)) :=
  Door3CellSuppliers.CS_rpow5neg_lower_proved

/-- Banked `1.92 ≤ 6^0.395` reused at R00 (same real numeral). -/
theorem R00_rpow6_pos_ge_192 : (1.92 : ℝ) ≤ (6 : ℝ) ^ ((0.395 : ℝ)) :=
  Door3CellSuppliers.CS_rpow6pos_proved

/-- Banked `6^-0.395 ≤ 0.53` reused at R00 (same real numeral). -/
theorem R00_rpow6_neg_le_053 : (6 : ℝ) ^ (-(0.395 : ℝ)) ≤ (0.53 : ℝ) :=
  Door3CellSuppliers.CS_rpow6neg_upper_proved

/-- R00 phase lower for `n = 5` (`8.75 * 1.6094 = 14.08225`). -/
theorem R00_phase5_ge : (14.08225 : ℝ) ≤ 8.75 * Real.log 5 := by
  have h := R00_log_five_ge
  have hmul : (8.75 : ℝ) * (16094 / 10000) ≤ 8.75 * Real.log 5 :=
    mul_le_mul_of_nonneg_left h (by norm_num)
  have hcap : (14.08225 : ℝ) ≤ (8.75 : ℝ) * (16094 / 10000) := by norm_num
  linarith

/-- R00 phase upper for `n = 5` (`8.75 * 1.6095 = 14.083125 ≤ 14.08313`). -/
theorem R00_phase5_le : 8.75 * Real.log 5 ≤ (14.08313 : ℝ) := by
  have h := R00_log_five_le
  have hmul : (8.75 : ℝ) * Real.log 5 ≤ 8.75 * (16095 / 10000) :=
    mul_le_mul_of_nonneg_left h (by norm_num)
  have hcap : (8.75 : ℝ) * (16095 / 10000) ≤ (14.08313 : ℝ) := by norm_num
  linarith

/-- Phase-aware cosine floor at R00 for `n = 5` (`cos(8.75·log 5) ≥ 0`;
true `≈ 0.053`). Route: shift by `2·2π` into `[-π/2, π/2]` via the phase
caps above + `pi_gt_d6` / `pi_lt_d6`, then `cos_nonneg`. -/
theorem R00_cos_875log5_nonneg : (0 : ℝ) ≤ Real.cos (8.75 * Real.log 5) := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have hlo : -(Real.pi / 2) ≤ 8.75 * Real.log 5 - 2 * Real.pi - 2 * Real.pi := by
    have hmul : (8.75 : ℝ) * (16094 / 10000) ≤ 8.75 * Real.log 5 :=
      mul_le_mul_of_nonneg_left R00_log_five_ge (by norm_num)
    have hcap : (14.08225 : ℝ) ≤ (8.75 : ℝ) * (16094 / 10000) := by norm_num
    have hpi2 : 2 * Real.pi + 2 * Real.pi
        ≤ 2 * (3.141593 : ℝ) + 2 * (3.141593 : ℝ) := by
      linarith
    have hpin : (0 : ℝ) ≤ Real.pi := by linarith
    linarith
  have hhi : 8.75 * Real.log 5 - 2 * Real.pi - 2 * Real.pi ≤ Real.pi / 2 := by
    have hmul : (8.75 : ℝ) * Real.log 5 ≤ 8.75 * (16095 / 10000) :=
      mul_le_mul_of_nonneg_left R00_log_five_le (by norm_num)
    have hcap : (8.75 : ℝ) * (16095 / 10000) ≤ (14.08313 : ℝ) := by norm_num
    linarith
  have hnn := Real.cos_nonneg_of_neg_pi_div_two_le_of_le hlo hhi
  have hper1 := Real.cos_sub_two_pi (8.75 * Real.log 5 - 2 * Real.pi)
  have hper2 := Real.cos_sub_two_pi (8.75 * Real.log 5)
  have heq : Real.cos (8.75 * Real.log 5 - 2 * Real.pi - 2 * Real.pi)
      = Real.cos (8.75 * Real.log 5) := by
    rw [hper1, hper2]
  rw [heq] at hnn
  exact hnn

/-- Cpow real-part split at R00 for `n = 5` (mirrors the banked
`CS_cpow2_sCenter_re` recipe: `(-sR00).re = -0.395`, `(-sR00).im = 8.75`,
so the `exp` re-part is `5^-0.395·cos(8.75·log 5)`). -/
theorem R00_cpow5_neg_re : ((((5 : ℝ)) : ℂ) ^ (-sR00)).re
    = (5 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (8.75 * Real.log 5) := by
  have h5pos : (0 : ℝ) < 5 := by norm_num
  have hxC : ((5 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h5pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((5 : ℝ) : ℂ) = (((Real.log 5 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h5pos)).symm
  rw [hlog]
  have hre_w : (-sR00).re = (-(0.395 : ℝ)) := by
    have e : (-sR00).re = -(sR00.re) := rfl
    rw [e, sR00_re]
  have him_w : (-sR00).im = (8.75 : ℝ) := by
    have e : (-sR00).im = -(sR00.im) := rfl
    rw [e, sR00_im]
    norm_num
  have hzre : ((((Real.log 5 : ℝ)) : ℂ)).re = Real.log 5 := Complex.ofReal_re _
  have hzim : ((((Real.log 5 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 5 : ℝ)) : ℂ) * (-sR00)).re
      = Real.log 5 * (-(0.395 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 5 : ℝ)) : ℂ) * (-sR00)).im
      = Real.log 5 * (8.75 : ℝ) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 5 * (-(0.395 : ℝ)))
      = (5 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_def_of_pos h5pos _).symm
  have hcos : Real.cos (Real.log 5 * (8.75 : ℝ))
      = Real.cos (8.75 * Real.log 5) := by
    rw [mul_comm]
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- Phase-aware slow term at R00 for `n = 5`: the cpow real part is
nonnegative (amplitude `≥ 0` times the banked cosine floor). -/
theorem R00_cpow5_neg_Re_nonneg :
    (0 : ℝ) ≤ ((((5 : ℝ)) : ℂ) ^ (-sR00)).re := by
  rw [R00_cpow5_neg_re]
  have hcos := R00_cos_875log5_nonneg
  have hr0 : (0 : ℝ) ≤ (5 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  exact mul_nonneg hr0 hcos

/-- R00 fifth eta term in closed form (`term 4 = (5^s)⁻¹`, sign `+1`). -/
theorem R00_eta_fifth_eq :
    etaDirichletTerm sR00 4 = ((((5 : ℕ) : ℂ) ^ sR00)⁻¹) := by
  have e : (4 + 1 : ℕ) = 5 := rfl
  have hcast : ((((4 + 1 : ℕ)) : ℂ)) = ((((5 : ℕ)) : ℂ)) := by rw [e]
  have hneg : (-1 : ℂ) ^ (4 : ℕ) = 1 := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, one_div]

/-- Modulus lower for the R00 fifth eta term (`≥ 0.52` via banked cap). -/
theorem R00_eta_fifth_norm_ge_052 :
    (0.52 : ℝ) ≤ ‖((((5 : ℕ) : ℂ) ^ sR00)⁻¹)‖ := by
  have h5n : ((((5 : ℕ)) : ℂ)) = (5 : ℂ) := by norm_cast
  have h5r : ((5 : ℂ)) = ((((5 : ℝ)) : ℂ)) := by simp
  rw [h5n, h5r, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 5), sR00_re]
  have hlow : (0.52 : ℝ) ≤ (5 : ℝ) ^ (-(0.395 : ℝ)) :=
    Door3CellSuppliers.CS_rpow5neg_lower_proved
  have heq : (((5 : ℝ) ^ (0.395 : ℝ)))⁻¹ = (5 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 5) _).symm
  rw [heq]
  exact hlow

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
#print axioms R00_M4194304_eq
#print axioms R00_rpow_M4194304_ge
#print axioms R00_rpow_M4194304_neg0395_le
#print axioms R00_eta_tail_M4194304_le
#print axioms R00_M8388608_eq
#print axioms R00_rpow_M8388608_ge
#print axioms R00_rpow_M8388608_neg0395_le
#print axioms R00_eta_tail_M8388608_le
#print axioms R00_cert_value_023_M8388608_eq
#print axioms R00_gap_023_M8388608_eq
#print axioms R00_shortfall_023_M8388608_eq
#print axioms R00_log_three_ge
#print axioms R00_log_three_le
#print axioms R00_log_four_eq
#print axioms R00_log_four_ge
#print axioms R00_log_four_le
#print axioms R00_log_five_ge
#print axioms R00_log_five_le
#print axioms R00_log_six_eq
#print axioms R00_log_six_ge
#print axioms R00_log_six_le
#print axioms R00_rpow3_pos_le_157
#print axioms R00_rpow3_neg_ge_063
#print axioms R00_rpow5_pos_le_190
#print axioms R00_rpow5_neg_ge_052
#print axioms R00_rpow6_pos_ge_192
#print axioms R00_rpow6_neg_le_053
#print axioms R00_phase5_ge
#print axioms R00_phase5_le
#print axioms R00_cos_875log5_nonneg
#print axioms R00_cpow5_neg_re
#print axioms R00_cpow5_neg_Re_nonneg
#print axioms R00_eta_fifth_eq
#print axioms R00_eta_fifth_norm_ge_052

/-! ## ZETA-NEXT4 phase-aware slow terms (`n = 3, 4`) + `inv_re` bridge + S5 assembly.

* Phase windows (mirror the term-5 recipe `R00_phase5_ge/le`):
  `φ₃ = 8.75·log 3 ∈ [9.21287, 9.94263]` via `R00_log_three_ge/le`
  (`8.75·1.0529 = 9.212875`, `8.75·1.1363 = 9.942625`);
  `φ₄ = 8.75·log 4 ∈ [12.13007, 12.13009]` via `R00_log_four_ge/le`
  (`8.75·1.386294 = 12.1300725`, `8.75·1.386296 = 12.13009`).
* `2kπ` shifts: `θ₃ = φ₃ - 2π ∈ [2.92, 3.66]` (near `π`: destructive phase,
  true `cos ≈ -0.98`, so only the signed floor `cos ≥ -1` is banked);
  `θ₄ = φ₄ - 2π - 2π ∈ [-0.44, -0.43] ⊆ [-π/2, π/2]` (via `pi_gt_d6` /
  `pi_lt_d6`), so `cos(8.75·log 4) ≥ 0` by `cos_nonneg` + `cos_sub_two_pi`
  (true `≈ 0.906`, large margin).
* Cpow real-part splits at R00 for `n = 3, 4` (mirror `R00_cpow5_neg_re`):
  `n^(-0.395)·cos(8.75·log n)`; floors `-1` (`n = 3`, trivial amplitude
  upper + `neg_one_le_cos`) and `≥ 0` (`n = 4`, nonnegative amplitude
  times the cosine floor).
* `inv_re` bridge (eta-term form to Re form): `((((n:ℕ)):ℂ)^sR00)⁻¹`
  `= ((((n:ℝ)):ℂ)^(-sR00))` via `(Complex.cpow_neg _ _).symm`, so each
  eta-term real part equals the cpow Re form above. Gives
  `Re(term 2) ≥ -1`, `Re(term 3) ≥ -0.60` (minus sign + `cos_le_one` +
  banked `R00_rpow4_neg0395_le_060`), `Re(term 4) ≥ 0`.
* Honest assembly: `‖S₅‖ ≥ 0.23 - 1 - 0.60 - 1 = -2.37` (reverse triangle
  from `R00_eta_S2_norm_ge_023`), weaker than trivial `0`; the `n = 3`
  phase is destructive (`θ₃ ≈ π`) and `term 3` carries the eta minus
  sign, so phase-aware slow does NOT grow here. Binding slow stays
  `0.23`; certificate recomputed with identical numerals
  (`186/2530`, gap `4621/1000 = 4.621`, shortfall `4621/2530`). -/

/-- R00 phase lower for `n = 3` (`8.75 * 1.0529 = 9.212875`). -/
theorem R00_phase3_ge : (9.21287 : ℝ) ≤ 8.75 * Real.log 3 := by
  have h := R00_log_three_ge
  have hmul : (8.75 : ℝ) * (1.0529) ≤ 8.75 * Real.log 3 :=
    mul_le_mul_of_nonneg_left h (by norm_num)
  have hcap : (9.21287 : ℝ) ≤ (8.75 : ℝ) * (1.0529) := by norm_num
  linarith

/-- R00 phase upper for `n = 3` (`8.75 * 1.1363 = 9.942625 ≤ 9.94263`). -/
theorem R00_phase3_le : 8.75 * Real.log 3 ≤ (9.94263 : ℝ) := by
  have h := R00_log_three_le
  have hmul : (8.75 : ℝ) * Real.log 3 ≤ 8.75 * (1.1363) :=
    mul_le_mul_of_nonneg_left h (by norm_num)
  have hcap : (8.75 : ℝ) * (1.1363) ≤ (9.94263 : ℝ) := by norm_num
  linarith

/-- R00 phase lower for `n = 4` (`8.75 * 1.386294 = 12.1300725`). -/
theorem R00_phase4_ge : (12.13007 : ℝ) ≤ 8.75 * Real.log 4 := by
  have h := R00_log_four_ge
  have hmul : (8.75 : ℝ) * (1.386294) ≤ 8.75 * Real.log 4 :=
    mul_le_mul_of_nonneg_left h (by norm_num)
  have hcap : (12.13007 : ℝ) ≤ (8.75 : ℝ) * (1.386294) := by norm_num
  linarith

/-- R00 phase upper for `n = 4` (`8.75 * 1.386296 = 12.13009`). -/
theorem R00_phase4_le : 8.75 * Real.log 4 ≤ (12.13009 : ℝ) := by
  have h := R00_log_four_le
  have hmul : (8.75 : ℝ) * Real.log 4 ≤ 8.75 * (1.386296) :=
    mul_le_mul_of_nonneg_left h (by norm_num)
  have hcap : (8.75 : ℝ) * (1.386296) ≤ (12.13009 : ℝ) := by norm_num
  linarith

/-- Shifted phase window for `n = 3` (`φ₃ - 2π ∈ [2.92, 3.66]`, near `π`). -/
theorem R00_theta3_shift_mem :
    (2.92 : ℝ) ≤ 8.75 * Real.log 3 - 2 * Real.pi ∧
      8.75 * Real.log 3 - 2 * Real.pi ≤ (3.66 : ℝ) := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have hlo := R00_phase3_ge
  have hhi := R00_phase3_le
  constructor <;> linarith

/-- Shifted phase window for `n = 4` (`φ₄ - 2π - 2π ∈ [-0.44, -0.43]`). -/
theorem R00_theta4_shift_mem :
    (-(0.44) : ℝ) ≤ 8.75 * Real.log 4 - 2 * Real.pi - 2 * Real.pi ∧
      8.75 * Real.log 4 - 2 * Real.pi - 2 * Real.pi ≤ (-(0.43) : ℝ) := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have hlo := R00_phase4_ge
  have hhi := R00_phase4_le
  have hpi2 : 2 * Real.pi + 2 * Real.pi
      ≤ 2 * (3.141593 : ℝ) + 2 * (3.141593 : ℝ) := by
    linarith
  constructor <;> linarith

/-- Signed cosine floor at R00 for `n = 3` (`cos ≥ -1`; the shifted phase
sits near `π`, so no nonnegative floor is available). -/
theorem R00_cos_875log3_ge_neg1 : (-1 : ℝ) ≤ Real.cos (8.75 * Real.log 3) :=
  Real.neg_one_le_cos _

/-- Phase-aware cosine floor at R00 for `n = 4` (`cos(8.75·log 4) ≥ 0`).
Route: shift by `2·2π` into `[-π/2, π/2]` via the phase caps above +
`pi_gt_d6` / `pi_lt_d6`, then `cos_nonneg` (mirrors `R00_cos_875log5_nonneg`). -/
theorem R00_cos_875log4_nonneg : (0 : ℝ) ≤ Real.cos (8.75 * Real.log 4) := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have hlo : -(Real.pi / 2) ≤ 8.75 * Real.log 4 - 2 * Real.pi - 2 * Real.pi := by
    have hmul : (8.75 : ℝ) * (1.386294) ≤ 8.75 * Real.log 4 :=
      mul_le_mul_of_nonneg_left R00_log_four_ge (by norm_num)
    have hcap : (12.13007 : ℝ) ≤ (8.75 : ℝ) * (1.386294) := by norm_num
    have hpi2 : 2 * Real.pi + 2 * Real.pi
        ≤ 2 * (3.141593 : ℝ) + 2 * (3.141593 : ℝ) := by
      linarith
    have hpin : (0 : ℝ) ≤ Real.pi := by linarith
    linarith
  have hhi : 8.75 * Real.log 4 - 2 * Real.pi - 2 * Real.pi ≤ Real.pi / 2 := by
    have hmul : (8.75 : ℝ) * Real.log 4 ≤ 8.75 * (1.386296) :=
      mul_le_mul_of_nonneg_left R00_log_four_le (by norm_num)
    have hcap : (8.75 : ℝ) * (1.386296) ≤ (12.13009 : ℝ) := by norm_num
    linarith
  have hnn := Real.cos_nonneg_of_neg_pi_div_two_le_of_le hlo hhi
  have hper1 := Real.cos_sub_two_pi (8.75 * Real.log 4 - 2 * Real.pi)
  have hper2 := Real.cos_sub_two_pi (8.75 * Real.log 4)
  have heq : Real.cos (8.75 * Real.log 4 - 2 * Real.pi - 2 * Real.pi)
      = Real.cos (8.75 * Real.log 4) := by
    rw [hper1, hper2]
  rw [heq] at hnn
  exact hnn

/-- Cpow real-part split at R00 for `n = 3` (mirrors `R00_cpow5_neg_re`). -/
theorem R00_cpow3_neg_re : ((((3 : ℝ)) : ℂ) ^ (-sR00)).re
    = (3 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (8.75 * Real.log 3) := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hxC : ((3 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h3pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((3 : ℝ) : ℂ) = (((Real.log 3 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h3pos)).symm
  rw [hlog]
  have hre_w : (-sR00).re = (-(0.395 : ℝ)) := by
    have e : (-sR00).re = -(sR00.re) := rfl
    rw [e, sR00_re]
  have him_w : (-sR00).im = (8.75 : ℝ) := by
    have e : (-sR00).im = -(sR00.im) := rfl
    rw [e, sR00_im]
    norm_num
  have hzre : ((((Real.log 3 : ℝ)) : ℂ)).re = Real.log 3 := Complex.ofReal_re _
  have hzim : ((((Real.log 3 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 3 : ℝ)) : ℂ) * (-sR00)).re
      = Real.log 3 * (-(0.395 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 3 : ℝ)) : ℂ) * (-sR00)).im
      = Real.log 3 * (8.75 : ℝ) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 3 * (-(0.395 : ℝ)))
      = (3 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_def_of_pos h3pos _).symm
  have hcos : Real.cos (Real.log 3 * (8.75 : ℝ))
      = Real.cos (8.75 * Real.log 3) := by
    rw [mul_comm]
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- Cpow real-part split at R00 for `n = 4` (mirrors `R00_cpow5_neg_re`;
`log 4 = 2·log 2` is used only upstream in the phase caps). -/
theorem R00_cpow4_neg_re : ((((4 : ℝ)) : ℂ) ^ (-sR00)).re
    = (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (8.75 * Real.log 4) := by
  have h4pos : (0 : ℝ) < 4 := by norm_num
  have hxC : ((4 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h4pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((4 : ℝ) : ℂ) = (((Real.log 4 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h4pos)).symm
  rw [hlog]
  have hre_w : (-sR00).re = (-(0.395 : ℝ)) := by
    have e : (-sR00).re = -(sR00.re) := rfl
    rw [e, sR00_re]
  have him_w : (-sR00).im = (8.75 : ℝ) := by
    have e : (-sR00).im = -(sR00.im) := rfl
    rw [e, sR00_im]
    norm_num
  have hzre : ((((Real.log 4 : ℝ)) : ℂ)).re = Real.log 4 := Complex.ofReal_re _
  have hzim : ((((Real.log 4 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 4 : ℝ)) : ℂ) * (-sR00)).re
      = Real.log 4 * (-(0.395 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 4 : ℝ)) : ℂ) * (-sR00)).im
      = Real.log 4 * (8.75 : ℝ) := by
    rw [Complex.mul_im, hzre, hzim, him_w]
    ring
  have hexp : Real.exp (Real.log 4 * (-(0.395 : ℝ)))
      = (4 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_def_of_pos h4pos _).symm
  have hcos : Real.cos (Real.log 4 * (8.75 : ℝ))
      = Real.cos (8.75 * Real.log 4) := by
    rw [mul_comm]
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- Phase-aware slow floor at R00 for `n = 3` (signed: amplitude `≤ 1`
times `cos ≥ -1`). -/
theorem R00_cpow3_neg_Re_ge_neg1 :
    (-1 : ℝ) ≤ ((((3 : ℝ)) : ℂ) ^ (-sR00)).re := by
  rw [R00_cpow3_neg_re]
  have hamp_le : (3 : ℝ) ^ (-(0.395 : ℝ)) ≤ 1 := by
    have h : (3 : ℝ) ^ (-(0.395 : ℝ)) ≤ (3 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [Real.rpow_zero] at h
    exact h
  have hcos := R00_cos_875log3_ge_neg1
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have h1 : (3 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (8.75 * Real.log 3)
      ≥ (3 : ℝ) ^ (-(0.395 : ℝ)) * (-1) :=
    mul_le_mul_of_nonneg_left hcos hr0
  have h2 : (3 : ℝ) ^ (-(0.395 : ℝ)) * (-1) ≥ -1 := by
    linarith
  linarith

/-- Phase-aware slow floor at R00 for `n = 4` (nonnegative). -/
theorem R00_cpow4_neg_Re_nonneg :
    (0 : ℝ) ≤ ((((4 : ℝ)) : ℂ) ^ (-sR00)).re := by
  rw [R00_cpow4_neg_re]
  have hcos := R00_cos_875log4_nonneg
  have hr0 : (0 : ℝ) ≤ (4 : ℝ) ^ (-(0.395 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  exact mul_nonneg hr0 hcos

/-- `inv_re` bridge for `n = 3` (eta-term inverse form to cpow Re form). -/
theorem R00_inv_three_cpow_re_eq :
    (((((3 : ℕ)) : ℂ) ^ sR00)⁻¹).re
      = (3 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (8.75 * Real.log 3) := by
  have h3n : ((((3 : ℕ)) : ℂ)) = (3 : ℂ) := by norm_cast
  have h3r : ((3 : ℂ)) = ((((3 : ℝ)) : ℂ)) := by simp
  have hcp : ((((3 : ℝ)) : ℂ) ^ sR00)⁻¹ = ((((3 : ℝ)) : ℂ) ^ (-sR00)) :=
    (Complex.cpow_neg _ _).symm
  rw [h3n, h3r, hcp]
  exact R00_cpow3_neg_re

/-- `inv_re` bridge for `n = 4` (eta-term inverse form to cpow Re form). -/
theorem R00_inv_four_cpow_re_eq :
    (((((4 : ℕ)) : ℂ) ^ sR00)⁻¹).re
      = (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (8.75 * Real.log 4) := by
  have h4n : ((((4 : ℕ)) : ℂ)) = (4 : ℂ) := by norm_cast
  have h4r : ((4 : ℂ)) = ((((4 : ℝ)) : ℂ)) := by simp
  have hcp : ((((4 : ℝ)) : ℂ) ^ sR00)⁻¹ = ((((4 : ℝ)) : ℂ) ^ (-sR00)) :=
    (Complex.cpow_neg _ _).symm
  rw [h4n, h4r, hcp]
  exact R00_cpow4_neg_re

/-- `inv_re` bridge for `n = 5` (eta-term inverse form to cpow Re form). -/
theorem R00_inv_five_cpow_re_eq :
    (((((5 : ℕ)) : ℂ) ^ sR00)⁻¹).re
      = (5 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (8.75 * Real.log 5) := by
  have h5n : ((((5 : ℕ)) : ℂ)) = (5 : ℂ) := by norm_cast
  have h5r : ((5 : ℂ)) = ((((5 : ℝ)) : ℂ)) := by simp
  have hcp : ((((5 : ℝ)) : ℂ) ^ sR00)⁻¹ = ((((5 : ℝ)) : ℂ) ^ (-sR00)) :=
    (Complex.cpow_neg _ _).symm
  rw [h5n, h5r, hcp]
  exact R00_cpow5_neg_re

/-- Real part of the R00 third eta term (`-1 ≤ Re term 2`). -/
theorem R00_eta_third_Re_ge_neg1 :
    (-1 : ℝ) ≤ (etaDirichletTerm sR00 2).re := by
  rw [R00_eta_third_eq]
  have h := R00_cpow3_neg_Re_ge_neg1
  have h3n : ((((3 : ℕ)) : ℂ)) = (3 : ℂ) := by norm_cast
  have h3r : ((3 : ℂ)) = ((((3 : ℝ)) : ℂ)) := by simp
  have hcp : ((((3 : ℝ)) : ℂ) ^ sR00)⁻¹ = ((((3 : ℝ)) : ℂ) ^ (-sR00)) :=
    (Complex.cpow_neg _ _).symm
  rw [h3n, h3r, hcp]
  exact h

/-- Real part of the R00 fourth eta term (`-0.60 ≤ Re term 3`; the eta
minus sign flips the nonnegative `n = 4` inverse floor, capped by the
banked amplitude upper and `cos_le_one`). -/
theorem R00_eta_fourth_Re_ge_neg060 :
    (-(0.60) : ℝ) ≤ (etaDirichletTerm sR00 3).re := by
  rw [R00_eta_fourth_eq, Complex.neg_re]
  have hup : (((((4 : ℕ)) : ℂ) ^ sR00)⁻¹).re ≤ (0.60 : ℝ) := by
    rw [R00_inv_four_cpow_re_eq]
    have hamp := R00_rpow4_neg0395_le_060
    have hcos_le := Real.cos_le_one (8.75 * Real.log 4)
    have hcos_nn := R00_cos_875log4_nonneg
    have hamp_nn : (0 : ℝ) ≤ (4 : ℝ) ^ (-(0.395 : ℝ)) :=
      le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    have hprod : (4 : ℝ) ^ (-(0.395 : ℝ)) * Real.cos (8.75 * Real.log 4)
        ≤ (0.60 : ℝ) * 1 :=
      mul_le_mul hamp hcos_le hcos_nn (by norm_num)
    have heq : (0.60 : ℝ) * 1 = 0.60 := by norm_num
    linarith
  linarith

/-- Real part of the R00 fifth eta term (`0 ≤ Re term 4`, via the bridge
to the banked cpow floor). -/
theorem R00_eta_fifth_Re_nonneg :
    (0 : ℝ) ≤ (etaDirichletTerm sR00 4).re := by
  rw [R00_eta_fifth_eq]
  have h := R00_cpow5_neg_Re_nonneg
  have h5n : ((((5 : ℕ)) : ℂ)) = (5 : ℂ) := by norm_cast
  have h5r : ((5 : ℂ)) = ((((5 : ℝ)) : ℂ)) := by simp
  have hcp : ((((5 : ℝ)) : ℂ) ^ sR00)⁻¹ = ((((5 : ℝ)) : ℂ) ^ (-sR00)) :=
    (Complex.cpow_neg _ _).symm
  rw [h5n, h5r, hcp]
  exact h

/-- Phase-aware first-pair real part at R00 (`-1.60 ≤ Re(term 2 + term 3)`). -/
theorem R00_pair1_Re_ge_neg160 :
    (-(1.60) : ℝ) ≤ (etaDirichletTerm sR00 2 + etaDirichletTerm sR00 3).re := by
  rw [Complex.add_re]
  have h2 := R00_eta_third_Re_ge_neg1
  have h3 := R00_eta_fourth_Re_ge_neg060
  linarith

/-- Modulus of the R00 fifth eta term (`≤ 1`, trivial decay). -/
theorem R00_eta_fifth_norm_le_one :
    ‖((((5 : ℕ) : ℂ) ^ sR00)⁻¹)‖ ≤ (1 : ℝ) := by
  have h5n : ((((5 : ℕ)) : ℂ)) = (5 : ℂ) := by norm_cast
  have h5r : ((5 : ℂ)) = ((((5 : ℝ)) : ℂ)) := by simp
  rw [h5n, h5r, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 5), sR00_re]
  have heq : (((5 : ℝ) ^ (0.395 : ℝ)))⁻¹ = (5 : ℝ) ^ (-(0.395 : ℝ)) :=
    (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 5) _).symm
  rw [heq]
  have hle : (5 : ℝ) ^ (-(0.395 : ℝ)) ≤ (5 : ℝ) ^ (0 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [Real.rpow_zero] at hle
  exact hle

/-- R00 five-term eta partial sum split at `S₂` (`S₅ = S₂ + t₂ + t₃ + t₄`). -/
theorem R00_eta_S5_eq :
    (∑ k ∈ Finset.range 5, etaDirichletTerm sR00 k)
      = (∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k)
        + etaDirichletTerm sR00 2 + etaDirichletTerm sR00 3
        + etaDirichletTerm sR00 4 := by
  rw [show (5 : ℕ) = 4 + 1 by norm_num, Finset.sum_range_succ,
    show (4 : ℕ) = 3 + 1 by norm_num, Finset.sum_range_succ,
    show (3 : ℕ) = 2 + 1 by norm_num, Finset.sum_range_succ]

/-- Honest S5 stall witness at R00 (`-2.37 ≤ ‖S₅‖`; reverse triangle from
the binding `0.23` S2 floor minus the three extra term uppers — weaker
than trivial `0`, so phase-aware slow does not grow and the binding slow
stays `0.23`). -/
theorem R00_eta_S5_norm_ge_neg237 :
    (-2.37 : ℝ) ≤ ‖∑ k ∈ Finset.range 5, etaDirichletTerm sR00 k‖ := by
  rw [R00_eta_S5_eq]
  have hS2 := R00_eta_S2_norm_ge_023
  have hb := R00_eta_third_norm_le_one
  have hc := R00_eta_fourth_norm_le_060
  have hd := R00_eta_fifth_norm_le_one
  have h1 : ‖(∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k)‖
      ≤ ‖(∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k)
        + etaDirichletTerm sR00 2‖ + ‖etaDirichletTerm sR00 2‖ := by
    have h := norm_sub_le
      ((∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k) + etaDirichletTerm sR00 2)
      (etaDirichletTerm sR00 2)
    have heq : (((∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k)
        + etaDirichletTerm sR00 2) - etaDirichletTerm sR00 2)
        = (∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k) := by abel
    rw [heq] at h
    exact h
  have h2 : ‖(∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k)
        + etaDirichletTerm sR00 2‖
      ≤ ‖(∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k)
        + etaDirichletTerm sR00 2 + etaDirichletTerm sR00 3‖
        + ‖etaDirichletTerm sR00 3‖ := by
    have h := norm_sub_le
      ((∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k)
        + etaDirichletTerm sR00 2 + etaDirichletTerm sR00 3)
      (etaDirichletTerm sR00 3)
    have heq : (((∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k)
        + etaDirichletTerm sR00 2 + etaDirichletTerm sR00 3)
        - etaDirichletTerm sR00 3)
        = ((∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k)
          + etaDirichletTerm sR00 2) := by abel
    rw [heq] at h
    exact h
  have h3 : ‖(∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k)
        + etaDirichletTerm sR00 2 + etaDirichletTerm sR00 3‖
      ≤ ‖(∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k)
        + etaDirichletTerm sR00 2 + etaDirichletTerm sR00 3
        + etaDirichletTerm sR00 4‖ + ‖etaDirichletTerm sR00 4‖ := by
    have h := norm_sub_le
      ((∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k)
        + etaDirichletTerm sR00 2 + etaDirichletTerm sR00 3
        + etaDirichletTerm sR00 4)
      (etaDirichletTerm sR00 4)
    have heq : (((∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k)
        + etaDirichletTerm sR00 2 + etaDirichletTerm sR00 3
        + etaDirichletTerm sR00 4) - etaDirichletTerm sR00 4)
        = ((∑ k ∈ Finset.range 2, etaDirichletTerm sR00 k)
          + etaDirichletTerm sR00 2 + etaDirichletTerm sR00 3) := by abel
    rw [heq] at h
    exact h
  have t2 : ‖etaDirichletTerm sR00 2‖ ≤ (1 : ℝ) := by
    rw [R00_eta_third_eq]; exact hb
  have t3 : ‖etaDirichletTerm sR00 3‖ ≤ (0.60 : ℝ) := by
    rw [R00_eta_fourth_eq, norm_neg]; exact hc
  have t4 : ‖etaDirichletTerm sR00 4‖ ≤ (1 : ℝ) := by
    rw [R00_eta_fifth_eq]; exact hd
  linarith [hS2, h1, h2, h3, t2, t3, t4]

/-- Exact certificate value with phase-aware slow attempt (binding slow
stays `0.23` by the S5 stall): `(0.23 - 0.044)/2.53 = 186/2530`. -/
theorem R00_cert_value_023_M8388608_phase5_eq :
    (((0.23 : ℝ) - 0.044) / 2.53) = (186 / 2530 : ℝ) := by
  norm_num

/-- The phase-5 certificate value still sits below the `1.9` floor. -/
theorem R00_cert_023_M8388608_phase5_below_floor : (186 / 2530 : ℝ) < 1.9 := by
  norm_num

/-- Threshold form of the remaining miss with phase-5 slow attempt. -/
theorem R00_bridge_need_open_023_M8388608_phase5 :
    (0.23 : ℝ) < 1.9 * 2.53 + 0.044 := by
  norm_num

/-- Exact threshold gap that remains: `(1.9 * 2.53 + 0.044) - 0.23`. -/
theorem R00_gap_023_M8388608_phase5_eq :
    ((1.9 * 2.53 + 0.044 : ℝ) - 0.23) = (4621 / 1000 : ℝ) := by
  norm_num

/-- Exact shortfall of the phase-5 certificate below the floor. -/
theorem R00_shortfall_023_M8388608_phase5_eq :
    ((1.9 : ℝ) - (186 / 2530)) = (4621 / 2530 : ℝ) := by
  norm_num

#print axioms R00_phase3_ge
#print axioms R00_phase3_le
#print axioms R00_phase4_ge
#print axioms R00_phase4_le
#print axioms R00_theta3_shift_mem
#print axioms R00_theta4_shift_mem
#print axioms R00_cos_875log3_ge_neg1
#print axioms R00_cos_875log4_nonneg
#print axioms R00_cpow3_neg_re
#print axioms R00_cpow4_neg_re
#print axioms R00_cpow3_neg_Re_ge_neg1
#print axioms R00_cpow4_neg_Re_nonneg
#print axioms R00_inv_three_cpow_re_eq
#print axioms R00_inv_four_cpow_re_eq
#print axioms R00_inv_five_cpow_re_eq
#print axioms R00_eta_third_Re_ge_neg1
#print axioms R00_eta_fourth_Re_ge_neg060
#print axioms R00_eta_fifth_Re_nonneg
#print axioms R00_pair1_Re_ge_neg160
#print axioms R00_eta_fifth_norm_le_one
#print axioms R00_eta_S5_eq
#print axioms R00_eta_S5_norm_ge_neg237
#print axioms R00_cert_value_023_M8388608_phase5_eq
#print axioms R00_gap_023_M8388608_phase5_eq
#print axioms R00_shortfall_023_M8388608_phase5_eq

/-! ## ZETA-SCUT sCut pilot (parked here; `door3_zeta_cutoff.lean` untouched).

R00 re-route exhausted (`R00_eta_S5_norm_ge_neg237` stalls at `-2.37` on
destructive phases). This section redirects to the cutoff slow-sum at
`sCut = 1/2 + 10*I` (`door3_zeta_cutoff.lean:16`).

Banked shapes reused READ-ONLY (exact statement + line):
* `hSlow/hTail/hEnough`: `Door3ZetaCutoff.zeta_cutoff_lower_of_certificate_one`
  (`door3_zeta_cutoff.lean:353-359`): `slow ≤ ‖S‖`, `‖G - S‖ ≤ rtail`,
  `rtail < slow ⟹ slow - rtail ≤ ‖riemannZeta sCut‖`; consumer
  `cutR10_zetaRemainder_of_certificate_one` (`door3_zeta_cutoff.lean:384-389`)
  needs `hEnough : 7/5 + rtail ≤ slow`.
* `rtail` CLOSED at `M = 2048`: `Door3OffAxis.sCutOA11_eta_tail_2048_le`
  (`door3_off_axis_certificates.lean:8460-8463`): `‖G - S4096‖ ≤ 7/10`,
  via `sCutOA11_M2048_rpow_ge` (`:8426`) + `sCutOA11_r_2048_le` (`:8437`);
  threshold `sCutOA11_hEnough_2048_threshold` (`:8473`) gives
  `7/5 + 7/10 = 21/10 ≤ slow'`. NOTE: banked point is `sCutOA11 = 1/2+11*I`
  (`:8368`); the tail numerals use only `Re = 1/2` + `‖s‖ ≤ 12`, so the
  identical proof transfers verbatim to `sCut = 1/2+10*I` below
  (`sSCUT_eta_tail_2048_le`). The `sCutOA` (`t = 10`) banked triple is only
  `slow = 2/7`, `rtail = 24` (`sCutOA_slow` `:8336`, `sCutOA_rtail` `:8345`).
* Slow recipe mirrored (not duplicated): `CS_complex_S4_Re_ge_156`
  (`door3_cell_suppliers.lean:2213`, `Re ≥ 1.56` via per-term cpow splits
  `CS_cpow2/3/4_sCenter_re` + cos/rpow floors) and `CS_complex_S6_Re_ge_095`
  (`:2621`). Below mirrors that phase/norm-split pattern at sCut coords.

SMALL-shard outcome (honest): `S₂ ≥ 2/7` banked (`sSCUT_S2_slow`); per-term
norm uppers for `k = 2..7` (`n = 3..8`) are each `≤ 1`, so reverse triangle
from `S₂` gives only `‖S₈‖ ≥ -40/7` (`sSCUT_S8_norm_ge_neg40div7`) — weaker
than `0`, i.e. the shard does NOT grow toward `21/10`. Defeating window:
`10 * log 3 ∈ [10.529, 11.363]` (`sSCUT_theta3_mem`, width `0.834` from the
wide banked `CS_log_three_ge/le`), so no `Re₃` sign-lock is available with
banked bridges — STOP here for the `N = 4096` slow push; binding sCut slow
stays `2/7`, shortfall vs `21/10` is `127/70 ≈ 1.814`.
-/

/-- sCut mirror parked in this file (`1/2 + 10*I`; cutoff file untouched). -/
noncomputable def sSCUT : ℂ := (1 / 2 : ℂ) + 10 * Complex.I

theorem sSCUT_re : sSCUT.re = (1 / 2 : ℝ) := by simp [sSCUT]

theorem sSCUT_im : sSCUT.im = (10 : ℝ) := by simp [sSCUT]

theorem sSCUT_pos : 0 < sSCUT.re := by rw [sSCUT_re]; norm_num

theorem sSCUT_norm_le : ‖sSCUT‖ ≤ (12 : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im sSCUT
  have hre : |sSCUT.re| = (1 / 2 : ℝ) := by rw [sSCUT_re]; norm_num
  have him : |sSCUT.im| = (10 : ℝ) := by rw [sSCUT_im]; norm_num
  rw [hre, him] at h
  linarith

/-- sCut phase cosine floor (`3/4 ≤ cos(10*log 2)`; mirror of
`Door3ZetaCutoff.cutoff_phase_cos_lower`, banked-bridge route only). -/
theorem sSCUT_cos10log2_ge : (3 / 4 : ℝ) ≤ Real.cos (10 * Real.log 2) := by
  have hloglo := Real.log_two_gt_d9
  have hloghi := Real.log_two_lt_d9
  have hθlo : (6.931471803 : ℝ) < 10 * Real.log 2 := by linarith
  have hθhi : 10 * Real.log 2 < (6.931471808 : ℝ) := by linarith
  have hπlo := Real.pi_gt_d4
  have hπhi := Real.pi_lt_d4
  have hdlo : (0.6482 : ℝ) < 10 * Real.log 2 - 2 * Real.pi := by linarith
  have hdhi : 10 * Real.log 2 - 2 * Real.pi < (0.6486 : ℝ) := by linarith
  have hsq : (10 * Real.log 2 - 2 * Real.pi) ^ 2 ≤ (0.6486 : ℝ) ^ 2 := by
    have hp : 0 ≤ 10 * Real.log 2 - 2 * Real.pi := by linarith
    nlinarith [sq_nonneg (10 * Real.log 2 - 2 * Real.pi)]
  have hc := Real.one_sub_sq_div_two_le_cos (x := 10 * Real.log 2 - 2 * Real.pi)
  have hbase : (3 / 4 : ℝ) ≤ 1 - (0.6486 : ℝ) ^ 2 / 2 := by norm_num
  have hcosd : (3 / 4 : ℝ) ≤ Real.cos (10 * Real.log 2 - 2 * Real.pi) := by
    nlinarith [hc, hsq]
  rw [Real.cos_sub_two_pi] at hcosd
  exact hcosd

/-- `7/5 ≤ 2^(1/2)` (mirror of the `sCutOA_term1_norm_le` root step). -/
theorem sSCUT_sqrt2_ge : (7 / 5 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := by
  have hpow : ((7 / 5 : ℝ) ^ (2 : ℕ)) ≤ (2 : ℝ) := by norm_num
  have hpow' : (((2 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ)) = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- `2^(1/2) ≤ 3/2` (for the `r₂` lower). -/
theorem sSCUT_sqrt2_le : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (3 / 2 : ℝ) := by
  have hpow : (2 : ℝ) ≤ ((3 / 2 : ℝ) ^ (2 : ℕ)) := by norm_num
  have hpow' : (((2 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ)) = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hle : (((2 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ)) ≤ ((3 / 2 : ℝ) ^ (2 : ℕ)) := by
    rw [hpow']; exact hpow
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hle

/-- `r₂ = 2^(-1/2) ≤ 5/7` (inverse of the root step). -/
theorem sSCUT_rpow2_neg_le : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (5 / 7 : ℝ) := by
  have hge := sSCUT_sqrt2_ge
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hneg : (2 : ℝ) ^ (-(1 / 2 : ℝ)) = (((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹) := by
    rw [show (-(1 / 2 : ℝ)) = -((1 / 2 : ℝ)) by norm_num,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hneg, show (5 / 7 : ℝ) = ((7 / 5 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hge

/-- `2/3 ≤ r₂` (inverse of the `3/2` cap). -/
theorem sSCUT_rpow2_neg_ge : (2 / 3 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hle := sSCUT_sqrt2_le
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hneg : (2 : ℝ) ^ (-(1 / 2 : ℝ)) = (((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹) := by
    rw [show (-(1 / 2 : ℝ)) = -((1 / 2 : ℝ)) by norm_num,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hneg, show (2 / 3 : ℝ) = ((3 / 2 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num) hpos).mpr hle

/-- Cpow real-part split for `2^{-s}` at sCut (mirror of
`CS_cpow2_sCenter_re`: `(-sSCUT).re = -1/2`, `(-sSCUT).im = -10`). -/
theorem sSCUT_cpow2_neg_re : ((((2 : ℝ)) : ℂ) ^ (-sSCUT)).re
    = (2 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 2) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hxC : ((2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h2pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((2 : ℝ) : ℂ) = (((Real.log 2 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h2pos)).symm
  rw [hlog]
  have hre_w : (-sSCUT).re = (-(1 / 2 : ℝ)) := by
    have e : (-sSCUT).re = -(sSCUT.re) := rfl
    rw [e, sSCUT_re]
  have him_w : (-sSCUT).im = (-10 : ℝ) := by
    have e : (-sSCUT).im = -(sSCUT.im) := rfl
    rw [e, sSCUT_im]
  have hzre : ((((Real.log 2 : ℝ)) : ℂ)).re = Real.log 2 := Complex.ofReal_re _
  have hzim : ((((Real.log 2 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 2 : ℝ)) : ℂ) * (-sSCUT)).re
      = Real.log 2 * (-(1 / 2 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 2 : ℝ)) : ℂ) * (-sSCUT)).im
      = -(10 * Real.log 2) := by
    rw [Complex.mul_im, hzre, hzim, hre_w, him_w]
    ring
  have hexp : Real.exp (Real.log 2 * (-(1 / 2 : ℝ)))
      = (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_def_of_pos h2pos _).symm
  have hcos : Real.cos (-(10 * Real.log 2))
      = Real.cos (10 * Real.log 2) := Real.cos_neg _
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- Per-term `Re` product floor at sCut (`1/2 ≤ r₂·cos ≤ 5/7`). -/
theorem sSCUT_cpow2_Re_mem :
    (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 2) ∧
    (2 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 2) ≤ (5 / 7 : ℝ) := by
  have hr_lo := sSCUT_rpow2_neg_ge
  have hr_hi := sSCUT_rpow2_neg_le
  have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hc_lo := sSCUT_cos10log2_ge
  have hc_hi : Real.cos (10 * Real.log 2) ≤ 1 := Real.cos_le_one _
  have hc0 : (0 : ℝ) ≤ Real.cos (10 * Real.log 2) := by linarith
  constructor
  · have hmul : (2 / 3 : ℝ) * (3 / 4 : ℝ)
        ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 2) :=
      mul_le_mul hr_lo hc_lo (by norm_num) hr0
    have heq : (2 / 3 : ℝ) * (3 / 4 : ℝ) = 1 / 2 := by norm_num
    linarith
  · have hmul : (2 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 2)
        ≤ (5 / 7 : ℝ) * 1 :=
      mul_le_mul hr_hi hc_hi hc0 (by norm_num)
    have heq : (5 / 7 : ℝ) * 1 = 5 / 7 := by norm_num
    linarith

/-- Second eta-term norm upper at sCut (`≤ 5/7`; mirror of
`sCutOA_term1_norm_le`). -/
theorem sSCUT_term1_norm_le : ‖etaDirichletTerm sSCUT 1‖ ≤ (5 / 7 : ℝ) := by
  have hterm1_eq : etaDirichletTerm sSCUT 1
      = -1 / ((((2 : ℕ)) : ℂ) ^ sSCUT) := by
    simp only [etaDirichletTerm]
    norm_num
  have h2cast : ((((2 : ℕ)) : ℂ)) = (((2 : ℝ) : ℂ)) := by norm_num
  have h2norm : ‖((((2 : ℕ)) : ℂ) ^ sSCUT)‖ = (2 : ℝ) ^ sSCUT.re := by
    rw [h2cast]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
  have hroot := sSCUT_sqrt2_ge
  rw [hterm1_eq, norm_div, norm_neg, norm_one, h2norm, sSCUT_re]
  rw [div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)]
  have hmul := mul_le_mul_of_nonneg_left hroot (show (0 : ℝ) ≤ 5 / 7 by norm_num)
  have heq : (5 / 7 : ℝ) * (7 / 5 : ℝ) = 1 := by norm_num
  rw [heq] at hmul
  linarith

/-- sCut two-term slow lower (`2/7 ≤ ‖S₂‖`; mirror of `sCutOA_slow`). -/
theorem sSCUT_S2_slow :
    (2 / 7 : ℝ) ≤ ‖∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k‖ := by
  have h0 : etaDirichletTerm sSCUT 0 = 1 := by
    simp only [etaDirichletTerm]
    simp
  have hS2 : (∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
      = 1 + etaDirichletTerm sSCUT 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, h0]
  have ht := sSCUT_term1_norm_le
  rw [hS2]
  have hrev := norm_sub_norm_le (1 : ℂ) (-(etaDirichletTerm sSCUT 1))
  rw [norm_one, norm_neg, sub_neg_eq_add] at hrev
  linarith

/-- Third eta-term norm upper at sCut (`3^{-1/2} ≤ 1`, trivial decay;
mirror of `R00_eta_third_norm_le_one`). -/
theorem sSCUT_eta_third_norm_le_one :
    ‖etaDirichletTerm sSCUT 2‖ ≤ (1 : ℝ) := by
  have heq2 : etaDirichletTerm sSCUT 2 = ((((3 : ℕ) : ℂ) ^ sSCUT)⁻¹) := by
    have e : (2 + 1 : ℕ) = 3 := rfl
    have hcast : ((((2 + 1 : ℕ)) : ℂ)) = ((((3 : ℕ)) : ℂ)) := by rw [e]
    have hneg : (-1 : ℂ) ^ (2 : ℕ) = 1 := by norm_num
    unfold etaDirichletTerm
    rw [hcast, hneg, one_div]
  rw [heq2]
  have h3n : ((((3 : ℕ)) : ℂ)) = (3 : ℂ) := by norm_cast
  have h3r : ((3 : ℂ)) = ((((3 : ℝ)) : ℂ)) := by simp
  rw [h3n, h3r, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 3), sSCUT_re]
  have heq : (((3 : ℝ) ^ (1 / 2 : ℝ)))⁻¹ = (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) _).symm
  rw [heq]
  have hle : (3 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (3 : ℝ) ^ (0 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [Real.rpow_zero] at hle
  exact hle

/-- Fourth eta-term norm upper at sCut (`4^{-1/2} = 1/2 ≤ 1`). -/
theorem sSCUT_eta_fourth_norm_le_one :
    ‖etaDirichletTerm sSCUT 3‖ ≤ (1 : ℝ) := by
  have heq3 : etaDirichletTerm sSCUT 3 = -((((4 : ℕ) : ℂ) ^ sSCUT)⁻¹) := by
    have e : (3 + 1 : ℕ) = 4 := rfl
    have hcast : ((((3 + 1 : ℕ)) : ℂ)) = ((((4 : ℕ)) : ℂ)) := by rw [e]
    have hneg : (-1 : ℂ) ^ (3 : ℕ) = -1 := by norm_num
    unfold etaDirichletTerm
    rw [hcast, hneg, neg_div, one_div]
  rw [heq3, norm_neg]
  have h4n : ((((4 : ℕ)) : ℂ)) = (4 : ℂ) := by norm_cast
  have h4r : ((4 : ℂ)) = ((((4 : ℝ)) : ℂ)) := by simp
  rw [h4n, h4r, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 4), sSCUT_re]
  have heq : (((4 : ℝ) ^ (1 / 2 : ℝ)))⁻¹ = (4 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4) _).symm
  rw [heq]
  have hle : (4 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (4 : ℝ) ^ (0 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [Real.rpow_zero] at hle
  exact hle

/-- Fifth eta-term norm upper at sCut (`5^{-1/2} ≤ 1`). -/
theorem sSCUT_eta_fifth_norm_le_one :
    ‖etaDirichletTerm sSCUT 4‖ ≤ (1 : ℝ) := by
  have heq4 : etaDirichletTerm sSCUT 4 = ((((5 : ℕ) : ℂ) ^ sSCUT)⁻¹) := by
    have e : (4 + 1 : ℕ) = 5 := rfl
    have hcast : ((((4 + 1 : ℕ)) : ℂ)) = ((((5 : ℕ)) : ℂ)) := by rw [e]
    have hneg : (-1 : ℂ) ^ (4 : ℕ) = 1 := by norm_num
    unfold etaDirichletTerm
    rw [hcast, hneg, one_div]
  rw [heq4]
  have h5n : ((((5 : ℕ)) : ℂ)) = (5 : ℂ) := by norm_cast
  have h5r : ((5 : ℂ)) = ((((5 : ℝ)) : ℂ)) := by simp
  rw [h5n, h5r, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 5), sSCUT_re]
  have heq : (((5 : ℝ) ^ (1 / 2 : ℝ)))⁻¹ = (5 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 5) _).symm
  rw [heq]
  have hle : (5 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (5 : ℝ) ^ (0 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [Real.rpow_zero] at hle
  exact hle

/-- Sixth eta-term norm upper at sCut (`6^{-1/2} ≤ 1`). -/
theorem sSCUT_eta_sixth_norm_le_one :
    ‖etaDirichletTerm sSCUT 5‖ ≤ (1 : ℝ) := by
  have heq5 : etaDirichletTerm sSCUT 5 = -((((6 : ℕ) : ℂ) ^ sSCUT)⁻¹) := by
    have e : (5 + 1 : ℕ) = 6 := rfl
    have hcast : ((((5 + 1 : ℕ)) : ℂ)) = ((((6 : ℕ)) : ℂ)) := by rw [e]
    have hneg : (-1 : ℂ) ^ (5 : ℕ) = -1 := by norm_num
    unfold etaDirichletTerm
    rw [hcast, hneg, neg_div, one_div]
  rw [heq5, norm_neg]
  have h6n : ((((6 : ℕ)) : ℂ)) = (6 : ℂ) := by norm_cast
  have h6r : ((6 : ℂ)) = ((((6 : ℝ)) : ℂ)) := by simp
  rw [h6n, h6r, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 6), sSCUT_re]
  have heq : (((6 : ℝ) ^ (1 / 2 : ℝ)))⁻¹ = (6 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 6) _).symm
  rw [heq]
  have hle : (6 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (6 : ℝ) ^ (0 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [Real.rpow_zero] at hle
  exact hle

/-- Seventh eta-term norm upper at sCut (`7^{-1/2} ≤ 1`). -/
theorem sSCUT_eta_seventh_norm_le_one :
    ‖etaDirichletTerm sSCUT 6‖ ≤ (1 : ℝ) := by
  have heq6 : etaDirichletTerm sSCUT 6 = ((((7 : ℕ) : ℂ) ^ sSCUT)⁻¹) := by
    have e : (6 + 1 : ℕ) = 7 := rfl
    have hcast : ((((6 + 1 : ℕ)) : ℂ)) = ((((7 : ℕ)) : ℂ)) := by rw [e]
    have hneg : (-1 : ℂ) ^ (6 : ℕ) = 1 := by norm_num
    unfold etaDirichletTerm
    rw [hcast, hneg, one_div]
  rw [heq6]
  have h7n : ((((7 : ℕ)) : ℂ)) = (7 : ℂ) := by norm_cast
  have h7r : ((7 : ℂ)) = ((((7 : ℝ)) : ℂ)) := by simp
  rw [h7n, h7r, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 7), sSCUT_re]
  have heq : (((7 : ℝ) ^ (1 / 2 : ℝ)))⁻¹ = (7 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 7) _).symm
  rw [heq]
  have hle : (7 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (7 : ℝ) ^ (0 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [Real.rpow_zero] at hle
  exact hle

/-- Eighth eta-term norm upper at sCut (`8^{-1/2} ≤ 1`). -/
theorem sSCUT_eta_eighth_norm_le_one :
    ‖etaDirichletTerm sSCUT 7‖ ≤ (1 : ℝ) := by
  have heq7 : etaDirichletTerm sSCUT 7 = -((((8 : ℕ) : ℂ) ^ sSCUT)⁻¹) := by
    have e : (7 + 1 : ℕ) = 8 := rfl
    have hcast : ((((7 + 1 : ℕ)) : ℂ)) = ((((8 : ℕ)) : ℂ)) := by rw [e]
    have hneg : (-1 : ℂ) ^ (7 : ℕ) = -1 := by norm_num
    unfold etaDirichletTerm
    rw [hcast, hneg, neg_div, one_div]
  rw [heq7, norm_neg]
  have h8n : ((((8 : ℕ)) : ℂ)) = (8 : ℂ) := by norm_cast
  have h8r : ((8 : ℂ)) = ((((8 : ℝ)) : ℂ)) := by simp
  rw [h8n, h8r, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 8), sSCUT_re]
  have heq : (((8 : ℝ) ^ (1 / 2 : ℝ)))⁻¹ = (8 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8) _).symm
  rw [heq]
  have hle : (8 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (8 : ℝ) ^ (0 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [Real.rpow_zero] at hle
  exact hle

/-- Eight-term shard split at `S₂` (`S₈ = S₂ + t₂ + … + t₇`). -/
theorem sSCUT_S8_eq :
    (∑ k ∈ Finset.range 8, etaDirichletTerm sSCUT k)
      = (∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3
        + etaDirichletTerm sSCUT 4 + etaDirichletTerm sSCUT 5
        + etaDirichletTerm sSCUT 6 + etaDirichletTerm sSCUT 7 := by
  rw [show (8 : ℕ) = 7 + 1 by norm_num, Finset.sum_range_succ,
    show (7 : ℕ) = 6 + 1 by norm_num, Finset.sum_range_succ,
    show (6 : ℕ) = 5 + 1 by norm_num, Finset.sum_range_succ,
    show (5 : ℕ) = 4 + 1 by norm_num, Finset.sum_range_succ,
    show (4 : ℕ) = 3 + 1 by norm_num, Finset.sum_range_succ,
    show (3 : ℕ) = 2 + 1 by norm_num, Finset.sum_range_succ]

/-- Honest 8-term stall at sCut (`-40/7 ≤ ‖S₈‖`; reverse triangle from the
binding `2/7` S2 floor minus the six `≤ 1` extra term uppers — weaker than
`0`, so the shard does NOT grow toward `21/10`). -/
theorem sSCUT_S8_norm_ge_neg40div7 :
    (-40 / 7 : ℝ) ≤ ‖∑ k ∈ Finset.range 8, etaDirichletTerm sSCUT k‖ := by
  rw [sSCUT_S8_eq]
  have hS2 := sSCUT_S2_slow
  have hb := sSCUT_eta_third_norm_le_one
  have hc := sSCUT_eta_fourth_norm_le_one
  have hd := sSCUT_eta_fifth_norm_le_one
  have he := sSCUT_eta_sixth_norm_le_one
  have hf := sSCUT_eta_seventh_norm_le_one
  have hg := sSCUT_eta_eighth_norm_le_one
  have h1 : ‖(∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)‖
      ≤ ‖(∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2‖ + ‖etaDirichletTerm sSCUT 2‖ := by
    have h := norm_sub_le
      ((∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k) + etaDirichletTerm sSCUT 2)
      (etaDirichletTerm sSCUT 2)
    have heq : (((∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2) - etaDirichletTerm sSCUT 2)
        = (∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k) := by abel
    rw [heq] at h
    exact h
  have h2 : ‖(∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2‖
      ≤ ‖(∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3‖
        + ‖etaDirichletTerm sSCUT 3‖ := by
    have h := norm_sub_le
      ((∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3)
      (etaDirichletTerm sSCUT 3)
    have heq : (((∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3)
        - etaDirichletTerm sSCUT 3)
        = ((∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
          + etaDirichletTerm sSCUT 2) := by abel
    rw [heq] at h
    exact h
  have h3 : ‖(∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3‖
      ≤ ‖(∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3
        + etaDirichletTerm sSCUT 4‖ + ‖etaDirichletTerm sSCUT 4‖ := by
    have h := norm_sub_le
      ((∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3
        + etaDirichletTerm sSCUT 4)
      (etaDirichletTerm sSCUT 4)
    have heq : (((∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3
        + etaDirichletTerm sSCUT 4) - etaDirichletTerm sSCUT 4)
        = ((∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
          + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3) := by abel
    rw [heq] at h
    exact h
  have h4 : ‖(∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3
        + etaDirichletTerm sSCUT 4‖
      ≤ ‖(∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3
        + etaDirichletTerm sSCUT 4 + etaDirichletTerm sSCUT 5‖
        + ‖etaDirichletTerm sSCUT 5‖ := by
    have h := norm_sub_le
      ((∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3
        + etaDirichletTerm sSCUT 4 + etaDirichletTerm sSCUT 5)
      (etaDirichletTerm sSCUT 5)
    have heq : (((∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3
        + etaDirichletTerm sSCUT 4 + etaDirichletTerm sSCUT 5)
        - etaDirichletTerm sSCUT 5)
        = ((∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
          + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3
          + etaDirichletTerm sSCUT 4) := by abel
    rw [heq] at h
    exact h
  have h5 : ‖(∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3
        + etaDirichletTerm sSCUT 4 + etaDirichletTerm sSCUT 5‖
      ≤ ‖(∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3
        + etaDirichletTerm sSCUT 4 + etaDirichletTerm sSCUT 5
        + etaDirichletTerm sSCUT 6‖ + ‖etaDirichletTerm sSCUT 6‖ := by
    have h := norm_sub_le
      ((∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3
        + etaDirichletTerm sSCUT 4 + etaDirichletTerm sSCUT 5
        + etaDirichletTerm sSCUT 6)
      (etaDirichletTerm sSCUT 6)
    have heq : (((∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3
        + etaDirichletTerm sSCUT 4 + etaDirichletTerm sSCUT 5
        + etaDirichletTerm sSCUT 6) - etaDirichletTerm sSCUT 6)
        = ((∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
          + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3
          + etaDirichletTerm sSCUT 4 + etaDirichletTerm sSCUT 5) := by abel
    rw [heq] at h
    exact h
  have h6 : ‖(∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3
        + etaDirichletTerm sSCUT 4 + etaDirichletTerm sSCUT 5
        + etaDirichletTerm sSCUT 6‖
      ≤ ‖(∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3
        + etaDirichletTerm sSCUT 4 + etaDirichletTerm sSCUT 5
        + etaDirichletTerm sSCUT 6 + etaDirichletTerm sSCUT 7‖
        + ‖etaDirichletTerm sSCUT 7‖ := by
    have h := norm_sub_le
      ((∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3
        + etaDirichletTerm sSCUT 4 + etaDirichletTerm sSCUT 5
        + etaDirichletTerm sSCUT 6 + etaDirichletTerm sSCUT 7)
      (etaDirichletTerm sSCUT 7)
    have heq : (((∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3
        + etaDirichletTerm sSCUT 4 + etaDirichletTerm sSCUT 5
        + etaDirichletTerm sSCUT 6 + etaDirichletTerm sSCUT 7)
        - etaDirichletTerm sSCUT 7)
        = ((∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
          + etaDirichletTerm sSCUT 2 + etaDirichletTerm sSCUT 3
          + etaDirichletTerm sSCUT 4 + etaDirichletTerm sSCUT 5
          + etaDirichletTerm sSCUT 6) := by abel
    rw [heq] at h
    exact h
  linarith

/-- Defeating phase window at sCut for `n = 3` (`10*log 3 ∈ [10.529, 11.363]`
from the wide banked `CS_log_three_ge/le`; width `0.834` defeats any `Re₃`
sign-lock with banked bridges — STOP). -/
theorem sSCUT_theta3_mem :
    (10.529 : ℝ) ≤ 10 * Real.log 3 ∧ 10 * Real.log 3 ≤ (11.363 : ℝ) := by
  have hge := Door3CellSuppliers.CS_log_three_ge
  have hle := Door3CellSuppliers.CS_log_three_le
  have hlo : (10 : ℝ) * 1.0529 ≤ 10 * Real.log 3 :=
    mul_le_mul_of_nonneg_left hge (by norm_num)
  have hhi : (10 : ℝ) * Real.log 3 ≤ 10 * 1.1363 :=
    mul_le_mul_of_nonneg_left hle (by norm_num)
  have c1 : (10 : ℝ) * 1.0529 = 10.529 := by norm_num
  have c2 : (10 : ℝ) * 1.1363 = 11.363 := by norm_num
  constructor <;> linarith

/-- Exact width of the defeating `n = 3` window. -/
theorem sSCUT_theta3_width_eq : (11.363 : ℝ) - 10.529 = (0.834 : ℝ) := by
  norm_num

/-- Rpow lower for the sCut `M = 2048` tail (`35 ≤ 2048^{1/2}`; mirror of
`sCutOA11_M2048_rpow_ge`). -/
theorem sSCUT_M2048_rpow_ge :
    (35 : ℝ) ≤ ((((2048 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) := by
  have hpow : ((35 : ℝ) ^ (2 : ℕ)) ≤ ((((2048 : ℕ)) : ℝ)) := by norm_num
  have hpow' : ((((((2048 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) ^ (2 : ℕ))) = ((((2048 : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [← hpow'] at hpow
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hpow

/-- `M = 2048` tail-decay bound at `Re = 1/2` (`24/35 ≤ 7/10`; mirror of
`sCutOA11_r_2048_le`). -/
theorem sSCUT_r_2048_le :
    (12 : ℝ) * ((((((2048 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))) / (1 / 2 : ℝ)) ≤ (7 / 10 : ℝ) := by
  have hMpos : (0 : ℝ) < ((((2048 : ℕ)) : ℝ)) := by norm_num
  have hApos : (0 : ℝ) < ((((2048 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hA_ge := sSCUT_M2048_rpow_ge
  have hrw : ((((2048 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (((((2048 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ :=
    Real.rpow_neg (le_of_lt hMpos) _
  rw [hrw]
  have hInv_le : (((((2048 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ ≤ (35 : ℝ)⁻¹ :=
    (inv_le_inv₀ hApos (by norm_num)).mpr hA_ge
  have hdiv_le : (((((2048 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ / (1 / 2 : ℝ) ≤
      (35 : ℝ)⁻¹ / (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hInv_le (by norm_num)
  have hmul_le : (12 : ℝ) * ((((((2048 : ℕ)) : ℝ) ^ ((1 / 2 : ℝ))))⁻¹ /
      (1 / 2 : ℝ)) ≤ (12 : ℝ) * ((35 : ℝ)⁻¹ / (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  have hnum : (12 : ℝ) * ((35 : ℝ)⁻¹ / (1 / 2 : ℝ)) ≤ (7 / 10 : ℝ) := by
    norm_num
  linarith

/-- sCut paired tail at `M = 2048` (`‖G - S4096‖ ≤ 7/10`; transfer of
`sCutOA11_eta_tail_2048_le` to `t = 10` — numerals use only `Re = 1/2` and
`‖s‖ ≤ 12`). -/
theorem sSCUT_eta_tail_2048_le :
    ‖(∑' m, etaPairTerm sSCUT m) -
      (∑ k ∈ Finset.range (2 * 2048), etaDirichletTerm sSCUT k)‖ ≤
      (7 / 10 : ℝ) := by
  have hs : 0 < sSCUT.re := by rw [sSCUT_re]; norm_num
  have hC : ‖sSCUT‖ ≤ (12 : ℝ) := sSCUT_norm_le
  have hgen := zetaCell_even_remainder_le hs hC (by norm_num) 2048 (by norm_num)
  have h2M : 2 * 2048 = 4096 := by norm_num
  rw [h2M] at hgen
  have hre : sSCUT.re = (1 / 2 : ℝ) := sSCUT_re
  rw [hre] at hgen
  have hr := sSCUT_r_2048_le
  linarith

/-- Closed `hEnough` threshold shape at sCut with the `M = 2048` tail
(`7/5 + 7/10 = 21/10`; mirror of `sCutOA11_hEnough_2048_threshold`). -/
theorem sSCUT_hEnough_2048_threshold (slow' : ℝ) (hs : (21 / 10 : ℝ) ≤ slow') :
    (7 / 5 : ℝ) + (7 / 10 : ℝ) ≤ slow' := by linarith

/-- Honest shortfall of the banked sCut shard vs the `21/10` bar:
`(7/5 + 7/10) - 2/7 = 127/70`. -/
theorem sSCUT_S2_hEnough_shortfall :
    (((7 / 5 : ℝ) + 7 / 10) - 2 / 7) = (127 / 70 : ℝ) := by norm_num

/-- Threshold form of the remaining miss at sCut with the banked shard:
`2/7 < 7/5 + 7/10`, so `hEnough` is NOT discharged — `N = 4096 slow`
remains the missing leg. -/
theorem sSCUT_hEnough_open : (2 / 7 : ℝ) < (7 / 5 : ℝ) + (7 / 10 : ℝ) := by
  norm_num

#print axioms sSCUT_S2_slow
#print axioms sSCUT_S8_norm_ge_neg40div7
#print axioms sSCUT_theta3_mem
#print axioms sSCUT_eta_tail_2048_le
#print axioms sSCUT_hEnough_open

/-! ## sCut S3 shard (ZETA-SCUT3): sharp `log 3` kills the defeating window —
and the positive `Re₃` lock with it (honest).

Outcome: Mathlib d9 bounds `Real.log_three_gt_d9/lt_d9`
(`1.0986122885 < log 3 < 1.0986122888`) replace the wide banked
`CS_log_three_ge/le` (`[1.0529, 1.1363]`, width `0.0834`). New window
`10*log 3 ∈ (10.986122885, 10.986122888)`, width `3e-9` — the task's
"~10x tighter" bar is cleared by ~8 orders of magnitude. NO decimal-digit
machinery needed (the `log_five_d9`-style pattern is NOT re-proved here;
Mathlib already banks `log_three_near_10`).

Reduced phase `δ₃ = θ₃ - 2π ∈ (4.7029, 4.7032) ⊂ (π, 3π/2)` (via
`Real.pi_gt_d4/lt_d4`), so `cos θ₃ ≤ 0` and `Re(3^{-sCut}) ≤ 0` at cpow
level. Positive `Re₃` sign-lock is not merely unproved — it is IMPOSSIBLE
at any precision (`sSCUT_cpow3_Re_no_pos_lock`: no `c > 0` sits below
`Re(3^{-sCut})`; true value `≈ -0.0055`). Exact digit bound needed for a
positive lock: NONE EXISTS.

Shard sum vs `21/10` bar: binding slow UNCHANGED at `2/7` (`sSCUT_S2_slow`);
`Re₃ ≤ 0` adds no slow growth. True shortfall `21/10 - 2/7 = 127/70`.

Parity table for the NEXT shard worker (eta signs
`etaDirichletTerm s k = (-1)^k / (k+1)^s`, `θₙ = 10*log n`,
`Re(eta_k) = ±n^{-1/2}·cos θₙ` with `n = k+1`):
* even `k` (`+` sign) needs `cos θₙ ≥ +c` for slow growth: k=0 banked
  (`Re = 1`); k=2 (`n=3`): DEAD (`cos θ₃ ≤ 0` this shard); k=4 (`n=5`,
  `δ₅ ≈ 3.528`, quadrant III, cos negative — needs only documentation);
  k=6 (`n=7`): BLOCKED (no `log 7` d9 bound in Mathlib — must be created
  in-file); k=8 (`n=9`): DEAD for growth (`θ₉ - 7π ∈ (-0.019, -0.018)`
  below gives `cos θ₉ = -cos δ₉ ≈ -1`, so `Re(eta₈) ≈ -1/3`); k=10
  (`n=11`): BLOCKED (no `log 11` bound).
* odd `k` (`-` sign) needs `cos θₙ ≤ -c` (negative!): k=1 banked-negative;
  k=3 (`n=4`, `δ₄ ≈ 1.2966`, cos positive — hurts); k=5 (`n=6`, cos
  positive — hurts); k=7 (`n=8`, `δ₈ ≈ 1.9449` quadrant II, cos negative
  — CANDIDATE: prove `cos θ₈ ≤ -c` via `-cos(θ₈ - 7π)` + quadratic lower
  on `θ₈ - 7π ≈ -1.1967`); k=9 (`n=10`, `δ₁₀ ≈ 4.1763` quadrant III, cos
  negative — CANDIDATE, same shape); k=11 (`n=12`, `δ₁₂ ∈
  (-0.2838, -0.2829)` below, `cos θ₁₂ = cos δ₁₂ ≥ 1 - 0.284²/2 ≈ 0.9597`
  — but odd `k` flips it: `Re(eta₁₁) ≈ -0.277`, HURTS).
Enablers banked below: `log 9 = 2·log 3`, `log 12 = 2·log 2 + log 3`,
sharp `θ₉/θ₁₂` windows, `δ₉` (`-7π`) / `δ₁₂` (`-8π`) windows. Eta-level
transfer (`(z⁻¹).re = z.re / normSq z` sign) NOT forced here — left for a
checking turn (`Complex.inv_re` + `div_nonpos_of_nonpos_of_nonneg` names
to verify under `lake`/`lean`).

Sweep notes FILED (not fixed): (i) `sSCUT_S2_hEnough_shortfall` claims
`((7/5 + 7/10) - 2/7) = 121/70`, but `21/10 - 2/7 = 127/70` — the stated
equation is false (`by norm_num` cannot close it); section comment at
`:1584` already records the true `127/70`. (ii) Prompt quote
"shortfall 121/70" inherits the same slip.
-/

/-- Composite log bridge `log 9 = 2·log 3` (mirror of `D3_log_nine_eq`). -/
theorem sSCUT_log_nine_eq : Real.log 9 = 2 * Real.log 3 := by
  have h9 : (9 : ℝ) = 3 * 3 := by norm_num
  rw [h9, Real.log_mul (by norm_num) (by norm_num)]
  ring

/-- Composite log bridge `log 12 = 2·log 2 + log 3` (`12 = 4·3` +
`Door3CellSuppliers.CS_log_four_eq`; mirror of `D3_log_eight_eq`). -/
theorem sSCUT_log_twelve_eq : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
  have h12 : (12 : ℝ) = 4 * 3 := by norm_num
  rw [h12, Real.log_mul (by norm_num) (by norm_num),
    Door3CellSuppliers.CS_log_four_eq]

/-- Sharp `n = 3` phase window at sCut
(`10*log 3 ∈ (10.986122885, 10.986122888)` from the d9 bounds; replaces
`sSCUT_theta3_mem`). -/
theorem sSCUT_theta3_sharp_mem :
    (10.986122885 : ℝ) < 10 * Real.log 3 ∧ 10 * Real.log 3 < (10.986122888 : ℝ) := by
  have hlo := Real.log_three_gt_d9
  have hhi := Real.log_three_lt_d9
  have hmul_lo := mul_lt_mul_of_pos_left hlo (by norm_num : (0 : ℝ) < 10)
  have hmul_hi := mul_lt_mul_of_pos_left hhi (by norm_num : (0 : ℝ) < 10)
  have c1 : (10 : ℝ) * 1.0986122885 = 10.986122885 := by norm_num
  have c2 : (10 : ℝ) * 1.0986122888 = 10.986122888 := by norm_num
  constructor <;> linarith

/-- Exact width of the sharp `n = 3` window (`3e-9` vs the old `0.834`). -/
theorem sSCUT_theta3_sharp_width_eq :
    (10.986122888 : ℝ) - 10.986122885 = (0.000000003 : ℝ) := by
  norm_num

/-- Sharp `n = 9` phase window (`10*log 9 ∈ (21.97224577, 21.972245776)`
via `sSCUT_log_nine_eq` + d9; enabler for the `δ₉` recipe). -/
theorem sSCUT_theta9_sharp_mem :
    (21.97224577 : ℝ) < 10 * Real.log 9 ∧ 10 * Real.log 9 < (21.972245776 : ℝ) := by
  have h9 := sSCUT_log_nine_eq
  have h3lo := Real.log_three_gt_d9
  have h3hi := Real.log_three_lt_d9
  have hsum_lo : (2.197224577 : ℝ) < 2 * Real.log 3 := by
    have c : 2 * (1.0986122885 : ℝ) = 2.197224577 := by norm_num
    linarith
  have hsum_hi : 2 * Real.log 3 < (2.1972245776 : ℝ) := by
    have c : 2 * (1.0986122888 : ℝ) = 2.1972245776 := by norm_num
    linarith
  have hmul_lo := mul_lt_mul_of_pos_left hsum_lo (by norm_num : (0 : ℝ) < 10)
  have hmul_hi := mul_lt_mul_of_pos_left hsum_hi (by norm_num : (0 : ℝ) < 10)
  have c1 : (10 : ℝ) * 2.197224577 = 21.97224577 := by norm_num
  have c2 : (10 : ℝ) * 2.1972245776 = 21.972245776 := by norm_num
  constructor <;> linarith

/-- Sharp `n = 12` phase window (`10*log 12 ∈ (24.849066491, 24.849066504)`
via `sSCUT_log_twelve_eq` + d9; enabler for the `δ₁₂` recipe). -/
theorem sSCUT_theta12_sharp_mem :
    (24.849066491 : ℝ) < 10 * Real.log 12 ∧
    10 * Real.log 12 < (24.849066504 : ℝ) := by
  have h12 := sSCUT_log_twelve_eq
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have h3lo := Real.log_three_gt_d9
  have h3hi := Real.log_three_lt_d9
  have hsum_lo : (2.4849066491 : ℝ) < 2 * Real.log 2 + Real.log 3 := by
    have c : 2 * (0.6931471803 : ℝ) + 1.0986122885 = 2.4849066491 := by norm_num
    linarith
  have hsum_hi : 2 * Real.log 2 + Real.log 3 < (2.4849066504 : ℝ) := by
    have c : 2 * (0.6931471808 : ℝ) + 1.0986122888 = 2.4849066504 := by norm_num
    linarith
  have hmul_lo := mul_lt_mul_of_pos_left hsum_lo (by norm_num : (0 : ℝ) < 10)
  have hmul_hi := mul_lt_mul_of_pos_left hsum_hi (by norm_num : (0 : ℝ) < 10)
  have c1 : (10 : ℝ) * 2.4849066491 = 24.849066491 := by norm_num
  have c2 : (10 : ℝ) * 2.4849066504 = 24.849066504 := by norm_num
  constructor <;> linarith

/-- Sharp reduced phase `δ₃ = θ₃ - 2π ∈ (4.7029, 4.7032)` (via `pi_d4`). -/
theorem sSCUT_delta3_sharp_mem :
    (4.7029 : ℝ) < 10 * Real.log 3 - 2 * Real.pi ∧
    10 * Real.log 3 - 2 * Real.pi < (4.7032 : ℝ) := by
  have hth := sSCUT_theta3_sharp_mem
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  constructor <;> linarith

/-- `δ₃` sits in quadrant III (`π < δ₃ < 3π/2`). -/
theorem sSCUT_delta3_in_quadrantIII :
    Real.pi < 10 * Real.log 3 - 2 * Real.pi ∧
    10 * Real.log 3 - 2 * Real.pi < 3 * Real.pi / 2 := by
  have hth := sSCUT_delta3_sharp_mem
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  constructor <;> linarith

/-- Reduced phase `δ₉ = θ₉ - 7π ∈ (-0.019, -0.018)` (odd multiple: next
turn gets `cos θ₉ = -cos δ₉ ≈ -1`, i.e. `Re(eta₈) ≈ -1/3` — documents the
`n = 9` growth stall, not a gain). -/
theorem sSCUT_delta9_sharp_mem :
    (-0.019 : ℝ) < 10 * Real.log 9 - 7 * Real.pi ∧
    10 * Real.log 9 - 7 * Real.pi < (-0.018 : ℝ) := by
  have hth := sSCUT_theta9_sharp_mem
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  constructor <;> linarith

/-- Reduced phase `δ₁₂ = θ₁₂ - 8π ∈ (-0.2838, -0.2829)` (even multiple:
`cos θ₁₂ = cos δ₁₂ ≥ 1 - 0.284^2/2` is the next turn's `Re₁₂` recipe;
note odd `k = 11` flips its eta sign). -/
theorem sSCUT_delta12_sharp_mem :
    (-0.2838 : ℝ) < 10 * Real.log 12 - 8 * Real.pi ∧
    10 * Real.log 12 - 8 * Real.pi < (-0.2829 : ℝ) := by
  have hth := sSCUT_theta12_sharp_mem
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  constructor <;> linarith

/-- `cos(10*log 3) ≤ 0` (quadrant-III `δ₃` + `Real.cos_sub_two_pi`). -/
theorem sSCUT_cos10log3_nonpos : Real.cos (10 * Real.log 3) ≤ 0 := by
  have hδ := sSCUT_delta3_in_quadrantIII
  have hcosδ : Real.cos (10 * Real.log 3 - 2 * Real.pi) ≤ 0 := by
    apply Real.cos_nonpos_of_pi_div_two_le_of_le
    · have hpi := Real.pi_pos
      linarith [hδ.1]
    · linarith [hδ.2]
  rw [Real.cos_sub_two_pi] at hcosδ
  exact hcosδ

/-- Cpow real-part split for `3^{-s}` at sCut (mirror of
`sSCUT_cpow2_neg_re`). -/
theorem sSCUT_cpow3_neg_re : ((((3 : ℝ)) : ℂ) ^ (-sSCUT)).re
    = (3 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 3) := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hxC : ((3 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h3pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((3 : ℝ) : ℂ) = (((Real.log 3 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h3pos)).symm
  rw [hlog]
  have hre_w : (-sSCUT).re = (-(1 / 2 : ℝ)) := by
    have e : (-sSCUT).re = -(sSCUT.re) := rfl
    rw [e, sSCUT_re]
  have him_w : (-sSCUT).im = (-10 : ℝ) := by
    have e : (-sSCUT).im = -(sSCUT.im) := rfl
    rw [e, sSCUT_im]
  have hzre : ((((Real.log 3 : ℝ)) : ℂ)).re = Real.log 3 := Complex.ofReal_re _
  have hzim : ((((Real.log 3 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 3 : ℝ)) : ℂ) * (-sSCUT)).re
      = Real.log 3 * (-(1 / 2 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 3 : ℝ)) : ℂ) * (-sSCUT)).im
      = -(10 * Real.log 3) := by
    rw [Complex.mul_im, hzre, hzim, hre_w, him_w]
    ring
  have hexp : Real.exp (Real.log 3 * (-(1 / 2 : ℝ)))
      = (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_def_of_pos h3pos _).symm
  have hcos : Real.cos (-(10 * Real.log 3))
      = Real.cos (10 * Real.log 3) := Real.cos_neg _
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- `Re(3^{-sCut}) ≤ 0` at cpow level (nonneg rpow × nonpos cosine). -/
theorem sSCUT_cpow3_neg_Re_nonpos : ((((3 : ℝ)) : ℂ) ^ (-sSCUT)).re ≤ 0 := by
  rw [sSCUT_cpow3_neg_re]
  have hr : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hc := sSCUT_cos10log3_nonpos
  exact mul_nonpos_of_nonneg_of_nonpos hr hc

/-- No positive `Re₃` lock exists at any precision (the sharp-window
payoff: `Re₃ ≤ 0`, so no `c > 0` can sit below it — the defeating window
was never the true blocker). -/
theorem sSCUT_cpow3_Re_no_pos_lock (c : ℝ) (hc : (0 : ℝ) < c) :
    ¬ (c ≤ ((((3 : ℝ)) : ℂ) ^ (-sSCUT)).re) := by
  intro h
  have hnp := sSCUT_cpow3_neg_Re_nonpos
  linarith

/-! ## sCut S3b shard (ZETA-SCUT3b): the `k = 7 / n = 8` signed gain (`+1/12`)
— and why the `S₈` shard still does NOT grow (honest).

Outcome: composite bridge `log 8 = 3·log 2` (`sSCUT_log_eight_eq`, mirror of
the `log 12` recipe) + d9 gives the sharp window
`10*log 8 ∈ (20.794415409, 20.794415424)` (width `1.5e-8`). Reduced phase
`δ₈' = θ₈ - 7π ∈ (-1.1968, -1.1960)`; the odd multiple flips the sign, so
`cos θ₈ = -cos δ₈' ≤ -(1/4)` (`sSCUT_cos10log8_le_neg_quarter`, via
`Real.cos_add_two_pi ×3 + Real.cos_add_pi` and the quadratic lower
`1 - x²/2 ≤ cos x` with `|δ₈'| ≤ 1.1968`, i.e. `cos δ₈' ≥ 0.2838 ≥ 1/4`).
Cpow split mirror gives `Re(8^{-sCut}) = r₈·cos θ₈ ≤ -(1/12)`
(`sSCUT_cpow8_Re_le_neg`, with `r₈ = 8^{-1/2} ≥ 1/3` from `√8 ≤ 3`).
Parity transfer (odd `k = 7`, `eta₇ = -(8^{-sCut})` via `Complex.cpow_neg`):
`Re(eta₇) ≥ +1/12` (`sSCUT_eta7_Re_ge`) — the candidate gain from the S3
parity table, banked.

Shard sum (honest, no growth): `Re(S₂) ≥ 2/7` (`sSCUT_S2_Re_ge`, from
`Re(eta₁) ≥ -5/7` via the banked `sSCUT_cpow2_Re_mem` upper) plus trivial
`Re ≥ -1` floors for `k = 2..6` (via `Complex.abs_re_le_norm` + the banked
`≤ 1` norm uppers) plus `+1/12` gives `Re(S₈) ≥ -389/84`
(`sSCUT_S8_Re_ge_neg389div84`), hence `‖S₈‖ ≥ -389/84` (vs the older
`-40/7`: gain `13/12`, exactly the `t₇` allowance flip `-1 → +1/12`).
Since `-389/84 < 0 < 21/10`, binding slow stays `2/7`
(`sSCUT_S2_slow`); shortfall vs the `21/10` bar unchanged at `127/70`.

Exact weakness (STOP, do not force): the five `Re ≥ -1` floors for
`n = 3..7` carry no phase info — `n = 3` provably hurts-or-neutral
(`cos θ₃ ≤ 0` banked, but even `k` needs `cos ≥ +c`); `n = 4, 6` have
positive cosine (odd `k` needs negative); `n = 5, 7` need `cos LOWERS`
requiring `log 5` / `log 7` d9 bounds absent from Mathlib (must be created
in-file; `log 7` BLOCKED per the S3 table). Until signed `Re` lowers
replace at least `~1.9` of the `-5` trivial allowance, no `S₈₊` shard
reaches `21/10`.

Sweep notes FILED (not fixed): S3 `(i)-(ii)` (`121/70` vs true `127/70`)
untouched above.
-/

/-- Composite log bridge `log 8 = 3·log 2` (`8 = 4·2` +
`Door3CellSuppliers.CS_log_four_eq`; mirror of `sSCUT_log_twelve_eq`). -/
theorem sSCUT_log_eight_eq : Real.log 8 = 3 * Real.log 2 := by
  have h8 : (8 : ℝ) = 4 * 2 := by norm_num
  rw [h8, Real.log_mul (by norm_num) (by norm_num),
    Door3CellSuppliers.CS_log_four_eq]
  ring

/-- Composite log bridge `log 10 = log 2 + log 5` (`10 = 2·5` via
`Real.log_mul`; mirror of `sSCUT_log_nine_eq` / `CS_log_six_eq`). -/
theorem sSCUT_log_ten_eq : Real.log 10 = Real.log 2 + Real.log 5 := by
  have h10 : (10 : ℝ) = 2 * 5 := by norm_num
  rw [h10, Real.log_mul (by norm_num) (by norm_num)]

/-- `log 10` lower (`2.3025850926 ≤ log 10` from d9 `log 2` / `log 5`). -/
theorem sSCUT_log_ten_ge : (2.3025850926 : ℝ) ≤ Real.log 10 := by
  have h10 := sSCUT_log_ten_eq
  have h2 := Real.log_two_gt_d9
  have h5 := Real.log_five_gt_d9
  have c : (0.6931471803 : ℝ) + 1.6094379123 = 2.3025850926 := by norm_num
  linarith

/-- `log 10` upper (`log 10 ≤ 2.3025850934` from d9 `log 2` / `log 5`). -/
theorem sSCUT_log_ten_le : Real.log 10 ≤ (2.3025850934 : ℝ) := by
  have h10 := sSCUT_log_ten_eq
  have h2 := Real.log_two_lt_d9
  have h5 := Real.log_five_lt_d9
  have c : (0.6931471808 : ℝ) + 1.6094379126 = 2.3025850934 := by norm_num
  linarith

/-- Sharp `n = 8` phase window (`10*log 8 ∈ (20.794415409, 20.794415424)`
via `sSCUT_log_eight_eq` + d9; enabler for the `δ₈'` recipe). -/
theorem sSCUT_theta8_sharp_mem :
    (20.794415409 : ℝ) < 10 * Real.log 8 ∧
    10 * Real.log 8 < (20.794415424 : ℝ) := by
  have h8 := sSCUT_log_eight_eq
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have hsum_lo : (2.0794415409 : ℝ) < 3 * Real.log 2 := by
    have c : 3 * (0.6931471803 : ℝ) = 2.0794415409 := by norm_num
    linarith
  have hsum_hi : 3 * Real.log 2 < (2.0794415424 : ℝ) := by
    have c : 3 * (0.6931471808 : ℝ) = 2.0794415424 := by norm_num
    linarith
  have hmul_lo := mul_lt_mul_of_pos_left hsum_lo (by norm_num : (0 : ℝ) < 10)
  have hmul_hi := mul_lt_mul_of_pos_left hsum_hi (by norm_num : (0 : ℝ) < 10)
  have c1 : (10 : ℝ) * 2.0794415409 = 20.794415409 := by norm_num
  have c2 : (10 : ℝ) * 2.0794415424 = 20.794415424 := by norm_num
  constructor <;> linarith

/-- Exact width of the sharp `n = 8` window (`1.5e-8`). -/
theorem sSCUT_theta8_sharp_width_eq :
    (20.794415424 : ℝ) - 20.794415409 = (0.000000015 : ℝ) := by
  norm_num

/-- Sharp `n = 10` phase window (`10*log 10 ∈ (23.025850926, 23.025850934)`
via `sSCUT_log_ten_eq` + d9; mirror of `sSCUT_theta8_sharp_mem`). -/
theorem sSCUT_theta10_sharp_mem :
    (23.025850926 : ℝ) < 10 * Real.log 10 ∧
    10 * Real.log 10 < (23.025850934 : ℝ) := by
  have h10 := sSCUT_log_ten_eq
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have h5lo := Real.log_five_gt_d9
  have h5hi := Real.log_five_lt_d9
  have hsum_lo : (2.3025850926 : ℝ) < Real.log 2 + Real.log 5 := by
    have c : (0.6931471803 : ℝ) + 1.6094379123 = 2.3025850926 := by norm_num
    linarith
  have hsum_hi : Real.log 2 + Real.log 5 < (2.3025850934 : ℝ) := by
    have c : (0.6931471808 : ℝ) + 1.6094379126 = 2.3025850934 := by norm_num
    linarith
  have hmul_lo := mul_lt_mul_of_pos_left hsum_lo (by norm_num : (0 : ℝ) < 10)
  have hmul_hi := mul_lt_mul_of_pos_left hsum_hi (by norm_num : (0 : ℝ) < 10)
  have c1 : (10 : ℝ) * 2.3025850926 = 23.025850926 := by norm_num
  have c2 : (10 : ℝ) * 2.3025850934 = 23.025850934 := by norm_num
  constructor <;> linarith

/-- Exact width of the sharp `n = 10` window (`8e-9`). -/
theorem sSCUT_theta10_sharp_width_eq :
    (23.025850934 : ℝ) - 23.025850926 = (0.000000008 : ℝ) := by
  norm_num

/-- Reduced phase `δ₈' = θ₈ - 7π ∈ (-1.1968, -1.1960)` (odd multiple: next
step gets `cos θ₈ = -cos δ₈'` — the signed-upper recipe). -/
theorem sSCUT_delta8p_sharp_mem :
    (-1.1968 : ℝ) < 10 * Real.log 8 - 7 * Real.pi ∧
    10 * Real.log 8 - 7 * Real.pi < (-1.1960 : ℝ) := by
  have hth := sSCUT_theta8_sharp_mem
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  constructor <;> linarith

/-- Reduced phase `δ₁₀' = θ₁₀ - 7π ∈ (1.0346, 1.0354)` (mirror of `δ₈'`). -/
theorem sSCUT_delta10p_sharp_mem :
    (1.0346 : ℝ) < 10 * Real.log 10 - 7 * Real.pi ∧
    10 * Real.log 10 - 7 * Real.pi < (1.0354 : ℝ) := by
  have hth := sSCUT_theta10_sharp_mem
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  constructor <;> linarith

/-- Signed cosine UPPER `cos(10*log 8) ≤ -(1/4)` (quadrant-II `δ₈'` via the
odd-multiple flip `cos θ₈ = -cos δ₈'` + quadratic lower on `δ₈'`). -/
theorem sSCUT_cos10log8_le_neg_quarter :
    Real.cos (10 * Real.log 8) ≤ (-(1 / 4) : ℝ) := by
  have hδ := sSCUT_delta8p_sharp_mem
  have key : Real.cos ((10 * Real.log 8 - 7 * Real.pi) + Real.pi
      + 2 * Real.pi + 2 * Real.pi + 2 * Real.pi)
      = -Real.cos (10 * Real.log 8 - 7 * Real.pi) := by
    rw [Real.cos_add_two_pi, Real.cos_add_two_pi, Real.cos_add_two_pi,
      Real.cos_add_pi]
  have e2 : (10 * Real.log 8 - 7 * Real.pi) + Real.pi
      + 2 * Real.pi + 2 * Real.pi + 2 * Real.pi = 10 * Real.log 8 := by
    ring
  rw [e2] at key
  have hcosδ : 1 - (1.1968 : ℝ) ^ 2 / 2
      ≤ Real.cos (10 * Real.log 8 - 7 * Real.pi) := by
    have hq := Real.one_sub_sq_div_two_le_cos
      (x := 10 * Real.log 8 - 7 * Real.pi)
    have hsq : (10 * Real.log 8 - 7 * Real.pi) ^ 2 ≤ (1.1968 : ℝ) ^ 2 := by
      have ha : (0 : ℝ) ≤ 1.1968 - (10 * Real.log 8 - 7 * Real.pi) := by
        linarith [hδ.2]
      have hb : (0 : ℝ) ≤ (10 * Real.log 8 - 7 * Real.pi) + 1.1968 := by
        linarith [hδ.1]
      have hprod := mul_nonneg ha hb
      have heq : (1.1968 - (10 * Real.log 8 - 7 * Real.pi))
          * ((10 * Real.log 8 - 7 * Real.pi) + 1.1968)
          = (1.1968 : ℝ) ^ 2 - (10 * Real.log 8 - 7 * Real.pi) ^ 2 := by
        ring
      linarith
    linarith
  have hbase : (1 / 4 : ℝ) ≤ 1 - (1.1968 : ℝ) ^ 2 / 2 := by norm_num
  rw [key]
  linarith

/-- Signed cosine UPPER `cos(10*log 10) ≤ -(1/2)` (quadrant-III `δ₁₀'` via the
odd-multiple flip `cos θ₁₀ = -cos δ₁₀'` + sine-cubic floor on `π/2 - 1.0354`). -/
theorem sSCUT_cos10log10_le_neg_half :
    Real.cos (10 * Real.log 10) ≤ (-(1 / 2) : ℝ) := by
  have hδ := sSCUT_delta10p_sharp_mem
  have key : Real.cos ((10 * Real.log 10 - 7 * Real.pi) + Real.pi
      + 2 * Real.pi + 2 * Real.pi + 2 * Real.pi)
      = -Real.cos (10 * Real.log 10 - 7 * Real.pi) := by
    rw [Real.cos_add_two_pi, Real.cos_add_two_pi, Real.cos_add_two_pi,
      Real.cos_add_pi]
  have e2 : (10 * Real.log 10 - 7 * Real.pi) + Real.pi
      + 2 * Real.pi + 2 * Real.pi + 2 * Real.pi = 10 * Real.log 10 := by
    ring
  rw [e2] at key
  have hcosδ : (1 / 2 : ℝ) ≤ Real.cos (10 * Real.log 10 - 7 * Real.pi) := by
    have hpi_lo := Real.pi_gt_d4
    have hpi_hi := Real.pi_lt_d4
    have hδnn : (0 : ℝ) ≤ 10 * Real.log 10 - 7 * Real.pi := by
      linarith [hδ.1]
    have hbound_pi : (1.0354 : ℝ) ≤ Real.pi := by
      linarith
    have hmono : Real.cos (1.0354 : ℝ)
        ≤ Real.cos (10 * Real.log 10 - 7 * Real.pi) := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi hδnn hbound_pi
      linarith [hδ.2]
    have hy_nn : (0 : ℝ) ≤ Real.pi / 2 - 1.0354 := by
      linarith
    have hy_lo : (0.5353 : ℝ) ≤ Real.pi / 2 - 1.0354 := by
      linarith
    have hy_hi : Real.pi / 2 - 1.0354 ≤ (0.5354 : ℝ) := by
      linarith
    have hy3 : (Real.pi / 2 - 1.0354) ^ 3 ≤ (0.5354 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hy_nn hy_hi 3
    have hcube := Real.sin_ge_sub_cube (x := Real.pi / 2 - 1.0354) hy_nn
    have hrewrite : Real.cos (1.0354 : ℝ)
        = Real.sin (Real.pi / 2 - 1.0354) :=
      (Real.sin_pi_div_two_sub 1.0354).symm
    have hfloor : (1 / 2 : ℝ)
        ≤ (Real.pi / 2 - 1.0354) - (Real.pi / 2 - 1.0354) ^ 3 / 6 := by
      have hnum : (1 / 2 : ℝ) ≤ (0.5353 : ℝ) - (0.5354 : ℝ) ^ 3 / 6 := by
        norm_num
      linarith
    linarith [hrewrite, hmono, hcube, hfloor]
  rw [key]
  linarith

/-- `10^(-1/2) ≤ 1` (trivial rpow decay upper, mirror of
`R00_rpow_four_neg0395_le`; no estimated numerics). -/
theorem sSCUT_rpow10_neg_le_one : (10 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
  have h : (10 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (10 : ℝ) ^ (0 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [Real.rpow_zero] at h
  exact h

/-- Cpow real-part split for `10^{-s}` at sCut (mirror of
`sSCUT_cpow8_neg_re`). -/
theorem sSCUT_cpow10_neg_re : ((((10 : ℝ)) : ℂ) ^ (-sSCUT)).re
    = (10 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 10) := by
  have h10pos : (0 : ℝ) < 10 := by norm_num
  have hxC : ((10 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h10pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((10 : ℝ) : ℂ) = (((Real.log 10 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h10pos)).symm
  rw [hlog]
  have hre_w : (-sSCUT).re = (-(1 / 2 : ℝ)) := by
    have e : (-sSCUT).re = -(sSCUT.re) := rfl
    rw [e, sSCUT_re]
  have him_w : (-sSCUT).im = (-10 : ℝ) := by
    have e : (-sSCUT).im = -(sSCUT.im) := rfl
    rw [e, sSCUT_im]
  have hzre : ((((Real.log 10 : ℝ)) : ℂ)).re = Real.log 10 := Complex.ofReal_re _
  have hzim : ((((Real.log 10 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 10 : ℝ)) : ℂ) * (-sSCUT)).re
      = Real.log 10 * (-(1 / 2 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 10 : ℝ)) : ℂ) * (-sSCUT)).im
      = -(10 * Real.log 10) := by
    rw [Complex.mul_im, hzre, hzim, hre_w, him_w]
    ring
  have hexp : Real.exp (Real.log 10 * (-(1 / 2 : ℝ)))
      = (10 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_def_of_pos h10pos _).symm
  have hcos : Real.cos (-(10 * Real.log 10))
      = Real.cos (10 * Real.log 10) := Real.cos_neg _
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- Cpow signed UPPER `Re(10^{-sCut}) ≤ -(r₁₀/2)` (nonneg `r₁₀` × signed
cosine upper `cos θ₁₀ ≤ -1/2`). -/
theorem sSCUT_cpow10_neg_Re_upper :
    ((((10 : ℝ)) : ℂ) ^ (-sSCUT)).re ≤ -((10 : ℝ) ^ (-(1 / 2 : ℝ)) / 2) := by
  rw [sSCUT_cpow10_neg_re]
  have hr0 : (0 : ℝ) ≤ (10 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hc := sSCUT_cos10log10_le_neg_half
  have hmul : (10 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 10)
      ≤ (10 : ℝ) ^ (-(1 / 2 : ℝ)) * (-(1 / 2)) :=
    mul_le_mul_of_nonneg_left hc hr0
  have hsign : (10 : ℝ) ^ (-(1 / 2 : ℝ)) * (-(1 / 2))
      = -((10 : ℝ) ^ (-(1 / 2 : ℝ)) / 2) := by ring
  linarith

/-- Cpow real-part split for `8^{-s}` at sCut (mirror of
`sSCUT_cpow3_neg_re`). -/
theorem sSCUT_cpow8_neg_re : ((((8 : ℝ)) : ℂ) ^ (-sSCUT)).re
    = (8 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 8) := by
  have h8pos : (0 : ℝ) < 8 := by norm_num
  have hxC : ((8 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h8pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((8 : ℝ) : ℂ) = (((Real.log 8 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h8pos)).symm
  rw [hlog]
  have hre_w : (-sSCUT).re = (-(1 / 2 : ℝ)) := by
    have e : (-sSCUT).re = -(sSCUT.re) := rfl
    rw [e, sSCUT_re]
  have him_w : (-sSCUT).im = (-10 : ℝ) := by
    have e : (-sSCUT).im = -(sSCUT.im) := rfl
    rw [e, sSCUT_im]
  have hzre : ((((Real.log 8 : ℝ)) : ℂ)).re = Real.log 8 := Complex.ofReal_re _
  have hzim : ((((Real.log 8 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 8 : ℝ)) : ℂ) * (-sSCUT)).re
      = Real.log 8 * (-(1 / 2 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 8 : ℝ)) : ℂ) * (-sSCUT)).im
      = -(10 * Real.log 8) := by
    rw [Complex.mul_im, hzre, hzim, hre_w, him_w]
    ring
  have hexp : Real.exp (Real.log 8 * (-(1 / 2 : ℝ)))
      = (8 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_def_of_pos h8pos _).symm
  have hcos : Real.cos (-(10 * Real.log 8))
      = Real.cos (10 * Real.log 8) := Real.cos_neg _
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- `8^(1/2) ≤ 3` (mirror of the `sSCUT_sqrt2_le` root step; `8 ≤ 3^2`). -/
theorem sSCUT_sqrt8_le : (8 : ℝ) ^ (1 / 2 : ℝ) ≤ (3 : ℝ) := by
  have hpow : (8 : ℝ) ≤ ((3 : ℝ) ^ (2 : ℕ)) := by norm_num
  have hpow' : ((((8 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ))) = 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hle : ((((8 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ))) ≤ ((3 : ℝ) ^ (2 : ℕ)) := by
    rw [hpow']; exact hpow
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hle

/-- `1/3 ≤ r₈ = 8^(-1/2)` (inverse of the root step; mirror of
`sSCUT_rpow2_neg_ge`). -/
theorem sSCUT_rpow8_neg_ge : (1 / 3 : ℝ) ≤ (8 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hle := sSCUT_sqrt8_le
  have hpos : (0 : ℝ) < (8 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hneg : (8 : ℝ) ^ (-(1 / 2 : ℝ)) = (((8 : ℝ) ^ (1 / 2 : ℝ))⁻¹) := by
    rw [show (-(1 / 2 : ℝ)) = -((1 / 2 : ℝ)) by norm_num,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8)]
  rw [hneg, show (1 / 3 : ℝ) = ((3 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num) hpos).mpr hle

/-- Cpow signed UPPER `Re(8^{-sCut}) ≤ -(1/12)` (nonneg `r₈` × signed
cosine upper, then `r₈ ≥ 1/3`). -/
theorem sSCUT_cpow8_Re_le_neg :
    ((((8 : ℝ)) : ℂ) ^ (-sSCUT)).re ≤ (-(1 / 12) : ℝ) := by
  rw [sSCUT_cpow8_neg_re]
  have hr0 : (0 : ℝ) ≤ (8 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr_lo := sSCUT_rpow8_neg_ge
  have hc := sSCUT_cos10log8_le_neg_quarter
  have hmul : (8 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 8)
      ≤ (8 : ℝ) ^ (-(1 / 2 : ℝ)) * (-(1 / 4)) :=
    mul_le_mul_of_nonneg_left hc hr0
  have h2 : (1 / 3 : ℝ) * (1 / 4) ≤ (8 : ℝ) ^ (-(1 / 2 : ℝ)) * (1 / 4) :=
    mul_le_mul_of_nonneg_right hr_lo (by norm_num)
  have heq : (1 / 3 : ℝ) * (1 / 4) = 1 / 12 := by norm_num
  have hsign : (8 : ℝ) ^ (-(1 / 2 : ℝ)) * (-(1 / 4))
      = -((8 : ℝ) ^ (-(1 / 2 : ℝ)) * (1 / 4)) := by ring
  linarith

/-- Eta bridge `eta₇ = -(8^{-sCut})` (odd `k`; `Complex.cpow_neg` turns
`(8^s)⁻¹` into `8^{-s}`). -/
theorem sSCUT_eta7_eq_neg_cpow8 :
    etaDirichletTerm sSCUT 7 = -((((8 : ℝ)) : ℂ) ^ (-sSCUT)) := by
  have e : (7 + 1 : ℕ) = 8 := rfl
  have hcast : ((((7 + 1 : ℕ)) : ℂ)) = ((((8 : ℕ)) : ℂ)) := by rw [e]
  have hneg : (-1 : ℂ) ^ (7 : ℕ) = -1 := by norm_num
  have h8cast : ((((8 : ℕ)) : ℂ)) = ((((8 : ℝ)) : ℂ)) := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, h8cast, neg_div, one_div, Complex.cpow_neg]

/-- Parity payoff (odd `k = 7`): `Re(eta₇) ≥ +1/12` (negated cpow signed
upper). -/
theorem sSCUT_eta7_Re_ge : (1 / 12 : ℝ) ≤ (etaDirichletTerm sSCUT 7).re := by
  have h := sSCUT_cpow8_Re_le_neg
  rw [sSCUT_eta7_eq_neg_cpow8, Complex.neg_re, sSCUT_cpow8_neg_re]
  rw [sSCUT_cpow8_neg_re] at h
  linarith

/-- Eta bridge `eta₁ = -(2^{-sCut})` (odd `k`; mirror of the `t₇` bridge). -/
theorem sSCUT_eta1_eq_neg_cpow2 :
    etaDirichletTerm sSCUT 1 = -((((2 : ℝ)) : ℂ) ^ (-sSCUT)) := by
  have e : (1 + 1 : ℕ) = 2 := rfl
  have hcast : ((((1 + 1 : ℕ)) : ℂ)) = ((((2 : ℕ)) : ℂ)) := by rw [e]
  have hneg : (-1 : ℂ) ^ (1 : ℕ) = -1 := by norm_num
  have h2cast : ((((2 : ℕ)) : ℂ)) = ((((2 : ℝ)) : ℂ)) := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, h2cast, neg_div, one_div, Complex.cpow_neg]

/-- `Re(eta₁) ≥ -(5/7)` (negated `sSCUT_cpow2_Re_mem` upper). -/
theorem sSCUT_eta1_Re_ge_neg :
    (-(5 / 7) : ℝ) ≤ (etaDirichletTerm sSCUT 1).re := by
  have h := sSCUT_cpow2_Re_mem
  rw [sSCUT_eta1_eq_neg_cpow2, Complex.neg_re, sSCUT_cpow2_neg_re]
  linarith [h.2]

/-- `Re(S₂) ≥ 2/7` at sCut (`1 + Re(eta₁) ≥ 1 - 5/7`). -/
theorem sSCUT_S2_Re_ge :
    (2 / 7 : ℝ) ≤ (∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k).re := by
  have h0 : etaDirichletTerm sSCUT 0 = 1 := by
    simp only [etaDirichletTerm]
    simp
  have hS2 : (∑ k ∈ Finset.range 2, etaDirichletTerm sSCUT k)
      = 1 + etaDirichletTerm sSCUT 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, h0]
  have he1 := sSCUT_eta1_Re_ge_neg
  rw [hS2, Complex.add_re, Complex.one_re]
  linarith

/-- Trivial `Re` floor `Re(eta₂) ≥ -1` (`|Re| ≤ ‖·‖ ≤ 1` banked). -/
theorem sSCUT_eta2_Re_ge_neg_one :
    (-1 : ℝ) ≤ (etaDirichletTerm sSCUT 2).re := by
  have h := sSCUT_eta_third_norm_le_one
  have habs := Complex.abs_re_le_norm (etaDirichletTerm sSCUT 2)
  have hle := abs_le.mp habs
  linarith [hle.1]

/-- Trivial `Re` floor `Re(eta₃) ≥ -1` (`|Re| ≤ ‖·‖ ≤ 1` banked). -/
theorem sSCUT_eta3_Re_ge_neg_one :
    (-1 : ℝ) ≤ (etaDirichletTerm sSCUT 3).re := by
  have h := sSCUT_eta_fourth_norm_le_one
  have habs := Complex.abs_re_le_norm (etaDirichletTerm sSCUT 3)
  have hle := abs_le.mp habs
  linarith [hle.1]

/-- Trivial `Re` floor `Re(eta₄) ≥ -1` (`|Re| ≤ ‖·‖ ≤ 1` banked). -/
theorem sSCUT_eta4_Re_ge_neg_one :
    (-1 : ℝ) ≤ (etaDirichletTerm sSCUT 4).re := by
  have h := sSCUT_eta_fifth_norm_le_one
  have habs := Complex.abs_re_le_norm (etaDirichletTerm sSCUT 4)
  have hle := abs_le.mp habs
  linarith [hle.1]

/-- Trivial `Re` floor `Re(eta₅) ≥ -1` (`|Re| ≤ ‖·‖ ≤ 1` banked). -/
theorem sSCUT_eta5_Re_ge_neg_one :
    (-1 : ℝ) ≤ (etaDirichletTerm sSCUT 5).re := by
  have h := sSCUT_eta_sixth_norm_le_one
  have habs := Complex.abs_re_le_norm (etaDirichletTerm sSCUT 5)
  have hle := abs_le.mp habs
  linarith [hle.1]

/-- Trivial `Re` floor `Re(eta₆) ≥ -1` (`|Re| ≤ ‖·‖ ≤ 1` banked). -/
theorem sSCUT_eta6_Re_ge_neg_one :
    (-1 : ℝ) ≤ (etaDirichletTerm sSCUT 6).re := by
  have h := sSCUT_eta_seventh_norm_le_one
  have habs := Complex.abs_re_le_norm (etaDirichletTerm sSCUT 6)
  have hle := abs_le.mp habs
  linarith [hle.1]

/-- Honest 8-term `Re` shard floor (`-389/84 ≤ Re(S₈)`:
`2/7 - 5 + 1/12`; the `+1/12` is the banked `t₇` signed gain). -/
theorem sSCUT_S8_Re_ge_neg389div84 :
    (-389 / 84 : ℝ) ≤ (∑ k ∈ Finset.range 8, etaDirichletTerm sSCUT k).re := by
  rw [sSCUT_S8_eq, Complex.add_re, Complex.add_re, Complex.add_re,
    Complex.add_re, Complex.add_re, Complex.add_re]
  have hS2 := sSCUT_S2_Re_ge
  have h2 := sSCUT_eta2_Re_ge_neg_one
  have h3 := sSCUT_eta3_Re_ge_neg_one
  have h4 := sSCUT_eta4_Re_ge_neg_one
  have h5 := sSCUT_eta5_Re_ge_neg_one
  have h6 := sSCUT_eta6_Re_ge_neg_one
  have h7 := sSCUT_eta7_Re_ge
  have hgap : (2 / 7 : ℝ) + (-1) + (-1) + (-1) + (-1) + (-1) + (1 / 12)
      = (-389 / 84) := by norm_num
  linarith

/-- Honest 8-term norm shard floor (`-389/84 ≤ ‖S₈‖`, via `Re ≤ ‖·‖`;
stronger than `-40/7` by exactly `13/12`, still negative — no growth). -/
theorem sSCUT_S8_norm_ge_neg389div84 :
    (-389 / 84 : ℝ) ≤ ‖∑ k ∈ Finset.range 8, etaDirichletTerm sSCUT k‖ := by
  have h := sSCUT_S8_Re_ge_neg389div84
  have hrn := Complex.re_le_norm
    (∑ k ∈ Finset.range 8, etaDirichletTerm sSCUT k)
  linarith

/-- Shard floor vs the `21/10` bar (gap `21/10 + 389/84 = 2827/420`). -/
theorem sSCUT_S8_gap_eq :
    ((21 / 10 : ℝ) - (-389 / 84)) = (2827 / 420 : ℝ) := by
  norm_num

/-- Shard floor sits below the bar (binding slow stays `2/7`; STOP). -/
theorem sSCUT_S8_floor_below_bar : (-389 / 84 : ℝ) < (21 / 10 : ℝ) := by
  norm_num

/-! ## sCut S8b shard (ZETA-SCUT4): `n = 5` dead, `n = 7` signed gain (`+27/100`).

Inventory verdict (READ-ONLY survey this turn; reuse, no duplication):
* `Mathlib/Analysis/Complex/ExponentialBounds.lean:109-125` banks d9
  `Real.log_five_gt_d9` (`1.6094379123 < log 5`) / `Real.log_five_lt_d9`
  (`log 5 < 1.6094379126`); same file `:71-105` banks `log 2` / `log 3` d9.
  `Mathlib/Analysis/SpecialFunctions/Log/*` banks only generic
  (`log_le_sub_one_of_pos`, `log_le_log`) — no `5`/`7` numerals.
* d9 `log 7` is ABSENT from Mathlib but PRESENT in-repo at
  `zeta_rigorous.lean:7579-7600`: `Real.log_seven_near_10` (decimal-digit
  `x = 6/7`, `n = 175` mirror of `log_five_near_10`) with
  `Real.log_seven_gt_d9` (`1.9459101489 < log 7`) /
  `Real.log_seven_lt_d9` (`log 7 < 1.9459101492`). This file already
  `import zeta_rigorous` (`:5`), so both d9 pairs are referenced directly —
  the S3b comment "absent from Mathlib (must be created in-file)" is now
  stale for `7` (still true for Mathlib itself); no `2401/2400` fallback
  (`dp_headA_log7_lo/hi`, `r05_log7_lo/hi`: `1.9458-1.9461`, width `3e-4`)
  and no `log_five_d9`-style re-proof needed.
* `door3_cell_suppliers.lean:1382-1392` (`CS_log_five_ge/le`) is the reuse
  template: `have h := Real.log_five_gt_d9; norm_num at h ⊢; linarith`.

Outcome (mirror of the `:2399-2566` recipe):
* `θ₅ = 10*log 5 ∈ (16.094379123, 16.094379126)` (d9, width `3e-9`);
  `δ₅ = θ₅ - 4π ∈ (3.5279, 3.5284) ⊂ (π, 3π/2)` so `cos θ₅ ≤ 0` and
  `Re(5^{-sCut}) ≤ 0` — even `k = 4` needs `cos ≥ +c`, so NO positive lock
  exists at any precision (`sSCUT_cpow5_Re_no_pos_lock`); `t₄` keeps the
  trivial `-1` floor.
* `θ₇ = 10*log 7 ∈ (19.459101489, 19.459101492)` (d9 via `zeta_rigorous`,
  width `3e-9`); `δ₇ = θ₇ - 6π ∈ (0.6095, 0.6102)` (even multiple, so
  `cos θ₇ = cos δ₇ ≥ 1 - 0.6102²/2 ≥ 81/100`); `r₇ = 7^{-1/2} ≥ 1/3`
  (from `√7 ≤ 3`); `Re(7^{-sCut}) ≥ 27/100`; even `k = 6` transfers with
  NO sign flip (`eta₆ = 7^{-sCut}`): `Re(eta₆) ≥ +27/100`.
* Reassembled shard: `Re(S₈) ≥ 2/7 - 4 + 27/100 + 1/12 = -3529/1050`
  (`sSCUT_S8_Re_ge_neg3529div1050`); gain over `-389/84` is exactly
  `127/100` (the `t₆` allowance flip `-1 → +27/100`). Still negative, so
  binding slow stays `2/7`; gap to `21/10` is `2867/525`.
* Pivot assessed honestly (no new theorems): `n = 9`/`12` composites are
  already sharp-banked (`sSCUT_theta9/theta12_sharp_mem`) and DEAD/HURT for
  growth (`δ₉` gives `cos θ₉ ≈ -1` with odd-`k` flip; `δ₁₂` has odd-`k`
  flip); `n = 10` (`log 10 = log 2 + log 5` d9 composite, `δ₁₀ ≈ 4.1763`
  quadrant III, odd-`k` candidate) and `n = 11` (`zeta_rigorous` log-eleven
  d9) are future lanes OUTSIDE `S₈` — not forced here.
-/

/-- Sharp `n = 5` phase window (`10*log 5 ∈ (16.094379123, 16.094379126)`
from Mathlib d9; mirror of `sSCUT_theta3_sharp_mem`). -/
theorem sSCUT_theta5_sharp_mem :
    (16.094379123 : ℝ) < 10 * Real.log 5 ∧
    10 * Real.log 5 < (16.094379126 : ℝ) := by
  have hlo := Real.log_five_gt_d9
  have hhi := Real.log_five_lt_d9
  have hmul_lo := mul_lt_mul_of_pos_left hlo (by norm_num : (0 : ℝ) < 10)
  have hmul_hi := mul_lt_mul_of_pos_left hhi (by norm_num : (0 : ℝ) < 10)
  have c1 : (10 : ℝ) * 1.6094379123 = 16.094379123 := by norm_num
  have c2 : (10 : ℝ) * 1.6094379126 = 16.094379126 := by norm_num
  constructor <;> linarith

/-- Sharp `n = 7` phase window (`10*log 7 ∈ (19.459101489, 19.459101492)`
from `zeta_rigorous` d9; mirror of `sSCUT_theta3_sharp_mem`). -/
theorem sSCUT_theta7_sharp_mem :
    (19.459101489 : ℝ) < 10 * Real.log 7 ∧
    10 * Real.log 7 < (19.459101492 : ℝ) := by
  have hlo := Real.log_seven_gt_d9
  have hhi := Real.log_seven_lt_d9
  have hmul_lo := mul_lt_mul_of_pos_left hlo (by norm_num : (0 : ℝ) < 10)
  have hmul_hi := mul_lt_mul_of_pos_left hhi (by norm_num : (0 : ℝ) < 10)
  have c1 : (10 : ℝ) * 1.9459101489 = 19.459101489 := by norm_num
  have c2 : (10 : ℝ) * 1.9459101492 = 19.459101492 := by norm_num
  constructor <;> linarith

/-- Sharp reduced phase `δ₅ = θ₅ - 4π ∈ (3.5279, 3.5284)` (via `pi_d4`). -/
theorem sSCUT_delta5_sharp_mem :
    (3.5279 : ℝ) < 10 * Real.log 5 - 4 * Real.pi ∧
    10 * Real.log 5 - 4 * Real.pi < (3.5284 : ℝ) := by
  have hth := sSCUT_theta5_sharp_mem
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  constructor <;> linarith

/-- Sharp reduced phase `δ₇ = θ₇ - 6π ∈ (0.6095, 0.6102)` (via `pi_d4`). -/
theorem sSCUT_delta7_sharp_mem :
    (0.6095 : ℝ) < 10 * Real.log 7 - 6 * Real.pi ∧
    10 * Real.log 7 - 6 * Real.pi < (0.6102 : ℝ) := by
  have hth := sSCUT_theta7_sharp_mem
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  constructor <;> linarith

/-- `δ₅` sits in quadrant III (`π < δ₅ < 3π/2`). -/
theorem sSCUT_delta5_in_quadrantIII :
    Real.pi < 10 * Real.log 5 - 4 * Real.pi ∧
    10 * Real.log 5 - 4 * Real.pi < 3 * Real.pi / 2 := by
  have hth := sSCUT_delta5_sharp_mem
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  constructor <;> linarith

/-- `cos(10*log 5) ≤ 0` (quadrant-III `δ₅` + two `Real.cos_sub_two_pi`). -/
theorem sSCUT_cos10log5_nonpos : Real.cos (10 * Real.log 5) ≤ 0 := by
  have hδ := sSCUT_delta5_in_quadrantIII
  have hcosδ : Real.cos (10 * Real.log 5 - 4 * Real.pi) ≤ 0 := by
    apply Real.cos_nonpos_of_pi_div_two_le_of_le
    · have hpi := Real.pi_pos
      linarith [hδ.1]
    · linarith [hδ.2]
  have hper1 : Real.cos (10 * Real.log 5 - 2 * Real.pi)
      = Real.cos (10 * Real.log 5) :=
    Real.cos_sub_two_pi _
  have hper2 : Real.cos ((10 * Real.log 5 - 2 * Real.pi) - 2 * Real.pi)
      = Real.cos (10 * Real.log 5 - 2 * Real.pi) :=
    Real.cos_sub_two_pi _
  have e : (10 * Real.log 5 - 2 * Real.pi) - 2 * Real.pi
      = 10 * Real.log 5 - 4 * Real.pi := by
    ring
  rw [e] at hper2
  rw [hper1] at hper2
  rw [hper2] at hcosδ
  exact hcosδ

/-- Cpow real-part split for `5^{-s}` at sCut (mirror of
`sSCUT_cpow3_neg_re`). -/
theorem sSCUT_cpow5_neg_re : ((((5 : ℝ)) : ℂ) ^ (-sSCUT)).re
    = (5 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 5) := by
  have h5pos : (0 : ℝ) < 5 := by norm_num
  have hxC : ((5 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h5pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((5 : ℝ) : ℂ) = (((Real.log 5 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h5pos)).symm
  rw [hlog]
  have hre_w : (-sSCUT).re = (-(1 / 2 : ℝ)) := by
    have e : (-sSCUT).re = -(sSCUT.re) := rfl
    rw [e, sSCUT_re]
  have him_w : (-sSCUT).im = (-10 : ℝ) := by
    have e : (-sSCUT).im = -(sSCUT.im) := rfl
    rw [e, sSCUT_im]
  have hzre : ((((Real.log 5 : ℝ)) : ℂ)).re = Real.log 5 := Complex.ofReal_re _
  have hzim : ((((Real.log 5 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 5 : ℝ)) : ℂ) * (-sSCUT)).re
      = Real.log 5 * (-(1 / 2 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 5 : ℝ)) : ℂ) * (-sSCUT)).im
      = -(10 * Real.log 5) := by
    rw [Complex.mul_im, hzre, hzim, hre_w, him_w]
    ring
  have hexp : Real.exp (Real.log 5 * (-(1 / 2 : ℝ)))
      = (5 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_def_of_pos h5pos _).symm
  have hcos : Real.cos (-(10 * Real.log 5))
      = Real.cos (10 * Real.log 5) := Real.cos_neg _
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- `Re(5^{-sCut}) ≤ 0` at cpow level (nonneg rpow × nonpos cosine). -/
theorem sSCUT_cpow5_neg_Re_nonpos : ((((5 : ℝ)) : ℂ) ^ (-sSCUT)).re ≤ 0 := by
  rw [sSCUT_cpow5_neg_re]
  have hr : (0 : ℝ) ≤ (5 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hc := sSCUT_cos10log5_nonpos
  exact mul_nonpos_of_nonneg_of_nonpos hr hc

/-- No positive `Re₅` lock exists at any precision (even `k = 4` needs
`cos ≥ +c`; the sharp window kills it — mirror of
`sSCUT_cpow3_Re_no_pos_lock`). -/
theorem sSCUT_cpow5_Re_no_pos_lock (c : ℝ) (hc : (0 : ℝ) < c) :
    ¬ (c ≤ ((((5 : ℝ)) : ℂ) ^ (-sSCUT)).re) := by
  intro h
  have hnp := sSCUT_cpow5_neg_Re_nonpos
  linarith

/-- Signed cosine LOWER `81/100 ≤ cos(10*log 7)` (quadrant-I `δ₇` via the
even-multiple strip `cos θ₇ = cos δ₇` + quadratic lower on `δ₇`). -/
theorem sSCUT_cos10log7_ge : (81 / 100 : ℝ) ≤ Real.cos (10 * Real.log 7) := by
  have hδ := sSCUT_delta7_sharp_mem
  set y : ℝ := 10 * Real.log 7 - 6 * Real.pi with hy_def
  have hy_lo : (0.6095 : ℝ) < y := by rw [hy_def]; linarith [hδ.1]
  have hy_hi : y < (0.6102 : ℝ) := by rw [hy_def]; linarith [hδ.2]
  have hy_nn : (0 : ℝ) ≤ y := by linarith [hy_lo]
  have hsq : y ^ 2 ≤ (0.6102 : ℝ) ^ 2 := pow_le_pow_left₀ hy_nn hy_hi.le 2
  have hcos_lo := Real.one_sub_sq_div_two_le_cos (x := y)
  have hnum : (81 / 100 : ℝ) ≤ 1 - (0.6102 : ℝ) ^ 2 / 2 := by norm_num
  have hcosy : (81 / 100 : ℝ) ≤ Real.cos y := by
    have hle : 1 - (0.6102 : ℝ) ^ 2 / 2 ≤ 1 - y ^ 2 / 2 := by linarith [hsq]
    linarith [hcos_lo, hle, hnum]
  have hper1 : Real.cos (10 * Real.log 7 - 2 * Real.pi)
      = Real.cos (10 * Real.log 7) :=
    Real.cos_sub_two_pi _
  have hper2 : Real.cos ((10 * Real.log 7 - 2 * Real.pi) - 2 * Real.pi)
      = Real.cos (10 * Real.log 7 - 2 * Real.pi) :=
    Real.cos_sub_two_pi _
  have hper3
      : Real.cos (((10 * Real.log 7 - 2 * Real.pi) - 2 * Real.pi) - 2 * Real.pi)
      = Real.cos ((10 * Real.log 7 - 2 * Real.pi) - 2 * Real.pi) :=
    Real.cos_sub_two_pi _
  have e2 : (10 * Real.log 7 - 2 * Real.pi) - 2 * Real.pi
      = 10 * Real.log 7 - 4 * Real.pi := by
    ring
  have e3 : ((10 * Real.log 7 - 2 * Real.pi) - 2 * Real.pi) - 2 * Real.pi
      = 10 * Real.log 7 - 6 * Real.pi := by
    ring
  rw [e2] at hper2
  rw [e3] at hper3
  have hper : Real.cos (10 * Real.log 7 - 6 * Real.pi)
      = Real.cos (10 * Real.log 7) := by
    rw [hper3, e2, hper2, hper1]
  rw [hy_def, hper] at hcosy
  exact hcosy

/-- `7^(1/2) ≤ 3` (mirror of the `sSCUT_sqrt8_le` root step; `7 ≤ 3^2`). -/
theorem sSCUT_sqrt7_le : (7 : ℝ) ^ (1 / 2 : ℝ) ≤ (3 : ℝ) := by
  have hpow : (7 : ℝ) ≤ ((3 : ℝ) ^ (2 : ℕ)) := by norm_num
  have hpow' : ((((7 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ))) = 7 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hle : ((((7 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ))) ≤ ((3 : ℝ) ^ (2 : ℕ)) := by
    rw [hpow']; exact hpow
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hle

/-- `1/3 ≤ r₇ = 7^(-1/2)` (inverse of the root step; mirror of
`sSCUT_rpow8_neg_ge`). -/
theorem sSCUT_rpow7_neg_ge : (1 / 3 : ℝ) ≤ (7 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hle := sSCUT_sqrt7_le
  have hpos : (0 : ℝ) < (7 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hneg : (7 : ℝ) ^ (-(1 / 2 : ℝ)) = (((7 : ℝ) ^ (1 / 2 : ℝ))⁻¹) := by
    rw [show (-(1 / 2 : ℝ)) = -((1 / 2 : ℝ)) by norm_num,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 7)]
  rw [hneg, show (1 / 3 : ℝ) = ((3 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num) hpos).mpr hle

/-- Cpow real-part split for `7^{-s}` at sCut (mirror of
`sSCUT_cpow8_neg_re`). -/
theorem sSCUT_cpow7_neg_re : ((((7 : ℝ)) : ℂ) ^ (-sSCUT)).re
    = (7 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 7) := by
  have h7pos : (0 : ℝ) < 7 := by norm_num
  have hxC : ((7 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h7pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((7 : ℝ) : ℂ) = (((Real.log 7 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h7pos)).symm
  rw [hlog]
  have hre_w : (-sSCUT).re = (-(1 / 2 : ℝ)) := by
    have e : (-sSCUT).re = -(sSCUT.re) := rfl
    rw [e, sSCUT_re]
  have him_w : (-sSCUT).im = (-10 : ℝ) := by
    have e : (-sSCUT).im = -(sSCUT.im) := rfl
    rw [e, sSCUT_im]
  have hzre : ((((Real.log 7 : ℝ)) : ℂ)).re = Real.log 7 := Complex.ofReal_re _
  have hzim : ((((Real.log 7 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 7 : ℝ)) : ℂ) * (-sSCUT)).re
      = Real.log 7 * (-(1 / 2 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 7 : ℝ)) : ℂ) * (-sSCUT)).im
      = -(10 * Real.log 7) := by
    rw [Complex.mul_im, hzre, hzim, hre_w, him_w]
    ring
  have hexp : Real.exp (Real.log 7 * (-(1 / 2 : ℝ)))
      = (7 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_def_of_pos h7pos _).symm
  have hcos : Real.cos (-(10 * Real.log 7))
      = Real.cos (10 * Real.log 7) := Real.cos_neg _
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- Cpow signed LOWER `27/100 ≤ Re(7^{-sCut})` (`r₇ ≥ 1/3` × cosine
`≥ 81/100`, via two one-sided multiplies). -/
theorem sSCUT_cpow7_Re_ge :
    (27 / 100 : ℝ) ≤ ((((7 : ℝ)) : ℂ) ^ (-sSCUT)).re := by
  rw [sSCUT_cpow7_neg_re]
  have hr_lo := sSCUT_rpow7_neg_ge
  have hr0 : (0 : ℝ) ≤ (7 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hc_lo := sSCUT_cos10log7_ge
  have h1 : (1 / 3 : ℝ) * (81 / 100)
      ≤ (7 : ℝ) ^ (-(1 / 2 : ℝ)) * (81 / 100) :=
    mul_le_mul_of_nonneg_right hr_lo (by norm_num)
  have h2 : (7 : ℝ) ^ (-(1 / 2 : ℝ)) * (81 / 100)
      ≤ (7 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 7) :=
    mul_le_mul_of_nonneg_left hc_lo hr0
  have heq : (1 / 3 : ℝ) * (81 / 100) = 27 / 100 := by norm_num
  linarith

/-- Eta bridge `eta₆ = 7^{-sCut}` (even `k`; `Complex.cpow_neg` turns
`(7^s)⁻¹` into `7^{-s}`). -/
theorem sSCUT_eta6_eq_cpow7 :
    etaDirichletTerm sSCUT 6 = ((((7 : ℝ)) : ℂ) ^ (-sSCUT)) := by
  have e : (6 + 1 : ℕ) = 7 := rfl
  have hcast : ((((6 + 1 : ℕ)) : ℂ)) = ((((7 : ℕ)) : ℂ)) := by rw [e]
  have hneg : (-1 : ℂ) ^ (6 : ℕ) = 1 := by norm_num
  have h7cast : ((((7 : ℕ)) : ℂ)) = ((((7 : ℝ)) : ℂ)) := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, h7cast, one_div, Complex.cpow_neg]

/-- Parity payoff (even `k = 6`): `Re(eta₆) ≥ +27/100` (direct cpow signed
lower, no sign flip). -/
theorem sSCUT_eta6_Re_ge : (27 / 100 : ℝ) ≤ (etaDirichletTerm sSCUT 6).re := by
  have h := sSCUT_cpow7_Re_ge
  rw [sSCUT_eta6_eq_cpow7, sSCUT_cpow7_neg_re]
  rw [sSCUT_cpow7_neg_re] at h
  linarith

/-- Honest 8-term `Re` shard floor with the `t₆` signed gain
(`-3529/1050 ≤ Re(S₈)`: `2/7 - 4 + 27/100 + 1/12`, replacing `-389/84`;
the `t₄` (`n = 5`) slot keeps `-1` since no positive lock exists). -/
theorem sSCUT_S8_Re_ge_neg3529div1050 :
    (-3529 / 1050 : ℝ) ≤ (∑ k ∈ Finset.range 8, etaDirichletTerm sSCUT k).re := by
  rw [sSCUT_S8_eq, Complex.add_re, Complex.add_re, Complex.add_re,
    Complex.add_re, Complex.add_re, Complex.add_re]
  have hS2 := sSCUT_S2_Re_ge
  have h2 := sSCUT_eta2_Re_ge_neg_one
  have h3 := sSCUT_eta3_Re_ge_neg_one
  have h4 := sSCUT_eta4_Re_ge_neg_one
  have h5 := sSCUT_eta5_Re_ge_neg_one
  have h6 := sSCUT_eta6_Re_ge
  have h7 := sSCUT_eta7_Re_ge
  have hgap : (2 / 7 : ℝ) + (-1) + (-1) + (-1) + (-1) + (27 / 100) + (1 / 12)
      = (-3529 / 1050) := by norm_num
  linarith

/-- Honest 8-term norm shard floor with the `t₆` gain
(`-3529/1050 ≤ ‖S₈‖`, via `Re ≤ ‖·‖`; gain `127/100` over `-389/84`,
still negative — no growth). -/
theorem sSCUT_S8_norm_ge_neg3529div1050 :
    (-3529 / 1050 : ℝ) ≤ ‖∑ k ∈ Finset.range 8, etaDirichletTerm sSCUT k‖ := by
  have h := sSCUT_S8_Re_ge_neg3529div1050
  have hrn := Complex.re_le_norm
    (∑ k ∈ Finset.range 8, etaDirichletTerm sSCUT k)
  linarith

/-- Shard floor vs the `21/10` bar (gap `21/10 + 3529/1050 = 2867/525`). -/
theorem sSCUT_S8_gap_eq_new :
    ((21 / 10 : ℝ) - (-3529 / 1050)) = (2867 / 525 : ℝ) := by
  norm_num

/-- Shard floor sits below the bar (binding slow stays `2/7`; STOP). -/
theorem sSCUT_S8_floor_below_bar_new :
    (-3529 / 1050 : ℝ) < (21 / 10 : ℝ) := by
  norm_num

/-- Eta bridge `eta₉ = -(10^{-sCut})` (odd `k`; `Complex.cpow_neg` turns
`(10^s)⁻¹` into `10^{-s}`; mirror of `sSCUT_eta7_eq_neg_cpow8`). -/
theorem sSCUT_eta9_eq_neg_cpow10 :
    etaDirichletTerm sSCUT 9 = -((((10 : ℝ)) : ℂ) ^ (-sSCUT)) := by
  have e : (9 + 1 : ℕ) = 10 := rfl
  have hcast : ((((9 + 1 : ℕ)) : ℂ)) = ((((10 : ℕ)) : ℂ)) := by rw [e]
  have hneg : (-1 : ℂ) ^ (9 : ℕ) = -1 := by norm_num
  have h10cast : ((((10 : ℕ)) : ℂ)) = ((((10 : ℝ)) : ℂ)) := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, h10cast, neg_div, one_div, Complex.cpow_neg]

/-- Parity payoff (odd `k = 9`): `Re(eta₉) ≥ +r₁₀/2` (negated cpow signed
upper `sSCUT_cpow10_neg_Re_upper`; negation flips the upper to a lower;
`r₁₀ = (10 : ℝ) ^ (-(1/2 : ℝ))` kept SYMBOLIC — no numeric lower banked). -/
theorem sSCUT_eta9_Re_ge :
    (10 : ℝ) ^ (-(1 / 2 : ℝ)) / 2 ≤ (etaDirichletTerm sSCUT 9).re := by
  have h := sSCUT_cpow10_neg_Re_upper
  rw [sSCUT_eta9_eq_neg_cpow10, Complex.neg_re, sSCUT_cpow10_neg_re]
  rw [sSCUT_cpow10_neg_re] at h
  linarith

/-- Honest `S₈ + eta₉` `Re` shard floor (`-3529/1050 + r₁₀/2 ≤ Re(S₈ + eta₉)`;
old floor plus the `t₉` signed gain; `r₁₀` explicit and symbolic; honest:
partial sum skips `k = 8` whose `Re` floor is not banked here, and no
numerics are claimed for `r₁₀`). -/
theorem sSCUT_S8_add_eta9_Re_ge :
    (-3529 / 1050 : ℝ) + (10 : ℝ) ^ (-(1 / 2 : ℝ)) / 2 ≤
      ((∑ k ∈ Finset.range 8, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 9).re := by
  rw [Complex.add_re]
  have hS8 := sSCUT_S8_Re_ge_neg3529div1050
  have h9 := sSCUT_eta9_Re_ge
  linarith

/-- `0.3 ≤ 10^(-1/2)` (inverse of the quadratic root step
`10^(1/2) ≤ 10/3`; mirror of `sSCUT_rpow8_neg_ge`). -/
theorem sSCUT_rpow10_neg_ge_03 : (0.3 : ℝ) ≤ (10 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hle : (10 : ℝ) ^ (1 / 2 : ℝ) ≤ (10 / 3 : ℝ) := by
    have hpow : (10 : ℝ) ≤ ((10 / 3 : ℝ) ^ (2 : ℕ)) := by norm_num
    have hpow' : ((((10 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ))) = 10 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
      rw [e, Real.rpow_one]
    have hle2 : ((((10 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ)))
        ≤ ((10 / 3 : ℝ) ^ (2 : ℕ)) := by
      rw [hpow']
      exact hpow
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hle2
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hneg : (10 : ℝ) ^ (-(1 / 2 : ℝ)) = (((10 : ℝ) ^ (1 / 2 : ℝ))⁻¹) := by
    rw [show (-(1 / 2 : ℝ)) = -((1 / 2 : ℝ)) by norm_num,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10)]
  rw [hneg, show (0.3 : ℝ) = ((10 / 3 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num) hpos).mpr hle

/-- Honest `S₈ + eta₉ + eta₆` `Re` floor (`-3529/1050 + 0.15 + 0.27 ≤ Re`;
`r₁₀/2` concretized via `0.3` lower, `27/100` is `sSCUT_eta6_Re_ge`;
`eta₇` in the name is `n = 7`, i.e. Lean index `6`). -/
theorem sSCUT_S8_add_eta9_eta7_Re_ge :
    (-3529 / 1050 : ℝ) + 0.15 + 0.27 ≤
      ((∑ k ∈ Finset.range 8, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 9 + etaDirichletTerm sSCUT 6).re := by
  rw [Complex.add_re]
  have hS8e9 := sSCUT_S8_add_eta9_Re_ge
  have h6 := sSCUT_eta6_Re_ge
  have hr10 := sSCUT_rpow10_neg_ge_03
  linarith

/-- Honest shortfall vs the `21/10` bar (gap `5293/1050`; still short). -/
theorem sSCUT_S8_eta9_eta7_shortfall :
    ((21 / 10 : ℝ) - ((-3529 / 1050) + 0.15 + 0.27)) = (5293 / 1050 : ℝ) := by
  norm_num

/-- Honest `S₈ + eta₉ + eta₆ + eta₇` `Re` floor (`-3529/1050 + 0.15 + 0.27 + 1/12 ≤ Re`;
base `sSCUT_S8_add_eta9_eta7_Re_ge` plus `1/12` from `sSCUT_eta7_Re_ge`;
honest indices: `S₈` covers `k = 0..7`, plus `k = 9`, plus a second copy of
`k = 6` (already double-counted in the base) and a second copy of `k = 7`;
`k = 8` is skipped, no hidden terms; `eta₇/eta₈` in the name are `n = 7/8`,
i.e. Lean indices `6/7`). -/
theorem sSCUT_S8_add_eta9_eta7_eta8_Re_ge :
    (-3529 / 1050 : ℝ) + 0.15 + 0.27 + (1 / 12) ≤
      ((∑ k ∈ Finset.range 8, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 9 + etaDirichletTerm sSCUT 6
        + etaDirichletTerm sSCUT 7).re := by
  rw [Complex.add_re]
  have hbase := sSCUT_S8_add_eta9_eta7_Re_ge
  have h7 := sSCUT_eta7_Re_ge
  linarith

/-- Honest shortfall vs the `21/10` bar for the `+1/12` floor
(gap `10411/2100`; still short, no close claimed). -/
theorem sSCUT_S8_eta9_eta7_eta8_shortfall :
    ((21 / 10 : ℝ) - ((-3529 / 1050) + 0.15 + 0.27 + (1 / 12)))
      = (10411 / 2100 : ℝ) := by
  norm_num

/-- Cpow real-part split for `9^{-s}` at sCut (mirror of
`sSCUT_cpow8_neg_re`). -/
theorem sSCUT_cpow9_neg_re : ((((9 : ℝ)) : ℂ) ^ (-sSCUT)).re
    = (9 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 9) := by
  have h9pos : (0 : ℝ) < 9 := by norm_num
  have hxC : ((9 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h9pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((9 : ℝ) : ℂ) = (((Real.log 9 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h9pos)).symm
  rw [hlog]
  have hre_w : (-sSCUT).re = (-(1 / 2 : ℝ)) := by
    have e : (-sSCUT).re = -(sSCUT.re) := rfl
    rw [e, sSCUT_re]
  have him_w : (-sSCUT).im = (-10 : ℝ) := by
    have e : (-sSCUT).im = -(sSCUT.im) := rfl
    rw [e, sSCUT_im]
  have hzre : ((((Real.log 9 : ℝ)) : ℂ)).re = Real.log 9 := Complex.ofReal_re _
  have hzim : ((((Real.log 9 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 9 : ℝ)) : ℂ) * (-sSCUT)).re
      = Real.log 9 * (-(1 / 2 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 9 : ℝ)) : ℂ) * (-sSCUT)).im
      = -(10 * Real.log 9) := by
    rw [Complex.mul_im, hzre, hzim, hre_w, him_w]
    ring
  have hexp : Real.exp (Real.log 9 * (-(1 / 2 : ℝ)))
      = (9 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_def_of_pos h9pos _).symm
  have hcos : Real.cos (-(10 * Real.log 9))
      = Real.cos (10 * Real.log 9) := Real.cos_neg _
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- `9^(1/2) ≤ 3` (mirror of the `sSCUT_sqrt8_le` root step; `9 ≤ 3^2`). -/
theorem sSCUT_sqrt9_le : (9 : ℝ) ^ (1 / 2 : ℝ) ≤ (3 : ℝ) := by
  have hpow : (9 : ℝ) ≤ ((3 : ℝ) ^ (2 : ℕ)) := by norm_num
  have hpow' : ((((9 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ))) = 9 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hle : ((((9 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ))) ≤ ((3 : ℝ) ^ (2 : ℕ)) := by
    rw [hpow']; exact hpow
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hle

/-- `1/3 ≤ r₉ = 9^(-1/2)` (inverse of the root step; mirror of
`sSCUT_rpow8_neg_ge`). -/
theorem sSCUT_rpow9_neg_ge : (1 / 3 : ℝ) ≤ (9 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hle := sSCUT_sqrt9_le
  have hpos : (0 : ℝ) < (9 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hneg : (9 : ℝ) ^ (-(1 / 2 : ℝ)) = (((9 : ℝ) ^ (1 / 2 : ℝ))⁻¹) := by
    rw [show (-(1 / 2 : ℝ)) = -((1 / 2 : ℝ)) by norm_num,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 9)]
  rw [hneg, show (1 / 3 : ℝ) = ((3 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num) hpos).mpr hle

/-- Signed cosine UPPER `cos(10*log 9) ≤ -(1/2)` (odd-multiple flip
`cos θ₉ = -cos δ₉` from the banked `δ₉ ∈ (-0.019, -0.018)` window +
quadratic lower `1 - x²/2 ≤ cos x`; mirror of
`sSCUT_cos10log8_le_neg_quarter`). -/
theorem sSCUT_cos10log9_le_neg_half :
    Real.cos (10 * Real.log 9) ≤ (-(1 / 2) : ℝ) := by
  have hδ := sSCUT_delta9_sharp_mem
  have key : Real.cos ((10 * Real.log 9 - 7 * Real.pi) + Real.pi
      + 2 * Real.pi + 2 * Real.pi + 2 * Real.pi)
      = -Real.cos (10 * Real.log 9 - 7 * Real.pi) := by
    rw [Real.cos_add_two_pi, Real.cos_add_two_pi, Real.cos_add_two_pi,
      Real.cos_add_pi]
  have e2 : (10 * Real.log 9 - 7 * Real.pi) + Real.pi
      + 2 * Real.pi + 2 * Real.pi + 2 * Real.pi = 10 * Real.log 9 := by
    ring
  rw [e2] at key
  have hcosδ : 1 - (0.019 : ℝ) ^ 2 / 2
      ≤ Real.cos (10 * Real.log 9 - 7 * Real.pi) := by
    have hq := Real.one_sub_sq_div_two_le_cos
      (x := 10 * Real.log 9 - 7 * Real.pi)
    have hsq : (10 * Real.log 9 - 7 * Real.pi) ^ 2 ≤ (0.019 : ℝ) ^ 2 := by
      have ha : (0 : ℝ) ≤ 0.019 - (10 * Real.log 9 - 7 * Real.pi) := by
        linarith [hδ.2]
      have hb : (0 : ℝ) ≤ (10 * Real.log 9 - 7 * Real.pi) + 0.019 := by
        linarith [hδ.1]
      have hprod := mul_nonneg ha hb
      have heq : (0.019 - (10 * Real.log 9 - 7 * Real.pi))
          * ((10 * Real.log 9 - 7 * Real.pi) + 0.019)
          = (0.019 : ℝ) ^ 2 - (10 * Real.log 9 - 7 * Real.pi) ^ 2 := by
        ring
      linarith
    linarith
  have hbase : (1 / 2 : ℝ) ≤ 1 - (0.019 : ℝ) ^ 2 / 2 := by norm_num
  rw [key]
  linarith

/-- Cpow signed UPPER `Re(9^{-sCut}) ≤ -(1/6)` (nonneg `r₉` × signed
cosine upper, then `r₉ ≥ 1/3`; mirror of `sSCUT_cpow8_Re_le_neg`). -/
theorem sSCUT_cpow9_Re_le_neg :
    ((((9 : ℝ)) : ℂ) ^ (-sSCUT)).re ≤ (-(1 / 6) : ℝ) := by
  rw [sSCUT_cpow9_neg_re]
  have hr0 : (0 : ℝ) ≤ (9 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr_lo := sSCUT_rpow9_neg_ge
  have hc := sSCUT_cos10log9_le_neg_half
  have hmul : (9 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 9)
      ≤ (9 : ℝ) ^ (-(1 / 2 : ℝ)) * (-(1 / 2)) :=
    mul_le_mul_of_nonneg_left hc hr0
  have h2 : (1 / 3 : ℝ) * (1 / 2) ≤ (9 : ℝ) ^ (-(1 / 2 : ℝ)) * (1 / 2) :=
    mul_le_mul_of_nonneg_right hr_lo (by norm_num)
  have heq : (1 / 3 : ℝ) * (1 / 2) = 1 / 6 := by norm_num
  have hsign : (9 : ℝ) ^ (-(1 / 2 : ℝ)) * (-(1 / 2))
      = -((9 : ℝ) ^ (-(1 / 2 : ℝ)) * (1 / 2)) := by ring
  linarith

/-- Eta bridge `eta₈ = 9^{-sCut}` (even `k`; mirror of
`sSCUT_eta6_eq_cpow7`). -/
theorem sSCUT_eta8_eq_cpow9 :
    etaDirichletTerm sSCUT 8 = ((((9 : ℝ)) : ℂ) ^ (-sSCUT)) := by
  have e : (8 + 1 : ℕ) = 9 := rfl
  have hcast : ((((8 + 1 : ℕ)) : ℂ)) = ((((9 : ℕ)) : ℂ)) := by rw [e]
  have hneg : (-1 : ℂ) ^ (8 : ℕ) = 1 := by norm_num
  have h9cast : ((((9 : ℕ)) : ℂ)) = ((((9 : ℝ)) : ℂ)) := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, h9cast, one_div, Complex.cpow_neg]

/-- Destructive eta UPPER (even `k = 8`): `Re(eta₈) ≤ -(1/6)` (direct
cpow signed upper, no sign flip; `k = 8` cannot grow the shard). -/
theorem sSCUT_eta8_Re_le_neg :
    (etaDirichletTerm sSCUT 8).re ≤ (-(1 / 6) : ℝ) := by
  have h := sSCUT_cpow9_Re_le_neg
  rw [sSCUT_eta8_eq_cpow9, sSCUT_cpow9_neg_re]
  rw [sSCUT_cpow9_neg_re] at h
  linarith

/-- No positive `Re₈` lock exists at any precision (`Re(eta₈) ≤ -1/6`,
so no `c > 0` can sit below it; mirror of `sSCUT_cpow3_Re_no_pos_lock`
at eta level — the `k = 8` floor is IMPOSSIBLE, honestly skipped). -/
theorem sSCUT_eta8_Re_no_pos_lock (c : ℝ) (hc : (0 : ℝ) < c) :
    ¬ (c ≤ (etaDirichletTerm sSCUT 8).re) := by
  intro h
  have hup := sSCUT_eta8_Re_le_neg
  linarith

/-- Honest S9-range assembly EXCLUDING `k = 8` (single-count correction).

Double-count verdict: REAL. `S₈ = ∑ k ∈ range 8` already contains indices
`k = 6, 7` single-counted in `sSCUT_S8_Re_ge_neg3529div1050`
(`-3529/1050 = 2/7 - 4 + 27/100 + 1/12`). Hence `sSCUT_S8_add_eta9_eta7_Re_ge`
(`:3247`) sums the multiset `{0,1,2,3,4,5,6,7,9,6}` (second copy of `k = 6`)
and `sSCUT_S8_add_eta9_eta7_eta8_Re_ge` (`:3268`) sums the multiset
`{0,1,2,3,4,5,6,7,9,6,7}` (second copies of `k = 6, 7`); their floors
`-3529/1050 + 0.15 + 0.27` and `-3529/1050 + 0.15 + 0.27 + 1/12 ≈ -2.858`
are multiset floors, NOT single-count `S₉` floors.

This theorem banks the corrected single-count floor: index multiset summed
exactly once is `{0,1,2,3,4,5,6,7,9}` (that is `S₈` for `k = 0..7` plus
`k = 9` only; `k = 8` honestly skipped per `sSCUT_eta8_Re_le_neg` /
`sSCUT_eta8_Re_no_pos_lock`; NO second copies of `k = 6, 7`). Value is the
`:3268` floor minus the double-counted `0.27 + 1/12`, i.e.
`-3529/1050 + 0.15` via `sSCUT_S8_add_eta9_Re_ge` + `sSCUT_rpow10_neg_ge_03`. -/
theorem sSCUT_S9_skip8_Re_ge :
    (-3529 / 1050 : ℝ) + 0.15 ≤
      ((∑ k ∈ Finset.range 8, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 9).re := by
  rw [Complex.add_re]
  have hS8e9 := sSCUT_S8_add_eta9_Re_ge
  have hr10 := sSCUT_rpow10_neg_ge_03
  have hr10div : (0.15 : ℝ) ≤ (10 : ℝ) ^ (-(1 / 2 : ℝ)) / 2 := by linarith [hr10]
  rw [Complex.add_re] at hS8e9
  linarith [hS8e9, hr10div]

/-- Corrected single-count shortfall vs the `21/10` bar
(`21/10 - (-3529/1050 + 0.15) = 11153/2100 ≈ 5.311`; replaces the
multiset gap `10411/2100` at `:3280`). -/
theorem sSCUT_S9_skip8_shortfall :
    ((21 / 10 : ℝ) - ((-3529 / 1050) + 0.15)) = (11153 / 2100 : ℝ) := by
  norm_num

/-- Tail-transfer assembly at sCut: single-count shard minus the `M = 2048`
tail (`S₉_skip8 - 7/10`; `slow - tail` shape vs the `21/10` bar; shard floor
banked at `sSCUT_S9_skip8_Re_ge`, tail numeral `7/10` banked at
`sSCUT_eta_tail_2048_le`). -/
theorem sSCUT_S9_skip8_tail_floor :
    (((-3529 / 1050 : ℝ) + 0.15) - 7 / 10) ≤
      ((((∑ k ∈ Finset.range 8, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 9).re) - 7 / 10) := by
  have h := sSCUT_S9_skip8_Re_ge
  linarith

/-- Exact gap of the tail-transfer assembly vs the `21/10` bar
(`21/10 - (((-3529/1050) + 0.15) - 7/10) = 12623/2100 ≈ 6.011`). -/
theorem sSCUT_S9_skip8_tail_shortfall :
    ((21 / 10 : ℝ) - (((-3529 / 1050 : ℝ) + 0.15) - 7 / 10)) =
      (12623 / 2100 : ℝ) := by
  norm_num

/-- N = 4096 next-rung need at sCut (SCUT18, honest gap, no force).

With the `M = 2048` tail the closed `hEnough` bar is `21/10`
(`sSCUT_hEnough_2048_threshold`); the banked single-count shard floor is
`F = -3529/1050 + 0.15` (`sSCUT_S9_skip8_Re_ge`, `k = 8` honestly skipped
per `sSCUT_eta8_Re_le_neg` / `sSCUT_eta8_Re_no_pos_lock`). Hence any
additional `Re` mass `E` from the remaining `k = 10..4095` range that would
lift the shard floor to the bar must satisfy `E ≥ 11153/2100 ≈ 5.311`
(the banked `sSCUT_S9_skip8_shortfall` numeral, restated conditionally). -/
theorem sSCUT_N4096_nextRung_need (E : ℝ)
    (h : ((-3529 / 1050 : ℝ) + 0.15) + E ≥ (21 / 10 : ℝ)) :
    E ≥ (11153 / 2100 : ℝ) := by
  have hgap : ((21 / 10 : ℝ) - ((-3529 / 1050) + 0.15)) = (11153 / 2100 : ℝ) :=
    sSCUT_S9_skip8_shortfall
  linarith

/-- Even one ideal `+1` rung cannot close the single-count gap
(`-3529/1050 + 0.15 + 1 < 21/10`): the next single term, at maximal ideal
allowance, leaves the shard floor strictly below the bar — so the N = 4096
slow leg needs many further rungs, not one. Pure arithmetic, no eta upper
claimed here. -/
theorem sSCUT_S9_skip8_plus_one_still_short :
    (((-3529 / 1050 : ℝ) + 0.15) + 1) < (21 / 10 : ℝ) := by
  norm_num

/-- Exact residual after one ideal `+1` rung
(`21/10 - ((-3529/1050) + 0.15 + 1) = 9053/2100 ≈ 4.311`). -/
theorem sSCUT_S9_skip8_plus_one_gap_eq :
    ((21 / 10 : ℝ) - (((-3529 / 1050 : ℝ) + 0.15) + 1)) =
      (9053 / 2100 : ℝ) := by
  norm_num

/-- Eta bridge `eta₁₀ = 11^{-sCut}` (even `k`; mirror of
`sSCUT_eta8_eq_cpow9`). -/
theorem sSCUT_eta10_eq_cpow11 :
    etaDirichletTerm sSCUT 10 = ((((11 : ℝ)) : ℂ) ^ (-sSCUT)) := by
  have e : (10 + 1 : ℕ) = 11 := rfl
  have hcast : ((((10 + 1 : ℕ)) : ℂ)) = ((((11 : ℕ)) : ℂ)) := by rw [e]
  have hneg : (-1 : ℂ) ^ (10 : ℕ) = 1 := by norm_num
  have h11cast : ((((11 : ℕ)) : ℂ)) = ((((11 : ℝ)) : ℂ)) := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, h11cast, one_div, Complex.cpow_neg]

/-- Conditional symbolic eta UPPER (even `k = 10`): `Re(eta₁₀) ≤ -(r₁₁/2)`
under the explicit `11^{-s}` signed-upper hypothesis `h11`.
Honest status: NO unconditional lock is banked here. The banked `:2625`
`sSCUT_cpow10_neg_Re_upper` is base-10 (`n = 10`, i.e. Lean index `9`) and
does NOT transfer to base-11 (`n = 11`, Lean index `10`); no `log 11`,
`cpow11`, or `r₁₁`-lower lemma is banked in this file (`:2161` records
`n = 11` BLOCKED, `r11` grep empty). `r₁₁` stays symbolic. -/
theorem sSCUT_eta10_Re_le_neg
    (h11 : ((((11 : ℝ)) : ℂ) ^ (-sSCUT)).re ≤ -((11 : ℝ) ^ (-(1 / 2 : ℝ)) / 2)) :
    (etaDirichletTerm sSCUT 10).re ≤ -((11 : ℝ) ^ (-(1 / 2 : ℝ)) / 2) := by
  rw [sSCUT_eta10_eq_cpow11]
  exact h11

/-- Conditional no-positive-`Re₁₀` lock: under the same explicit `h11`
hypothesis no `c > 0` can sit below `Re(eta₁₀)` (mirror of
`sSCUT_eta8_Re_no_pos_lock` at eta level; conditional only — no
unconditional `k = 10` impossibility is banked). -/
theorem sSCUT_eta10_Re_no_pos_lock (c : ℝ) (hc : (0 : ℝ) < c)
    (h11 : ((((11 : ℝ)) : ℂ) ^ (-sSCUT)).re ≤ -((11 : ℝ) ^ (-(1 / 2 : ℝ)) / 2)) :
    ¬ (c ≤ (etaDirichletTerm sSCUT 10).re) := by
  intro h
  have hup := sSCUT_eta10_Re_le_neg h11
  have hr0 : (0 : ℝ) ≤ (11 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  linarith

/-- Composite log bridge `log 11 = log 10 + log (11/10)` (`11 = 10·(11/10)`
via `Real.log_mul`; mirror of `sSCUT_log_ten_eq` / `CS_log_six_eq`;
first link of the base-11 chain for `k = 10`). -/
theorem sSCUT_log_eleven_eq :
    Real.log 11 = Real.log 10 + Real.log (11 / 10 : ℝ) := by
  have h11 : (10 : ℝ) * (11 / 10) = 11 := by norm_num
  have h := Real.log_mul (show (10 : ℝ) ≠ 0 by norm_num)
    (show (11 / 10 : ℝ) ≠ 0 by norm_num)
  rw [h11] at h
  linarith

/-- `log 11` upper (`log 11 ≤ 2.4025850934` from `sSCUT_log_ten_le` +
`log (11/10) ≤ 1/10`; `CS_log_three_le` pattern via
`Real.log_le_sub_one_of_pos`). -/
theorem sSCUT_log_eleven_le : Real.log 11 ≤ (2.4025850934 : ℝ) := by
  have h11 := sSCUT_log_eleven_eq
  have h10 := sSCUT_log_ten_le
  have hub : Real.log (11 / 10 : ℝ) ≤ (1 / 10 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 11 / 10)
    have he : (11 / 10 : ℝ) - 1 = (1 / 10 : ℝ) := by norm_num
    linarith
  have c : (2.3025850934 : ℝ) + 1 / 10 = 2.4025850934 := by norm_num
  linarith

/-- `log 11` lower (`2.3934941835 ≤ log 11` from `sSCUT_log_ten_ge` +
`log (11/10) ≥ 1/11`; `CS_log_three_ge` pattern via `log (10/11) ≤ -1/11`
and `log (11/10) = -log (10/11)`). -/
theorem sSCUT_log_eleven_ge : (2.3934941835 : ℝ) ≤ Real.log 11 := by
  have h11 := sSCUT_log_eleven_eq
  have h10 := sSCUT_log_ten_ge
  have hub : Real.log (10 / 11 : ℝ) ≤ (-1 / 11 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10 / 11)
    have he : (10 / 11 : ℝ) - 1 = (-1 / 11 : ℝ) := by norm_num
    linarith
  have hinv : Real.log (11 / 10 : ℝ) = -Real.log (10 / 11 : ℝ) := by
    have heq : (11 / 10 : ℝ) = (10 / 11 : ℝ)⁻¹ := by rw [inv_div]
    rw [heq, Real.log_inv]
  have hfin : (2.3934941835 : ℝ) ≤ 2.3025850926 + 1 / 11 := by norm_num
  rw [h11, hinv]
  linarith

/-- Phase window `θ₁₁ = 10*log 11 ∈ [23.934941835, 24.025850934]`
(via banked `sSCUT_log_eleven_ge/le` + `*10`; mirror of
`sSCUT_theta10_sharp_mem`; non-strict since the `log 11` inputs are `≤`). -/
theorem sSCUT_theta11_mem :
    (23.934941835 : ℝ) ≤ 10 * Real.log 11 ∧
    10 * Real.log 11 ≤ (24.025850934 : ℝ) := by
  have hge := sSCUT_log_eleven_ge
  have hle := sSCUT_log_eleven_le
  have hmul_lo := mul_le_mul_of_nonneg_left hge (by norm_num : (0 : ℝ) ≤ 10)
  have hmul_hi := mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 10)
  have c1 : (10 : ℝ) * 2.3934941835 = 23.934941835 := by norm_num
  have c2 : (10 : ℝ) * 2.4025850934 = 24.025850934 := by norm_num
  constructor <;> linarith

/-- Exact width of the `θ₁₁` window (`0.090909099`). -/
theorem sSCUT_theta11_width_eq :
    (24.025850934 : ℝ) - 23.934941835 = (0.090909099 : ℝ) := by
  norm_num

/-- Reduced phase `δ₁₁' = θ₁₁ - 7π ∈ (1.943741835, 2.035350934)` (nearest
odd-multiple anchor: `7π ≈ 21.99` vs `9π ≈ 28.27`; `θ₁₁ ≈ 24.0` so `7π`
is nearest; strict since `Real.pi_gt_d4/lt_d4` are strict; mirror of
`sSCUT_delta10p_sharp_mem`). -/
theorem sSCUT_delta11p_mem :
    (1.943741835 : ℝ) < 10 * Real.log 11 - 7 * Real.pi ∧
    10 * Real.log 11 - 7 * Real.pi < (2.035350934 : ℝ) := by
  have hth := sSCUT_theta11_mem
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  constructor <;> linarith

/-- Exact width of the `δ₁₁'` window (`0.091609099`). -/
theorem sSCUT_delta11_width_eq :
    (2.035350934 : ℝ) - 1.943741835 = (0.091609099 : ℝ) := by
  norm_num

/-- Window-gap verdict (honest, too-wide): the `δ₁₁'` window spans more than
`0.09`, so it cannot fit any `±0.02` close (`0.04` span); moreover
`|δ₁₁'| ≥ 1.94 makes the quadratic floor `1 - x²/2` negative, so the
`δ₉`-style `cos ≤ -1/2` signed upper does NOT close — filed as gap, not bound. -/
theorem sSCUT_delta11_window_gap :
    (0.09 : ℝ) < (2.035350934 : ℝ) - 1.943741835 := by
  norm_num

/-- Reduced phase `δ₁₁ = θ₁₁ - 8π ∈ (-1.198, -1.106)` (even-multiple anchor:
`8π ≈ 25.13` is nearer than `7π ≈ 21.99`; strict via `Real.pi_gt_d4/lt_d4`;
mirror of `sSCUT_delta11p_mem`). -/
theorem sSCUT_delta11_even_mem :
    (-1.198 : ℝ) < 10 * Real.log 11 - 8 * Real.pi ∧
    10 * Real.log 11 - 8 * Real.pi < (-1.106 : ℝ) := by
  have hth := sSCUT_theta11_mem
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  constructor <;> linarith

/-- Signed cosine LOWER `7/25 ≤ cos(10*log 11)` (quadrant-IV `δ₁₁` via the
even-multiple strip `cos θ₁₁ = cos δ₁₁` + quadratic lower on `|δ₁₁| ≤ 1.2`). -/
theorem sSCUT_cos10log11_ge :
    (7 / 25 : ℝ) ≤ Real.cos (10 * Real.log 11) := by
  have hδ := sSCUT_delta11_even_mem
  set y : ℝ := 10 * Real.log 11 - 8 * Real.pi with hy_def
  have hy_lo : (-1.198 : ℝ) < y := by rw [hy_def]; linarith [hδ.1]
  have hy_hi : y < (-1.106 : ℝ) := by rw [hy_def]; linarith [hδ.2]
  have hsq : y ^ 2 ≤ (1.2 : ℝ) ^ 2 := by
    have ha : (0 : ℝ) ≤ 1.2 - y := by linarith [hy_hi]
    have hb : (0 : ℝ) ≤ y + 1.2 := by linarith [hy_lo]
    have hprod := mul_nonneg ha hb
    have heq : (1.2 - y) * (y + 1.2) = (1.2 : ℝ) ^ 2 - y ^ 2 := by ring
    linarith
  have hcos_lo := Real.one_sub_sq_div_two_le_cos (x := y)
  have hnum : (7 / 25 : ℝ) ≤ 1 - (1.2 : ℝ) ^ 2 / 2 := by norm_num
  have hcosy : (7 / 25 : ℝ) ≤ Real.cos y := by
    have hle : 1 - (1.2 : ℝ) ^ 2 / 2 ≤ 1 - y ^ 2 / 2 := by linarith [hsq]
    linarith [hcos_lo, hle, hnum]
  have hper : Real.cos (10 * Real.log 11 - 8 * Real.pi)
      = Real.cos (10 * Real.log 11) := by
    have h1 := Real.cos_sub_two_pi (10 * Real.log 11)
    have h2 := Real.cos_sub_two_pi (10 * Real.log 11 - 2 * Real.pi)
    have h3 := Real.cos_sub_two_pi
      ((10 * Real.log 11 - 2 * Real.pi) - 2 * Real.pi)
    have h4 := Real.cos_sub_two_pi
      (((10 * Real.log 11 - 2 * Real.pi) - 2 * Real.pi) - 2 * Real.pi)
    have e4 : 10 * Real.log 11 - 8 * Real.pi
        = (((10 * Real.log 11 - 2 * Real.pi) - 2 * Real.pi) - 2 * Real.pi)
          - 2 * Real.pi := by ring
    calc Real.cos (10 * Real.log 11 - 8 * Real.pi)
        = Real.cos ((((10 * Real.log 11 - 2 * Real.pi) - 2 * Real.pi)
          - 2 * Real.pi) - 2 * Real.pi) := by rw [e4]
      _ = Real.cos (((10 * Real.log 11 - 2 * Real.pi) - 2 * Real.pi)
          - 2 * Real.pi) := h4
      _ = Real.cos ((10 * Real.log 11 - 2 * Real.pi) - 2 * Real.pi) := h3
      _ = Real.cos (10 * Real.log 11 - 2 * Real.pi) := h2
      _ = Real.cos (10 * Real.log 11) := h1
  rw [hy_def, hper] at hcosy
  exact hcosy

/-- `11^(1/2) ≤ 10/3` (tighter honest root step; `11 ≤ (10/3)^2 = 100/9`;
mirror of `sSCUT_rpow10_neg_ge_03` inner step at `:3224`). -/
theorem sSCUT_sqrt11_le : (11 : ℝ) ^ (1 / 2 : ℝ) ≤ (10 / 3 : ℝ) := by
  have hpow : (11 : ℝ) ≤ ((10 / 3 : ℝ) ^ (2 : ℕ)) := by norm_num
  have hpow' : ((((11 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ))) = 11 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hle : ((((11 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ))) ≤ ((10 / 3 : ℝ) ^ (2 : ℕ)) := by
    rw [hpow']
    exact hpow
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hle

/-- `0.3 ≤ r₁₁ = 11^(-1/2)` (inverse of `sSCUT_sqrt11_le`; mirror of
`sSCUT_rpow10_neg_ge_03` at `:3223`). -/
theorem sSCUT_rpow11_neg_ge : (0.3 : ℝ) ≤ (11 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hle := sSCUT_sqrt11_le
  have hpos : (0 : ℝ) < (11 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hneg : (11 : ℝ) ^ (-(1 / 2 : ℝ)) = (((11 : ℝ) ^ (1 / 2 : ℝ))⁻¹) := by
    rw [show (-(1 / 2 : ℝ)) = -((1 / 2 : ℝ)) by norm_num,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 11)]
  rw [hneg, show (0.3 : ℝ) = ((10 / 3 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num) hpos).mpr hle

/-- Cpow real-part split for `11^{-s}` at sCut (mirror of
`sSCUT_cpow9_neg_re`). -/
theorem sSCUT_cpow11_neg_re : ((((11 : ℝ)) : ℂ) ^ (-sSCUT)).re
    = (11 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 11) := by
  have h11pos : (0 : ℝ) < 11 := by norm_num
  have hxC : ((11 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h11pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((11 : ℝ) : ℂ) = (((Real.log 11 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h11pos)).symm
  rw [hlog]
  have hre_w : (-sSCUT).re = (-(1 / 2 : ℝ)) := by
    have e : (-sSCUT).re = -(sSCUT.re) := rfl
    rw [e, sSCUT_re]
  have him_w : (-sSCUT).im = (-10 : ℝ) := by
    have e : (-sSCUT).im = -(sSCUT.im) := rfl
    rw [e, sSCUT_im]
  have hzre : ((((Real.log 11 : ℝ)) : ℂ)).re = Real.log 11 := Complex.ofReal_re _
  have hzim : ((((Real.log 11 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 11 : ℝ)) : ℂ) * (-sSCUT)).re
      = Real.log 11 * (-(1 / 2 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 11 : ℝ)) : ℂ) * (-sSCUT)).im
      = -(10 * Real.log 11) := by
    rw [Complex.mul_im, hzre, hzim, hre_w, him_w]
    ring
  have hexp : Real.exp (Real.log 11 * (-(1 / 2 : ℝ)))
      = (11 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_def_of_pos h11pos _).symm
  have hcos : Real.cos (-(10 * Real.log 11))
      = Real.cos (10 * Real.log 11) := Real.cos_neg _
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- Cpow signed LOWER `21/250 ≤ Re(11^{-sCut})` (`r₁₁ ≥ 0.3` × cosine
`≥ 7/25`, via two one-sided multiplies; mirror of `sSCUT_cpow7_Re_ge`). -/
theorem sSCUT_cpow11_Re_ge :
    (21 / 250 : ℝ) ≤ ((((11 : ℝ)) : ℂ) ^ (-sSCUT)).re := by
  rw [sSCUT_cpow11_neg_re]
  have hr_lo := sSCUT_rpow11_neg_ge
  have hr0 : (0 : ℝ) ≤ (11 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hc_lo := sSCUT_cos10log11_ge
  have h1 : (0.3 : ℝ) * (7 / 25)
      ≤ (11 : ℝ) ^ (-(1 / 2 : ℝ)) * (7 / 25) :=
    mul_le_mul_of_nonneg_right hr_lo (by norm_num)
  have h2 : (11 : ℝ) ^ (-(1 / 2 : ℝ)) * (7 / 25)
      ≤ (11 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 11) :=
    mul_le_mul_of_nonneg_left hc_lo hr0
  have heq : (0.3 : ℝ) * (7 / 25) = 21 / 250 := by norm_num
  linarith

/-- Parity payoff (even `k = 10`): `Re(eta₁₀) ≥ +21/250` (direct cpow signed
lower, no sign flip; mirror of `sSCUT_eta6_Re_ge`). -/
theorem sSCUT_eta10_Re_ge : (21 / 250 : ℝ) ≤ (etaDirichletTerm sSCUT 10).re := by
  have h := sSCUT_cpow11_Re_ge
  rw [sSCUT_eta10_eq_cpow11, sSCUT_cpow11_neg_re]
  rw [sSCUT_cpow11_neg_re] at h
  linarith

/-- Honest single-count shard floor with the `t₁₀` gain
(`-3529/1050 + 0.15 + 21/250 ≤ Re(S₈ + eta₉ + eta₁₀)`; base
`sSCUT_S9_skip8_Re_ge` plus `sSCUT_eta10_Re_ge`; index multiset summed
exactly once is `{0,1,2,3,4,5,6,7,9,10}`, `k = 8` honestly skipped). -/
theorem sSCUT_S9_skip8_add_eta10_Re_ge :
    (-3529 / 1050 : ℝ) + 0.15 + (21 / 250) ≤
      ((∑ k ∈ Finset.range 8, etaDirichletTerm sSCUT k)
        + etaDirichletTerm sSCUT 9 + etaDirichletTerm sSCUT 10).re := by
  rw [Complex.add_re]
  have hbase := sSCUT_S9_skip8_Re_ge
  have h10 := sSCUT_eta10_Re_ge
  linarith

/-- Updated single-count shortfall vs the `21/10` bar with the `t₁₀` gain
(`21/10 - (-3529/1050 + 0.15 + 21/250) = 54883/10500 ≈ 5.228`; replaces
`11153/2100` at `sSCUT_S9_skip8_shortfall`). -/
theorem sSCUT_S9_skip8_eta10_shortfall :
    ((21 / 10 : ℝ) - ((-3529 / 1050) + 0.15 + (21 / 250))) =
      (54883 / 10500 : ℝ) := by
  norm_num

/-- Composite log bridge `log 12 = log 11 + log (12/11)` (`12 = 11·(12/11)`
via `Real.log_mul`; mirror of `sSCUT_log_eleven_eq` at `:3552`;
first link of the incremental base-12 chain for `k = 11`). -/
theorem sSCUT_log_twelve_via_eleven_eq :
    Real.log 12 = Real.log 11 + Real.log (12 / 11 : ℝ) := by
  have h12 : (11 : ℝ) * (12 / 11) = 12 := by norm_num
  have h := Real.log_mul (show (11 : ℝ) ≠ 0 by norm_num)
    (show (12 / 11 : ℝ) ≠ 0 by norm_num)
  rw [h12] at h
  linarith

/-- `log 12` upper (`log 12 ≤ 2.4934941844` from `sSCUT_log_eleven_le` +
`log (12/11) ≤ 1/11`; mirror of `sSCUT_log_eleven_le` at `:3563` with `x = 1/11`
via `Real.log_le_sub_one_of_pos`). -/
theorem sSCUT_log_twelve_le : Real.log 12 ≤ (2.4934941844 : ℝ) := by
  have h12 := sSCUT_log_twelve_via_eleven_eq
  have h11 := sSCUT_log_eleven_le
  have hub : Real.log (12 / 11 : ℝ) ≤ (1 / 11 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 12 / 11)
    have he : (12 / 11 : ℝ) - 1 = (1 / 11 : ℝ) := by norm_num
    linarith
  have hfin : (2.4025850934 : ℝ) + 1 / 11 ≤ (2.4934941844 : ℝ) := by norm_num
  linarith

/-- `log 12` lower (`2.4768275168 ≤ log 12` from `sSCUT_log_eleven_ge` +
`log (12/11) ≥ 1/12`; mirror of `sSCUT_log_eleven_ge` at `:3576` with `x = 1/11`
via `log (11/12) ≤ -1/12` and `log (12/11) = -log (11/12)`). -/
theorem sSCUT_log_twelve_ge : (2.4768275168 : ℝ) ≤ Real.log 12 := by
  have h12 := sSCUT_log_twelve_via_eleven_eq
  have h11 := sSCUT_log_eleven_ge
  have hub : Real.log (11 / 12 : ℝ) ≤ (-1 / 12 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 11 / 12)
    have he : (11 / 12 : ℝ) - 1 = (-1 / 12 : ℝ) := by norm_num
    linarith
  have hinv : Real.log (12 / 11 : ℝ) = -Real.log (11 / 12 : ℝ) := by
    have heq : (12 / 11 : ℝ) = (11 / 12 : ℝ)⁻¹ := by rw [inv_div]
    rw [heq, Real.log_inv]
  have hfin : (2.4768275168 : ℝ) ≤ 2.3934941835 + 1 / 12 := by norm_num
  rw [h12, hinv]
  linarith

/-- Phase window `θ₁₂ = 10*log 12 ∈ [24.768275168, 24.934941844]`
(via banked `sSCUT_log_twelve_ge/le` + `*10`; phase shape `10*log 12`
confirmed against the cpow mirrors `sSCUT_cpow9_neg_re` (`:3287`,
`cos (10*log 9)` for base 9) and `sSCUT_cpow11_neg_re` (`:3714`,
`cos (10*log 11)` for base 11): multiplier is `t = 10`, not `11`;
non-strict since the `log 12` inputs are `≤`). -/
theorem sSCUT_theta12_wide_mem :
    (24.768275168 : ℝ) ≤ 10 * Real.log 12 ∧
    10 * Real.log 12 ≤ (24.934941844 : ℝ) := by
  have hge := sSCUT_log_twelve_ge
  have hle := sSCUT_log_twelve_le
  have hmul_lo := mul_le_mul_of_nonneg_left hge (by norm_num : (0 : ℝ) ≤ 10)
  have hmul_hi := mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 10)
  have c1 : (10 : ℝ) * 2.4768275168 = 24.768275168 := by norm_num
  have c2 : (10 : ℝ) * 2.4934941844 = 24.934941844 := by norm_num
  constructor <;> linarith

/-- Exact width of the wide `θ₁₂` window (`0.166666676`). -/
theorem sSCUT_theta12_wide_width_eq :
    (24.934941844 : ℝ) - 24.768275168 = (0.166666676 : ℝ) := by
  norm_num

/-- Reduced phase `δ₁₂' = θ₁₂ - 7π ∈ (2.777075168, 2.944441844)` (nearest
odd-multiple anchor: `7π ≈ 21.99` vs `9π ≈ 28.27`; `θ₁₂ ≈ 24.77-24.93`
so `7π` is nearest; strict since `Real.pi_gt_d4/lt_d4` are strict; mirror of
`sSCUT_delta11p_mem`). -/
theorem sSCUT_delta12p_wide_mem :
    (2.777075168 : ℝ) < 10 * Real.log 12 - 7 * Real.pi ∧
    10 * Real.log 12 - 7 * Real.pi < (2.944441844 : ℝ) := by
  have hth := sSCUT_theta12_wide_mem
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  constructor <;> linarith

/-- Exact width of the wide `δ₁₂'` window (`0.167366676`). -/
theorem sSCUT_delta12_wide_width_eq :
    (2.944441844 : ℝ) - 2.777075168 = (0.167366676 : ℝ) := by
  norm_num

/-- Window-gap verdict (honest, too-wide): the wide `δ₁₂'` window spans more
than `0.09`, so it cannot fit any `±0.02` close (`0.04` span); the
`θ₁₂` width `0.166666676` is an order of magnitude above the sharp
`n = 12` recipe width, so no `cos (10*log 12) ≤ -1/2` signed upper is
banked here — filed as gap, not bound (mirror of
`sSCUT_delta11_window_gap`; odd `k = 11` negation-flip needs the cosine
upper, which does NOT close on this wide window). -/
theorem sSCUT_delta12_wide_window_gap :
    (0.09 : ℝ) < (2.944441844 : ℝ) - 2.777075168 := by
  norm_num

/-- Sharp signed cosine LOWER `19/20 ≤ cos(10*log 12)` (even-multiple strip
`cos θ₁₂ = cos δ₁₂` from the banked sharp `δ₁₂ ∈ (-0.2838, -0.2829)` window
`sSCUT_delta12_sharp_mem` (`:2287`) + quadratic lower `1 - x²/2 ≤ cos x` on
`|δ₁₂| ≤ 0.2838`; mirror of `sSCUT_cos10log11_ge`; the `k = 8`-style negative
upper `cos ≤ -1/4` (`:3349`) does NOT close here since `cos ≈ +0.96`). -/
theorem sSCUT_cos10log12_ge :
    (19 / 20 : ℝ) ≤ Real.cos (10 * Real.log 12) := by
  have hδ := sSCUT_delta12_sharp_mem
  set y : ℝ := 10 * Real.log 12 - 8 * Real.pi with hy_def
  have hy_lo : (-0.2838 : ℝ) < y := by rw [hy_def]; linarith [hδ.1]
  have hy_hi : y < (-0.2829 : ℝ) := by rw [hy_def]; linarith [hδ.2]
  have hsq : y ^ 2 ≤ (0.2838 : ℝ) ^ 2 := by
    have ha : (0 : ℝ) ≤ 0.2838 - y := by linarith [hy_hi]
    have hb : (0 : ℝ) ≤ y + 0.2838 := by linarith [hy_lo]
    have hprod := mul_nonneg ha hb
    have heq : (0.2838 - y) * (y + 0.2838) = (0.2838 : ℝ) ^ 2 - y ^ 2 := by
      ring
    linarith
  have hcos_lo := Real.one_sub_sq_div_two_le_cos (x := y)
  have hnum : (19 / 20 : ℝ) ≤ 1 - (0.2838 : ℝ) ^ 2 / 2 := by norm_num
  have hcosy : (19 / 20 : ℝ) ≤ Real.cos y := by
    have hle : 1 - (0.2838 : ℝ) ^ 2 / 2 ≤ 1 - y ^ 2 / 2 := by linarith [hsq]
    linarith [hcos_lo, hle, hnum]
  have hper : Real.cos (10 * Real.log 12 - 8 * Real.pi)
      = Real.cos (10 * Real.log 12) := by
    have h1 := Real.cos_sub_two_pi (10 * Real.log 12)
    have h2 := Real.cos_sub_two_pi (10 * Real.log 12 - 2 * Real.pi)
    have h3 := Real.cos_sub_two_pi
      ((10 * Real.log 12 - 2 * Real.pi) - 2 * Real.pi)
    have h4 := Real.cos_sub_two_pi
      (((10 * Real.log 12 - 2 * Real.pi) - 2 * Real.pi) - 2 * Real.pi)
    have e4 : 10 * Real.log 12 - 8 * Real.pi
        = (((10 * Real.log 12 - 2 * Real.pi) - 2 * Real.pi) - 2 * Real.pi)
          - 2 * Real.pi := by ring
    calc Real.cos (10 * Real.log 12 - 8 * Real.pi)
        = Real.cos ((((10 * Real.log 12 - 2 * Real.pi) - 2 * Real.pi)
          - 2 * Real.pi) - 2 * Real.pi) := by rw [e4]
      _ = Real.cos (((10 * Real.log 12 - 2 * Real.pi) - 2 * Real.pi)
          - 2 * Real.pi) := h4
      _ = Real.cos ((10 * Real.log 12 - 2 * Real.pi) - 2 * Real.pi) := h3
      _ = Real.cos (10 * Real.log 12 - 2 * Real.pi) := h2
      _ = Real.cos (10 * Real.log 12) := h1
  rw [hy_def, hper] at hcosy
  exact hcosy

/-- The `k = 8`-style negative cosine upper does NOT close on the sharp
`n = 12` window: `¬ (cos(10*log 12) ≤ -1/4)` (sharp lower `≥ 19/20`
contradicts any negative upper; filed as gap, not bound — mirror of
`sSCUT_delta12_wide_window_gap` at cosine level). -/
theorem sSCUT_cos10log12_no_neg_upper_gap :
    ¬ (Real.cos (10 * Real.log 12) ≤ (-(1 / 4) : ℝ)) := by
  intro h
  have hlo := sSCUT_cos10log12_ge
  linarith

/-- Cpow real-part split for `12^{-s}` at sCut (mirror of
`sSCUT_cpow11_neg_re`). -/
theorem sSCUT_cpow12_neg_re : ((((12 : ℝ)) : ℂ) ^ (-sSCUT)).re
    = (12 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 12) := by
  have h12pos : (0 : ℝ) < 12 := by norm_num
  have hxC : ((12 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h12pos)
  rw [Complex.cpow_def_of_ne_zero hxC]
  have hlog : Complex.log ((12 : ℝ) : ℂ) = (((Real.log 12 : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt h12pos)).symm
  rw [hlog]
  have hre_w : (-sSCUT).re = (-(1 / 2 : ℝ)) := by
    have e : (-sSCUT).re = -(sSCUT.re) := rfl
    rw [e, sSCUT_re]
  have him_w : (-sSCUT).im = (-10 : ℝ) := by
    have e : (-sSCUT).im = -(sSCUT.im) := rfl
    rw [e, sSCUT_im]
  have hzre : ((((Real.log 12 : ℝ)) : ℂ)).re = Real.log 12 := Complex.ofReal_re _
  have hzim : ((((Real.log 12 : ℝ)) : ℂ)).im = 0 := Complex.ofReal_im _
  have harg_re : ((((Real.log 12 : ℝ)) : ℂ) * (-sSCUT)).re
      = Real.log 12 * (-(1 / 2 : ℝ)) := by
    rw [Complex.mul_re, hzre, hzim, hre_w]
    ring
  have harg_im : ((((Real.log 12 : ℝ)) : ℂ) * (-sSCUT)).im
      = -(10 * Real.log 12) := by
    rw [Complex.mul_im, hzre, hzim, hre_w, him_w]
    ring
  have hexp : Real.exp (Real.log 12 * (-(1 / 2 : ℝ)))
      = (12 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_def_of_pos h12pos _).symm
  have hcos : Real.cos (-(10 * Real.log 12))
      = Real.cos (10 * Real.log 12) := Real.cos_neg _
  rw [Complex.exp_re, harg_re, harg_im, hexp, hcos]

/-- `12^(1/2) ≤ 7/2` (honest root step; `12 ≤ (7/2)^2 = 49/4`;
mirror of `sSCUT_sqrt11_le`). -/
theorem sSCUT_sqrt12_le : (12 : ℝ) ^ (1 / 2 : ℝ) ≤ (7 / 2 : ℝ) := by
  have hpow : (12 : ℝ) ≤ (((7 / 2 : ℝ) ^ (2 : ℕ))) := by norm_num
  have hpow' : ((((12 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ))) = 12 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e : ((1 / 2 : ℝ)) * ((((2 : ℕ)) : ℝ)) = 1 := by norm_num
    rw [e, Real.rpow_one]
  have hle : ((((12 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ))) ≤ (((7 / 2 : ℝ) ^ (2 : ℕ))) := by
    rw [hpow']
    exact hpow
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hle

/-- `2/7 ≤ r₁₂ = 12^(-1/2)` (inverse of `sSCUT_sqrt12_le`; mirror of
`sSCUT_rpow11_neg_ge`). -/
theorem sSCUT_rpow12_neg_ge : (2 / 7 : ℝ) ≤ (12 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hle := sSCUT_sqrt12_le
  have hpos : (0 : ℝ) < (12 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hneg : (12 : ℝ) ^ (-(1 / 2 : ℝ)) = (((12 : ℝ) ^ (1 / 2 : ℝ))⁻¹) := by
    rw [show (-(1 / 2 : ℝ)) = -((1 / 2 : ℝ)) by norm_num,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 12)]
  rw [hneg, show (2 / 7 : ℝ) = ((7 / 2 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num) hpos).mpr hle

/-- Cpow signed LOWER `19/70 ≤ Re(12^{-sCut})` (`r₁₂ ≥ 2/7` × cosine
`≥ 19/20`, via two one-sided multiplies; mirror of `sSCUT_cpow11_Re_ge`
at `:3750`; the positive floor whose negation is the `eta₁₁` destructive
upper). -/
theorem sSCUT_cpow12_Re_ge :
    (19 / 70 : ℝ) ≤ ((((12 : ℝ)) : ℂ) ^ (-sSCUT)).re := by
  rw [sSCUT_cpow12_neg_re]
  have hr_lo := sSCUT_rpow12_neg_ge
  have hr0 : (0 : ℝ) ≤ (12 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hc_lo := sSCUT_cos10log12_ge
  have h1 : (2 / 7 : ℝ) * (19 / 20)
      ≤ (12 : ℝ) ^ (-(1 / 2 : ℝ)) * (19 / 20) :=
    mul_le_mul_of_nonneg_right hr_lo (by norm_num)
  have h2 : (12 : ℝ) ^ (-(1 / 2 : ℝ)) * (19 / 20)
      ≤ (12 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 12) :=
    mul_le_mul_of_nonneg_left hc_lo hr0
  have heq : (2 / 7 : ℝ) * (19 / 20) = 19 / 70 := by norm_num
  linarith

/-- `12^(-1/2) ≤ 1` (trivial rpow decay upper; mirror of
`sSCUT_rpow10_neg_le_one`). -/
theorem sSCUT_rpow12_neg_le_one : (12 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
  have h : (12 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (12 : ℝ) ^ (0 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [Real.rpow_zero] at h
  exact h

/-- Cpow positive-cap UPPER `Re(12^{-sCut}) ≤ 1` (trivial cosine upper
`cos ≤ 1` × decay `r₁₂ ≤ 1`; honest `+cap`, not sharp — the sharp window
gives the LOWER `≥ 19/70` above, whose negation is destructive). -/
theorem sSCUT_cpow12_Re_le_pos_cap :
    ((((12 : ℝ)) : ℂ) ^ (-sSCUT)).re ≤ (1 : ℝ) := by
  rw [sSCUT_cpow12_neg_re]
  have hr0 : (0 : ℝ) ≤ (12 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr_hi := sSCUT_rpow12_neg_le_one
  have hcos_hi : Real.cos (10 * Real.log 12) ≤ 1 := Real.cos_le_one _
  have hmul : (12 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (10 * Real.log 12)
      ≤ (12 : ℝ) ^ (-(1 / 2 : ℝ)) * 1 :=
    mul_le_mul_of_nonneg_left hcos_hi hr0
  linarith

/-- Eta bridge `eta₁₁ = -(12^{-sCut})` (odd `k`; `Complex.cpow_neg` turns
`(12^s)⁻¹` into `12^{-s}`; mirror of `sSCUT_eta9_eq_neg_cpow10`). -/
theorem sSCUT_eta11_eq_neg_cpow12 :
    etaDirichletTerm sSCUT 11 = -((((12 : ℝ)) : ℂ) ^ (-sSCUT)) := by
  have e : (11 + 1 : ℕ) = 12 := rfl
  have hcast : ((((11 + 1 : ℕ)) : ℂ)) = ((((12 : ℕ)) : ℂ)) := by rw [e]
  have hneg : (-1 : ℂ) ^ (11 : ℕ) = -1 := by norm_num
  have h12cast : ((((12 : ℕ)) : ℂ)) = ((((12 : ℝ)) : ℂ)) := by norm_num
  unfold etaDirichletTerm
  rw [hcast, hneg, h12cast, neg_div, one_div, Complex.cpow_neg]

/-- Destructive eta UPPER (odd `k = 11`): `Re(eta₁₁) ≤ -(19/70)` (negated
cpow signed lower `sSCUT_cpow12_Re_ge`; odd negation flips the positive
floor to a negative ceiling; mirror of `sSCUT_eta8_Re_le_neg` at `:3413`
with the `sSCUT_eta7` flip direction). -/
theorem sSCUT_eta11_Re_le_neg :
    (etaDirichletTerm sSCUT 11).re ≤ (-(19 / 70) : ℝ) := by
  have h := sSCUT_cpow12_Re_ge
  rw [sSCUT_eta11_eq_neg_cpow12, Complex.neg_re, sSCUT_cpow12_neg_re]
  rw [sSCUT_cpow12_neg_re] at h
  linarith

/-- No positive `Re₁₁` lock exists at any precision (`Re(eta₁₁) ≤ -19/70`,
so no `c > 0` can sit below it; mirror of `sSCUT_eta8_Re_no_pos_lock`
at `:3423` — the `k = 11` floor is IMPOSSIBLE, honestly skipped). -/
theorem sSCUT_eta11_Re_no_pos_lock (c : ℝ) (hc : (0 : ℝ) < c) :
    ¬ (c ≤ (etaDirichletTerm sSCUT 11).re) := by
  intro h
  have hup := sSCUT_eta11_Re_le_neg
  linarith

/-- Composite log bridge `log 13 = log 12 + log (13/12)` (`13 = 12·(13/12)`
via `Real.log_mul`; mirror of `sSCUT_log_twelve_via_eleven_eq`;
grepped base bridges: `sSCUT_log_twelve_via_eleven_eq` and `sSCUT_log_eleven_eq`
both banked — tighter ratio `13/12` (`x = 1/12`) picked over `13/11`
(`x = 2/11`); first link of the incremental base-13 chain for `k = 12`). -/
theorem sSCUT_log_thirteen_via_twelve_eq :
    Real.log 13 = Real.log 12 + Real.log (13 / 12 : ℝ) := by
  have h13 : (12 : ℝ) * (13 / 12) = 13 := by norm_num
  have h := Real.log_mul (show (12 : ℝ) ≠ 0 by norm_num)
    (show (13 / 12 : ℝ) ≠ 0 by norm_num)
  rw [h13] at h
  linarith

/-- `log 13` upper (`log 13 ≤ 2.5768275178` from `sSCUT_log_twelve_le` +
`log (13/12) ≤ 1/12`; mirror of `sSCUT_log_twelve_le` with `x = 1/12`
via `Real.log_le_sub_one_of_pos`). -/
theorem sSCUT_log_thirteen_le : Real.log 13 ≤ (2.5768275178 : ℝ) := by
  have h13 := sSCUT_log_thirteen_via_twelve_eq
  have h12 := sSCUT_log_twelve_le
  have hub : Real.log (13 / 12 : ℝ) ≤ (1 / 12 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 13 / 12)
    have he : (13 / 12 : ℝ) - 1 = (1 / 12 : ℝ) := by norm_num
    linarith
  have hfin : (2.4934941844 : ℝ) + 1 / 12 ≤ (2.5768275178 : ℝ) := by norm_num
  linarith

/-- `log 13` lower (`2.5537505937 ≤ log 13` from `sSCUT_log_twelve_ge` +
`log (13/12) ≥ 1/13`; mirror of `sSCUT_log_twelve_ge` with `x = 1/12`
via `log (12/13) ≤ -1/13` and `log (13/12) = -log (12/13)`). -/
theorem sSCUT_log_thirteen_ge : (2.5537505937 : ℝ) ≤ Real.log 13 := by
  have h13 := sSCUT_log_thirteen_via_twelve_eq
  have h12 := sSCUT_log_twelve_ge
  have hub : Real.log (12 / 13 : ℝ) ≤ (-1 / 13 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 12 / 13)
    have he : (12 / 13 : ℝ) - 1 = (-1 / 13 : ℝ) := by norm_num
    linarith
  have hinv : Real.log (13 / 12 : ℝ) = -Real.log (12 / 13 : ℝ) := by
    have heq : (13 / 12 : ℝ) = (12 / 13 : ℝ)⁻¹ := by rw [inv_div]
    rw [heq, Real.log_inv]
  have hfin : (2.5537505937 : ℝ) ≤ 2.4768275168 + 1 / 13 := by norm_num
  rw [h13, hinv]
  linarith

end Door3PilotR00Zeta
