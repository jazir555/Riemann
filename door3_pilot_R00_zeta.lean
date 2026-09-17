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
  linarith

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
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _).le hle

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
    norm_num
  have him_w : (-sSCUT).im = (-10 : ℝ) := by
    have e : (-sSCUT).im = -(sSCUT.im) := rfl
    rw [e, sSCUT_im]
    norm_num
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
      mul_le_mul hr_lo hc_lo hc0 (by norm_num)
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

/-- Sharp `n = 9` phase window (`10*log 9 ∈ (21.97224577, 21.97224578)`
via `sSCUT_log_nine_eq` + d9; enabler for the `δ₉` recipe). -/
theorem sSCUT_theta9_sharp_mem :
    (21.97224577 : ℝ) < 10 * Real.log 9 ∧ 10 * Real.log 9 < (21.97224578 : ℝ) := by
  have h9 := sSCUT_log_nine_eq
  have h3lo := Real.log_three_gt_d9
  have h3hi := Real.log_three_lt_d9
  have hsum_lo : (2.197224577 : ℝ) < 2 * Real.log 3 := by
    have c : 2 * (1.0986122885 : ℝ) = 2.197224577 := by norm_num
    linarith
  have hsum_hi : 2 * Real.log 3 < (2.197224578 : ℝ) := by
    have c : 2 * (1.0986122888 : ℝ) = 2.197224578 := by norm_num
    linarith
  have hmul_lo := mul_lt_mul_of_pos_left hsum_lo (by norm_num : (0 : ℝ) < 10)
  have hmul_hi := mul_lt_mul_of_pos_left hsum_hi (by norm_num : (0 : ℝ) < 10)
  have c1 : (10 : ℝ) * 2.197224577 = 21.97224577 := by norm_num
  have c2 : (10 : ℝ) * 2.197224578 = 21.97224578 := by norm_num
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
    norm_num
  have him_w : (-sSCUT).im = (-10 : ℝ) := by
    have e : (-sSCUT).im = -(sSCUT.im) := rfl
    rw [e, sSCUT_im]
    norm_num
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

end Door3PilotR00Zeta
