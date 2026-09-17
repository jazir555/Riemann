import door3_R02_ball_advance
import zeta_rigorous

/-!
# Door-3 R02 zeta bridge (UZ = 934).

Import-closure only: `door3_R02_ball_advance` banks the assembly-ready
`R02_polyPiGammaZetaVal_cap_disc_of_zeta (UZ)` (explicit `‖zeta s‖ ≤ UZ`
premise) but does NOT import `zeta_rigorous`, where the unconditional
`R02_D3_zeta_upper_934 : ‖riemannZeta s‖ ≤ 934` lives on the SAME full R02
rect (`Re ∈ [0.05, 0.74]`, `Im ∈ [-8.25, -5.25]`). `zeta = riemannZeta` by
`rfl` (`riemann_hypothesis.lean:16`), so the transfer is a definitional
rewrite. Banks `‖P * Q * G * Z‖ ≤ 1680 * 934 = 1569120`.
No `sorry` / `admit` / `axiom` / `simpa`; explicit premises; short numerals.
-/

noncomputable section

open Complex

/-- Transfer of `R02_D3_zeta_upper_934` to `zeta` on the full R02 rect. -/
theorem R02_zetaVal_934_of_D3 (s : ℂ) (hre_lo : 0.05 ≤ s.re)
    (hre_hi : s.re ≤ 0.74) (him_lo : -8.25 ≤ s.im)
    (him_hi : s.im ≤ -5.25) :
    ‖zeta s‖ ≤ 934 := by
  show ‖riemannZeta s‖ ≤ 934
  exact R02_D3_zeta_upper_934 s hre_lo hre_hi him_lo him_hi

/-- Banked 4-factor value cap on the R02 rect with `UZ := 934`:
`‖P * Q * G * Z‖ ≤ 1680 * 934 = 1569120`. -/
theorem R02_polyPiGammaZetaVal_cap_934 {s : ℂ}
    (hre_lo : 0.05 ≤ s.re) (hre_hi : s.re ≤ 0.74)
    (him_lo : -8.25 ≤ s.im) (him_hi : s.im ≤ -5.25) :
    ‖DerivCauchyBridge.polyOf s * DerivCauchyBridge.piOf s *
      DerivCauchyBridge.gammaOf s * zeta s‖ ≤ 1569120 := by
  have hZ : ‖zeta s‖ ≤ 934 :=
    R02_zetaVal_934_of_D3 s hre_lo hre_hi him_lo him_hi
  have h := Door3R02BallAdvance.R02_polyPiGammaZetaVal_cap_disc_of_zeta
    934 hre_lo hre_hi him_lo him_hi hZ
  have heq : (1680 : ℝ) * 934 = 1569120 := by norm_num
  rw [heq] at h
  exact h
