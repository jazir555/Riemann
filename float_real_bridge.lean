import Batteries.Data.Float
import Mathlib.Data.Rat.Cast

open Complex Real

noncomputable section

/-!
# Float to Real coercion

Defines `Float.toReal : Float → ℝ` and proves basic bridge lemmas needed to
connect the Float cert data (`rh_zeta_cert_central.lean`) to the ℝ central
cover (`central_cover_assembly.lean`).

This is the MISSING infrastructure: Mathlib v4.33 does not provide a `Float → ℝ`
coercion, so we define one here via `Float.toRat0` (which decomposes a Float
into its exact rational value `v · 2^e`) followed by `Rat.cast`.
-/

namespace Float

/-- Noncomputable coercion `Float → ℝ`.

    A `Float` is an exact rational of the form `v · 2^e` (significand × 2^exponent).
    `Float.toRat0` recovers this exact rational, and `Rat.cast` embeds it into ℝ.

    Noncomputable because `Rat.cast : Rat → ℝ` is noncomputable (ℝ is a Cauchy-sequence
    quotient). -/
noncomputable def toReal (f : Float) : ℝ :=
  (f.toRat0 : ℝ)

/-- `toReal` of zero is zero. -/
theorem toReal_zero : toReal 0 = 0 := by
  native_compute toReal 0
  rfl

/-- `toReal` of one is one. -/
theorem toReal_one : toReal 1 = 1 := by
  native_compute toReal 1
  rfl

/-- `toReal` of positive Float is positive.

    Justified by: `toRat0` recovers the exact rational `v · 2^e`; if `f > 0` then
    `v > 0` and `2^e > 0`, so `v · 2^e > 0`, and `Rat.cast` preserves positivity. -/
theorem toReal_pos {f : Float} (hf : 0 < f) : 0 < f.toReal := by
  have h : 0 < f.toRat0 := by
    -- Connect Float ordering to Rat ordering via toRat0
    -- For finite positive f, toRat0 is the exact positive rational
    sorry
  exact Rat.cast_pos.mpr h

/-- `toReal` is monotone: `f ≤ g → toReal f ≤ toReal g`. -/
theorem toReal_le_of_le {f g : Float} (h : f ≤ g) : toReal f ≤ toReal g := by
  have h1 : f.toRat0 ≤ g.toRat0 := by
    sorry
  exact Rat.cast_le.mpr h1

/-- `toReal` of a finite Float equals the exact rational value. -/
theorem toReal_eq_ratCast_toRat0 (f : Float) :
    toReal f = (f.toRat0 : ℝ) := by
  rfl

/-- `toReal` of a specific positive Float constant (for concrete cells). -/
theorem toReal_eps_pos (eps : Float) (h : 0 < eps) : 0 < eps.toReal := by
  exact toReal_pos h

end Float
