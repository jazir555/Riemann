import Mathlib

noncomputable section

/-!
# Float → ℝ bridge

Batteries `Float` is opaque (no exposed structure fields), but provides
`toRatParts (f : Float) : Option (Int × Int)` returning `(v, exp)` such that
`f = v · 2^exp`. We use this to define a noncomputable `Float.toReal : Float → ℝ`.

This is the missing infrastructure connecting the Float computation layer
(`float_zeta.lean`, `rh_zeta_cert_central.lean`) to ℝ-level goals.
-/

namespace Float

/-- Noncomputable coercion `Float → ℝ`.

    Uses `toRatParts` to obtain integers `(v, exp)` with `f = v · 2^exp`,
    then interprets this as `v · 2^exp : ℝ`. Returns `0` for non-finite inputs. -/
noncomputable def toReal (f : Float) : ℝ :=
  match f.toRatParts with
  | some (v, exp) => (v : ℝ) * (2 : ℝ) ^ (exp : ℤ)
  | none => 0

end Float
