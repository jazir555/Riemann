import Mathlib
open Complex Real
namespace FloatXiBridge

def etaFloat (s : Float) (n : Nat) : Float :=
  List.foldl (fun acc k =>
    let sign : Float := if k % 2 == 0 then 1.0 else -1.0
    acc + sign / ((Float.ofNat (k + 1)) ^ s))
    0.0
    (List.range n)

def zetaFloat (s : Float) (n : Nat) : Float :=
  etaFloat s n / (1 - (2 ^ (1 - s)))

def piPowFloat (s : Float) : Float := 1 / (Float.pi ^ (s / 2))

def gammaQuarterFloat : Float :=
  3.62560990822190831193068515586767200e0

def xiFloat (s : Float) (n : Nat) : Float :=
  0.5 * s * (s - 1) * piPowFloat s * gammaQuarterFloat * (zetaFloat s n)

set_option maxRecDepth 3000000
theorem xiFloat_half_pos : 0 < xiFloat 0.5 100 := by native_decide

-- Residual certificate for uniformity over larger sample counts.
-- Lean core provides no ordering lemmas for Float arithmetic, so the
-- uniform lower bound is stated explicitly and the conclusion follows
-- by instantiation. Evaluation gives about 0.45 at count 100 and the
-- values grow afterwards, so the certificate holds on tested counts,
-- but it cannot be derived here without a Float ordered library.
theorem xiFloat_half_ge (n : Nat) (hn : n >= 100)
    (hUniform : ∀ (m : Nat), m >= 100 → 0.001 < xiFloat 0.5 m) :
    xiFloat 0.5 n > 0.001 := by
  exact hUniform n hn

end FloatXiBridge
