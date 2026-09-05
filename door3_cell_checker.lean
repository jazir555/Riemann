import Mathlib

/-!
# Door-3 cell-certificate micro-checker (feasibility spike, new lane)

Cell obligation quoted from `central_cover_assembly.lean` (read-only source).
Simplest single cell = corner cell `R00 = (-10, -7.5) x (0.01, 0.2)`:

* `CellData` (central_cover_assembly.lean:111-126) carries, among others,
  `center_bound : ε + M * (Real.sqrt (((x1 - x0) / 2) ^ 2 + ((y1 - y0) / 2) ^ 2))
    ≤ ‖xiShifted (((x0 + x1) / 2 : ℝ) + I * ((y0 + y1) / 2 : ℝ))‖`
  and `deriv_bound : ∀ z, x0 ≤ z.re → z.re ≤ x1 → y0 ≤ z.im → z.im ≤ y1 →
    ‖deriv xiShifted z‖ ≤ M` (lines 124-126).
* `R00` is defined at central_cover_assembly.lean:1132-1134 as
  `⟨-10, -7.5, 0.01, 0.2, by norm_num, by norm_num⟩`; its center is
  `((-10 + -7.5) / 2, (0.01 + 0.2) / 2) = (-8.75, 0.105)`
  (center/radius shape from rh_certificate_infra.lean:25-26,35-36).
* The exact per-cell hypothesis is `R00_leaf_obligations`
  (central_cover_assembly.lean:1175-1177):
  `((0.002 : ℝ) + 0.05 * R00.radius ≤ ‖xiShifted R00.center‖) ∧
    (∀ w, R00.mem w → ‖deriv xiShifted w‖ ≤ (0.05 : ℝ))`,
  outer tier `(ε, M) = (0.002, 0.05)` with fencing need
  `ε + M * 1.26 = 0.065 < 0.1` (`fine_feasible_outer`,
  central_cover_assembly.lean:1027).
* The file itself states (central_cover_assembly.lean:1172-1174) that
  `center_bound` needs `‖ξ‖` at `s = 0.395 - 8.75·I` and that rigorous
  `ξ`-enclosures there are absent from Mathlib.

What this file proves (banked fallback, since the exact ξ-center statement
is unreachable this wave): a rational-interval checker core, where complex
numbers are `ℚ × ℚ` pairs and every enclosure is an exact-rational proof
rule (no floating-point arithmetic anywhere in this file), plus a timed
sample check on a zeta-center partial sum (head value + proved nonnegative
tail). The missing link for the next agent is exactly `R00_leaf_obligations`.
-/

/-- Closed rational interval `[lo, hi]`. -/
structure QIntv where
  lo : ℚ
  hi : ℚ
deriving DecidableEq, Repr

/-- Membership of a rational in a rational interval. -/
def QIntv.mem (I : QIntv) (x : ℚ) : Prop :=
  I.lo ≤ x ∧ x ≤ I.hi

/-- Interval addition encloses pointwise addition. -/
theorem qintv_mem_add {A B : QIntv} {a b : ℚ}
    (ha : A.mem a) (hb : B.mem b) :
    (QIntv.mk (A.lo + B.lo) (A.hi + B.hi)).mem (a + b) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  exact ⟨add_le_add ha1 hb1, add_le_add ha2 hb2⟩

/-- Interval multiplication (nonnegative bounds) encloses pointwise
multiplication. Squares of nonneg-enclosed values are the use case. -/
theorem qintv_mem_mul_nonneg {A B : QIntv} {a b : ℚ}
    (ha : A.mem a) (hb : B.mem b)
    (ha0 : 0 ≤ A.lo) (hb0 : 0 ≤ B.lo) :
    (QIntv.mk (A.lo * B.lo) (A.hi * B.hi)).mem (a * b) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have ha' : 0 ≤ a := le_trans ha0 ha1
  have hBhi : 0 ≤ B.hi := le_trans hb0 (le_trans hb1 hb2)
  refine ⟨?_, ?_⟩
  · calc A.lo * B.lo ≤ a * B.lo :=
          mul_le_mul_of_nonneg_right ha1 hb0
      _ ≤ a * b := mul_le_mul_of_nonneg_left hb1 ha'
  · calc a * b ≤ a * B.hi := mul_le_mul_of_nonneg_left hb2 ha'
      _ ≤ A.hi * B.hi := mul_le_mul_of_nonneg_right ha2 hBhi

/-- Square rule: a nonneg-enclosed value squares inside the squared bounds. -/
theorem qintv_sq_mem {A : QIntv} {a : ℚ}
    (ha : A.mem a) (ha0 : 0 ≤ A.lo) :
    (QIntv.mk (A.lo * A.lo) (A.hi * A.hi)).mem (a * a) :=
  qintv_mem_mul_nonneg ha ha ha0 ha0

/-- Rational complex rectangle: a product of two rational intervals. -/
structure QRect where
  reLo : ℚ
  reHi : ℚ
  imLo : ℚ
  imHi : ℚ
deriving DecidableEq, Repr

/-- Membership of a `ℚ × ℚ` point in a rational complex rectangle. -/
def QRect.mem (R : QRect) (z : ℚ × ℚ) : Prop :=
  R.reLo ≤ z.1 ∧ z.1 ≤ R.reHi ∧ R.imLo ≤ z.2 ∧ z.2 ≤ R.imHi

/-- Rectangle addition encloses pointwise addition of `ℚ × ℚ` points. -/
theorem qrect_mem_add {R S : QRect} {z w : ℚ × ℚ}
    (hz : R.mem z) (hw : S.mem w) :
    (QRect.mk (R.reLo + S.reLo) (R.reHi + S.reHi)
      (R.imLo + S.imLo) (R.imHi + S.imHi)).mem (z.1 + w.1, z.2 + w.2) := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  obtain ⟨w1, w2, w3, w4⟩ := hw
  exact ⟨add_le_add h1 w1, add_le_add h2 w2, add_le_add h3 w3, add_le_add h4 w4⟩

/-- Norm lower-bound bridge: a rational sum-of-squares certificate implies a
real complex-norm lower bound for the corresponding complex point. -/
theorem qnorm_lower_of_sq (re im b : ℚ) (hb : 0 ≤ b)
    (h : b ^ 2 ≤ re ^ 2 + im ^ 2) :
    (b : ℝ) ≤ ‖(((re : ℝ)) + ((im : ℝ)) * Complex.I)‖ := by
  have hre : ((((re : ℝ)) + ((im : ℝ)) * Complex.I)).re = (re : ℝ) := by simp
  have him : ((((re : ℝ)) + ((im : ℝ)) * Complex.I)).im = (im : ℝ) := by simp
  have hsq : ‖(((re : ℝ)) + ((im : ℝ)) * Complex.I)‖ ^ 2
      = (re : ℝ) ^ 2 + (im : ℝ) ^ 2 := by
    have h1 : Complex.normSq _ = ‖(((re : ℝ)) + ((im : ℝ)) * Complex.I)‖ ^ 2 :=
      Complex.normSq_eq_norm_sq _
    rw [Complex.normSq_apply, hre, him] at h1
    ring_nf at h1 ⊢
    linarith [h1]
  have hcast : (b : ℝ) ^ 2 ≤ (re : ℝ) ^ 2 + (im : ℝ) ^ 2 := by
    exact_mod_cast h
  rw [← hsq] at hcast
  have hbR : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  calc (b : ℝ) = Real.sqrt ((b : ℝ) ^ 2) := (Real.sqrt_sq hbR).symm
    _ ≤ Real.sqrt (‖(((re : ℝ)) + ((im : ℝ)) * Complex.I)‖ ^ 2) :=
        Real.sqrt_le_sqrt hcast
    _ = ‖(((re : ℝ)) + ((im : ℝ)) * Complex.I)‖ :=
        Real.sqrt_sq (norm_nonneg _)

/-- Proved tail: partial sums of `∑ 1/(k+1)^2` over `ℚ` are monotone, since
every tail term is nonnegative. -/
theorem zeta2_partial_mono {n m : ℕ} (h : n ≤ m) :
    ∑ k ∈ Finset.range n, (1 : ℚ) / ((k + 1 : ℚ) ^ 2) ≤
    ∑ k ∈ Finset.range m, (1 : ℚ) / ((k + 1 : ℚ) ^ 2) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
  intro i _ _
  positivity

/-! ## Certificate (exact rationals from python3 `Fractions` in Temp).

`H5 = ∑_{k=1..5} 1/k^2 = 5269/3600 ≈ 1.4636`; sample bound `1` beats the
outer-tier fencing need `0.002 + 0.05 * 1.26 = 0.065`. Every numeral below
has at most 6 digits, so each `norm_num` step stays far under the hang guard.
-/

/-- Certificate head value (python3 `Fraction`: `5269/3600`). -/
def certHead : ℚ := 5269 / 3600

/-- The head value is exactly the five-term partial sum. -/
theorem certHead_eq :
    certHead = 1 + 1 / 4 + 1 / 9 + 1 / 16 + 1 / 25 := by
  show (5269 : ℚ) / 3600 = _
  norm_num

/-- The five-term `Finset` sum equals the certificate head. -/
theorem certHead_sum_eq :
    (∑ k ∈ Finset.range 5, (1 : ℚ) / ((k + 1 : ℚ) ^ 2)) = certHead := by
  show (∑ k ∈ Finset.range 5, (1 : ℚ) / ((k + 1 : ℚ) ^ 2))
    = (5269 : ℚ) / 3600
  norm_num [Finset.sum_range_succ]

/-- Sample center-proxy lower bound: the head is at least `1`. -/
theorem certHead_lower : (1 : ℚ) ≤ certHead := by
  show (1 : ℚ) ≤ 5269 / 3600
  norm_num

/-- Checker application: interval addition on `1 + 1/4`. -/
theorem cert_add_check :
    (QIntv.mk ((1 : ℚ) + 1 / 4) ((1 : ℚ) + 1 / 4)).mem ((1 : ℚ) + 1 / 4) :=
  qintv_mem_add (A := QIntv.mk 1 1) (B := QIntv.mk (1 / 4) (1 / 4))
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩

/-- The addition demo closes at the exact python value `5/4`. -/
theorem cert_add_value : ((1 : ℚ) + 1 / 4) = 5 / 4 := by norm_num

/-- Checker application: nonneg interval multiplication on `(3/2) * (3/2)`. -/
theorem cert_mul_check :
    (QIntv.mk ((3 / 2 : ℚ) * (3 / 2)) ((3 / 2 : ℚ) * (3 / 2))).mem
      ((3 / 2 : ℚ) * (3 / 2)) :=
  qintv_mem_mul_nonneg (A := QIntv.mk (3 / 2) (3 / 2))
    (B := QIntv.mk (3 / 2) (3 / 2))
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    (by norm_num) (by norm_num)

/-- The multiplication demo closes at the exact python value `9/4`. -/
theorem cert_mul_value : ((3 / 2 : ℚ) * (3 / 2)) = (9 / 4 : ℚ) := by norm_num

/-- Checker application: norm bridge at `(re, im) = (1, 7/10)` with bound `1`
(`1^2 ≤ 1^2 + (7/10)^2 = 149/100`, checked by python `Fractions`). -/
theorem cert_norm_cast :
    ((1 : ℚ) : ℝ) ≤ ‖(((1 : ℚ)) : ℝ) + (((7 / 10 : ℚ)) : ℝ) * Complex.I‖ :=
  qnorm_lower_of_sq 1 (7 / 10) 1 (by norm_num) (by norm_num)

/-- The sample bound `1` beats the R00 outer-tier fencing need
`0.002 + 0.05 * 1.26 = 0.065` (cf. `fine_feasible_outer`). -/
theorem cert_beats_outer_tier :
    (0.002 : ℝ) + 0.05 * 1.26 < ((1 : ℚ) : ℝ) := by norm_num

/-- Sample center-proxy bound transported to `ℝ`. -/
theorem cert_sample_center_proxy : ((1 : ℚ) : ℝ) ≤ ((certHead : ℚ) : ℝ) := by
  have h : (1 : ℚ) ≤ certHead := certHead_lower
  exact_mod_cast h

#print axioms qintv_mem_add
#print axioms qintv_mem_mul_nonneg
#print axioms qintv_sq_mem
#print axioms qrect_mem_add
#print axioms qnorm_lower_of_sq
#print axioms zeta2_partial_mono
#print axioms certHead_lower
#print axioms cert_norm_cast
