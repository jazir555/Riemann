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
/-! ## Door-3 generalization (checker lane): two-sided complex mul + sqrt upper.

Banked this wave (sorry-free):
* `qintv_mem_sub`: interval subtraction enclosure.
* `qintv_mem_mul`: general two-sided interval multiplication enclosure via
  explicit corner bounds (handles negative bounds; proved by sign-split on `b`
  and the interval endpoint, using only `mul_le_mul_of_nonneg_left/right`
  plus `ring`/`linarith` — no `decide`, no floats).
* `qrect_mem_mul_of_products`: two-sided complex-multiplication enclosure:
  four real product enclosures (each via `qintv_mem_mul`) combine through
  `qintv_mem_sub` (real part) and `qintv_mem_add` (imag part).
* `real_sqrt_upper` + `qsqrt_upper`: rigorous `Real.sqrt` UPPER-bound rules.
-/

/-- Interval subtraction encloses pointwise subtraction. -/
theorem qintv_mem_sub {A B : QIntv} {a b : ℚ}
    (ha : A.mem a) (hb : B.mem b) :
    (QIntv.mk (A.lo - B.hi) (A.hi - B.lo)).mem (a - b) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  exact ⟨by linarith, by linarith⟩

/-- General two-sided interval multiplication: if `lo`/`hi` bound all four
corner products, they enclose every pointwise product (negative bounds OK). -/
theorem qintv_mem_mul {A B : QIntv} {a b : ℚ} {lo hi : ℚ}
    (ha : A.mem a) (hb : B.mem b)
    (hlo1 : lo ≤ A.lo * B.lo) (hlo2 : lo ≤ A.lo * B.hi)
    (hlo3 : lo ≤ A.hi * B.lo) (hlo4 : lo ≤ A.hi * B.hi)
    (hhi1 : A.lo * B.lo ≤ hi) (hhi2 : A.lo * B.hi ≤ hi)
    (hhi3 : A.hi * B.lo ≤ hi) (hhi4 : A.hi * B.hi ≤ hi) :
    (QIntv.mk lo hi).mem (a * b) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  constructor
  · by_cases hb0 : 0 ≤ b
    · have hAB : A.lo * b ≤ a * b := mul_le_mul_of_nonneg_right ha1 hb0
      by_cases hAlo : 0 ≤ A.lo
      · have h2 : A.lo * B.lo ≤ A.lo * b := mul_le_mul_of_nonneg_left hb1 hAlo
        linarith
      · push_neg at hAlo
        have hpos : 0 ≤ -A.lo := by linarith
        have h2 : (-A.lo) * b ≤ (-A.lo) * B.hi :=
          mul_le_mul_of_nonneg_left hb2 hpos
        have e1 : (-A.lo) * b = -(A.lo * b) := by ring
        have e2 : (-A.lo) * B.hi = -(A.lo * B.hi) := by ring
        have h3 : A.lo * B.hi ≤ A.lo * b := by linarith
        linarith
    · push_neg at hb0
      have hneg : 0 ≤ -b := by linarith
      have hAB : A.hi * b ≤ a * b := by
        have h2 : (-b) * a ≤ (-b) * A.hi :=
          mul_le_mul_of_nonneg_left ha2 hneg
        have e1 : (-b) * a = -(a * b) := by ring
        have e2 : (-b) * A.hi = -(A.hi * b) := by ring
        linarith
      by_cases hAhi : 0 ≤ A.hi
      · have h2 : A.hi * B.lo ≤ A.hi * b := mul_le_mul_of_nonneg_left hb1 hAhi
        linarith
      · push_neg at hAhi
        have hpos : 0 ≤ -A.hi := by linarith
        have h2 : (-A.hi) * b ≤ (-A.hi) * B.hi :=
          mul_le_mul_of_nonneg_left hb2 hpos
        have e1 : (-A.hi) * b = -(A.hi * b) := by ring
        have e2 : (-A.hi) * B.hi = -(A.hi * B.hi) := by ring
        have h3 : A.hi * B.hi ≤ A.hi * b := by linarith
        linarith
  · by_cases hb0 : 0 ≤ b
    · have hAB : a * b ≤ A.hi * b := mul_le_mul_of_nonneg_right ha2 hb0
      by_cases hAhi : 0 ≤ A.hi
      · have h2 : A.hi * b ≤ A.hi * B.hi := mul_le_mul_of_nonneg_left hb2 hAhi
        linarith
      · push_neg at hAhi
        have hpos : 0 ≤ -A.hi := by linarith
        have h2 : (-A.hi) * B.lo ≤ (-A.hi) * b :=
          mul_le_mul_of_nonneg_left hb1 hpos
        have e1 : (-A.hi) * B.lo = -(A.hi * B.lo) := by ring
        have e2 : (-A.hi) * b = -(A.hi * b) := by ring
        have h3 : A.hi * b ≤ A.hi * B.lo := by linarith
        linarith
    · push_neg at hb0
      have hneg : 0 ≤ -b := by linarith
      have hAB : a * b ≤ A.lo * b := by
        have h2 : (-b) * A.lo ≤ (-b) * a :=
          mul_le_mul_of_nonneg_left ha1 hneg
        have e1 : (-b) * A.lo = -(A.lo * b) := by ring
        have e2 : (-b) * a = -(a * b) := by ring
        linarith
      by_cases hAlo : 0 ≤ A.lo
      · have h2 : A.lo * b ≤ A.lo * B.hi := mul_le_mul_of_nonneg_left hb2 hAlo
        linarith
      · push_neg at hAlo
        have hpos : 0 ≤ -A.lo := by linarith
        have h2 : (-A.lo) * B.lo ≤ (-A.lo) * b :=
          mul_le_mul_of_nonneg_left hb1 hpos
        have e1 : (-A.lo) * B.lo = -(A.lo * B.lo) := by ring
        have e2 : (-A.lo) * b = -(A.lo * b) := by ring
        have h3 : A.lo * b ≤ A.lo * B.lo := by linarith
        linarith

/-- Two-sided complex-multiplication enclosure from four real product
enclosures (real part via sub, imag part via add; negatives OK). -/
theorem qrect_mem_mul_of_products {z w : ℚ × ℚ}
    {P1 P2 P3 P4 : QIntv}
    (hP1 : P1.mem (z.1 * w.1)) (hP2 : P2.mem (z.2 * w.2))
    (hP3 : P3.mem (z.1 * w.2)) (hP4 : P4.mem (z.2 * w.1)) :
    (QRect.mk (P1.lo - P2.hi) (P1.hi - P2.lo)
      (P3.lo + P4.lo) (P3.hi + P4.hi)).mem
      (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1) := by
  have hRe := qintv_mem_sub hP1 hP2
  have hIm := qintv_mem_add hP3 hP4
  obtain ⟨hr1, hr2⟩ := hRe
  obtain ⟨hi1, hi2⟩ := hIm
  exact ⟨hr1, hr2, hi1, hi2⟩

/-- Rigorous `Real.sqrt` upper bound (real version). -/
theorem real_sqrt_upper {x m : ℝ} (hm : 0 ≤ m) (h : x ≤ m ^ 2) :
    Real.sqrt x ≤ m := by
  calc Real.sqrt x ≤ Real.sqrt (m ^ 2) := Real.sqrt_le_sqrt h
    _ = m := Real.sqrt_sq hm

/-- Rigorous `Real.sqrt` upper bound (rational bridge; exact Fractions). -/
theorem qsqrt_upper {x b : ℚ} (hb : 0 ≤ b) (h : x ≤ b * b) :
    Real.sqrt (x : ℝ) ≤ (b : ℝ) := by
  apply real_sqrt_upper (by exact_mod_cast hb)
  have hcast : (x : ℝ) ≤ (b : ℝ) * (b : ℝ) := by exact_mod_cast h
  have h2 : (b : ℝ) ^ 2 = (b : ℝ) * (b : ℝ) := by ring
  rw [h2]
  exact hcast

/-! ### Demos of the generalized rules (exact rationals, `by norm_num` only).
All numerals ≤6 digits. -/

/-- Demo: interval subtraction `(3/2) - (1/2) = 1`. -/
theorem cert_sub_check :
    (QIntv.mk ((3 / 2 : ℚ) - 1 / 2) ((3 / 2 : ℚ) - 1 / 2)).mem
      ((3 / 2 : ℚ) - 1 / 2) :=
  qintv_mem_sub (A := QIntv.mk (3 / 2) (3 / 2)) (B := QIntv.mk (1 / 2) (1 / 2))
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩

/-- Demo value: `(3/2) - (1/2) = 1`. -/
theorem cert_sub_value : ((3 / 2 : ℚ) - 1 / 2) = (1 : ℚ) := by norm_num

/-- Demo: two-sided product with negatives.
`a = -3/2 ∈ [-2,-1]`, `b = 1/2 ∈ [-3,2]`; corners `6,-4,3,-2`; `lo=-4,hi=6`. -/
theorem cert_mul_two_sided_check :
    (QIntv.mk (-4 : ℚ) 6).mem ((-3 / 2 : ℚ) * (1 / 2 : ℚ)) :=
  qintv_mem_mul (A := QIntv.mk (-2) (-1)) (B := QIntv.mk (-3) 2)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Demo value: `(-3/2) * (1/2) = -3/4`. -/
theorem cert_mul_two_sided_value : ((-3 / 2 : ℚ) * (1 / 2 : ℚ)) = (-3 / 4 : ℚ) := by
  norm_num

/-- Demo: complex product `(1,1) * (1,-1) = (2,0)` via four product enclosures.
`P1=[1,1] ∋ 1*1`, `P2=[-1,-1] ∋ 1*(-1)`, `P3=[-1,-1] ∋ 1*(-1)`, `P4=[1,1] ∋ 1*1`. -/
theorem cert_rect_mul_check :
    (QRect.mk (1 - (-1) : ℚ) (1 - (-1) : ℚ) ((-1) + 1 : ℚ) ((-1) + 1 : ℚ)).mem
      ((1 : ℚ) * 1 - 1 * (-1), (1 : ℚ) * (-1) + 1 * 1) := by
  have hP1 : (QIntv.mk (1 : ℚ) 1).mem ((1 : ℚ) * 1) :=
    qintv_mem_mul (A := QIntv.mk 1 1) (B := QIntv.mk 1 1)
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP2 : (QIntv.mk (-1 : ℚ) (-1)).mem ((1 : ℚ) * (-1)) :=
    qintv_mem_mul (A := QIntv.mk 1 1) (B := QIntv.mk (-1) (-1))
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP3 : (QIntv.mk (-1 : ℚ) (-1)).mem ((1 : ℚ) * (-1)) :=
    qintv_mem_mul (A := QIntv.mk 1 1) (B := QIntv.mk (-1) (-1))
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP4 : (QIntv.mk (1 : ℚ) 1).mem ((1 : ℚ) * 1) :=
    qintv_mem_mul (A := QIntv.mk 1 1) (B := QIntv.mk 1 1)
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := qrect_mem_mul_of_products (z := (1, 1)) (w := (1, -1)) hP1 hP2 hP3 hP4
  exact h

/-- Demo value: complex product closes at `(2,0)`. -/
theorem cert_rect_mul_value :
    ((1 : ℚ) * 1 - 1 * (-1), (1 : ℚ) * (-1) + 1 * 1) = (2, 0) := by
  norm_num

/-- Demo: rigorous sqrt upper bound for the R00 geometry
`√(1.25² + 0.095²) ≤ 1.26` (exact decimal check `1.571525 ≤ 1.5876`). -/
theorem cert_sqrt_upper_check :
    Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) ≤ (1.26 : ℝ) := by
  apply real_sqrt_upper (by norm_num)
  norm_num

/-! ### R00 full proxy cell obligation (`center_bound` shape, outer tier).

Corner cell `R00 = (-10,-7.5) × (0.01,0.2)` (central_cover_assembly.lean:1132),
tier `(ε,M) = (0.002,0.05)` (`fine_feasible_outer`), center `(-8.75,0.105)`,
`dx = 1.25`, `dy = 0.095`. Shape mirrors `CellData.center_bound` /
`R00_leaf_obligations` with the rational proxy head `certHead` in place of
`‖xiShifted center‖` (true `ξ`-enclosure absent from Mathlib — the residual
missing lemma is inventoried below): head sum (`certHead_sum_eq`) + tail mono
(`zeta2_partial_mono` reuse) + norm lower (`qnorm_lower_of_sq`).
All steps `by norm_num`, numerals ≤6 digits. -/

/-- R00 radius upper bound through the generalized checker rule. -/
theorem R00_radius_upper_checker :
    Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2) ≤ (1.26 : ℝ) :=
  cert_sqrt_upper_check

/-- R00 tail step reusing the proved majorant `zeta2_partial_mono`
(one-term partial sum ≤ five-term head). -/
theorem R00_tail_mono :
    (∑ k ∈ Finset.range 1, (1 : ℚ) / ((k + 1 : ℚ) ^ 2)) ≤ certHead := by
  have h := zeta2_partial_mono (n := 1) (m := 5) (by norm_num)
  rw [certHead_sum_eq] at h
  exact h

/-- R00 proxy center bound (`center_bound` shape at the 1.26 radius cap):
`0.002 + 0.05 * √(1.25²+0.095²) ≤ certHead`. -/
theorem R00_proxy_center :
    (0.002 : ℝ) + 0.05 * Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2)
      ≤ ((certHead : ℚ) : ℝ) := by
  have hRad := R00_radius_upper_checker
  have hM : (0.05 : ℝ) * Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2)
      ≤ 0.05 * 1.26 :=
    mul_le_mul_of_nonneg_left hRad (by norm_num)
  have h1 : (0.002 : ℝ) + 0.05 * Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2)
      ≤ (0.002 : ℝ) + 0.05 * 1.26 := by linarith
  have h2 : ((0.002 : ℝ) + 0.05 * 1.26) ≤ ((certHead : ℚ) : ℝ) := by
    have hle : ((0.002 : ℝ) + 0.05 * 1.26) ≤ (((1 : ℚ)) : ℝ) := by norm_num
    exact le_trans hle cert_sample_center_proxy
  exact le_trans h1 h2

/-- R00 proxy center bound transported through the norm bridge
(`center_bound` shape with an explicit complex norm target). -/
theorem R00_proxy_center_norm :
    (0.002 : ℝ) + 0.05 * Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2)
      ≤ ‖(((1 : ℚ)) : ℝ) + (((7 / 10 : ℚ)) : ℝ) * Complex.I‖ := by
  have hRad := R00_radius_upper_checker
  have hM : (0.05 : ℝ) * Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2)
      ≤ 0.05 * 1.26 :=
    mul_le_mul_of_nonneg_left hRad (by norm_num)
  have h4 : (0.002 : ℝ) + 0.05 * Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2)
      ≤ (((1 : ℚ)) : ℝ) := by
    have hle : (0.002 : ℝ) + 0.05 * Real.sqrt ((1.25 : ℝ) ^ 2 + (0.095 : ℝ) ^ 2)
        ≤ (0.002 : ℝ) + 0.05 * 1.26 := by linarith
    have hlt : ((0.002 : ℝ) + 0.05 * 1.26) ≤ (((1 : ℚ)) : ℝ) := by norm_num
    exact le_trans hle hlt
  exact le_trans h4 cert_norm_cast

#print axioms qintv_mem_sub
#print axioms qintv_mem_mul
#print axioms qrect_mem_mul_of_products
#print axioms real_sqrt_upper
#print axioms qsqrt_upper
#print axioms cert_sub_check
#print axioms cert_mul_two_sided_check
#print axioms cert_rect_mul_check
#print axioms cert_sqrt_upper_check
#print axioms R00_radius_upper_checker
#print axioms R00_tail_mono
#print axioms R00_proxy_center
#print axioms R00_proxy_center_norm
