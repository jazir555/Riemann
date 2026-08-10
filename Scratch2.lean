import Mathlib
open Filter

theorem zsum_geometric (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => if n = 0 then (0:ℝ) else q ^ (n.natAbs)) (2 * (q / (1 - q))) := by
  have hg : HasSum (fun n : ℕ => q ^ n) (1 - q)⁻¹ := hasSum_geometric_of_lt_one hq0 hq1
  have hg_sum : (1 - q)⁻¹ = 1 + q / (1 - q) := by ring_nf
  rw [hg_sum] at hg
  -- nonneg part over ℤ: Σ_{n≥0} q^n minus the n=0 term 1 gives Σ_{n≥0, n≠0} q^n.
  have hpos : HasSum (fun n : ℕ => if n = 0 then (0:ℝ) else q ^ n) (q / (1 - q)) := by
    rw [show (fun n => if n = 0 then (0:ℝ) else q ^ n) = fun n => q ^ n - if n = 0 then 1 else 0
        from by funext n; by_cases h n0; all_goals simp [*]]
    have h1 : HasSum (fun n : ℕ => (if n = 0 then (1:ℝ) else 0)) (1:ℝ) :=
      hasSum_ite_eq (0:ℕ) 1
    exact hg.sub h1
  -- negative part: Σ_{n<0} q^{|n|} = Σ_{m≥0} q^{m+1} via n = -(m+1).
  have hneg_nat : HasSum (fun m : ℕ => q ^ (m + 1)) (q / (1 - q)) := by
    have h := hg.mul_left q
    rw [pow_succ', mul_div_assoc, hg_sum] at h
    exact h
  have hneg : HasSum (fun n : ℤ => if n < 0 then q ^ (n.natAbs) else 0) (q / (1 - q)) := by
    convert hneg_nat using 1
    ext1 m
    rw [Int.neg_natAbs]
    simp
  have hpos' : HasSum (fun n : ℤ => if 0 < n then q ^ (n.natAbs) else 0) (q / (1 - q)) := by
    convert hpos using 1
    ext1 n
    by_cases h : n < 0
    · simp [h]
    · have hn0 : n ≠ 0 → 0 < n := by
        intro hn0; rcases le_iff_eq_or_lt.mp (Int.ofNat_nonneg _) with rfl | hlt <;> simp [hn0, h]
      by_cases hn0 : n = 0
      · simp [hn0, h]
      · simp [hn0, h, hn0]
  have hsum : HasSum (fun n : ℤ => (if 0 < n then q ^ (n.natAbs) else 0) +
      (if n < 0 then q ^ (n.natAbs) else 0)) (q / (1 - q) + q / (1 - q)) := hpos'.add hneg
  refine hsum.congr ?_
  intro n
  by_cases hn0 : n = 0
  · simp [hn0]
  rcases lt_or_gt_of_ne hn0 with hlt | hgt
  · simp [hlt, Int.natAbs_of_nonpos (le_of_lt hlt)]
  · simp [hgt, Int.natAbs_of_nonneg (le_of_lt hgt)]
