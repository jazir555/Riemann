import central_cover_assembly

open Complex Real Set Topology
noncomputable section

namespace Door3BoundaryEndpoints

open CentralCoverAssembly

 theorem xiShifted_at_pos_I_half : _root_.xiShifted (Complex.I / 2) = 0 := by
  unfold _root_.xiShifted classicalXi XiFromPrefactor classicalXiPrefactor
  have hI : (Complex.I : ℂ) * (Complex.I / 2) = -(1 / 2 : ℂ) := by
    calc
      (Complex.I : ℂ) * (Complex.I / 2) = (Complex.I * Complex.I) / 2 := by ring
      _ = -(1 / 2 : ℂ) := by rw [Complex.I_mul_I]; ring
  rw [hI]
  norm_num

 theorem xiShifted_at_neg_I_half : _root_.xiShifted (-(Complex.I / 2)) = 0 := by
  unfold _root_.xiShifted classicalXi XiFromPrefactor classicalXiPrefactor
  have hI : (Complex.I : ℂ) * (-(Complex.I / 2)) = (1 / 2 : ℂ) := by
    calc
      (Complex.I : ℂ) * (-(Complex.I / 2)) = -((Complex.I * Complex.I) / 2) := by ring
      _ = (1 / 2 : ℂ) := by rw [Complex.I_mul_I]; ring
  rw [hI]
  norm_num

 theorem xiShiftedEntire_at_pos_I_half : xiShiftedEntire (Complex.I / 2) = (1 / 2 : ℂ) := by
  unfold xiShiftedEntire
  have hsq : (Complex.I / 2) ^ 2 + (1 / 4 : ℂ) = 0 := by
    rw [div_pow, Complex.I_sq]
    norm_num
  rw [hsq]
  ring

 theorem xiShiftedEntire_at_neg_I_half : xiShiftedEntire (-(Complex.I / 2)) = (1 / 2 : ℂ) := by
  unfold xiShiftedEntire
  have hsq : (-(Complex.I / 2)) ^ 2 + (1 / 4 : ℂ) = 0 := by
    rw [neg_sq, div_pow, Complex.I_sq]
    norm_num
  rw [hsq]
  ring

#print axioms xiShifted_at_pos_I_half
#print axioms xiShifted_at_neg_I_half
#print axioms xiShiftedEntire_at_pos_I_half
#print axioms xiShiftedEntire_at_neg_I_half

end Door3BoundaryEndpoints

