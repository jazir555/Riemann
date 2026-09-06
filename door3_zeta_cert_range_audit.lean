import rh_zeta_cert_data

set_option maxRecDepth 1000000

/-!
# Door 3 certificate-range audit

The finite `zeta_cert_data` table is useful only on the range represented by
its two height coordinates.  This file records that range by exact kernel
checked finite computation, so that it cannot be silently reused as a
certificate for the central strip.
-/

theorem zeta_cert_data_all_heights_above_ten :
    ∀ t ∈ zeta_cert_data, (10 : Float) < t.2.2.1 := by
  decide

theorem zeta_cert_data_all_height_ends_below_twelve :
    ∀ t ∈ zeta_cert_data, t.2.2.2.2 < (12 : Float) := by
  decide

theorem zeta_cert_data_disjoint_from_central_height_band :
    ∀ t ∈ zeta_cert_data,
      ¬ (t.2.2.1 < (0.49 : Float) ∧ (0.01 : Float) < t.2.2.2.2) := by
  decide

theorem zeta_cert_data_first_height_is_above_ten :
    (10 : Float) < zeta_cert_data[0]!.2.2.1 := by
  decide

theorem zeta_cert_data_last_height_is_below_twelve :
    zeta_cert_data[zeta_cert_data.size - 1]!.2.2.2.2 < (12 : Float) := by
  decide
