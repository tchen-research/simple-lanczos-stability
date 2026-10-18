import FinitePrecisionLanczos.Lanczos.Greenbaum.Dilation


namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)


theorem greenbaumKsucc_strictUpper : StrictUpper L.greenbaumKsucc :=
  triangularK_strictUpper (Nat.succ_pos k) _ L.normalizedRsucc_strictUpper

structure PhysicalDilation : Prop where
  orthonormal : L.greenbaumVhatᵀ * L.greenbaumVhat = 1
  first_column :
    L.greenbaumVhat *ᵥ firstCoord (Nat.succ_pos k) =
      physicalFirst L.hk_pos L.normalizedV

theorem physical_dilation : L.PhysicalDilation where
  orthonormal := L.greenbaumVhat_orthonormal
  first_column := L.greenbaumVhat_first


structure ExchangeRule : Prop where
  L_def : L.greenbaumL = L.greenbaumC * L.normalizedCommutator * L.greenbaumC
  K_norm : ‖L.greenbaumK‖ ≤ 1
  C_norm : ‖L.greenbaumC‖ ≤ 2
  L_bound : ‖L.greenbaumL‖ ≤ (38400 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖
  power_exchange : ∀ r : ℕ, ∃ D : Mat k k,
    L.underlineTmat * L.greenbaumK ^ r - L.greenbaumKsucc ^ r * L.underlineTmat =
        embedJ * D ∧
      ‖D‖ ≤ (r : ℝ) * ‖L.greenbaumL‖

theorem exchange_rule : L.ExchangeRule where
  L_def := rfl
  K_norm := L.greenbaumK_norm_le_one
  C_norm := L.greenbaumC_norm_le_two
  L_bound := L.greenbaumL_bound
  power_exchange r :=
    ⟨L.greenbaumD r, by rw [embedJ_mul]; exact L.greenbaum_power_exchange r,
      L.greenbaumD_norm r⟩


structure BlockRecurrence (r : ℕ) (hr : r ≤ k) : Prop where
  equation :
    L.H * L.greenbaumVBlock r =
      L.greenbaumVhatBlock r * L.underlineTmat + L.greenbaumErrorBlock r
  error_formula :
    L.greenbaumErrorBlock r =
      L.normalizedFmat * L.greenbaumC * L.greenbaumK ^ r +
        L.normalizedV * (L.greenbaumD r - L.greenbaumD (r + 1))
  error_norm :
    ‖L.greenbaumErrorBlock r‖ ≤
      2 * ‖L.normalizedFmat‖ + (2 * (k : ℝ) + 1) * (k : ℝ) * ‖L.greenbaumL‖
  error_bound :
    ‖L.greenbaumErrorBlock r‖ ≤ (120000 * (k : ℝ) ^ 5) * L.ε * ‖L.H‖

theorem block_recurrence (r : ℕ) (hr : r ≤ k) :
    L.BlockRecurrence r hr where
  equation := L.greenbaum_block_recurrence r
  error_formula := L.greenbaumErrorBlock_eq r
  error_norm := L.greenbaumErrorBlock_norm r hr
  error_bound := L.greenbaumErrorBlock_bound r hr

structure DilatedRecurrence : Prop where
  recurrence :
    L.greenbaumBlockOperator * L.greenbaumX =
      L.greenbaumVhat * L.underlineTmat + L.greenbaumError
  error_bound :
    ‖L.greenbaumError‖ ≤ (240000 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖

theorem dilated_recurrence : L.DilatedRecurrence where
  recurrence := L.greenbaum_dilation_recurrence
  error_bound := L.greenbaumError_bound

end LanczosRun
end FinitePrecisionLanczos
