import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_subgroup_eq_top_of_forall_inertia_le

theorem NumberField.subgroup_eq_top_of_forall_inertia_le {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K] (H : Subgroup (K ≃ₐ[ℚ] K)) (hH : ∀ P : Ideal (NumberField.RingOfIntegers K), P.IsMaximal → P.inertia (K ≃ₐ[ℚ] K) ≤ H) : H = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_subgroup_eq_top_of_forall_inertia_le.solution
