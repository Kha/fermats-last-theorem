import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_forall_existsUnique_eq_sum_zsmul

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_forall_existsUnique_eq_sum_zsmul
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) :
    ∃ β : Fin (2 * 2) → ↥Λ, ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_forall_existsUnique_eq_sum_zsmul.solution
