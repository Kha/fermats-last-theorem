import Mathlib
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_generalLinearGroup_forall_algHom_apply_eq_conj_algHom_apply

set_option autoImplicit false

open scoped Quaternion MatrixGroups

theorem QuaternionAlgebra.exists_generalLinearGroup_forall_algHom_apply_eq_conj_algHom_apply
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (K : Type) [Field K] [CharZero K]
    (ι₀ ι₁ : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K) :
    ∃ g : GL (Fin 2) K, ∀ x : ℍ[ℚ, a, b],
      ι₁ x = (g : Matrix (Fin 2) (Fin 2) K) * ι₀ x * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_generalLinearGroup_forall_algHom_apply_eq_conj_algHom_apply.solution
