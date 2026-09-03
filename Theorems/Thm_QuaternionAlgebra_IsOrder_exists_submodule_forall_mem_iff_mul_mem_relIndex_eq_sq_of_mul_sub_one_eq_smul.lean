import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_exists_submodule_forall_mem_iff_mul_mem_relIndex_eq_sq_of_mul_sub_one_eq_smul

set_option autoImplicit false

open scoped Quaternion Pointwise
open QuaternionAlgebra

theorem QuaternionAlgebra.IsOrder.exists_submodule_forall_mem_iff_mul_mem_relIndex_eq_sq_of_mul_sub_one_eq_smul
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (ℓ : ℕ)
    (J : Submodule ℤ ℍ[ℚ, a, b]) (hJ : J ≤ Λ) (hℓJ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ J)
    (hJ_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ J → (y : ℍ[ℚ, a, b]) * x ∈ J)
    (hJ_index : J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    (w : ↥Λ) (hwu : ∃ w' : ↥Λ, ∃ y : ↥Λ, (w' : ℍ[ℚ, a, b]) * (w : ℍ[ℚ, a, b]) - 1 = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) :
    ∃ L₀ : Submodule ℤ ℍ[ℚ, a, b], L₀ ≤ Λ ∧ (∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀) ∧
      (∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀) ∧
      L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 ∧

      (∀ z : ℍ[ℚ, a, b], z ∈ L₀ ↔ z ∈ Λ ∧ z * (w : ℍ[ℚ, a, b]) ∈ J) ∧

      (∀ x : ℍ[ℚ, a, b], x ∈ J ↔
        ∃ z ∈ L₀, ∃ y : ↥Λ, x = z * (w : ℍ[ℚ, a, b]) + (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_exists_submodule_forall_mem_iff_mul_mem_relIndex_eq_sq_of_mul_sub_one_eq_smul.solution
