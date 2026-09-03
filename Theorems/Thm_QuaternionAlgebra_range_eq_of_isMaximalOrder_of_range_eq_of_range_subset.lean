import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_range_eq_of_isMaximalOrder_of_range_eq_of_range_subset

set_option autoImplicit false
open scoped Quaternion

theorem QuaternionAlgebra.range_eq_of_isMaximalOrder_of_range_eq_of_range_subset
    {a b : ℚ} {E : Type*} [Ring E] (θ θ' : E →+* ℍ[ℚ, a, b])
    (hθ : Function.Injective θ) (hθ' : Function.Injective θ')
    {Λ' Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ' : QuaternionAlgebra.IsMaximalOrder Λ') (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    (hrange : Set.range θ = (Λ' : Set ℍ[ℚ, a, b])) (hsub : Set.range θ' ⊆ (Λ : Set ℍ[ℚ, a, b])) :
    Set.range θ' = (Λ : Set ℍ[ℚ, a, b]) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_range_eq_of_isMaximalOrder_of_range_eq_of_range_subset.solution
