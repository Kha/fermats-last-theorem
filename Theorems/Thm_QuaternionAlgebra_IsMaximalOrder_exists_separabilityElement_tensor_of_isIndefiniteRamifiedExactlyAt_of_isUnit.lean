import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_separabilityElement_tensor_of_isIndefiniteRamifiedExactlyAt_of_isUnit
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open QuaternionAlgebra hiding exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne

universe u v

theorem QuaternionAlgebra.IsMaximalOrder.exists_separabilityElement_tensor_of_isIndefiniteRamifiedExactlyAt_of_isUnit
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {R : Type v} [Ring R] (θ : R →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (S : Type u) [CommRing S] (hqq'u : IsUnit ((q * q' : ℕ) : S)) :
    ∃ e : (S ⊗[ℤ] R) ⊗[S] (S ⊗[ℤ] R),
      LinearMap.mul' S (S ⊗[ℤ] R) e = 1 ∧
      ∀ x : S ⊗[ℤ] R, TensorProduct.map (LinearMap.mulLeft S x) LinearMap.id e =
        TensorProduct.map LinearMap.id (LinearMap.mulRight S x) e := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_separabilityElement_tensor_of_isIndefiniteRamifiedExactlyAt_of_isUnit.solution
