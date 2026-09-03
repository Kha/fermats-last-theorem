import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_forall_add_sub_eq_zero_of_map_mul_of_separabilityElement_tensor

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem Algebra.exists_forall_add_sub_eq_zero_of_map_mul_of_separabilityElement_tensor
    (k : Type u) [CommRing k] (Λ : Type v) [Ring Λ]

    (e : (k ⊗[ℤ] Λ) ⊗[k] (k ⊗[ℤ] Λ))
    (he₁ : LinearMap.mul' k (k ⊗[ℤ] Λ) e = 1)
    (he₂ : ∀ x : k ⊗[ℤ] Λ, _root_.TensorProduct.map (LinearMap.mulLeft k x) LinearMap.id e =
      _root_.TensorProduct.map LinearMap.id (LinearMap.mulRight k x) e)

    (M : Type w) [AddCommGroup M] [Module k M]
    (θ : Λ →+* Module.End k M) (ρ : Λᵐᵒᵖ →+* Module.End k M)
    (hθρ : ∀ (x : Λ) (y : Λᵐᵒᵖ), (θ x).comp (ρ y) = (ρ y).comp (θ x))

    (o : Λ →+ M) (ho : ∀ x y : Λ, o (x * y) = θ x (o y) + ρ (MulOpposite.op y) (o x)) :
    ∃ ξ : M, ∀ x : Λ, o x + θ x ξ - ρ (MulOpposite.op x) ξ = 0 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_forall_add_sub_eq_zero_of_map_mul_of_separabilityElement_tensor.solution
