import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_finrank_eq_one_of_forall_mem_iff_forall_map_tmul_eq_of_finrank_eq_two
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped Quaternion TensorProduct
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.finrank_eq_one_of_forall_mem_iff_forall_map_tmul_eq_of_finrank_eq_two
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    {k : Type*} [Field k] [CharP k ℓ]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (hV : Module.finrank k V = 2)
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W] (hW : Module.finrank k W = 2)

    (θ : ↥Λ → Module.End k V)
    (hθadd : ∀ x y : ↥Λ, θ (x + y) = θ x + θ y)
    (hθone : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, θ ⟨1, h⟩ = 1)
    (hθmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      θ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = θ x * θ y)

    (ρ : ↥Λ → Module.End k W)
    (hρadd : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y)
    (hρone : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = 1)
    (hρmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ρ y * ρ x)

    (T : Submodule k (V ⊗[k] W))
    (hT : ∀ ξ : V ⊗[k] W, ξ ∈ T ↔
      ∀ x : ↥Λ, TensorProduct.map (θ x) (LinearMap.id : W →ₗ[k] W) ξ = TensorProduct.map (LinearMap.id : V →ₗ[k] V) (ρ x) ξ) :
    Module.finrank k ↥T = 1 := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_finrank_eq_one_of_forall_mem_iff_forall_map_tmul_eq_of_finrank_eq_two.solution
