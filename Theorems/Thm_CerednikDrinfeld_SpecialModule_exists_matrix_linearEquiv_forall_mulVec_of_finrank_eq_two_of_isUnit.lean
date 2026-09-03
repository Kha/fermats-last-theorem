import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialModule_exists_matrix_linearEquiv_forall_mulVec_of_finrank_eq_two_of_isUnit
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.SpecialModule.exists_matrix_linearEquiv_forall_mulVec_of_finrank_eq_two_of_isUnit
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (k : Type) [Field k] [IsAlgClosed k] (hqq : IsUnit ((q * q' : ℕ) : k))
    (W : Type) [AddCommGroup W] [Module k W] [Module.Finite k W] (hW : Module.finrank k W = 2)
    (Ψ : ↥Λ → (W →ₗ[k] W))
    (hΨ_add : ∀ x y : ↥Λ, Ψ (x + y) = Ψ x + Ψ y)
    (hΨ_one : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, Ψ ⟨1, h1⟩ = LinearMap.id)
    (hΨ_mul : ∀ (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      Ψ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ = Ψ x ∘ₗ Ψ y) :
    ∃ (θ : ↥Λ → Matrix (Fin 2) (Fin 2) k) (e : W ≃ₗ[k] (Fin 2 → k)),
      (∀ (x : ↥Λ) (w : W), e (Ψ x w) = (θ x).mulVec (e w)) ∧
      (∀ x y : ↥Λ, θ (x + y) = θ x + θ y) ∧
      (∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, θ ⟨1, h1⟩ = 1) ∧
      (∀ (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        θ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ = θ x * θ y) ∧
      (∀ m : Matrix (Fin 2) (Fin 2) k, m ∈ Submodule.span k (Set.range θ)) ∧
      (∀ x : ↥Λ, θ (star x) = (θ μ)⁻¹ * (θ x).adjugate * θ μ) ∧
      (θ μ).trace = 0 ∧ (θ μ).det = ((q * q' : ℕ) : k) ∧
      (∀ (x : ↥Λ) (n : ℤ), (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        (θ x).trace = (n : k)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialModule_exists_matrix_linearEquiv_forall_mulVec_of_finrank_eq_two_of_isUnit.solution
