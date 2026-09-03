import Definitions.Def_CerednikDrinfeld_QMModuliProps
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_lineImage_classification
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry open QuaternionAlgebra hiding exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne open CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem QuaternionAlgebra.IsMaximalOrder.lineImage_classification
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (M : Type) [AddCommGroup M] (ρ : ↥Λ → M →+ M)
    (ρ_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = AddMonoidHom.id M)
    (ρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y))
    (ρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y)
    (P₀ : M) (hgen : ∀ P : M, ∃ m : ↥Λ, P = ρ m P₀)
    (hann : ∀ m : ↥Λ, ρ m P₀ = 0 ↔ ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) :

    (∀ J : Submodule ℤ ℍ[ℚ, a, b], (J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
          (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) →
      (∃ e : ZMod ℓ × ZMod ℓ ≃ {P : M // (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀)},
          ∀ x y : ZMod ℓ × ZMod ℓ, ((e (x + y) : {P : M // (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀)}) : M) = (e x : M) + (e y : M)) ∧
      (∀ (n : ↥Λ) (P : M), (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀) → (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ ρ n P = ρ m P₀))) ∧

    (∀ J J' : Submodule ℤ ℍ[ℚ, a, b], (J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
          (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) → (J' ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J') ∧ (∀ m ∈ Λ, ∀ x ∈ J', m * x ∈ J') ∧
          (∃ x ∈ J', ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J' ≠ Λ) → J ≠ J' →
      ∀ P : M, (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀) → (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J' ∧ P = ρ m P₀) → P = 0) ∧

    (∀ S : AddSubgroup M, (∀ (n : ↥Λ) (P : M), P ∈ S → ρ n P ∈ S) →
      (∃ e : ZMod ℓ × ZMod ℓ ≃ S, ∀ x y : ZMod ℓ × ZMod ℓ, ((e (x + y) : S) : M) = (e x : M) + (e y : M)) →
      ∃! J : Submodule ℤ ℍ[ℚ, a, b], (J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
          (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) ∧ ∀ P : M, P ∈ S ↔ (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀)) ∧

    (∀ T : AddSubgroup M, (∀ (n : ↥Λ) (P : M), P ∈ T → ρ n P ∈ T) →
      ∀ J : Submodule ℤ ℍ[ℚ, a, b], (J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
          (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) →
        (∀ P : M, (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀) → P ∈ T → P = 0) ∨ (∀ P : M, (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀) → P ∈ T)) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_lineImage_classification.solution
