import Definitions.Def_CerednikDrinfeld_QMModuliProps
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_natCard_levelLift_eq_of_dvd
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry open QuaternionAlgebra hiding exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne open CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem QuaternionAlgebra.IsMaximalOrder.natCard_levelLift_eq_of_dvd
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') {N : ℕ} [NeZero N] (hℓN : ℓ ∣ N)
    (M : Type) [AddCommGroup M] (ρ : ↥Λ → M →+ M)
    (ρ_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = AddMonoidHom.id M)
    (ρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y))
    (ρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y)
    (P₀ : M) (hgen : ∀ P : M, ∃ m : ↥Λ, P = ρ m P₀)
    (hann : ∀ m : ↥Λ, ρ m P₀ = 0 ↔
      ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = (((N * ℓ : ℕ) : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]))
    (C : AddSubgroup M) (hC : ∀ (n : ↥Λ) (P : M), P ∈ C → ρ n P ∈ C)
    (eC : ZMod N × ZMod N ≃ C) (heC : ∀ x y : ZMod N × ZMod N, ((eC (x + y) : C) : M) = (eC x : M) + (eC y : M))
    (S₀ : AddSubgroup M) (hS₀ : ∀ (n : ↥Λ) (P : M), P ∈ S₀ → ρ n P ∈ S₀)
    (eS₀ : ZMod (N * ℓ) × ZMod (N * ℓ) ≃ S₀)
    (heS₀ : ∀ x y : ZMod (N * ℓ) × ZMod (N * ℓ), ((eS₀ (x + y) : S₀) : M) = (eS₀ x : M) + (eS₀ y : M))
    (hS₀C : ∀ Q : M, Q ∈ S₀ → ℓ • Q ∈ C) :
    Nat.card {S : AddSubgroup M //
        (∀ (n : ↥Λ) (P : M), P ∈ S → ρ n P ∈ S) ∧
        (∀ P : M, P ∈ C ↔ ∃ Q ∈ S, P = ℓ • Q) ∧
        (∀ P : M, P ∈ S → ℓ • P = 0 → P ∈ C)} = ℓ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_natCard_levelLift_eq_of_dvd.solution
