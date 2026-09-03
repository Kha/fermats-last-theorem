import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_existsUnique_eq_smul_of_isPerfPair_of_alternating_starAdjoint

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

universe u v w

theorem QuaternionAlgebra.IsMaximalOrder.existsUnique_eq_smul_of_isPerfPair_of_alternating_starAdjoint
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (R : Type u) [CommRing R] [IsDomain R] [CharZero R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (ρ : ↥Λ → (M →ₗ[R] M))
    (ρ_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = LinearMap.id)
    (ρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ρ x ∘ₗ ρ y)
    (ρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y)
    {ι : Type w} (bΛ : Module.Basis ι ℤ ↥Λ) (e : M) (bM : Module.Basis ι R M)
    (hbM : ∀ i : ι, bM i = ρ (bΛ i) e)
    (E₀ : M →ₗ[R] M →ₗ[R] R) (h₀alt : ∀ m : M, E₀ m m = 0)
    (h₀star : ∀ (x : ↥Λ) (m n : M), E₀ (ρ x m) n = E₀ m (ρ (star x) n))
    (hperf : E₀.IsPerfPair)
    (E : M →ₗ[R] M →ₗ[R] R) (halt : ∀ m : M, E m m = 0)
    (hstarE : ∀ (x : ↥Λ) (m n : M), E (ρ x m) n = E m (ρ (star x) n)) :
    ∃! r : R, E = r • E₀ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_existsUnique_eq_smul_of_isPerfPair_of_alternating_starAdjoint.solution
