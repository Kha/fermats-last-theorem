import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import P2M.Util
import P2M.Sol.S_Deformation_HondaSystem_exists_free_resolution_of_isNilpotent

universe u v

theorem Deformation.HondaSystem.exists_free_resolution_of_isNilpotent
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ℓ : A}
    (hℓ : IsLocalRing.maximalIdeal A = Ideal.span {ℓ})
    {D : Type v} [AddCommGroup D] [Module A D] [IsNoetherian A D] [IsArtinian A D]
    (H : Deformation.HondaSystem ℓ D) (hV : IsNilpotent H.V) :
    ∃ (r N : ℕ) (H₁ H₂ : Deformation.HondaSystem ℓ (Fin r → A))
      (φ : (Fin r → A) →ₗ[A] (Fin r → A)) (π : (Fin r → A) →ₗ[A] D),
      Function.Injective φ ∧ Function.Surjective π ∧ LinearMap.range φ = LinearMap.ker π ∧
      φ ∘ₗ H₂.F = H₁.F ∘ₗ φ ∧ φ ∘ₗ H₂.V = H₁.V ∘ₗ φ ∧
      π ∘ₗ H₁.F = H.F ∘ₗ π ∧ π ∘ₗ H₁.V = H.V ∘ₗ π ∧
      Submodule.map π H₁.L = H.L ∧ Submodule.comap φ H₁.L = H₂.L ∧
      (∀ x, ∃ y, (H₁.V ^ N) x = ℓ • y) ∧ (∀ x, ∃ y, (H₂.V ^ N) x = ℓ • y) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_HondaSystem_exists_free_resolution_of_isNilpotent.solution
