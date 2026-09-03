import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import P2M.Util
import P2M.Sol.S_Deformation_HondaSystem_exists_hondaSystem_lifts_of_equivariant_surjective

universe u v w

theorem Deformation.HondaSystem.exists_hondaSystem_lifts_of_equivariant_surjective
    {A : Type u} [CommRing A] [IsLocalRing A] {ℓ : A}
    (hℓ : IsLocalRing.maximalIdeal A = Ideal.span {ℓ})
    {D : Type v} [AddCommGroup D] [Module A D] [IsNoetherian A D] [IsArtinian A D]
    (H : Deformation.HondaSystem ℓ D)
    {D₁ : Type w} [AddCommGroup D₁] [Module A D₁]
    (M₁ : Deformation.DieudonneDatum ℓ D₁) (hV₁ : Function.Injective M₁.V)
    (π : D₁ →ₗ[A] D) (hπ : Function.Surjective π)
    (hF : π ∘ₗ M₁.F = H.F ∘ₗ π) (hV : π ∘ₗ M₁.V = H.V ∘ₗ π) :
    ∃ (H₁ : Deformation.HondaSystem ℓ D₁)
      (H₂ : Deformation.HondaSystem ℓ ↥(LinearMap.ker π)),
      H₁.toDieudonneDatum = M₁ ∧
      (∀ x : LinearMap.ker π, (H₂.F x : D₁) = M₁.F x) ∧
      (∀ x : LinearMap.ker π, (H₂.V x : D₁) = M₁.V x) ∧
      Submodule.map (LinearMap.ker π).subtype H₂.L ≤ H₁.L ∧
      Submodule.map π H₁.L = H.L := by p2m_exact_reverting @_root_.P2MW.S_Deformation_HondaSystem_exists_hondaSystem_lifts_of_equivariant_surjective.solution
