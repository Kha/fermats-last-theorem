import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneDatum_exists_free_cover_of_isNilpotent_V

universe u v

theorem Deformation.DieudonneDatum.exists_free_cover_of_isNilpotent_V
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ℓ : A}
    (hℓ : IsLocalRing.maximalIdeal A = Ideal.span {ℓ})
    {D : Type v} [AddCommGroup D] [Module A D] [IsNoetherian A D] [IsArtinian A D]
    (M : Deformation.DieudonneDatum ℓ D) (hV : IsNilpotent M.V) :
    ∃ (r N : ℕ) (M₁ : Deformation.DieudonneDatum ℓ (Fin r → A)) (π : (Fin r → A) →ₗ[A] D),
      Function.Surjective π ∧ π ∘ₗ M₁.F = M.F ∘ₗ π ∧ π ∘ₗ M₁.V = M.V ∘ₗ π ∧
      (∀ x, ∃ y, (M₁.V ^ N) x = ℓ • y) ∧ Function.Injective M₁.V := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneDatum_exists_free_cover_of_isNilpotent_V.solution
