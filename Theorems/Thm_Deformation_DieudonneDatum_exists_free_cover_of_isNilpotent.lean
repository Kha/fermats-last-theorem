import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneDatum_exists_free_cover_of_isNilpotent

universe u v

theorem Deformation.DieudonneDatum.exists_free_cover_of_isNilpotent
    {A : Type u} [CommRing A] {ℓ : A} {D : Type v} [AddCommGroup D] [Module A D]
    [Module.Finite A D] (M : Deformation.DieudonneDatum ℓ D)
    (hF : IsNilpotent M.F) (hV : IsNilpotent M.V) :
    ∃ (r N k : ℕ) (M₁ : Deformation.DieudonneDatum ℓ (Fin r → A)) (π : (Fin r → A) →ₗ[A] D),
      Function.Surjective π ∧ π ∘ₗ M₁.F = M.F ∘ₗ π ∧ π ∘ₗ M₁.V = M.V ∘ₗ π ∧
      0 < k ∧ M₁.F ^ N = ℓ ^ k • LinearMap.id ∧ M₁.V ^ N = ℓ ^ k • LinearMap.id := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneDatum_exists_free_cover_of_isNilpotent.solution
