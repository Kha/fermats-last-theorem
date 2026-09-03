import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import P2M.Util
import P2M.Sol.S_Deformation_HondaSystem_comap_L_eq_of_injective_of_map_L_le

universe u

theorem Deformation.HondaSystem.comap_L_eq_of_injective_of_map_L_le
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ℓ : A}
    (hℓ : IsLocalRing.maximalIdeal A = Ideal.span {ℓ}) {r : ℕ}
    (H₁ H₂ : Deformation.HondaSystem ℓ (Fin r → A))
    (φ : (Fin r → A) →ₗ[A] (Fin r → A)) (hφ : Function.Injective φ)
    (hφF : φ ∘ₗ H₂.F = H₁.F ∘ₗ φ) (hφV : φ ∘ₗ H₂.V = H₁.V ∘ₗ φ)
    (hφL : Submodule.map φ H₂.L ≤ H₁.L) :
    Submodule.comap φ H₁.L = H₂.L := by p2m_exact_reverting @_root_.P2MW.S_Deformation_HondaSystem_comap_L_eq_of_injective_of_map_L_le.solution
