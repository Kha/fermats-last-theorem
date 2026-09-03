import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_refinement_preimage_preimage_of_isSeparated

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_refinement_preimage_preimage_of_isSeparated
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
    (𝒦 : X.OrderedAffineCover) (h₁ h₂ : X ⟶ X) [IsAffineHom h₁] [IsAffineHom h₂] :
    ∃ (𝒲 : X.OrderedAffineCover) (lam₁ lam₂ : 𝒲.ι → 𝒦.ι),
      (∀ w, 𝒲.U w ≤ h₁ ⁻¹ᵁ 𝒦.U (lam₁ w)) ∧ (∀ w, 𝒲.U w ≤ h₂ ⁻¹ᵁ 𝒦.U (lam₂ w)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_refinement_preimage_preimage_of_isSeparated.solution
