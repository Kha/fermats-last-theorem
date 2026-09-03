import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_hom_comp_eq_and_comp_eq_of_isProper_of_isDiscreteValuationRing_stalk

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk Topology"

theorem AlgebraicGeometry.exists_hom_comp_eq_and_comp_eq_of_isProper_of_isDiscreteValuationRing_stalk
    {κ : Type u} [Field κ] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of κ)) [IsReduced X] [IsLocallyNoetherian X]
    (g : Y ⟶ Spec (CommRingCat.of κ)) [IsProper g]
    (U : X.Opens) (φ : (U : Scheme.{u}) ⟶ Y) (hφ : φ ≫ g = U.ι ≫ f)
    (hval : ∀ x : X, x ∉ U →
      (∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing (X.presheaf.stalk x)) ∧
        ∃ y : X, y ∈ U ∧ y ⤳ x) :
    ∃ τ : X ⟶ Y, τ ≫ g = f ∧ U.ι ≫ τ = φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_hom_comp_eq_and_comp_eq_of_isProper_of_isDiscreteValuationRing_stalk.solution
