import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_pushforwardUnit_unit_retraction_of_finrank_eq_of_isUnit

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.exists_affHom_pushforwardUnit_unit_retraction_of_finrank_eq_of_isUnit
    {R : Type u} [CommRing R] {V W : Scheme.{u}} (π : V ⟶ Spec (.of R))
    (γ : W ⟶ V) [IsFinite γ] [Flat γ] [LocallyOfFinitePresentation γ]
    (d : ℕ) (hd : ∀ x : V, γ.finrank x = d) (hdu : IsUnit ((d : ℕ) : R)) :
    ∃ r : OModulePresheaf.AffHom (OModulePresheaf.pushforwardUnit π γ) (OModulePresheaf.unit π),
      ∀ (U : V.affineOpens) (a : Γ(V, U.1)),
        r.app U (show (OModulePresheaf.pushforwardUnit π γ).obj U.1 from
            (γ.appLE U.1 (γ ⁻¹ᵁ U.1) le_rfl).hom a) =
          (show (OModulePresheaf.unit π).obj U.1 from a) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_pushforwardUnit_unit_retraction_of_finrank_eq_of_isUnit.solution
