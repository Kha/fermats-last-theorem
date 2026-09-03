import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIso_morphismRestrict_of_isOpenImmersion_of_range_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.isIso_morphismRestrict_of_isOpenImmersion_of_range_eq
    {P P' : Scheme.{u}} (β : P' ⟶ P) (U : P.Opens) (s : (U : Scheme.{u}) ⟶ P') [IsOpenImmersion s]
    (hsβ : s ≫ β = U.ι) (hsr : Set.range s.base = β.base ⁻¹' (U : Set P)) :
    IsIso (β ∣_ U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_morphismRestrict_of_isOpenImmersion_of_range_eq.solution
