import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isOpenImmersion_and_isClosedImmersion_of_comp_eq_id

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isOpenImmersion_and_isClosedImmersion_of_comp_eq_id
    {S T : Scheme.{u}} (g : T ⟶ S) [LocallyOfFiniteType g] [FormallyUnramified g] [IsSeparated g]
    (s : S ⟶ T) (hs : s ≫ g = 𝟙 S) :
    IsOpenImmersion s ∧ IsClosedImmersion s := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isOpenImmersion_and_isClosedImmersion_of_comp_eq_id.solution
