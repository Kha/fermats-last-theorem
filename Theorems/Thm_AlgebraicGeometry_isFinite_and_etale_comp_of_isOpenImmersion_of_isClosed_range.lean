import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isFinite_and_etale_comp_of_isOpenImmersion_of_isClosed_range

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isFinite_and_etale_comp_of_isOpenImmersion_of_isClosed_range
    {V U X : Scheme.{u}} (i : V ⟶ U) [IsOpenImmersion i] (hi : IsClosed (Set.range i.base))
    (π : U ⟶ X) [IsFinite π] [AlgebraicGeometry.Etale π] :
    IsFinite (i ≫ π) ∧ AlgebraicGeometry.Etale (i ≫ π) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isFinite_and_etale_comp_of_isOpenImmersion_of_isClosed_range.solution
