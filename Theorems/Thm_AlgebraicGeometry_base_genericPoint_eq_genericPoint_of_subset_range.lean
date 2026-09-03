import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_base_genericPoint_eq_genericPoint_of_subset_range

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.base_genericPoint_eq_genericPoint_of_subset_range
    {Z X : Scheme.{u}} [IrreducibleSpace ↥Z] [IsIntegral X] (q : Z ⟶ X) (U : X.Opens)
    (hU : (U : Set ↥X).Nonempty) (hsub : (U : Set ↥X) ⊆ Set.range q.base) :
    q.base (genericPoint ↥Z) = genericPoint ↥X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_base_genericPoint_eq_genericPoint_of_subset_range.solution
