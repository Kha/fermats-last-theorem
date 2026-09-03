import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_surjective_of_isFinite_of_smoothOfRelativeDimension_one

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.surjective_of_isFinite_of_smoothOfRelativeDimension_one
    {k : Type u} [Field k] {C U : Scheme.{u}}
    (πC : C ⟶ Spec (CommRingCat.of k)) (πU : U ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsIntegral U]
    [SmoothOfRelativeDimension 1 πC] [SmoothOfRelativeDimension 1 πU]
    (c : C ⟶ U) (hc : c ≫ πU = πC) [IsFinite c] :
    Function.Surjective c.base := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_surjective_of_isFinite_of_smoothOfRelativeDimension_one.solution
