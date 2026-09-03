import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

theorem AlgebraicGeometry.GeometricallyReduced.of_isReduced_of_perfectField
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [IsReduced X] :
    GeometricallyReduced f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField.solution
