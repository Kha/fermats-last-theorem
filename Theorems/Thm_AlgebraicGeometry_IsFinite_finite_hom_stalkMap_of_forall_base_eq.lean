import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsFinite_finite_hom_stalkMap_of_forall_base_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.IsFinite.finite_hom_stalkMap_of_forall_base_eq
    {X Y : Scheme} (f : X ⟶ Y) [IsFinite f] (x : X)
    (hx : ∀ x' : X, f.base x' = f.base x → x' = x) :
    (f.stalkMap x).hom.Finite := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsFinite_finite_hom_stalkMap_of_forall_base_eq.solution
