import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_algHom_of_finite_of_valuationRing_of_isAlgClosed

set_option autoImplicit false

theorem AlgebraicGeometry.exists_algHom_of_finite_of_valuationRing_of_isAlgClosed
    (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (hC : IsAlgClosed (FractionRing R))
    (D : Type) [CommRing D] [Algebra R D] [Module.Finite R D]
    (hD : Nontrivial (TensorProduct R (FractionRing R) D)) :
    Nonempty (D →ₐ[R] R) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_algHom_of_finite_of_valuationRing_of_isAlgClosed.solution
