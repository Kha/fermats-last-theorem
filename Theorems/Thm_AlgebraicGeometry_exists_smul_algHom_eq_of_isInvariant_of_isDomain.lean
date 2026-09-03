import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_smul_algHom_eq_of_isInvariant_of_isDomain

set_option autoImplicit false

theorem AlgebraicGeometry.exists_smul_algHom_eq_of_isInvariant_of_isDomain
    (A : Type) [CommRing A] (D : Type) [CommRing D] [Algebra A D]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G D] [SMulCommClass G A D] [Algebra.IsInvariant A D G]
    (R : Type) [CommRing R] [IsDomain R] [Algebra A R]
    (s s' : D →ₐ[A] R) :
    ∃ g : G, ∀ d : D, s' d = s (g • d) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_smul_algHom_eq_of_isInvariant_of_isDomain.solution
