import Mathlib
import P2M.Util
import P2M.Sol.S_LaurentPolynomial_uniqueFactorizationMonoid

set_option autoImplicit false

open LaurentPolynomial

universe u

theorem LaurentPolynomial.uniqueFactorizationMonoid
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid R[T;T⁻¹] := by p2m_exact_reverting @_root_.P2MW.S_LaurentPolynomial_uniqueFactorizationMonoid.solution
