import Mathlib
import P2M.Util
import P2M.Sol.S_LaurentPolynomial_isUnit_iff_exists_C_mul_T

set_option autoImplicit false

open LaurentPolynomial

universe u

theorem LaurentPolynomial.isUnit_iff_exists_C_mul_T
    {R : Type u} [CommRing R] [IsDomain R] (f : R[T;T⁻¹]) :
    IsUnit f ↔ ∃ (c : Rˣ) (n : ℤ), f = C (c : R) * T n := by p2m_exact_reverting @_root_.P2MW.S_LaurentPolynomial_isUnit_iff_exists_C_mul_T.solution
