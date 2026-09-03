import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import P2M.Util
import P2M.Sol.S_DoubleComplex_nonempty_HTot_transpose_equiv

set_option autoImplicit false

universe u

theorem DoubleComplex.nonempty_HTot_transpose_equiv
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R) (n : ℕ) :
    Nonempty (DoubleComplex.HTot (DoubleComplex.transpose D) n ≃ₗ[R] DoubleComplex.HTot D n) := by p2m_exact_reverting @_root_.P2MW.S_DoubleComplex_nonempty_HTot_transpose_equiv.solution
