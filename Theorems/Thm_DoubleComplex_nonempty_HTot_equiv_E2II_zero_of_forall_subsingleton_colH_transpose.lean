import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import P2M.Util
import P2M.Sol.S_DoubleComplex_nonempty_HTot_equiv_E2II_zero_of_forall_subsingleton_colH_transpose

set_option autoImplicit false

universe u

theorem DoubleComplex.nonempty_HTot_equiv_E2II_zero_of_forall_subsingleton_colH_transpose
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R)
    (hex : ∀ p q : ℕ, Subsingleton (DoubleComplex.colH (DoubleComplex.transpose D) q (p + 1)))
    (n : ℕ) :
    Nonempty (DoubleComplex.HTot D n ≃ₗ[R] DoubleComplex.E₂II D 0 n) := by p2m_exact_reverting @_root_.P2MW.S_DoubleComplex_nonempty_HTot_equiv_E2II_zero_of_forall_subsingleton_colH_transpose.solution
