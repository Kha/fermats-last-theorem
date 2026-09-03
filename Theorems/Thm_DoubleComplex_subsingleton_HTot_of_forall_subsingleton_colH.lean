import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import P2M.Util
import P2M.Sol.S_DoubleComplex_subsingleton_HTot_of_forall_subsingleton_colH

set_option autoImplicit false

universe u

theorem DoubleComplex.subsingleton_HTot_of_forall_subsingleton_colH
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R)
    (h : ∀ p q : ℕ, Subsingleton (DoubleComplex.colH D p q)) (n : ℕ) :
    Subsingleton (DoubleComplex.HTot D n) := by p2m_exact_reverting @_root_.P2MW.S_DoubleComplex_subsingleton_HTot_of_forall_subsingleton_colH.solution
