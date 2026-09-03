import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import P2M.Util
import P2M.Sol.S_DoubleComplex_subsingleton_HTot_of_rowContraction

set_option autoImplicit false

universe u

theorem DoubleComplex.subsingleton_HTot_of_rowContraction
    {R : Type u} [CommRing R] (T : DoubleComplex.Bounded R)
    (s : ∀ p q : ℕ, T.C (p + 1) q →ₗ[R] T.C p q)
    (h0 : ∀ (q : ℕ) (x : T.C 0 q), s 0 q (T.dH 0 q x) = x)
    (hs : ∀ (p q : ℕ) (x : T.C (p + 1) q), s (p + 1) q (T.dH (p + 1) q x) + T.dH p q (s p q x) = x)
    (hsV : ∀ (p q : ℕ) (x : T.C (p + 1) q), s p (q + 1) (T.dV (p + 1) q x) = T.dV p q (s p q x))
    (n : ℕ) :
    Subsingleton (DoubleComplex.HTot T n) := by p2m_exact_reverting @_root_.P2MW.S_DoubleComplex_subsingleton_HTot_of_rowContraction.solution
