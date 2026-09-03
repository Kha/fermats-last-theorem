import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import P2M.Util
import P2M.Sol.S_DoubleComplex_subsingleton_HTot_of_colContraction

set_option autoImplicit false

universe u

theorem DoubleComplex.subsingleton_HTot_of_colContraction
    {R : Type u} [CommRing R] (T : DoubleComplex.Bounded R)
    (s : ∀ p q : ℕ, T.C p (q + 1) →ₗ[R] T.C p q)
    (h0 : ∀ (p : ℕ) (x : T.C p 0), s p 0 (T.dV p 0 x) = x)
    (hs : ∀ (p q : ℕ) (x : T.C p (q + 1)), s p (q + 1) (T.dV p (q + 1) x) + T.dV p q (s p q x) = x)
    (hsH : ∀ (p q : ℕ) (x : T.C p (q + 1)), s (p + 1) q (T.dH p (q + 1) x) = T.dH p q (s p q x))
    (n : ℕ) :
    Subsingleton (DoubleComplex.HTot T n) := by p2m_exact_reverting @_root_.P2MW.S_DoubleComplex_subsingleton_HTot_of_colContraction.solution
