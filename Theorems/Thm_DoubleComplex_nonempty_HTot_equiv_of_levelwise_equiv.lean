import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import P2M.Util
import P2M.Sol.S_DoubleComplex_nonempty_HTot_equiv_of_levelwise_equiv

set_option autoImplicit false

universe u

theorem DoubleComplex.nonempty_HTot_equiv_of_levelwise_equiv
    {R : Type u} [CommRing R] (D D' : DoubleComplex.Bounded R)
    (e : ∀ p q : ℕ, D.C p q ≃ₗ[R] D'.C p q)
    (hH : ∀ (p q : ℕ) (x : D.C p q), e (p + 1) q (D.dH p q x) = D'.dH p q (e p q x))
    (hV : ∀ (p q : ℕ) (x : D.C p q), e p (q + 1) (D.dV p q x) = D'.dV p q (e p q x))
    (n : ℕ) :
    Nonempty (DoubleComplex.HTot D n ≃ₗ[R] DoubleComplex.HTot D' n) := by p2m_exact_reverting @_root_.P2MW.S_DoubleComplex_nonempty_HTot_equiv_of_levelwise_equiv.solution
