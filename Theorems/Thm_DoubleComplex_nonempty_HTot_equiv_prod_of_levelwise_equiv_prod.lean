import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import P2M.Util
import P2M.Sol.S_DoubleComplex_nonempty_HTot_equiv_prod_of_levelwise_equiv_prod

set_option autoImplicit false

universe u

theorem DoubleComplex.nonempty_HTot_equiv_prod_of_levelwise_equiv_prod
    {R : Type u} [CommRing R] (S A B : DoubleComplex.Bounded R)
    (e : ∀ p q : ℕ, S.C p q ≃ₗ[R] (A.C p q × B.C p q))
    (hH : ∀ (p q : ℕ) (x : S.C p q), e (p + 1) q (S.dH p q x) = (A.dH p q (e p q x).1, B.dH p q (e p q x).2))
    (hV : ∀ (p q : ℕ) (x : S.C p q), e p (q + 1) (S.dV p q x) = (A.dV p q (e p q x).1, B.dV p q (e p q x).2))
    (n : ℕ) :
    Nonempty (DoubleComplex.HTot S n ≃ₗ[R] (DoubleComplex.HTot A n × DoubleComplex.HTot B n)) := by p2m_exact_reverting @_root_.P2MW.S_DoubleComplex_nonempty_HTot_equiv_prod_of_levelwise_equiv_prod.solution
