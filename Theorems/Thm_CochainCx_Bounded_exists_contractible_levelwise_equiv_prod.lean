import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import P2M.Util
import P2M.Sol.S_CochainCx_Bounded_exists_contractible_levelwise_equiv_prod

set_option autoImplicit false

universe u

theorem CochainCx.Bounded.exists_contractible_levelwise_equiv_prod
    {k : Type u} [Field k] (C : CochainCx.Bounded k) :
    ∃ (E : CochainCx.Bounded k) (σ : ∀ p : ℕ, E.X (p + 1) →ₗ[k] E.X p)
      (_ : ∀ x : E.X 0, σ 0 (E.d 0 x) = x)
      (_ : ∀ (p : ℕ) (x : E.X (p + 1)), σ (p + 1) (E.d (p + 1) x) + E.d p (σ p x) = x)
      (e : ∀ p : ℕ, C.X p ≃ₗ[k] (C.H p × E.X p)),
      ∀ (p : ℕ) (x : C.X p), e (p + 1) (C.d p x) = (0, E.d p (e p x).2) := by p2m_exact_reverting @_root_.P2MW.S_CochainCx_Bounded_exists_contractible_levelwise_equiv_prod.solution
