import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.Algebra.Tower
import P2M.Util
import P2M.Sol.S_AlgHom_exists_intertwiner_of_adjoin_eq_top_of_injective

set_option autoImplicit false

theorem AlgHom.exists_intertwiner_of_adjoin_eq_top_of_injective
    {R : Type} [CommRing R]
    {C₁ C₀ : Type} [CommRing C₁] [CommRing C₀] [Algebra R C₁] [Algebra R C₀]
    {M₁ M₀ : Type} [AddCommGroup M₁] [AddCommGroup M₀] [Module R M₁] [Module R M₀]
    [Module C₁ M₁] [Module C₀ M₀] [IsScalarTower R C₁ M₁] [IsScalarTower R C₀ M₀]
    (i : M₀ →ₗ[R] M₁) (hi : Function.Injective i)
    (hfaith : ∀ y : C₀, (∀ m : M₀, y • m = 0) → y = 0)
    (G : Set C₁) (hG : Algebra.adjoin R G = ⊤)
    (y : C₁ → C₀) (hy : ∀ g ∈ G, ∀ m : M₀, g • i m = i (y g • m)) :
    ∃ res : C₁ →ₐ[R] C₀,
      (∀ (t : C₁) (m : M₀), t • i m = i (res t • m)) ∧
      (∀ g ∈ G, res g = y g) ∧
      (∀ res' : C₁ →ₐ[R] C₀, (∀ (t : C₁) (m : M₀), t • i m = i (res' t • m)) → res' = res) := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_exists_intertwiner_of_adjoin_eq_top_of_injective.solution
