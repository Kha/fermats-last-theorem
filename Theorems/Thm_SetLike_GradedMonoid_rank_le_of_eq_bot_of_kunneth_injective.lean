import Mathlib
import P2M.Util
import P2M.Sol.S_SetLike_GradedMonoid_rank_le_of_eq_bot_of_kunneth_injective

set_option autoImplicit false

open scoped TensorProduct DirectSum

universe u

theorem SetLike.GradedMonoid.rank_le_of_eq_bot_of_kunneth_injective
    {k : Type u} [Field k] {H : Type u} [Ring H] [Algebra k H]
    {H' : Type u} [Ring H'] [Algebra k H']
    (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜] (p₁ p₂ m : H →ₐ[k] H')
    (hK : Function.Injective (DirectSum.toModule k (ℕ × ℕ) H' fun ab : ℕ × ℕ =>
      LinearMap.mul' k H' ∘ₗ
        TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 ab.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 ab.2).subtype)))
    (hanti : ∀ x ∈ 𝒜 1, ∀ y ∈ 𝒜 1, p₂ x * p₁ y = -(p₁ y * p₂ x))
    (hm : ∀ x ∈ 𝒜 1, m x = p₁ x + p₂ x)
    {d : ℕ} (hd : 𝒜 (d + 1) = ⊥) :
    Module.rank k ↥(𝒜 1) ≤ d := by p2m_exact_reverting @_root_.P2MW.S_SetLike_GradedMonoid_rank_le_of_eq_bot_of_kunneth_injective.solution
