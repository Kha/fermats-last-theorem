import Mathlib
import P2M.Util
import P2M.Sol.S_SetLike_GradedMonoid_eq_zero_of_mem_two_of_map_eq_add_of_kunneth_injective

set_option autoImplicit false

open scoped TensorProduct DirectSum

universe u
theorem SetLike.GradedMonoid.eq_zero_of_mem_two_of_map_eq_add_of_kunneth_injective
    {k : Type u} [Field k] {H : Type u} [Ring H] [Algebra k H]
    {H' : Type u} [Ring H'] [Algebra k H']
    (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜] (p₁ p₂ m : H →ₐ[k] H')
    (hK : Function.Injective (DirectSum.toModule k (ℕ × ℕ) H' fun ab : ℕ × ℕ =>
      LinearMap.mul' k H' ∘ₗ
        TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 ab.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 ab.2).subtype)))
    (hanti : ∀ x ∈ 𝒜 1, ∀ y ∈ 𝒜 1, p₂ x * p₁ y = -(p₁ y * p₂ x))
    (hcomm : ∀ x ∈ 𝒜 2, ∀ y ∈ 𝒜 1, p₂ x * p₁ y = p₁ y * p₂ x)
    (hm : ∀ y ∈ 𝒜 1, m y = p₁ y + p₂ y)
    {d : ℕ} (a : Fin d → H) (ha : ∀ i, a i ∈ 𝒜 1) (hli : LinearIndependent k a)
    (hd : ∀ n : ℕ, d < n → 𝒜 n = ⊥)
    (x : H) (hx : x ∈ 𝒜 2) (hmx : m x = p₁ x + p₂ x) :
    x = 0 := by p2m_exact_reverting @_root_.P2MW.S_SetLike_GradedMonoid_eq_zero_of_mem_two_of_map_eq_add_of_kunneth_injective.solution
