import Mathlib
import P2M.Util
import P2M.Sol.S_SetLike_GradedMonoid_listProd_ne_zero_of_linearIndependent_of_kunneth_injective

set_option autoImplicit false

open scoped TensorProduct DirectSum

universe u

theorem SetLike.GradedMonoid.listProd_ne_zero_of_linearIndependent_of_kunneth_injective
    {k : Type u} [Field k] {H : Type u} [Ring H] [Algebra k H] [Nontrivial H]
    {H' : Type u} [Ring H'] [Algebra k H']
    (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜] (p₁ p₂ m : H →ₐ[k] H')
    (hK : Function.Injective (DirectSum.toModule k (ℕ × ℕ) H' fun ab : ℕ × ℕ =>
      LinearMap.mul' k H' ∘ₗ
        TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 ab.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 ab.2).subtype)))
    (hanti : ∀ x ∈ 𝒜 1, ∀ y ∈ 𝒜 1, p₂ x * p₁ y = -(p₁ y * p₂ x))
    (hm : ∀ x ∈ 𝒜 1, m x = p₁ x + p₂ x)
    {n : ℕ} (x : Fin n → H) (hx : ∀ i, x i ∈ 𝒜 1) (hli : LinearIndependent k x) :
    (List.ofFn x).prod ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_SetLike_GradedMonoid_listProd_ne_zero_of_linearIndependent_of_kunneth_injective.solution
