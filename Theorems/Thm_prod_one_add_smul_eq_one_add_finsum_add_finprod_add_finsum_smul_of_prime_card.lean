import Mathlib
import P2M.Util
import P2M.Sol.S_prod_one_add_smul_eq_one_add_finsum_add_finprod_add_finsum_smul_of_prime_card

set_option autoImplicit false

theorem prod_one_add_smul_eq_one_add_finsum_add_finprod_add_finsum_smul_of_prime_card
    {B : Type*} [CommRing B] {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
    (hℓ : (Nat.card G).Prime) (γ : B) :
    ∃ δ ∈ Ideal.span {x : B | ∃ σ₁ σ₂ : G, σ₁ ≠ σ₂ ∧ x = (σ₁ • γ) * (σ₂ • γ)},
      ∏ᶠ σ : G, (1 + σ • γ) = 1 + ∑ᶠ σ : G, σ • γ + ∏ᶠ σ : G, σ • γ + ∑ᶠ σ : G, σ • δ := by p2m_exact_reverting @_root_.P2MW.S_prod_one_add_smul_eq_one_add_finsum_add_finprod_add_finsum_smul_of_prime_card.solution
