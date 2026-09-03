import Mathlib
import P2M.Util
import P2M.Sol.S_Finite_exists_isUnit_prod_pow_apply_eq_of_isReduced_of_prime

set_option autoImplicit false

theorem Finite.exists_isUnit_prod_pow_apply_eq_of_isReduced_of_prime
    {R : Type*} [CommRing R] [Finite R] [IsReduced R]
    (τ : R ≃+* R) (ℓ : ℕ) (hℓ : ℓ.Prime) (hτℓ : τ ^ ℓ = 1)
    (hmax : ∀ m : Ideal R, m.IsMaximal → (∀ x ∈ m, τ x ∈ m) → ∃ x, τ x - x ∉ m)
    (c : R) (hc : IsUnit c) (hτc : τ c = c) :
    ∃ u : R, IsUnit u ∧ ∏ i ∈ Finset.range ℓ, (τ ^ i) u = c := by p2m_exact_reverting @_root_.P2MW.S_Finite_exists_isUnit_prod_pow_apply_eq_of_isReduced_of_prime.solution
