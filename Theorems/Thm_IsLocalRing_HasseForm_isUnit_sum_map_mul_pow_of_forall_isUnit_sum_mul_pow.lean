import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_HasseForm_isUnit_sum_map_mul_pow_of_forall_isUnit_sum_mul_pow

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.HasseForm.isUnit_sum_map_mul_pow_of_forall_isUnit_sum_mul_pow
    (q : ℕ) [Fact q.Prime]
    {W₁ W₂ : Type*} [CommRing W₁] [IsLocalRing W₁] [CommRing W₂] [IsLocalRing W₂]
    (hq₁ : (q : W₁) ∈ maximalIdeal W₁)
    (ρ : W₁ →+* W₂) (hρ : ∀ x ∈ maximalIdeal W₁, ρ x ∈ maximalIdeal W₂)
    (e₀ : ℕ) (c : ℕ → W₁)
    (hunit : ∀ a b : W₁, (a ∉ maximalIdeal W₁ ∨ b ∉ maximalIdeal W₁) →
      a ^ q * b - a * b ^ q ∈ maximalIdeal W₁ →
        IsUnit (∑ i ∈ Finset.range (e₀ + 1), c i * a ^ i * b ^ (e₀ - i))) :
    ∀ a b : W₂, (a ∉ maximalIdeal W₂ ∨ b ∉ maximalIdeal W₂) →
      a ^ q * b - a * b ^ q ∈ maximalIdeal W₂ →
        IsUnit (∑ i ∈ Finset.range (e₀ + 1), ρ (c i) * a ^ i * b ^ (e₀ - i)) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_HasseForm_isUnit_sum_map_mul_pow_of_forall_isUnit_sum_mul_pow.solution
