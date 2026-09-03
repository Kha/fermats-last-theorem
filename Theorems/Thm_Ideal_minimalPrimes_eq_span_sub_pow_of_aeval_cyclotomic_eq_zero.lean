import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_minimalPrimes_eq_span_sub_pow_of_aeval_cyclotomic_eq_zero

set_option autoImplicit false

theorem Ideal.minimalPrimes_eq_span_sub_pow_of_aeval_cyclotomic_eq_zero
    (A₀ R : Type) [CommRing A₀] [CommRing R] [Algebra A₀ R]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : A₀)) (ω : A₀) (hω : IsPrimitiveRoot ω ℓ)

    (hωu : ∀ i j : ℕ, i < ℓ → j < ℓ → i ≠ j → IsUnit (ω ^ i - ω ^ j))
    (ξ : R) (hξ : Polynomial.aeval ξ (Polynomial.cyclotomic ℓ A₀) = 0) :

    (∀ 𝔭 ∈ (⊥ : Ideal R).minimalPrimes, ∃! j : ℕ, (1 ≤ j ∧ j < ℓ) ∧ ξ - algebraMap A₀ R (ω ^ j) ∈ 𝔭) ∧

    (∀ j : ℕ, 1 ≤ j → j < ℓ → IsDomain (R ⧸ Ideal.span {ξ - algebraMap A₀ R (ω ^ j)}) →
      Ideal.span {ξ - algebraMap A₀ R (ω ^ j)} ∈ (⊥ : Ideal R).minimalPrimes ∧
      ∀ 𝔭 ∈ (⊥ : Ideal R).minimalPrimes, ξ - algebraMap A₀ R (ω ^ j) ∈ 𝔭 → 𝔭 = Ideal.span {ξ - algebraMap A₀ R (ω ^ j)}) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_minimalPrimes_eq_span_sub_pow_of_aeval_cyclotomic_eq_zero.solution
