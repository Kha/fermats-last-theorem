import Mathlib
import P2M.Util
import P2M.Sol.S_CompleteOrthogonalIdempotents_exists_forall_mul_eq_mul_pow_val_of_pow_eq_one_of_isUnit_one_sub_pow

set_option autoImplicit false

open scoped BigOperators

theorem CompleteOrthogonalIdempotents.exists_forall_mul_eq_mul_pow_val_of_pow_eq_one_of_isUnit_one_sub_pow
    {K : Type*} [AddCommGroup K] [Fintype K] [DecidableEq K] {d : ℕ} [NeZero d]
    {R : Type*} [CommRing R] (hd : IsUnit ((d : ℕ) : R)) (ζ : R) (hζ : ζ ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j))
    (e : K → K → Rˣ) (hed : ∀ k k' : K, e k k' ^ d = 1)
    (he₁ : ∀ k₁ k₂ k' : K, e (k₁ + k₂) k' = e k₁ k' * e k₂ k') (he₂ : ∀ k k₁ k₂ : K, e k (k₁ + k₂) = e k k₁ * e k k₂)
    (hee : ∀ k : K, e k k = 1) :
    ∃ ε : (K → K → ZMod d) → R, CompleteOrthogonalIdempotents ε ∧
      (∀ (B : K → K → ZMod d) (k k' : K), ε B * (e k k' : R) = ε B * ζ ^ (B k k').val) ∧
      (∀ B : K → K → ZMod d, ε B ≠ 0 →
        (∀ k₁ k₂ k' : K, B (k₁ + k₂) k' = B k₁ k' + B k₂ k') ∧ (∀ k k₁ k₂ : K, B k (k₁ + k₂) = B k k₁ + B k k₂) ∧
        (∀ k : K, B k k = 0)) := by p2m_exact_reverting @_root_.P2MW.S_CompleteOrthogonalIdempotents_exists_forall_mul_eq_mul_pow_val_of_pow_eq_one_of_isUnit_one_sub_pow.solution
