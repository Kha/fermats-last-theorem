import Mathlib
import P2M.Util
import P2M.Sol.S_IsCyclotomicExtension_exists_isUnit_pow_sub_one_eq_mul_natCast_of_isDiscreteValuationRing

set_option autoImplicit false

theorem IsCyclotomicExtension.exists_isUnit_pow_sub_one_eq_mul_natCast_of_isDiscreteValuationRing
    (q ℓ : ℕ) [Fact q.Prime] [Fact ℓ.Prime] (hqℓ : q ≠ ℓ)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) :
    ∃ ε : A, IsUnit ε ∧ ϖ ^ (q - 1) = ε * (q : A) := by p2m_exact_reverting @_root_.P2MW.S_IsCyclotomicExtension_exists_isUnit_pow_sub_one_eq_mul_natCast_of_isDiscreteValuationRing.solution
