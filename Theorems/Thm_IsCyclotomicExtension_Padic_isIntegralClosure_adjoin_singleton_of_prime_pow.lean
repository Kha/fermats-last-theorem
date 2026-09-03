import Mathlib
import P2M.Util
import P2M.Sol.S_IsCyclotomicExtension_Padic_isIntegralClosure_adjoin_singleton_of_prime_pow

set_option autoImplicit false

theorem IsCyclotomicExtension.Padic.isIntegralClosure_adjoin_singleton_of_prime_pow
    (p : ℕ) [Fact p.Prime] (k : ℕ) (K : Type*) [Field K] [Algebra ℚ_[p] K]
    [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] [IsCyclotomicExtension {p ^ k} ℚ_[p] K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    IsIntegralClosure (Algebra.adjoin ℤ_[p] ({ζ} : Set K)) ℤ_[p] K := by p2m_exact_reverting @_root_.P2MW.S_IsCyclotomicExtension_Padic_isIntegralClosure_adjoin_singleton_of_prime_pow.solution
