import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_dvd_ramificationIdx_of_pow_eq_unit_mul_zpow_of_isCoprime

set_option autoImplicit false

theorem Ideal.dvd_ramificationIdx_of_pow_eq_unit_mul_zpow_of_isCoprime
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra O R]
    {E : Type*} [Field E] [Algebra R E] [IsFractionRing R E] [Algebra O E] [IsScalarTower O R E]
    (ϖ : O) (hϖ : Irreducible ϖ) (u : Oˣ) (m : ℤ) (n : ℕ) (hn : 0 < n) (hmn : IsCoprime m (n : ℤ))
    (a : E) (hab : a ^ n = algebraMap O E (u : O) * algebraMap O E ϖ ^ m)
    (𝔓 : Ideal R) [𝔓.IsPrime] (h𝔓 : 𝔓 ≠ ⊥) [𝔓.LiesOver (IsLocalRing.maximalIdeal O)] :
    n ∣ (IsLocalRing.maximalIdeal O).ramificationIdx' 𝔓 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_dvd_ramificationIdx_of_pow_eq_unit_mul_zpow_of_isCoprime.solution
