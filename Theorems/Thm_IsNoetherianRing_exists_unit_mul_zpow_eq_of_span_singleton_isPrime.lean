import Mathlib
import P2M.Util
import P2M.Sol.S_IsNoetherianRing_exists_unit_mul_zpow_eq_of_span_singleton_isPrime

set_option autoImplicit false

theorem IsNoetherianRing.exists_unit_mul_zpow_eq_of_span_singleton_isPrime
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : (Ideal.span {π}).IsPrime) (hπ0 : π ≠ 0)
    (a : K) (hab : ∃ (m : ℕ) (b : A), a * algebraMap A K π ^ m = algebraMap A K b)
    (hac : ∃ (m : ℕ) (c : A), a⁻¹ * algebraMap A K π ^ m = algebraMap A K c) (ha0 : a ≠ 0) :
    ∃ (n : ℤ) (u : Aˣ), a = algebraMap A K (u : A) * algebraMap A K π ^ n := by p2m_exact_reverting @_root_.P2MW.S_IsNoetherianRing_exists_unit_mul_zpow_eq_of_span_singleton_isPrime.solution
