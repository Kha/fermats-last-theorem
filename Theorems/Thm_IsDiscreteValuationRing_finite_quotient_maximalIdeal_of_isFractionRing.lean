import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_finite_quotient_maximalIdeal_of_isFractionRing

set_option autoImplicit false

theorem IsDiscreteValuationRing.finite_quotient_maximalIdeal_of_isFractionRing (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (L : Type*) [Field L] [CharZero L] [Algebra A L] [IsFractionRing A L] [FiniteDimensional ℚ L]
    (p : ℕ) [Fact p.Prime] (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) :
    Finite (A ⧸ IsLocalRing.maximalIdeal A) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_finite_quotient_maximalIdeal_of_isFractionRing.solution
