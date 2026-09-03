import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_maximalIdeal_eq_span_one_sub_of_isPrimitiveRoot

set_option autoImplicit false

theorem IsDiscreteValuationRing.maximalIdeal_eq_span_one_sub_of_isPrimitiveRoot
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (z : A) (hz : algebraMap A L z = ζ) :
    IsLocalRing.maximalIdeal A = Ideal.span {1 - z} := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_maximalIdeal_eq_span_one_sub_of_isPrimitiveRoot.solution
