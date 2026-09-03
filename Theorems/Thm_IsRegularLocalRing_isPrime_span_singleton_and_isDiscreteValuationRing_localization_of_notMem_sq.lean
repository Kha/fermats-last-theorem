import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_isPrime_span_singleton_and_isDiscreteValuationRing_localization_of_notMem_sq
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open IsLocalRing

theorem IsRegularLocalRing.isPrime_span_singleton_and_isDiscreteValuationRing_localization_of_notMem_sq
    (R : Type) [CommRing R] [IsDomain R] [IsRegularLocalRing R] [IsRegularRing R]
    (x : R) (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) (hx0 : x ≠ 0) :
    ∃ hP : (Ideal.span {x}).IsPrime, (Ideal.span {x}).height = 1 ∧
      @IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {x}) (hp := hP)) _ _ := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_isPrime_span_singleton_and_isDiscreteValuationRing_localization_of_notMem_sq.solution
