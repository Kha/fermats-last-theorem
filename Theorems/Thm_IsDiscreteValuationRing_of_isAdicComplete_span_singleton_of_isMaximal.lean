import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_of_isAdicComplete_span_singleton_of_isMaximal

set_option autoImplicit false

theorem IsDiscreteValuationRing.of_isAdicComplete_span_singleton_of_isMaximal
    (R : Type) [CommRing R] [IsDomain R] (ϖ : R) (hϖ : ϖ ≠ 0)
    (hc : IsAdicComplete (Ideal.span {ϖ}) R) (hm : (Ideal.span {ϖ}).IsMaximal) :
    IsDiscreteValuationRing R := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_of_isAdicComplete_span_singleton_of_isMaximal.solution
