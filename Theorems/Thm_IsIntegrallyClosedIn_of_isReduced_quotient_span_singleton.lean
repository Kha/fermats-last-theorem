import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosedIn_of_isReduced_quotient_span_singleton

theorem IsIntegrallyClosedIn.of_isReduced_quotient_span_singleton
    {B : Type*} [CommRing B] (ϖ : B) (hϖ : ϖ ∈ nonZeroDivisors B)
    [IsReduced (B ⧸ Ideal.span {ϖ})]
    (L : Type*) [CommRing L] [Algebra B L] [IsLocalization.Away ϖ L] :
    IsIntegrallyClosedIn B L := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosedIn_of_isReduced_quotient_span_singleton.solution
