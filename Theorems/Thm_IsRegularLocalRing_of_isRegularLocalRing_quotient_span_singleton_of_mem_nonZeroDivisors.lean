import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_of_isRegularLocalRing_quotient_span_singleton_of_mem_nonZeroDivisors

set_option autoImplicit false

open IsLocalRing

theorem IsRegularLocalRing.of_isRegularLocalRing_quotient_span_singleton_of_mem_nonZeroDivisors
    {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (ϖ : S) (hϖ : ϖ ∈ maximalIdeal S) (hreg : ϖ ∈ nonZeroDivisors S)
    (hfib : IsRegularLocalRing (S ⧸ Ideal.span {ϖ})) :
    IsRegularLocalRing S ∧ ringKrullDim S = ringKrullDim (S ⧸ Ideal.span {ϖ}) + 1 ∧
      (ringKrullDim (S ⧸ Ideal.span {ϖ}) = 1 → ∃ t : S, maximalIdeal S = Ideal.span {ϖ, t}) := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_of_isRegularLocalRing_quotient_span_singleton_of_mem_nonZeroDivisors.solution
