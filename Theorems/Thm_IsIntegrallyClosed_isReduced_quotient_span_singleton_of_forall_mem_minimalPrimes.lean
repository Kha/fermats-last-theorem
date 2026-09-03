import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_isReduced_quotient_span_singleton_of_forall_mem_minimalPrimes

theorem IsIntegrallyClosed.isReduced_quotient_span_singleton_of_forall_mem_minimalPrimes
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    {x : A} (hx : x ≠ 0)
    (h : ∀ (P : Ideal A) [P.IsPrime], P ∈ (Ideal.span {x}).minimalPrimes →
      Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {x}) =
        IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    IsReduced (A ⧸ Ideal.span {x}) := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_isReduced_quotient_span_singleton_of_forall_mem_minimalPrimes.solution
