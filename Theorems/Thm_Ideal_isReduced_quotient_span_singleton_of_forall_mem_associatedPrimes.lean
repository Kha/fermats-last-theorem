import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes

theorem Ideal.isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes
    {A : Type*} [CommRing A] [IsNoetherianRing A] (x : A)
    (h : ∀ (P : Ideal A) [P.IsPrime], P ∈ associatedPrimes A (A ⧸ Ideal.span {x}) →
      Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {x}) =
        IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    IsReduced (A ⧸ Ideal.span {x}) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes.solution
