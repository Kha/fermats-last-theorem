import Mathlib
import Theorems.Thm_IsIntegrallyClosed_mem_minimalPrimes_of_mem_associatedPrimes
import Theorems.Thm_Ideal_isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes
import P2M.Util
namespace P2MW.S_IsIntegrallyClosed_isReduced_quotient_span_singleton_of_forall_mem_minimalPrimes

theorem solution
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    {x : A} (hx : x ≠ 0)
    (h : ∀ (P : Ideal A) [P.IsPrime], P ∈ (Ideal.span {x}).minimalPrimes →
      Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {x}) =
        IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    IsReduced (A ⧸ Ideal.span {x}) :=
  Ideal.isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes x fun P _ hP =>
    h P (IsIntegrallyClosed.mem_minimalPrimes_of_mem_associatedPrimes hx P hP)
