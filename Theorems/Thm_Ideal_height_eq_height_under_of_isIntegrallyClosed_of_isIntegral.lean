import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral

universe u
theorem Ideal.height_eq_height_under_of_isIntegrallyClosed_of_isIntegral
    (P B : Type u) [CommRing P] [IsDomain P] [IsNoetherianRing P] [IsIntegrallyClosed P]
    [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra P B] [FaithfulSMul P B]
    [Algebra.IsIntegral P B] (q : Ideal B) [q.IsPrime] :
    q.height = (q.under P).height := by p2m_exact_reverting @_root_.P2MW.S_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral.solution
