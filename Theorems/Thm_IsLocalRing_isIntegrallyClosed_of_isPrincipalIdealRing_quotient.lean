import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isIntegrallyClosed_of_isPrincipalIdealRing_quotient

theorem IsLocalRing.isIntegrallyClosed_of_isPrincipalIdealRing_quotient
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (t : A)
    [IsDomain (A ⧸ Ideal.span {t})] [IsPrincipalIdealRing (A ⧸ Ideal.span {t})] :
    IsIntegrallyClosed A := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isIntegrallyClosed_of_isPrincipalIdealRing_quotient.solution
