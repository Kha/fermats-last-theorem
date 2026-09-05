module

public import Mathlib
public import P2M.Util
public import P2M.Sol.S_IsLocalRing_isIntegrallyClosed_of_isPrincipalIdealRing_quotient

@[expose] public section

theorem IsLocalRing.isIntegrallyClosed_of_isPrincipalIdealRing_quotient
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (t : A)
    [IsDomain (A ⧸ Ideal.span {t})] [IsPrincipalIdealRing (A ⧸ Ideal.span {t})] :
    IsIntegrallyClosed A := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isIntegrallyClosed_of_isPrincipalIdealRing_quotient.solution
