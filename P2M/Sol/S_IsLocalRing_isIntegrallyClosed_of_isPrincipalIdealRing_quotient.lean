module

import P2M.Sol.S_IsLocalRing_uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient
import P2M.Util
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

namespace P2MW.S_IsLocalRing_isIntegrallyClosed_of_isPrincipalIdealRing_quotient

theorem solution
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (t : A)
    [IsDomain (A ⧸ Ideal.span {t})] [IsPrincipalIdealRing (A ⧸ Ideal.span {t})] :
    IsIntegrallyClosed A := by
  haveI := IsLocalRing.uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient t
  haveI : Nonempty (GCDMonoid A) := ⟨UniqueFactorizationMonoid.toGCDMonoid A⟩
  infer_instance
end S_IsLocalRing_isIntegrallyClosed_of_isPrincipalIdealRing_quotient
end P2MW

public section
theorem IsLocalRing.isIntegrallyClosed_of_isPrincipalIdealRing_quotient
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (t : A)
    [IsDomain (A ⧸ Ideal.span {t})] [IsPrincipalIdealRing (A ⧸ Ideal.span {t})] :
    IsIntegrallyClosed A := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isIntegrallyClosed_of_isPrincipalIdealRing_quotient.solution
end
