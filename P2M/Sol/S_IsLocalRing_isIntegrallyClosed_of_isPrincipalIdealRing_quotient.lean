module

public import Mathlib
public import Theorems.Thm_IsLocalRing_uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient
import P2M.Util

@[expose] public section
namespace P2MW.S_IsLocalRing_isIntegrallyClosed_of_isPrincipalIdealRing_quotient

theorem solution
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (t : A)
    [IsDomain (A ⧸ Ideal.span {t})] [IsPrincipalIdealRing (A ⧸ Ideal.span {t})] :
    IsIntegrallyClosed A := by
  haveI := IsLocalRing.uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient t
  haveI : Nonempty (GCDMonoid A) := ⟨UniqueFactorizationMonoid.toGCDMonoid A⟩
  infer_instance
