import Mathlib
import Definitions.Def_GaloisRep_StrictOrdinary
import Theorems.Thm_GaloisRepAdic_isStrictOrdinaryAt_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_isUnramifiedAt_baseChangeAlong
import P2M.Util
namespace P2MW.S_GaloisRepAdic_strictOrdinaryCondition_baseChangeAlong

set_option autoImplicit false

theorem solution
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A] [Algebra 𝒪 B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A) {p : ℕ} {S : Finset ℕ}
    (h : GaloisRep.strictOrdinaryCondition 𝒪 p S ρ) :
    GaloisRep.strictOrdinaryCondition 𝒪 p S (ρ.baseChangeAlong φ hφ) :=
  ⟨GaloisRepAdic.detIsCyclotomic_baseChangeAlong φ hφ ρ h.1,
    GaloisRepAdic.isStrictOrdinaryAt_baseChangeAlong φ hφ ρ h.2.1,
    fun q hq hqS => GaloisRepAdic.isUnramifiedAt_baseChangeAlong φ hφ ρ (h.2.2 q hq hqS)⟩
