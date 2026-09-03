import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRepAdic_isFlatAt_of_isEquiv
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_of_isEquiv
import Theorems.Thm_GaloisRepAdic_isUnramifiedAt_of_isEquiv
import P2M.Util
namespace P2MW.S_GaloisRepAdic_flatCondition_of_isEquiv

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ} {S : Finset ℕ}
    (h : GaloisRep.flatCondition 𝒪 p S ρ₁) : GaloisRep.flatCondition 𝒪 p S ρ₂ :=
  ⟨GaloisRepAdic.detIsCyclotomic_of_isEquiv e h.1, GaloisRepAdic.isFlatAt_of_isEquiv e h.2.1,
    fun q hq hqS => GaloisRepAdic.isUnramifiedAt_of_isEquiv e (h.2.2 q hq hqS)⟩
