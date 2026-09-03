import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_tangentFinite_unramifiedOutside
import Theorems.Thm_GaloisRep_tangentFinite_of_imp
import P2M.Util
namespace P2MW.S_GaloisRep_tangentFinite_flatCondition

open IsLocalRing GaloisRep

theorem solution (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    [Finite (ResidueField 𝒪)] (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (p : ℕ) (S : Finset ℕ) :
    TangentFinite 𝒪 ρbar (flatCondition 𝒪 p S) :=
  tangentFinite_of_imp 𝒪 ρbar _ _ (fun _ _ _ _ _ hρ => hρ.2.2) (tangentFinite_unramifiedOutside 𝒪 ρbar S)
