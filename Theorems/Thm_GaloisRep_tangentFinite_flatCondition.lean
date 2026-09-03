import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_tangentFinite_flatCondition

open IsLocalRing
theorem GaloisRep.tangentFinite_flatCondition (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    [Finite (ResidueField 𝒪)] (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (p : ℕ) (S : Finset ℕ) :
    TangentFinite 𝒪 ρbar (flatCondition 𝒪 p S) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_tangentFinite_flatCondition.solution
