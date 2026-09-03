import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_tangentFinite_unramifiedOutside

open IsLocalRing
theorem GaloisRep.tangentFinite_unramifiedOutside (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    [Finite (ResidueField 𝒪)] (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (S : Finset ℕ) :
    TangentFinite 𝒪 ρbar (fun _A _ _ _ ρ => ∀ q : ℕ, q.Prime → q ∉ S → ρ.IsUnramifiedAt q) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_tangentFinite_unramifiedOutside.solution
