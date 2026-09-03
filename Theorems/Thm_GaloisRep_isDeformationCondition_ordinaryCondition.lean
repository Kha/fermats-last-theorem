import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRep_isDeformationCondition_ordinaryCondition

theorem GaloisRep.isDeformationCondition_ordinaryCondition (𝒪 : Type) [CommRing 𝒪]
    {p : ℕ} {S : Finset ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GaloisRep.IsDeformationCondition 𝒪 (GaloisRep.ordinaryCondition 𝒪 p S) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_isDeformationCondition_ordinaryCondition.solution
