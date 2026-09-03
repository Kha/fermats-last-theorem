import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_StrictOrdinary
import P2M.Util
import P2M.Sol.S_GaloisRep_isDeformationCondition_strictOrdinaryCondition

set_option autoImplicit false
theorem GaloisRep.isDeformationCondition_strictOrdinaryCondition (𝒪 : Type) [CommRing 𝒪]
    {p : ℕ} {S : Finset ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GaloisRep.IsDeformationCondition 𝒪 (GaloisRep.strictOrdinaryCondition 𝒪 p S) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_isDeformationCondition_strictOrdinaryCondition.solution
