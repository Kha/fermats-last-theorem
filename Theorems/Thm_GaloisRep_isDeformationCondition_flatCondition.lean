import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_isDeformationCondition_flatCondition
attribute [-instance] instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

theorem GaloisRep.isDeformationCondition_flatCondition (𝒪 : Type) [CommRing 𝒪]
    {p : ℕ} {S : Finset ℕ} :
    GaloisRep.IsDeformationCondition 𝒪 (GaloisRep.flatCondition 𝒪 p S) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_isDeformationCondition_flatCondition.solution
