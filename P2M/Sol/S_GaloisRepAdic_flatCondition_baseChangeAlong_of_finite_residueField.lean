import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_isUnramifiedAt_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_isFlatAt_baseChangeAlong_of_finite_residueField
import P2M.Util
namespace P2MW.S_GaloisRepAdic_flatCondition_baseChangeAlong_of_finite_residueField
attribute [-instance] instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

theorem solution
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Finite (IsLocalRing.ResidueField B)]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A] [Algebra 𝒪 B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A) {p : ℕ} {S : Finset ℕ}
    (h : GaloisRep.flatCondition 𝒪 p S ρ) :
    GaloisRep.flatCondition 𝒪 p S (ρ.baseChangeAlong φ hφ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact GaloisRepAdic.detIsCyclotomic_baseChangeAlong φ hφ ρ h.1
  · exact GaloisRepAdic.isFlatAt_baseChangeAlong_of_finite_residueField φ hφ ρ h.2.1
  · exact fun q hq hqS => GaloisRepAdic.isUnramifiedAt_baseChangeAlong φ hφ ρ (h.2.2 q hq hqS)

