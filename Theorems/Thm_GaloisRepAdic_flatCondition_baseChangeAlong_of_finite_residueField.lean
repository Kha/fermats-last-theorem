import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_flatCondition_baseChangeAlong_of_finite_residueField
attribute [-instance] instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

theorem GaloisRepAdic.flatCondition_baseChangeAlong_of_finite_residueField
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Finite (IsLocalRing.ResidueField B)]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A] [Algebra 𝒪 B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A) {p : ℕ} {S : Finset ℕ}
    (h : GaloisRep.flatCondition 𝒪 p S ρ) :
    GaloisRep.flatCondition 𝒪 p S (ρ.baseChangeAlong φ hφ) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_flatCondition_baseChangeAlong_of_finite_residueField.solution
