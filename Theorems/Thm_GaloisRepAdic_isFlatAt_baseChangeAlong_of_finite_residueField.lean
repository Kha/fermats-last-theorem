import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isFlatAt_baseChangeAlong_of_finite_residueField
attribute [-instance] instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

theorem GaloisRepAdic.isFlatAt_baseChangeAlong_of_finite_residueField
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Finite (IsLocalRing.ResidueField B)]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    {p : ℕ} (h : ρ.IsFlatAt p) : (ρ.baseChangeAlong φ hφ).IsFlatAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isFlatAt_baseChangeAlong_of_finite_residueField.solution
