import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_isFlatAt_ofResidualGaloisRep_of_baseChangeAlong
attribute [-instance] instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

theorem ResidualGaloisRep.isFlatAt_ofResidualGaloisRep_of_baseChangeAlong
    {k k' : Type} [Field k] [Field k'] (ψ : k →+* k') (ρ : ResidualGaloisRep k) {p : ℕ}
    (h : (GaloisRepAdic.ofResidualGaloisRep (ρ.baseChangeAlong ψ)).IsFlatAt p) :
    (GaloisRepAdic.ofResidualGaloisRep ρ).IsFlatAt p := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_isFlatAt_ofResidualGaloisRep_of_baseChangeAlong.solution
