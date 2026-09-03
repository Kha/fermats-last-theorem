import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isFlatAt_baseChangeAlong
attribute [-instance] instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

set_option autoImplicit false

theorem GaloisRepAdic.isFlatAt_ofResidualGaloisRep_of_isFlatAt_baseChangeAlong
    {k₀ k : Type} [Field k₀] [Field k] (φ : k₀ →+* k) (ρ : ResidualGaloisRep k₀) (p : ℕ)
    (h : (GaloisRepAdic.ofResidualGaloisRep (ρ.baseChangeAlong φ)).IsFlatAt p) :
    (GaloisRepAdic.ofResidualGaloisRep ρ).IsFlatAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isFlatAt_baseChangeAlong.solution
