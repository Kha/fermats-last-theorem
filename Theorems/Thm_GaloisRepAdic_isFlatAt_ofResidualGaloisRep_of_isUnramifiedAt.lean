import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt
attribute [-instance] instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

set_option autoImplicit false

theorem GaloisRepAdic.isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt
    {k : Type} [Field k] [Finite k] (ρ : ResidualGaloisRep k) {p : ℕ} (hp : p.Prime)
    (h : (GaloisRepAdic.ofResidualGaloisRep ρ).IsUnramifiedAt p) :
    (GaloisRepAdic.ofResidualGaloisRep ρ).IsFlatAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt.solution
