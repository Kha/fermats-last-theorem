import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual
attribute [-instance] instIsScalarTowerTensorProduct_definitions AlgebraicClosure.Rat.isGalois CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff CuspForm.HeckeGaloisRepDatum.mk.sizeOf_spec CuspForm.HeckeGaloisRepDatum.mk.injEq CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open IsLocalRing
theorem GaloisRepAdic.isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpA : (p : A) ∈ maximalIdeal A)
    (ρ : GaloisRepAdic A) (hdet : ρ.DetIsCyclotomic p) (hflat : ρ.IsFlatAt p)
    (hres : (GaloisRepAdic.ofResidualGaloisRep ρ.residual).IsOrdinaryAt p) :
    ρ.IsOrdinaryAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual.solution
