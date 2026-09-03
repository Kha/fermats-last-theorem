import Mathlib
import Definitions.Def_CuspForm_EigenformCoefficientRing
import P2M.Util
import P2M.Sol.S_CuspForm_IsNormalizedEigenform_eigenCoeffRing_moduleFinite
attribute [-instance] CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree
attribute [-simp] CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU
set_option autoImplicit false

theorem CuspForm.IsNormalizedEigenform.eigenCoeffRing_moduleFinite {M : ℕ} [NeZero M]
    {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNormalizedEigenform)
    (hint : g.PrimeCoeffsIntegral) : Module.Finite ℤ (CuspForm.eigenCoeffRing hint) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNormalizedEigenform_eigenCoeffRing_moduleFinite.solution
