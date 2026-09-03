import Definitions.Def_CuspForm_ModPForms
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import P2M.Util
import P2M.Sol.S_ModPForms_mk_sigma_one_sub_sigma_one_div_mem_modPMod_four_of_dvd
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ
set_option autoImplicit false

theorem ModPForms.mk_sigma_one_sub_sigma_one_div_mem_modPMod_four_of_dvd (N' : ℕ) [NeZero N'] (d : ℕ) (hd : d ∣ N')
    (F : Type) [Field F] [CharP F 3] :
    let B : PowerSeries F := PowerSeries.mk fun n : ℕ =>
      ((((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) -
        (if d ∣ n then ((ArithmeticFunction.sigma 1 (n / d) : ℕ) : ℤ) else 0) : ℤ) : F)
    B ∈ modPMod N' 4 F := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_mk_sigma_one_sub_sigma_one_div_mem_modPMod_four_of_dvd.solution
