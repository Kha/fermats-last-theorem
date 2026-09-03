import Definitions.Def_CuspForm_ModPForms
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import P2M.Util
import P2M.Sol.S_ModPForms_thetaPS_add_smul_mul_mem_modPMod_add_two
attribute [-simp] PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat
set_option autoImplicit false

theorem ModPForms.thetaPS_add_smul_mul_mem_modPMod_add_two (N' : ℕ) [NeZero N'] (d : ℕ) (hd : d ∣ N')
    (hd3 : d % 3 = 2) (F : Type) [Field F] [CharP F 3] (k : ℤ) (φ : PowerSeries F)
    (hφ : φ ∈ ModPForms.modPMod N' k F) :
    ModPForms.thetaPS φ + (k : F) •
      ((PowerSeries.mk fun n : ℕ =>
          ((((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) -
            (if d ∣ n then ((ArithmeticFunction.sigma 1 (n / d) : ℕ) : ℤ) else 0) : ℤ) : F)) * φ) ∈
      ModPForms.modPMod N' (k + 2) F := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_thetaPS_add_smul_mul_mem_modPMod_add_two.solution
