import Mathlib
import Definitions.Def_CuspForm_Newforms
import Theorems.Thm_CuspForm_qCoeff_sq_eq_one_of_isNewform
import Theorems.Thm_CuspForm_qCoeff_eq_zero_of_isNewform_of_sq_dvd
import P2M.Util
namespace P2MW.S_CuspForm_newformBadPrimeCoeff
attribute [-simp] ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.coe_traceLin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply CuspForm.coe_heckeULowerLin_apply

theorem solution (N : ℕ) : CuspForm.NewformBadPrimeCoeff N :=
  fun _f hf q hq hqN =>
    ⟨fun hsq => CuspForm.qCoeff_sq_eq_one_of_isNewform hf q hq hqN hsq,
     fun hsq => CuspForm.qCoeff_eq_zero_of_isNewform_of_sq_dvd hf q hq hsq⟩
