import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators
import P2M.Util
import P2M.Sol.S_ModPForms_heckeV_mem_modPMod_mul
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat
set_option autoImplicit false

theorem ModPForms.heckeV_mem_modPMod_mul (N : ℕ) [NeZero N] (k : ℤ) (ℓ : ℕ) (hℓ : ℓ ≠ 0)
    (F : Type) [Field F] (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPMod N k F) :
    PowerSeries.heckeV ℓ φ ∈ ModPForms.modPMod (N * ℓ) k F := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_heckeV_mem_modPMod_mul.solution
