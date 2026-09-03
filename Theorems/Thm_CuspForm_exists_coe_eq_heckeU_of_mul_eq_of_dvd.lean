import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_exists_coe_eq_heckeU_of_mul_eq_of_dvd
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat

theorem CuspForm.exists_coe_eq_heckeU_of_mul_eq_of_dvd
    {m q R : ℕ} [NeZero m] (hqR : q * R = m) (hq : q ∣ R)
    (F : CuspForm (CongruenceSubgroup.Gamma0 m) 2) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 R) 2, ⇑g = ModularForm.heckeU 2 q ⇑F := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_coe_eq_heckeU_of_mul_eq_of_dvd.solution
