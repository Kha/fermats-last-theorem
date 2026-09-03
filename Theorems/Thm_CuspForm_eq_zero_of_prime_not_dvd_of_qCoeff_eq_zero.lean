import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply

theorem CuspForm.eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
    {m p : ℕ} [NeZero m] (hp : p.Prime) (hpm : ¬ p ∣ m)
    (F : CuspForm (CongruenceSubgroup.Gamma0 m) 2)
    (hF : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff F n = 0) : F = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero.solution
