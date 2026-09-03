import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_IsNormalizedEigenform_qCoeff_eq_of_coprime_of_forall_prime_not_dvd_of_dvd
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply

theorem CuspForm.IsNormalizedEigenform.qCoeff_eq_of_coprime_of_forall_prime_not_dvd_of_dvd
    {L N A B : ℕ} [NeZero N] (hLN : L ∣ N)
    {h : CuspForm (CongruenceSubgroup.Gamma0 A) 2} {g : CuspForm (CongruenceSubgroup.Gamma0 B) 2}
    (hh : h.IsNormalizedEigenform) (hg : g.IsNormalizedEigenform) (hA : A ∣ L) (hB : B ∣ L)
    (hagree : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ModularFormClass.qCoeff h ℓ = ModularFormClass.qCoeff g ℓ)
    {n : ℕ} (hn : Nat.Coprime n L) :
    ModularFormClass.qCoeff h n = ModularFormClass.qCoeff g n := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNormalizedEigenform_qCoeff_eq_of_coprime_of_forall_prime_not_dvd_of_dvd.solution
