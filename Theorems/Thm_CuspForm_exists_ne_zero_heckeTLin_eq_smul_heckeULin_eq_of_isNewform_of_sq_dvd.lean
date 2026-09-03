import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_Newforms
import P2M.Util
import P2M.Sol.S_CuspForm_exists_ne_zero_heckeTLin_eq_smul_heckeULin_eq_of_isNewform_of_sq_dvd
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.exists_ne_zero_heckeTLin_eq_smul_heckeULin_eq_of_isNewform_of_sq_dvd
    (N : ℕ) [NeZero N]
    (hN3 : ∀ q : ℕ, q.Prime → ¬ q ^ 3 ∣ N)
    (Mg : ℕ) [NeZero Mg] (hMgN : Mg ∣ N)
    (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2) (hg : g.IsNewform)

    (hone : ∀ q : ℕ, q.Prime → q ∣ N → ¬ q ^ 2 ∣ N → q ∣ Mg)

    (hap0 : ∀ q : ℕ, q.Prime → q ^ 2 ∣ Mg → ModularFormClass.qCoeff g q = 0) :
    ∃ g' : CuspForm (CongruenceSubgroup.Gamma0 N) 2, g' ≠ 0 ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
        CuspForm.heckeTLin 2 hℓ hℓN g' = (ModularFormClass.qCoeff g ℓ) • g') ∧
      (∀ (q : ℕ), q.Prime → ∀ (hqN : q ∣ N), q ^ 2 ∣ N → CuspForm.heckeULin 2 hqN g' = 0) ∧
      (∀ (q : ℕ), q.Prime → ∀ (hqN : q ∣ N), ¬ q ^ 2 ∣ N →
        CuspForm.heckeULin 2 hqN g' = (ModularFormClass.qCoeff g q) • g') := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_ne_zero_heckeTLin_eq_smul_heckeULin_eq_of_isNewform_of_sq_dvd.solution
