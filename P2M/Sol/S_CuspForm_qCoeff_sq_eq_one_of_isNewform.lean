import Mathlib
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Theorems.Thm_ModularForm_AtkinLehnerDatum_nonempty_of_prime_of_dvd_of_not_sq_dvd
import Theorems.Thm_CuspForm_atkinLehnerLin_eq_neg_qCoeff_smul_of_isNewform
import Theorems.Thm_CuspForm_sq_eq_one_of_atkinLehnerLin_eq_smul
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeT
import P2M.Util
namespace P2MW.S_CuspForm_qCoeff_sq_eq_one_of_isNewform
attribute [-simp] CuspForm.coe_traceLin_apply ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply

theorem solution {N : ℕ} {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNewform)
    (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hsq : ¬ q ^ 2 ∣ N) :
    ModularFormClass.qCoeff f q ^ 2 = 1 := by
  haveI : NeZero N := ⟨by rintro rfl; exact hsq (dvd_zero _)⟩
  obtain ⟨W⟩ := ModularForm.AtkinLehnerDatum.nonempty_of_prime_of_dvd_of_not_sq_dvd hq hqN hsq

  have hfeig := (CuspForm.isNormalizedEigenform_iff_heckeT f).mp hf.1
  have hfne : f ≠ 0 := by
    intro h0
    have h1 := hfeig.1
    rw [h0] at h1
    have hz : ModularFormClass.qCoeff (⇑(0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2)) 1 = 0 := by
      have hcoe : ((0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : UpperHalfPlane → ℂ) = 0 := rfl
      simp only [ModularFormClass.qCoeff, hcoe, UpperHalfPlane.qExpansion_zero, map_zero]
    rw [hz] at h1
    exact zero_ne_one h1
  have hw := CuspForm.atkinLehnerLin_eq_neg_qCoeff_smul_of_isNewform W hq hf
  have hsq1 := CuspForm.sq_eq_one_of_atkinLehnerLin_eq_smul W hfne hw
  rwa [neg_sq] at hsq1
