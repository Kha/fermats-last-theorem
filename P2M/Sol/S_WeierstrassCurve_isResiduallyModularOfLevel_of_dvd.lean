import Definitions.Def_FLTPrelim_ModularRep
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_of_dvd
import P2M.Util
namespace P2MW.S_WeierstrassCurve_isResiduallyModularOfLevel_of_dvd
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

noncomputable section

theorem solution (W : WeierstrassCurve ℤ) (p : ℕ) {M N : ℕ} [NeZero N] (hMN : M ∣ N) (h : W.IsResiduallyModularOfLevel p M) : W.IsResiduallyModularOfLevel p N := by
  obtain ⟨f, 𝔪, hf, hmax, hpm, hcong⟩ := h
  obtain ⟨g, hg, hcoeff⟩ := CuspForm.exists_isNormalizedEigenform_of_dvd hMN f hf
  refine ⟨g, 𝔪, hg, hmax, hpm, fun ℓ hℓ hgood hℓN hℓp ↦ ?_⟩
  obtain ⟨a, ha, ham⟩ := hcong ℓ hℓ hgood (fun hℓM ↦ hℓN (hℓM.trans hMN)) hℓp
  exact ⟨a, ha.trans (hcoeff ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)).symm, ham⟩

end
