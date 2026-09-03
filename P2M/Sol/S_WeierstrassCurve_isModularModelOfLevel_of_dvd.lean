import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_of_dvd
import P2M.Util
namespace P2MW.S_WeierstrassCurve_isModularModelOfLevel_of_dvd
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

noncomputable section

theorem solution (W : WeierstrassCurve ℤ) {M N : ℕ} [NeZero N] (hMN : M ∣ N) (h : W.IsModularModelOfLevel M) : W.IsModularModelOfLevel N := by
  obtain ⟨f, hf, hap⟩ := h
  obtain ⟨g, hg, hcoeff⟩ := CuspForm.exists_isNormalizedEigenform_of_dvd hMN f hf
  exact ⟨g, hg, fun p hp hgood hpN ↦
    (hcoeff p (hp.coprime_iff_not_dvd.mpr hpN)).trans (hap p hp hgood fun hpM ↦ hpN (hpM.trans hMN))⟩

end
