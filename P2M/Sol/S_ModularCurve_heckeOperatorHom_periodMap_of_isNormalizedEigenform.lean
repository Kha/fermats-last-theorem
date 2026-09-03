import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularCurve_periodMap_heckeTLin
import Theorems.Thm_ModularCurve_periodMap_smul
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin
import P2M.Util
namespace P2MW.S_ModularCurve_heckeOperatorHom_periodMap_of_isNormalizedEigenform

set_option Elab.async false
set_option autoImplicit false

theorem solution {N : ℕ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓN : ¬ ℓ ∣ N) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    HeckeEis.heckeOperatorHom N ℓ ℂ (ModularCurve.periodMap N f)
      = (ModularFormClass.qCoeff f ℓ) • ModularCurve.periodMap N f := by
  haveI : NeZero N := ⟨fun h => hℓN (h ▸ dvd_zero ℓ)⟩
  have heig : CuspForm.heckeTLin 2 hℓ hℓN f = ModularFormClass.qCoeff f ℓ • f :=
    (((CuspForm.isNormalizedEigenform_iff_heckeTLin f).mp hf).2 ℓ hℓ).1 hℓN
  have h := ModularCurve.periodMap_heckeTLin hℓ hℓN f
  rw [heig, ModularCurve.periodMap_smul] at h
  exact h.symm

#print axioms solution
