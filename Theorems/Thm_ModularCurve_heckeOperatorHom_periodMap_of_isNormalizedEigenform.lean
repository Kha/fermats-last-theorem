import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeOperatorHom_periodMap_of_isNormalizedEigenform

theorem ModularCurve.heckeOperatorHom_periodMap_of_isNormalizedEigenform {N : ℕ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓN : ¬ ℓ ∣ N) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    HeckeEis.heckeOperatorHom N ℓ ℂ (ModularCurve.periodMap N f)
      = (ModularFormClass.qCoeff f ℓ) • ModularCurve.periodMap N f := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeOperatorHom_periodMap_of_isNormalizedEigenform.solution
