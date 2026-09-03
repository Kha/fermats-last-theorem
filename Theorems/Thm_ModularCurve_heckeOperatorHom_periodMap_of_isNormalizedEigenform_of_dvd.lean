import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeOperatorHom_periodMap_of_isNormalizedEigenform_of_dvd

theorem ModularCurve.heckeOperatorHom_periodMap_of_isNormalizedEigenform_of_dvd {N : ℕ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform) {q : ℕ} (hq : q.Prime)
    (hqN : q ∣ N) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    HeckeEis.heckeOperatorHom N q ℂ (ModularCurve.periodMap N f)
      = (ModularFormClass.qCoeff f q) • ModularCurve.periodMap N f := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeOperatorHom_periodMap_of_isNormalizedEigenform_of_dvd.solution
