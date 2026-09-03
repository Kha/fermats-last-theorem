import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_Gamma0HeckeOperatorHom
import P2M.Util
import P2M.Sol.S_ModularCurve_periodMap_traceLin

set_option autoImplicit false
open CongruenceSubgroup

theorem ModularCurve.periodMap_traceLin {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q)
    (hq : q.Prime) (f : CuspForm (Gamma0 M) 2) :
    ModularCurve.periodMap W.R (CuspForm.traceLin W hq f) =
      HeckeEis.coresHom ((Gamma0 M).subgroupOf (Gamma0 W.R))
        (HeckeEis.pullbackHom ((Gamma0 W.R).subtype.subgroupComap (Gamma0 M))
          (ModularCurve.periodMap M f)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodMap_traceLin.solution
