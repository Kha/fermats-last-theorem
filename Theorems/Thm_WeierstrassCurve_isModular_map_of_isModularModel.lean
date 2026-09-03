import Definitions.Def_WeierstrassCurve_ModularityProps
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_isModular_map_of_isModularModel

theorem WeierstrassCurve.isModular_map_of_isModularModel {W : WeierstrassCurve ℤ} (h : W.IsModularModel) :
    (W.map (Int.castRingHom ℚ)).IsModular := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_isModular_map_of_isModularModel.solution
