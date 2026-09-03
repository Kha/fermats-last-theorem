import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_isCusp_infty_gamma1_mapGL

theorem CongruenceSubgroup.isCusp_infty_gamma1_mapGL (M : ℕ) :
    IsCusp OnePoint.infty (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma1 M)) := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_isCusp_infty_gamma1_mapGL.solution
