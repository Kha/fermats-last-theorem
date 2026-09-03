import Mathlib
import Definitions.Def_ModularCurve_UVCrossingChart
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_range_chartHom_le_fixedSubring

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.range_chartHom_le_fixedSubring {W : Type*} [CommRing W] (π : W) : (chartHom π).range ≤ fixedSubring π := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_range_chartHom_le_fixedSubring.solution
