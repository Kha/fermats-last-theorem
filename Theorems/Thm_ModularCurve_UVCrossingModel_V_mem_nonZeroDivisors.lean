import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_V_mem_nonZeroDivisors

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.V_mem_nonZeroDivisors {W : Type*} [CommRing W] {π : W} (hπ : π ∈ nonZeroDivisors W) : V π ∈ nonZeroDivisors (UVCrossingModel W π) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_V_mem_nonZeroDivisors.solution
