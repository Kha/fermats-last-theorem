import Mathlib
import Definitions.Def_ModularCurve_UVCrossingChart
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_chartHom_injective

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.chartHom_injective {W : Type*} [CommRing W] {π : W} (hπ : π ∈ nonZeroDivisors W) (hsep : ∀ x : W, (∀ n : ℕ, π ^ n ∣ x) → x = 0) : Function.Injective (chartHom π) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_chartHom_injective.solution
