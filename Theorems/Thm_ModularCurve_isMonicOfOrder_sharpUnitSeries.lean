import Definitions.Def_ModularCurve_EtaQuotient
import P2M.Util
import P2M.Sol.S_ModularCurve_isMonicOfOrder_sharpUnitSeries

theorem ModularCurve.isMonicOfOrder_sharpUnitSeries (ℓ : ℕ) [NeZero ℓ] : ModularCurve.IsMonicOfOrder (ModularCurve.sharpUnitSeries ℓ) (-(ModularCurve.eisensteinNumerator ℓ : ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isMonicOfOrder_sharpUnitSeries.solution
