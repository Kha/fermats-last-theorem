import Definitions.Def_ModularCurve_EtaQuotient
import P2M.Util
import P2M.Sol.S_ModularCurve_sharpUnitSeries_pow_sharpIndex

theorem ModularCurve.sharpUnitSeries_pow_sharpIndex (ℓ : ℕ) [NeZero ℓ] : ModularCurve.sharpUnitSeries ℓ ^ ModularCurve.sharpIndex ℓ = ModularCurve.modularUnitSeries ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sharpUnitSeries_pow_sharpIndex.solution
