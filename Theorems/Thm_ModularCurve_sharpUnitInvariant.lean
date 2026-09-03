import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_NumberTheory_DedekindSum
import P2M.Util
import P2M.Sol.S_ModularCurve_sharpUnitInvariant

theorem ModularCurve.sharpUnitInvariant (ℓ : ℕ) [NeZero ℓ] : ModularCurve.SharpUnitInvariant ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sharpUnitInvariant.solution
