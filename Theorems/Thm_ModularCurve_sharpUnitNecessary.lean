import Definitions.Def_ModularCurve_EtaQuotient
import P2M.Util
import P2M.Sol.S_ModularCurve_sharpUnitNecessary

theorem ModularCurve.sharpUnitNecessary (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : ModularCurve.SharpUnitNecessary ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sharpUnitNecessary.solution
