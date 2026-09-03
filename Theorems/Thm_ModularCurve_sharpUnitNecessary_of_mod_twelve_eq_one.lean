import Definitions.Def_ModularCurve_EtaQuotient
import P2M.Util
import P2M.Sol.S_ModularCurve_sharpUnitNecessary_of_mod_twelve_eq_one

theorem ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_one (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (h : ℓ % 12 = 1) : ModularCurve.SharpUnitNecessary ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sharpUnitNecessary_of_mod_twelve_eq_one.solution
