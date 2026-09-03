import Definitions.Def_ModularCurve_EtaQuotient
import P2M.Util
import P2M.Sol.S_ModularCurve_sharpUnitNecessary_of_mod_oneTwenty_eq_one_or_fortyNine

theorem ModularCurve.sharpUnitNecessary_of_mod_oneTwenty_eq_one_or_fortyNine (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (h : ℓ % 120 = 1 ∨ ℓ % 120 = 49) : ModularCurve.SharpUnitNecessary ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sharpUnitNecessary_of_mod_oneTwenty_eq_one_or_fortyNine.solution
