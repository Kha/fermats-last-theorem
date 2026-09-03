import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_NumberTheory_DedekindSum
import P2M.Util
import P2M.Sol.S_ModularCurve_sharpUnitNecessary_of_prime

theorem ModularCurve.sharpUnitNecessary_of_prime (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (h : ℓ % 12 ≠ 1) : ModularCurve.SharpUnitNecessary ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sharpUnitNecessary_of_prime.solution
