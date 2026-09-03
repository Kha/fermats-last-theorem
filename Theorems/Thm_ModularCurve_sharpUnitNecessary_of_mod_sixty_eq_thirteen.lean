import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_NumberTheory_DedekindSum
import P2M.Util
import P2M.Sol.S_ModularCurve_sharpUnitNecessary_of_mod_sixty_eq_thirteen

theorem ModularCurve.sharpUnitNecessary_of_mod_sixty_eq_thirteen (i : ℕ) : ModularCurve.SharpUnitNecessary (60 * i + 13) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sharpUnitNecessary_of_mod_sixty_eq_thirteen.solution
