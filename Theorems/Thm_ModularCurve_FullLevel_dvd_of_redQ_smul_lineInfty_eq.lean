import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_dvd_of_redQ_smul_lineInfty_eq

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.dvd_of_redQ_smul_lineInfty_eq
    (q : ℕ) [Fact q.Prime] (δ : SL(2, ℤ))
    (hfix : ModularCurve.FullLevel.redQ q δ • ModularCurve.FullLevel.lineInfty q = ModularCurve.FullLevel.lineInfty q) :
    (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_dvd_of_redQ_smul_lineInfty_eq.solution
