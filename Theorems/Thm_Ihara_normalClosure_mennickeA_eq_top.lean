import Definitions.Def_IharaMennickeCarrier
import P2M.Util
import P2M.Sol.S_Ihara_normalClosure_mennickeA_eq_top

open scoped MatrixGroups

theorem Ihara.normalClosure_mennickeA_eq_top (q : ℕ) [NeZero q] :
    Subgroup.normalClosure
        ({Ihara.slToAway q Ihara.mennickeA} : Set SL(2, Ihara.ZAway q)) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Ihara_normalClosure_mennickeA_eq_top.solution
