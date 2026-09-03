import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_card_le_two_mul_add_one

theorem WeierstrassCurve.card_le_two_mul_add_one {F : Type*} [Field F] [Finite F]
    (W : WeierstrassCurve F) : W.card ≤ 2 * Nat.card F + 1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_card_le_two_mul_add_one.solution
