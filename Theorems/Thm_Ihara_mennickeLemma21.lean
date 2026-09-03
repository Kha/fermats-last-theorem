import Definitions.Def_IharaMennickeCarrier
import P2M.Util
import P2M.Sol.S_Ihara_mennickeLemma21

set_option autoImplicit false

open scoped MatrixGroups
theorem Ihara.mennickeLemma21 (q m : ℕ) [NeZero q] (hmq : Nat.Coprime m q) :
    Ihara.MennickeLemma21 q m hmq := by p2m_exact_reverting @_root_.P2MW.S_Ihara_mennickeLemma21.solution
