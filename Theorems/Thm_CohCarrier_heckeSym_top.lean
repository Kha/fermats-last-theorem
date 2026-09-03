import Definitions.Def_CohCarrier_Lower
import P2M.Util
import P2M.Sol.S_CohCarrier_heckeSym_top

set_option autoImplicit false

theorem CohCarrier.heckeSym_top (M q : ℕ) [NeZero M] [NeZero q] (hq : q.Prime) (hqM : ¬ q ∣ M)
    {V : Type} [AddCommGroup V] (F : H1 M ⊤ V) :
    heckeTlower M ⊤ q V F = heckeT M ⊤ q V F := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_heckeSym_top.solution
