import Definitions.Def_IharaMennickeCarrier
import P2M.Util
import P2M.Sol.S_Ihara_mennickeCSP_of_prime

set_option autoImplicit false

theorem Ihara.mennickeCSP_of_prime (q : ℕ) (hq : q.Prime) (N : ℕ) (hNq : Nat.Coprime N q) :
    Ihara.MennickeCSP N q hNq := by p2m_exact_reverting @_root_.P2MW.S_Ihara_mennickeCSP_of_prime.solution
