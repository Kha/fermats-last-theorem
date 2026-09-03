import Definitions.Def_IharaAmalgamMap
import P2M.Util
import P2M.Sol.S_Ihara_amalgamToGamma0Away_injective

theorem Ihara.amalgamToGamma0Away_injective {N q : ℕ} (hq : q.Prime) (hqN : N.Coprime q) :
    Function.Injective (Ihara.amalgamToGamma0Away N q) := by p2m_exact_reverting @_root_.P2MW.S_Ihara_amalgamToGamma0Away_injective.solution
