import Definitions.Def_Gamma0Away
import Definitions.Def_IharaIota
import Definitions.Def_IharaAmalgam
import Definitions.Def_IharaAmalgamMap
import P2M.Util
import P2M.Sol.S_Ihara_amalgamToGamma0Away_surjective

theorem Ihara.amalgamToGamma0Away_surjective (N q : ℕ) (hNq : Nat.Coprime N q)
    (hq : q.Prime) :
    Function.Surjective (Ihara.amalgamToGamma0Away N q) := by p2m_exact_reverting @_root_.P2MW.S_Ihara_amalgamToGamma0Away_surjective.solution
