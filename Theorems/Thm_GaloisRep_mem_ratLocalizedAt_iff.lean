import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_mem_ratLocalizedAt_iff

theorem GaloisRep.mem_ratLocalizedAt_iff
    {p : ℕ} (hp : p.Prime) (q : ℚ) :
    q ∈ GaloisRep.ratLocalizedAt p ↔ ¬ p ∣ q.den := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_mem_ratLocalizedAt_iff.solution
