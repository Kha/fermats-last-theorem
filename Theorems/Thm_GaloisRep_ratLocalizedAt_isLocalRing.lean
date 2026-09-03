import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_ratLocalizedAt_isLocalRing

theorem GaloisRep.ratLocalizedAt.isLocalRing
    {p : ℕ} (hp : p.Prime) : IsLocalRing (GaloisRep.ratLocalizedAt p) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_ratLocalizedAt_isLocalRing.solution
