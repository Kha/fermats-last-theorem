import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_isPrincipalIdealRing_ratLocalizedAt

theorem GaloisRep.isPrincipalIdealRing_ratLocalizedAt (p : ℕ) :
    IsPrincipalIdealRing (GaloisRep.ratLocalizedAt p) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_isPrincipalIdealRing_ratLocalizedAt.solution
