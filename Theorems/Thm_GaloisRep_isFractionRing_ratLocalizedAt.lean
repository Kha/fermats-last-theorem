import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_isFractionRing_ratLocalizedAt

theorem GaloisRep.isFractionRing_ratLocalizedAt (p : ℕ) :
    IsFractionRing (GaloisRep.ratLocalizedAt p) ℚ := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_isFractionRing_ratLocalizedAt.solution
