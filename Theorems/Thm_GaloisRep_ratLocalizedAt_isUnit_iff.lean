import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_ratLocalizedAt_isUnit_iff

theorem GaloisRep.ratLocalizedAt.isUnit_iff
    {p : ℕ} (hp : p.Prime) (x : GaloisRep.ratLocalizedAt p) :
    IsUnit x ↔ ¬ p ∣ (x : ℚ).num.natAbs := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_ratLocalizedAt_isUnit_iff.solution
