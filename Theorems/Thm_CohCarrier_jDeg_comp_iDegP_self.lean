import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_jDeg_comp_iDegP_self

set_option autoImplicit false

theorem CohCarrier.jDeg_comp_iDegP_self {M M' d : ℕ} {H : Subgroup (ZMod M)ˣ}
    {H' : Subgroup (ZMod M')ˣ} {A : Type*} [AddCommGroup A] [NeZero M'] [NeZero d]
    (h : LevelLE M M' H H' d) (φ : H1 M H A) :
    jDeg M M' H H' d A h (iDeg' M M' H H' d A h φ)
      = (iotaDeg M M' H H' d h).range.index • φ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_jDeg_comp_iDegP_self.solution
