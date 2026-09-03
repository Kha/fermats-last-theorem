import Definitions.Def_FrobeniusDensity_PrimeSums
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_idealSum_ne_top

theorem FrobeniusDensity.idealSum_ne_top
    (K : Type*) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    FrobeniusDensity.idealSum K s ≠ ⊤ := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_idealSum_ne_top.solution
