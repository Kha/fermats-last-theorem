import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_index_GammaHUpper_of_dvd

set_option autoImplicit false

theorem CohCarrier.index_GammaHUpper_of_dvd (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] (hℓM : ℓ ∣ M) :
    (CohCarrier.GammaHUpper M H ℓ).index = ℓ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_index_GammaHUpper_of_dvd.solution
