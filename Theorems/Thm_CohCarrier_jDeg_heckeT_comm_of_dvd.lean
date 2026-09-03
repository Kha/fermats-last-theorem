import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_jDeg_heckeT_comm_of_dvd

set_option autoImplicit false

theorem CohCarrier.jDeg_heckeT_comm_of_dvd {M : ℕ} {H H' : Subgroup (ZMod M)ˣ} {ℓ : ℕ}
    {A : Type} [AddCommGroup A] [NeZero M] [NeZero ℓ]
    (h : LevelLE M M H H' 1) (hℓM : ℓ ∣ M) (φ : H1 M H' A) :
    heckeT M H ℓ A (jDeg M M H H' 1 A h φ) = jDeg M M H H' 1 A h (heckeT M H' ℓ A φ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_jDeg_heckeT_comm_of_dvd.solution
