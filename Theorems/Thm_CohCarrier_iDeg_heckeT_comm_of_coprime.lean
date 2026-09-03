import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_iDeg_heckeT_comm_of_coprime

set_option autoImplicit false

theorem CohCarrier.iDeg_heckeT_comm_of_coprime {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ}
    {d ℓ : ℕ} {A : Type} [AddCommGroup A] [NeZero d] [NeZero ℓ] (h : LevelLE M M' H H' d)
    (hℓd : Nat.Coprime ℓ d) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') (φ : H1 M H A) :
    iDeg' M M' H H' d A h (heckeT M H ℓ A φ) = heckeT M' H' ℓ A (iDeg' M M' H H' d A h φ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_iDeg_heckeT_comm_of_coprime.solution
