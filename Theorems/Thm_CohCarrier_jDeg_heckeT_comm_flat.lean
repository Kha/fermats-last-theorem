import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_jDeg_heckeT_comm_flat

set_option autoImplicit false

theorem CohCarrier.jDeg_heckeT_comm_flat {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ} {d ℓ : ℕ}
    {A : Type} [AddCommGroup A] [NeZero d] [NeZero M'] [NeZero ℓ]
    (h : LevelLE M M' H H' d) (hℓd : ℓ.Coprime d) (hℓ : ℓ.Prime)
    (hℓM' : ¬ ℓ ∣ M') (φ : H1 M' H' A) :
    heckeT M H ℓ A (jDeg M M' H H' d A h φ)
      = jDeg M M' H H' d A h (heckeT M' H' ℓ A φ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_jDeg_heckeT_comm_flat.solution
