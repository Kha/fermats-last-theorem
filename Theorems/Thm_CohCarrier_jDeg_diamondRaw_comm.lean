import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_jDeg_diamondRaw_comm

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CohCarrier.jDeg_diamondRaw_comm {M M' : ℕ} {H : Subgroup (ZMod M)ˣ}
    {H' : Subgroup (ZMod M')ˣ} {d : ℕ} {A : Type} [AddCommGroup A] [NeZero d] [NeZero M']
    (σ : Gamma0 M) (hσ' : (σ : SL(2, ℤ)) ∈ Gamma0 M') (h : LevelLE M M' H H' d)
    (φ : H1 M' H' A) :
    diamondRaw M H A σ (jDeg M M' H H' d A h φ)
      = jDeg M M' H H' d A h (diamondRaw M' H' A ⟨↑σ, hσ'⟩ φ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_jDeg_diamondRaw_comm.solution
