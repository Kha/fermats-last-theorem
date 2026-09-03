import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_iDeg_diamondRaw_comm

set_option autoImplicit false

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

theorem CohCarrier.iDeg_diamondRaw_comm
    {M M' : ℕ} [NeZero M] [NeZero M'] {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ} {d : ℕ} [NeZero d]
    (h : LevelLE M M' H H' d) {A : Type} [AddCommGroup A] (σ' : Gamma0 M')
    (hd : (d : ℤ) ∣ (σ' : SL(2, ℤ)) 1 0) (σ : Gamma0 M) (hσ : (σ : SL(2, ℤ)) = conjLowerMat d (σ' : SL(2, ℤ)) hd)
    (φ : H1 M H A) :
    iDeg' M M' H H' d A h (diamondRaw M H A σ φ) = diamondRaw M' H' A σ' (iDeg' M M' H H' d A h φ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_iDeg_diamondRaw_comm.solution
