import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_injective_iDeg_one_of_isUnit_relIndex

set_option autoImplicit false

open CongruenceSubgroup

theorem CohCarrier.injective_iDeg_one_of_isUnit_relIndex
    (M : ℕ) [NeZero M] (H H' : Subgroup (ZMod M)ˣ)
    (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A]
    (h : CohCarrier.LevelLE M M H' H 1)
    (hunit : IsUnit ((H.relIndex H' : ℕ) : R)) :
    Function.Injective (CohCarrier.iDeg' M M H' H 1 A h) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_injective_iDeg_one_of_isUnit_relIndex.solution
