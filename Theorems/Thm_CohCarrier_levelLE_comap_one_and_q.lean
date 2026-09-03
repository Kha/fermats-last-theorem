import Mathlib
import Definitions.Def_CohCarrier_Lower
import P2M.Util
import P2M.Sol.S_CohCarrier_levelLE_comap_one_and_q

set_option autoImplicit false

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

theorem CohCarrier.levelLE_comap_one_and_q (N q : ℕ) [NeZero N] [NeZero q] (H : Subgroup (ZMod N)ˣ) :
    LevelLE N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) 1 ∧
    LevelLE N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) q := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_levelLE_comap_one_and_q.solution
