import Mathlib
import Definitions.Def_CohCarrier_Lower
import P2M.Util
namespace P2MW.S_CohCarrier_levelLE_comap_one_and_q

set_option autoImplicit false

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

theorem solution (N q : ℕ) [NeZero N] [NeZero q] (H : Subgroup (ZMod N)ˣ) :
    LevelLE N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) 1 ∧
    LevelLE N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) q :=
  ⟨⟨dvd_mul_right N q, one_dvd _, fun u hu => hu⟩,
   ⟨dvd_mul_right N q, by rw [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero (NeZero.ne N))], fun u hu => hu⟩⟩
