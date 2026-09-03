import Mathlib
import Definitions.Def_CohCarrier_Lower
import P2M.Util
import P2M.Sol.S_CohCarrier_index_range_iotaDeg_of_prime_comap

set_option autoImplicit false

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

theorem CohCarrier.index_range_iotaDeg_of_prime_comap (N q : ℕ) [NeZero N] [NeZero q]
    (hq : q.Prime) (hqN : ¬ q ∣ N) (H : Subgroup (ZMod N)ˣ)
    (h₁ : LevelLE N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) 1)
    (hq' : LevelLE N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) q) :
    (iotaDeg N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) 1 h₁).range.index = q + 1 ∧
    (iotaDeg N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) q hq').range.index = q + 1 ∧
    ((iotaDeg N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) q hq').range.subgroupOf (GammaHUpper N H q)).index = 1 ∧
    ((iotaDeg N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) 1 h₁).range.subgroupOf (GammaHLower N H q)).index = 1 := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_index_range_iotaDeg_of_prime_comap.solution
