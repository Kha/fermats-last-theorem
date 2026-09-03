import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_eq_two_mul_of_five_le

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.natCard_doubleCoset_gamma1_map_T_eq_two_mul_of_five_le
    (N : ℕ) [NeZero N] (hN : 5 ≤ N) :
    Nat.card (DoubleCoset.Quotient (((CongruenceSubgroup.Gamma1 N).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N)))) : Set SL(2, ZMod N)) (((Subgroup.zpowers ModularGroup.T).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N)))) : Set SL(2, ZMod N))) =
      2 * Nat.card (DoubleCoset.Quotient (((CongruenceSubgroup.Gamma1 N).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N)))) : Set SL(2, ZMod N)) (((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N)))) : Set SL(2, ZMod N))) := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_eq_two_mul_of_five_le.solution
