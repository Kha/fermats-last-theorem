import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_mul_of_coprime

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.natCard_doubleCoset_gamma1_map_T_mul_of_coprime
    (M n : ℕ) [NeZero M] [NeZero n] (hMn : M.Coprime n) :
    Nat.card (DoubleCoset.Quotient (((CongruenceSubgroup.Gamma1 (M * n)).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod (M * n))))) : Set SL(2, ZMod (M * n))) (((Subgroup.zpowers ModularGroup.T).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod (M * n))))) : Set SL(2, ZMod (M * n)))) =
      Nat.card (DoubleCoset.Quotient (((CongruenceSubgroup.Gamma1 M).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod M)))) : Set SL(2, ZMod M)) (((Subgroup.zpowers ModularGroup.T).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod M)))) : Set SL(2, ZMod M))) * Nat.card (DoubleCoset.Quotient (((CongruenceSubgroup.Gamma1 n).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod n)))) : Set SL(2, ZMod n)) (((Subgroup.zpowers ModularGroup.T).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod n)))) : Set SL(2, ZMod n))) := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_mul_of_coprime.solution
