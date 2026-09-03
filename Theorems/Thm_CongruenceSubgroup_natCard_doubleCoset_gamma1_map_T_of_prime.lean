import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_of_prime

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.natCard_doubleCoset_gamma1_map_T_of_prime
    (p : ℕ) [Fact p.Prime] :
    Nat.card (DoubleCoset.Quotient (((CongruenceSubgroup.Gamma1 p).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod p)))) : Set SL(2, ZMod p)) (((Subgroup.zpowers ModularGroup.T).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod p)))) : Set SL(2, ZMod p))) = 2 * (p - 1) := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_of_prime.solution
