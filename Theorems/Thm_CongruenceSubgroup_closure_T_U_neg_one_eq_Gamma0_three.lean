import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_closure_T_U_neg_one_eq_Gamma0_three

open scoped MatrixGroups in

theorem CongruenceSubgroup.closure_T_U_neg_one_eq_Gamma0_three (U : SL(2, ℤ))
    (hU : (U : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -3, 1]) :
    Subgroup.closure ({ModularGroup.T, U, -1} : Set SL(2, ℤ)) = CongruenceSubgroup.Gamma0 3 := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_closure_T_U_neg_one_eq_Gamma0_three.solution
