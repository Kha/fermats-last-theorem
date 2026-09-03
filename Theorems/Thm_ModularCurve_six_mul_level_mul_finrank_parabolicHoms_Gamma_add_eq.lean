import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_ModularCurve_six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq (N : ℕ) (hN : 2 ≤ N) :
    6 * N * Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma N) ℤ) +
        6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      12 * N + N * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq.solution
