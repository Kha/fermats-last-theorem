import Mathlib
import Definitions.Def_ModularCurve_CuspSpace
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_CuspSpace_conj_T_zpow_mem_Gamma0_iff

open OnePoint
open scoped MatrixGroups
theorem ModularCurve.CuspSpace.conj_T_zpow_mem_Gamma0_iff {N : ℕ} (hN : N ≠ 0) (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (m : ℤ) :
    σ * ModularGroup.T ^ m * σ⁻¹ ∈ CongruenceSubgroup.Gamma0 N ↔
      (ModularCurve.CuspSpace.cuspWidth (ModularCurve.CuspSpace.mk N (Matrix.SpecialLinearGroup.mapGL ℚ σ • (∞ : OnePoint ℚ))) : ℤ) ∣ m := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CuspSpace_conj_T_zpow_mem_Gamma0_iff.solution
