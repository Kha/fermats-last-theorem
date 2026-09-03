import Mathlib
import P2M.Util
namespace P2MW.S_CongruenceSubgroup_isCusp_infty_gamma1_mapGL

open Matrix Matrix.SpecialLinearGroup Matrix.GeneralLinearGroup CongruenceSubgroup

namespace IsCuspInftyGamma1

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ Gamma1 M := by
  simp [Gamma1_mem, ModularGroup.T]

theorem mapGL_T : mapGL ℝ ModularGroup.T = upperRightHom (1 : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.T]

theorem one_mem_strictPeriods (M : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (mapGL ℝ) (Gamma1 M)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_map]
  exact ⟨ModularGroup.T, T_mem_Gamma1 M, mapGL_T⟩

end IsCuspInftyGamma1

theorem solution (M : ℕ) :
    IsCusp OnePoint.infty (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma1 M)) :=
  Subgroup.isCusp_of_mem_strictPeriods one_pos (IsCuspInftyGamma1.one_mem_strictPeriods M)
