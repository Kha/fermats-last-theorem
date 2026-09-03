import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_const_mem_nonZeroDivisors
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mul_V
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_V_mem_nonZeroDivisors

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] {π : W} (hπ : π ∈ nonZeroDivisors W) :
    V π ∈ nonZeroDivisors (UVCrossingModel W π) :=
  by
  have h := ModularCurve.UVCrossingModel.const_mem_nonZeroDivisors hπ
  rw [← ModularCurve.UVCrossingModel.U_mul_V] at h
  exact (mul_mem_nonZeroDivisors.mp h).2
