import Mathlib
import Theorems.Thm_ModularForm_finiteDimensional_of_isArithmetic
import P2M.Util
namespace P2MW.S_CuspForm_finiteDimensional_Gamma1

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (M : ℕ) [NeZero M] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) k) := by
  haveI := ModularForm.finiteDimensional_of_isArithmetic
    (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k
  exact FiniteDimensional.of_injective
    (CuspForm.toModularFormₗ : CuspForm (CongruenceSubgroup.Gamma1 M) k →ₗ[ℂ] ModularForm (CongruenceSubgroup.Gamma1 M) k)
    CuspForm.toModularFormₗ_injective
