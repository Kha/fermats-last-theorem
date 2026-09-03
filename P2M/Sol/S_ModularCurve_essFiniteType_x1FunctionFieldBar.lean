import Mathlib
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Definitions.Def_ModularCurve_X1
import P2M.Util
namespace P2MW.S_ModularCurve_essFiniteType_x1FunctionFieldBar

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem solution (M : ℕ) [NeZero M] :
    Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) := by
  obtain ⟨x, htr, hfd⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 M) (by rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])
  exact AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional htr hfd
