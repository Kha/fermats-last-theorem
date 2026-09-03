import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Theorems.Thm_ModularForm_finiteDimensional_of_isArithmetic
import P2M.Util
namespace P2MW.S_ModularForm_finiteDimensional_Gamma0

open UpperHalfPlane ModularForm SlashInvariantForm Matrix.SpecialLinearGroup ConjAct
open scoped MatrixGroups ModularForm Topology Manifold Pointwise

noncomputable section

theorem solution (N : ℕ) [NeZero N] (k : ℤ) : FiniteDimensional ℂ (ModularForm (CongruenceSubgroup.Gamma0 N) k) := by
  exact ModularForm.finiteDimensional_of_isArithmetic _ k
end
