import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import P2M.Util
import P2M.Sol.S_ModularForm_finiteDimensional_Gamma0

open UpperHalfPlane
open scoped MatrixGroups
theorem ModularForm.finiteDimensional_Gamma0 (N : ℕ) [NeZero N] (k : ℤ) : FiniteDimensional ℂ (ModularForm (CongruenceSubgroup.Gamma0 N) k) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_finiteDimensional_Gamma0.solution
