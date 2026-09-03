import Mathlib.NumberTheory.ModularForms.QExpansion
import P2M.Util
import P2M.Sol.S_ModularForm_finiteDimensional_and_finrank_le_of_isArithmetic

open UpperHalfPlane
open scoped MatrixGroups
theorem ModularForm.finiteDimensional_and_finrank_le_of_isArithmetic (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] [𝒢.HasDetOne] (k : ℤ) (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) :
    FiniteDimensional ℂ (ModularForm 𝒢 k) ∧
      Module.finrank ℂ (ModularForm 𝒢 k) ≤ (k * 𝒢.relIndex 𝒮ℒ).toNat / 12 + 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_finiteDimensional_and_finrank_le_of_isArithmetic.solution
