import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Order
import P2M.Util
import P2M.Sol.S_ModularForm_sturm_bound_of_isArithmetic

open UpperHalfPlane
open scoped MatrixGroups
theorem ModularForm.sturm_bound_of_isArithmetic {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] {k : ℤ} {f : ModularForm 𝒢 k} (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) (h : (↑((k * 𝒢.relIndex 𝒮ℒ).toNat / 12) : ℕ∞) < (qExpansion 1 f).order) : f = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_sturm_bound_of_isArithmetic.solution
