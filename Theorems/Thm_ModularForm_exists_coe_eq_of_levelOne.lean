import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.LaurentSeries
import P2M.Util
import P2M.Sol.S_ModularForm_exists_coe_eq_of_levelOne

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularForm.exists_coe_eq_of_levelOne (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    ∃ G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k, (G : ℍ → ℂ) = (F : ℍ → ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_coe_eq_of_levelOne.solution
