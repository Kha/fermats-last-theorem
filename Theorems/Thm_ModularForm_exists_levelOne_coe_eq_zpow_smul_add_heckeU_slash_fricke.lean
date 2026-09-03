import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import P2M.Util
import P2M.Sol.S_ModularForm_exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke

open scoped ModularForm MatrixGroups

theorem ModularForm.exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke (p : ℕ) [Fact p.Prime] (k : ℤ) (X : ModularForm (CongruenceSubgroup.Gamma0 p) k) (W : Matrix.GeneralLinearGroup (Fin 2) ℝ) (hW : ((W : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) : ∃ Y : ModularForm 𝒮ℒ k, ⇑Y = (p : ℂ) ^ (k - 2) • ⇑X + ModularForm.heckeU k p (⇑X ∣[k] W) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke.solution
