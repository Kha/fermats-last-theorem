import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_ModularForm_levelOne_weight_fourteen_qCoeff_eq_zero

open scoped MatrixGroups

theorem ModularForm.levelOne_weight_fourteen_qCoeff_eq_zero (Z : ModularForm 𝒮ℒ 14) (h0 : ModularFormClass.qCoeff ⇑Z 0 = 0) : ∀ n : ℕ, ModularFormClass.qCoeff ⇑Z n = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_levelOne_weight_fourteen_qCoeff_eq_zero.solution
