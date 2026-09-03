import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularForm_heckeU_add_slash_fricke_eq_zero

open scoped ModularForm MatrixGroups

theorem ModularForm.heckeU_add_slash_fricke_eq_zero (p : ℕ) [Fact p.Prime]
    (f : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (W : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hW : ((W : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, -1; (p : ℝ), 0]) :
    ModularForm.heckeU 2 p ⇑f + ⇑f ∣[(2 : ℤ)] W = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_heckeU_add_slash_fricke_eq_zero.solution
