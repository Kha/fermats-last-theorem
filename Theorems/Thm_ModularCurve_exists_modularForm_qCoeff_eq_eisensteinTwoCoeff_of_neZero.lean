import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_modularForm_qCoeff_eq_eisensteinTwoCoeff_of_neZero
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve

theorem ModularCurve.exists_modularForm_qCoeff_eq_eisensteinTwoCoeff_of_neZero (N : ℕ) [NeZero N] :
    ∃ E : ModularForm (CongruenceSubgroup.Gamma0 N) 2,
      ∀ n : ℕ, ModularFormClass.qCoeff E n = (eisensteinTwoCoeff N n : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_modularForm_qCoeff_eq_eisensteinTwoCoeff_of_neZero.solution
