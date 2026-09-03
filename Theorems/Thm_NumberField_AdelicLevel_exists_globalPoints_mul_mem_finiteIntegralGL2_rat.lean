import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat
attribute [-simp] AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe

theorem NumberField.AdelicLevel.exists_globalPoints_mul_mem_finiteIntegralGL2_rat
    (g : Matrix.GeneralLinearGroup (Fin 2)
      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    ∃ γ : Matrix.GeneralLinearGroup (Fin 2) ℚ,
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ
          (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ) * g
        ∈ NumberField.AdelicLevel.finiteIntegralGL2 (NumberField.RingOfIntegers ℚ) ℚ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.solution
