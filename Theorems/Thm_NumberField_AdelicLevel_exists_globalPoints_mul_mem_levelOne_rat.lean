import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
attribute [-simp] AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe

theorem NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat
    {N : Ideal (NumberField.RingOfIntegers ℚ)} (hN : N ≠ ⊥)
    (g : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    ∃ γ : Matrix.GeneralLinearGroup (Fin 2) ℚ,
      AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * g
          ∈ NumberField.AdelicLevel.levelOne (NumberField.RingOfIntegers ℚ) ℚ N ∧
        ∀ (w : NumberField.InfinitePlace ℚ) (hw : w.IsReal),
          Matrix.GeneralLinearGroup.map
              (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom
              (NumberField.AdelicLevel.archComponent ℚ w
                (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ
                  (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * g)))
            ∈ Matrix.GLPos (Fin 2) ℝ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat.solution
