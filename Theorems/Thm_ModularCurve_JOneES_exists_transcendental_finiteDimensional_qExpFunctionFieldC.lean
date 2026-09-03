import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC

theorem ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) :
    ∃ x : ModularCurve.qExpFunctionFieldC ℚ Γ, Transcendental ℚ x ∧
      FiniteDimensional
        (IntermediateField.adjoin ℚ ({x} : Set (ModularCurve.qExpFunctionFieldC ℚ Γ)))
        (ModularCurve.qExpFunctionFieldC ℚ Γ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC.solution
