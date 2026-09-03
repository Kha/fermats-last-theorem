import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange

theorem ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (L : Type*) [Field L] [Algebra ℚ L]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) :
    ∃ x : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ),
      Transcendental L x ∧
      FiniteDimensional
        (IntermediateField.adjoin L
          ({x} : Set (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))))
        (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange.solution
