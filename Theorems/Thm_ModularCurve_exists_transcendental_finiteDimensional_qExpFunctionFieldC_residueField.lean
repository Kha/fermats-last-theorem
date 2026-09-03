import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
attribute [-simp] ModularCurve.qExpandAlgHomC_apply

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
    (L : Type*) [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) :
    ∃ x : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ,
      (x : LaurentSeries (IsLocalRing.ResidueField A)) =
          ModularCurve.jqModC (IsLocalRing.ResidueField A) ∧
      Transcendental (IsLocalRing.ResidueField A) x ∧
      FiniteDimensional
        (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({x} : Set (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)))
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) ∧
      ∀ (y : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)),
        (y : LaurentSeries L) = ModularCurve.jqModC L →
        Module.finrank
            (IntermediateField.adjoin (IsLocalRing.ResidueField A)
              ({x} : Set (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)))
            (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) ≤
          Module.finrank
            (IntermediateField.adjoin L
              ({y} : Set (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))))
            (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField.solution
