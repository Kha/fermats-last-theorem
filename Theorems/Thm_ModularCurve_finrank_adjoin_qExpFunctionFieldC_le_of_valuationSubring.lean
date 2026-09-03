import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring

theorem ModularCurve.finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring
    {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    {k : Type*} [Field k] (π : A →+* k)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hF : ∃ t : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ),
      Transcendental L t ∧
        FiniteDimensional
          (IntermediateField.adjoin L
            ({t} : Set (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (a b : PowerSeries ℤ)
    (X : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (hX : (X : LaurentSeries L) = ModularCurve.intSeriesC L a / ModularCurve.intSeriesC L b)
    (x : ModularCurve.qExpFunctionFieldC k Γ)
    (hx : (x : LaurentSeries k) = ModularCurve.intSeriesC k a / ModularCurve.intSeriesC k b)
    (htr : Transcendental k x) :
    FiniteDimensional (IntermediateField.adjoin k ({x} : Set (ModularCurve.qExpFunctionFieldC k Γ)))
        (ModularCurve.qExpFunctionFieldC k Γ) ∧
      Module.finrank (IntermediateField.adjoin k ({x} : Set (ModularCurve.qExpFunctionFieldC k Γ)))
          (ModularCurve.qExpFunctionFieldC k Γ) ≤
        Module.finrank
          (IntermediateField.adjoin L
            ({X} : Set (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring.solution
