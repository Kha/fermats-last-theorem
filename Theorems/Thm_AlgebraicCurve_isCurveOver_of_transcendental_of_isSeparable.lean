module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable

@[expose] public section

open AlgebraicCurve
theorem AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable (K F : Type*) [Field K] [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F) :
    IsCurveOver K F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable.solution
