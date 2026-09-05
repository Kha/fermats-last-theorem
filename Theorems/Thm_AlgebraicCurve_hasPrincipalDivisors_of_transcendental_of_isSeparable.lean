module

public import Definitions.Def_AlgebraicCurve_IsCurveOver
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_hasPrincipalDivisors_of_transcendental_of_isSeparable

@[expose] public section
open AlgebraicCurve IntermediateField
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
theorem AlgebraicCurve.hasPrincipalDivisors_of_transcendental_of_isSeparable
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F) :
    HasPrincipalDivisors K F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_transcendental_of_isSeparable.solution
