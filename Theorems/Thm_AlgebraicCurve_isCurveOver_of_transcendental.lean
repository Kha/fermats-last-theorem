module

public import Definitions.Def_AlgebraicCurve_IsCurveOver
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_isCurveOver_of_transcendental

@[expose] public section
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
open AlgebraicCurve IntermediateField
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
theorem AlgebraicCurve.isCurveOver_of_transcendental
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F) :
    IsCurveOver K F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_isCurveOver_of_transcendental.solution
