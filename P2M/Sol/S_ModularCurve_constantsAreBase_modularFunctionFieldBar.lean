module

public import Definitions.Def_ModularCurve_ArithmeticGalois
public import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Sol.S_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional
import P2M.Sol.S_ModularCurve_laurentBaseChange_adjoin_pair
import P2M.Sol.S_ModularCurve_functionFieldGeneration
import P2M.Sol.S_ModularCurve_order_jqModC
import P2M.Sol.S_ModularCurve_deg_qInftyPlaceBar
import P2M.Sol.S_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import P2M.Util
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_DegeneracyTower
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

namespace P2MW.S_ModularCurve_constantsAreBase_modularFunctionFieldBar

set_option autoImplicit false

noncomputable section

open IntermediateField

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "HasPrincipalDivisors ConstantsAreBase constantsAreBase_of_deg_eq_one"
p2m_open "AlgebraicCurve~IsCurveOver"

namespace RCAB

open ModularCurve

private theorem constantsAreBase_of_mem (K : Type*) [Field K] (E : IntermediateField K (LaurentSeries K))
    [HasPrincipalDivisors K E] {j : LaurentSeries K} (hjE : j ∈ E) (hj : j.order = -1) :
    ConstantsAreBase K E :=
  have h : ∃ x : E, (qSeriesBar K E x).order = -1 := ⟨⟨j, hjE⟩, hj⟩
  constantsAreBase_of_deg_eq_one (qInftyPlaceBar K E h) (deg_qInftyPlaceBar K h)

private theorem constantsAreBase_laurentBaseChange (L : Type*) [Field L] {instQL : Algebra ℚ L}
    (N : ℕ) [NeZero N] : ConstantsAreBase L (laurentBaseChange L (modularFunctionFieldFull N)) := by
  haveI := hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional L N
  have hmem : jqModC L ∈ laurentBaseChange L (modularFunctionFieldFull N) := by
    rw [laurentBaseChange_adjoin_pair L N (functionFieldGeneration N)]
    exact jqModC_mem L N
  exact constantsAreBase_of_mem L _ hmem (order_jqModC L)

end RCAB

end AlgebraicCurve

end

p2m_open "ModularCurve AlgebraicCurve~IsCurveOver P2MW.S_ModularCurve_constantsAreBase_modularFunctionFieldBar.AlgebraicCurve"

theorem solution (N : ℕ) [NeZero N] :
    ConstantsAreBase (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  AlgebraicCurve.RCAB.constantsAreBase_laurentBaseChange (AlgebraicClosure ℚ) N

example : ∀ (N : ℕ) [NeZero N], ConstantsAreBase (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := @solution
end S_ModularCurve_constantsAreBase_modularFunctionFieldBar
end P2MW

public section
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] ModularCurve.jqNModC_one ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
attribute [-simp] AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong
attribute [-simp] ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
open ModularCurve AlgebraicCurve
theorem ModularCurve.constantsAreBase_modularFunctionFieldBar (N : ℕ) [NeZero N] :
    ConstantsAreBase (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_constantsAreBase_modularFunctionFieldBar.solution
end
