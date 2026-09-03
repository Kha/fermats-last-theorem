import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_MumfordUniformization
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_addMonoidHom_eq_of_apply_QL_eq_of_apply_eq_of_eq_pic0Mk_single_sub_single
attribute [-instance] AlgebraicCurve.TotallyDegenerateCovering.instDecidableEqV AlgebraicCurve.TotallyDegenerateCovering.instFintypeV AlgebraicCurve.TotallyDegenerateCovering.instDecidableEqE AlgebraicCurve.TotallyDegenerateCovering.instFintypeE
attribute [-simp] CerednikDrinfeld.DegeneracyData.FiniteHom.comp_deg CerednikDrinfeld.DegeneracyData.FiniteHom.pullback_apply CerednikDrinfeld.DegeneracyData.FiniteHom.comp_mapE AlgebraicCurve.TotallyDegenerateCovering.Hom.mk.injEq CerednikDrinfeld.DegeneracyData.FiniteHom.mk.sizeOf_spec CerednikDrinfeld.DegeneracyData.FiniteHom.mk.injEq AlgebraicCurve.TotallyDegenerateCovering.Hom.mk.sizeOf_spec CerednikDrinfeld.DegeneracyData.FiniteHom.pullbackFun_apply CerednikDrinfeld.DegeneracyData.FiniteHom.pushforward_apply AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_b AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_w AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_a AlgebraicCurve.TotallyDegenerateCovering.mk.sizeOf_spec AlgebraicCurve.TotallyDegenerateCovering.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

theorem CerednikDrinfeld.Mumford.addMonoidHom_eq_of_apply_QL_eq_of_apply_eq_of_eq_pic0Mk_single_sub_single
    {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (K₀ : Type) [Field K₀] [Algebra K₀ A.valuation.Completion]
    (FC : Type) [Field FC] [Algebra A.valuation.Completion FC] [hcurve : IsCurveOver A.valuation.Completion FC]
    (E V : Type) [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]
    (D : DegeneracyData E V)
    (pt : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion FC) (hpt_onto : Function.Surjective pt)
    (K : IntermediateField ℚ A.valuation.Completion) (ord : Additive (↥K)ˣ →+ ℤ)
    (P : PeriodDatum D (↥K) A.valuation.Completion ord)
    (eFull : P.TorusPoints →+ Pic0 A.valuation.Completion FC) (hsurj : Function.Surjective eFull)
    (hker : ∀ u : P.TorusPoints, eFull u = 0 ↔ u ∈ P.periodLattice)
    (T : Type) [AddCommGroup T] (f g : P.TorusPoints →+ T)
    (hΛ : ∀ z : ↥(ribbonKernel D), f (P.QL z) = g (P.QL z))
    (hdiff : ∀ (u : P.TorusPoints) (a b : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (Dv : Divisor.degZero (K := A.valuation.Completion) (F := FC)),
      (Dv : Divisor A.valuation.Completion FC) = Finsupp.single (pt a) 1 - Finsupp.single (pt b) 1 → eFull u = Pic0.mk Dv → f u = g u) :
    f = g := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_addMonoidHom_eq_of_apply_QL_eq_of_apply_eq_of_eq_pic0Mk_single_sub_single.solution
