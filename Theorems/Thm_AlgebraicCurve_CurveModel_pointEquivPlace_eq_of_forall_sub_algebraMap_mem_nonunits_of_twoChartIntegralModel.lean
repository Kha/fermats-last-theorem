import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_pointEquivPlace_eq_of_forall_sub_algebraMap_mem_nonunits_of_twoChartIntegralModel

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u v

theorem AlgebraicCurve.CurveModel.pointEquivPlace_eq_of_forall_sub_algebraMap_mem_nonunits_of_twoChartIntegralModel
    {R F₀ : Type u} [CommRing R] [Field F₀] [Algebra R F₀] (j : F₀) [Fact (j ≠ 0)]
    {K : Type u} [Field K] [IsAlgClosed K] {F : Type v} [Field F] [Algebra K F]
    (N : AlgebraicCurve.CurveModel K F) (h : N.C ⟶ AlgebraicCurve.TwoChartIntegralModel R F₀ j)
    (hinj : ∀ y y' : {q : Spec (CommRingCat.of K) ⟶ N.C // q ≫ N.toBase = 𝟙 _}, y.1 ≫ h = y'.1 ≫ h → y = y')
    (πF : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F₀ j) →+* F) (πI : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F₀ j) →+* F)
    (hπj : πI (AlgebraicCurve.TwoChartIntegralModel.jInvChartInf R F₀ j) * πF (AlgebraicCurve.TwoChartIntegralModel.jChartFin R F₀ j) = 1)
    (hcenF : ∀ (y : {q : Spec (CommRingCat.of K) ⟶ N.C // q ≫ N.toBase = 𝟙 _}) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F₀ j) →+* K),
      y.1 ≫ h = Spec.map (CommRingCat.ofHom β) ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin R F₀ j →
      ∀ b, πF b - algebraMap K F (β b) ∈ (N.pointEquivPlace y).toValuationSubring.nonunits)
    (hcenI : ∀ (y : {q : Spec (CommRingCat.of K) ⟶ N.C // q ≫ N.toBase = 𝟙 _}) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F₀ j) →+* K),
      y.1 ≫ h = Spec.map (CommRingCat.ofHom β) ≫ AlgebraicCurve.TwoChartIntegralModel.ιInf R F₀ j →
      ∀ b, πI b - algebraMap K F (β b) ∈ (N.pointEquivPlace y).toValuationSubring.nonunits) :
    (∀ (w : AlgebraicCurve.Place K F) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F₀ j) →+* K),
        (∀ b, πF b - algebraMap K F (β b) ∈ w.toValuationSubring.nonunits) →
        ∀ y : {q : Spec (CommRingCat.of K) ⟶ N.C // q ≫ N.toBase = 𝟙 _}, y.1 ≫ h = Spec.map (CommRingCat.ofHom β) ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin R F₀ j → N.pointEquivPlace y = w) ∧
    (∀ (w : AlgebraicCurve.Place K F) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F₀ j) →+* K),
        (∀ b, πI b - algebraMap K F (β b) ∈ w.toValuationSubring.nonunits) →
        ∀ y : {q : Spec (CommRingCat.of K) ⟶ N.C // q ≫ N.toBase = 𝟙 _}, y.1 ≫ h = Spec.map (CommRingCat.ofHom β) ≫ AlgebraicCurve.TwoChartIntegralModel.ιInf R F₀ j → N.pointEquivPlace y = w) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_pointEquivPlace_eq_of_forall_sub_algebraMap_mem_nonunits_of_twoChartIntegralModel.solution
