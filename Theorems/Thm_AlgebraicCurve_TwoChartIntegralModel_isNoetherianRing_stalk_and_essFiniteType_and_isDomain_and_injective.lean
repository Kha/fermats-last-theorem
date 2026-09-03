import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_isNoetherianRing_stalk_and_essFiniteType_and_isDomain_and_injective

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.isNoetherianRing_stalk_and_essFiniteType_and_isDomain_and_injective
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (F : Type u) [Field F] [Algebra R F]
    (hinj : Function.Injective (algebraMap R F)) (j : F) [Fact (j ≠ 0)]
    (hFT : Algebra.FiniteType R ↥(chartAlgFin R F j)) (hFT' : Algebra.FiniteType R ↥(chartAlgInf R F j))
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))

    [Algebra R ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z)]
    (halg : ∀ r : R, algebraMap R ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z) r =
      (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ z trivial).hom
        (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))) :
    IsNoetherianRing ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z) ∧
    Algebra.EssFiniteType R ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z) ∧
    IsDomain ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z) ∧
    Function.Injective (algebraMap R ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isNoetherianRing_stalk_and_essFiniteType_and_isDomain_and_injective.solution
