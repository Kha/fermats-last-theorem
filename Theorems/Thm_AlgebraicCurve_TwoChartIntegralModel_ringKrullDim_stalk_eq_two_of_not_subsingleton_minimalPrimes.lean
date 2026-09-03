import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_ringKrullDim_stalk_eq_two_of_not_subsingleton_minimalPrimes

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicCurve.TwoChartIntegralModel.ringKrullDim_stalk_eq_two_of_not_subsingleton_minimalPrimes
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (hR : ringKrullDim R = 1)
    (F : Type u) [Field F] [Algebra R F] (hinj : Function.Injective (algebraMap R F))
    (j : F) [Fact (j ≠ 0)]
    (ϖ : R) (z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase R F j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)))
    (hmany : ¬ ((Ideal.span {ϖz} : Ideal ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z)).minimalPrimes).Subsingleton) :
    ringKrullDim ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z) = 2 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_ringKrullDim_stalk_eq_two_of_not_subsingleton_minimalPrimes.solution
