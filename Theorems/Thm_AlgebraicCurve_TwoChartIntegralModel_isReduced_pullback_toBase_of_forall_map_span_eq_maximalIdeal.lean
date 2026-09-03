import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_forall_map_span_eq_maximalIdeal

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel~finiteType_chartAlgFin_and_chartAlgInf"

theorem AlgebraicCurve.TwoChartIntegralModel.isReduced_pullback_toBase_of_forall_map_span_eq_maximalIdeal
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (IsLocalRing.ResidueField R)]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hFin : ∀ (P : Ideal ↥(chartAlgFin R F j)) [P.IsPrime],
      P ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}).minimalPrimes →
        Ideal.map (algebraMap ↥(chartAlgFin R F j) (Localization.AtPrime P))
            (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}) =
          IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hInf : ∀ (P : Ideal ↥(chartAlgInf R F j)) [P.IsPrime],
      P ∈ (Ideal.span {algebraMap R ↥(chartAlgInf R F j) ϖ}).minimalPrimes →
        Ideal.map (algebraMap ↥(chartAlgInf R F j) (Localization.AtPrime P))
            (Ideal.span {algebraMap R ↥(chartAlgInf R F j) ϖ}) =
          IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (κ : Type u) [Field κ] [Algebra R κ] (hκ : algebraMap R κ ϖ = 0) :
    IsReduced (pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_forall_map_span_eq_maximalIdeal.solution
