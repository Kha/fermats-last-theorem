import Mathlib
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_locallyOfFinitePresentation_toBase
import Definitions.Def_ModularCurve_DRModelPackage
import P2M.Util
namespace P2MW.S_ModularCurve_DRModelPackage_locallyOfFinitePresentation_toBase

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem solution (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) :
    LocallyOfFinitePresentation (DRModel.toBase p) := by

  have hFin : Algebra.FiniteType ℤ
      ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) := by
    letI := (TwoChartIntegralModel.polynomialToChartFin ℤ ↥(modularFunctionFieldFull p)
      (IgusaScheme.jFull p)).toRingHom.toAlgebra
    haveI : IsScalarTower ℤ (Polynomial ℤ)
        ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) :=
      IsScalarTower.of_algebraMap_eq fun r =>
        ((TwoChartIntegralModel.polynomialToChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).commutes r).symm
    haveI : Module.Finite (Polynomial ℤ)
        ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) := 𝔛.chartFin_finite
    exact Algebra.FiniteType.trans (S := Polynomial ℤ) inferInstance inferInstance
  have hInf : Algebra.FiniteType ℤ
      ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) := by
    letI := (TwoChartIntegralModel.polynomialToChartInf ℤ ↥(modularFunctionFieldFull p)
      (IgusaScheme.jFull p)).toRingHom.toAlgebra
    haveI : IsScalarTower ℤ (Polynomial ℤ)
        ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) :=
      IsScalarTower.of_algebraMap_eq fun r =>
        ((TwoChartIntegralModel.polynomialToChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).commutes r).symm
    haveI : Module.Finite (Polynomial ℤ)
        ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) := 𝔛.chartInf_finite
    exact Algebra.FiniteType.trans (S := Polynomial ℤ) inferInstance inferInstance
  haveI := hFin; haveI := hInf
  exact AlgebraicCurve.TwoChartIntegralModel.locallyOfFinitePresentation_toBase ℤ ↥(modularFunctionFieldFull p)
    (IgusaScheme.jFull p)
