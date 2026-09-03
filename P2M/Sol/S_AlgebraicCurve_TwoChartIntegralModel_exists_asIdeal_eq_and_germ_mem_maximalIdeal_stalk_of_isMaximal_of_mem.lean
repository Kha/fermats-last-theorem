import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgFin
import P2M.Util
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_asIdeal_eq_and_germ_mem_maximalIdeal_stalk_of_isMaximal_of_mem

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (y : Ideal ↥(chartAlgFin R F j)) (hy : y.IsMaximal)
    (r : R) (hr : algebraMap R ↥(chartAlgFin R F j) r ∈ y) :
    ∃ (y' : ↥(XFin R F j)), y'.asIdeal = y ∧
      (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ ((ιFin R F j).base y') trivial).hom
          (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) ∈
        IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y')) := by
  classical
  haveI : y.IsPrime := hy.isPrime
  let y' : ↥(XFin R F j) := (⟨y, hy.isPrime⟩ : PrimeSpectrum ↥(chartAlgFin R F j))
  refine ⟨y', rfl, ?_⟩
  obtain ⟨e, he, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_chartAlgFin R F j y' ⟨y', trivial, rfl⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hu' := hu.map e.hom.hom
  rw [he r] at hu'
  have hmem : algebraMap R (Localization.AtPrime y'.asIdeal) r ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime y'.asIdeal) := by
    rw [IsScalarTower.algebraMap_apply R ↥(chartAlgFin R F j) (Localization.AtPrime y'.asIdeal) r,
      ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hr
  exact ((IsLocalRing.mem_maximalIdeal _).mp hmem) hu'
