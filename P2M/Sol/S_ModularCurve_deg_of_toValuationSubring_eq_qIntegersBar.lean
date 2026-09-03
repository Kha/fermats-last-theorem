import Definitions.Def_ModularCurve_QAdicPlace
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import P2M.Util
namespace P2MW.S_ModularCurve_deg_of_toValuationSubring_eq_qIntegersBar

open ModularCurve AlgebraicCurve

theorem solution {F : IntermediateField ℚ (LaurentSeries ℚ)} [i : Algebra ℚ F] (h : ∃ j : F, (qSeriesBar ℚ F j).order = -1) (v : Place ℚ F) (hv : v.toValuationSubring = qIntegersBar ℚ F) : v.deg = 1 := by
  obtain rfl : i = SubalgebraClass.toAlgebra F := Subsingleton.elim _ _
  obtain rfl : v = qInftyPlaceBar ℚ F h :=
    @Place.ext ℚ F _ _ (SubalgebraClass.toAlgebra F) _ _ hv
  exact ModularCurve.deg_qInftyPlaceBar ℚ h
