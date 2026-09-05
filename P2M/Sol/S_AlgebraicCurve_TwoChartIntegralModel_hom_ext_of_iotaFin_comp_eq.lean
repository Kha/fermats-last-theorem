import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral
import P2M.Util
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_hom_ext_of_iotaFin_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

namespace PinsBody

theorem isDominant_ιFin (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    IsDominant (ιFin R F j) := by
  haveI := TwoChartIntegralModel.isIntegral R F j
  exact ⟨(ιFin R F j).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

theorem hom_ext (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {Y Z : Scheme.{u}} (f g : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ Y) (q : Y ⟶ Z) [IsSeparated q]
    (h : f ≫ q = g ≫ q) (hFin : ιFin R F j ≫ f = ιFin R F j ≫ g) : f = g := by
  haveI := TwoChartIntegralModel.isIntegral R F j
  haveI := isDominant_ιFin R F j
  exact ext_of_isDominant_of_isSeparated q h (ιFin R F j) hFin

end PinsBody

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {Y Z : Scheme.{u}} (f g : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ Y) (q : Y ⟶ Z) [IsSeparated q]
    (h : f ≫ q = g ≫ q) (hFin : ιFin R F j ≫ f = ιFin R F j ≫ g) : f = g :=
  PinsBody.hom_ext R F j f g q h hFin

