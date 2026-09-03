import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_nonempty_schemeHomOver_id_toBase_of_algHom

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra AlgebraicCurve.TwoChartIntegralModel

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (φ : ↥(chartAlgInf R F j) →ₐ[R] R) :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) (toBase R F j)) := by
  have hcomp : φ.toRingHom.comp (algebraMap R ↥(chartAlgInf R F j)) = RingHom.id R := by
    ext x
    simpa using φ.commutes x
  refine ⟨⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ιInf R F j, ?_⟩⟩
  rw [Category.assoc, ιInf_toBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  simp
