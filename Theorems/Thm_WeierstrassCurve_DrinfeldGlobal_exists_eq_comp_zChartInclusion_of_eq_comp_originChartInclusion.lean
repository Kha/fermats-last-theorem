import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_exists_eq_comp_zChartInclusion_of_eq_comp_originChartInclusion

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_eq_comp_zChartInclusion_of_eq_comp_originChartInclusion
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) {F : Type u} [Field F]
    (p : Spec (CommRingCat.of F) ⟶ projModelCR W.toProjective) (χ : OriginChartRing W →+* F)
    (hp : p = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W) (hv : χ (zOverY W) ≠ 0) :
    ∃ χ' : ZChartRing W.toProjective →+* F,
      p = Spec.map (CommRingCat.ofHom χ') ≫ zChartι W.toProjective ∧
      χ' (xOverZ W.toProjective) = χ (xOverY W) / χ (zOverY W) ∧
      χ' (yOverZ W.toProjective) = 1 / χ (zOverY W) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_eq_comp_zChartInclusion_of_eq_comp_originChartInclusion.solution
