import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_of_specMap_comp_eq_originChart

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_of_specMap_comp_eq_originChart
    {T : Type u} [CommRing T] [IsLocalRing T] (W : WeierstrassCurve.Projective T) (P : Section W)
    {K : Type u} [Field K] (π : T →+* K) (hπ : RingHom.ker π = maximalIdeal T)
    (χbar : OriginChartRing W →+* K)
    (h : Spec.map (CommRingCat.ofHom π) ≫ P.1 = Spec.map (CommRingCat.ofHom χbar) ≫ originChartι W)
    (hx : χbar (xOverY W) = 0) (hz : χbar (zOverY W) = 0) :
    ∃ χ : OriginChartRing W →+* T, ReducesToOrigin P χ (maximalIdeal T) ∧ π.comp χ = χbar := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_of_specMap_comp_eq_originChart.solution
