import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_of_specMap_comp_eq_zChart

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_of_specMap_comp_eq_zChart
    {T : Type u} [CommRing T] [IsLocalRing T] (W : WeierstrassCurve.Projective T) (S : Section W)
    {K : Type u} [Field K] (π : T →+* K) (hπ : RingHom.ker π = maximalIdeal T)
    (ρbar : ZChartRing W →+* K)
    (h : Spec.map (CommRingCat.ofHom π) ≫ S.1 = Spec.map (CommRingCat.ofHom ρbar) ≫ zChartι W) :
    ∃ x y : T, IsSectionThrough S x y ∧ π x = ρbar (xOverZ W) ∧ π y = ρbar (yOverZ W) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_of_specMap_comp_eq_zChart.solution
