import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_one_comp_projMap_eq_of_isOriginChartSection

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.one_comp_projMap_eq_of_isOriginChartSection
    {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ)
    (G : RelativeGroupLaw T (projModelStrCR W)) (L : RelativeGroupLaw T' (projModelStrCR (W.map f)))
    (χ : OriginChartRing W →+* T) (hχ : IsOriginChartSection (G.one (𝟙 _)) χ)
    (hχx : χ (xOverY W) = 0) (hχz : χ (zOverY W) = 0)
    (χ' : OriginChartRing (W.map f) →+* T') (hχ' : IsOriginChartSection (L.one (𝟙 _)) χ')
    (hχ'x : χ' (xOverY (W.map f)) = 0) (hχ'z : χ' (zOverY (W.map f)) = 0) :
    (L.one (𝟙 (Spec (CommRingCat.of T')))).1 ≫ Proj.map φ hφ =
      Spec.map (CommRingCat.ofHom f) ≫ (G.one (𝟙 (Spec (CommRingCat.of T)))).1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_one_comp_projMap_eq_of_isOriginChartSection.solution
