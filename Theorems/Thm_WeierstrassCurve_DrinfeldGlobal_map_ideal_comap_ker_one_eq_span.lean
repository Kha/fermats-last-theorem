import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_map_ideal_comap_ker_one_eq_span

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.map_ideal_comap_ker_one_eq_span
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (G : RelativeGroupLaw T (projModelStrCR W))
    (hGone : ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    {B : Type u} [CommRing B] (χ : OriginChartRing W →+* B) :
    Ideal.map (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
      (((Scheme.Hom.ker (G.one (𝟙 _)).1).comap (Spec.map (CommRingCat.ofHom χ) ≫ originChartι W)).ideal
        ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩) =
      Ideal.span {χ (xOverY W), χ (zOverY W)} := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_map_ideal_comap_ker_one_eq_span.solution
