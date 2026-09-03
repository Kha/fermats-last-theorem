import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_FormalGroup_NSeries
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_IsOriginChartSection_map_ideal_comap_ker_eq_ker

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing
  HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.IsOriginChartSection.map_ideal_comap_ker_eq_ker
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (P : Section W) (χ : OriginChartRing W →+* T)
    (hP : IsOriginChartSection P χ) :
    Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (OriginChartRing W))).hom.hom
      (((Scheme.Hom.ker P.1).comap (originChartι W)).ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩) =
      RingHom.ker χ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsOriginChartSection_map_ideal_comap_ker_eq_ker.solution
