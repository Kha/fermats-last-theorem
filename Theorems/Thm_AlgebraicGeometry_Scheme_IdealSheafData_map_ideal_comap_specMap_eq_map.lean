import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_map_ideal_comap_specMap_eq_map

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.IdealSheafData.map_ideal_comap_specMap_eq_map
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (I : (Spec (CommRingCat.of A)).IdealSheafData) :
    Ideal.map (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
      ((I.comap (Spec.map (CommRingCat.ofHom φ))).ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩) =
      Ideal.map φ (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
        (I.ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_map_ideal_comap_specMap_eq_map.solution
