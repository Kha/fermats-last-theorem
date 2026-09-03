import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_le_iff_map_localization_comap_ideal_top_le

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

theorem AlgebraicGeometry.Scheme.IdealSheafData.map_germ_le_iff_map_localization_comap_ideal_top_le
    {Y : Scheme.{u}} (A : Type u) [CommRing A] (ι : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion ι]
    (𝔭 : Ideal A) [𝔭.IsPrime] (I J : Y.IdealSheafData)
    (U : Y.affineOpens) (hU : ι.base (⟨𝔭, inferInstance⟩ : PrimeSpectrum A) ∈ (U : Y.Opens)) :
    Ideal.map (Y.presheaf.germ (U : Y.Opens) _ hU).hom (I.ideal U) ≤
        Ideal.map (Y.presheaf.germ (U : Y.Opens) _ hU).hom (J.ideal U) ↔
      Ideal.map ((algebraMap A (Localization.AtPrime 𝔭)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom)
          ((I.comap ι).ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩) ≤
        Ideal.map ((algebraMap A (Localization.AtPrime 𝔭)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom)
          ((J.comap ι).ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_le_iff_map_localization_comap_ideal_top_le.solution
