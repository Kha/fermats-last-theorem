import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Spec_map_germ_le_iff_map_algebraMap_localization_le

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

theorem AlgebraicGeometry.Spec.map_germ_le_iff_map_algebraMap_localization_le
    (A : Type u) [CommRing A] (𝔭 : Ideal A) [𝔭.IsPrime]
    (J K : Ideal ((Spec (CommRingCat.of A)).presheaf.obj (Opposite.op ⊤))) :
    Ideal.map ((Spec (CommRingCat.of A)).presheaf.germ ⊤ (⟨𝔭, inferInstance⟩ : PrimeSpectrum A) trivial).hom J ≤
        Ideal.map ((Spec (CommRingCat.of A)).presheaf.germ ⊤ (⟨𝔭, inferInstance⟩ : PrimeSpectrum A) trivial).hom K ↔
      Ideal.map ((algebraMap A (Localization.AtPrime 𝔭)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom) J ≤
        Ideal.map ((algebraMap A (Localization.AtPrime 𝔭)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom) K := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Spec_map_germ_le_iff_map_algebraMap_localization_le.solution
