import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_comap_ideal_eq_map_stalkMap_of_isOpenImmersion
import Theorems.Thm_AlgebraicGeometry_Spec_map_germ_le_iff_map_algebraMap_localization_le
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_le_iff_map_localization_comap_ideal_top_le

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

theorem g3_map_le_map_iff_of_bijective {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Bijective φ) (a b : Ideal R) : a.map φ ≤ b.map φ ↔ a ≤ b := by
  refine ⟨fun h => ?_, fun h => Ideal.map_mono h⟩
  have := Ideal.comap_mono (f := φ) h
  rwa [Ideal.comap_map_of_bijective φ hφ, Ideal.comap_map_of_bijective φ hφ] at this

theorem solution
    {Y : Scheme.{u}} (A : Type u) [CommRing A] (ι : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion ι]
    (𝔭 : Ideal A) [𝔭.IsPrime] (I J : Y.IdealSheafData)
    (U : Y.affineOpens) (hU : ι.base (⟨𝔭, inferInstance⟩ : PrimeSpectrum A) ∈ (U : Y.Opens)) :
    Ideal.map (Y.presheaf.germ (U : Y.Opens) _ hU).hom (I.ideal U) ≤
        Ideal.map (Y.presheaf.germ (U : Y.Opens) _ hU).hom (J.ideal U) ↔
      Ideal.map ((algebraMap A (Localization.AtPrime 𝔭)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom)
          ((I.comap ι).ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩) ≤
        Ideal.map ((algebraMap A (Localization.AtPrime 𝔭)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom)
          ((J.comap ι).ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩) := by
  set x : PrimeSpectrum A := ⟨𝔭, inferInstance⟩ with hx
  have hbij : Function.Bijective (ι.stalkMap x).hom :=
    ConcreteCategory.bijective_of_isIso (ι.stalkMap x)
  have hI := AlgebraicGeometry.Scheme.IdealSheafData.map_germ_comap_ideal_eq_map_stalkMap_of_isOpenImmersion
    ι I x U hU ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩ trivial
  have hJ := AlgebraicGeometry.Scheme.IdealSheafData.map_germ_comap_ideal_eq_map_stalkMap_of_isOpenImmersion
    ι J x U hU ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩ trivial
  rw [← g3_map_le_map_iff_of_bijective _ hbij, ← hI, ← hJ]
  exact AlgebraicGeometry.Spec.map_germ_le_iff_map_algebraMap_localization_le A 𝔭 _ _
