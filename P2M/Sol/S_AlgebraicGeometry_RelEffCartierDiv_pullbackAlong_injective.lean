import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_injective_of_flat_of_surjective
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_injective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open AlgebraicGeometry in
theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}
    (φ : T ⟶ T') (hφ : φ ≫ g' = g) [Flat φ] [Surjective φ] :
    Function.Injective fun D : RelEffCartierDiv f r g' => D.pullbackAlong φ hφ := by
  intro D E h
  have hI := congrArg RelEffCartierDiv.I h
  change D.I.comap (mapOnProdOver f φ hφ) = E.I.comap (mapOnProdOver f φ hφ) at hI

  haveI : Flat (mapOnProdOver f φ hφ) :=
    MorphismProperty.of_isPullback (isPullback_mapOnProdOver f φ hφ).flip inferInstance
  haveI : Surjective (mapOnProdOver f φ hφ) :=
    MorphismProperty.of_isPullback (isPullback_mapOnProdOver f φ hφ).flip inferInstance
  exact RelEffCartierDiv.ext
    (Scheme.IdealSheafData.comap_injective_of_flat_of_surjective (mapOnProdOver f φ hφ) hI)
