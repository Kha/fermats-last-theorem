import Mathlib
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_placesOf_preimage_subset_preimage_restrictAlong_placesOf
import Theorems.Thm_AlgebraicCurve_preimage_restrictAlong_placesOf_subset_placesOf_preimage
import P2M.Util
namespace P2MW.S_AlgebraicCurve_placesOf_preimage_eq_preimage_restrictAlong_placesOf

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem solution
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsIntegral Y] [IsSeparated cX] [SmoothOfRelativeDimension 1 cX]
    [IsProper cY] [SmoothOfRelativeDimension 1 cY]
    (π : Y ⟶ X) [UniversallyClosed π]
    (φ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      X.functionField →ₐ[K] Y.functionField)
    (hφ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      φ.toRingHom.IsIntegral)
    (hφπ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      Y.fromSpecStalk (genericPoint Y) ≫ π =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.fromSpecStalk (genericPoint X))
    (U : X.Opens) :
    letI := (baseToFunctionField cX).toAlgebra
    letI := (baseToFunctionField cY).toAlgebra
    placesOf cY (π ⁻¹ᵁ U) = (Place.restrictAlong φ hφ) ⁻¹' placesOf cX U :=
  Set.Subset.antisymm (AlgebraicCurve.placesOf_preimage_subset_preimage_restrictAlong_placesOf cX cY π φ hφ hφπ U)
    (AlgebraicCurve.preimage_restrictAlong_placesOf_subset_placesOf_preimage cX cY π φ hφ hφπ U)
