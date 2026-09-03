import Mathlib.AlgebraicGeometry.Geometrically.Connected
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_GeometricallyConnected_of_comp_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [GeometricallyConnected (f ≫ g)] [Surjective f] :
    GeometricallyConnected g := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ k ↦ ?_⟩

  have hX : ConnectedSpace ↥(pullback (f ≫ g) k) :=
    pullback_of_geometrically (GeometricallyConnected.geometrically_connectedSpace (f := f ≫ g)) K k

  let φ : pullback (f ≫ g) k ⟶ pullback g k :=
    pullback.map (f ≫ g) k g k f (𝟙 _) (𝟙 Z) (Category.comp_id _) (by simp)
  have hφ : Surjective φ :=
    MorphismProperty.pullbackMap (P := @Surjective) ‹Surjective f› inferInstance rfl
      (Category.id_comp _).symm
  rw [connectedSpace_iff_univ, ← hφ.surj.range_eq]
  exact isConnected_range φ.continuous
