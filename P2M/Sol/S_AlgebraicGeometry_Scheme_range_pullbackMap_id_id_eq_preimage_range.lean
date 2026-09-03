import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_range_pullbackMap_id_id_eq_preimage_range

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {X S T T' : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (g' : T' ⟶ S) (i : T' ⟶ T)
    (e₁ : f ≫ 𝟙 S = 𝟙 X ≫ f) (e₂ : g' ≫ 𝟙 S = i ≫ g) :
    Set.range (pullback.map f g' f g (𝟙 X) i (𝟙 S) e₁ e₂).base =
      (pullback.snd f g).base ⁻¹' Set.range i.base := by
  have h := Scheme.Pullback.range_map f g' f g (𝟙 X) i (𝟙 S) e₁ e₂
  have h1 : Set.range ((𝟙 X : X ⟶ X) : X → X) = Set.univ := by
    ext x
    exact ⟨fun _ => trivial, fun _ => ⟨x, rfl⟩⟩
  rw [h1, Set.preimage_univ, Set.univ_inter] at h
  exact h
