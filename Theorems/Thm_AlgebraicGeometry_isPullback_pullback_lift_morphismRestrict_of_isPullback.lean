import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isPullback_pullback_lift_morphismRestrict_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isPullback_pullback_lift_morphismRestrict_of_isPullback
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (U₁ U₂ : A₀.Opens)
    (Y₁ Y₂ : Scheme.{u}) (q₁ : Y₁ ⟶ Spec (CommRingCat.of T')) (q₂ : Y₂ ⟶ Spec (CommRingCat.of T'))
    (g₁ : (↑U₁ : Scheme.{u}) ⟶ Y₁) (g₂ : (↑U₂ : Scheme.{u}) ⟶ Y₂)
    (hg₁ : IsPullback g₁ (U₁.ι ≫ f₀) q₁ (Spec.map (CommRingCat.ofHom π)))
    (hg₂ : IsPullback g₂ (U₂.ι ≫ f₀) q₂ (Spec.map (CommRingCat.ofHom π))) :
    IsPullback (pullback.lift
        ((pullback f₀ f₀).homOfLE (inf_le_left : pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂ ≤ _) ≫
          (pullback.fst f₀ f₀ ∣_ U₁) ≫ g₁)
        ((pullback f₀ f₀).homOfLE (inf_le_right : pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂ ≤ _) ≫
          (pullback.snd f₀ f₀ ∣_ U₂) ≫ g₂)
        (by simp only [Category.assoc]; rw [hg₁.w, hg₂.w];
            simp only [Category.assoc, morphismRestrict_ι_assoc, Scheme.homOfLE_ι_assoc, pullback.condition_assoc]) :
        (↑(pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂) : Scheme.{u}) ⟶ pullback q₁ q₂)
      ((pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂).ι ≫ pullback.fst f₀ f₀ ≫ f₀)
      (pullback.fst q₁ q₂ ≫ q₁) (Spec.map (CommRingCat.ofHom π)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isPullback_pullback_lift_morphismRestrict_of_isPullback.solution
