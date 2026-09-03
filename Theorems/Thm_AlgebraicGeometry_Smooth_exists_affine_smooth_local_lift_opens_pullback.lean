import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_exists_affine_smooth_local_lift_opens_pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits open AlgebraicGeometry hiding isAffine_of_isClosedImmersion_of_surjective

universe u

theorem AlgebraicGeometry.Smooth.exists_affine_smooth_local_lift_opens_pullback
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (U₁ U₂ : A₀.Opens)
    (Y₁ Y₂ : Scheme.{u}) (q₁ : Y₁ ⟶ Spec (CommRingCat.of T')) (q₂ : Y₂ ⟶ Spec (CommRingCat.of T'))
    (hq₁ : Smooth q₁) (hq₂ : Smooth q₂)
    (g₁ : (↑U₁ : Scheme.{u}) ⟶ Y₁) (g₂ : (↑U₂ : Scheme.{u}) ⟶ Y₂)
    (hg₁ : IsPullback g₁ (U₁.ι ≫ f₀) q₁ (Spec.map (CommRingCat.ofHom π)))
    (hg₂ : IsPullback g₂ (U₂.ι ≫ f₀) q₂ (Spec.map (CommRingCat.ofHom π)))
    (V : (pullback f₀ f₀).Opens) (hVaff : IsAffineOpen V)
    (hV₁ : V ≤ pullback.fst f₀ f₀ ⁻¹ᵁ U₁) (hV₂ : V ≤ pullback.snd f₀ f₀ ⁻¹ᵁ U₂) :
    ∃ (Z : Scheme.{u}) (qZ : Z ⟶ Spec (CommRingCat.of T')) (_ : IsAffine Z) (_ : Smooth qZ)
      (gZ : (↑V : Scheme.{u}) ⟶ Z)
      (_ : IsPullback gZ (V.ι ≫ pullback.fst f₀ f₀ ≫ f₀) qZ (Spec.map (CommRingCat.ofHom π)))
      (h₁ : Z ⟶ Y₁) (h₂ : Z ⟶ Y₂),
      (h₁ ≫ q₁ = qZ ∧ gZ ≫ h₁ = (pullback f₀ f₀).homOfLE hV₁ ≫ (pullback.fst f₀ f₀ ∣_ U₁) ≫ g₁) ∧
      (h₂ ≫ q₂ = qZ ∧ gZ ≫ h₂ = (pullback f₀ f₀).homOfLE hV₂ ≫ (pullback.snd f₀ f₀ ∣_ U₂) ≫ g₂) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_exists_affine_smooth_local_lift_opens_pullback.solution
