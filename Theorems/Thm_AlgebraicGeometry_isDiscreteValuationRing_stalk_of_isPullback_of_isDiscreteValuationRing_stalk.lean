import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isDiscreteValuationRing_stalk_of_isPullback_of_isDiscreteValuationRing_stalk

set_option autoImplicit false

p2m_open "IsLocalRing CategoryTheory AlgebraicGeometry~exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd"

theorem AlgebraicGeometry.isDiscreteValuationRing_stalk_of_isPullback_of_isDiscreteValuationRing_stalk
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁]
    (ι₁' : A₀ →+* A₁) [IsLocalHom ι₁'] (hι₁' : Function.Injective ι₁')
    (hres₁ : Function.Surjective ((IsLocalRing.residue A₁).comp ι₁'))
    (ϖ₁ : A₁) (hϖ₁ : maximalIdeal A₁ = Ideal.span {ϖ₁})
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁)) (g₁ : X₁ ⟶ X₀)
    (hsq : IsPullback g₁ f₁ toBase₀ (Spec.map (CommRingCat.ofHom ι₁')))
    (η₁ : X₁) (hη₁ : f₁.base η₁ = closedPoint A₁)
    [IsDiscreteValuationRing (X₀.presheaf.stalk (g₁.base η₁))]
    (h𝔪₀ : maximalIdeal (X₀.presheaf.stalk (g₁.base η₁)) =
      Ideal.span {(X₀.presheaf.germ ⊤ (g₁.base η₁) trivial).hom
        (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom ϖ₀))}) :
    ∃ (_ : IsDomain (X₁.presheaf.stalk η₁)),
      IsDiscreteValuationRing (X₁.presheaf.stalk η₁) ∧
      maximalIdeal (X₁.presheaf.stalk η₁) =
        Ideal.span {(X₁.presheaf.germ ⊤ η₁ trivial).hom (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom ϖ₁))} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isDiscreteValuationRing_stalk_of_isPullback_of_isDiscreteValuationRing_stalk.solution
