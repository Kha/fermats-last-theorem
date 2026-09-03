import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_app_curveChange_injective_and_exists_of_app_eq_of_isReduced
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.IsClosedImmersion.app_curveChange_injective_and_exists_of_app_eq_of_isReduced
    {k : Type u} [Field k] {X Y₁ Y₂ Z : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (hXred : IsReduced X)
    (y₁ : Y₁ ⟶ Spec (CommRingCat.of k)) (y₂ : Y₂ ⟶ Spec (CommRingCat.of k)) (z : Z ⟶ Spec (CommRingCat.of k))
    (i₁ : SchemeHomOver y₁ x) (i₂ : SchemeHomOver y₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ p : X, p ∈ Set.range i₁.1.base ∨ p ∈ Set.range i₂.1.base)
    (j₁ : SchemeHomOver z y₁) (j₂ : SchemeHomOver z y₂) (hZ : IsPullback j₁.1 j₂.1 i₁.1 i₂.1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (hsq : curveChange j₁.1 j₁.2 t ≫ curveChange i₁.1 i₁.2 t = curveChange j₂.1 j₂.2 t ≫ curveChange i₂.1 i₂.2 t)
    (U : (Limits.pullback x t).Opens) :
    Function.Injective (fun f : Γ(Limits.pullback x t, U) =>
      ((curveChange i₁.1 i₁.2 t).app U f, (curveChange i₂.1 i₂.2 t).app U f)) ∧
      ∀ (g₁ : Γ(Limits.pullback y₁ t, (curveChange i₁.1 i₁.2 t) ⁻¹ᵁ U))
        (g₂ : Γ(Limits.pullback y₂ t, (curveChange i₂.1 i₂.2 t) ⁻¹ᵁ U)),
        (Limits.pullback z t).presheaf.map
            (eqToHom (show (curveChange j₂.1 j₂.2 t) ⁻¹ᵁ ((curveChange i₂.1 i₂.2 t) ⁻¹ᵁ U) =
                (curveChange j₁.1 j₁.2 t) ⁻¹ᵁ ((curveChange i₁.1 i₁.2 t) ⁻¹ᵁ U) by
              rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hsq])).op
          ((curveChange j₁.1 j₁.2 t).app ((curveChange i₁.1 i₁.2 t) ⁻¹ᵁ U) g₁) =
          (curveChange j₂.1 j₂.2 t).app ((curveChange i₂.1 i₂.2 t) ⁻¹ᵁ U) g₂ →
        ∃ f : Γ(Limits.pullback x t, U),
          (curveChange i₁.1 i₁.2 t).app U f = g₁ ∧ (curveChange i₂.1 i₂.2 t).app U f = g₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_app_curveChange_injective_and_exists_of_app_eq_of_isReduced.solution
