import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_forall_exists_twoAffineOpenCover_linearEquiv_sectionsOf_fibreModule

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.forall_exists_twoAffineOpenCover_linearEquiv_sectionsOf_fibreModule
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hx : s ≫ t = x) (M : (pullback c t).Modules) :
    (∀ 𝒱 : (pullback c x).TwoAffineOpenCover, ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x)
          ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj M)).H0) ∧
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x)
          ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj M)).H1)) ∧
    (∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover, ∃ 𝒱 : (pullback c x).TwoAffineOpenCover,
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x)
          ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj M)).H0) ∧
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x)
          ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj M)).H1)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_twoAffineOpenCover_linearEquiv_sectionsOf_fibreModule.solution
