import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_exists_forall_basis_pushforward_dualNumberThickening_of_forall_basis
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp] AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry NeronModelInfra
  AlgebraicGeometry.RelPicard AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem AlgebraicGeometry.RelPicard.exists_forall_basis_pushforward_dualNumberThickening_of_forall_basis
    {R : Type u} [CommRing R] {C C' : Scheme.{u}} (c : C ⟶ Spec (.of R)) (c' : C' ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover) (𝒲 : C'.TwoAffineOpenCover)
    (f : HomOver (RingHom.id A) (𝒱.pullback c A) (pullback.snd c (specMap R A))
      (𝒲.pullback c' A) (pullback.snd c' (specMap R A)))
    (fε : HomOver (RingHom.id (DualNumber A))
      (𝒱.pullback c (DualNumber A)) (pullback.snd c (specMap R (DualNumber A)))
      (𝒲.pullback c' (DualNumber A)) (pullback.snd c' (specMap R (DualNumber A))))
    [IsAffineHom f.hom]

    (hsq : IsPullback fε.hom (dualNumberThickening A 𝒲 c').hom (dualNumberThickening A 𝒱 c).hom f.hom)
    (d : ℕ) (U : (Limits.pullback c (specMap R A)).Opens)
    (Uε : (Limits.pullback c (specMap R (DualNumber A))).Opens) (hUε : Uε = (dualNumberThickening A 𝒱 c).hom ⁻¹ᵁ U)

    (e : Fin d → Γ((Scheme.Modules.pushforward f.hom).obj (𝟙_ _), U))
    (he : ∀ (W : (Limits.pullback c (specMap R A)).Opens) (hW : W ≤ U),
      ∃ b : Module.Basis (Fin d) Γ(Limits.pullback c (specMap R A), W)
          Γ((Scheme.Modules.pushforward f.hom).obj (𝟙_ _), W),
        ∀ i, b i = ((Scheme.Modules.pushforward f.hom).obj (𝟙_ _)).presheaf.map (homOfLE hW).op (e i)) :
    ∃ eε : Fin d → Γ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _), Uε),
      ∀ (W : (Limits.pullback c (specMap R (DualNumber A))).Opens) (hW : W ≤ Uε),
        ∃ b : Module.Basis (Fin d) Γ(Limits.pullback c (specMap R (DualNumber A)), W)
            Γ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _), W),
          ∀ i, b i = ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _)).presheaf.map (homOfLE hW).op (eε i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_exists_forall_basis_pushforward_dualNumberThickening_of_forall_basis.solution
