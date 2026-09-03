import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul
attribute [-instance] SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp] PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry NeronModelInfra
  AlgebraicGeometry.RelPicard AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem AlgebraicGeometry.RelPicard.exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul
    {R : Type u} [CommRing R] {C C' : Scheme.{u}} (c : C ⟶ Spec (.of R)) (c' : C' ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover) (𝒲 : C'.TwoAffineOpenCover)
    (f : HomOver (RingHom.id A) (𝒱.pullback c A) (pullback.snd c (specMap R A))
      (𝒲.pullback c' A) (pullback.snd c' (specMap R A)))
    (fε : HomOver (RingHom.id (DualNumber A))
      (𝒱.pullback c (DualNumber A)) (pullback.snd c (specMap R (DualNumber A)))
      (𝒲.pullback c' (DualNumber A)) (pullback.snd c' (specMap R (DualNumber A))))

    (hsq : IsPullback fε.hom (dualNumberThickening A 𝒲 c').hom (dualNumberThickening A 𝒱 c).hom f.hom)

    (hW0 : (𝒲.pullback c' A).U0 = f.hom ⁻¹ᵁ (𝒱.pullback c A).U0)
    (hW1 : (𝒲.pullback c' A).U1 = f.hom ⁻¹ᵁ (𝒱.pullback c A).U1)
    (hW0ε : (𝒲.pullback c' (DualNumber A)).U0 = fε.hom ⁻¹ᵁ (𝒱.pullback c (DualNumber A)).U0)
    (hW1ε : (𝒲.pullback c' (DualNumber A)).U1 = fε.hom ⁻¹ᵁ (𝒱.pullback c (DualNumber A)).U1)

    [IsFinite fε.hom] [Flat fε.hom] [LocallyOfFinitePresentation fε.hom]
    (d : ℕ) (hd : ∀ x, fε.hom.finrank x = d)

    (e₀ : Fin d → Γ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _), (𝒱.pullback c (DualNumber A)).U0))
    (he₀ : ∀ (W : (Limits.pullback c (specMap R (DualNumber A))).Opens) (hW : W ≤ (𝒱.pullback c (DualNumber A)).U0),
      ∃ b : Module.Basis (Fin d) Γ(Limits.pullback c (specMap R (DualNumber A)), W)
          Γ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _), W),
        ∀ i, b i = ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _)).presheaf.map (homOfLE hW).op (e₀ i))
    (e₁ : Fin d → Γ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _), (𝒱.pullback c (DualNumber A)).U1))
    (he₁ : ∀ (W : (Limits.pullback c (specMap R (DualNumber A))).Opens) (hW : W ≤ (𝒱.pullback c (DualNumber A)).U1),
      ∃ b : Module.Basis (Fin d) Γ(Limits.pullback c (specMap R (DualNumber A)), W)
          Γ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _), W),
        ∀ i, b i = ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _)).presheaf.map (homOfLE hW).op (e₁ i))

    (L : (Limits.pullback c' (specMap R (DualNumber A))).Modules)
    (s₀ : Γ(L, (𝒲.pullback c' (DualNumber A)).U0)) (s₁ : Γ(L, (𝒲.pullback c' (DualNumber A)).U1))
    (hs₀ : Scheme.Modules.IsFrameOn s₀ (𝒲.pullback c' (DualNumber A)).U0)
    (hs₁ : Scheme.Modules.IsFrameOn s₁ (𝒲.pullback c' (DualNumber A)).U1)
    (g : ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01)
    (hs : L.presheaf.map (homOfLE inf_le_right).op s₁ =
      (show Γ(Limits.pullback c' (specMap R (DualNumber A)),
          (𝒲.pullback c' (DualNumber A)).U0 ⊓ (𝒲.pullback c' (DualNumber A)).U1)
        from oneAddEpsMul A 𝒲 c' g) • L.presheaf.map (homOfLE inf_le_left).op s₀) :
    letI : Algebra ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01
        ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01 :=
      (f.hom.appLE ((𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1) ((𝒲.pullback c' A).U0 ⊓ (𝒲.pullback c' A).U1)
        f.inf_le).hom.toAlgebra

    ∀ [Module.Free ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01
        ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01]
      [Module.Finite ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01
        ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01],
    ∃ (Ω₀ : Γ(Scheme.Modules.normModule fε.hom d L, (𝒱.pullback c (DualNumber A)).U0))
      (Ω₁ : Γ(Scheme.Modules.normModule fε.hom d L, (𝒱.pullback c (DualNumber A)).U1)),
      Scheme.Modules.IsFrameOn Ω₀ (𝒱.pullback c (DualNumber A)).U0 ∧
      Scheme.Modules.IsFrameOn Ω₁ (𝒱.pullback c (DualNumber A)).U1 ∧
      (Scheme.Modules.normModule fε.hom d L).presheaf.map (homOfLE inf_le_right).op Ω₁ =
        (show Γ(Limits.pullback c (specMap R (DualNumber A)),
            (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1)
          from oneAddEpsMul A 𝒱 c
            (Algebra.trace ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01
              ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01 g)) •
        (Scheme.Modules.normModule fε.hom d L).presheaf.map (homOfLE inf_le_left).op Ω₀ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul.solution
