import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SymmRootFunctor
import Definitions.Def_AlgebraicGeometry_SymmRootAdm
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_equiv_symmRoot_adm_classFunctor_natural
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback
attribute [-simp] AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.SymmRoot

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_equiv_symmRoot_adm_classFunctor_natural
    {R₀ : Type} [CommRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R₀ f) (hA : AbelianSchemePropertyBundle R₀ f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (hadm : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (W : Type) [CommRing W] [Algebra R₀ W]
    (M₀ : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))))
    (h₀ : symmRootPred L 𝓛 R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) M₀.L) :
    ∃ e : ∀ (B' : Under (CommRingCat.of R₀)) (b : (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) ⟶ B'), (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).obj B' ≃ (classFunctor f (L.one (𝟙 _)) R₀ (admStablePred L R₀ hadm)).obj B',
      ∀ (B' B'' : Under (CommRingCat.of R₀)) (b : (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) ⟶ B') (ψ : B' ⟶ B'') (x : (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).obj B'),
        e B'' (b ≫ ψ) ((classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).map ψ x) = (classFunctor f (L.one (𝟙 _)) R₀ (admStablePred L R₀ hadm)).map ψ (e B' b x) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_equiv_symmRoot_adm_classFunctor_natural.solution
