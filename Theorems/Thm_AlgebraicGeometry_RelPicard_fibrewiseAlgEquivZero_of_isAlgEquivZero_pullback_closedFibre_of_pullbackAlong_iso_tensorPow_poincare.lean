import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_fibrewiseAlgEquivZero_of_isAlgEquivZero_pullback_closedFibre_of_pullbackAlong_iso_tensorPow_poincare
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'
attribute [-simp] AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.fibrewiseAlgEquivZero_of_isAlgEquivZero_pullback_closedFibre_of_pullbackAlong_iso_tensorPow_poincare
    {A : Type u} [CommRing A] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of A))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) c)
    (D : RelativePic0Designation A c) (hrep : Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D))
    (k : Type u) [Field k] [Algebra A k]
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : A →+* O)
    (toκ : O →+* k) (htoκ : toκ.comp ρO = algebraMap A k) (htoκs : Function.Surjective toκ)
    (bc : pullback c (specMap A k) ⟶ pullback c (Spec.map (CommRingCat.ofHom ρO)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ))
    (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']
    (y : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap O T').comp ρO))) D.toBase) (n : ℕ)
    (M : RigidifiedLineBundle c ε (Spec.map (CommRingCat.ofHom ρO)))
    (hclosed : IsAlgEquivZero (pullback.snd c (specMap A k)) ((Scheme.Modules.pullback bc).obj M.L))
    (hgen : Nonempty ((M.pullbackAlong
        (⟨Spec.map (CommRingCat.ofHom (algebraMap O T')), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap O T').comp ρO))) (Spec.map (CommRingCat.ofHom ρO)))).L ≅
      (hrep.some.poincare.pullbackAlong y).L.tensorPow n)) :
    FibrewiseAlgEquivZero M := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_fibrewiseAlgEquivZero_of_isAlgEquivZero_pullback_closedFibre_of_pullbackAlong_iso_tensorPow_poincare.solution
