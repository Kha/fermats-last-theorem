import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_baseChangeSnd_comp_restrictHom_eq_of_baseChangeSnd_comp
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.baseChangeSnd_comp_restrictHom_eq_of_baseChangeSnd_comp
    {R : Type u} [CommRing R] (κ : Type u) [CommRing κ] [Algebra R κ]
    {𝔛 𝔛₀ : Scheme.{u}} {x : 𝔛 ⟶ Spec (CommRingCat.of R)} {x₀ : 𝔛₀ ⟶ Spec (CommRingCat.of R)}
    {εR : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) x} {ε₀R : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) x₀}
    {D_R : RelativePic0Designation R x} {D₀ : RelativePic0Designation R x₀}
    (hD_R : RepresentsRelSubPic x εR (algEquivZeroCut x εR) D_R)
    (hD₀ : RepresentsRelSubPic x₀ ε₀R (algEquivZeroCut x₀ ε₀R) D₀)
    (hD : RepresentsRelSubPic (baseChange R x κ) (sectionBaseChange κ εR)
      (algEquivZeroCut (baseChange R x κ) (sectionBaseChange κ εR)) (D_R.baseChange κ))
    (hPD : Nonempty (hD.poincare.L ≅ (BaseChange.ofR x εR κ
      (hD_R.poincare.pullbackAlong ⟨pullback.fst D_R.toBase (specMap R κ), pullback.condition⟩)).L))
    (hD' : RepresentsRelSubPic (baseChange R x₀ κ) (sectionBaseChange κ ε₀R)
      (algEquivZeroCut (baseChange R x₀ κ) (sectionBaseChange κ ε₀R)) (D₀.baseChange κ))
    (hPD' : Nonempty (hD'.poincare.L ≅ (BaseChange.ofR x₀ ε₀R κ
      (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap R κ), pullback.condition⟩)).L))
    (f : pullback x₀ (specMap R κ) ⟶ pullback x (specMap R κ)) (hf : f ≫ baseChange R x κ = baseChange R x₀ κ)
    (τ : SchemeHomOver (specMap R κ) (specMap R κ))
    (hcomm : baseChangeSnd x₀ τ ≫ f = f ≫ baseChangeSnd x τ) :
    (∀ hε : (sectionBaseChange κ ε₀R).1 ≫ f = (sectionBaseChange κ εR).1,
      baseChangeSnd D_R.toBase τ ≫ (RepresentsRelSubPic.pullbackHom f hf hε hD hD').1 =
        (RepresentsRelSubPic.pullbackHom f hf hε hD hD').1 ≫ baseChangeSnd D₀.toBase τ) ∧
    (∀ ν : SchemeHomOver (D_R.baseChange κ).toBase (D₀.baseChange κ).toBase,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t (D_R.baseChange κ).toBase),
        Nonempty ((hD'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν)).L ≅
          Scheme.Modules.rigidify (rigSection (baseChange R x₀ κ) t (sectionBaseChange κ ε₀R))
            (pullback.snd (baseChange R x₀ κ) t)
            ((Scheme.Modules.pullback (curveChange f hf t)).obj (hD.poincare.pullbackAlong a).L))) →
      baseChangeSnd D_R.toBase τ ≫ ν.1 = ν.1 ≫ baseChangeSnd D₀.toBase τ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_baseChangeSnd_comp_restrictHom_eq_of_baseChangeSnd_comp.solution
