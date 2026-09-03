import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_SheafOfModules_Monoidal
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_tensor_of_pullback_baseChangeSnd_iso_of_tensor_iso_unit
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.isAlgEquivZero_tensor_of_pullback_baseChangeSnd_iso_of_tensor_iso_unit
    {k : Type u} [Field k] {K : Type u} [Field K] (κ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    {X V : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (hV : V ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType hV] [GeometricallyIntegral hV]
    (F : (pullback x (hV ≫ κ)).Modules) (hF : Scheme.Modules.IsInvertible F)
    (v₀ v₁ : Spec (CommRingCat.of K) ⟶ V) (hv₀ : v₀ ≫ hV = 𝟙 _) (hv₁ : v₁ ≫ hV = 𝟙 _)
    (A B P : (pullback x κ).Modules)
    (eA : (Scheme.Modules.pullback (baseChangeSnd x
      (⟨v₀, by rw [← Category.assoc, hv₀, Category.id_comp]⟩ : SchemeHomOver κ (hV ≫ κ)))).obj F ≅ A)
    (eB : (Scheme.Modules.pullback (baseChangeSnd x
      (⟨v₁, by rw [← Category.assoc, hv₁, Category.id_comp]⟩ : SchemeHomOver κ (hV ≫ κ)))).obj F ≅ B)
    (hP : Scheme.Modules.IsInvertible P) (eP : A ⊗ P ≅ 𝟙_ (pullback x κ).Modules) :
    IsAlgEquivZero (pullback.snd x κ) (B ⊗ P) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_tensor_of_pullback_baseChangeSnd_iso_of_tensor_iso_unit.solution
