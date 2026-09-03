import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_nonempty_iso_tensor_pullback_negMor_pullback_of_comp_eq
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_iso_tensor_pullback_negMor_pullback_of_comp_eq
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {T₁ T₂ : Type} [CommRing T₁] [CommRing T₂] (s₁ : S →+* T₁) (s₂ : S →+* T₂) (τ : T₁ →+* T₂)
    (hτ : τ.comp s₁ = s₂)
    (ρ : pullback f (Spec.map (CommRingCat.ofHom s₂)) ⟶ pullback f (Spec.map (CommRingCat.ofHom s₁)))
    (hρ₁ : ρ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom s₁)) = pullback.fst f (Spec.map (CommRingCat.ofHom s₂)))
    (hρ₂ : ρ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom s₁)) =
      pullback.snd f (Spec.map (CommRingCat.ofHom s₂)) ≫ Spec.map (CommRingCat.ofHom τ))
    (𝓛 : A.Modules) (𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom s₁))).Modules)
    (e : Nonempty ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom s₁)))).obj 𝓛 ≅
      𝓛₀ ⊗ (Scheme.Modules.pullback
        (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom s₁))) (L.baseChange (Spec.map (CommRingCat.ofHom s₁))))).obj 𝓛₀)) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom s₂)))).obj 𝓛 ≅
      (Scheme.Modules.pullback ρ).obj 𝓛₀ ⊗ (Scheme.Modules.pullback
        (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom s₂))) (L.baseChange (Spec.map (CommRingCat.ofHom s₂))))).obj
          ((Scheme.Modules.pullback ρ).obj 𝓛₀)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_nonempty_iso_tensor_pullback_negMor_pullback_of_comp_eq.solution
