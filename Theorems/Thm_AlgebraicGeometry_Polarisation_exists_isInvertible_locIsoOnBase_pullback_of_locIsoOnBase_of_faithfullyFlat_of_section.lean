import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_exists_isInvertible_locIsoOnBase_pullback_of_locIsoOnBase_of_faithfullyFlat_of_section
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Polarisation
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.Polarisation.exists_isInvertible_locIsoOnBase_pullback_of_locIsoOnBase_of_faithfullyFlat_of_section
    {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R']
    {A A' A'' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [IsSeparated f]
    (hH0 : ∀ (T : Type u) [CommRing T] [Algebra R T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd f (Scheme.TwoAffineOpenCover.specMap R T)) ⊤
      Function.Bijective (algebraMap T Γ(pullback f (Scheme.TwoAffineOpenCover.specMap R T), ⊤)))
    (e : Spec (CommRingCat.of R) ⟶ A) (he : e ≫ f = 𝟙 _)
    (f' : A' ⟶ Spec (CommRingCat.of R')) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (f'' : A'' ⟶ Spec (CommRingCat.of (R' ⊗[R] R'))) (a₁ a₂ : A'' ⟶ A')
    (ha₁ : IsPullback a₁ f'' f'
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : R' →ₐ[R] R' ⊗[R] R').toRingHom)))
    (ha₂ : IsPullback a₂ f'' f'
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : R' →ₐ[R] R' ⊗[R] R').toRingHom)))
    (hga : a₁ ≫ g = a₂ ≫ g)
    (𝓛' : A'.Modules) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (hdd : LocIsoOnBase f'' ((Scheme.Modules.pullback a₁).obj 𝓛') ((Scheme.Modules.pullback a₂).obj 𝓛')) :
    ∃ 𝓛 : A.Modules, Scheme.Modules.IsInvertible 𝓛 ∧ LocIsoOnBase f' ((Scheme.Modules.pullback g).obj 𝓛) 𝓛' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_exists_isInvertible_locIsoOnBase_pullback_of_locIsoOnBase_of_faithfullyFlat_of_section.solution
