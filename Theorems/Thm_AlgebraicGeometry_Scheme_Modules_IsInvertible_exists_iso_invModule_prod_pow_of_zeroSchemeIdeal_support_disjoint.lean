import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_invModule_prod_pow_of_zeroSchemeIdeal_support_disjoint
attribute [-instance] SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback
attribute [-simp] PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_iso_invModule_prod_pow_of_zeroSchemeIdeal_support_disjoint
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    {ι : Type u} [Fintype ι] (C : ι → X.IdealSheafData) (hC : ∀ i, (C i).IsInvertible)
    (hCU : ∀ i (x : X), x ∈ (C i).support → x ∉ U)
    (η : ι → X) (hηU : ∀ i, η i ∉ U)
    (hη : ∀ i, ∃ (V : X.affineOpens) (hV : η i ∈ (V : X.Opens)),
      Ideal.map (X.presheaf.germ (V : X.Opens) (η i) hV).hom ((C i).ideal V) =
          IsLocalRing.maximalIdeal (X.presheaf.stalk (η i)) ∧
        ∀ j, j ≠ i → Ideal.map (X.presheaf.germ (V : X.Opens) (η i) hV).hom ((C j).ideal V) = ⊤)
    (hcodim : ∀ x : X, x ∉ U → ringKrullDim (X.presheaf.stalk x) ≤ 1 → ∃ i, x = η i)
    (hprin : ∀ x : X, x ∉ U → ∀ P : Ideal (X.presheaf.stalk x), P.IsPrime → P.height = 1 →
      Submodule.IsPrincipal P)
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) (s : 𝟙_ X.Modules ⟶ L)
    (hs : ∀ x : X, x ∈ (Scheme.Modules.zeroSchemeIdeal s).support → x ∉ U) :
    ∃ n : ι → ℕ, Nonempty (L ≅ (∏ i, C i ^ n i).invModule) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_invModule_prod_pow_of_zeroSchemeIdeal_support_disjoint.solution
