import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_tensorProduct_sections_linearEquiv_sections_box_natural_of_isInvertible
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.exists_tensorProduct_sections_linearEquiv_sections_box_natural_of_isInvertible
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated πX] [IsSeparated πY]
    (F : X.Modules) (hF : Scheme.Modules.IsInvertible F)
    (G : Y.Modules) (hG : Scheme.Modules.IsInvertible G) :
    ∃ e : ∀ (U : X.affineOpens) (V : Y.affineOpens),
        (OModulePresheaf.ofModules πX F).obj U.1 ⊗[k] (OModulePresheaf.ofModules πY G).obj V.1 ≃ₗ[k]
          (OModulePresheaf.ofModules (pullback.fst πX πY ≫ πX)
            ((Scheme.Modules.pullback (pullback.fst πX πY)).obj F ⊗
              (Scheme.Modules.pullback (pullback.snd πX πY)).obj G)).obj
            (pullback.fst πX πY ⁻¹ᵁ U.1 ⊓ pullback.snd πX πY ⁻¹ᵁ V.1),
      ∀ (U U' : X.affineOpens) (V V' : Y.affineOpens) (hU : U'.1 ≤ U.1) (hV : V'.1 ≤ V.1)
        (s : (OModulePresheaf.ofModules πX F).obj U.1) (t : (OModulePresheaf.ofModules πY G).obj V.1),
        (OModulePresheaf.ofModules (pullback.fst πX πY ≫ πX)
            ((Scheme.Modules.pullback (pullback.fst πX πY)).obj F ⊗
              (Scheme.Modules.pullback (pullback.snd πX πY)).obj G)).res
          (inf_le_inf ((pullback.fst πX πY).preimage_mono hU) ((pullback.snd πX πY).preimage_mono hV))
          (e U V (s ⊗ₜ t)) =
        e U' V' ((OModulePresheaf.ofModules πX F).res hU s ⊗ₜ (OModulePresheaf.ofModules πY G).res hV t) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_tensorProduct_sections_linearEquiv_sections_box_natural_of_isInvertible.solution
