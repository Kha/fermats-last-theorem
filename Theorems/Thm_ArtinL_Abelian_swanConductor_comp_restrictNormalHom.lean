import Mathlib
import Definitions.Def_ArtinL_Abelian
import P2M.Util
import P2M.Sol.S_ArtinL_Abelian_swanConductor_comp_restrictNormalHom
attribute [-instance] ValuationSubring.lowerRamificationGroup_normal IsLocalRing.lowerRamificationGroup_normal FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype
attribute [-simp] Ideal.inertia_top ValuationSubring.mem_lowerRamificationGroup IsLocalRing.pointwise_smul_maximalIdeal IsLocalRing.pointwise_smul_maximalIdeal_pow IsLocalRing.mem_lowerRamificationGroup IsLocalRing.upperRamificationGroup_zero IsLocalRing.upperRamificationIndex_zero IsLocalRing.herbrandPhi_zero ValuationSubring.herbrandPhi_zero IsLocalRing.mem_upperRamificationGroup IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf

set_option autoImplicit false

open NumberField NumberField.InfinitePlace IsDedekindDomain

universe u v w

theorem ArtinL.Abelian.swanConductor_comp_restrictNormalHom
    (K : Type u) (L : Type v) (M : Type w) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (ψ : (L ≃ₐ[K] L) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ArtinL.Abelian.swanConductor (ψ.comp (AlgEquiv.restrictNormalHom (K₁ := M) L)) v =
      ArtinL.Abelian.swanConductor ψ v := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_Abelian_swanConductor_comp_restrictNormalHom.solution
