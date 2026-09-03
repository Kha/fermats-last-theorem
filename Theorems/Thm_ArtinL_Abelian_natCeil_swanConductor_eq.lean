import Mathlib
import Definitions.Def_ArtinL_Abelian
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import P2M.Util
import P2M.Sol.S_ArtinL_Abelian_natCeil_swanConductor_eq
attribute [-instance] FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype
attribute [-simp] IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf

set_option autoImplicit false

open NumberField IsDedekindDomain

universe u v

theorem ArtinL.Abelian.natCeil_swanConductor_eq
    (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (hram : ¬ ArtinL.Abelian.IsUnramifiedAt ψ v) :
    (⌈ArtinL.Abelian.swanConductor ψ v⌉₊ : ℚ) = ArtinL.Abelian.swanConductor ψ v := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_Abelian_natCeil_swanConductor_eq.solution
