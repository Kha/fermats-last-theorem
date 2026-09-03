import Mathlib
import Definitions.Def_ArtinL_Abelian
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import P2M.Util
import P2M.Sol.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le

set_option autoImplicit false

open NumberField IsDedekindDomain

universe u v

theorem ArtinL.Abelian.forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le
    (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : ArtinL.Abelian.conductorExponent ψ v ≤ n) :
    ∀ σ ∈ ValuationSubring.upperRamificationGroup K (((⟨LanglandsTunnell.P2.Artin.primeAbove K M v, inferInstance, LanglandsTunnell.P2.Artin.primeAbove_ne_bot K M v⟩ :
          HeightOneSpectrum (𝓞 M)).valuation M).valuationSubring) (n : ℚ),
      ψ ((σ : ↥((((⟨LanglandsTunnell.P2.Artin.primeAbove K M v, inferInstance, LanglandsTunnell.P2.Artin.primeAbove_ne_bot K M v⟩ :
          HeightOneSpectrum (𝓞 M)).valuation M).valuationSubring).decompositionSubgroup K)) : M ≃ₐ[K] M) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.solution
