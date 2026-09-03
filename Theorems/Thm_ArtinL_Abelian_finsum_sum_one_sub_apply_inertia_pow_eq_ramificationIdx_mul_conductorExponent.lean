import Mathlib
import Definitions.Def_ArtinL_Abelian
import P2M.Util
import P2M.Sol.S_ArtinL_Abelian_finsum_sum_one_sub_apply_inertia_pow_eq_ramificationIdx_mul_conductorExponent
attribute [-instance] ValuationSubring.lowerRamificationGroup_normal IsLocalRing.lowerRamificationGroup_normal FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype
attribute [-simp] IsLocalRing.upperRamificationGroup_zero IsLocalRing.upperRamificationIndex_zero IsLocalRing.herbrandPhi_zero ValuationSubring.herbrandPhi_zero IsLocalRing.mem_upperRamificationGroup Ideal.inertia_top ValuationSubring.mem_lowerRamificationGroup IsLocalRing.pointwise_smul_maximalIdeal IsLocalRing.pointwise_smul_maximalIdeal_pow IsLocalRing.mem_lowerRamificationGroup IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf

set_option autoImplicit false

open NumberField
open scoped Classical in

theorem ArtinL.Abelian.finsum_sum_one_sub_apply_inertia_pow_eq_ramificationIdx_mul_conductorExponent
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (ψ : (L ≃ₐ[K] L) →* ℂˣ) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    (hQ : Q.under (𝓞 K) = w.asIdeal) :
    ∑ᶠ j : ℕ, ∑ t : ↥((Q ^ (j + 1)).inertia (L ≃ₐ[K] L)), (1 - ((ψ (t : L ≃ₐ[K] L) : ℂˣ) : ℂ)) =
      ((w.asIdeal.ramificationIdx' Q * ArtinL.Abelian.conductorExponent ψ w : ℕ) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_Abelian_finsum_sum_one_sub_apply_inertia_pow_eq_ramificationIdx_mul_conductorExponent.solution
