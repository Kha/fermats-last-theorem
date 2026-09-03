import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

theorem AdicCompletion.isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal
    {C : Type*} [CommRing C] [IsNoetherianRing C] (𝔫 : Ideal C) [𝔫.IsMaximal] :
    IsNoetherianRing (AdicCompletion 𝔫 C) ∧
    ∃ _ : IsLocalRing (AdicCompletion 𝔫 C),
      IsLocalRing.maximalIdeal (AdicCompletion 𝔫 C) = 𝔫.map (algebraMap C (AdicCompletion 𝔫 C)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (AdicCompletion 𝔫 C)) (AdicCompletion 𝔫 C) ∧
      (IsLocalRing.maximalIdeal (AdicCompletion 𝔫 C)).comap (algebraMap C (AdicCompletion 𝔫 C)) = 𝔫 ∧
      Function.Surjective ((IsLocalRing.residue (AdicCompletion 𝔫 C)).comp (algebraMap C (AdicCompletion 𝔫 C))) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal.solution
