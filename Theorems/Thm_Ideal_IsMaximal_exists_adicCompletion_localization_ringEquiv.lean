import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_IsMaximal_exists_adicCompletion_localization_ringEquiv

set_option autoImplicit false
universe u

theorem Ideal.IsMaximal.exists_adicCompletion_localization_ringEquiv
    {C : Type u} [CommRing C] (𝔪 : Ideal C) [𝔪.IsMaximal] :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)) (Localization.AtPrime 𝔪) ≃+*
        AdicCompletion 𝔪 C,
      ∀ c : C, e (algebraMap (Localization.AtPrime 𝔪) _ (algebraMap C (Localization.AtPrime 𝔪) c)) =
        algebraMap C (AdicCompletion 𝔪 C) c := by p2m_exact_reverting @_root_.P2MW.S_Ideal_IsMaximal_exists_adicCompletion_localization_ringEquiv.solution
