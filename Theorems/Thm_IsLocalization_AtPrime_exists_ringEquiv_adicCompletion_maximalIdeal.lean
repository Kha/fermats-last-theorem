import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalization_AtPrime_exists_ringEquiv_adicCompletion_maximalIdeal

set_option autoImplicit false

universe u v

theorem IsLocalization.AtPrime.exists_ringEquiv_adicCompletion_maximalIdeal
    {B : Type u} [CommRing B] (𝔪 : Ideal B) [𝔪.IsMaximal]
    (O : Type v) [CommRing O] [IsLocalRing O] [Algebra B O] [IsLocalization.AtPrime O 𝔪] :
    ∃ ê : AdicCompletion 𝔪 B ≃+* AdicCompletion (IsLocalRing.maximalIdeal O) O,
      ∀ b : B, ê (algebraMap B (AdicCompletion 𝔪 B) b) =
        algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O) (algebraMap B O b) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalization_AtPrime_exists_ringEquiv_adicCompletion_maximalIdeal.solution
