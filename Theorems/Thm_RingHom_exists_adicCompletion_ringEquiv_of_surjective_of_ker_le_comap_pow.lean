import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_exists_adicCompletion_ringEquiv_of_surjective_of_ker_le_comap_pow

set_option autoImplicit false
universe u

theorem RingHom.exists_adicCompletion_ringEquiv_of_surjective_of_ker_le_comap_pow
    {B C : Type u} [CommRing B] [CommRing C] (θ : B →+* C) (hθ : Function.Surjective θ)
    (𝔪 : Ideal C) (hker : ∀ n : ℕ, RingHom.ker θ ≤ (Ideal.comap θ 𝔪) ^ n) :
    ∃ e : AdicCompletion (Ideal.comap θ 𝔪) B ≃+* AdicCompletion 𝔪 C,
      ∀ b : B, e (algebraMap B (AdicCompletion (Ideal.comap θ 𝔪) B) b) = algebraMap C (AdicCompletion 𝔪 C) (θ b) := by p2m_exact_reverting @_root_.P2MW.S_RingHom_exists_adicCompletion_ringEquiv_of_surjective_of_ker_le_comap_pow.solution
