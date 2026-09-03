import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_pow_maximalIdeal_smul_top_baseChange_eq_bot_of_isFiniteLength_of_isPrime

set_option autoImplicit false

universe u v w

open TensorProduct

theorem Module.exists_pow_maximalIdeal_smul_top_baseChange_eq_bot_of_isFiniteLength_of_isPrime
    (S : Type u) [CommRing S] (H : Type v) [AddCommGroup H] [Module S H] (hH : IsFiniteLength S H)
    (𝔭 : Ideal S) [𝔭.IsPrime]
    (B : Type w) [CommRing B] [Algebra S B] [IsLocalization.AtPrime B 𝔭] [IsLocalRing B] :
    ∃ n : ℕ, IsLocalRing.maximalIdeal B ^ n • (⊤ : Submodule B (B ⊗[S] H)) = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_pow_maximalIdeal_smul_top_baseChange_eq_bot_of_isFiniteLength_of_isPrime.solution
