import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_mem_iff_exists_not_dvd_of_prime_of_forall_mem_maximalIdeal_iff_dvd

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.mem_iff_exists_not_dvd_of_prime_of_forall_mem_maximalIdeal_iff_dvd
    {K : Type*} [Field K] (S : Subring K) [IsNoetherianRing ↥S] (ϖ : ↥S) (hϖ : Prime ϖ)
    (O : ValuationSubring K) (hSO : ∀ s : ↥S, (s : K) ∈ O)
    (hcen : ∀ s : ↥S, (⟨(s : K), hSO s⟩ : ↥O) ∈ maximalIdeal ↥O ↔ ϖ ∣ s) :
    ∀ f : K, (∃ g h : ↥S, (h : K) ≠ 0 ∧ f * (h : K) = (g : K)) →
      (f ∈ O ↔ ∃ g h : ↥S, ¬ (ϖ ∣ h) ∧ f * (h : K) = (g : K)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_mem_iff_exists_not_dvd_of_prime_of_forall_mem_maximalIdeal_iff_dvd.solution
