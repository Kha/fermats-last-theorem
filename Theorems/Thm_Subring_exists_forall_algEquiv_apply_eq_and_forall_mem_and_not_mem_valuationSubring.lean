import Mathlib
import P2M.Util
import P2M.Sol.S_Subring_exists_forall_algEquiv_apply_eq_and_forall_mem_and_not_mem_valuationSubring

set_option autoImplicit false

open IsLocalRing

theorem Subring.exists_forall_algEquiv_apply_eq_and_forall_mem_and_not_mem_valuationSubring
    {k K : Type} [Field k] [Field K] [Algebra k K]
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (B : Subring K) (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B)
    (V : ValuationSubring K) (hBV : ∀ f : K, f ∈ B → f ∈ V)
    (hp : ∃ (b : K) (hb : b ∈ B), b ≠ 0 ∧ (⟨b, hBV b hb⟩ : ↥V) ∈ maximalIdeal ↥V)
    (E : Finset (Subring K)) (hEloc : ∀ O ∈ E, IsLocalRing ↥O) (hBE : ∀ O ∈ E, ∀ f : K, f ∈ B → f ∈ O)
    (hEG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ O ∈ E, ∃ O' ∈ E, ∀ f : K, f ∈ O' ↔ σ f ∈ O)
    (hsep : ∀ (O : Subring K) (hO : O ∈ E), ∃ (b : K) (hb : b ∈ B),
      (⟨b, hBV b hb⟩ : ↥V) ∈ maximalIdeal ↥V ∧ IsUnit (⟨b, hBE O hO b hb⟩ : ↥O)) :
    ∃ f : K, (∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f) ∧ (∀ O ∈ E, f ∈ O) ∧ f ∉ V := by p2m_exact_reverting @_root_.P2MW.S_Subring_exists_forall_algEquiv_apply_eq_and_forall_mem_and_not_mem_valuationSubring.solution
