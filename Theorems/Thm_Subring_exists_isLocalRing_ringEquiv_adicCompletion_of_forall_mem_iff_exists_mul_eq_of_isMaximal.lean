import Mathlib
import P2M.Util
import P2M.Sol.S_Subring_exists_isLocalRing_ringEquiv_adicCompletion_of_forall_mem_iff_exists_mul_eq_of_isMaximal

set_option autoImplicit false

open IsLocalRing

theorem Subring.exists_isLocalRing_ringEquiv_adicCompletion_of_forall_mem_iff_exists_mul_eq_of_isMaximal
    (K : Type) [Field K] (B : Subring K) (P : Ideal ↥B) (hP : P.IsMaximal)
    (O : Subring K)
    (hO : ∀ f : K, f ∈ O ↔ ∃ g h : ↥B, h ∉ P ∧ f * (h : K) = (g : K)) :
    ∃ (hBO : ∀ b : ↥B, (b : K) ∈ O) (_ : IsLocalRing ↥O),
      (∀ b : ↥B, (⟨(b : K), hBO b⟩ : ↥O) ∈ maximalIdeal ↥O ↔ b ∈ P) ∧
      (IsNoetherianRing ↥B → IsNoetherianRing ↥O) ∧
      (∀ (f : K) (hf : f ∈ O), ∃ (g h : ↥B), h ∉ P ∧ (⟨f, hf⟩ : ↥O) * ⟨(h : K), hBO h⟩ = ⟨(g : K), hBO g⟩) ∧
      ∃ T : AdicCompletion P ↥B ≃+* AdicCompletion (maximalIdeal ↥O) ↥O,
        ∀ b : ↥B, T (algebraMap ↥B (AdicCompletion P ↥B) b) =
          algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨(b : K), hBO b⟩ := by p2m_exact_reverting @_root_.P2MW.S_Subring_exists_isLocalRing_ringEquiv_adicCompletion_of_forall_mem_iff_exists_mul_eq_of_isMaximal.solution
