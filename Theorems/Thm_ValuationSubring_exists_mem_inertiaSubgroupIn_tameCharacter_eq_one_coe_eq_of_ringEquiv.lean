import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_coe_eq_of_ringEquiv

set_option autoImplicit false

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_coe_eq_of_ringEquiv
    (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ) (hπ0 : π ≠ 0)
    (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)
    (hσP : ∀ a : AlgebraicClosure ℚ, a ∈ P ↔ σ a ∈ P) (hσπ : σ π = π)
    (hσres : ∀ (a : P) (h : σ (a : AlgebraicClosure ℚ) ∈ P),
      IsLocalRing.residue P ⟨σ (a : AlgebraicClosure ℚ), h⟩ = IsLocalRing.residue P a) :
    ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ∈ P.inertiaSubgroupIn ℚ ∧ P.tameCharacter π τ = 1 ∧
      ∀ a, τ a = σ a := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_coe_eq_of_ringEquiv.solution
