import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.FieldTheory.Finite.GaloisField
import P2M.Util
import P2M.Sol.S_ValuationSubring_tameCharacter_eq_one_iff_apply_eq_and_conj_mem_and_exists_apply_eq_of_pow_sq_sub_one_eq

set_option autoImplicit false

theorem
ValuationSubring.tameCharacter_eq_one_iff_apply_eq_and_conj_mem_and_exists_apply_eq_of_pow_sq_sub_one_eq
    (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) :
    (∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.tameCharacter π τ = 1 ↔ τ π = π) ∧
    (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 →
      σ * τ * σ⁻¹ ∈ P.inertiaSubgroupIn ℚ ∧ P.tameCharacter π (σ * τ * σ⁻¹) = 1) ∧
    (∀ ι : GaloisField q 2 →+* IsLocalRing.ResidueField P,
      ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∃ α : GaloisField q 2, ι α = P.tameCharacter π τ) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_tameCharacter_eq_one_iff_apply_eq_and_conj_mem_and_exists_apply_eq_of_pow_sq_sub_one_eq.solution
