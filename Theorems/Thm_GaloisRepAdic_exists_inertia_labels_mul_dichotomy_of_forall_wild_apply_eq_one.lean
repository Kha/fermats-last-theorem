import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_inertia_labels_mul_dichotomy_of_forall_wild_apply_eq_one

set_option autoImplicit false

open Polynomial

theorem GaloisRepAdic.exists_inertia_labels_mul_dichotomy_of_forall_wild_apply_eq_one
    {O' : Type} [CommRing O'] [IsLocalRing O'] (ρ : GaloisRepAdic O')
    {q : ℕ} [Fact q.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (htame : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ P.inertiaSubgroupIn ℚ →
        (∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) → ρ.ρ σ = 1)
    {O'' : Type} [CommRing O''] [IsDomain O''] (j : O' →+* O'')
    (hsplit : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∃ α β : O'',
      (LinearMap.charpoly (ρ.ρ σ)).map j = (X - C α) * (X - C β)) :
    ∃ a b : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → O''ˣ,
      (∀ σ ∈ P.inertiaSubgroupIn ℚ,
        (LinearMap.charpoly (ρ.ρ σ)).map j = (X - C ((a σ : O''ˣ) : O'')) * (X - C ((b σ : O''ˣ) : O''))) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ,
        a (σ * τ) = a σ * a τ ∧ b (σ * τ) = b σ * b τ) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, a σ ^ (q ^ 2 - 1) = 1 ∧ b σ ^ (q ^ 2 - 1) = 1) ∧
      ((∀ σ ∈ P.inertiaSubgroupIn ℚ, a σ ^ (q - 1) = 1 ∧ b σ ^ (q - 1) = 1) ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, b σ = a σ ^ q ∧ a σ = b σ ^ q)) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ,
        (∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) → a σ = 1 ∧ b σ = 1) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_inertia_labels_mul_dichotomy_of_forall_wild_apply_eq_one.solution
