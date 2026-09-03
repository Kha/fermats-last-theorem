import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import P2M.Util
import P2M.Sol.S_GaloisRep_exists_inertia_eigenvector_tameCharacter_pow_map_of_forall_eq_pow

set_option autoImplicit false
theorem GaloisRep.exists_inertia_eigenvector_tameCharacter_pow_map_of_forall_eq_pow
    (p : ℕ) [Fact p.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (p ^ 2 - 1) = (p : AlgebraicClosure ℚ))
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      GL (Fin 2) (IsLocalRing.ResidueField P))
    (φ : IsLocalRing.ResidueField P →+* IsLocalRing.ResidueField P) (j : ℕ)
    (hφ : ∀ x, φ x = x ^ p ^ j) (kn : ℕ)
    (h : ∃ v : Fin 2 → IsLocalRing.ResidueField P, v ≠ 0 ∧
      ((∀ σ ∈ P.inertiaSubgroupIn ℚ,
          (ρ σ).val.mulVec v = P.tameCharacter π σ ^ (kn - 1) • v) ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          (ρ σ).val.mulVec v = (P.tameCharacter π σ ^ p) ^ (kn - 1) • v))) :
    ∃ v : Fin 2 → IsLocalRing.ResidueField P, v ≠ 0 ∧
      ((∀ σ ∈ P.inertiaSubgroupIn ℚ,
          ((ρ σ).val.map φ).mulVec v = P.tameCharacter π σ ^ (kn - 1) • v) ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          ((ρ σ).val.map φ).mulVec v = (P.tameCharacter π σ ^ p) ^ (kn - 1) • v)) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_exists_inertia_eigenvector_tameCharacter_pow_map_of_forall_eq_pow.solution
