import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_monoidHom_decompositionSubgroup_zmod_two_eq_one_of_mem_inertiaSubgroupIn_ne_one_of_isFrobeniusAt

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_monoidHom_decompositionSubgroup_zmod_two_eq_one_of_mem_inertiaSubgroupIn_ne_one_of_isFrobeniusAt
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∃ χ : ↥(A.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2),
      (∀ τ : ↥(A.decompositionSubgroup ℚ),
          (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ → χ τ = 1) ∧
      (∀ φ : ↥(A.decompositionSubgroup ℚ),
          A.IsFrobeniusAt (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) r → χ φ ≠ 1) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ),
          χ σ = 1 ↔ ∀ x : ResidueField ↥A, x ^ (r ^ 2) = x → σ • x = x) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_monoidHom_decompositionSubgroup_zmod_two_eq_one_of_mem_inertiaSubgroupIn_ne_one_of_isFrobeniusAt.solution
