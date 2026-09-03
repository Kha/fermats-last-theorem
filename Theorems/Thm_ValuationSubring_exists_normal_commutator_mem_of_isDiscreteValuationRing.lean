import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_normal_commutator_mem_of_isDiscreteValuationRing

set_option autoImplicit false

universe u v

theorem ValuationSubring.exists_normal_commutator_mem_of_isDiscreteValuationRing
    (K : Type u) [Field K] {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing ↥A] :
    ∃ Pw : Subgroup ↥(A.inertiaSubgroup K),
      (∀ σ : ↥(A.inertiaSubgroup K), σ ∈ Pw ↔
        ∀ ϖ : ↥A, Irreducible ϖ →
          ((σ : ↥(A.decompositionSubgroup K)) • ϖ - ϖ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A ^ 2) ∧
      Pw.Normal ∧ ∀ a b : ↥(A.inertiaSubgroup K), a⁻¹ * b⁻¹ * a * b ∈ Pw := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_normal_commutator_mem_of_isDiscreteValuationRing.solution
