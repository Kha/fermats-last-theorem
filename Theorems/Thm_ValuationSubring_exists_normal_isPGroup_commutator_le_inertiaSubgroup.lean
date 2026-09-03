import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_normal_isPGroup_commutator_le_inertiaSubgroup

set_option autoImplicit false

universe u v

theorem ValuationSubring.exists_normal_isPGroup_commutator_le_inertiaSubgroup
    (K : Type u) [Field K] {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing ↥A]
    (p : ℕ) [Fact p.Prime] (hp : (p : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) :
    ∃ Pw : Subgroup ↥(A.inertiaSubgroup K),
      (∀ σ : ↥(A.inertiaSubgroup K), σ ∈ Pw ↔
        ∀ ϖ : ↥A, Irreducible ϖ →
          ((σ : ↥(A.decompositionSubgroup K)) • ϖ - ϖ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A ^ 2) ∧
      Pw.Normal ∧ IsPGroup p ↥Pw ∧
      ∀ a b : ↥(A.inertiaSubgroup K), a⁻¹ * b⁻¹ * a * b ∈ Pw := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_normal_isPGroup_commutator_le_inertiaSubgroup.solution
