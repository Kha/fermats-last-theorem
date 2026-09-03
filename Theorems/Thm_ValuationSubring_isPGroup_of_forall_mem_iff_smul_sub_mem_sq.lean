import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_isPGroup_of_forall_mem_iff_smul_sub_mem_sq

set_option autoImplicit false

universe u v

theorem ValuationSubring.isPGroup_of_forall_mem_iff_smul_sub_mem_sq
    (K : Type u) [Field K] {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing ↥A]
    (p : ℕ) [Fact p.Prime] (hp : (p : ↥A) ∈ IsLocalRing.maximalIdeal ↥A)
    (Pw : Subgroup ↥(A.inertiaSubgroup K))
    (hPw : ∀ σ : ↥(A.inertiaSubgroup K), σ ∈ Pw ↔
        ∀ ϖ : ↥A, Irreducible ϖ →
          ((σ : ↥(A.decompositionSubgroup K)) • ϖ - ϖ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A ^ 2) :
    IsPGroup p ↥Pw := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isPGroup_of_forall_mem_iff_smul_sub_mem_sq.solution
