import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_algHom_forall_apply_mem_iff_of_isAlgebraic

set_option autoImplicit false

theorem ValuationSubring.exists_algHom_forall_apply_mem_iff_of_isAlgebraic
    (K : Type) [Field K] [Algebra K (AlgebraicClosure ℚ)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (L : Type) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (V : ValuationSubring L)
    (hV : ∀ x : K, algebraMap K L x ∈ V ↔ algebraMap K (AlgebraicClosure ℚ) x ∈ A) :
    ∃ τ : L →ₐ[K] AlgebraicClosure ℚ, ∀ y : L, τ y ∈ A ↔ y ∈ V := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_algHom_forall_apply_mem_iff_of_isAlgebraic.solution
