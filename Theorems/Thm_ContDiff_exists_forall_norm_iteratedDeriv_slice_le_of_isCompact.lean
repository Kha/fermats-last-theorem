import Mathlib
import P2M.Util
import P2M.Sol.S_ContDiff_exists_forall_norm_iteratedDeriv_slice_le_of_isCompact

set_option autoImplicit false

theorem ContDiff.exists_forall_norm_iteratedDeriv_slice_le_of_isCompact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : E → ℝ → F) (hΨ : ContDiff ℝ (⊤ : ℕ∞) (fun p : E × ℝ => Ψ p.1 p.2))
    (S : Set E) (hS : IsCompact S) (R : ℝ) (N : ℕ) :
    (∀ a : E, ContDiff ℝ N (Ψ a)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ S, ∀ u ∈ Set.Icc (-R) R, ∀ n ≤ N, ‖iteratedDeriv n (Ψ a) u‖ ≤ C := by p2m_exact_reverting @_root_.P2MW.S_ContDiff_exists_forall_norm_iteratedDeriv_slice_le_of_isCompact.solution
