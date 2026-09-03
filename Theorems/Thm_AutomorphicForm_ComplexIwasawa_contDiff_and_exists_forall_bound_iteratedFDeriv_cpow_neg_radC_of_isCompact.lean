import Definitions.Def_AutomorphicForm_ComplexIwasawa
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Topology.Compactness.Compact
import P2M.Util
import P2M.Sol.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact

set_option autoImplicit false

p2m_open "MeasureTheory AutomorphicForm.ComplexIwasawa~exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact"
open scoped ContDiff

theorem AutomorphicForm.ComplexIwasawa.contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (_h𝒢 : IsCompact 𝒢) (_hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (U : Set ℂ) (_hU : IsCompact U) (n : ℕ) :
    (∀ g ∈ 𝒢, ∀ u : ℂ, ContDiff ℝ ∞ (fun z : ℂ => ((radC g z : ℂ) ^ (-u)))) ∧
    ∃ K : ℝ, 0 < K ∧ ∀ g ∈ 𝒢, ∀ u ∈ U, ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (fun z : ℂ => ((radC g z : ℂ) ^ (-u))) z‖ ≤ K * radC g z ^ (-u.re) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.solution
