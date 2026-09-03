import Definitions.Def_AutomorphicForm_FactorizableTestFn
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isArchTestFactor_of_forall_eq_integral_snoc

set_option autoImplicit false

open NumberField MeasureTheory
open scoped Classical

theorem AutomorphicForm.isArchTestFactor_of_forall_eq_integral_snoc
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    [BorelSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    (μ : Measure (GL (Fin 2) (InfiniteAdeleRing K))) [IsFiniteMeasureOnCompacts μ] {n : ℕ}
    (Φ : (Fin (n + 1) → GL (Fin 2) (InfiniteAdeleRing K)) → ℂ)
    (hΦs : ∃ Ψ : (Fin (n + 1) → Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ ∀ x, Φ x = Ψ (fun k => AutomorphicForm.archEntries K (x k)))
    (hΦc : HasCompactSupport Φ)
    (f : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (hf : ∀ h, f h = ∫ c : Fin n → GL (Fin 2) (InfiniteAdeleRing K),
      Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h)) ∂(Measure.pi fun _ => μ)) :
    AutomorphicForm.IsArchTestFactor K f := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isArchTestFactor_of_forall_eq_integral_snoc.solution
