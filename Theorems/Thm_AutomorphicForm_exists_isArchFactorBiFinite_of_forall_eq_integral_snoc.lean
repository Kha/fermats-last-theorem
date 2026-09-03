import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isArchFactorBiFinite_of_forall_eq_integral_snoc

set_option autoImplicit false

open NumberField MeasureTheory

theorem AutomorphicForm.exists_isArchFactorBiFinite_of_forall_eq_integral_snoc
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    [BorelSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    (μ : Measure (GL (Fin 2) (InfiniteAdeleRing K))) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] {n : ℕ}
    (Φ : (Fin (n + 1) → GL (Fin 2) (InfiniteAdeleRing K)) → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) (tys : AutomorphicForm.ArchTypeFamily K)
    (h0 : ∀ x : Fin (n + 1) → GL (Fin 2) (InfiniteAdeleRing K),
      (fun g => Φ (Function.update x 0 g⁻¹)) ∈ AutomorphicForm.archFactorCutSubmodule K tys)
    (hn : ∀ x : Fin (n + 1) → GL (Fin 2) (InfiniteAdeleRing K),
      (fun g => Φ (Function.update x (Fin.last n) g)) ∈
        AutomorphicForm.archFactorDualCutSubmodule K tys)
    (f : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (hf : ∀ h, f h = ∫ c : Fin n → GL (Fin 2) (InfiniteAdeleRing K),
      Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h)) ∂(Measure.pi fun _ => μ)) :
    ∃ tysK : AutomorphicForm.ArchTypeFamily K, AutomorphicForm.IsArchFactorBiFinite K tysK f := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_of_forall_eq_integral_snoc.solution
