import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_finiteDimensional_span_range_of_isArchFactorBiFinite

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.finiteDimensional_span_range_of_isArchFactorBiFinite
    (F : Type) [Field F] (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfa : IsArchFactorBiFinite F tys fa) (w : InfinitePlace F) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
        fun x : GL (Fin 2) (InfiniteAdeleRing F) => fa (x * archRowIsometryInclAt₀ F w k))) ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
        fun x : GL (Fin 2) (InfiniteAdeleRing F) => fa (x * archRowIsometryInclAt₀ F w k)⁻¹)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_finiteDimensional_span_range_of_isArchFactorBiFinite.solution
