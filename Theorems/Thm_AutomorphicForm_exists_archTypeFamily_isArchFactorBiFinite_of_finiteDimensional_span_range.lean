import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_archTypeFamily_isArchFactorBiFinite_of_finiteDimensional_span_range

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.exists_archTypeFamily_isArchFactorBiFinite_of_finiteDimensional_span_range
    (F : Type) [Field F] (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfin : ∀ w : InfinitePlace F,
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
        fun x : GL (Fin 2) (InfiniteAdeleRing F) => fa (x * archRowIsometryInclAt₀ F w k))) ∧
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
        fun x : GL (Fin 2) (InfiniteAdeleRing F) => fa (x * archRowIsometryInclAt₀ F w k)⁻¹))) :
    ∃ tys : ArchTypeFamily F, IsArchFactorBiFinite F tys fa := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_archTypeFamily_isArchFactorBiFinite_of_finiteDimensional_span_range.solution
