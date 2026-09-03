import Definitions.Def_AutomorphicForm_FactorizableTestFn
import P2M.Util
import P2M.Sol.S_AutomorphicForm_IsFinTestFactor_exists_isCompact_isOpen_forall_mul_eq

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain

theorem AutomorphicForm.IsFinTestFactor.exists_isCompact_isOpen_forall_mul_eq (K : Type) [Field K]
    [NumberField K] (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ) (hff : IsFinTestFactor K ff) :
    ∃ U : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)),
      IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) ∧
        IsOpen (U : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) ∧
          ∀ x, ∀ u ∈ U, ff (x * u) = ff x := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_IsFinTestFactor_exists_isCompact_isOpen_forall_mul_eq.solution
