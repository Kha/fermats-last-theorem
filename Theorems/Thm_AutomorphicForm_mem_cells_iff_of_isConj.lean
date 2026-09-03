import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import P2M.Util
import P2M.Sol.S_AutomorphicForm_mem_cells_iff_of_isConj

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.mem_cells_iff_of_isConj (K : Type) [Field K] (γ δ : GL (Fin 2) K) (h : IsConj γ δ) :
    (γ ∈ centralCell K ↔ δ ∈ centralCell K) ∧ (γ ∈ unipotentCell K ↔ δ ∈ unipotentCell K) ∧
      (γ ∈ hyperbolicCell K ↔ δ ∈ hyperbolicCell K) ∧ (γ ∈ ellipticCell K ↔ δ ∈ ellipticCell K) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_mem_cells_iff_of_isConj.solution
