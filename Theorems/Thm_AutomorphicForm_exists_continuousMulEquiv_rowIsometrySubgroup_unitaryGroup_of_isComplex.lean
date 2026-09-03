import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_continuousMulEquiv_rowIsometrySubgroup_unitaryGroup_of_isComplex

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_continuousMulEquiv_rowIsometrySubgroup_unitaryGroup_of_isComplex
    (F : Type) [Field F] (w : InfinitePlace F) (_hw : w.IsComplex) :
    ∃ e : ↥(rowIsometrySubgroup w.Completion) ≃ₜ* ↥(Matrix.unitaryGroup (Fin 2) ℂ),
      ∀ (k : ↥(rowIsometrySubgroup w.Completion)) (i j : Fin 2),
        ((e k : ↥(Matrix.unitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) i j
          = extensionEmbedding w
              (((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_continuousMulEquiv_rowIsometrySubgroup_unitaryGroup_of_isComplex.solution
