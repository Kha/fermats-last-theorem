import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isClosedEmbedding_toTensorGL_and_exists_nhds_one_mem_twistedCentralizer_conjAe_iff

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isClosedEmbedding_toTensorGL_and_exists_nhds_one_mem_twistedCentralizer_conjAe_iff
    (d : ℝˣ) :
    Topology.IsClosedEmbedding (toTensorGL ℝ ℂ ℝ) ∧
    ∃ U ∈ nhds (1 : GL (Fin 2) ℝ),
      (∀ t ∈ U, ∀ x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        x ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe
            (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)) ↔
          ∃ m : GL (Fin 2) ℝ, m ∈ Subgroup.centralizer ({t} : Set (GL (Fin 2) ℝ)) ∧ x = toTensorGL ℝ ℂ ℝ m) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isClosedEmbedding_toTensorGL_and_exists_nhds_one_mem_twistedCentralizer_conjAe_iff.solution
