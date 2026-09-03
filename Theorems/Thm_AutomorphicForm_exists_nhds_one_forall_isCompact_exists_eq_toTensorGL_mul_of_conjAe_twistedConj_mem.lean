import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_nhds_one_forall_isCompact_exists_eq_toTensorGL_mul_of_conjAe_twistedConj_mem

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_nhds_one_forall_isCompact_exists_eq_toTensorGL_mul_of_conjAe_twistedConj_mem
    (d : ℝˣ) :
    ∃ U ∈ nhds (1 : GL (Fin 2) ℝ),
      ∀ C : Set (GL (Fin 2) ℂ), IsCompact C →
        ∃ K : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), IsCompact K ∧
          ∀ t ∈ U, ∀ x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
            (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
              (x⁻¹ * toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d) *
                sigmaGL ℝ ℂ ℝ Complex.conjAe x) : GL (Fin 2) ℂ) ∈ C →
              ∃ (m : GL (Fin 2) ℝ) (k : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), k ∈ K ∧ x = toTensorGL ℝ ℂ ℝ m * k := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_nhds_one_forall_isCompact_exists_eq_toTensorGL_mul_of_conjAe_twistedConj_mem.solution
