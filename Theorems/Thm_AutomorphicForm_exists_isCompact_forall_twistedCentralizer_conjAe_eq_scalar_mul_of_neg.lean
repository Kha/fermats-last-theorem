import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) :
    ∃ C : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), IsCompact C ∧
      C ⊆ (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ))) ∧
      ∀ t ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ,
        ∃ e : ℝˣ, ∃ k ∈ C,
          t = toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) e) * k := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg.solution
