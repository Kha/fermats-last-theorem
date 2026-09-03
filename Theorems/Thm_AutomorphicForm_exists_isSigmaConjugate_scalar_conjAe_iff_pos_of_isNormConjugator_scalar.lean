import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar
    (c : ℝˣ) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) :
    (∃ z : (ℂ ⊗[ℝ] ℝ)ˣ, IsSigmaConjugate ℝ ℂ ℝ Complex.conjAe δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ↔
      0 < (c : ℝ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar.solution
