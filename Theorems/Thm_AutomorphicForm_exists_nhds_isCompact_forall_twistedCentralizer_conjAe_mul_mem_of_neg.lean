import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_nhds_isCompact_forall_twistedCentralizer_conjAe_mul_mem_of_neg

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_nhds_isCompact_forall_twistedCentralizer_conjAe_mul_mem_of_neg
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (ω : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ))) (hω : IsCompact ω) :
    ∃ U₁ ∈ nhds (1 : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)),
      ∃ Ω : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), IsCompact Ω ∧
      ∀ h ∈ U₁, h ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ →
        ∀ x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
          x⁻¹ * (h * δ) * sigmaGL ℝ ℂ ℝ Complex.conjAe x ∈ ω →
            ∃ t ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ, ∃ d ∈ Ω, x = t * d := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_nhds_isCompact_forall_twistedCentralizer_conjAe_mul_mem_of_neg.solution
