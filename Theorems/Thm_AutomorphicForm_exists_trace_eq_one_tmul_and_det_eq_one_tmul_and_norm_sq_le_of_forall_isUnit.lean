import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_trace_eq_one_tmul_and_det_eq_one_tmul_and_norm_sq_le_of_forall_isUnit

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal

theorem AutomorphicForm.exists_trace_eq_one_tmul_and_det_eq_one_tmul_and_norm_sq_le_of_forall_isUnit
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hdiv : ∀ X ∈ twistedCommutant K L (v.adicCompletion K) σ δ, X ≠ 0 → IsUnit X)
    (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hX : X ∈ twistedCommutant K L (v.adicCompletion K) σ δ) :
    ∃ t n : v.adicCompletion K,
      X.trace = (1 : L) ⊗ₜ[K] t ∧ X.det = (1 : L) ⊗ₜ[K] n ∧ ‖t‖ ^ 2 ≤ ‖n‖ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_trace_eq_one_tmul_and_det_eq_one_tmul_and_norm_sq_le_of_forall_isUnit.solution
