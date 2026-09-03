import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_norm_det_mul_absNorm_eq_one_and_exists_norm_trace_eq_one_of_forall_isUnit

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal

theorem AutomorphicForm.exists_norm_det_mul_absNorm_eq_one_and_exists_norm_trace_eq_one_of_forall_isUnit
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (e : Fin 4 → Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hbasis : ∀ X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K),
      X ∈ twistedCommutant K L (v.adicCompletion K) σ δ ↔
        ∃! a : Fin 4 → v.adicCompletion K,
          X = ∑ i, (e i).map (fun t : L ⊗[K] v.adicCompletion K => t * ((1 : L) ⊗ₜ[K] a i)))
    (hdiv : ∀ X ∈ twistedCommutant K L (v.adicCompletion K) σ δ, X ≠ 0 → IsUnit X) :
    (∃ X ∈ twistedCommutant K L (v.adicCompletion K) σ δ, ∃ n : v.adicCompletion K,
        X.det = (1 : L) ⊗ₜ[K] n ∧ ‖n‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) = 1) ∧
    (∃ X ∈ twistedCommutant K L (v.adicCompletion K) σ δ, ∃ t n : v.adicCompletion K,
        X.trace = (1 : L) ⊗ₜ[K] t ∧ X.det = (1 : L) ⊗ₜ[K] n ∧ ‖n‖ ≤ 1 ∧ ‖t‖ = 1) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_norm_det_mul_absNorm_eq_one_and_exists_norm_trace_eq_one_of_forall_isUnit.solution
