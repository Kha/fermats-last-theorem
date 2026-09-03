import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_closure_iff_det_mem_integers_and_norm_det_trace_mul_absNorm_sq_eq_norm_sixteen_of_forall_isUnit

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal

theorem AutomorphicForm.exists_closure_iff_det_mem_integers_and_norm_det_trace_mul_absNorm_sq_eq_norm_sixteen_of_forall_isUnit
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (e : Fin 4 → Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hbasis : ∀ X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K),
      X ∈ twistedCommutant K L (v.adicCompletion K) σ δ ↔
        ∃! a : Fin 4 → v.adicCompletion K,
          X = ∑ i, (e i).map (fun t : L ⊗[K] v.adicCompletion K => t * ((1 : L) ⊗ₜ[K] a i)))
    (hdiv : ∀ X ∈ twistedCommutant K L (v.adicCompletion K) σ δ, X ≠ 0 → IsUnit X)
    (τ : L ⊗[K] v.adicCompletion K →+ v.adicCompletion K)
    (hτ : ∀ (l : L) (a : v.adicCompletion K),
      τ (l ⊗ₜ[K] a) = algebraMap K (v.adicCompletion K) (Algebra.trace K L l) * a) :
    ∃ f : Fin 4 → Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K),
      (∀ X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K),
        X ∈ AddSubgroup.closure
            {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
              ∃ (i : Fin 4) (a : v.adicCompletion K), a ∈ v.adicCompletionIntegers K ∧
                X = (f i).map (fun t : L ⊗[K] v.adicCompletion K => t * ((1 : L) ⊗ₜ[K] a))} ↔
          X ∈ twistedCommutant K L (v.adicCompletion K) σ δ ∧
            ∃ a : v.adicCompletion K, a ∈ v.adicCompletionIntegers K ∧ X.det = (1 : L) ⊗ₜ[K] a) ∧
      ‖(Matrix.of fun i j : Fin 4 => τ (Matrix.trace (f i * f j))).det‖ *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ 2 =
        ‖(16 : v.adicCompletion K)‖ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_closure_iff_det_mem_integers_and_norm_det_trace_mul_absNorm_sq_eq_norm_sixteen_of_forall_isUnit.solution
