import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_absNorm_sq_mul_relIndex_sq_mul_norm_det_trace_eq_norm_sixteen_mul_relIndex_sq_of_forall_isUnit

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain open AutomorphicForm hiding exists_closure_iff_det_mem_integers_and_norm_det_trace_mul_absNorm_sq_eq_norm_sixteen_of_forall_isUnit
open scoped TensorProduct TensorProduct.RightActions ENNReal

theorem AutomorphicForm.absNorm_sq_mul_relIndex_sq_mul_norm_det_trace_eq_norm_sixteen_mul_relIndex_sq_of_forall_isUnit
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L)
    {κ : Type} [Fintype κ] [DecidableEq κ] (hκ : Fintype.card κ = 4)
    (x : κ → Matrix (Fin 2) (Fin 2) L) (hx : LinearIndependent K x)
    (hspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range x))
    (v : HeightOneSpectrum (𝓞 K))
    (hdiv : ∀ X ∈ twistedCommutant K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀),
      X ≠ 0 → IsUnit X) :
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ 2 *
      ((AddSubgroup.closure
          {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
            ∃ (i : κ) (a : v.adicCompletion K), a ∈ v.adicCompletionIntegers K ∧
              X = (x i).map (fun l : L => l ⊗ₜ[K] a)}).relIndex
        (AddSubgroup.closure
          {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
            X ∈ twistedCommutant K L (v.adicCompletion K) σ
                (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀) ∧
              ∃ a : v.adicCompletion K, a ∈ v.adicCompletionIntegers K ∧ X.det = (1 : L) ⊗ₜ[K] a}) : ℝ) ^ 2 *
      ‖algebraMap K (v.adicCompletion K)
          (Matrix.of fun i j : κ => Algebra.trace K L (Matrix.trace (x i * x j))).det‖ =
    ‖(16 : v.adicCompletion K)‖ *
      ((AddSubgroup.closure
          {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
            X ∈ twistedCommutant K L (v.adicCompletion K) σ
                (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀) ∧
              ∃ a : v.adicCompletion K, a ∈ v.adicCompletionIntegers K ∧ X.det = (1 : L) ⊗ₜ[K] a}).relIndex
        (AddSubgroup.closure
          {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
            ∃ (i : κ) (a : v.adicCompletion K), a ∈ v.adicCompletionIntegers K ∧
              X = (x i).map (fun l : L => l ⊗ₜ[K] a)}) : ℝ) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_absNorm_sq_mul_relIndex_sq_mul_norm_det_trace_eq_norm_sixteen_mul_relIndex_sq_of_forall_isUnit.solution
