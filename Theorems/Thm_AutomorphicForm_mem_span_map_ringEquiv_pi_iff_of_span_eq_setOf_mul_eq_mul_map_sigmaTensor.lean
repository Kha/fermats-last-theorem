import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((w : InfinitePlace K) → L ⊗[K] w.Completion))
    (hΞt : ∀ (x : L) (a : InfiniteAdeleRing K) (w : InfinitePlace K), Ξ (x ⊗ₜ a) w = x ⊗ₜ (a w))
    [algE : ∀ w : InfinitePlace K, Algebra ℝ (L ⊗[K] w.Completion)]
    (hΞr : ∀ (r : ℝ) (z : L ⊗[K] InfiniteAdeleRing K),
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      Ξ (r • z) = r • Ξ z)
    (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (δw : ∀ w : InfinitePlace K, Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion))
    (hδw : ∀ (w : InfinitePlace K) (i j : Fin 2), Ξ (δ i j) w = δw w i j)
    (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hL :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      LinearIndependent ℝ e₂ ∧
        (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
          {X | X * δ = δ * X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)}) :
    LinearIndependent ℝ (fun a => (e₂ a).map Ξ) ∧
      ∀ X : Matrix (Fin 2) (Fin 2) ((w : InfinitePlace K) → L ⊗[K] w.Completion),
        X ∈ Submodule.span ℝ (Set.range (fun a => (e₂ a).map Ξ)) ↔
          ∀ w : InfinitePlace K,
            X.map (Pi.evalRingHom (fun w : InfinitePlace K => L ⊗[K] w.Completion) w) ∈
              Submodule.span ℝ {Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion) |
                Y * δw w = δw w * Y.map (AutomorphicForm.sigmaTensor K L w.Completion σ)} := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor.solution
