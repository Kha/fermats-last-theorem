import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
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
    (n₁ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hK :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      LinearIndependent ℝ e₁ ∧
        (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
          Set.range (fun Y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
            Y.map (Algebra.TensorProduct.includeRight :
              InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K))) :
    LinearIndependent ℝ (fun a => (e₁ a).map Ξ) ∧
      ∀ X : Matrix (Fin 2) (Fin 2) ((w : InfinitePlace K) → L ⊗[K] w.Completion),
        X ∈ Submodule.span ℝ (Set.range (fun a => (e₁ a).map Ξ)) ↔
          ∀ w : InfinitePlace K, X.map (Pi.evalRingHom (fun w : InfinitePlace K => L ⊗[K] w.Completion) w) ∈
            Submodule.span ℝ (Set.range (fun Y : Matrix (Fin 2) (Fin 2) w.Completion =>
              Y.map (fun x : w.Completion => (1 : L) ⊗ₜ[K] x))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight.solution
