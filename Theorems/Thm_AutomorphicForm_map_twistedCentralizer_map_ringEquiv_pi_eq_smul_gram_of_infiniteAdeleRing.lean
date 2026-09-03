import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((w : InfinitePlace K) → L ⊗[K] w.Completion))
    (hΞ : Continuous Ξ) (hΞ' : Continuous Ξ.symm)
    [algE : ∀ w : InfinitePlace K, Algebra ℝ (L ⊗[K] w.Completion)]
    (hΞr : ∀ (r : ℝ) (z : L ⊗[K] InfiniteAdeleRing K),
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      Ξ (r • z) = r • Ξ z)
    (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ))
    (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (s : ENNReal)
    (hL :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      letI := AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ
      Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
          ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τ' =
        s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
              Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
            (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
              (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)) :
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) ((w : InfinitePlace K) → L ⊗[K] w.Completion)) := borel _
    letI := AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ
    Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
        (((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))).map Ξ) τ' =
      s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
              Algebra.trace ℝ ((w : InfinitePlace K) → L ⊗[K] w.Completion)
                (Matrix.trace ((e₂ i).map Ξ * (e₂ j).map Ξ))).det|)) •
            Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • (e₂ i).map Ξ) volume).withDensity
          (fun X : Matrix (Fin 2) (Fin 2) ((w : InfinitePlace K) → L ⊗[K] w.Completion) =>
            (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing.solution
