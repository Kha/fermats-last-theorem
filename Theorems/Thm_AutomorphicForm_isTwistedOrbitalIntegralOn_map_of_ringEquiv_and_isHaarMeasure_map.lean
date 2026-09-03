import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map
    {K L A : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)
    {K' L' A' : Type} [Field K'] [Field L'] [Algebra K' L'] [FiniteDimensional K' L']
    [CommRing A'] [Algebra K' A'] [TopologicalSpace A'] [IsTopologicalRing A'] (σ' : L' ≃ₐ[K'] L')
    (E : L ⊗[K] A ≃+* L' ⊗[K'] A') (hE : Continuous E) (hE' : Continuous E.symm)
    (hEσ : ∀ z, E (sigmaTensor K L A σ z) = sigmaTensor K' L' A' σ' (E z))
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    (∀ (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
        (τ'' : @Measure (twistedCentralizer K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ))
          (twistedCentralizerBorel K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ))),
        (letI := glBorelOf (L' ⊗[K'] A'); letI := twistedCentralizerBorel K L A σ δ;
          letI := twistedCentralizerBorel K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ);
          Measure.map (fun t : twistedCentralizer K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ) =>
              (t : GL (Fin 2) (L' ⊗[K'] A'))) τ'' =
            Measure.map (fun t : twistedCentralizer K L A σ δ =>
              Matrix.GeneralLinearGroup.map E.toRingHom (t : GL (Fin 2) (L ⊗[K] A))) τ') →
        ∀ (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (I : ℂ),
          IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I →
          IsTwistedOrbitalIntegralOn K' L' A' σ'
            (@Measure.map _ _ (glBorelOf (L ⊗[K] A)) (glBorelOf (L' ⊗[K'] A'))
              (Matrix.GeneralLinearGroup.map E.toRingHom) μ)
            (Matrix.GeneralLinearGroup.map E.toRingHom δ) τ''
            (φ ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom) I) ∧
    (@Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] A)) μ →
      @Measure.IsHaarMeasure _ _ _ (glBorelOf (L' ⊗[K'] A'))
        (@Measure.map _ _ (glBorelOf (L ⊗[K] A)) (glBorelOf (L' ⊗[K'] A'))
          (Matrix.GeneralLinearGroup.map E.toRingHom) μ)) ∧
    (∀ τ'' : @Measure (twistedCentralizer K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ))
        (twistedCentralizerBorel K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ)),
      @Measure.IsHaarMeasure _ _ _
        (twistedCentralizerBorel K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ)) τ'' →
      ∃ τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ),
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ' ∧
        (letI := glBorelOf (L' ⊗[K'] A'); letI := twistedCentralizerBorel K L A σ δ;
          letI := twistedCentralizerBorel K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ);
          Measure.map (fun t : twistedCentralizer K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ) =>
              (t : GL (Fin 2) (L' ⊗[K'] A'))) τ'' =
            Measure.map (fun t : twistedCentralizer K L A σ δ =>
              Matrix.GeneralLinearGroup.map E.toRingHom (t : GL (Fin 2) (L ⊗[K] A))) τ')) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map.solution
