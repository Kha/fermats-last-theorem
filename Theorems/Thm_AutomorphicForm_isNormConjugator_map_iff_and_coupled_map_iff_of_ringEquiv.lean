import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv
    {K L A : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)
    {K' L' A' : Type} [Field K'] [Field L'] [Algebra K' L'] [FiniteDimensional K' L']
    [CommRing A'] [Algebra K' A'] [TopologicalSpace A'] [IsTopologicalRing A'] (σ' : L' ≃ₐ[K'] L')
    (hrank : Module.finrank K L = Module.finrank K' L')
    (e : A ≃+* A') (he : Continuous e) (he' : Continuous e.symm)
    (E : L ⊗[K] A ≃+* L' ⊗[K'] A') (hE : Continuous E) (hE' : Continuous E.symm)
    (hEσ : ∀ z, E (sigmaTensor K L A σ z) = sigmaTensor K' L' A' σ' (E z))
    (hEe : ∀ g : GL (Fin 2) A, Matrix.GeneralLinearGroup.map E.toRingHom (toTensorGL K L A g) =
      toTensorGL K' L' A' (Matrix.GeneralLinearGroup.map e.toRingHom g))
    (γ : GL (Fin 2) A) (δ y : GL (Fin 2) (L ⊗[K] A)) :
    (IsNormConjugator K L A σ γ δ y ↔
      IsNormConjugator K' L' A' σ' (Matrix.GeneralLinearGroup.map e.toRingHom γ)
        (Matrix.GeneralLinearGroup.map E.toRingHom δ) (Matrix.GeneralLinearGroup.map E.toRingHom y)) ∧
    ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
      (τ₀ : @Measure (Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) A')))
        (centralizerBorel A' (Matrix.GeneralLinearGroup.map e.toRingHom γ)))
      (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
      (τ₀' : @Measure (twistedCentralizer K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ))
        (twistedCentralizerBorel K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ))),
      (letI := glBorelOf A'; letI := centralizerBorel A γ;
        letI := centralizerBorel A' (Matrix.GeneralLinearGroup.map e.toRingHom γ);
        Measure.map (fun t : Subgroup.centralizer
            ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) A')) => (t : GL (Fin 2) A')) τ₀ =
          Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
            Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) τ) →
      (letI := glBorelOf (L' ⊗[K'] A'); letI := twistedCentralizerBorel K L A σ δ;
        letI := twistedCentralizerBorel K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ);
        Measure.map (fun t : twistedCentralizer K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ) =>
            (t : GL (Fin 2) (L' ⊗[K'] A'))) τ₀' =
          Measure.map (fun t : twistedCentralizer K L A σ δ =>
            Matrix.GeneralLinearGroup.map E.toRingHom (t : GL (Fin 2) (L ⊗[K] A))) τ') →
      (Coupled K L A σ γ δ y τ τ' ↔
        Coupled K' L' A' σ' (Matrix.GeneralLinearGroup.map e.toRingHom γ)
          (Matrix.GeneralLinearGroup.map E.toRingHom δ) (Matrix.GeneralLinearGroup.map E.toRingHom y) τ₀ τ₀') := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv.solution
