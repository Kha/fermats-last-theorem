import Definitions.Def_AutomorphicForm_BaseChangePlaces
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange_of_isMulRightInvariant

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions Pointwise

theorem AutomorphicForm.exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange_of_isMulRightInvariant
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ))
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)))
    (hτf : ∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsMulRightInvariant _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
        (AutomorphicForm.tensorPlace K L v δ)) _ (τf v))
    (hτf1 : ∀ v : HeightOneSpectrum (𝓞 K),
      τf v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ) (φa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      (∀ v ∉ S, AutomorphicForm.tensorPlace K L v x ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
        φ x = φa (AutomorphicForm.tensorArch K L x) *
          ∏ v ∈ S, φS v (AutomorphicForm.tensorPlace K L v x))
    (hφ0 : ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      (∃ v ∉ S, AutomorphicForm.tensorPlace K L v x ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
        φ x = 0)
    (hw : ∃ w : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℝ,
      AutomorphicForm.IsTwistedSectionFnOn K L (AdeleRing (𝓞 K) K) σ δ τ φ w)
    (hne : ∃ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) ≠ 0) :
    (∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧ ∀ v ∉ S₁,
      AutomorphicForm.IsTwistedSectionFnOn K L (v.adicCompletion K) σ
        (AutomorphicForm.tensorPlace K L v δ) (τf v)
        ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
        ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℝ))) ∧
    (∀ v ∈ S, ∃ C : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)), IsCompact C ∧
      {y : GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
          φS v (y⁻¹ * AutomorphicForm.tensorPlace K L v δ *
            AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ y) ≠ 0} ⊆
        (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
            (AutomorphicForm.tensorPlace K L v δ) :
          Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) * C) ∧
    (∀ v ∉ S, ∃ C : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)), IsCompact C ∧
      {y : GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
          y⁻¹ * AutomorphicForm.tensorPlace K L v δ *
              AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ y ∈
            AutomorphicForm.semiLocalIntegralSet K L v} ⊆
        (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
            (AutomorphicForm.tensorPlace K L v δ) :
          Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) * C) ∧
    (∃ C : Set (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)), IsCompact C ∧
      {y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) |
          φa (y⁻¹ * AutomorphicForm.tensorArch K L δ *
            AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ y) ≠ 0} ⊆
        (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
            (AutomorphicForm.tensorArch K L δ) :
          Set (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) * C) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange_of_isMulRightInvariant.solution
