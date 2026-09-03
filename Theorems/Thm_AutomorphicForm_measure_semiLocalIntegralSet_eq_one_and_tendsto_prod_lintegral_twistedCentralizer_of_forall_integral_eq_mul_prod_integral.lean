import Definitions.Def_AutomorphicForm_BaseChangePlaces
import P2M.Util
import P2M.Sol.S_AutomorphicForm_measure_semiLocalIntegralSet_eq_one_and_tendsto_prod_lintegral_twistedCentralizer_of_forall_integral_eq_mul_prod_integral

set_option autoImplicit false

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions Topology ENNReal

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

theorem AutomorphicForm.measure_semiLocalIntegralSet_eq_one_and_tendsto_prod_lintegral_twistedCentralizer_of_forall_integral_eq_mul_prod_integral
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (τa : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
      (AutomorphicForm.tensorArch K L δ)))
    (hτa : τa.IsHaarMeasure)
    (τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v δ)))
    (hτf : ∀ v, (τf v).IsHaarMeasure)
    (τ : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ))
    (c : ℝ) (hc : 0 < c) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (hτprod : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S →
        ∀ (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ) => Wa t) τa →
        (∀ v ∈ S, AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ) => WS v t) (τf v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂τ = c * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))
    (S₁ : Finset (HeightOneSpectrum (𝓞 K)))
    (Fa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞)
    (hFa : Measurable fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
      (AutomorphicForm.tensorArch K L δ) => Fa t)
    (Ff : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ≥0∞)
    (hFf : ∀ v, Measurable fun t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v δ) => Ff v t)
    (hunit : ∀ v ∉ S₁, ∀ t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v δ),
      (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L v → Ff v t = 1)
    (F : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ → ℝ≥0∞)
    (hF : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₁ ⊆ S →
      ∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
        (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
          F t = Fa (AutomorphicForm.tensorArch K L t) * ∏ v ∈ S, Ff v (AutomorphicForm.tensorPlace K L v t)) :
    (∀ v ∉ S₀, τf v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1) ∧
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
        ENNReal.ofReal c * (∫⁻ t, Fa t ∂τa) * ∏ v ∈ S, ∫⁻ t, Ff v t ∂(τf v))
      atTop (𝓝 (∫⁻ t, F t ∂τ)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_measure_semiLocalIntegralSet_eq_one_and_tendsto_prod_lintegral_twistedCentralizer_of_forall_integral_eq_mul_prod_integral.solution
