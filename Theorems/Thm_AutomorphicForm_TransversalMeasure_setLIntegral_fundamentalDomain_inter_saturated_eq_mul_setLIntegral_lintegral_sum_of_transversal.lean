import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_TransversalMeasure
import P2M.Util
import P2M.Sol.S_AutomorphicForm_TransversalMeasure_setLIntegral_fundamentalDomain_inter_saturated_eq_mul_setLIntegral_lintegral_sum_of_transversal
attribute [-instance] M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm.TransversalMeasure
open scoped ENNReal

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel in

theorem AutomorphicForm.TransversalMeasure.setLIntegral_fundamentalDomain_inter_saturated_eq_mul_setLIntegral_lintegral_sum_of_transversal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Sτ : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (τ : Fin n → Measure (AdeleRing (𝓞 L) L)ˣ) (cτ : ℝ≥0∞)
    (hmeas : MeasurableSet (saturated K L Sτ))
    (hmul : ∀ t ∈ saturated K L Sτ, ∀ s : (AdeleRing (𝓞 K) K)ˣ, t * idelesBaseChange K L s ∈ saturated K L Sτ)
    (hτfin : ∀ j, IsFiniteMeasureOnCompacts (τ j)) (hτ0 : ∀ j, τ j (saturated K L Sτ)ᶜ = 0)
    (hτ2 : ∀ E : Set (AdeleRing (𝓞 L) L)ˣ, MeasurableSet E → E ⊆ saturated K L Sτ →
      Measurable (fun s : (AdeleRing (𝓞 K) K)ˣ =>
        (∑ j, τ j) ((fun t => t * idelesBaseChange K L s) ⁻¹' E)) ∧
      NumberField.Idele.idelicHaar L E = cτ *
        ∫⁻ s : (AdeleRing (𝓞 K) K)ˣ, (∑ j, τ j) ((fun t => t * idelesBaseChange K L s) ⁻¹' E)
          ∂(NumberField.Idele.idelicHaar K))
    (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK
      (NumberField.Idele.idelicHaar K))
    (Ω : Set (AdeleRing (𝓞 L) L)ˣ) (hΩm : MeasurableSet Ω)
    (hΩ : IsFundamentalDomain
      ((idelesBaseChange K L).comp (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))).range Ω
      (NumberField.Idele.idelicHaar L)) :
    (∀ G : (AdeleRing (𝓞 L) L)ˣ → ℝ≥0∞, Measurable G →
      (∀ (k : Kˣ) (t : (AdeleRing (𝓞 L) L)ˣ),
        G (t * idelesBaseChange K L (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k)) =
          G t) →
      ∫⁻ t in Ω ∩ saturated K L Sτ, G t ∂(NumberField.Idele.idelicHaar L) =
        cτ * ∫⁻ s in ΩK, ∫⁻ t, G (t * idelesBaseChange K L s) ∂(∑ j, τ j) ∂(NumberField.Idele.idelicHaar K)) ∧
    (∀ F : (AdeleRing (𝓞 L) L)ˣ → ℂ, Measurable F →
      (∀ (k : Kˣ) (t : (AdeleRing (𝓞 L) L)ˣ),
        F (t * idelesBaseChange K L (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k)) =
          F t) →
      (∫⁻ t in Ω ∩ saturated K L Sτ, ‖F t‖ₑ ∂(NumberField.Idele.idelicHaar L) ≠ ⊤) →
      ∫ t in Ω ∩ saturated K L Sτ, F t ∂(NumberField.Idele.idelicHaar L) =
        (cτ.toReal : ℂ) *
          ∫ s in ΩK, ∫ t, F (t * idelesBaseChange K L s) ∂(∑ j, τ j) ∂(NumberField.Idele.idelicHaar K)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_TransversalMeasure_setLIntegral_fundamentalDomain_inter_saturated_eq_mul_setLIntegral_lintegral_sum_of_transversal.solution
