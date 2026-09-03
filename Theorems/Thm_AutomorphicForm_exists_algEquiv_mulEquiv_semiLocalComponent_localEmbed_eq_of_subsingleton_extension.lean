import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_algEquiv_mulEquiv_semiLocalComponent_localEmbed_eq_of_subsingleton_extension

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_algEquiv_mulEquiv_semiLocalComponent_localEmbed_eq_of_subsingleton_extension
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hinert : Subsingleton (v.Extension (𝓞 L))) (w : v.Extension (𝓞 L)) :
    ∃ (Φ : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
      (e : GL (Fin 2) (w.1.adicCompletion L) ≃* GL (Fin 2) (L ⊗[K] v.adicCompletion K))
      (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L),

      (∀ (x : GL (Fin 2) (w.1.adicCompletion L)) (p q : Fin 2),
        ((e x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) p q =
          Φ.symm ((x : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) p q)) ∧

      (∀ x : L ⊗[K] v.adicCompletion K, Φ (sigmaTensor K L (v.adicCompletion K) σ x) = θ (Φ x)) ∧
      (∀ t : v.adicCompletion K, Φ ((1 : L) ⊗ₜ[K] t) = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) t) ∧
      (∀ x : L ⊗[K] v.adicCompletion K, x ∈ semiLocalIntegers K L v ↔ Φ x ∈ w.1.adicCompletionIntegers L) ∧
      orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) ∧
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = Module.finrank K L ∧
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1 ∧
      (∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖θ y - y‖ = 1) ∧

      (∀ g : GL (Fin 2) (w.1.adicCompletion L),
        semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w.1 g) = e g) ∧
      e '' localIntegralSet L w.1 = semiLocalIntegralSet K L v ∧
      (∀ x : GL (Fin 2) (w.1.adicCompletion L),
        sigmaGL K L (v.adicCompletion K) σ (e x) = e (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x)) ∧
      (∀ g : GL (Fin 2) (v.adicCompletion K),
        toTensorGL K L (v.adicCompletion K) g =
          e (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)) g)) ∧
      (∀ x : GL (Fin 2) (w.1.adicCompletion L), semiLocalWeight K L v (e x) = LocalWeight.weight x) ∧

      (∀ (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
          (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
            (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
          (_ : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
          (_ : τ' {t | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ semiLocalIntegralSet K L v} = 1)
          (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (J' : ℂ),
          IsTwistedWeightedOrbitalIntegral K L v σ δ τ' φ J' →
          ∃ (τE : @Measure (sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (e.symm δ))
              (borel _)) (sE : GL (Fin 2) (w.1.adicCompletion L) → ℝ),
            @Measure.IsHaarMeasure _ _ _ (borel _) τE ∧
            τE {t | (t : GL (Fin 2) (w.1.adicCompletion L)) ∈ localIntegralSet L w.1} = 1 ∧
            (∀ y, 0 ≤ sE y) ∧ Measurable[localGLBorel L w.1] sE ∧ HasCompactSupport sE ∧
            (∀ y : GL (Fin 2) (w.1.adicCompletion L),
              φ (e (y⁻¹ * e.symm δ * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom y)) ≠ 0 →
                ∫ t : sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (e.symm δ),
                    sE ((t : GL (Fin 2) (w.1.adicCompletion L)) * y) ∂τE = 1) ∧
            J' = ∫ y : GL (Fin 2) (w.1.adicCompletion L),
                φ (e (y⁻¹ * e.symm δ * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom y)) *
                  ((LocalWeight.weight y : ℝ) : ℂ) * (sE y : ℂ) ∂(localHaar L w.1)) ∧
      (∀ s : Set (GL (Fin 2) (w.1.adicCompletion L)), MeasurableSet[localGLBorel L w.1] s →
        semiLocalHaar K L v (e '' s) = localHaar L w.1 s) ∧
      Continuous e ∧ Continuous e.symm := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_algEquiv_mulEquiv_semiLocalComponent_localEmbed_eq_of_subsingleton_extension.solution
