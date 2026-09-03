import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isHaarMeasure_and_eq_integral_indicator_localIntegralSet_twistedConj_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isHaarMeasure_and_eq_integral_indicator_localIntegralSet_twistedConj_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) {m : ℕ}
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (Ψ : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] (Fin (m + 1) → w.1.adicCompletion L))
    (hΨσ : ∀ z : L ⊗[K] v.adicCompletion K,
      (∀ k : Fin m, Ψ (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ z) k.castSucc = Ψ z k.succ) ∧
        Ψ (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ z) (Fin.last m) = θ (Ψ z 0))
    (hΨint : ∀ z : L ⊗[K] v.adicCompletion K,
      z ∈ AutomorphicForm.semiLocalIntegers K L v ↔ ∀ j, Ψ z j ∈ w.1.adicCompletionIntegers L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hT : ∀ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ, ∀ p q,
      ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) p q ∈
        Set.range (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (hτ'1 : τ' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (I : ℂ) (hI : AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ'
        ((AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))) I)
    (ν : GL (Fin 2) (w.1.adicCompletion L))
    (hν : ν = (List.ofFn fun j : Fin (m + 1) => Matrix.GeneralLinearGroup.map
        ((Pi.evalRingHom (fun _ : Fin (m + 1) => w.1.adicCompletion L) j).comp
          (Ψ : L ⊗[K] v.adicCompletion K →+* (Fin (m + 1) → w.1.adicCompletion L))) δ).prod) :
    ∃ (τ₀ : @Measure (AutomorphicForm.sigmaCentralizer
          (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) ν) (borel _))
      (s : GL (Fin 2) (w.1.adicCompletion L) → ℝ),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ₀ ∧
      τ₀ {t | (t : GL (Fin 2) (w.1.adicCompletion L)) ∈ AutomorphicForm.localIntegralSet L w.1} = 1 ∧
      (∀ x, 0 ≤ s x) ∧ Measurable[AutomorphicForm.localGLBorel L w.1] s ∧ HasCompactSupport s ∧
      (∀ x : GL (Fin 2) (w.1.adicCompletion L),
        x⁻¹ * ν * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x ∈ AutomorphicForm.localIntegralSet L w.1 →
          ∫ t : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) ν,
            s ((t : GL (Fin 2) (w.1.adicCompletion L)) * x) ∂τ₀ = 1) ∧
      (I = 0 ∨
        I = ∫ x : GL (Fin 2) (w.1.adicCompletion L),
          (AutomorphicForm.localIntegralSet L w.1).indicator (fun _ => (1 : ℂ))
              (x⁻¹ * ν * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x) * (s x : ℂ)
            ∂(AutomorphicForm.localHaar L w.1)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isHaarMeasure_and_eq_integral_indicator_localIntegralSet_twistedConj_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet.solution
