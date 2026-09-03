import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists
attribute [-simp] LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TensorProduct
open scoped TensorProduct.RightActions

theorem
AutomorphicForm.isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsRegularSemisimple
      (AutomorphicForm.normString K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      ∀ u₁ ∈ AutomorphicForm.semiLocalIntegralSet K L v, ∀ u₂ ∈ AutomorphicForm.semiLocalIntegralSet K L v,
        φ (u₁ * g * u₂) = φ g)
    (S : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hS :
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
          ∀ u ∈ AutomorphicForm.semiLocalIntegralSet K L v, s' = t * s * u → s' = s)
    (hcov :
      ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) ≠ 0 →
          ∃ s ∈ S,
            ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
              ∃ u ∈ AutomorphicForm.semiLocalIntegralSet K L v, x = t * s * u) :
    AutomorphicForm.IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ
      (AutomorphicForm.semiLocalHaar K L v) δ τ' φ
      (∑ s ∈ S, φ (s⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ s) /
        ((τ' {t | s⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * s ∈
            AutomorphicForm.semiLocalIntegralSet K L v}).toReal : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists.solution
