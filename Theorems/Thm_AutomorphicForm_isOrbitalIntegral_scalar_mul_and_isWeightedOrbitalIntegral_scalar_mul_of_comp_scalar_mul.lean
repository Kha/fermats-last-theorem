import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isOrbitalIntegral_scalar_mul_and_isWeightedOrbitalIntegral_scalar_mul_of_comp_scalar_mul

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.isOrbitalIntegral_scalar_mul_and_isWeightedOrbitalIntegral_scalar_mul_of_comp_scalar_mul
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (c : (v.adicCompletion K)ˣ)
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ)
    (hτ1 : τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (τ'' : @Measure (AutomorphicForm.localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * γ))
        (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * γ)))
    (hτ'' : @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * γ)) τ'')
    (hτ''1 : τ'' (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) :
    (∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ
        (fun x => fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c * x)) I →
      AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * γ) τ'' fv I) ∧
    (∀ J : ℂ, AutomorphicForm.IsWeightedOrbitalIntegral K v γ τ
        (fun x => fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c * x)) J →
      AutomorphicForm.IsWeightedOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * γ) τ'' fv J) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isOrbitalIntegral_scalar_mul_and_isWeightedOrbitalIntegral_scalar_mul_of_comp_scalar_mul.solution
