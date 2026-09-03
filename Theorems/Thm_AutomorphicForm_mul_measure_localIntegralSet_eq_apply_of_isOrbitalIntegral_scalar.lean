import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_AutomorphicForm_mul_measure_localIntegralSet_eq_apply_of_isOrbitalIntegral_scalar

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

theorem AutomorphicForm.mul_measure_localIntegralSet_eq_apply_of_isOrbitalIntegral_scalar
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : ∃ c : (v.adicCompletion K)ˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ)
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (I : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegral K v γ τ fv I) :
    letI := AutomorphicForm.localCentralizerBorel K v γ
    I * ((τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v}).toReal : ℂ) =
      fv γ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_mul_measure_localIntegralSet_eq_apply_of_isOrbitalIntegral_scalar.solution
