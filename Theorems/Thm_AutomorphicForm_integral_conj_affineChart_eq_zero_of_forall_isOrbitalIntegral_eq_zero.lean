import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integral_conj_affineChart_eq_zero_of_forall_isOrbitalIntegral_eq_zero

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

theorem AutomorphicForm.integral_conj_affineChart_eq_zero_of_forall_isOrbitalIntegral_eq_zero
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv)
    (c : (v.adicCompletion K)ˣ)
    (ϖ : v.adicCompletion K) (hϖ : ϖ ≠ 0)
    (hϖsq : ∀ a t : v.adicCompletion K, t ≠ 0 → ‖a‖ ^ 2 ≠ ‖ϖ‖ * ‖t‖ ^ 2)
    (p r : v.adicCompletion K) (hpr : p ^ 2 - ϖ * r ^ 2 ≠ 0) (hr : r ≠ 0)
    (u : GL (Fin 2) (v.adicCompletion K))
    (hu : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![p, r; ϖ * r, p])
    (σ : v.adicCompletion K → (v.adicCompletion K)ˣ → GL (Fin 2) (v.adicCompletion K))
    (hσ : ∀ (a : v.adicCompletion K) (b : (v.adicCompletion K)ˣ),
      (σ a b : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![1, 0; a, (b : v.adicCompletion K)])
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
    (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure]
    (hvan : ∀ τ : @Measure (AutomorphicForm.localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * u))
        (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * u)),
      @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * u)) τ →
        ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * u) τ fv I →
          I = 0) :
    ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
      fv ((σ q.2 q.1)⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) c * u) * σ q.2 q.1) ∂(ν.prod μ) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integral_conj_affineChart_eq_zero_of_forall_isOrbitalIntegral_eq_zero.solution
