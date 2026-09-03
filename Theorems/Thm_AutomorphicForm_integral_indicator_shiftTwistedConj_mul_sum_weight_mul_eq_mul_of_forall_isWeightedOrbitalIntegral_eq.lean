import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integral_indicator_shiftTwistedConj_mul_sum_weight_mul_eq_mul_of_forall_isWeightedOrbitalIntegral_eq

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.integral_indicator_shiftTwistedConj_mul_sum_weight_mul_eq_mul_of_forall_isWeightedOrbitalIntegral_eq
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (α β : Fin (n + 1) → (v.adicCompletion K)ˣ) (hα : ∏ i, α i = a) (hβ : ∏ i, β i = b)
    (τ : @Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a b))
      (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)) τ)
    (c : ℂ)
    (hc : ∀ J : ℂ, AutomorphicForm.IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ
      ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) J → J = c)
    [MeasurableSpace (GL (Fin 2) (v.adicCompletion K))] [BorelSpace (GL (Fin 2) (v.adicCompletion K))]
    (μ : Measure (GL (Fin 2) (v.adicCompletion K))) [μ.IsHaarMeasure]
    (hμ : μ (AutomorphicForm.localIntegralSet K v) = 1)
    (s : (Fin (n + 1) → GL (Fin 2) (v.adicCompletion K)) → ℝ) (hs0 : ∀ x, 0 ≤ s x)
    (hsm : Measurable s) (hsc : HasCompactSupport s)
    (hs1 : ∀ x : Fin (n + 1) → GL (Fin 2) (v.adicCompletion K),
      (∀ i, (x i)⁻¹ * diagUnits2 (α i) (β i) * x (finRotate (n + 1) i) ∈
          AutomorphicForm.localIntegralSet K v) →
        ∫ t : AutomorphicForm.localCentralizer K v (diagUnits2 a b),
          s (fun i => ((t : GL (Fin 2) (v.adicCompletion K)) * x i)) ∂τ = 1) :
    ∫ x : Fin (n + 1) → GL (Fin 2) (v.adicCompletion K),
        (Set.pi Set.univ fun _ : Fin (n + 1) => AutomorphicForm.localIntegralSet K v).indicator
            (fun _ => (1 : ℂ))
            (fun i => (x i)⁻¹ * diagUnits2 (α i) (β i) * x (finRotate (n + 1) i)) *
          ((∑ i, AutomorphicForm.LocalWeight.weight (x i) : ℝ) : ℂ) * (s x : ℂ)
      ∂(Measure.pi fun _ : Fin (n + 1) => μ) = ((n + 1 : ℕ) : ℂ) * c := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integral_indicator_shiftTwistedConj_mul_sum_weight_mul_eq_mul_of_forall_isWeightedOrbitalIntegral_eq.solution
