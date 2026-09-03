import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isWeightedOrbitalIntegral_and_integral_pi_mul_prod_indicator_cyclicString_eq_mul_of_forall_mul_eq

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_isWeightedOrbitalIntegral_and_integral_pi_mul_prod_indicator_cyclicString_eq_mul_of_forall_mul_eq
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (j₀ : Fin (n + 1))
    (δ : Fin (n + 1) → GL (Fin 2) (v.adicCompletion K))
    (hδ : ∀ j, ((δ j : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
      ((δ j : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (hγ : ∀ j : Fin (n + 1), (List.ofFn fun k : Fin (n + 1) => δ (j + k)).prod = diagUnits2 a b)
    (τ : @Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a b))
      (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)) τ)
    (hτ1 : τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1)

    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (hfK : ∀ (y : GL (Fin 2) (v.adicCompletion K)) (k : GL (Fin 2) (v.adicCompletion K)),
      k ∈ AutomorphicForm.localIntegralSet K v → f (y * k) = f y)

    (s : (Fin (n + 1) → GL (Fin 2) (v.adicCompletion K)) → ℝ) (hs0 : ∀ x, 0 ≤ s x)
    (hsm : @Measurable _ _ (@MeasurableSpace.pi (Fin (n + 1)) (fun _ => GL (Fin 2) (v.adicCompletion K))
      (fun _ => AutomorphicForm.localGLBorel K v)) _ s)
    (hsc : HasCompactSupport s)
    (hs1 : ∀ x : Fin (n + 1) → GL (Fin 2) (v.adicCompletion K),
      f ((x j₀)⁻¹ * δ j₀ * x (j₀ + 1)) *
          (∏ j ∈ Finset.univ.erase j₀,
            (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ)) ((x j)⁻¹ * δ j * x (j + 1))) ≠ 0 →
      ∫ t : AutomorphicForm.localCentralizer K v (diagUnits2 a b), s (fun j => (t : GL (Fin 2) (v.adicCompletion K)) * x j) ∂τ = 1) :
    letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := AutomorphicForm.localGLBorel K v
    ∃ J : ℂ, AutomorphicForm.IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ f J ∧
      ∫ x : Fin (n + 1) → GL (Fin 2) (v.adicCompletion K),
          f ((x j₀)⁻¹ * δ j₀ * x (j₀ + 1)) *
            (∏ j ∈ Finset.univ.erase j₀,
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ)) ((x j)⁻¹ * δ j * x (j + 1))) *
            ((∑ j, AutomorphicForm.LocalWeight.weight (x j) : ℝ) : ℂ) * (s x : ℂ)
        ∂(Measure.pi fun _ => AutomorphicForm.localHaar K v) = ((n + 1 : ℕ) : ℂ) * J := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isWeightedOrbitalIntegral_and_integral_pi_mul_prod_indicator_cyclicString_eq_mul_of_forall_mul_eq.solution
