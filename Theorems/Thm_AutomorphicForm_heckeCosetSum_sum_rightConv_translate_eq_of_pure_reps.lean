import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.SmoothCusp IsDedekindDomain UnramifiedWhittaker HeckeIntegralSeam

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (U : Subgroup (AdelicGL2 (𝓞 K) K))
    (hUv : ∀ kv : GL (Fin 2) (v.adicCompletionIntegers K),
      placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv) ∈ U)
    (reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K)
    (hsys : IsHeckeCosetSystem U (heckeGen (𝓞 K) K v) reps)
    (hpure : ∀ j, ∃ m : GL (Fin 2) (v.adicCompletion K), reps j = placeEmbed K v m)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, φ (g * u) = φ g)
    (a : ℂ) (hφT : IsHeckeCosetEigenfunctionAt K U (heckeGen (𝓞 K) K v) v φ a)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hsupp : ∀ z : AdelicGL2 (𝓞 K) K, f z ≠ 0 → ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K,
      z = z₁ * z₂ ∧ z₂ ∈ U ∧ ∀ xv : GL (Fin 2) (v.adicCompletion K), z₁ * placeEmbed K v xv = placeEmbed K v xv * z₁)
    (hint : ∀ g : AdelicGL2 (𝓞 K) K, Integrable (fun z => φ (g * z) * f z) (adelicGLHaar (Fin 2) (𝓞 K) K))
    {n : ℕ} (h : Fin n → AdelicGL2 (𝓞 K) K) (c : Fin n → ℂ)
    (hh : ∀ i, ∀ xv : GL (Fin 2) (v.adicCompletion K), h i * placeEmbed K v xv = placeEmbed K v xv * h i) :
    let Φ : AdelicGL2 (𝓞 K) K → ℂ := fun g => ∑ i, c i * rightConv K φ f (g * h i)
    (∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
      Φ (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = Φ g) ∧
    (∀ g : AdelicGL2 (𝓞 K) K, heckeCosetSum K reps Φ g = a * Φ g) ∧
    IsHeckeCosetEigenfunctionAt K U (heckeGen (𝓞 K) K v) v Φ a := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps.solution
