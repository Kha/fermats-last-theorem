import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import P2M.Util
import P2M.Sol.S_UnramifiedWhittaker_exists_hasProd_eulerFactors_and_integral_zetaIntegrand_eq

set_option autoImplicit false

open Matrix MeasureTheory Polynomial
open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdeleRing NumberField.TateGlobal
open AutomorphicForm AdelicDock

open scoped Classical in

theorem UnramifiedWhittaker.exists_hasProd_eulerFactors_and_integral_zetaIntegrand_eq
    (F : Type) [Field F] [NumberField F] [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] (ν : Measure (AdeleRing (𝓞 F) F)ˣ)
    (Φ : HeckeEigensystem F ℂ) (S : Finset (HeightOneSpectrum (𝓞 F))) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (W : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), AddChar (v.adicCompletion F) ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)
    (hπ : ∀ v : HeightOneSpectrum (𝓞 F),
      algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v) ≠ 0)
    {I : HeightOneSpectrum (𝓞 F) → Type*} [∀ v, Fintype (I v)] [∀ v, Nonempty (I v)]
    (b : ∀ v : HeightOneSpectrum (𝓞 F), I v → v.adicCompletionIntegers F)
    (hI : ∀ v ∉ S, Fintype.card (I v) = Ideal.absNorm v.asIdeal)
    (hgen : ∀ v ∉ S, finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (LocalGL2.diagPi (ϖ v) (hπ v))) = heckeGen (𝓞 F) F v)
    (hψ0 : ∀ v ∉ S, ∀ r : v.adicCompletionIntegers F,
      ψ v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r) = 1)
    (hψ1 : ∀ v ∉ S, ∃ r : v.adicCompletionIntegers F,
      ψ v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r /
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) ≠ 1)
    (hN : ∀ v ∉ S, ∀ (x : v.adicCompletion F) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)),
      W (placeEmbed F v (unipotent x) * g) = ψ v x * W g)
    (hK : ∀ v ∉ S, ∀ (r : v.adicCompletionIntegers F) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)),
      W (g * placeEmbed F v (unipotent
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r))) = W g)
    (hT : ∀ v ∉ S, ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      (∑ i, W (g * placeEmbed F v (repSome
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v)
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b v i))))) +
        W (g * placeEmbed F v (repInf
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v))) =
        Φ.a v * W g)
    (hZ : ∀ v ∉ S, ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      W (g * placeEmbed F v (scalarPi
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v))) =
        Φ.toRawCentral.b v * W g)
    (hU : ∀ u : (AdeleRing (𝓞 F) F)ˣ,
      (u : AdeleRing (𝓞 F) F).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 F) F).2 v = 1) →
      finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F →
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F), W (g * diagOne u) = W g)
    (hχU : ∀ u : (AdeleRing (𝓞 F) F)ˣ,
      (u : AdeleRing (𝓞 F) F).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 F) F).2 v = 1) →
      finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F →
      χ u = 1)
    (hnormU : ∀ u : (AdeleRing (𝓞 F) F)ˣ,
      (u : AdeleRing (𝓞 F) F).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 F) F).2 v = 1) →
      finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F →
      ideleNorm F u = 1)
    (hnorm : ∀ v : HeightOneSpectrum (𝓞 F),
      ideleNorm F (uniformizerIdele F v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹)
    (τ : ℝ)
    (hτ : ∀ v ∉ S,
      ‖((χ (uniformizerIdele F v) : ℂˣ) : ℂ)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ τ)
    (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      ‖Φ.a v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖Φ.b v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
    (σ₀ : ℝ) (hσ₀ : κ + τ + 4 ≤ σ₀)
    (Hν : ProductMeasureData S ν)
    (hS : ∀ s : ℂ, σ₀ < s.re → Integrable (zetaIntegrand W χ s) Hν.νS) :
    ∃ L : ℂ → ℂ, ∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
          ((if IsUnramifiedCharAt χ v.1
            then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * Φ.a v.1) * X
              + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) * Φ.b v.1) * X ^ 2
            else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (L s) ∧
        Integrable (zetaIntegrand W χ s) ν ∧
        (∫ a, zetaIntegrand W χ s a ∂ν) = Hν.c * (∫ a, zetaIntegrand W χ s a ∂Hν.νS) * L s := by p2m_exact_reverting @_root_.P2MW.S_UnramifiedWhittaker_exists_hasProd_eulerFactors_and_integral_zetaIntegrand_eq.solution
