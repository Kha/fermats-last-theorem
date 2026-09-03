import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain UnramifiedWhittaker

theorem LanglandsTunnell.RankinSelberg.hasSum_cell_terms_rsLocalIntegral
    (v : HeightOneSpectrum (𝓞 ℚ)) [SecondCountableTopology (GL (Fin 2) (v.adicCompletion ℚ))]
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borel (GL (Fin 2) (v.adicCompletion ℚ))
    ∀ (μ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ.IsHaarMeasure]
      (μN : Measure (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure]
      [μN.IsMulRightInvariant]
      (δ : GL (Fin 2) (v.adicCompletion ℚ) → ℝ)
      (_hδN : ∀ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), δ (n * g) = δ g)
      (_hδK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), δ (g * k) = δ g)
      (s : ℂ) (W F : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
      (_hN : ∀ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), W (n * g) * F (n * g) = W g * F g)
      (_hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), W (g * k) * F (g * k) = W g * F g)
      (_hint : Integrable
        (fun g : GL (Fin 2) (v.adicCompletion ℚ) => (W g * F g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ.withDensity
          (HaarQuotient.density (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))),
      HasSum (fun p : ℤ × ℤ =>
          (((μ.withDensity
                (HaarQuotient.density (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))
              {g : GL (Fin 2) (v.adicCompletion ℚ) |
                ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                  ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, g = n * k}).toReal : ℂ) *
            ((Ideal.absNorm v.asIdeal : ℂ) ^ (p.1 - p.2)) *
            ((W (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
                  scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2) *
                F (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
                  scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2)) *
              ((δ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
                  scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2) :
                    ℝ) : ℂ) ^ (s - 1 / 2)))
        (RSCarrier.rsLocalIntegral μ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN δ s W
          F) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.solution
