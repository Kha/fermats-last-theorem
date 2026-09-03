import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_lintegral_eq_tsum_cellMass_mul_apply_torus_of_invariant

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain UnramifiedWhittaker
open scoped ENNReal

theorem LanglandsTunnell.RankinSelberg.lintegral_eq_tsum_cellMass_mul_apply_torus_of_invariant
    (v : HeightOneSpectrum (𝓞 ℚ)) [SecondCountableTopology (GL (Fin 2) (v.adicCompletion ℚ))]
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borel (GL (Fin 2) (v.adicCompletion ℚ))
    ∀ (μ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ.IsHaarMeasure]
      (μN : Measure (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure]
      [μN.IsMulRightInvariant]
      (f : GL (Fin 2) (v.adicCompletion ℚ) → ℝ≥0∞)
      (_hN : ∀ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), f (n * g) = f g)
      (_hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), f (g * k) = f g),
      ∫⁻ g, f g ∂(μ.withDensity
          (HaarQuotient.density (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) =
        ∑' p : ℤ × ℤ,
          (μ.withDensity
                (HaarQuotient.density (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))
              {g : GL (Fin 2) (v.adicCompletion ℚ) |
                ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                  ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, g = n * k} *
            ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (p.1 - p.2) *
            f (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_lintegral_eq_tsum_cellMass_mul_apply_torus_of_invariant.solution
