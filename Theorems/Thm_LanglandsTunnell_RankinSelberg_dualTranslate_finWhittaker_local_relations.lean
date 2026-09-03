import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_dualTranslate_finWhittaker_local_relations
attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal LanglandsTunnell LanglandsTunnell.Converse

open UnramifiedWhittaker in

theorem LanglandsTunnell.RankinSelberg.dualTranslate_finWhittaker_local_relations
    {p : HeightOneSpectrum (𝓞 ℚ)} (Φ : HeckeEigensystem ℚ ℂ) [Fintype (𝓞 ℚ ⧸ p.asIdeal)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (ϖ : p.adicCompletionIntegers ℚ) (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (hb0 : Φ.b p ≠ 0)
    (hnorm : TateGlobal.ideleNorm ℚ (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ)
      (AdelicLevel.localUnit (𝓞 ℚ) ℚ p (Units.mk0 _ hπ))) = (Ideal.absNorm p.asIdeal : ℝ)⁻¹)
    (Wf : finiteAdelicGL2Subgroup ℚ → ℂ) (k : finiteAdelicGL2Subgroup ℚ) (hk : localAt ℚ p (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1)
    (h1 : ∀ (x : p.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      Wf (RSCarrier.finFactor (placeEmbed ℚ p (unipotent x) * g)) =
        psiLoc NumberField.StandardAddChar.psiQ p x * Wf (RSCarrier.finFactor g))
    (h2 : ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
      Wf (RSCarrier.finFactor (g * placeEmbed ℚ p x)) = Wf (RSCarrier.finFactor g))
    (h3 : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      (∑ r, Wf (RSCarrier.finFactor (g * placeEmbed ℚ p (repSome
          (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
          (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (algebraMap (𝓞 ℚ) (p.adicCompletionIntegers ℚ) (Quotient.out (r : 𝓞 ℚ ⧸ p.asIdeal)))))))) +
        Wf (RSCarrier.finFactor (g * placeEmbed ℚ p (repInf (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ))) =
        Φ.a p * Wf (RSCarrier.finFactor g))
    (h4 : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wf (RSCarrier.finFactor (g * placeEmbed ℚ p (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ))) =
        (Φ.b p / (Ideal.absNorm p.asIdeal : ℂ)) * Wf (RSCarrier.finFactor g))
    (w₀ : GL (Fin 2) ℚ) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])
    (Wfd : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWfd : ∀ gf : finiteAdelicGL2Subgroup ℚ, Wfd gf =
      ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ) * (k : AdelicGL2 (𝓞 ℚ) ℚ)))) :
    (∀ (x : p.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      Wfd (RSCarrier.finFactor (placeEmbed ℚ p (unipotent x) * g)) = psiLoc ψ p x * Wfd (RSCarrier.finFactor g)) ∧
    (∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
      Wfd (RSCarrier.finFactor (g * placeEmbed ℚ p x)) = Wfd (RSCarrier.finFactor g)) ∧
    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      (∑ r, Wfd (RSCarrier.finFactor (g * placeEmbed ℚ p (repSome
          (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
          (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (algebraMap (𝓞 ℚ) (p.adicCompletionIntegers ℚ) (Quotient.out (r : 𝓞 ℚ ⧸ p.asIdeal)))))))) +
        Wfd (RSCarrier.finFactor (g * placeEmbed ℚ p (repInf (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ))) =
        (Φ.a p / Φ.b p) * Wfd (RSCarrier.finFactor g)) ∧
    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wfd (RSCarrier.finFactor (g * placeEmbed ℚ p (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ))) =
        ((Φ.b p)⁻¹ / (Ideal.absNorm p.asIdeal : ℂ)) * Wfd (RSCarrier.finFactor g)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_dualTranslate_finWhittaker_local_relations.solution
