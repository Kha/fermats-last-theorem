import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_finWhittaker_unipotent_levelOne_hecke_centre_of_isIsotypicCuspFormAt
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell UnramifiedWhittaker
open NumberField.AdelicLevel NumberField.AdelicBox

theorem LanglandsTunnell.finWhittaker_unipotent_levelOne_hecke_centre_of_isIsotypicCuspFormAt
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (ξ : (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
        (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Φ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (_hiso : IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
        (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ N S Φ φ)
    (WA : GL (Fin 2) ℝ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (_hfact : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ
          (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
            (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
          NumberField.StandardAddChar.psiQ φ 1 g
        = WA (ratArchGL2 g) * Wf (RSCarrier.finFactor g))
    (_hW : whittakerCoefficient ℚ
        (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
          (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ 1 ≠ 0)
    (p : HeightOneSpectrum (𝓞 ℚ)) [Fintype (𝓞 ℚ ⧸ p.asIdeal)] (_hpS : p ∉ S) (_hpN : ¬ N ≤ p.asIdeal)
    (ϖ : p.adicCompletionIntegers ℚ)
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (_hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    (∀ (x : p.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      Wf (RSCarrier.finFactor (placeEmbed ℚ p (unipotent x) * g)) =
        NumberField.StandardAddChar.psiV p x * Wf (RSCarrier.finFactor g)) ∧
    (∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
        Wf (RSCarrier.finFactor (g * placeEmbed ℚ p x)) = Wf (RSCarrier.finFactor g)) ∧
    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      (∑ i : 𝓞 ℚ ⧸ p.asIdeal, Wf (RSCarrier.finFactor (g * placeEmbed ℚ p (repSome
          (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
          (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ)
            (algebraMap (𝓞 ℚ) (p.adicCompletionIntegers ℚ) (Quotient.out i))))))) +
        Wf (RSCarrier.finFactor (g * placeEmbed ℚ p (repInf
          (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ))) =
        Φ.a p * Wf (RSCarrier.finFactor g)) ∧
    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wf (RSCarrier.finFactor (g * placeEmbed ℚ p (scalarPi
        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ))) =
        (Φ.b p / (Ideal.absNorm p.asIdeal : ℂ)) * Wf (RSCarrier.finFactor g)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_finWhittaker_unipotent_levelOne_hecke_centre_of_isIsotypicCuspFormAt.solution
