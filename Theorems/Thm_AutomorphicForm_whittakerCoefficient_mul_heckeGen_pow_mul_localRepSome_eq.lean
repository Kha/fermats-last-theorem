import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import P2M.Util
import P2M.Sol.S_AutomorphicForm_whittakerCoefficient_mul_heckeGen_pow_mul_localRepSome_eq

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicLevel NumberField.AdelicBox AdelicDock LocalGL2

theorem AutomorphicForm.whittakerCoefficient_mul_heckeGen_pow_mul_localRepSome_eq
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsPrincipalInvariantAddChar F ψ)
    (v : HeightOneSpectrum (𝓞 F))
    (hψv : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (0 : ℤ) →
      ψ (NumberField.StandardAddChar.adeleSingleAt F v x) = 1)
    (ϖ : v.adicCompletionIntegers F)
    (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    (hgen : finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) = heckeGen (𝓞 F) F v)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g))
    (g : AdelicGL2 (𝓞 F) F) (hg : finComponent (𝓞 F) F v (glFin (𝓞 F) F g) = 1)
    (e : ℕ) (b : v.adicCompletionIntegers F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
        (g * heckeGen (𝓞 F) F v ^ e * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (localRepSome ϖ hϖ0 b))) =
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
        (g * heckeGen (𝓞 F) F v ^ (e + 1)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_whittakerCoefficient_mul_heckeGen_pow_mul_localRepSome_eq.solution
