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
import P2M.Sol.S_AutomorphicForm_whittakerCoefficient_mul_heckeGen_pow_succ_mul_localRepInf_eq

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicLevel NumberField.AdelicBox AdelicDock LocalGL2

theorem AutomorphicForm.whittakerCoefficient_mul_heckeGen_pow_succ_mul_localRepInf_eq
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (v : HeightOneSpectrum (𝓞 F))
    (ϖ : v.adicCompletionIntegers F)
    (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    (hgen : finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) = heckeGen (𝓞 F) F v)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (hcent : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (x : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F z * x) = χ z * φ x)
    (g : AdelicGL2 (𝓞 F) F) (e : ℕ) :
    whittakerCoefficient F pins ψ φ 1
        (g * heckeGen (𝓞 F) F v ^ (e + 1) * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (localRepInf ϖ hϖ0))) =
      χ (Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F)
          (localUnit (𝓞 F) F v (Units.mk0 (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0))) *
        whittakerCoefficient F pins ψ φ 1 (g * heckeGen (𝓞 F) F v ^ e) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_whittakerCoefficient_mul_heckeGen_pow_succ_mul_localRepInf_eq.solution
