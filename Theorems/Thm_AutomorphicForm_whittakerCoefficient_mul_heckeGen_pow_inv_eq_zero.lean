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
import P2M.Sol.S_AutomorphicForm_whittakerCoefficient_mul_heckeGen_pow_inv_eq_zero

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicLevel NumberField.AdelicBox AdelicDock LocalGL2

theorem AutomorphicForm.whittakerCoefficient_mul_heckeGen_pow_inv_eq_zero
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsPrincipalInvariantAddChar F ψ)
    (v : HeightOneSpectrum (𝓞 F))
    (hψv1 : ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧
      ψ (NumberField.StandardAddChar.adeleSingleAt F v x) ≠ 1)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g))
    (hinv : ∀ (u : v.adicCompletionIntegers F) (x : AdelicGL2 (𝓞 F) F),
      φ (x * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (unipotentInt (v.adicCompletion F) u))) = φ x)
    (g : AdelicGL2 (𝓞 F) F) (hg : finComponent (𝓞 F) F v (glFin (𝓞 F) F g) = 1) (k : ℕ) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
        (g * (heckeGen (𝓞 F) F v ^ (k + 1))⁻¹) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_whittakerCoefficient_mul_heckeGen_pow_inv_eq_zero.solution
