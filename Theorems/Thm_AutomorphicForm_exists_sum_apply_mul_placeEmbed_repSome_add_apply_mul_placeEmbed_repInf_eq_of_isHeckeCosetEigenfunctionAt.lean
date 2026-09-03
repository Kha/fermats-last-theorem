import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_sum_apply_mul_placeEmbed_repSome_add_apply_mul_placeEmbed_repInf_eq_of_isHeckeCosetEigenfunctionAt
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm UnramifiedWhittaker

theorem AutomorphicForm.exists_sum_apply_mul_placeEmbed_repSome_add_apply_mul_placeEmbed_repInf_eq_of_isHeckeCosetEigenfunctionAt
    (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ v.asIdeal ∣ N)
    (ϖ : v.adicCompletionIntegers F)
    (hπ : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) = WithZero.exp (-1 : ℤ))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ)
    (hU : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, f (g * u) = f g)
    (hf : SmoothCusp.IsHeckeCosetEigenfunctionAt F (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (heckeGen (𝓞 F) F v) v f c) :
    ∃ b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers F,
      ∀ g : AdelicGL2 (𝓞 F) F,
        (∑ i, f (g * placeEmbed F v (repSome (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hπ
            (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b i))))) +
          f (g * placeEmbed F v (repInf (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hπ)) =
        c * f g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_sum_apply_mul_placeEmbed_repSome_add_apply_mul_placeEmbed_repInf_eq_of_isHeckeCosetEigenfunctionAt.solution
