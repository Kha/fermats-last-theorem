import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_AutomorphicForm_apply_mul_placeEmbed_scalarPi_eq_toRawCentral_b_mul_of_isIsotypicCuspFormAt

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm UnramifiedWhittaker

theorem AutomorphicForm.apply_mul_placeEmbed_scalarPi_eq_toRawCentral_b_mul_of_isIsotypicCuspFormAt
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun M => levelOne (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
        (fun w => heckeGen (𝓞 F) F w) B).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Φ : HeckeEigensystem F ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsIsotypicCuspFormAt F
      (productionPinsOf F D (fun M => levelOne (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
        (fun w => heckeGen (𝓞 F) F w) B) ξ N S Φ φ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) (hvN : ¬ v.asIdeal ∣ N)
    (ϖ : v.adicCompletionIntegers F)
    (hπ : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) = WithZero.exp (-1 : ℤ)) :
    (∀ g : AdelicGL2 (𝓞 F) F,
        φ (g * placeEmbed F v (scalarPi (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hπ)) =
          Φ.toRawCentral.b v * φ g) ∧
    ((∃ g : AdelicGL2 (𝓞 F) F, φ g ≠ 0) →
      (((ξ.comp Subgroup.topEquiv.symm.toMonoidHom)
          (Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F)
            (localUnit (𝓞 F) F v (Units.mk0 _ hπ))) : ℂˣ) : ℂ) = Φ.toRawCentral.b v) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_apply_mul_placeEmbed_scalarPi_eq_toRawCentral_b_mul_of_isIsotypicCuspFormAt.solution
